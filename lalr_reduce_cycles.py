"""Find cycles formed by reductions in a PLY LALR parser report."""

from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

from lalr_recognizer import LALRTable, Production, load_report


@dataclass(frozen=True)
class ReduceEdge:
    source: int
    target: int
    rule_number: int
    predecessor: int
    lookaheads: tuple[str, ...]


def _transitions(table: LALRTable) -> dict[str, dict[int, set[int]]]:
    reverse: dict[str, dict[int, set[int]]] = defaultdict(
        lambda: defaultdict(set)
    )
    for source, row in table.actions.items():
        for symbol, action in row.items():
            if action.kind == "shift" and action.target is not None:
                reverse[symbol][action.target].add(source)
    for source, row in table.gotos.items():
        for symbol, target in row.items():
            reverse[symbol][target].add(source)
    return reverse


def find_reduce_edges(table: LALRTable) -> list[ReduceEdge]:
    """Build possible state transitions caused by reductions."""
    reverse = _transitions(table)
    reductions: dict[tuple[int, int], set[str]] = defaultdict(set)
    for state, row in table.actions.items():
        for lookahead, action in row.items():
            if action.kind == "reduce" and action.target is not None:
                reductions[state, action.target].add(lookahead)

    edges: list[ReduceEdge] = []
    for (state, rule_number), lookaheads in reductions.items():
        production = table.productions.get(rule_number)
        if production is None:
            raise ValueError(f"state {state} reduces by unknown rule {rule_number}")

        predecessors = {state}
        for symbol in reversed(production.rhs):
            predecessors = {
                predecessor
                for target in predecessors
                for predecessor in reverse.get(symbol, {}).get(target, ())
            }
            if not predecessors:
                break

        for predecessor in predecessors:
            target = table.gotos.get(predecessor, {}).get(production.lhs)
            if target is not None:
                edges.append(
                    ReduceEdge(
                        state,
                        target,
                        rule_number,
                        predecessor,
                        tuple(sorted(lookaheads)),
                    )
                )
    return edges


def reduce_cycles(table: LALRTable) -> list[tuple[ReduceEdge, ...]]:
    """Return all strongly connected components containing a reduce cycle."""
    edges = find_reduce_edges(table)
    adjacency: dict[int, set[int]] = defaultdict(set)
    states: set[int] = set()
    for edge in edges:
        adjacency[edge.source].add(edge.target)
        states.update((edge.source, edge.target))

    index = 0
    indices: dict[int, int] = {}
    lowlinks: dict[int, int] = {}
    stack: list[int] = []
    on_stack: set[int] = set()
    components: list[set[int]] = []

    def visit(state: int) -> None:
        nonlocal index
        indices[state] = lowlinks[state] = index
        index += 1
        stack.append(state)
        on_stack.add(state)

        for target in adjacency[state]:
            if target not in indices:
                visit(target)
                lowlinks[state] = min(lowlinks[state], lowlinks[target])
            elif target in on_stack:
                lowlinks[state] = min(lowlinks[state], indices[target])

        if lowlinks[state] == indices[state]:
            component: set[int] = set()
            while True:
                member = stack.pop()
                on_stack.remove(member)
                component.add(member)
                if member == state:
                    break
            components.append(component)

    for state in states:
        if state not in indices:
            visit(state)

    cyclic_components = [
        component
        for component in components
        if len(component) > 1
        or any(state in adjacency[state] for state in component)
    ]
    cyclic_components.sort(key=lambda component: min(component))
    return [
        tuple(
            sorted(
                (
                    edge
                    for edge in edges
                    if edge.source in component and edge.target in component
                ),
                key=lambda edge: (
                    edge.source,
                    edge.target,
                    edge.rule_number,
                    edge.predecessor,
                ),
            )
        )
        for component in cyclic_components
    ]


def format_production(production: Production) -> str:
    rhs = " ".join(production.rhs) or "ε"
    return f"Rule {production.number}: {production.lhs} -> {rhs}"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path, help="PLY parser.out report")
    args = parser.parse_args()
    table = load_report(args.report)
    cycles = reduce_cycles(table)

    if not cycles:
        print("No reduce-operation cycles found.")
        return 0

    print(f"Found {len(cycles)} reduce-operation cycle(s).")
    print(
        "Note: cycles are in the state-only abstraction; whether a sequence "
        "of reductions repeats depends on the parser stack."
    )
    for cycle_number, edges in enumerate(cycles, start=1):
        states = sorted({edge.source for edge in edges} | {edge.target for edge in edges})
        print(f"\nCycle {cycle_number}: states {states}")
        rules = sorted({edge.rule_number for edge in edges})
        print("  Reduce-edge counts by rule:")
        for rule_number in rules:
            edge_count = sum(edge.rule_number == rule_number for edge in edges)
            print(
                f"    Rule {rule_number}: {edge_count} edge(s)"
            )
        print("  Involved grammar productions:")
        for rule_number in rules:
            print(f"    {format_production(table.productions[rule_number])}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
