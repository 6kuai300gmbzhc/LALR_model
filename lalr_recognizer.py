"""Parse a PLY LALR report and recognize token streams with its parse table."""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


END_TOKEN = "$end"


@dataclass(frozen=True)
class Production:
    number: int
    lhs: str
    rhs: tuple[str, ...]


@dataclass(frozen=True)
class Action:
    kind: str
    target: int | None = None


@dataclass
class LALRTable:
    parsing_method: str
    terminals: set[str]
    nonterminals: set[str]
    productions: dict[int, Production]
    actions: dict[int, dict[str, Action]]
    gotos: dict[int, dict[str, int]]
    start_state: int = 0


@dataclass(frozen=True)
class Step:
    state: int
    lookahead: str
    action: str


@dataclass
class RecognitionResult:
    accepted: bool
    steps: list[Step]
    error: str | None = None


_RULE_RE = re.compile(r"^\s*Rule\s+(\d+)\s+(.+?)\s*->\s*(.*)$")
_SYMBOL_RE = re.compile(r"^\s*(\S+)\s*:\s*(.*)$")
_STATE_RE = re.compile(r"^\s*state\s+(\d+)\s*$")
_ITEM_RE = re.compile(r"^\s*\((\d+)\)\s+(\S+)\s*->\s*(.*)$")
_SHIFT_RE = re.compile(r"^\s*(\S+)\s+shift\s+and\s+go\s+to\s+state\s+(\d+)\s*$")
_REDUCE_RE = re.compile(r"^\s*(\S+)\s+reduce\s+using\s+rule\s+(\d+)\s+\(.*\)\s*$")


def _parse_symbol_section(lines: list[str], start: int) -> tuple[set[str], int]:
    symbols: set[str] = set()
    index = start
    while index < len(lines) and not lines[index].strip():
        index += 1
    while index < len(lines):
        line = lines[index]
        if not line.strip():
            break
        match = _SYMBOL_RE.match(line)
        if match:
            symbols.add(match.group(1))
        index += 1
    return symbols, index


def parse_report(text: str) -> LALRTable:
    """Parse the grammar and parse table printed by PLY."""
    lines = text.splitlines()
    productions: dict[int, Production] = {}
    terminals: set[str] = set()
    nonterminals: set[str] = set()
    actions: dict[int, dict[str, Action]] = {}
    gotos: dict[int, dict[str, int]] = {}
    completed_start_states: set[int] = set()
    parsing_method = ""
    current_state: int | None = None

    for index, line in enumerate(lines):
        rule_match = _RULE_RE.match(line)
        if rule_match:
            number = int(rule_match.group(1))
            lhs = rule_match.group(2).strip()
            rhs_text = rule_match.group(3).strip()
            productions[number] = Production(
                number, lhs, tuple(rhs_text.split()) if rhs_text else ()
            )
            continue

        if line.startswith("Parsing method:"):
            parsing_method = line.split(":", 1)[1].strip()
            continue

        if line.strip() == "Terminals, with rules where they appear":
            terminals, _ = _parse_symbol_section(lines, index + 1)
            continue

        if line.strip() == "Nonterminals, with rules where they appear":
            nonterminals, _ = _parse_symbol_section(lines, index + 1)
            continue

        state_match = _STATE_RE.match(line)
        if state_match:
            current_state = int(state_match.group(1))
            actions.setdefault(current_state, {})
            gotos.setdefault(current_state, {})
            continue

        if current_state is None:
            continue

        item_match = _ITEM_RE.match(line)
        if item_match:
            rule_number = int(item_match.group(1))
            rhs = item_match.group(3).split()
            if rule_number == 0 and rhs and rhs[-1] == ".":
                completed_start_states.add(current_state)
            continue

        shift_match = _SHIFT_RE.match(line)
        if shift_match:
            symbol = shift_match.group(1)
            target = int(shift_match.group(2))
            if symbol in nonterminals:
                gotos[current_state][symbol] = target
            else:
                actions[current_state][symbol] = Action("shift", target)
            continue

        reduce_match = _REDUCE_RE.match(line)
        if reduce_match:
            symbol = reduce_match.group(1)
            rule_number = int(reduce_match.group(2))
            actions[current_state][symbol] = Action("reduce", rule_number)

    for state in completed_start_states:
        actions.setdefault(state, {})[END_TOKEN] = Action("accept")

    if not parsing_method:
        raise ValueError("PLY report does not contain a parsing method")
    if not productions:
        raise ValueError("PLY report does not contain any productions")
    if not terminals or not nonterminals:
        raise ValueError("PLY report does not contain terminal/nonterminal tables")
    return LALRTable(
        parsing_method,
        terminals,
        nonterminals,
        productions,
        actions,
        gotos,
    )


def load_report(path: str | Path) -> LALRTable:
    return parse_report(Path(path).read_text(encoding="utf-8"))


def recognize_detailed(table: LALRTable, tokens: Iterable[str]) -> RecognitionResult:
    """Run the LALR table and return acceptance plus an execution trace."""
    input_tokens = list(tokens) + [END_TOKEN]
    state_stack = [table.start_state]
    position = 0
    steps: list[Step] = []

    while position < len(input_tokens):
        state = state_stack[-1]
        lookahead = input_tokens[position]
        action = table.actions.get(state, {}).get(lookahead)
        if action is None:
            return RecognitionResult(
                False,
                steps,
                f"no action for state {state} and token {lookahead!r}; "
                f"state stack={state_stack}",
            )

        if action.kind == "shift":
            state_stack.append(action.target)  # type: ignore[arg-type]
            steps.append(Step(state, lookahead, f"shift {action.target}"))
            position += 1
        elif action.kind == "reduce":
            production = table.productions.get(action.target)  # type: ignore[arg-type]
            if production is None:
                return RecognitionResult(False, steps, f"unknown production {action.target}")
            if len(state_stack) - 1 < len(production.rhs):
                return RecognitionResult(False, steps, "state stack underflow during reduction")
            if production.rhs:
                del state_stack[-len(production.rhs):]
            goto_state = table.gotos.get(state_stack[-1], {}).get(production.lhs)
            if goto_state is None:
                return RecognitionResult(
                    False,
                    steps,
                    f"no goto for state {state_stack[-1]} and nonterminal {production.lhs!r}",
                )
            state_stack.append(goto_state)
            steps.append(Step(state, lookahead, f"reduce rule {production.number}"))
        elif action.kind == "accept":
            steps.append(Step(state, lookahead, "accept"))
            return RecognitionResult(True, steps)
        else:
            return RecognitionResult(False, steps, f"unknown action kind {action.kind!r}")

    return RecognitionResult(False, steps, "input ended without an accept action")


def recognize(table: LALRTable, tokens: Iterable[str]) -> bool:
    return recognize_detailed(table, tokens).accepted


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path, help="PLY parser.out report")
    parser.add_argument("tokens", nargs="*", help="whitespace-separated terminal names")
    args = parser.parse_args()
    table = load_report(args.report)
    result = recognize_detailed(table, args.tokens)
    if result.accepted:
        print("accepted")
        return 0
    print("rejected")
    if result.error:
        print(result.error)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())