import unittest
from pathlib import Path

from lalr_recognizer import Action, LALRTable, Production, load_report
from lalr_reduce_cycles import find_reduce_edges, reduce_cycles


REPORT = Path(__file__).with_name("test_lalr")


class LALRReduceCycleTests(unittest.TestCase):
    def test_existing_expression_grammar_has_no_reduce_cycle(self):
        self.assertEqual(reduce_cycles(load_report(REPORT)), [])

    def test_detects_self_cycle_and_associated_production(self):
        table = LALRTable(
            parsing_method="LALR",
            terminals={"$end"},
            nonterminals={"A"},
            productions={1: Production(1, "A", ("A",))},
            actions={1: {"$end": Action("reduce", 1)}},
            gotos={0: {"A": 1}},
        )

        edges = find_reduce_edges(table)
        cycles = reduce_cycles(table)

        self.assertEqual(len(edges), 1)
        self.assertEqual((edges[0].source, edges[0].target), (1, 1))
        self.assertEqual(len(cycles), 1)
        self.assertEqual({edge.rule_number for edge in cycles[0]}, {1})


if __name__ == "__main__":
    unittest.main()
