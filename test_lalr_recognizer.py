import unittest
from pathlib import Path

from lalr_recognizer import load_report, recognize, recognize_detailed


REPORT = Path(__file__).with_name("test_lalr")


class LALRRecognizerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.table = load_report(REPORT)

    def test_report_metadata_and_table(self):
        self.assertEqual(self.table.parsing_method, "LALR")
        self.assertEqual(self.table.terminals, {"A", "LPAREN", "PLUS", "RPAREN", "error"})
        self.assertEqual(self.table.nonterminals, {"E", "Eprime", "T"})
        self.assertEqual(self.table.productions[2].rhs, ("E", "PLUS", "T"))
        self.assertEqual(self.table.actions[0]["A"].kind, "shift")
        self.assertEqual(self.table.actions[2]["$end"].kind, "reduce")
        self.assertEqual(self.table.actions[1]["$end"].kind, "accept")
        self.assertEqual(self.table.gotos[0]["E"], 2)

    def test_accepts_valid_token_streams(self):
        for tokens in (
            ["A"],
            ["A", "PLUS", "A"],
            ["LPAREN", "A", "RPAREN"],
            ["LPAREN", "A", "PLUS", "A", "RPAREN"],
        ):
            with self.subTest(tokens=tokens):
                self.assertTrue(recognize(self.table, tokens))

    def test_rejects_invalid_token_streams(self):
        for tokens in (
            ["PLUS", "A"],
            ["A", "PLUS"],
            ["LPAREN", "A"],
            ["A", "RPAREN"],
        ):
            with self.subTest(tokens=tokens):
                self.assertFalse(recognize(self.table, tokens))

    def test_trace_contains_shift_reduce_and_accept(self):
        result = recognize_detailed(self.table, ["A", "PLUS", "A"])
        self.assertTrue(result.accepted)
        actions = [step.action.split()[0] for step in result.steps]
        self.assertIn("shift", actions)
        self.assertIn("reduce", actions)
        self.assertEqual(actions[-1], "accept")


if __name__ == "__main__":
    unittest.main()