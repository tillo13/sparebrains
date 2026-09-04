"""Small parser contract tests. Lean remains the end-to-end verifier in Actions."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from attempt import extract_proof


class ExtractProofTests(unittest.TestCase):
    def test_recovers_bare_by_block(self):
        self.assertEqual(extract_proof("by\n  norm_num\n", "demo"), "  norm_num\n")

    def test_does_not_mine_by_from_prose(self):
        self.assertIsNone(extract_proof("Here is a proof: by\n  norm_num\n", "demo"))

    def test_keeps_fenced_full_file_behavior(self):
        reply = "```lean\nimport Mathlib\n\ntheorem demo : 2 + 2 = 4 := by\n  norm_num\n```"
        self.assertEqual(extract_proof(reply, "demo"), "  norm_num\n")


if __name__ == "__main__":
    unittest.main()
