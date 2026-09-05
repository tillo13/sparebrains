"""Small parser contract tests. Lean remains the end-to-end verifier in Actions."""
import sys
import unittest
from unittest.mock import patch
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from attempt import extract_proof
import attempt


class ExtractProofTests(unittest.TestCase):
    def test_recovers_bare_by_block(self):
        self.assertEqual(extract_proof("by\n  norm_num\n", "demo"), "  norm_num\n")

    def test_does_not_mine_by_from_prose(self):
        self.assertIsNone(extract_proof("Here is a proof: by\n  norm_num\n", "demo"))

    def test_keeps_fenced_full_file_behavior(self):
        reply = "```lean\nimport Mathlib\n\ntheorem demo : 2 + 2 = 4 := by\n  norm_num\n```"
        self.assertEqual(extract_proof(reply, "demo"), "  norm_num\n")


class LaneMetadataTests(unittest.TestCase):
    def test_runtime_flag_and_provenance_survive_roster(self):
        row = dict(name='groq-test', provider='groq', model='gpt-oss-test',
                   quality_tier='high', is_reasoning_model=True,
                   reasoning_sources=['endpoint.is_reasoning'], lifecycle_status='revived')
        with patch.object(attempt, 'llm_backends', return_value=[row]):
            known, unknown = attempt.lanes('')
        self.assertFalse(unknown)
        self.assertEqual(known[0]['capability']['reasoning_sources'], ['endpoint.is_reasoning'])
        self.assertTrue(known[0]['capability']['is_reasoning_model'])

    def test_explicit_lane_cannot_bypass_missing_canonical_state(self):
        with patch.object(attempt, 'llm_backends', return_value=[]):
            with self.assertRaisesRegex(ValueError, 'absent'):
                attempt.lanes('unknown-nvidia')

    def test_paused_lane_is_not_tested(self):
        with patch.object(attempt, 'llm_backends', return_value=[
                dict(name='test', model='test', lifecycle_status='paused')]):
            self.assertEqual(attempt.lanes(''), ([], []))


if __name__ == "__main__":
    unittest.main()
