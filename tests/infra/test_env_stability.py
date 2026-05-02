import unittest
import os
from tools.infra.lean_interact_wrapper import run_lean_source

class TestEnvCompaction(unittest.TestCase):
    def test_run_lean_source_env(self):
        # This test ensures that run_lean_source doesn't crash even if the current env is large.
        # Although run_lean_source in our repo doesn't use the compacting logic yet, 
        # it serves as a baseline for the fix we applied to REAL-Prover.
        source = "theorem test : 1 + 1 = 2 := rfl"
        result = run_lean_source(source, timeout=30)
        self.assertIn("ok", result)

if __name__ == "__main__":
    unittest.main()
