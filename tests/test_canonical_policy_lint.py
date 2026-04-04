import unittest

from tools.infra import canonical_policy_lint as lint


class CanonicalPolicyLintHelpersTests(unittest.TestCase):
    def test_invalid_source_line_is_rejected(self):
        lines = ["theorem foo : True := trivial"]
        self.assertFalse(lint.has_valid_source_line(lines, 0))
        self.assertFalse(lint.has_valid_source_line(lines, 2))

    def test_theorem_is_private_handles_invalid_line(self):
        lines = ["private theorem foo : True := trivial"]
        self.assertFalse(lint.theorem_is_private(lines, 0))

    def test_theorem_is_private_detects_private_declaration(self):
        lines = ["private theorem foo : True := trivial"]
        self.assertTrue(lint.theorem_is_private(lines, 1))

    def test_theorem_class_tag_handles_invalid_line(self):
        lines = ["-- theorem-class: bridge", "theorem foo : True := trivial"]
        self.assertIsNone(lint.theorem_class_tag(lines, 0))


if __name__ == "__main__":
    unittest.main()
