"""Regression tests for the project-wide Lean placeholder audit."""
import unittest
from check_no_placeholders import FORBIDDEN, mask_lean_comments


def found(text: str) -> bool:
    return FORBIDDEN.search(mask_lean_comments(text)) is not None


class PlaceholderScannerTests(unittest.TestCase):
    def test_plain_proof_placeholder(self):
        self.assertTrue(found('theorem bad : True := by sorry\n'))

    def test_axiom_command(self):
        self.assertTrue(found('axiom bad : False\n'))

    def test_unsafe_declaration(self):
        self.assertTrue(found('unsafe def bad : Nat := 0\n'))

    def test_line_comment_is_not_a_declaration(self):
        self.assertFalse(found('-- sorry axiom unsafe admit\ntheorem good : True := by trivial\n'))

    def test_nested_doc_comments_are_ignored(self):
        self.assertFalse(found('/-! axiom /- sorry admit -/ unsafe -/\ntheorem good : True := by trivial\n'))

    def test_code_after_nested_comment_is_checked(self):
        self.assertTrue(found('/- first /- inner -/ outer -/\naxiom bad : False\n'))

    def test_comment_marker_within_string_does_not_hide_code(self):
        self.assertTrue(found('def text := "--"\naxiom bad : False\n'))
        self.assertTrue(found('def text := "/-"\ntheorem bad : True := by sorry\n'))

    def test_escaped_quote_within_string_does_not_hide_code(self):
        self.assertTrue(found('def text := "\\"--"\naxiom bad : False\n'))


if __name__ == '__main__':
    unittest.main()
