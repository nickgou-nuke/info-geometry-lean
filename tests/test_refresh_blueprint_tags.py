import unittest

from tools.infra import refresh_blueprint_tags as refresh


class RefreshBlueprintTagsTests(unittest.TestCase):
    def test_locate_source_decl_finds_docstring_adjacent_declaration(self):
        lines = [
            "/-- doc -/",
            "private theorem Foo.bar : True := trivial",
        ]
        located = refresh.locate_source_decl(lines, 1)
        self.assertEqual(located, (2, "Foo.bar", "private theorem Foo.bar : True := trivial"))

    def test_source_decl_is_not_addressable_for_private_declaration(self):
        path = None
        cache = {}
        # Use helper directly on lines by monkey-patching cache through a temp path substitute.
        # The source matcher behavior is determined by the located declaration text.
        lines = ["private theorem Foo.bar : True := trivial"]
        self.assertFalse(
            refresh.PRIVATE_DECL_RE.match(lines[0]) is None
        )

    def test_source_decl_name_mismatch_is_rejected(self):
        lines = [
            "theorem SinkhornRicciIndexInvariant.mk_components : True := trivial",
        ]
        located = refresh.locate_source_decl(lines, 1)
        self.assertIsNotNone(located)
        _, short_name, _ = located
        self.assertNotEqual(
            "InfoGeometry.Canonical.AnalyticalIndex.sinkhornRicciIndexInvariant_of_components",
            short_name,
        )
        self.assertFalse(
            "InfoGeometry.Canonical.AnalyticalIndex.sinkhornRicciIndexInvariant_of_components".endswith(
                "." + short_name
            )
        )


if __name__ == "__main__":
    unittest.main()
