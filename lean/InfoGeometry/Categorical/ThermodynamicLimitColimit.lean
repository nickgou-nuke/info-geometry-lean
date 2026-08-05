import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Native thermodynamic colimits

For a filtered diagram `F : J ⥤ C`, Mathlib is the sole owner of the
thermodynamic/direct limit.  Use the native declarations directly:

* `colimit F` for the limiting object;
* `colimit.cocone F` for its canonical cocone;
* `colimit.isColimit F` for the universal property;
* `colimit.ι`, `colimit.desc`, `colimit.ι_desc`, and `colimit.hom_ext` for
  stage maps, descent, and uniqueness.

This routing module intentionally declares no aliases or custom evidence
structures.  The filtered hypothesis remains available through the imported
`IsFiltered` API, while existence of a particular colimit is expressed by
Mathlib's `HasColimit` instance.
-/
