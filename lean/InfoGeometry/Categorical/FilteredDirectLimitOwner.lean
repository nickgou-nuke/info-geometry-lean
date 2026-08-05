import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Native filtered-colimit routing

The former version of this module introduced local aliases for
`CategoryTheory.Limits.colimit`, `colimit.ι`, and `colimit.desc`.  Those
aliases duplicated Mathlib's universal-property API and obscured the owner
of the construction.  The repository now uses the native declarations
directly at each concrete owner:

* `colimit F` is the filtered colimit object;
* `colimit.ι F j` is the stage morphism;
* `colimit.desc F c` is descent through a compatible cocone;
* `colimit.ι_desc c j` and `colimit.hom_ext` provide the factorisation and
  uniqueness laws.

This import-only module is retained as a routing/documentation surface so
old import paths remain harmless, while no custom colimit carrier or
universal-property evidence is declared here.
-/
