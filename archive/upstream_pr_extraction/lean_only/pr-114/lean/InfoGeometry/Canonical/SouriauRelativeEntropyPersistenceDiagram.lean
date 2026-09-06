import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Canonical.SouriauRelativeEntropyPersistenceFunctor

namespace SouriauRelativeEntropyPersistenceDiagram

open CategoryTheory
open SouriauRelativeEntropyPersistenceQuotient
open SouriauRelativeEntropyPersistenceFunctor

variable {n : ℕ}

/-- The two-parameter KL persistence diagram valued in topological spaces. -/
noncomputable def relativeEntropyPersistenceDiagram {n : ℕ}
    (ε : ℝ) : (ℝ × ℝ) ⥤ TopCat where
  obj I :=
    TopCat.of
      (RelativeEntropySublevelQuotient (n := n) ε I.1 I.2)
  map {I J} h :=
    TopCat.ofHom
      (relativeEntropySublevelQuotientContinuousMap ε
        (leOfHom h.1) (leOfHom h.2))
  map_id I := by
    apply TopCat.hom_ext
    ext x
    exact relativeEntropySublevelQuotientMap_refl ε I.1 I.2 x
  map_comp {I J K} hIJ hJK := by
    apply TopCat.hom_ext
    ext x
    exact
      (relativeEntropySublevelQuotientMap_trans ε
        (leOfHom hIJ.1) (leOfHom hIJ.2)
        (leOfHom hJK.1) (leOfHom hJK.2) x).symm

@[simp] theorem relativeEntropyPersistenceDiagram_map_apply
    (ε : ℝ) {I J : ℝ × ℝ} (hIJ : I ≤ J)
    (x : RelativeEntropySublevelQuotient (n := n) ε I.1 I.2) :
    (relativeEntropyPersistenceDiagram (n := n) ε).map
        ((homOfLE hIJ.1, homOfLE hIJ.2) : I ⟶ J) x =
      relativeEntropySublevelQuotientMap ε hIJ.1 hIJ.2 x := by
  rfl

@[simp] theorem relativeEntropyPersistenceDiagram_map_id_apply
    (ε : ℝ) (I : ℝ × ℝ)
    (x : RelativeEntropySublevelQuotient (n := n) ε I.1 I.2) :
    (relativeEntropyPersistenceDiagram (n := n) ε).map
        (𝟙 I) x = x := by
  simp

end SouriauRelativeEntropyPersistenceDiagram
