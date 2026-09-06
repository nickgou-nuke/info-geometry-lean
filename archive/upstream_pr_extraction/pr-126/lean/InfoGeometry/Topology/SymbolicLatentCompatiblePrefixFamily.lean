import InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

/-!
# Compatible prefix families for the symbolic boundary

This owner exposes the compatible-family interface already represented by the
prefix cone.  It does not introduce a second inverse-limit construction: the
existing universal cone and its canonical equivalence with the sequence
boundary remain the owners of the limit.
-/

noncomputable section

namespace InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

open CategoryTheory
open CategoryTheory.Limits

variable {A : Type} [TopologicalSpace A]

abbrev CompatiblePrefixFamily := Cone (prefixDiagram (A := A))

noncomputable def compatiblePrefixFamilyToBoundary
    (C : CompatiblePrefixFamily (A := A)) :
    C.pt ⟶ TopCat.of (Boundary (A := A)) :=
  prefixLimitLift C

noncomputable def compatiblePrefixFamilyToLimit
    (C : CompatiblePrefixFamily (A := A)) :
    C.pt ⟶ limit (prefixDiagram (A := A)) :=
  compatiblePrefixFamilyToBoundary C ≫ prefixBoundaryLimitIso.hom

theorem compatiblePrefixFamilyToBoundary_stage
    (C : CompatiblePrefixFamily (A := A)) (n : ℕ) :
    C.π.app (Opposite.op n) =
      compatiblePrefixFamilyToBoundary C ≫
        prefixCone.π.app (Opposite.op n) := by
  change C.π.app (Opposite.op n) =
    prefixLimitLift C ≫ prefixCone.π.app (Opposite.op n)
  exact ((prefixConeIsLimit (A := A)).fac C (Opposite.op n)).symm

theorem compatiblePrefixFamilyToLimit_stage
    (C : CompatiblePrefixFamily (A := A)) (n : ℕ) :
    C.π.app (Opposite.op n) =
      compatiblePrefixFamilyToLimit C ≫
        limit.π (prefixDiagram (A := A)) (Opposite.op n) := by
  rw [compatiblePrefixFamilyToLimit, Category.assoc,
    prefixBoundaryLimitIso_hom_comp]
  exact compatiblePrefixFamilyToBoundary_stage C n

theorem compatiblePrefixFamilyToBoundary_unique
    (C : CompatiblePrefixFamily (A := A))
    {f g : C.pt ⟶ TopCat.of (Boundary (A := A))}
    (h : ∀ n : ℕ,
    f ≫ prefixCone.π.app (Opposite.op n) =
        g ≫ prefixCone.π.app (Opposite.op n)) :
    f = g := by
  apply (prefixConeIsLimit (A := A)).hom_ext
  intro j
  rcases j with ⟨n⟩
  exact h n

theorem compatiblePrefixFamilyToLimit_unique
    (C : CompatiblePrefixFamily (A := A))
    {f g : C.pt ⟶ limit (prefixDiagram (A := A))}
    (h : ∀ n : ℕ,
      f ≫ limit.π (prefixDiagram (A := A)) (Opposite.op n) =
        g ≫ limit.π (prefixDiagram (A := A)) (Opposite.op n)) :
    f = g := by
  apply (limit.isLimit (prefixDiagram (A := A))).hom_ext
  intro j
  rcases j with ⟨n⟩
  exact h n

end InfoGeometry.Topology.NaryTreeBoundaryInverseLimit
