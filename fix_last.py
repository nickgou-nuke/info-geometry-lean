import re

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'r') as f:
    text = f.read()

new_proof = """theorem circularNullBoundaryFlow_fixed_iff_of_ne_zero (t : ℝ) (ht : t ≠ 0)
    (p : CircularNullBoundary) :
    circularNullBoundaryFlow t p = p ↔
      (p.1.rep ∈ positiveWeightSubmodule ∨
       p.1.rep ∈ negativeWeightSubmodule ∨
       (p.1.rep ∈ zeroWeightSubmodule ∧ (p.1.rep 0 = 0 ∨ p.1.rep 4 = 0))) := by
  set x := p.1.rep
  have hx : x ≠ 0 := Projectivization.rep_ne_zero p.1
  have hp_eq : p.1 = Projectivization.mk ℝ x hx := (Projectivization.mk_rep p.1).symm
  have hQ : circularPeirceQuadratic x = 0 := by
    have hp2 := p.2
    rw [hp_eq] at hp2
    exact (isNull_mk_iff circularPeirceQuadratic x hx).mp hp2
  have hproj : circularNullBoundaryFlow t p = p ↔
      Projectivization.mk ℝ (hyperbolicFlowCoordinate t x) ((hyperbolicFlowCoordinateEquiv t).injective.ne hx) = Projectivization.mk ℝ x hx := by
    constructor
    · intro h
      have h1 : (circularNullBoundaryFlow t p).1 = p.1 := congr_arg Subtype.val h
      rw [hp_eq] at h1 ⊢
      simpa only [circularNullBoundaryFlow_mk_axialFlow] using h1
    · intro h
      apply Subtype.ext
      have h1 : (circularNullBoundaryFlow t p).1 = Projectivization.mk ℝ (hyperbolicFlowCoordinate t x) ((hyperbolicFlowCoordinateEquiv t).injective.ne hx) := by
        rw [hp_eq]
        exact circularNullBoundaryFlow_mk_axialFlow t x hx hp_eq.symm ▸ rfl
      -- wait, circularNullBoundaryFlow_mk_axialFlow theorem in the file is:
      -- theorem circularNullBoundaryFlow_mk_axialFlow (t : ℝ) (x : Coord) (hx : x ≠ 0) (hp : IsNull ...) : (circularNullBoundaryFlow t ⟨Projectivization.mk ...⟩).1 = Projectivization.mk ...
      sorry
"""

text = re.sub(r'theorem circularNullBoundaryFlow_fixed_iff_of_ne_zero.*?(?=theorem circularNullBoundaryFlow_preserves_incidence)', new_proof + '\n', text, flags=re.DOTALL)

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)
