import proofs.CanonicalZornCompositionTriality

/-!
# The canonical Zorn associator defect

This file records two elementary identities for the canonical complex Zorn
carrier.  The name `zorn3Cocycle` denotes only the associator defect; no
quasi-Hopf structure or cocycle law is asserted here.
-/

noncomputable section

namespace ZornQuasiHopfCocycle

open SplitOctonionBraidSU3

/-- The associator defect `(X * Y) * Z - X * (Y * Z)`. -/
def zorn3Cocycle (X Y Z : Zorn) : Zorn :=
  zornSub (zornMul (zornMul X Y) Z) (zornMul X (zornMul Y Z))

/-- A Zorn element is diagonal when both vector coordinates vanish. -/
def IsDiagonal (X : Zorn) : Prop :=
  X.u = 0 ∧ X.v = 0

/-- A pure upper off-diagonal Zorn element. -/
def upperNilpotent (u : Fin 3 → ℂ) : Zorn where
  a := 0
  u := u
  v := 0
  b := 0

/-- Diagonal Zorn elements associate. -/
theorem cocycle_vanishes_on_diagonal (X Y Z : Zorn)
    (hX : IsDiagonal X) (hY : IsDiagonal Y) (hZ : IsDiagonal Z) :
    zorn3Cocycle X Y Z = 0 := by
  rcases hX with ⟨hx_u, hx_v⟩
  rcases hY with ⟨hy_u, hy_v⟩
  rcases hZ with ⟨hz_u, hz_v⟩
  change zorn3Cocycle X Y Z = zornZero
  apply zorn_ext
  · simp [zorn3Cocycle, zornSub, zornMul, dot3, cross3,
      hx_u, hx_v, hy_u, hy_v, hz_u, hz_v, zornZero]
    ring
  · funext i
    fin_cases i <;>
      simp [zorn3Cocycle, zornSub, zornMul, dot3, cross3,
        hx_u, hx_v, hy_u, hy_v, hz_u, hz_v, zornZero]
  · funext i
    fin_cases i <;>
      simp [zorn3Cocycle, zornSub, zornMul, dot3, cross3,
        hx_u, hx_v, hy_u, hy_v, hz_u, hz_v, zornZero]
  · simp [zorn3Cocycle, zornSub, zornMul, dot3, cross3,
      hx_u, hx_v, hy_u, hy_v, hz_u, hz_v, zornZero]
    ring

/-- The associator of three pure upper elements is the scalar triple product
along the split grading element `ell`. -/
theorem cocycle_upper_triple (u₁ u₂ u₃ : Fin 3 → ℂ) :
    zorn3Cocycle (upperNilpotent u₁) (upperNilpotent u₂) (upperNilpotent u₃) =
      zornSmul (-dot3 (cross3 u₁ u₂) u₃) ell := by
  apply zorn_ext
  · simp [zorn3Cocycle, upperNilpotent, zornSub, zornMul, zornSmul,
      ell, dot3, cross3]
    ring
  · funext i
    fin_cases i <;>
      simp [zorn3Cocycle, upperNilpotent, zornSub, zornMul, zornSmul,
        ell, dot3, cross3]
  · funext i
    fin_cases i <;>
      simp [zorn3Cocycle, upperNilpotent, zornSub, zornMul, zornSmul,
        ell, dot3, cross3]
  · simp [zorn3Cocycle, upperNilpotent, zornSub, zornMul, zornSmul,
      ell, dot3, cross3]

end ZornQuasiHopfCocycle

end noncomputable section
