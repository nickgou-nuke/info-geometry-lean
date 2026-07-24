import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Arithmetic.MoebiusWeylEuler
import InfoGeometry.Canonical.SplitCliffordJordanWigner

/-!
# Local Jordan--Wigner determinant identity

This file proves only the displayed single-mode `2 × 2` determinant identity.
Global Euler products, Möbius Dirichlet-series identities, Fredholm determinant
identities, and zeta identities are not proved here.
-/

open Complex
open Matrix

namespace InfoGeometry.Arithmetic.MasterIdentity

/--
**Lemma 1 (Jordan-Wigner determinant for a single mode).**

For a single prime p, on the 2-dim Fock space {|0⟩, |1⟩}:
    Tr(Γ·diag(1,p^{-β})) = 1 - p^{-β} = det(1 - diag(0,p^{-β}))

where Γ = diag(1,-1) is the chiral gamma from `SplitCliffordJordanWigner`.

This is the local `2 × 2` determinant readout for the scalar factor
`1 - p^{-β}`.
-/
theorem jordan_wigner_determinant_single_mode (p : ℕ) (β : ℂ) :
    Matrix.trace (!![1, 0; 0, -1] * !![1, 0; 0, (p : ℂ) ^ (-β)]) =
      Matrix.det (1 - !![0, 0; 0, (p : ℂ) ^ (-β)]) := by
  simp [Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two]
  ring

/--
The scalar factor `1 - p^{-β}` equals the displayed `2 × 2` determinant.
-/
theorem local_euler_eq_det (p : ℕ) (β : ℂ) :
    (1 - (p : ℂ) ^ (-β)) =
      Matrix.det (1 - !![0, 0; 0, (p : ℂ) ^ (-β)]) := by
  simp [Matrix.det_fin_two]

/-
No global Möbius/zeta/Fredholm master identity is proved in this file.
-/

end InfoGeometry.Arithmetic.MasterIdentity
