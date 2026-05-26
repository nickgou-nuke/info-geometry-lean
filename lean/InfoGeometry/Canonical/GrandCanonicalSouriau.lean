import Mathlib
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Canonical.CantorHaarDiracSea
import InfoGeometry.Canonical.ModularSL2R

/-!
# InfoGeometry.Canonical.GrandCanonicalSouriau

Concrete finite grand-canonical regularization on `M₂(ℝ)`.

We define
`S(β, μ) = β ψ + μ φ`
with
`ψ = N_left - N_right` and `φ = N_left + N_right = 1`,
and prove the boundary pairing vanishes:
`traceForm (S(β, μ)) N = 0`.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.GrandCanonicalSouriau

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.CantorHaarDiracSea
open InfoGeometry.Canonical.ModularSL2R

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Souriau/Jaynes finite thermodynamic state on the `M₂(ℝ)` seed. -/
noncomputable def SouriauState (beta mu : ℝ) : M2R :=
  beta • HaarPsi + mu • HaarPhi

/-- Grand-canonical boundary regularization theorem on the finite seed. -/
theorem grand_canonical_regularization (beta mu : ℝ) :
    traceForm (SouriauState beta mu) N = 0 := by
  unfold SouriauState
  rw [HaarPsi_eq_K, HaarPhi_is_identity]
  unfold traceForm tr
  rw [InfoGeometry.Canonical.ModularLorentzBoost.K_eval]
  norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.GrandCanonicalSouriau

