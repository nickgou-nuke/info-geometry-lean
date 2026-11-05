/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CovarianceDynamics
import InfoGeometry.Quantum.KrausAmplificationCP

/-!
# Finite noise accumulation as an existing Kraus map

The finite Stein sum is the action of the Kraus family `T ^ j`, with `j : Fin k`.
The repository's Choi and amplification owners therefore supply positivity at
every finite ancillary dimension. This concerns the linear dependence on the
noise covariance, not linearity of an affine update with nonzero fixed noise.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CovarianceKraus

open Matrix
open scoped ComplexOrder
open InfoGeometry.Canonical.FiniteSteinInverse
open InfoGeometry.OperatorAlgebra.CovarianceTransport
open InfoGeometry.Quantum.KrausAmplification

variable {n r : Type*} [Fintype n] [DecidableEq n]
variable [Fintype r] [DecidableEq r]

/-- Native linear-map realization of finite accumulated innovation covariance. -/
def finiteNoiseMap (T : Matrix n n ℂ) (k : ℕ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  InfoGeometry.Modular.Choi.krausChannel (fun j : Fin k => T ^ j.val)

theorem finiteNoiseMap_apply (T Q : Matrix n n ℂ) (k : ℕ) :
    finiteNoiseMap T k Q = finiteStein T (star T) Q k := by
  change (∑ j : Fin k, T ^ j.val * Q * star (T ^ j.val)) = _
  simpa only [star_pow, finiteStein] using
    (Fin.sum_univ_eq_sum_range (fun j => T ^ j * Q * star T ^ j) k)

/-- The finite noise response has a positive native Choi matrix. -/
theorem finiteNoiseMap_choi_posSemidef (T : Matrix n n ℂ) (k : ℕ) :
    (InfoGeometry.Modular.Choi.choiMatrix (finiteNoiseMap T k)).PosSemidef :=
  InfoGeometry.Modular.Choi.krausChannel_choi_posSemidef _

/-- Complete positivity is verified at every finite matrix amplification. -/
theorem finiteNoiseMap_amplification_posSemidef (T : Matrix n n ℂ) (k : ℕ)
    (X : Matrix (r × n) (r × n) ℂ) (hX : X.PosSemidef) :
    (amplification (finiteNoiseMap T k) X).PosSemidef :=
  amplification_krausChannel_posSemidef _ X hX

/-- The first homogeneous covariance step is the one-operator Kraus map. -/
theorem homogeneous_step_eq_kraus (T C : Matrix n n ℂ) :
    covarianceStep T 0 C =
      InfoGeometry.Modular.Choi.krausChannel (fun _ : Unit => T) C := by
  simp [covarianceStep, InfoGeometry.Modular.Choi.krausChannel,
    InfoGeometry.Quantum.Choi.krausMap]

end InfoGeometry.OperatorAlgebra.CovarianceKraus
