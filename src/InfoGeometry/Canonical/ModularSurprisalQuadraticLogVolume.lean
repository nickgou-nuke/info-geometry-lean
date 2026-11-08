/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Analysis.ComplexMatrixLogDetCalculus
import InfoGeometry.Analysis.MatrixTraceQuadratic
import InfoGeometry.Canonical.ModularSurprisalClockingLocksPoset

/-!
# Directional derivative of finite-matrix quadratic log-volume

The potential is the real log determinant volume of `1 + β Φ²` on the open set where
that matrix is invertible. Its directional derivative is computed for arbitrary complex
matrix directions. The quadratic tangent is `β • (H Φ + Φ H)` in its noncommutative
order, and the scalar derivative is represented by the ordered trace pairing with the
inverse. This is not a claim about a CFC operator logarithm on an arbitrary algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.ModularSurprisalQuadraticLogVolume

open InfoGeometry.Analysis.ComplexMatrixLogDetCalculus
open InfoGeometry.Canonical.ModularSurprisalClockingLocksPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine
open scoped Matrix Matrix.Norms.L2Operator RightActions

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ


/-- The differential is over `ℝ`; `id <• Φ` is right multiplication by `Φ`,
so this definition does not assume the algebra is commutative. -/
def quadraticStrainDifferential {B : Type*} [NormedRing B]
    [NormedAlgebra ℝ B] (β : ℝ) (Φ : B) : B →L[ℝ] B :=
  β • (Φ • ContinuousLinearMap.id ℝ B +
    (ContinuousLinearMap.id ℝ B) <• Φ)

/-- Applying the strain differential gives the two ordered first-order terms. -/
@[simp] theorem quadraticStrainDifferential_apply {B : Type*} [NormedRing B]
    [NormedAlgebra ℝ B] (β : ℝ) (Φ H : B) :
    quadraticStrainDifferential β Φ H = β • (Φ * H + H * Φ) := by
  simp [quadraticStrainDifferential]

/-- The Fréchet differential of the quadratic strain map in any real normed
noncommutative algebra. -/
theorem hasFDerivAt_quadraticStrain {B : Type*} [NormedRing B]
    [NormedAlgebra ℝ B] (β : ℝ) (Φ : B) :
    HasFDerivAt (fun X : B => 1 + β • (X * X))
      (quadraticStrainDifferential β Φ) Φ := by
  have hid : HasFDerivAt (fun X : B => X) (ContinuousLinearMap.id ℝ B) Φ :=
    hasFDerivAt_id Φ
  have hsquare := hid.mul' hid
  simpa [quadraticStrainDifferential] using
    (hsquare.const_smul β).const_add (1 : B)

/-- Exact increment formula for the quadratic strain: after subtracting its value
and Fréchet linear term, the remainder is precisely `β H²`. This holds in the
noncommutative order without a commutation assumption on `Φ` and `H`. -/
theorem quadraticStrain_exact_remainder {B : Type*} [NormedRing B]
    [NormedAlgebra ℝ B] (β : ℝ) (Φ H : B) :
    (1 + β • ((Φ + H) * (Φ + H))) - (1 + β • (Φ * Φ)) -
        quadraticStrainDifferential β Φ H = β • (H * H) := by
  simp [quadraticStrainDifferential, mul_add, add_mul, smul_add,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  abel

/-- The exact quadratic strain remainder has the expected quadratic norm bound. -/
theorem quadraticStrain_remainder_bound {B : Type*} [NormedRing B]
    [NormedAlgebra ℝ B] (β : ℝ) (Φ H : B) :
    ‖(1 + β • ((Φ + H) * (Φ + H))) - (1 + β • (Φ * Φ)) -
      quadraticStrainDifferential β Φ H‖ ≤ ‖β‖ * ‖H‖ ^ 2 := by
  rw [quadraticStrain_exact_remainder]
  calc
    ‖β • (H * H)‖ = ‖β‖ * ‖H * H‖ := norm_smul _ _
    _ ≤ ‖β‖ * (‖H‖ * ‖H‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le H H) (norm_nonneg β)
    _ = ‖β‖ * ‖H‖ ^ 2 := by rw [pow_two]

/-- The real logarithmic volume potential of the finite-matrix quadratic strain. -/
def quadraticLogVolume (β : ℝ) (Φ : Mat) : ℝ :=
  -negLogDet (1 + (β : ℂ) • (Φ * Φ))

/-- The finite-matrix resolvent representative of the first variation of
`quadraticLogVolume`. This is an operator-valued trace-pairing gradient; no
inner-product or self-adjointness hypothesis is built into the definition. -/
def quadraticLogVolumeResolventForce (β : ℝ) (Φ : Mat) : Mat :=
  (2 * β : ℂ) • ((1 + (β : ℂ) • (Φ * Φ))⁻¹ * Φ)

/-- The full Fréchet differential of `quadraticLogVolume`, formed by composing
the native log-determinant differential with the noncommutative quadratic
strain differential. -/
def quadraticLogVolumeDifferential (β : ℝ) (Φ : Mat) : Mat →L[ℝ] ℝ :=
  (-(logDetDifferential (1 + (β : ℂ) • (Φ * Φ)))).comp
    (quadraticStrainDifferential β Φ)

/-- The log-volume potential is Fréchet differentiable at every matrix whose
quadratic strain `1 + β Φ²` is a unit. No self-adjointness or commutation
assumption on the matrix is required. -/
theorem hasFDerivAt_quadraticLogVolume (β : ℝ) (Φ : Mat)
    (hM : IsUnit (1 + (β : ℂ) • (Φ * Φ))) :
    HasFDerivAt (fun X : Mat => quadraticLogVolume β X)
      (quadraticLogVolumeDifferential β Φ) Φ := by
  have hstrain := hasFDerivAt_quadraticStrain β Φ
  have houter := (hasFDerivAt_negLogDet
    (1 + (β : ℂ) • (Φ * Φ)) hM).neg
  convert houter.comp Φ hstrain using 1 <;>
    rfl

/-- Along the affine direction `H`, the finite-matrix log-volume derivative is the trace
pairing of the inverse with the full noncommutative derivative of `Φ²`. No commutation
condition on `Φ` and `H` is assumed. -/
theorem hasDerivAt_quadraticLogVolume (β : ℝ) (Φ H : Mat)
    (hM : IsUnit (1 + (β : ℂ) • (Φ * Φ))) :
    HasDerivAt (fun t : ℝ => quadraticLogVolume β (Φ + t • H))
      (Matrix.trace ((1 + (β : ℂ) • (Φ * Φ))⁻¹ *
        ((β : ℂ) • (H * Φ + Φ * H)))).re 0 := by
  let X : ℝ → Mat := fun t =>
    1 + (β : ℂ) • ((Φ + t • H) * (Φ + t • H))
  let D : Mat := (β : ℂ) • (H * Φ + Φ * H)
  have hentries : ∀ i j : n, HasDerivAt (fun t : ℝ => X t i j) (D i j) 0 := by
    intro i j
    have hleft (k : n) :
        HasDerivAt (fun t : ℝ => Φ i k + t • H i k) (H i k) 0 := by
      simpa [add_comm] using
        ((hasDerivAt_id' (0 : ℝ)).smul_const (H i k)).const_add (Φ i k)
    have hright (k : n) :
        HasDerivAt (fun t : ℝ => Φ k j + t • H k j) (H k j) 0 := by
      simpa [add_comm] using
        ((hasDerivAt_id' (0 : ℝ)).smul_const (H k j)).const_add (Φ k j)
    have hterms : ∀ k : n,
        HasDerivAt
          (fun t : ℝ => (Φ i k + t • H i k) * (Φ k j + t • H k j))
          (H i k * Φ k j + Φ i k * H k j) 0 := by
      intro k
      convert (hleft k).mul (hright k) using 1
      · simp
    have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset n))
      (fun k _ => hterms k)
    have hscaled := hsum.const_mul (β : ℂ)
    have hentry := hscaled.const_add (if i = j then (1 : ℂ) else 0)
    have hderivSum :
        (∑ k : n, (H i k * Φ k j + Φ i k * H k j)) =
          (H * Φ + Φ * H) i j := by
      simp [Matrix.mul_apply, Finset.sum_add_distrib, add_comm]
    convert hentry using 1
    · ext t
      simp [X, Matrix.one_apply, Matrix.smul_apply, Matrix.mul_apply,
        add_comm]
    · change ((β : ℂ) • (H * Φ + Φ * H)) i j = _
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [hderivSum]
  have hlog := hasDerivAt_negLogDet (X := X) (X' := D) (t := 0)
    hentries (by simpa [X] using hM)
  have hpotential :
      (fun t : ℝ => quadraticLogVolume β (Φ + t • H)) =
        fun t => -negLogDet (X t) := by
    funext t
    rfl
  have hpositive := hlog.neg
  rw [hpotential]
  convert hpositive using 1
  · simp [X, D]

/-- Cyclicity of the finite-dimensional trace and commutation of `Φ` with its
invertible quadratic strain rewrite the directional differential as a trace-pairing
covector. This does not identify a Hilbert--Schmidt gradient, which would require
additional adjoint hypotheses. -/
theorem hasDerivAt_quadraticLogVolume_trace_pairing (β : ℝ) (Φ H : Mat)
    (hM : IsUnit (1 + (β : ℂ) • (Φ * Φ))) :
    HasDerivAt (fun t : ℝ => quadraticLogVolume β (Φ + t • H))
      (2 * β * (Matrix.trace
        ((1 + (β : ℂ) • (Φ * Φ))⁻¹ * Φ * H)).re) 0 := by
  let M : Mat := 1 + (β : ℂ) • (Φ * Φ)
  have hMunit : IsUnit M := by simpa [M] using hM
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hMunit
  have hMPhi : M * Φ = Φ * M := by
    dsimp [M]
    noncomm_ring
  have hInvPhi : M⁻¹ * Φ = Φ * M⁻¹ := by
    calc
      M⁻¹ * Φ = M⁻¹ * Φ * (M * M⁻¹) := by
        rw [M.mul_nonsing_inv hdet]
        simp
      _ = M⁻¹ * (Φ * M) * M⁻¹ := by noncomm_ring
      _ = M⁻¹ * (M * Φ) * M⁻¹ := by rw [← hMPhi]
      _ = (M⁻¹ * M) * Φ * M⁻¹ := by noncomm_ring
      _ = Φ * M⁻¹ := by
        rw [M.nonsing_inv_mul hdet]
        noncomm_ring
  have htrace : Matrix.trace (M⁻¹ * (H * Φ + Φ * H)) =
      (2 : ℂ) * Matrix.trace (M⁻¹ * Φ * H) := by
    calc
      Matrix.trace (M⁻¹ * (H * Φ + Φ * H)) =
          Matrix.trace (M⁻¹ * H * Φ) + Matrix.trace (M⁻¹ * Φ * H) := by
        rw [mul_add, Matrix.trace_add]
        congr 1 <;> simp [mul_assoc]
      _ = Matrix.trace (Φ * M⁻¹ * H) + Matrix.trace (M⁻¹ * Φ * H) := by
        rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace (M⁻¹ * Φ * H) + Matrix.trace (M⁻¹ * Φ * H) := by
        rw [← hInvPhi]
      _ = (2 : ℂ) * Matrix.trace (M⁻¹ * Φ * H) := by ring
  have hvalue :
      (Matrix.trace (M⁻¹ * ((β : ℂ) • (H * Φ + Φ * H)))).re =
        2 * β * (Matrix.trace (M⁻¹ * Φ * H)).re := by
    rw [Matrix.mul_smul, Matrix.trace_smul]
    simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [htrace]
    simp [Complex.mul_re]
    ring
  rw [← hvalue]
  simpa [M] using hasDerivAt_quadraticLogVolume β Φ H hM

/-- The exact finite-matrix surprisal derivative is represented by the
resolvent force under the real trace pairing, for every (possibly
noncommuting) matrix direction `H`. The theorem uses the ordered product
`(resolvent * Φ) * H`; it does not identify this covector with a Hilbert-space
gradient. -/
theorem hasDerivAt_quadraticLogVolume_force_pairing (β : ℝ) (Φ H : Mat)
    (hM : IsUnit (1 + (β : ℂ) • (Φ * Φ))) :
    HasDerivAt (fun t : ℝ => quadraticLogVolume β (Φ + t • H))
      (Matrix.trace (quadraticLogVolumeResolventForce β Φ * H)).re 0 := by
  have htrace :
      (Matrix.trace (quadraticLogVolumeResolventForce β Φ * H)).re =
        2 * β * (Matrix.trace
          ((1 + (β : ℂ) • (Φ * Φ))⁻¹ * Φ * H)).re := by
    simp [quadraticLogVolumeResolventForce, Algebra.smul_mul_assoc,
      Matrix.trace_smul, mul_assoc]
  rw [htrace]
  exact hasDerivAt_quadraticLogVolume_trace_pairing β Φ H hM

/-- The Fréchet differential evaluates on every direction as pairing with the
ordered resolvent force. This identifies the force as the actual differential
representative, rather than merely a separately specified operator. -/
theorem quadraticLogVolumeDifferential_apply (β : ℝ) (Φ H : Mat)
    (hM : IsUnit (1 + (β : ℂ) • (Φ * Φ))) :
    quadraticLogVolumeDifferential β Φ H =
      (Matrix.trace (quadraticLogVolumeResolventForce β Φ * H)).re := by
  have hline : HasDerivAt (fun t : ℝ => Φ + t • H) H 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const H).const_add Φ
  have hfrechet : HasDerivAt
      (fun t : ℝ => quadraticLogVolume β (Φ + t • H))
      (quadraticLogVolumeDifferential β Φ H) 0 := by
    simpa [Function.comp_def] using
      (hasFDerivAt_quadraticLogVolume β Φ hM).comp_hasDerivAt_of_eq
        0 hline (by simp)
  have hdirection := hasDerivAt_quadraticLogVolume_force_pairing β Φ H hM
  exact hfrechet.unique hdirection

/-- On the Peirce chiral block, the finite-matrix force is exactly the
repository's relative-volume resolvent force with the canonical inverse kernel.
The equality uses `genPhi² = genV` from the idempotent Peirce relations. -/
theorem quadratic_force_eq_peirce_volume_force
    (P A C : Mat) (hP : P * P = P) (β : ℝ) :
    quadraticLogVolumeResolventForce β (genPhi P A C) =
      volumeResolventForce β (relativeVolumeKernel β P A C)⁻¹ P A C := by
  have hPhiSq : genPhi P A C * genPhi P A C = genV P A C := by
    peirce_nf hP
  have hreal (r : ℝ) :
      (algebraMap ℂ Mat) (r : ℂ) = algebraMap ℝ Mat r := by
    simpa using (IsScalarTower.algebraMap_apply ℝ ℂ Mat r).symm
  have hdenom :
      1 + (β : ℂ) • (genPhi P A C * genPhi P A C) =
        relativeVolumeKernel β P A C := by
    rw [hPhiSq, relativeVolumeKernel, Algebra.smul_def,
      Algebra.smul_def, hreal β]
  unfold quadraticLogVolumeResolventForce volumeResolventForce
  rw [hdenom, Algebra.smul_def, Algebra.smul_def]
  have hcoef :
      (algebraMap ℂ Mat) ((2 : ℂ) * (β : ℂ)) = algebraMap ℝ Mat (2 * β) := by
    simpa using hreal (2 * β)
  rw [hcoef]

/-- Sensitivity of the finite-matrix log-volume to the real strain parameter `β`.
The tangent is `Φ²`, with its matrix order unchanged, and the theorem assumes only
invertibility of the base strain matrix. -/
theorem hasDerivAt_quadraticLogVolume_beta (β : ℝ) (Φ : Mat)
    (hM : IsUnit (1 + (β : ℂ) • (Φ * Φ))) :
    HasDerivAt (fun t : ℝ => quadraticLogVolume (β + t) Φ)
      (Matrix.trace ((1 + (β : ℂ) • (Φ * Φ))⁻¹ * (Φ * Φ))).re 0 := by
  let K : Mat := Φ * Φ
  let X : ℝ → Mat := fun t => 1 + (β + t) • K
  have hlin : HasDerivAt (fun t : ℝ => β + t) 1 0 := by
    simpa [add_comm] using (hasDerivAt_id' (0 : ℝ)).const_add β
  have hentries : ∀ i j : n, HasDerivAt (fun t : ℝ => X t i j) (K i j) 0 := by
    intro i j
    have hmul := (hlin.smul_const (K i j)).const_add
      (if i = j then (1 : ℂ) else 0)
    convert hmul using 1
    · ext t
      simp [X, K, Matrix.one_apply, Matrix.smul_apply]
    · simp
  have hlog := hasDerivAt_negLogDet (X := X) (X' := K) (t := 0)
    hentries (by simpa [X, K, Complex.real_smul] using hM)
  have hpotential :
      (fun t : ℝ => quadraticLogVolume (β + t) Φ) = fun t => -negLogDet (X t) := by
    funext t
    congr 1
  rw [hpotential]
  convert hlog.neg using 1
  · simp [X, K]

/-- At zero strain parameter, the first response of log-volume is the real trace of
the noncommutative quadratic strain `Φ * Φ`. -/
theorem deriv_quadraticLogVolume_beta_zero (Φ : Mat) :
    deriv (fun β : ℝ => quadraticLogVolume β Φ) 0 =
      (Matrix.trace (Φ * Φ)).re := by
  have h := (hasDerivAt_quadraticLogVolume_beta 0 Φ (by simp)).deriv
  simpa using h

/-- The second response at the isotropic parameter is the negative fourth-order trace
of the strain generator. This is the local quadratic curvature of the finite-matrix
surprisal potential; it makes no diagonalization or commutation assumption. -/
theorem second_deriv_quadraticLogVolume_beta_zero (Φ : Mat) :
    deriv (deriv (fun β : ℝ => quadraticLogVolume β Φ)) 0 =
      -(Matrix.trace ((Φ * Φ) ^ 2)).re := by
  let K : Mat := Φ * Φ
  have hpath : (fun β : ℝ => quadraticLogVolume β Φ) =
      fun β => -negLogDet (1 + β • K) := by
    funext β
    simp [quadraticLogVolume, K]
  have hbase := second_deriv_negLogDet_add_smul_zero
    (1 : Mat) K (by exact isUnit_one)
  have hneg := congrArg (fun r : ℝ => -r) hbase
  rw [hpath]
  simpa [K, Matrix.one_mul] using hneg

/-- The third response at zero is the positive cubic trace of the strain generator.
Together with the preceding theorem this records the next coefficient of the local
finite-matrix surprisal expansion. -/
theorem third_deriv_quadraticLogVolume_beta_zero (Φ : Mat) :
    deriv (deriv (deriv (fun β : ℝ => quadraticLogVolume β Φ))) 0 =
      2 * (Matrix.trace ((Φ * Φ) ^ 3)).re := by
  let K : Mat := Φ * Φ
  have hpath : (fun β : ℝ => quadraticLogVolume β Φ) =
      fun β => -negLogDet (1 + β • K) := by
    funext β
    simp [quadraticLogVolume, K]
  have hbase := third_deriv_negLogDet_add_smul_zero
    (1 : Mat) K (by exact isUnit_one)
  have hneg := congrArg (fun r : ℝ => -r) hbase
  rw [hpath]
  simpa [K, Matrix.one_mul] using hneg

/-! ## Finite-matrix BKM resolvent trace -/

/-- Pointwise trace factorization of the ordered Peirce resolvent integrand.
The order of the four matrix factors is retained. -/
theorem trace_resolvent_integrand_factorization (P A C : Mat) (hP : P * P = P)
    (p q s : ℝ) :
    Matrix.trace
      (genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P) =
      ((p + s) * (q + s))⁻¹ • Matrix.trace (genV P A C) := by
  have hfactor := genPhi_sheetRho_alternated_sq hP A C
    (p + s)⁻¹ (q + s)⁻¹
  dsimp [sheetResolvent] at hfactor ⊢
  rw [hfactor, ← mul_inv]
  simp [Matrix.trace_smul]

/-- The trace of the ordered Peirce resolvent integrand has the BKM divided-difference
integral, including the equal-sheet case. The result is complex-valued because an arbitrary
idempotent and arbitrary off-diagonal blocks do not imply a real trace. No commutativity
assumption on the matrices is used. -/
theorem bkm_trace_resolvent_integral (P A C : Mat) (hP : P * P = P)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ∫ s in Set.Ioi 0,
      Matrix.trace
        (genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P) =
      (bkmDividedDiffWeight p q : ℂ) * Matrix.trace (genV P A C) := by
  have hcongr : ∀ s ∈ Set.Ioi 0,
      Matrix.trace
        (genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P) =
        ((p + s) * (q + s))⁻¹ • Matrix.trace (genV P A C) := by
    intro s hs
    exact trace_resolvent_integrand_factorization P A C hP p q s
  calc
    ∫ s in Set.Ioi 0,
        Matrix.trace
          (genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P)
      = ∫ s in Set.Ioi 0,
          ((p + s) * (q + s))⁻¹ • Matrix.trace (genV P A C) := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            exact hcongr
    _ = (bkmDividedDiffWeight p q : ℂ) * Matrix.trace (genV P A C) := by
          rw [integral_smul_const, bkm_resolvent_kernel_integral_extended p q hp hq]
          simp

/-- The real-part BKM trace integral is the divided difference times the real trace of the
Peirce Gramian. This statement needs no separate self-adjointness assumption: it is the real
part of the exact complex trace identity. -/
theorem bkm_real_trace_resolvent_integral (P A C : Mat) (hP : P * P = P)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ∫ s in Set.Ioi 0,
      (Matrix.trace
        (genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P)).re =
      bkmDividedDiffWeight p q * (Matrix.trace (genV P A C)).re := by
  calc
    ∫ s in Set.Ioi 0,
        (Matrix.trace
          (genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P)).re
      = ∫ s in Set.Ioi 0,
          ((p + s) * (q + s))⁻¹ * (Matrix.trace (genV P A C)).re := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro s hs
            have htrace := trace_resolvent_integrand_factorization P A C hP p q s
            change (Matrix.trace
              (genPhi P A C * sheetResolvent p q s P * genPhi P A C *
                sheetResolvent p q s P)).re = _
            rw [htrace]
            exact Complex.smul_re _ _
    _ = bkmDividedDiffWeight p q * (Matrix.trace (genV P A C)).re := by
          change (∫ s in Set.Ioi 0,
            ((p + s) * (q + s))⁻¹ • (Matrix.trace (genV P A C)).re) = _
          rw [integral_smul_const, bkm_resolvent_kernel_integral_extended p q hp hq]
          rfl

/-- Equal-sheet BKM trace metric. On the isotropic diagonal the continuous
divided-difference coefficient is `1 / p`, so the ordered trace integral is
exactly the real trace of the Peirce strain divided by `p`. -/
theorem bkm_real_trace_resolvent_integral_isotropic (P A C : Mat)
    (hP : P * P = P) (p : ℝ) (hp : 0 < p) :
    ∫ s in Set.Ioi 0,
      (Matrix.trace
        (genPhi P A C * sheetResolvent p p s P * genPhi P A C * sheetResolvent p p s P)).re =
      p⁻¹ * (Matrix.trace (genV P A C)).re := by
  rw [bkm_real_trace_resolvent_integral P A C hP p p hp hp,
    bkmDividedDiffWeight_diag]

/-- At unit sheet weight, the isotropic BKM trace integral equals the initial
response of the finite-matrix quadratic log-volume.  This identifies the two
constructions on the same Peirce chiral block, using `genPhi² = genV`; it does
not identify an abstract operator logarithm with a trace-log potential. -/
theorem quadraticLogVolume_initial_response_eq_isotropic_bkm
    (P A C : Mat) (hP : P * P = P) :
    deriv (fun β : ℝ => quadraticLogVolume β (genPhi P A C)) 0 =
      ∫ s in Set.Ioi 0,
        (Matrix.trace
          (genPhi P A C * sheetResolvent 1 1 s P * genPhi P A C *
            sheetResolvent 1 1 s P)).re := by
  rw [deriv_quadraticLogVolume_beta_zero]
  have hPhiSq : genPhi P A C * genPhi P A C = genV P A C := by
    peirce_nf hP
  rw [hPhiSq]
  have hBKM := bkm_real_trace_resolvent_integral_isotropic P A C hP 1 zero_lt_one
  simpa using hBKM.symm

/-- The BKM integral is nonnegative on an adjoint-compatible Peirce mode.
Here `P` is a Hermitian idempotent and the lower corner is the adjoint of the
upper corner.  Consequently the chiral block is self-adjoint, its square is
the Peirce Gramian, and the finite-matrix trace positivity theorem applies.
The result is specific to this positive matrix realization; arbitrary
idempotents and unrelated lower blocks need not have nonnegative trace. -/
theorem bkm_real_trace_resolvent_integral_nonneg
    (P A : Mat) (hP : P * P = P) (hPstar : star P = P)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    0 ≤ ∫ s in Set.Ioi 0,
      (Matrix.trace
        (genPhi P A (star A) * sheetResolvent p q s P *
          genPhi P A (star A) * sheetResolvent p q s P)).re := by
  rw [bkm_real_trace_resolvent_integral P A (star A) hP p q hp hq]
  have hweight : 0 < bkmDividedDiffWeight p q :=
    bkmDividedDiffWeight_pos p q hp hq
  have hPhiStar : star (genPhi P A (star A)) = genPhi P A (star A) := by
    simp only [genPhi, conePlus, coneMinus, star_add, star_mul,
      star_sub, star_one, hPstar, star_star]
    noncomm_ring
  have hGram : genV P A (star A) =
      star (genPhi P A (star A)) * genPhi P A (star A) := by
    have hsq : genPhi P A (star A) * genPhi P A (star A) =
        genV P A (star A) := by
      peirce_nf hP
    rw [hPhiStar, hsq]
  have htrace : 0 ≤ (Matrix.trace (genV P A (star A))).re := by
    rw [hGram]
    simpa only [InfoGeometry.Analysis.MatrixTraceQuadratic.tracePair_apply] using
      InfoGeometry.Analysis.MatrixTraceQuadratic.tracePair_self_nonneg
        (genPhi P A (star A))
  exact mul_nonneg (le_of_lt hweight) htrace

/-- The same BKM integral is strictly positive on every nonzero
adjoint-compatible Peirce mode.  Thus the evaluated BKM quadratic form is
positive definite on this finite-dimensional mode space. -/
theorem bkm_real_trace_resolvent_integral_pos_of_mode_ne
    (P A : Mat) (hP : P * P = P) (hPstar : star P = P)
    (hMode : genPhi P A (star A) ≠ 0)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    0 < ∫ s in Set.Ioi 0,
      (Matrix.trace
        (genPhi P A (star A) * sheetResolvent p q s P *
          genPhi P A (star A) * sheetResolvent p q s P)).re := by
  rw [bkm_real_trace_resolvent_integral P A (star A) hP p q hp hq]
  have hweight : 0 < bkmDividedDiffWeight p q :=
    bkmDividedDiffWeight_pos p q hp hq
  have hPhiStar : star (genPhi P A (star A)) = genPhi P A (star A) := by
    simp only [genPhi, conePlus, coneMinus, star_add, star_mul,
      star_sub, star_one, hPstar, star_star]
    noncomm_ring
  have hGram : genV P A (star A) =
      star (genPhi P A (star A)) * genPhi P A (star A) := by
    have hsq : genPhi P A (star A) * genPhi P A (star A) =
        genV P A (star A) := by
      peirce_nf hP
    rw [hPhiStar, hsq]
  have htrace : 0 < (Matrix.trace (genV P A (star A))).re := by
    rw [hGram]
    exact (InfoGeometry.Analysis.MatrixTraceQuadratic.tracePair_self_pos_iff
      (genPhi P A (star A))).2 hMode
  exact mul_pos hweight htrace

end InfoGeometry.Canonical.ModularSurprisalQuadraticLogVolume
