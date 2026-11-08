/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceEvenObservables
import InfoGeometry.OperatorAlgebra.DerivationMatrixEnergy
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixPeirceOperatorGeometryD62

/-! # Trace orthogonality of Peirce pinching

The trace-preserving Peirce channel is an orthogonal projection for the
finite-dimensional Hilbert–Schmidt pairing. Its residual is orthogonal to
every fixed point, giving an exact Pythagorean decomposition.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingOrthogonality

open Matrix InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceEvenObservables
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- The residual of pinching is orthogonal to every even matrix. -/
theorem trace_even_residual (P O X : Mat) (hP : P * P = P)
    (hPs : star P = P) (hO : evenGrade P O = O) :
    Matrix.trace (star O * (X - evenGrade P X)) = 0 := by
  have hOs : evenGrade P (star O) = star O := by
    rw [← InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceChannelDynamics.star_evenGrade P O hPs, hO]
  rw [mul_sub, Matrix.trace_sub,
    trace_even_observable P (star O) X hP hPs hOs, sub_self]

/-- Pinching is the orthogonal projection onto its fixed-point sector. -/
theorem trace_pythagorean (P X O : Mat) (hP : P * P = P)
    (hPs : star P = P) (hO : evenGrade P O = O) :
    Matrix.trace (star (X - O) * (X - O)) =
      Matrix.trace (star (X - evenGrade P X) * (X - evenGrade P X)) +
      Matrix.trace (star (evenGrade P X - O) * (evenGrade P X - O)) := by
  let R : Mat := X - evenGrade P X
  let E : Mat := evenGrade P X - O
  have hE : evenGrade P E = E := by
    dsimp [E]
    rw [evenGrade_sub,
      InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel.pinching_idempotent P X hP, hO]
  have hER : Matrix.trace (star E * R) = 0 := trace_even_residual P E X hP hPs hE
  have hRE : Matrix.trace (star R * E) = 0 := by
    have h := congrArg star hER
    simp only [star_zero] at h
    change star (Matrix.trace (Eᴴ * R)) = 0 at h
    change Matrix.trace (Rᴴ * E) = 0
    simpa only [star_zero, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose] using h
  have hsplit : X - O = R + E := by dsimp [R, E]; abel
  rw [hsplit]
  simp only [star_add, add_mul, mul_add, Matrix.trace_add, hER, hRE, add_zero, zero_add]
  abel

/-- Equality in the Pythagorean identity characterizes the unique fixed
point with the same squared error as the pinched matrix. -/
theorem trace_error_eq_iff (P X O : Mat) (hP : P * P = P)
    (hPs : star P = P) (hO : evenGrade P O = O) :
    Matrix.trace (star (X - O) * (X - O)) =
        Matrix.trace (star (X - evenGrade P X) * (X - evenGrade P X)) ↔
      O = evenGrade P X := by
  constructor
  · intro h
    have hz : Matrix.trace (star (evenGrade P X - O) * (evenGrade P X - O)) = 0 := by
      have ht := trace_pythagorean P X O hP hPs hO
      rw [h] at ht
      exact add_left_cancel (ht.symm.trans (add_zero _).symm)
    have he : evenGrade P X - O = 0 :=
      Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz
    exact (sub_eq_zero.mp he).symm
  · intro h
    rw [h]

/-- The Hilbert--Schmidt squared distance decomposes into orthogonal parts. -/
theorem normSq_pythagorean (P X O : Mat) (hP : P * P = P)
    (hPs : star P = P) (hO : evenGrade P O = O) :
    matrixTraceNormSq (X - O) =
      matrixTraceNormSq (X - evenGrade P X) + matrixTraceNormSq (evenGrade P X - O) := by
  have h := congrArg Complex.re (trace_pythagorean P X O hP hPs hO)
  simpa only [matrixTraceNormSq, RCLike.re_eq_complex_re, Complex.add_re] using h

/-- Pinching uniquely minimizes the squared Hilbert--Schmidt distance
among all matrices fixed by the same Peirce projection. -/
theorem pinching_unique_best_approximation (P X O : Mat) (hP : P * P = P)
    (hPs : star P = P) (hO : evenGrade P O = O) :
    matrixTraceNormSq (X - evenGrade P X) ≤ matrixTraceNormSq (X - O) ∧
      (matrixTraceNormSq (X - evenGrade P X) = matrixTraceNormSq (X - O) ↔
        O = evenGrade P X) := by
  have hdecomp := normSq_pythagorean P X O hP hPs hO
  have hnonneg := matrixTraceNormSq_nonneg (evenGrade P X - O)
  constructor
  · rw [hdecomp]
    exact le_add_of_nonneg_right hnonneg
  · constructor
    · intro h
      have hz : matrixTraceNormSq (evenGrade P X - O) = 0 := by linarith
      exact (sub_eq_zero.mp ((matrixTraceNormSq_eq_zero_iff _).mp hz)).symm
    · intro h
      rw [h]

/-- For a density matrix the closest even matrix is itself a density
matrix, so the same optimum holds on the physical state space. -/
theorem pinching_density_unique_best_approximation (P ρ : Mat)
    (hP : P * P = P) (hPs : star P = P)
    (hρ : ρ.PosSemidef) (hTrace : Matrix.trace ρ = 1) :
    (evenGrade P ρ).PosSemidef ∧ Matrix.trace (evenGrade P ρ) = 1 ∧
      ∀ σ : Mat, σ.PosSemidef → Matrix.trace σ = 1 → evenGrade P σ = σ →
        matrixTraceNormSq (ρ - evenGrade P ρ) ≤ matrixTraceNormSq (ρ - σ) ∧
          (matrixTraceNormSq (ρ - evenGrade P ρ) = matrixTraceNormSq (ρ - σ) ↔
            σ = evenGrade P ρ) := by
  obtain ⟨hpos, htrace⟩ :=
    InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel.pinching_is_density
      P ρ hP hPs hρ hTrace
  refine ⟨hpos, htrace, ?_⟩
  intro σ _ _ hσ
  exact pinching_unique_best_approximation P ρ σ hP hPs hσ

/-- For a Hermitian matrix, the decrease in quadratic trace under pinching
is exactly the squared Hilbert--Schmidt norm of its off-diagonal part. -/
theorem pinching_quadratic_trace_defect (P X : Mat) (hP : P * P = P)
    (hPs : star P = P) (hX : star X = X) :
    (Matrix.trace (X * X)).re =
      (Matrix.trace (evenGrade P X * evenGrade P X)).re +
        matrixTraceNormSq (X - evenGrade P X) := by
  have hzero : evenGrade P (0 : Mat) = 0 := by simp [evenGrade]
  have hEs : star (evenGrade P X) = evenGrade P X := by
    rw [InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceChannelDynamics.star_evenGrade P X hPs, hX]
  have h := normSq_pythagorean P X 0 hP hPs hzero
  simp only [sub_zero] at h
  unfold matrixTraceNormSq at h
  rw [hX, hEs] at h
  simp only [RCLike.re_eq_complex_re] at h
  simp only [matrixTraceNormSq, RCLike.re_eq_complex_re]
  linarith

/-- For normalized positive matrices, pinching cannot increase quadratic
purity, and equality holds exactly on the even Peirce sector. -/
theorem pinching_density_purity (P ρ : Mat) (hP : P * P = P)
    (hPs : star P = P) (hρ : ρ.PosSemidef) (hTrace : Matrix.trace ρ = 1) :
    (evenGrade P ρ).PosSemidef ∧ Matrix.trace (evenGrade P ρ) = 1 ∧
      (Matrix.trace (evenGrade P ρ * evenGrade P ρ)).re ≤ (Matrix.trace (ρ * ρ)).re ∧
      ((Matrix.trace (evenGrade P ρ * evenGrade P ρ)).re = (Matrix.trace (ρ * ρ)).re ↔
        evenGrade P ρ = ρ) := by
  obtain ⟨hpos, htrace⟩ :=
    InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel.pinching_is_density
      P ρ hP hPs hρ hTrace
  have hdefect := pinching_quadratic_trace_defect P ρ hP hPs hρ.isHermitian.eq
  have hn := matrixTraceNormSq_nonneg (ρ - evenGrade P ρ)
  refine ⟨hpos, htrace, ?_, ?_⟩
  · linarith
  · constructor
    · intro heq
      have hz : matrixTraceNormSq (ρ - evenGrade P ρ) = 0 := by linarith
      exact (sub_eq_zero.mp ((matrixTraceNormSq_eq_zero_iff _).mp hz)).symm
    · intro heq
      rw [heq]

/-- The quadratic purity loss is the squared Hilbert--Schmidt size of the
actual commutator between the cut and the state. -/
theorem pinching_purity_loss_eq_commutator (P ρ : Mat) (hP : P * P = P)
    (hPs : star P = P) (hρ : ρ.PosSemidef) :
    (Matrix.trace (ρ * ρ)).re =
      (Matrix.trace (evenGrade P ρ * evenGrade P ρ)).re + matrixTraceNormSq ⁅P, ρ⁆ := by
  have hself : star ρ = ρ := hρ.isHermitian.eq
  have hodd : ρ - evenGrade P ρ = oddGrade P ρ := by
    unfold evenGrade oddGrade
    peirce_nf hP
  have hoddself : star (oddGrade P ρ) = oddGrade P ρ := by
    rw [← hodd, star_sub,
      InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceChannelDynamics.star_evenGrade P ρ hPs, hself]
  have hproj : IsStarProjection P := isStarProjection_iff'.2 ⟨hP, hPs⟩
  have hgram := d62_odd_square_eq_commutator_gram hproj hself
  have hsize : matrixTraceNormSq (ρ - evenGrade P ρ) = matrixTraceNormSq ⁅P, ρ⁆ := by
    rw [hodd]
    unfold matrixTraceNormSq
    rw [hoddself, hgram]
  rw [pinching_quadratic_trace_defect P ρ hP hPs hself, hsize]

/-- Equality of the input and output purities holds exactly when the
state commutes with the cutting projection. -/
theorem pinching_purity_eq_iff_commute (P ρ : Mat) (hP : P * P = P)
    (hPs : star P = P) (hρ : ρ.PosSemidef) :
    (Matrix.trace (ρ * ρ)).re = (Matrix.trace (evenGrade P ρ * evenGrade P ρ)).re ↔
      Commute P ρ := by
  have hdefect := pinching_purity_loss_eq_commutator P ρ hP hPs hρ
  constructor
  · intro heq
    have hz : matrixTraceNormSq ⁅P, ρ⁆ = 0 := by linarith
    have hc := (matrixTraceNormSq_eq_zero_iff _).mp hz
    change P * ρ - ρ * P = 0 at hc
    exact sub_eq_zero.mp hc
  · intro hc
    have hz : ⁅P, ρ⁆ = 0 := by
      change P * ρ - ρ * P = 0
      exact sub_eq_zero.mpr hc.eq
    rw [hz] at hdefect
    have hnorm : matrixTraceNormSq (0 : Mat) = 0 := (matrixTraceNormSq_eq_zero_iff _).mpr rfl
    rw [hnorm, add_zero] at hdefect
    exact hdefect

/-- A nontrivial cut admits indistinguishable density matrices for which
at least one loses quadratic purity under the pinching channel. -/
theorem exists_indistinguishable_densities_with_strict_purity_loss
    (P A : Mat) (hP : P * P = P) (hPs : star P = P)
    (hNonzero : conePlus P A ≠ 0) :
    ∃ ρ σ : Mat, ρ.PosSemidef ∧ σ.PosSemidef ∧
      Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
      evenGrade P ρ = evenGrade P σ ∧
      ((Matrix.trace (evenGrade P ρ * evenGrade P ρ)).re < (Matrix.trace (ρ * ρ)).re ∨
       (Matrix.trace (evenGrade P σ * evenGrade P σ)).re < (Matrix.trace (σ * σ)).re) := by
  obtain ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq⟩ :=
    InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePositiveCollision.exists_indistinguishable_densities
      P A hP hPs hNonzero
  have hr := pinching_density_purity P ρ hP hPs hρ htρ
  have hs := pinching_density_purity P σ hP hPs hσ htσ
  refine ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq, ?_⟩
  by_cases hfixed : evenGrade P ρ = ρ
  · right
    apply lt_of_le_of_ne hs.2.2.1
    intro h
    have hsfix := hs.2.2.2.mp h
    exact hne (hfixed.symm.trans (heq.trans hsfix))
  · left
    apply lt_of_le_of_ne hr.2.2.1
    intro h
    exact hfixed (hr.2.2.2.mp h)

end InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingOrthogonality

end
