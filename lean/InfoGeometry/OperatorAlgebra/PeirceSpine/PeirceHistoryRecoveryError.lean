/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingOrthogonality
import InfoGeometry.Quantum.ReplacementStateChannel

/-! # Finite-state recovery error from the complete pinched history

The full time-indexed history of a grading-covariant finite matrix channel
can coincide on two different density matrices. Consequently every decoder
has strictly positive Hilbert--Schmidt squared error on at least one of them.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceHistoryRecoveryError

open Matrix InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCoarseGrainedDynamics
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceChannelDynamics
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- Unequal full matrices have strictly positive squared trace distance. -/
theorem matrixTraceNormSq_sub_pos {X Y : Mat} (hne : X ≠ Y) :
    0 < matrixTraceNormSq (X - Y) := by
  apply lt_of_le_of_ne (matrixTraceNormSq_nonneg _)
  intro hz
  exact hne (sub_eq_zero.mp ((matrixTraceNormSq_eq_zero_iff _).mp hz.symm))

/-- Parallelogram identity for the full complex matrix trace pairing. -/
theorem matrixTraceNormSq_parallelogram (X Y : Mat) :
    matrixTraceNormSq (X - Y) + matrixTraceNormSq (X + Y) =
      2 * matrixTraceNormSq X + 2 * matrixTraceNormSq Y := by
  simp only [matrixTraceNormSq, star_sub, star_add, sub_mul, mul_sub, add_mul, mul_add,
    Matrix.trace_sub, Matrix.trace_add, map_sub, map_add]
  ring

/-- A single estimate cannot be closer than one quarter of the squared
separation to both inputs. -/
theorem two_point_error_lower_bound (X Y Z : Mat) :
    matrixTraceNormSq (X - Y) / 4 ≤
      max (matrixTraceNormSq (X - Z)) (matrixTraceNormSq (Y - Z)) := by
  have h := matrixTraceNormSq_parallelogram (X - Z) (Y - Z)
  have hd : (X - Z) - (Y - Z) = X - Y := by abel
  rw [hd] at h
  have hn := matrixTraceNormSq_nonneg ((X - Z) + (Y - Z))
  have h1 := le_max_left (matrixTraceNormSq (X - Z)) (matrixTraceNormSq (Y - Z))
  have h2 := le_max_right (matrixTraceNormSq (X - Z)) (matrixTraceNormSq (Y - Z))
  linarith

/-- The midpoint attains the two-point lower bound exactly. -/
theorem midpoint_attains_two_point_bound (X Y : Mat) :
    let M : Mat := (1 / 2 : ℂ) • (X + Y)
    matrixTraceNormSq (X - M) = matrixTraceNormSq (X - Y) / 4 ∧
      matrixTraceNormSq (Y - M) = matrixTraceNormSq (X - Y) / 4 := by
  dsimp only
  let M : Mat := (1 / 2 : ℂ) • (X + Y)
  have hsum : (X - M) + (Y - M) = 0 := by
    ext i j
    simp only [M, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply,
      smul_eq_mul]
    ring
  have hdiff : (X - M) - (Y - M) = X - Y := by abel
  have hneg : Y - M = -(X - M) := by
    ext i j
    simp only [M, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      smul_eq_mul]
    ring
  have hnorm : matrixTraceNormSq (Y - M) = matrixTraceNormSq (X - M) := by
    rw [hneg]
    simp only [matrixTraceNormSq, star_neg, neg_mul, mul_neg, neg_neg]
  have hpar := matrixTraceNormSq_parallelogram (X - M) (Y - M)
  rw [hsum, hdiff, hnorm] at hpar
  have hz : matrixTraceNormSq (0 : Mat) = 0 := (matrixTraceNormSq_eq_zero_iff _).mpr rfl
  rw [hz, add_zero] at hpar
  change matrixTraceNormSq (X - M) = matrixTraceNormSq (X - Y) / 4 ∧
    matrixTraceNormSq (Y - M) = matrixTraceNormSq (X - Y) / 4
  rw [hnorm]
  constructor <;> linarith

/-- The midpoint is the unique minimizer of the worst squared error for
two matrices, including the case where the matrices coincide. -/
theorem two_point_error_eq_bound_iff (X Y Z : Mat) :
    max (matrixTraceNormSq (X - Z)) (matrixTraceNormSq (Y - Z)) =
        matrixTraceNormSq (X - Y) / 4 ↔ Z = (1 / 2 : ℂ) • (X + Y) := by
  constructor
  · intro h
    have hp := matrixTraceNormSq_parallelogram (X - Z) (Y - Z)
    have hd : (X - Z) - (Y - Z) = X - Y := by abel
    rw [hd] at hp
    have h1 := le_max_left (matrixTraceNormSq (X - Z)) (matrixTraceNormSq (Y - Z))
    have h2 := le_max_right (matrixTraceNormSq (X - Z)) (matrixTraceNormSq (Y - Z))
    have hn := matrixTraceNormSq_nonneg ((X - Z) + (Y - Z))
    have hz : matrixTraceNormSq ((X - Z) + (Y - Z)) = 0 := by linarith
    have hsum : (X - Z) + (Y - Z) = 0 := (matrixTraceNormSq_eq_zero_iff _).mp hz
    ext i j
    have he := congrArg (fun T : Mat => T i j) hsum
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply] at he
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    linear_combination -(1 / 2 : ℂ) * he
  · intro h
    rw [h]
    rcases midpoint_attains_two_point_bound X Y with ⟨hX, hY⟩
    rw [hX, hY, max_self]

/-- If two inputs have the same observation, a decoder reaches the bound
exactly when its output on that observation is their midpoint. -/
theorem decoder_attains_bound_iff_midpoint {Ω : Type*}
    (X Y : Mat) (observation : Mat → Ω) (decode : Ω → Mat)
    (hobs : observation X = observation Y) :
    max (matrixTraceNormSq (X - decode (observation X)))
        (matrixTraceNormSq (Y - decode (observation Y))) =
      matrixTraceNormSq (X - Y) / 4 ↔
        decode (observation X) = (1 / 2 : ℂ) • (X + Y) := by
  rw [← hobs]
  exact two_point_error_eq_bound_iff X Y _

/-- For any observation type, a constant midpoint decoder attains the
minimax lower bound for a fixed pair of inputs. -/
theorem midpoint_decoder_attains_two_point_bound {Ω : Type*}
    (X Y : Mat) (hx hy : Ω) :
    ∃ decode : Ω → Mat,
      max (matrixTraceNormSq (X - decode hx)) (matrixTraceNormSq (Y - decode hy)) =
        matrixTraceNormSq (X - Y) / 4 := by
  refine ⟨fun _ => (1 / 2 : ℂ) • (X + Y), ?_⟩
  rcases midpoint_attains_two_point_bound X Y with ⟨hX, hY⟩
  rw [hX, hY, max_self]

/-- The midpoint of two density matrices is a density matrix. -/
theorem midpoint_is_density (ρ σ : Mat) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (htρ : Matrix.trace ρ = 1) (htσ : Matrix.trace σ = 1) :
    ((1 / 2 : ℂ) • (ρ + σ)).PosSemidef ∧
      Matrix.trace ((1 / 2 : ℂ) • (ρ + σ)) = 1 := by
  constructor
  · have h : ((1 / 2 : ℝ) • (ρ + σ)).PosSemidef :=
      (hρ.add hσ).smul (by norm_num)
    have heq : ((1 / 2 : ℝ) • (ρ + σ)) = (1 / 2 : ℂ) • (ρ + σ) := by
      ext i j
      simp [Complex.real_smul, mul_add]
    rw [heq] at h
    exact h
  · rw [Matrix.trace_smul, Matrix.trace_add, htρ, htσ]
    norm_num

/-- A density-valued decoder attains the sharp two-state error bound. -/
theorem density_midpoint_decoder_attains_bound {Ω : Type*}
    (ρ σ : Mat) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (htρ : Matrix.trace ρ = 1) (htσ : Matrix.trace σ = 1) (h₁ h₂ : Ω) :
    ∃ decode : Ω → Mat,
      (∀ observation, (decode observation).PosSemidef ∧ Matrix.trace (decode observation) = 1) ∧
      max (matrixTraceNormSq (ρ - decode h₁)) (matrixTraceNormSq (σ - decode h₂)) =
        matrixTraceNormSq (ρ - σ) / 4 := by
  refine ⟨fun _ => (1 / 2 : ℂ) • (ρ + σ), ?_, ?_⟩
  · intro observation
    exact midpoint_is_density ρ σ hρ hσ htρ htσ
  · rcases midpoint_attains_two_point_bound ρ σ with ⟨hX, hY⟩
    rw [hX, hY, max_self]

/-- For finite square matrices, a genuine CPTP replacement channel attains
the two-state midpoint bound on any pair of normalized observations. -/
theorem density_midpoint_cptp_attains_bound {m : ℕ}
    (ρ σ : Matrix (Fin m) (Fin m) ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (htρ : Matrix.trace ρ = 1) (htσ : Matrix.trace σ = 1)
    (O₁ O₂ : Matrix (Fin m) (Fin m) ℂ)
    (hO₁ : Matrix.trace O₁ = 1) (hO₂ : Matrix.trace O₂ = 1) :
    ∃ E : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ,
      (∀ X, Matrix.trace (E X) = Matrix.trace X) ∧
      (∀ (r : ℕ) (X : Matrix (Fin r × Fin m) (Fin r × Fin m) ℂ),
        X.PosSemidef →
        (InfoGeometry.Quantum.KrausAmplification.amplification (r := Fin r) E X).PosSemidef) ∧
      max (matrixTraceNormSq (ρ - E O₁)) (matrixTraceNormSq (σ - E O₂)) =
        matrixTraceNormSq (ρ - σ) / 4 := by
  let M : Matrix (Fin m) (Fin m) ℂ := (1 / 2 : ℂ) • (ρ + σ)
  have hM := midpoint_is_density ρ σ hρ hσ htρ htσ
  refine ⟨InfoGeometry.Quantum.ReplacementStateChannel.replacement M, ?_, ?_, ?_⟩
  · intro X
    exact InfoGeometry.Quantum.ReplacementStateChannel.replacement_trace M X hM.2
  · intro r X hX
    exact InfoGeometry.Quantum.ReplacementStateChannel.replacement_completely_positive M hM.1 X hX
  · rw [InfoGeometry.Quantum.ReplacementStateChannel.replacement_on_density M O₁ hO₁,
      InfoGeometry.Quantum.ReplacementStateChannel.replacement_on_density M O₂ hO₂]
    rcases midpoint_attains_two_point_bound ρ σ with ⟨hX, hY⟩
    change max (matrixTraceNormSq (ρ - M)) (matrixTraceNormSq (σ - M)) = _
    rw [hX, hY, max_self]

/-- For a nontrivial cut, one fixed pair of density matrices defeats every
decoder even if the decoder receives all pinched iterates at once. -/
theorem exists_density_pair_with_unavoidable_history_error
    (P A W : Mat) (hP : P * P = P) (hPs : star P = P)
    (hW : evenGrade P W = W) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    ∃ ρ σ : Mat, ρ.PosSemidef ∧ σ.PosSemidef ∧
      Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
      (∀ k, evenGrade P (evolve P A W k ρ) = evenGrade P (evolve P A W k σ)) ∧
      ∀ decode : (ℕ → Mat) → Mat,
        0 < matrixTraceNormSq (decode (fun k => evenGrade P (evolve P A W k ρ)) - ρ) ∨
        0 < matrixTraceNormSq (decode (fun k => evenGrade P (evolve P A W k σ)) - σ) := by
  obtain ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq⟩ :=
    exists_densities_colliding_after_evolution P A W hP hPs hW hP0 hP1
  refine ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq, ?_⟩
  intro decode
  have hhistory : (fun k => evenGrade P (evolve P A W k ρ)) =
      (fun k => evenGrade P (evolve P A W k σ)) := funext heq
  by_cases h : decode (fun k => evenGrade P (evolve P A W k ρ)) = ρ
  · right
    apply matrixTraceNormSq_sub_pos
    rw [← hhistory, h]
    exact hne
  · exact Or.inl (matrixTraceNormSq_sub_pos h)

/-- The same pair yields a positive error threshold independent of the
decoder, even when the complete infinite observation history is supplied. -/
theorem exists_density_pair_with_uniform_history_error
    (P A W : Mat) (hP : P * P = P) (hPs : star P = P)
    (hW : evenGrade P W = W) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    ∃ ρ σ : Mat, ρ.PosSemidef ∧ σ.PosSemidef ∧
      Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
      (∀ k, evenGrade P (evolve P A W k ρ) = evenGrade P (evolve P A W k σ)) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ decode : (ℕ → Mat) → Mat,
        ε ≤ max (matrixTraceNormSq (ρ - decode (fun k => evenGrade P (evolve P A W k ρ))))
          (matrixTraceNormSq (σ - decode (fun k => evenGrade P (evolve P A W k σ)))) := by
  obtain ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq⟩ :=
    exists_densities_colliding_after_evolution P A W hP hPs hW hP0 hP1
  refine ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq,
    matrixTraceNormSq (ρ - σ) / 4, ?_, ?_⟩
  · exact div_pos (matrixTraceNormSq_sub_pos hne) (by norm_num)
  · intro decode
    have hhistory : (fun k => evenGrade P (evolve P A W k ρ)) =
        (fun k => evenGrade P (evolve P A W k σ)) := funext heq
    rw [← hhistory]
    exact two_point_error_lower_bound ρ σ _

/-- Every finite iterate and every pinched observation of a density matrix
is again a density matrix, under Kraus completeness. -/
theorem evolve_and_observation_are_density (P A W ρ : Mat)
    (hP : P * P = P) (hPs : star P = P)
    (hResidual : star W * W = 1 - genV P A (star A))
    (hρ : ρ.PosSemidef) (hTrace : Matrix.trace ρ = 1) (k : ℕ) :
    (evolve P A W k ρ).PosSemidef ∧ Matrix.trace (evolve P A W k ρ) = 1 ∧
      (evenGrade P (evolve P A W k ρ)).PosSemidef ∧
      Matrix.trace (evenGrade P (evolve P A W k ρ)) = 1 := by
  have he : (evolve P A W k ρ).PosSemidef ∧ Matrix.trace (evolve P A W k ρ) = 1 := by
    induction k with
    | zero => exact ⟨hρ, hTrace⟩
    | succ k ih =>
        change (InfoGeometry.Quantum.Choi.krausMap (cornerKrausWithResidual P A W)
          (evolve P A W k ρ)).PosSemidef ∧
          Matrix.trace (InfoGeometry.Quantum.Choi.krausMap (cornerKrausWithResidual P A W)
            (evolve P A W k ρ)) = 1
        exact ⟨cornerKrausWithResidual_positive P A W _ ih.1,
          (cornerKrausWithResidual_trace P A W _ hPs hResidual).trans ih.2⟩
  exact ⟨he.1, he.2, pinching_is_density P _ hP hPs he.1 he.2⟩

/-- The quantitative decoder-independent error bound is realized by a
completely positive trace-preserving channel and density-valued histories. -/
theorem exists_cptp_density_history_uniform_error
    (P A : Mat) (hP : P * P = P) (hPs : star P = P)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1)
    (hBound : (1 - genV P A (star A)).PosSemidef) :
    ∃ W : Mat, evenGrade P W = W ∧
      (∀ X : Mat, Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual P A W) X) = Matrix.trace X) ∧
      (∀ (r : Type*) [Fintype r] [DecidableEq r]
        (X : Matrix (r × n) (r × n) ℂ), X.PosSemidef →
        (InfoGeometry.Quantum.KrausAmplification.amplification (r := r)
          (InfoGeometry.Modular.Choi.krausChannel (cornerKrausWithResidual P A W)) X).PosSemidef) ∧
      (∀ ρ : Mat, ρ.PosSemidef → Matrix.trace ρ = 1 → ∀ k,
        (evenGrade P (evolve P A W k ρ)).PosSemidef ∧
          Matrix.trace (evenGrade P (evolve P A W k ρ)) = 1) ∧
      ∃ ρ σ : Mat, ρ.PosSemidef ∧ σ.PosSemidef ∧
        Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
        (∀ k, evenGrade P (evolve P A W k ρ) = evenGrade P (evolve P A W k σ)) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ decode : (ℕ → Mat) → Mat,
          ε ≤ max (matrixTraceNormSq (ρ - decode (fun k => evenGrade P (evolve P A W k ρ))))
            (matrixTraceNormSq (σ - decode (fun k => evenGrade P (evolve P A W k σ)))) := by
  obtain ⟨W, hW, hResidual⟩ := exists_even_residual P A hP hBound
  refine ⟨W, hW, ?_, ?_, ?_, ?_⟩
  · intro X
    exact cornerKrausWithResidual_trace P A W X hPs hResidual
  · intro r _ _ X hX
    exact cornerKrausWithResidual_completely_positive P A W X hX
  · intro ρ hρ hTrace k
    exact (evolve_and_observation_are_density P A W ρ hP hPs hResidual hρ hTrace k).2.2
  · exact exists_density_pair_with_uniform_history_error P A W hP hPs hW hP0 hP1

/-- A positive Peirce residual produces a trace-preserving completely
positive channel with an unavoidable nonzero full-history decoding error. -/
theorem exists_cptp_with_unavoidable_history_error
    (P A : Mat) (hP : P * P = P) (hPs : star P = P)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1)
    (hBound : (1 - genV P A (star A)).PosSemidef) :
    ∃ W : Mat, evenGrade P W = W ∧
      (∀ X : Mat, Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual P A W) X) = Matrix.trace X) ∧
      (∀ (r : Type*) [Fintype r] [DecidableEq r]
        (X : Matrix (r × n) (r × n) ℂ), X.PosSemidef →
        (InfoGeometry.Quantum.KrausAmplification.amplification (r := r)
          (InfoGeometry.Modular.Choi.krausChannel (cornerKrausWithResidual P A W)) X).PosSemidef) ∧
      ∃ ρ σ : Mat, ρ.PosSemidef ∧ σ.PosSemidef ∧
        Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
        (∀ k, evenGrade P (evolve P A W k ρ) = evenGrade P (evolve P A W k σ)) ∧
        ∀ decode : (ℕ → Mat) → Mat,
          0 < matrixTraceNormSq (decode (fun k => evenGrade P (evolve P A W k ρ)) - ρ) ∨
          0 < matrixTraceNormSq (decode (fun k => evenGrade P (evolve P A W k σ)) - σ) := by
  obtain ⟨W, hW, hResidual⟩ := exists_even_residual P A hP hBound
  refine ⟨W, hW, ?_, ?_, ?_⟩
  · intro X
    exact cornerKrausWithResidual_trace P A W X hPs hResidual
  · intro r _ _ X hX
    exact cornerKrausWithResidual_completely_positive P A W X hX
  · exact exists_density_pair_with_unavoidable_history_error P A W hP hPs hW hP0 hP1

end InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceHistoryRecoveryError

end
