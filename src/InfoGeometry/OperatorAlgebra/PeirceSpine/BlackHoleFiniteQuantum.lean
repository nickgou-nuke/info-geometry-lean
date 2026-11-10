/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformationPeirce
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixBlackHolePeirceD63
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.Quantum.KrausAmplificationCP
import InfoGeometry.Meta.ArchetypePipeline
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Order

/-! # Finite matrix states and channels from Peirce corners -/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum

open Matrix InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformation
open InfoGeometry.MetaCompiler
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- The original same-sided mirror sandwich annihilates the identity. -/
theorem peirceMirrorMap_one (P A C : Mat) (hP : P * P = P) :
    peirceMirrorMap P A C 1 = 0 := by
  unfold peirceMirrorMap conePlus coneMinus
  peirce_nf hP

/-- On a nonzero finite trace space the same-sided mirror cannot be
trace-preserving. The Kraus channel below is a different construction. -/
theorem peirceMirrorMap_not_trace_preserving (P A C : Mat) (hP : P * P = P)
    (hOne : Matrix.trace (1 : Mat) ≠ 0) :
    ¬ ∀ X : Mat, Matrix.trace (peirceMirrorMap P A C X) = Matrix.trace X := by
  intro h
  have htrace := h 1
  rw [peirceMirrorMap_one P A C hP, Matrix.trace_zero] at htrace
  exact hOne htrace.symm

theorem peirceMirrorMap_not_trace_preserving_of_nonempty [Nonempty n]
    (P A C : Mat) (hP : P * P = P) :
    ¬ ∀ X : Mat, Matrix.trace (peirceMirrorMap P A C X) = Matrix.trace X := by
  apply peirceMirrorMap_not_trace_preserving P A C hP
  simp [Matrix.trace_one, Fintype.card_ne_zero]

/-- The lower sheet is a Gram matrix for adjoint-paired corners. -/
theorem lower_sheet_posSemidef (P A : Mat) (hP : star P = P) :
    (qgtMinus P A (star A)).PosSemidef := by
  change (coneMinus P (star A) * conePlus P A).PosSemidef
  rw [← star_conePlus hP A]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Positivity follows from the upper-corner bound and the lower Gram term. -/
theorem page_density_posSemidef (P A : Mat) (hP : P * P = P)
    (hPs : star P = P) (hUpper : (P - qgtPlus P A (star A)).PosSemidef) :
    (pageDensityOp P A (star A)).PosSemidef := by
  rw [page_density_eq_cut_sub_curvature hP]
  change (P - (qgtPlus P A (star A) - qgtMinus P A (star A))).PosSemidef
  have heq : P - (qgtPlus P A (star A) - qgtMinus P A (star A)) =
      (P - qgtPlus P A (star A)) + qgtMinus P A (star A) := by abel
  rw [heq]
  exact hUpper.add (lower_sheet_posSemidef P A hPs)

/-- Cyclicity fixes the trace of the D₆₃ density expression. -/
theorem page_density_trace (P A C : Mat) (hP : P * P = P) :
    Matrix.trace (pageDensityOp P A C) = Matrix.trace P := by
  rw [page_density_eq_cut_sub_curvature hP]
  change Matrix.trace (P - (conePlus P A * coneMinus P C -
    coneMinus P C * conePlus P A)) = Matrix.trace P
  rw [Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_mul_comm (conePlus P A) (coneMinus P C), sub_self, sub_zero]

/-- Under the upper-corner bound and unit trace of the projection, the
adjoint-paired Peirce expression is a finite-dimensional density matrix. -/
theorem page_density_is_density_matrix (P A : Mat) (hP : P * P = P)
    (hPs : star P = P) (hUpper : (P - qgtPlus P A (star A)).PosSemidef)
    (hTrace : Matrix.trace P = 1) :
    (pageDensityOp P A (star A)).PosSemidef ∧
      Matrix.trace (pageDensityOp P A (star A)) = 1 := by
  exact ⟨page_density_posSemidef P A hP hPs hUpper,
    (page_density_trace P A (star A) hP).trans hTrace⟩

/-- A bound on the full Peirce Gramian supplies the upper-corner bound. -/
theorem upper_corner_posSemidef_of_metric_bound (P A : Mat) (hP : P * P = P)
    (hPs : star P = P) (hBound : (1 - genV P A (star A)).PosSemidef) :
    (P - qgtPlus P A (star A)).PosSemidef := by
  have hCompress := hBound.conjTranspose_mul_mul_same P
  have hPstar : Pᴴ = P := hPs
  rw [hPstar] at hCompress
  have heq : P * (1 - genV P A (star A)) * P = P - qgtPlus P A (star A) := by
    unfold genV anticomm qgtPlus conePlus coneMinus
    peirce_nf hP
  rw [heq] at hCompress
  exact hCompress

theorem page_density_of_metric_bound (P A : Mat) (hP : P * P = P)
    (hPs : star P = P) (hTrace : Matrix.trace P = 1)
    (hBound : (1 - genV P A (star A)).PosSemidef) :
    (pageDensityOp P A (star A)).PosSemidef ∧
      Matrix.trace (pageDensityOp P A (star A)) = 1 := by
  exact page_density_is_density_matrix P A hP hPs
    (upper_corner_posSemidef_of_metric_bound P A hP hPs hBound) hTrace

/-- A positive residual has a square-root Kraus factor. -/
theorem exists_residual_kraus (P A : Mat)
    (hBound : (1 - genV P A (star A)).PosSemidef) :
    ∃ W : Mat, star W * W = 1 - genV P A (star A) := by
  obtain ⟨W, hW⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hBound.nonneg
  exact ⟨W, hW.symm⟩

/-- The two directed corners used as Kraus operators. -/
def cornerKraus (P A : Mat) : Fin 2 → Mat :=
  ![conePlus P A, coneMinus P (star A)]

/-- Completeness follows from the Peirce Jordan element being the identity. -/
theorem cornerKraus_complete (P A : Mat) (hPs : star P = P)
    (hV : genV P A (star A) = 1) :
    (∑ i, star (cornerKraus P A i) * cornerKraus P A i) = 1 := by
  have hs : star (coneMinus P (star A)) = conePlus P A := by
    rw [← star_conePlus hPs A, star_star]
  simp only [Fin.sum_univ_two, cornerKraus, Matrix.cons_val_zero,
    Matrix.cons_val_one, star_conePlus hPs A, hs]
  change coneMinus P (star A) * conePlus P A +
    conePlus P A * coneMinus P (star A) = 1
  change conePlus P A * coneMinus P (star A) +
    coneMinus P (star A) * conePlus P A = 1 at hV
  rw [add_comm, hV]

theorem cornerKraus_trace_preserving (P A X : Mat) (hPs : star P = P)
    (hV : genV P A (star A) = 1) :
    Matrix.trace (InfoGeometry.Quantum.Choi.krausMap (cornerKraus P A) X) =
      Matrix.trace X :=
  InfoGeometry.Quantum.Choi.trace_krausMap_of_completeness
    (cornerKraus P A) (cornerKraus_complete P A hPs hV) X

theorem cornerKraus_completely_positive (P A : Mat)
    {r : Type*} [Fintype r] [DecidableEq r]
    (X : Matrix (r × n) (r × n) ℂ) (hX : X.PosSemidef) :
    (InfoGeometry.Quantum.KrausAmplification.amplification (r := r)
      (InfoGeometry.Modular.Choi.krausChannel (cornerKraus P A)) X).PosSemidef :=
  InfoGeometry.Quantum.KrausAmplification.amplification_krausChannel_posSemidef
    (cornerKraus P A) X hX

/-- A third Kraus operator supplies the missing part of the completeness
relation when the Peirce Jordan element is below the identity. -/
def cornerKrausWithResidual (P A W : Mat) : Fin 3 → Mat :=
  ![conePlus P A, coneMinus P (star A), W]

theorem cornerKrausWithResidual_complete (P A W : Mat) (hPs : star P = P)
    (hResidual : star W * W = 1 - genV P A (star A)) :
    (∑ i, star (cornerKrausWithResidual P A W i) *
      cornerKrausWithResidual P A W i) = 1 := by
  have hs : star (coneMinus P (star A)) = conePlus P A := by
    rw [← star_conePlus hPs A, star_star]
  rw [Fin.sum_univ_three]
  change star (conePlus P A) * conePlus P A +
    star (coneMinus P (star A)) * coneMinus P (star A) + star W * W = 1
  rw [star_conePlus hPs A, hs, hResidual]
  unfold genV anticomm
  abel

/-- The residual-completed corner map preserves trace. -/
theorem cornerKrausWithResidual_trace (P A W X : Mat) (hPs : star P = P)
    (hResidual : star W * W = 1 - genV P A (star A)) :
    Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
      (cornerKrausWithResidual P A W) X) = Matrix.trace X :=
  InfoGeometry.Quantum.Choi.trace_krausMap_of_completeness
    (cornerKrausWithResidual P A W)
    (cornerKrausWithResidual_complete P A W hPs hResidual) X

theorem cornerKrausWithResidual_completely_positive (P A W : Mat)
    {r : Type*} [Fintype r] [DecidableEq r]
    (X : Matrix (r × n) (r × n) ℂ) (hX : X.PosSemidef) :
    (InfoGeometry.Quantum.KrausAmplification.amplification (r := r)
      (InfoGeometry.Modular.Choi.krausChannel (cornerKrausWithResidual P A W)) X).PosSemidef :=
  InfoGeometry.Quantum.KrausAmplification.amplification_krausChannel_posSemidef
    (cornerKrausWithResidual P A W) X hX

theorem cornerKrausWithResidual_positive (P A W X : Mat) (hX : X.PosSemidef) :
    (InfoGeometry.Quantum.Choi.krausMap (cornerKrausWithResidual P A W) X).PosSemidef := by
  change (∑ i, cornerKrausWithResidual P A W i * X *
    star (cornerKrausWithResidual P A W i)).PosSemidef
  rw [Fin.sum_univ_three]
  exact ((hX.mul_mul_conjTranspose_same _).add
    (hX.mul_mul_conjTranspose_same _)).add (hX.mul_mul_conjTranspose_same _)

/-- A normalized Peirce state remains a density matrix after the
residual-completed corner channel. -/
theorem corner_channel_preserves_page_density (P A W : Mat)
    (hP : P * P = P) (hPs : star P = P)
    (hUpper : (P - qgtPlus P A (star A)).PosSemidef)
    (hTrace : Matrix.trace P = 1)
    (hResidual : star W * W = 1 - genV P A (star A)) :
    (InfoGeometry.Quantum.Choi.krausMap (cornerKrausWithResidual P A W)
      (pageDensityOp P A (star A))).PosSemidef ∧
    Matrix.trace (InfoGeometry.Quantum.Choi.krausMap (cornerKrausWithResidual P A W)
      (pageDensityOp P A (star A))) = 1 := by
  rcases page_density_is_density_matrix P A hP hPs hUpper hTrace with ⟨hPos, hTr⟩
  exact ⟨cornerKrausWithResidual_positive P A W _ hPos,
    (cornerKrausWithResidual_trace P A W _ hPs hResidual).trans hTr⟩

/-- Discrete-time evolution from the Peirce density under the corner channel. -/
def cornerEvolution (P A W : Mat) : ℕ → Mat
  | 0 => pageDensityOp P A (star A)
  | k + 1 => InfoGeometry.Quantum.Choi.krausMap (cornerKrausWithResidual P A W)
      (cornerEvolution P A W k)

theorem cornerEvolution_is_density (P A W : Mat)
    (hP : P * P = P) (hPs : star P = P) (hTrace : Matrix.trace P = 1)
    (hBound : (1 - genV P A (star A)).PosSemidef)
    (hResidual : star W * W = 1 - genV P A (star A)) (k : ℕ) :
    (cornerEvolution P A W k).PosSemidef ∧ Matrix.trace (cornerEvolution P A W k) = 1 := by
  induction k with
  | zero => exact page_density_of_metric_bound P A hP hPs hTrace hBound
  | succ k ih =>
      change (InfoGeometry.Quantum.Choi.krausMap (cornerKrausWithResidual P A W)
        (cornerEvolution P A W k)).PosSemidef ∧
        Matrix.trace (InfoGeometry.Quantum.Choi.krausMap (cornerKrausWithResidual P A W)
          (cornerEvolution P A W k)) = 1
      exact ⟨cornerKrausWithResidual_positive P A W _ ih.1,
        (cornerKrausWithResidual_trace P A W _ hPs hResidual).trans ih.2⟩

/-- The Gramian bound constructs a trace-preserving corner channel and a
discrete family of finite-dimensional density matrices. -/
theorem exists_corner_channel_and_density_evolution (P A : Mat)
    (hP : P * P = P) (hPs : star P = P) (hTrace : Matrix.trace P = 1)
    (hBound : (1 - genV P A (star A)).PosSemidef) :
    ∃ W : Mat, star W * W = 1 - genV P A (star A) ∧
      (∀ X : Mat, Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual P A W) X) = Matrix.trace X) ∧
      (∀ k, (cornerEvolution P A W k).PosSemidef ∧
        Matrix.trace (cornerEvolution P A W k) = 1) := by
  obtain ⟨W, hW⟩ := exists_residual_kraus P A hBound
  exact ⟨W, hW, fun X => cornerKrausWithResidual_trace P A W X hPs hW,
    fun k => cornerEvolution_is_density P A W hP hPs hTrace hBound hW k⟩

/-! ## Proof-carrying finite-matrix state and channel archetypes -/

/-- Hypothesis data required for the Peirce expression to be a normalized
positive matrix state. Positivity of the cut compression is carried as input;
it is not inferred from idempotency alone. -/
def finitePageAdmissibility (input : D63MatrixPageInput n) : Prop :=
  Matrix.trace input.projection = 1 ∧
    (1 - genV input.projection input.amplitude (star input.amplitude)).PosSemidef

/-! An admissible input packages the exact algebraic and positivity conditions
needed by the state theorem. Its underlying data remain ordinary matrices. -/
def FinitePageAdmissibleInput (n : Type*) [Fintype n] [DecidableEq n] :=
  { input : D63MatrixPageInput n // finitePageAdmissibility input }

/-- A concrete admissible Page input in the noncommutative two-by-two
matrix carrier. The projection and amplitude are the existing tilted D₆₃
matrix witnesses; their metric is the identity, so the contraction
complement is positive semidefinite. This proves the admissible archetype
has a genuine noncommuting instance. -/
noncomputable def d63ConcreteFinitePageInput : FinitePageAdmissibleInput (Fin 2) := by
  refine ⟨⟨d63TiltedProjection, d63TiltedAmplitude,
    d63_tilted_projection_is_star_projection⟩, ?_⟩
  constructor
  · norm_num [Matrix.trace, d63TiltedProjection, Fin.sum_univ_two]
  · have hForward : conePlus d63TiltedProjection d63TiltedAmplitude =
        !![(1 / 2 : ℂ), -(1 / 2 : ℂ); (1 / 2 : ℂ), -(1 / 2 : ℂ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [conePlus, d63TiltedProjection, d63TiltedAmplitude,
          Matrix.mul_apply, Fin.sum_univ_two]
    have hBackward : coneMinus d63TiltedProjection d63TiltedAmplitude =
        !![(1 / 2 : ℂ), (1 / 2 : ℂ); -(1 / 2 : ℂ), -(1 / 2 : ℂ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [coneMinus, d63TiltedProjection, d63TiltedAmplitude,
          Matrix.mul_apply, Fin.sum_univ_two]
    have hUpper : qgtPlus d63TiltedProjection d63TiltedAmplitude
        (star d63TiltedAmplitude) = d63TiltedProjection := by
      unfold qgtPlus
      rw [d63_tilted_amplitude_is_selfAdjoint, hForward, hBackward]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [d63TiltedProjection, Matrix.mul_apply, Fin.sum_univ_two]
    have hLower : qgtMinus d63TiltedProjection d63TiltedAmplitude
        (star d63TiltedAmplitude) = 1 - d63TiltedProjection := by
      unfold qgtMinus
      rw [d63_tilted_amplitude_is_selfAdjoint, hForward, hBackward]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [d63TiltedProjection, Matrix.mul_apply, Fin.sum_univ_two]
    have hMetric : genV d63TiltedProjection d63TiltedAmplitude
        (star d63TiltedAmplitude) = 1 := by
      change qgtPlus d63TiltedProjection d63TiltedAmplitude
          (star d63TiltedAmplitude) +
        qgtMinus d63TiltedProjection d63TiltedAmplitude
          (star d63TiltedAmplitude) = 1
      rw [hUpper, hLower]
      simp
    rw [hMetric]
    simp
    exact Matrix.PosSemidef.zero

/-- The proof-carrying finite Page-state input is inhabited by a concrete
noncommuting matrix pair, so its universal density theorem is not vacuous. -/
theorem d63_finite_page_admissible_input_nonempty :
    Nonempty (FinitePageAdmissibleInput (Fin 2)) :=
  ⟨d63ConcreteFinitePageInput⟩

/-- A scaled version of the tilted amplitude gives an interior, rather than
endpoint, example for the finite Page-state defect. -/
def d63InteriorPageAmplitude : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 / 2 : ℂ), 1 / 2; 1 / 2, -(1 / 2 : ℂ)]

theorem d63_interior_page_metric_value :
    genV d63TiltedProjection d63InteriorPageAmplitude
      (star d63InteriorPageAmplitude) =
      !![(1 / 4 : ℂ), 0; 0, 1 / 4] := by
  have hStar : star d63InteriorPageAmplitude = d63InteriorPageAmplitude := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d63InteriorPageAmplitude, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply]
  have hForward : conePlus d63TiltedProjection d63InteriorPageAmplitude =
      !![(1 / 4 : ℂ), -(1 / 4 : ℂ); (1 / 4 : ℂ), -(1 / 4 : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [conePlus, d63TiltedProjection, d63InteriorPageAmplitude,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hBackward : coneMinus d63TiltedProjection d63InteriorPageAmplitude =
      !![(1 / 4 : ℂ), 1 / 4; -(1 / 4 : ℂ), -(1 / 4 : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [coneMinus, d63TiltedProjection, d63InteriorPageAmplitude,
        Matrix.mul_apply, Fin.sum_univ_two]
  unfold genV anticomm
  rw [hStar, hForward, hBackward]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem d63_interior_page_density_value :
    pageDensityOp d63TiltedProjection d63InteriorPageAmplitude
      (star d63InteriorPageAmplitude) =
      !![(1 / 2 : ℂ), 1 / 4; 1 / 4, 1 / 2] := by
  have hStar : star d63InteriorPageAmplitude = d63InteriorPageAmplitude := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d63InteriorPageAmplitude, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply]
  have hForward : conePlus d63TiltedProjection d63InteriorPageAmplitude =
      !![(1 / 4 : ℂ), -(1 / 4 : ℂ); (1 / 4 : ℂ), -(1 / 4 : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [conePlus, d63TiltedProjection, d63InteriorPageAmplitude,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hBackward : coneMinus d63TiltedProjection d63InteriorPageAmplitude =
      !![(1 / 4 : ℂ), 1 / 4; -(1 / 4 : ℂ), -(1 / 4 : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [coneMinus, d63TiltedProjection, d63InteriorPageAmplitude,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hQplus : qgtPlus d63TiltedProjection d63InteriorPageAmplitude
      (star d63InteriorPageAmplitude) =
      !![(1 / 8 : ℂ), 1 / 8; 1 / 8, 1 / 8] := by
    unfold qgtPlus
    rw [hStar, hForward, hBackward]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hQminus : qgtMinus d63TiltedProjection d63InteriorPageAmplitude
      (star d63InteriorPageAmplitude) =
      !![(1 / 8 : ℂ), -(1 / 8 : ℂ); -(1 / 8 : ℂ), 1 / 8] := by
    unfold qgtMinus
    rw [hStar, hForward, hBackward]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hP : d63TiltedProjection * d63TiltedProjection =
      d63TiltedProjection :=
    d63_tilted_projection_is_star_projection.isIdempotentElem
  rw [page_density_eq_cut_sub_curvature hP]
  change d63TiltedProjection -
    (qgtPlus d63TiltedProjection d63InteriorPageAmplitude
        (star d63InteriorPageAmplitude) -
      qgtMinus d63TiltedProjection d63InteriorPageAmplitude
        (star d63InteriorPageAmplitude)) = _
  rw [hQplus, hQminus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, d63TiltedProjection]

theorem d63_interior_page_impurity_value :
    pageImpurity d63TiltedProjection d63InteriorPageAmplitude
      (star d63InteriorPageAmplitude) =
      !![(3 / 16 : ℂ), 0; 0, 3 / 16] := by
  unfold pageImpurity
  rw [d63_interior_page_density_value]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem d63_interior_page_impurity_nonzero :
    pageImpurity d63TiltedProjection d63InteriorPageAmplitude
      (star d63InteriorPageAmplitude) ≠ 0 := by
  rw [d63_interior_page_impurity_value]
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  norm_num at h00

theorem d63_interior_page_input_noncommuting :
    d63TiltedProjection * d63InteriorPageAmplitude ≠
      d63InteriorPageAmplitude * d63TiltedProjection := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  norm_num [d63TiltedProjection, d63InteriorPageAmplitude,
    Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- A trace-one star projection and a noncommuting amplitude with strictly
positive metric complement give a genuine intermediate finite Page defect. -/
noncomputable def d63InteriorFinitePageInput : FinitePageAdmissibleInput (Fin 2) := by
  refine ⟨⟨d63TiltedProjection, d63InteriorPageAmplitude,
    d63_tilted_projection_is_star_projection⟩, ?_⟩
  constructor
  · norm_num [Matrix.trace, d63TiltedProjection, Fin.sum_univ_two]
  · rw [d63_interior_page_metric_value]
    have hdiag : (1 : Matrix (Fin 2) (Fin 2) ℂ) -
        !![(1 / 4 : ℂ), 0; 0, 1 / 4] =
        Matrix.diagonal (fun _ : Fin 2 => (3 / 4 : ℂ)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num
    rw [hdiag]
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> positivity

def finitePageDensityClaim (input : FinitePageAdmissibleInput n) : Prop :=
  (pageDensityOp input.val.projection input.val.amplitude
    (star input.val.amplitude)).PosSemidef ∧
    Matrix.trace (pageDensityOp input.val.projection input.val.amplitude
      (star input.val.amplitude)) = 1

theorem finitePageDensityClaim_proved (input : FinitePageAdmissibleInput n) :
    finitePageDensityClaim input := by
  rcases input.property with ⟨hTrace, hBound⟩
  have hIdem := input.val.projectionStar.isIdempotentElem
  have hStar := IsStarProjection.isSelfAdjoint input.val.projectionStar
  exact page_density_of_metric_bound input.val.projection input.val.amplitude
    hIdem hStar hTrace hBound

def finitePageChannelEvolutionClaim (input : FinitePageAdmissibleInput n) : Prop :=
    ∃ W : Matrix n n ℂ,
      star W * W = 1 - genV input.val.projection input.val.amplitude
        (star input.val.amplitude) ∧
      (∀ X : Matrix n n ℂ,
        Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
          (cornerKrausWithResidual input.val.projection input.val.amplitude W) X) =
            Matrix.trace X) ∧
      (∀ k, (cornerEvolution input.val.projection input.val.amplitude W k).PosSemidef ∧
        Matrix.trace (cornerEvolution input.val.projection input.val.amplitude W k) = 1) ∧
      (∀ (r : Type) [Fintype r] [DecidableEq r]
        (X : Matrix (r × n) (r × n) ℂ) (_hX : X.PosSemidef),
        (InfoGeometry.Quantum.KrausAmplification.amplification (r := r)
          (InfoGeometry.Modular.Choi.krausChannel
            (cornerKrausWithResidual input.val.projection input.val.amplitude W)) X).PosSemidef)

theorem finitePageChannelEvolutionClaim_proved
    (input : FinitePageAdmissibleInput n) : finitePageChannelEvolutionClaim input := by
  rcases input.property with ⟨hTrace, hBound⟩
  have hIdem := input.val.projectionStar.isIdempotentElem
  have hStar := IsStarProjection.isSelfAdjoint input.val.projectionStar
  rcases exists_corner_channel_and_density_evolution input.val.projection input.val.amplitude
      hIdem hStar hTrace hBound with ⟨W, hW, hTracePreserving, hEvolution⟩
  refine ⟨W, hW, hTracePreserving, hEvolution, ?_⟩
  intro r _ _ X hX
  exact cornerKrausWithResidual_completely_positive
    input.val.projection input.val.amplitude W X hX

theorem d63_interior_page_input_has_nonzero_impurity_and_channel :
    finitePageDensityClaim d63InteriorFinitePageInput ∧
    finitePageChannelEvolutionClaim d63InteriorFinitePageInput ∧
    pageImpurity d63TiltedProjection d63InteriorPageAmplitude
      (star d63InteriorPageAmplitude) ≠ 0 ∧
    d63TiltedProjection * d63InteriorPageAmplitude ≠
      d63InteriorPageAmplitude * d63TiltedProjection := by
  exact ⟨finitePageDensityClaim_proved _, finitePageChannelEvolutionClaim_proved _,
    d63_interior_page_impurity_nonzero, d63_interior_page_input_noncommuting⟩

/-- Concrete interior Page-defect archetype: normalized positive matrix state,
trace-preserving completely positive channel evolution, nonzero algebraic
impurity, and a genuinely noncommuting cut-amplitude pair. -/
def d63InteriorPageDefectArchetype : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.d63InteriorPageDefectArchetype
  phase := 63
  claim := fun _ =>
    finitePageDensityClaim d63InteriorFinitePageInput ∧
      finitePageChannelEvolutionClaim d63InteriorFinitePageInput ∧
      pageImpurity d63TiltedProjection d63InteriorPageAmplitude
        (star d63InteriorPageAmplitude) ≠ 0 ∧
      d63TiltedProjection * d63InteriorPageAmplitude ≠
        d63InteriorPageAmplitude * d63TiltedProjection
  evidence := fun _ => d63_interior_page_input_has_nonzero_impurity_and_channel

#register_archetype d63InteriorPageDefectArchetype
#audit_archetype d63InteriorPageDefectArchetype

/-- On the subtype of admissible matrix data, the Page-state operator is a
genuine finite-dimensional density matrix. -/
def finitePageDensityArchetype :
    TypedArchetype (FinitePageAdmissibleInput n) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.finitePageDensityArchetype
  phase := 63
  claim := finitePageDensityClaim
  evidence := finitePageDensityClaim_proved

/-- With the same certified metric bound, the state admits a residual Kraus
completion whose channel preserves trace and whose iterates remain density
matrices. -/
def finitePageChannelEvolutionArchetype :
    TypedArchetype (FinitePageAdmissibleInput n) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum.finitePageChannelEvolutionArchetype
  phase := 63
  claim := finitePageChannelEvolutionClaim
  evidence := finitePageChannelEvolutionClaim_proved

#register_archetype finitePageDensityArchetype
#audit_archetype finitePageDensityArchetype
#register_archetype finitePageChannelEvolutionArchetype
#audit_archetype finitePageChannelEvolutionArchetype

end InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum

end
