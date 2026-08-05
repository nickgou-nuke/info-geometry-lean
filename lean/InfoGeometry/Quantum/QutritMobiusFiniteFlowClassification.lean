import InfoGeometry.Quantum.QutritMobiusTripotentOrientationBridge
import InfoGeometry.Topology.MobiusClassification
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Exact finite classification of the qutrit-indexed Möbius flows

This module exponentiates the canonical elliptic/parabolic/hyperbolic generator
triad and proves exact finite formulas in the repository's `SL2C` classifier.
The finite actions are a rotation with its honest Riemann-sphere pole branch, a
translation, and a positive split scaling. Squared trace separates the three
nontrivial sectors and supplies a native conjugacy obstruction.

The qutrit remains an index for these three real sectors. No loxodromic sector,
anyon representation, or spacetime-orientation claim is introduced here.
-/

/-! Scratch owner for exact finite qutrit-indexed Möbius flows. -/

noncomputable section

open scoped Matrix.Norms.Operator

namespace InfoGeometry.Quantum.QutritMobiusFiniteFlowClassification

open InfoGeometry.Geometry
open InfoGeometry.Canonical.MatrixDetExpTraceJacobi
open InfoGeometry.Quantum.QutritMobiusTripotentOrientationBridge

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

private lemma smul_pow_even_of_sq_eq_one
    {S : Type*} [NormedRing S] [NormedAlgebra ℂ S]
    (G : S) (hSq : G * G = (1 : S)) (t : ℂ) :
    ∀ n : ℕ, (t • G) ^ (2 * n) = (t ^ (2 * n)) • (1 : S)
  | 0 => by simp
  | n + 1 => by
      have hpow2 : (t • G) ^ 2 = (t ^ 2) • (1 : S) := by
        rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, hSq]
        simp [pow_two]
      calc
        (t • G) ^ (2 * (n + 1)) = (t • G) ^ (2 * n) * (t • G) ^ 2 := by
          rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
        _ = ((t ^ (2 * n)) • (1 : S)) * ((t ^ 2) • (1 : S)) := by
          rw [smul_pow_even_of_sq_eq_one G hSq t n, hpow2]
        _ = (t ^ (2 * (n + 1))) • (1 : S) := by
          rw [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, ← pow_add]
          simp [show 2 * (n + 1) = 2 * n + 2 by omega]

private lemma smul_pow_odd_of_sq_eq_one
    {S : Type*} [NormedRing S] [NormedAlgebra ℂ S]
    (G : S) (hSq : G * G = (1 : S)) (t : ℂ) (n : ℕ) :
    (t • G) ^ (2 * n + 1) = (t ^ (2 * n + 1)) • G := by
  calc
    (t • G) ^ (2 * n + 1) = (t • G) ^ (2 * n) * (t • G) := by rw [pow_succ]
    _ = ((t ^ (2 * n)) • (1 : S)) * (t • G) := by
      rw [smul_pow_even_of_sq_eq_one G hSq t n]
    _ = (t ^ (2 * n + 1)) • G := by
      rw [smul_mul_assoc, one_mul, smul_smul]
      simp [pow_succ]

private lemma smul_pow_even_of_sq_eq_neg_one
    {S : Type*} [NormedRing S] [NormedAlgebra ℂ S]
    (G : S) (hSq : G * G = -(1 : S)) (t : ℂ) :
    ∀ n : ℕ, (t • G) ^ (2 * n) = ((-1 : ℂ) ^ n * t ^ (2 * n)) • (1 : S)
  | 0 => by simp
  | n + 1 => by
      have hpow2 : (t • G) ^ 2 = ((-1 : ℂ) * t ^ 2) • (1 : S) := by
        calc
          (t • G) ^ 2 = (t • G) * (t • G) := by simp [pow_two]
          _ = (t * t) • (G * G) := by rw [smul_mul_assoc, mul_smul_comm, smul_smul]
          _ = (t ^ 2) • (-(1 : S)) := by simp [hSq, pow_two]
          _ = ((-1 : ℂ) * t ^ 2) • (1 : S) := by simp
      calc
        (t • G) ^ (2 * (n + 1)) = (t • G) ^ (2 * n) * (t • G) ^ 2 := by
          rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
        _ = (((-1 : ℂ) ^ n * t ^ (2 * n)) • (1 : S)) *
            (((-1 : ℂ) * t ^ 2) • (1 : S)) := by
          rw [smul_pow_even_of_sq_eq_neg_one G hSq t n, hpow2]
        _ = ((-1 : ℂ) ^ (n + 1) * t ^ (2 * (n + 1))) • (1 : S) := by
          rw [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul]
          congr 1
          rw [pow_succ, show t ^ (2 * (n + 1)) = t ^ (2 * n) * t ^ 2 by
            rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]]
          ring

private lemma smul_pow_odd_of_sq_eq_neg_one
    {S : Type*} [NormedRing S] [NormedAlgebra ℂ S]
    (G : S) (hSq : G * G = -(1 : S)) (t : ℂ) (n : ℕ) :
    (t • G) ^ (2 * n + 1) = ((-1 : ℂ) ^ n * t ^ (2 * n + 1)) • G := by
  calc
    (t • G) ^ (2 * n + 1) = (t • G) ^ (2 * n) * (t • G) := by rw [pow_succ]
    _ = (((-1 : ℂ) ^ n * t ^ (2 * n)) • (1 : S)) * (t • G) := by
      rw [smul_pow_even_of_sq_eq_neg_one G hSq t n]
    _ = ((-1 : ℂ) ^ n * t ^ (2 * n + 1)) • G := by
      rw [smul_mul_assoc, one_mul, smul_smul]
      congr 1
      rw [pow_succ]
      ring

private theorem exp_eq_cosh_add_sinh_of_sq_eq_one
    {S : Type*} [NormedRing S] [NormedAlgebra ℂ S] [CompleteSpace S]
    {G : S} (hSq : G * G = (1 : S)) (t : ℂ) :
    NormedSpace.exp (t • G) = Complex.cosh t • (1 : S) + Complex.sinh t • G := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  have hsum : HasSum
      (fun n : ℕ => ((Nat.factorial n : ℕ) : ℂ)⁻¹ • (t • G) ^ n)
      (Complex.cosh t • (1 : S) + Complex.sinh t • G) := by
    refine HasSum.even_add_odd ?_ ?_
    · convert (Complex.hasSum_cosh t).smul_const (1 : S) using 1
      ext n
      rw [smul_pow_even_of_sq_eq_one G hSq t n]
      simp [div_eq_mul_inv, smul_smul, mul_comm]
    · convert (Complex.hasSum_sinh t).smul_const G using 1
      ext n
      rw [smul_pow_odd_of_sq_eq_one G hSq t n]
      simp [div_eq_mul_inv, smul_smul, mul_comm]
  exact hsum.tsum_eq

private theorem exp_eq_cos_add_sin_of_sq_eq_neg_one
    {S : Type*} [NormedRing S] [NormedAlgebra ℂ S] [CompleteSpace S]
    {G : S} (hSq : G * G = -(1 : S)) (t : ℂ) :
    NormedSpace.exp (t • G) = Complex.cos t • (1 : S) + Complex.sin t • G := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  have hsum : HasSum
      (fun n : ℕ => ((Nat.factorial n : ℕ) : ℂ)⁻¹ • (t • G) ^ n)
      (Complex.cos t • (1 : S) + Complex.sin t • G) := by
    refine HasSum.even_add_odd ?_ ?_
    · convert (Complex.hasSum_cos t).smul_const (1 : S) using 1
      ext n
      rw [smul_pow_even_of_sq_eq_neg_one G hSq t n]
      simp [div_eq_mul_inv, smul_smul, mul_comm]
    · convert (Complex.hasSum_sin t).smul_const G using 1
      ext n
      rw [smul_pow_odd_of_sq_eq_neg_one G hSq t n]
      simp [div_eq_mul_inv, smul_smul, mul_comm]
  exact hsum.tsum_eq

private theorem exp_eq_one_add_of_sq_eq_zero
    {S : Type*} [NormedRing S] [NormedAlgebra ℂ S] [CompleteSpace S]
    {G : S} (hSq : G * G = 0) (t : ℂ) :
    NormedSpace.exp (t • G) = (1 : S) + t • G := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  change (∑' n : ℕ, ((Nat.factorial n : ℕ) : ℂ)⁻¹ • (t • G) ^ n) = _
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.range, pow_zero, pow_one, add_comm]
  · intro n hn
    have h2n : 2 ≤ n := by simpa using hn
    have hpow2 : (t • G) ^ 2 = 0 := by
      rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, hSq, smul_zero]
    rw [pow_eq_zero_of_le h2n hpow2, smul_zero]

private theorem generator_sq_elliptic :
    (qutritMobiusGenerator 0).matrix * (qutritMobiusGenerator 0).matrix = -(1 : M2C) := by
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A.map Complex.ofRealHom)
    (qutritMobiusOperator_sq (0 : Fin 3))
  dsimp only at h
  rw [Matrix.map_mul] at h
  simp only [qutritOpSquareClass,
    InfoGeometry.Clifford.OpSquareTriadBridge.opSquareScalar, neg_smul, one_smul] at h
  have hrhs : (-(1 : Matrix (Fin 2) (Fin 2) ℝ)).map Complex.ofRealHom = -(1 : M2C) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hrhs] at h
  rw [qutritMobiusGenerator_matrix_eq_operator]
  simpa [complexifyRealMat2, qutritOpSquareClass,
    InfoGeometry.Clifford.OpSquareTriadBridge.opSquareScalar, Matrix.map_one] using h

private theorem generator_sq_parabolic :
    (qutritMobiusGenerator 1).matrix * (qutritMobiusGenerator 1).matrix = (0 : M2C) := by
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A.map Complex.ofRealHom)
    (qutritMobiusOperator_sq (1 : Fin 3))
  dsimp only at h
  rw [Matrix.map_mul] at h
  rw [qutritMobiusGenerator_matrix_eq_operator]
  simpa [complexifyRealMat2, qutritOpSquareClass,
    InfoGeometry.Clifford.OpSquareTriadBridge.opSquareScalar, Matrix.map_one] using h

private theorem generator_sq_hyperbolic :
    (qutritMobiusGenerator 2).matrix * (qutritMobiusGenerator 2).matrix = (1 : M2C) := by
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A.map Complex.ofRealHom)
    (qutritMobiusOperator_sq (2 : Fin 3))
  dsimp only at h
  rw [Matrix.map_mul] at h
  rw [qutritMobiusGenerator_matrix_eq_operator]
  simpa [complexifyRealMat2, qutritOpSquareClass,
    InfoGeometry.Clifford.OpSquareTriadBridge.opSquareScalar, Matrix.map_one] using h

/-- Elliptic finite flow in the qutrit Möbius triad. -/
def ellipticMatrixFlow (t : ℝ) : M2C := qutritMobiusMatrixFlow 0 (t : ℂ)

/-- Parabolic finite flow in the qutrit Möbius triad. -/
def parabolicMatrixFlow (t : ℝ) : M2C := qutritMobiusMatrixFlow 1 (t : ℂ)

/-- Hyperbolic finite flow in the qutrit Möbius triad. -/
def hyperbolicMatrixFlow (t : ℝ) : M2C := qutritMobiusMatrixFlow 2 (t : ℂ)

/-- Exact trigonometric closed form of the elliptic matrix exponential. -/
theorem ellipticMatrixFlow_closedForm (t : ℝ) :
    ellipticMatrixFlow t =
      (Real.cos t : ℂ) • (1 : M2C) + (Real.sin t : ℂ) • (qutritMobiusGenerator 0).matrix := by
  simpa [ellipticMatrixFlow, qutritMobiusMatrixFlow, matrixExpFlow] using
    (exp_eq_cos_add_sin_of_sq_eq_neg_one generator_sq_elliptic (t : ℂ))

/-- Exact polynomial closed form of the square-zero parabolic exponential. -/
theorem parabolicMatrixFlow_closedForm (t : ℝ) :
    parabolicMatrixFlow t = (1 : M2C) + (t : ℂ) • (qutritMobiusGenerator 1).matrix := by
  simpa [parabolicMatrixFlow, qutritMobiusMatrixFlow, matrixExpFlow] using
    (exp_eq_one_add_of_sq_eq_zero generator_sq_parabolic (t : ℂ))

/-- Exact hyperbolic closed form of the involutive matrix exponential. -/
theorem hyperbolicMatrixFlow_closedForm (t : ℝ) :
    hyperbolicMatrixFlow t =
      (Real.cosh t : ℂ) • (1 : M2C) +
        (Real.sinh t : ℂ) • (qutritMobiusGenerator 2).matrix := by
  simpa [hyperbolicMatrixFlow, qutritMobiusMatrixFlow, matrixExpFlow] using
    (exp_eq_cosh_add_sinh_of_sq_eq_one generator_sq_hyperbolic (t : ℂ))


/-- Elliptic flow as a determinant-one finite Möbius matrix. -/
def ellipticFinite (t : ℝ) : InfoGeometry.SL2C :=
  ⟨ellipticMatrixFlow t, by
    simpa [ellipticMatrixFlow] using qutritMobiusMatrixFlow_det 0 (t : ℂ)⟩

/-- Parabolic flow as a determinant-one finite Möbius matrix. -/
def parabolicFinite (t : ℝ) : InfoGeometry.SL2C :=
  ⟨parabolicMatrixFlow t, by
    simpa [parabolicMatrixFlow] using qutritMobiusMatrixFlow_det 1 (t : ℂ)⟩

/-- Hyperbolic flow as a determinant-one finite Möbius matrix. -/
def hyperbolicFinite (t : ℝ) : InfoGeometry.SL2C :=
  ⟨hyperbolicMatrixFlow t, by
    simpa [hyperbolicMatrixFlow] using qutritMobiusMatrixFlow_det 2 (t : ℂ)⟩

private theorem ellipticGenerator_diag_zero :
    complexifyRealMat2 !![0, -1; 1, 0] 0 0 = 0 := by
  norm_num [complexifyRealMat2, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private theorem ellipticGenerator_diag_one :
    complexifyRealMat2 !![0, -1; 1, 0] 1 1 = 0 := by
  norm_num [complexifyRealMat2, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private theorem parabolicGenerator_trace_zero :
    complexifyRealMat2 !![0, 1; 0, 0] 0 0 = 0 ∧
      complexifyRealMat2 !![0, 1; 0, 0] 1 1 = 0 := by
  constructor <;> norm_num [complexifyRealMat2, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]

private theorem parabolicGenerator_offdiag_re_ne_zero :
    (complexifyRealMat2 (qutritMobiusOperator 1) 0 1).re ≠ 0 := by
  norm_num [complexifyRealMat2, qutritMobiusOperator, qutritOpSquareClass,
    InfoGeometry.Clifford.OpSquareTriadBridge.opSquareMatrix,
    InfoGeometry.Algebra.HypercomplexTriad.N]

private theorem hyperbolicGenerator_diag_zero :
    complexifyRealMat2 !![1, 0; 0, -1] 0 1 = 0 ∧
      complexifyRealMat2 !![1, 0; 0, -1] 1 0 = 0 := by
  constructor <;> norm_num [complexifyRealMat2, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]

theorem ellipticFinite_traceSq (t : ℝ) :
    InfoGeometry.traceSq (ellipticFinite t) = (4 * Real.cos t ^ 2 : ℝ) := by
  change Matrix.trace (ellipticMatrixFlow t) ^ 2 = _
  rw [ellipticMatrixFlow_closedForm, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul]
  norm_num [Matrix.trace_one, Matrix.trace_fin_two, qutritMobiusGenerator,
    sl2C.matrix, qutritMobiusOperator, qutritOpSquareClass,
    Clifford.OpSquareTriadBridge.opSquareMatrix,
    InfoGeometry.Algebra.HypercomplexTriad.I, complexifyRealMat2,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons, ellipticGenerator_diag_zero,
    ellipticGenerator_diag_one]
  ring

theorem parabolicFinite_traceSq (t : ℝ) :
    InfoGeometry.traceSq (parabolicFinite t) = 4 := by
  change Matrix.trace (parabolicMatrixFlow t) ^ 2 = _
  rw [parabolicMatrixFlow_closedForm, Matrix.trace_add, Matrix.trace_smul]
  norm_num [Matrix.trace_one, Matrix.trace_fin_two, qutritMobiusGenerator,
    sl2C.matrix, qutritMobiusOperator, qutritOpSquareClass,
    Clifford.OpSquareTriadBridge.opSquareMatrix,
    InfoGeometry.Algebra.HypercomplexTriad.N, complexifyRealMat2,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons, parabolicGenerator_trace_zero]

theorem hyperbolicFinite_traceSq (t : ℝ) :
    InfoGeometry.traceSq (hyperbolicFinite t) = (4 * Real.cosh t ^ 2 : ℝ) := by
  change Matrix.trace (hyperbolicMatrixFlow t) ^ 2 = _
  rw [hyperbolicMatrixFlow_closedForm, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul]
  norm_num [Matrix.trace_one, Matrix.trace_fin_two, qutritMobiusGenerator,
    sl2C.matrix, qutritMobiusOperator, qutritOpSquareClass,
    Clifford.OpSquareTriadBridge.opSquareMatrix,
    InfoGeometry.Algebra.HypercomplexTriad.E, complexifyRealMat2,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons, hyperbolicGenerator_diag_zero]
  ring

/-- Nontrivial rotations are elliptic in the canonical finite trace-square classifier. -/
theorem ellipticFinite_isElliptic {t : ℝ} (ht : Real.sin t ≠ 0) :
    InfoGeometry.IsElliptic (ellipticFinite t) := by
  refine ⟨4 * Real.cos t ^ 2, by positivity, ?_, ellipticFinite_traceSq t⟩
  have hs : 0 < Real.sin t ^ 2 := sq_pos_of_ne_zero ht
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- Every nonzero unipotent translation flow is parabolic. -/
theorem parabolicFinite_isParabolic {t : ℝ} (ht : t ≠ 0) :
    InfoGeometry.IsParabolic (parabolicFinite t) := by
  refine ⟨parabolicFinite_traceSq t, ?_, ?_⟩
  · intro h
    have h01 := congr_fun (congr_fun h (0 : Fin 2)) (1 : Fin 2)
    change parabolicMatrixFlow t 0 1 = (1 : M2C) 0 1 at h01
    rw [parabolicMatrixFlow_closedForm] at h01
    have hreal := congrArg Complex.re h01
    norm_num [qutritMobiusGenerator, sl2C.matrix, sl2C.ofCoords] at hreal
    exact ht hreal
  · intro h
    have h01 := congr_fun (congr_fun h (0 : Fin 2)) (1 : Fin 2)
    change parabolicMatrixFlow t 0 1 = (-1 : M2C) 0 1 at h01
    rw [parabolicMatrixFlow_closedForm] at h01
    have hreal := congrArg Complex.re h01
    norm_num [qutritMobiusGenerator, sl2C.matrix, sl2C.ofCoords] at hreal
    exact ht hreal

/-- Every nonzero split-scaling flow is hyperbolic. -/
theorem hyperbolicFinite_isHyperbolic {t : ℝ} (ht : t ≠ 0) :
    InfoGeometry.IsHyperbolic (hyperbolicFinite t) := by
  refine ⟨4 * Real.cosh t ^ 2, ?_, hyperbolicFinite_traceSq t⟩
  have hc : 1 < Real.cosh t := Real.one_lt_cosh.mpr ht
  nlinarith

/-- The global elliptic Möbius flow on the Riemann sphere. -/
def ellipticTransform (t : ℝ) : InfoGeometry.MobiusTransform :=
  qutritMobiusTransform 0 (t : ℂ)

/-- The global parabolic Möbius flow on the Riemann sphere. -/
def parabolicTransform (t : ℝ) : InfoGeometry.MobiusTransform :=
  qutritMobiusTransform 1 (t : ℂ)

/-- The global hyperbolic Möbius flow on the Riemann sphere. -/
def hyperbolicTransform (t : ℝ) : InfoGeometry.MobiusTransform :=
  qutritMobiusTransform 2 (t : ℂ)

/-- Exact affine-chart formula for the elliptic flow, including its pole branch. -/
theorem ellipticTransform_eval_some (t : ℝ) (z : ℂ) :
    (ellipticTransform t).eval (some z) =
      if (Real.sin t : ℂ) * z + Real.cos t = 0 then none
      else some (((Real.cos t : ℂ) * z - Real.sin t) /
        ((Real.sin t : ℂ) * z + Real.cos t)) := by
  rw [InfoGeometry.MobiusTransform.eval]
  change (if ellipticMatrixFlow t 1 0 * z + ellipticMatrixFlow t 1 1 = 0 then none
    else some ((ellipticMatrixFlow t 0 0 * z + ellipticMatrixFlow t 0 1) /
      (ellipticMatrixFlow t 1 0 * z + ellipticMatrixFlow t 1 1))) = _
  rw [ellipticMatrixFlow_closedForm]
  simp [qutritMobiusGenerator, sl2C.matrix, sl2C.ofCoords, sl2C.a, sl2C.b,
    sl2C.c, sub_eq_add_neg]

/-- Exact affine translation generated by the parabolic Möbius operator. -/
theorem parabolicTransform_eval_some (t : ℝ) (z : ℂ) :
    (parabolicTransform t).eval (some z) = some (z + (t : ℂ)) := by
  rw [InfoGeometry.MobiusTransform.eval]
  change (if parabolicMatrixFlow t 1 0 * z + parabolicMatrixFlow t 1 1 = 0 then none
    else some ((parabolicMatrixFlow t 0 0 * z + parabolicMatrixFlow t 0 1) /
      (parabolicMatrixFlow t 1 0 * z + parabolicMatrixFlow t 1 1))) = _
  rw [parabolicMatrixFlow_closedForm]
  simp [qutritMobiusGenerator, sl2C.matrix, sl2C.ofCoords, sl2C.a, sl2C.b,
    sl2C.c]

private theorem cosh_sub_sinh_ne_zero (t : ℝ) : Real.cosh t - Real.sinh t ≠ 0 := by
  rw [Real.cosh_sub_sinh]
  exact (Real.exp_pos (-t)).ne'

/-- Exact affine scaling generated by the hyperbolic Möbius operator. -/
theorem hyperbolicTransform_eval_some (t : ℝ) (z : ℂ) :
    (hyperbolicTransform t).eval (some z) = some ((Real.exp (2 * t) : ℂ) * z) := by
  rw [InfoGeometry.MobiusTransform.eval]
  change (if hyperbolicMatrixFlow t 1 0 * z + hyperbolicMatrixFlow t 1 1 = 0 then none
    else some ((hyperbolicMatrixFlow t 0 0 * z + hyperbolicMatrixFlow t 0 1) /
      (hyperbolicMatrixFlow t 1 0 * z + hyperbolicMatrixFlow t 1 1))) = _
  have hden : Complex.cosh (t : ℂ) - Complex.sinh (t : ℂ) ≠ 0 := by
    rw [Complex.cosh_sub_sinh]
    exact Complex.exp_ne_zero (-(t : ℂ))
  have hdenExpr :
      hyperbolicMatrixFlow t 1 0 * z + hyperbolicMatrixFlow t 1 1 =
        Complex.cosh (t : ℂ) - Complex.sinh (t : ℂ) := by
    rw [hyperbolicMatrixFlow_closedForm]
    simp [qutritMobiusGenerator, sl2C.matrix, sl2C.ofCoords, sl2C.a, sl2C.b,
      sl2C.c, sub_eq_add_neg]
  have hnumExpr :
      hyperbolicMatrixFlow t 0 0 * z + hyperbolicMatrixFlow t 0 1 =
        (Complex.cosh (t : ℂ) + Complex.sinh (t : ℂ)) * z := by
    rw [hyperbolicMatrixFlow_closedForm]
    simp [qutritMobiusGenerator, sl2C.matrix, sl2C.ofCoords, sl2C.a, sl2C.b,
      sl2C.c]
  rw [hdenExpr, if_neg hden, hnumExpr]
  congr 1
  rw [Complex.cosh_add_sinh, Complex.cosh_sub_sinh]
  have hinv : (Complex.exp (-(t : ℂ)))⁻¹ = Complex.exp (t : ℂ) := by
    rw [Complex.exp_neg]
    simp
  rw [div_eq_mul_inv, hinv]
  calc
    Complex.exp (t : ℂ) * z * Complex.exp (t : ℂ) =
        z * (Complex.exp (t : ℂ) * Complex.exp (t : ℂ)) := by ring
    _ = z * Complex.exp ((t : ℂ) + t) := by rw [Complex.exp_add]
    _ = Complex.exp (2 * (t : ℂ)) * z := by
      have harg : (t : ℂ) + t = 2 * (t : ℂ) := by ring
      rw [harg]
      ring
    _ = (Real.exp (2 * t) : ℂ) * z := by simp

/-- Matrix conjugacy with an explicit inverse relation, sufficient for trace invariance. -/
def MatrixConjugate (A B : InfoGeometry.SL2C) : Prop :=
  ∃ P Q : M2C, Q * P = 1 ∧ A.val = P * B.val * Q

/-- The canonical squared trace is invariant under matrix conjugacy. -/
theorem traceSq_eq_of_matrixConjugate {A B : InfoGeometry.SL2C}
    (h : MatrixConjugate A B) : InfoGeometry.traceSq A = InfoGeometry.traceSq B := by
  rcases h with ⟨P, Q, hQP, hA⟩
  unfold InfoGeometry.traceSq
  congr 1
  calc
    Matrix.trace A.val = Matrix.trace (P * B.val * Q) := by rw [hA]
    _ = Matrix.trace (Q * (P * B.val)) := Matrix.trace_mul_comm (P * B.val) Q
    _ = Matrix.trace ((Q * P) * B.val) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace B.val := by rw [hQP, one_mul]

private theorem not_elliptic_of_traceSq_eq_four {A : InfoGeometry.SL2C}
    (hfour : InfoGeometry.traceSq A = 4) : ¬ InfoGeometry.IsElliptic A := by
  intro hA
  rcases hA with ⟨r, _, hr, htrace⟩
  have hcast : (r : ℂ) = 4 := by rw [← htrace, hfour]
  have : r = 4 := Complex.ofReal_injective hcast
  linarith

private theorem not_hyperbolic_of_traceSq_eq_four {A : InfoGeometry.SL2C}
    (hfour : InfoGeometry.traceSq A = 4) : ¬ InfoGeometry.IsHyperbolic A := by
  intro hA
  rcases hA with ⟨r, hr, htrace⟩
  have hcast : (r : ℂ) = 4 := by rw [← htrace, hfour]
  have : r = 4 := Complex.ofReal_injective hcast
  linarith

/-- Elliptic and parabolic finite Möbius transformations cannot be conjugate. -/
theorem not_matrixConjugate_of_elliptic_parabolic
    {A B : InfoGeometry.SL2C}
    (hA : InfoGeometry.IsElliptic A) (hB : InfoGeometry.IsParabolic B) :
    ¬ MatrixConjugate A B := by
  intro hconj
  have htrace := traceSq_eq_of_matrixConjugate hconj
  exact not_elliptic_of_traceSq_eq_four (htrace.trans hB.1) hA

/-- Parabolic and hyperbolic finite Möbius transformations cannot be conjugate. -/
theorem not_matrixConjugate_of_hyperbolic_parabolic
    {A B : InfoGeometry.SL2C}
    (hA : InfoGeometry.IsHyperbolic A) (hB : InfoGeometry.IsParabolic B) :
    ¬ MatrixConjugate A B := by
  intro hconj
  have htrace := traceSq_eq_of_matrixConjugate hconj
  exact not_hyperbolic_of_traceSq_eq_four (htrace.trans hB.1) hA

/-- Elliptic and hyperbolic finite Möbius transformations cannot be conjugate. -/
theorem not_matrixConjugate_of_elliptic_hyperbolic
    {A B : InfoGeometry.SL2C}
    (hA : InfoGeometry.IsElliptic A) (hB : InfoGeometry.IsHyperbolic B) :
    ¬ MatrixConjugate A B := by
  intro hconj
  rcases hB with ⟨r, hr, hBtrace⟩
  apply InfoGeometry.not_hyperbolic_of_elliptic hA
  refine ⟨r, hr, ?_⟩
  rw [traceSq_eq_of_matrixConjugate hconj, hBtrace]

/-- A nontrivial elliptic qutrit flow is not conjugate to a nontrivial parabolic flow. -/
theorem ellipticFinite_not_conjugate_parabolicFinite
    {s t : ℝ} (hs : Real.sin s ≠ 0) (ht : t ≠ 0) :
    ¬ MatrixConjugate (ellipticFinite s) (parabolicFinite t) :=
  not_matrixConjugate_of_elliptic_parabolic
    (ellipticFinite_isElliptic hs) (parabolicFinite_isParabolic ht)

/-- A nontrivial hyperbolic qutrit flow is not conjugate to a parabolic flow. -/
theorem hyperbolicFinite_not_conjugate_parabolicFinite
    {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) :
    ¬ MatrixConjugate (hyperbolicFinite s) (parabolicFinite t) :=
  not_matrixConjugate_of_hyperbolic_parabolic
    (hyperbolicFinite_isHyperbolic hs) (parabolicFinite_isParabolic ht)

/-- A nontrivial elliptic qutrit flow is not conjugate to a hyperbolic flow. -/
theorem ellipticFinite_not_conjugate_hyperbolicFinite
    {s t : ℝ} (hs : Real.sin s ≠ 0) (ht : t ≠ 0) :
    ¬ MatrixConjugate (ellipticFinite s) (hyperbolicFinite t) :=
  not_matrixConjugate_of_elliptic_hyperbolic
    (ellipticFinite_isElliptic hs) (hyperbolicFinite_isHyperbolic ht)

end InfoGeometry.Quantum.QutritMobiusFiniteFlowClassification
