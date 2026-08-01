import Mathlib.Tactic

open Matrix

noncomputable section

/-- Hyperbolic Clifford generator, square `+1`. -/
def e1 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Elliptic Clifford generator, square `-1`. -/
def e2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

theorem e1_sq : e1 * e1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e1]

theorem e2_sq_neg : e2 * e2 = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e2]

theorem e1_anticomm_e2 : e1 * e2 = -(e2 * e1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e1, e2]

/-- A general traceless real Pauli/Clifford seed. -/
def tracelessPauli (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; c, -a]

/-- The determinant is the causal Weyl gauge: `X² = -det(X) I` for traceless `2 x 2`. -/
theorem tracelessPauli_sq_eq_neg_det (a b c : ℝ) :
    let X := tracelessPauli a b c
    X * X = (-(X.det)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro X
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, tracelessPauli, Matrix.det_fin_two] <;> ring

theorem det_e1 : e1.det = -1 := by
  rw [Matrix.det_fin_two]
  norm_num [e1]

theorem det_e2 : e2.det = 1 := by
  rw [Matrix.det_fin_two]
  norm_num [e2]

theorem det_e1e2 : (e1 * e2).det = -1 := by
  rw [Matrix.det_fin_two]
  norm_num [e1, e2, Matrix.mul_apply, Fin.sum_univ_two]

inductive WeylSector where
  | positive
  | negative
  | null
  deriving DecidableEq, Repr

def weylSector (M : Matrix (Fin 2) (Fin 2) ℝ) : WeylSector :=
  if 0 < M.det then WeylSector.positive
  else if M.det < 0 then WeylSector.negative
  else WeylSector.null

noncomputable def hyperbolicChart (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh t, Real.sinh t; Real.sinh t, Real.cosh t]

noncomputable def ellipticChart (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

theorem det_hyperbolicChart (t : ℝ) : (hyperbolicChart t).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [hyperbolicChart]
  simpa [pow_two] using Real.cosh_sq_sub_sinh_sq t

theorem det_ellipticChart (t : ℝ) : (ellipticChart t).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [ellipticChart]
  simpa [pow_two] using Real.cos_sq_add_sin_sq t

def nullProjector : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- Nilpotent null generator: parabolic/lightlike sector. -/
def nilpotentN : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

theorem det_nullProjector : nullProjector.det = 0 := by
  rw [Matrix.det_fin_two]
  norm_num [nullProjector]

theorem det_nilpotentN : nilpotentN.det = 0 := by
  rw [Matrix.det_fin_two]
  norm_num [nilpotentN]

theorem nilpotentN_sq : nilpotentN * nilpotentN = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nilpotentN]

noncomputable def parabolicChart (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 : Matrix (Fin 2) (Fin 2) ℝ) + t • nilpotentN

theorem parabolicChart_eq (t : ℝ) :
    parabolicChart t = !![1, t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parabolicChart, nilpotentN]

theorem det_parabolicChart (t : ℝ) : (parabolicChart t).det = 1 := by
  rw [parabolicChart_eq, Matrix.det_fin_two]
  norm_num

/-- A rank-one null boundary representative in the conformal compactification. -/
def boundaryPoint (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, u; 0, 0]

theorem det_boundaryPoint (u : ℝ) : (boundaryPoint u).det = 0 := by
  rw [Matrix.det_fin_two]
  norm_num [boundaryPoint]

theorem parabolic_preserves_boundary_null (t u : ℝ) :
    ((parabolicChart t) * boundaryPoint u).det = 0 := by
  rw [Matrix.det_fin_two]
  simp [parabolicChart_eq, boundaryPoint, Matrix.mul_apply, Fin.sum_univ_two]

/-- The base null ray fixed by the parabolic stabilizer. -/
def baseNullRay : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

theorem parabolic_fixes_base_null_ray (t : ℝ) :
    parabolicChart t * baseNullRay = baseNullRay := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parabolicChart_eq, baseNullRay, Matrix.mul_apply, Fin.sum_univ_two]

structure Twistor where
  omega : Fin 2 → ℝ
  pi : Fin 2 → ℝ

def twistorIncidence (X : Matrix (Fin 2) (Fin 2) ℝ) (Z : Twistor) : Fin 2 → ℝ :=
  fun i => Z.omega i - ∑ j, X i j * Z.pi j

def scaleTwistor (s : ℝ) (Z : Twistor) : Twistor where
  omega := fun i => s * Z.omega i
  pi := fun i => s * Z.pi i

/-- Twistor incidence is projective: scaling the twistor scales the incidence. -/
theorem twistor_incidence_homogeneous
    (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) (Z : Twistor) :
    twistorIncidence X (scaleTwistor s Z) =
      fun i => s * twistorIncidence X Z i := by
  funext i
  simp [twistorIncidence, scaleTwistor, Fin.sum_univ_two]
  ring

theorem sector_hyperbolicChart (t : ℝ) :
    weylSector (hyperbolicChart t) = WeylSector.positive := by
  simp [weylSector, det_hyperbolicChart]

theorem sector_ellipticChart (t : ℝ) :
    weylSector (ellipticChart t) = WeylSector.positive := by
  simp [weylSector, det_ellipticChart]

theorem sector_nullProjector : weylSector nullProjector = WeylSector.null := by
  simp [weylSector, det_nullProjector]

theorem sector_nilpotentN : weylSector nilpotentN = WeylSector.null := by
  simp [weylSector, det_nilpotentN]

def P (x : Matrix (Fin 2) (Fin 2) ℝ) := -xᵀ
def T_op (x : Matrix (Fin 2) (Fin 2) ℝ) := xᵀ
def PT (x : Matrix (Fin 2) (Fin 2) ℝ) := -x

theorem V4_involutions :
    (∀ x, P (P x) = x) ∧ (∀ x, T_op (T_op x) = x) ∧ (∀ x, PT (PT x) = x) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro x <;> simp [P, T_op, PT]

theorem det_P (x : Matrix (Fin 2) (Fin 2) ℝ) : (P x).det = x.det := by
  rw [P]
  rw [← neg_one_smul ℝ xᵀ, Matrix.det_smul]
  simp

theorem det_T (x : Matrix (Fin 2) (Fin 2) ℝ) : (T_op x).det = x.det := by
  simp [T_op]

theorem det_PT (x : Matrix (Fin 2) (Fin 2) ℝ) : (PT x).det = x.det := by
  rw [PT]
  rw [← neg_one_smul ℝ x, Matrix.det_smul]
  simp

/-- Determinant sign sector is invariant under nonzero real scalar rescaling.

This mirrors the free-Weyl gauge sector stability used in
`CanonicalSouriauPauliThermodynamics`: dual/primal gauge scaling in the thermodynamic
paravector lane does not alter the determinant sign class (hyperbolic / elliptic / parabolic).
-/
theorem weylSector_smul_unit (σ : ℝˣ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    weylSector ((σ : ℝ) • M) = weylSector M := by
  have hsq : 0 < (σ : ℝ) ^ 2 := by
    exact sq_pos_of_ne_zero (show (σ : ℝ) ≠ 0 by exact_mod_cast (Units.ne_zero σ))
  have hpos : 0 < (σ : ℝ) ^ 2 * M.det ↔ 0 < M.det := by
    exact mul_pos_iff_of_pos_left hsq
  have hneg : (σ : ℝ) ^ 2 * M.det < 0 ↔ M.det < 0 := by
    constructor
    · intro h
      have h' : (σ : ℝ) ^ 2 * M.det < (σ : ℝ) ^ 2 * 0 := by simpa using h
      exact lt_of_mul_lt_mul_left h' (le_of_lt hsq)
    · intro h
      exact mul_neg_of_pos_of_neg hsq h
  simp [weylSector, hpos, hneg]

-- Formal volume viewpoint for Weyl gauge scaling.

def fvolume (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := M.det

def weylScaleFlow (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
  fun M => s • M

def weylLieFlow (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
  weylScaleFlow (Real.exp t)

def fvolume_vacuum : Matrix (Fin 2) (Fin 2) ℝ := 1

def volRNPotential (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := -Real.log (fvolume M)

theorem fvolume_smul (s : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    fvolume (weylScaleFlow s M) = s ^ 2 * fvolume M := by
  simp [fvolume, weylScaleFlow]

theorem fvolume_weylLieFlow (t : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    fvolume (weylLieFlow t M) = (Real.exp t) ^ 2 * fvolume M := by
  simpa [weylLieFlow, weylScaleFlow] using fvolume_smul (Real.exp t) M

theorem fvolume_weylLieFlow_vacuum (t : ℝ) :
    fvolume (weylLieFlow t (1 : Matrix (Fin 2) (Fin 2) ℝ)) = (Real.exp t) ^ 2 := by
  simp [fvolume, weylLieFlow, weylScaleFlow]

theorem weylFlow_zero_lightcone :
    weylScaleFlow (0 : ℝ) (fvolume_vacuum) = 0 := by
  simp [weylScaleFlow, fvolume_vacuum]

/-- Relative Jacobian (det ratio) of vacuum Weyl flow versus identity frame. -/
theorem weylLieFlow_jacobian_ratio_vacuum (t : ℝ) :
    fvolume (weylLieFlow t (1 : Matrix (Fin 2) (Fin 2) ℝ)) /
      fvolume (1 : Matrix (Fin 2) (Fin 2) ℝ) = (Real.exp t) ^ 2 := by
  rw [fvolume_weylLieFlow_vacuum]
  simp [fvolume]

theorem weylSector_zero_lightcone :
    weylSector (weylScaleFlow (0 : ℝ) (fvolume_vacuum)) = WeylSector.null := by
  have hdet : (0 : Matrix (Fin 2) (Fin 2) ℝ).det = 0 := by
    simp [Matrix.det_fin_two]
  simp [weylSector, weylScaleFlow, fvolume_vacuum, hdet]

theorem negLogDet_weylLieFlow_vacuum (t : ℝ) :
    volRNPotential (weylLieFlow t (1 : Matrix (Fin 2) (Fin 2) ℝ))
      = -(Real.log (Real.exp (2 * t)) ) := by
  simp [volRNPotential, fvolume, weylLieFlow, weylScaleFlow]

theorem negLogDet_weylLieFlow_vacuum_simplified (t : ℝ) :
    volRNPotential (weylLieFlow t (1 : Matrix (Fin 2) (Fin 2) ℝ)) = -2 * t := by
  rw [negLogDet_weylLieFlow_vacuum]
  rw [Real.log_exp]
  ring

/-- Weyl-flow Jacobian as a Radon–Nikodym density (vacuum frame). -/
def weylRNBarrier (t : ℝ) : ℝ :=
  volRNPotential (weylLieFlow t (1 : Matrix (Fin 2) (Fin 2) ℝ))

 theorem weylRNBarrier_eq_negLogDet_vacuum (t : ℝ) :
    weylRNBarrier t = -2 * t := by
  rw [weylRNBarrier, negLogDet_weylLieFlow_vacuum_simplified]

 theorem weylRNBarrier_vacuum_limit :
    weylRNBarrier (- (100 : ℝ)) = 200 := by
  rw [weylRNBarrier_eq_negLogDet_vacuum]
  norm_num

 theorem weylFlow_lightcone_limit (t : ℝ) :
    fvolume (weylLieFlow t (1 : Matrix (Fin 2) (Fin 2) ℝ)) > 0 := by
  rw [fvolume_weylLieFlow_vacuum]
  positivity

/-- Log-volume potential in rapidity/scale coordinate.
    For positive scale parameters `s`, this is the 1D Bregman-like generator. -/

def weylScalePotential (s : ℝ) : ℝ := -Real.log (s ^ 2)

def weylScaleBregman (s t : ℝ) : ℝ :=
  weylScalePotential s - weylScalePotential t + 2 * (s - t) / t

/-- Relative log-volume divergence for positive scales: equals
`2 * ((s/t) - log(s/t) - 1)`, i.e. a scaled Itakura-Saito divergence. -/
theorem weylScaleBregman_eq (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    weylScaleBregman s t = 2 * ((s / t) - Real.log (s / t) - 1) := by
  unfold weylScaleBregman weylScalePotential
  have hs2 : s ^ 2 ≠ 0 := by exact pow_ne_zero 2 (ne_of_gt hs)
  have ht2 : t ^ 2 ≠ 0 := by exact pow_ne_zero 2 (ne_of_gt ht)
  have hlogdiv : Real.log (s ^ 2 / t ^ 2) = Real.log (s ^ 2) - Real.log (t ^ 2) :=
    Real.log_div hs2 ht2
  have hratio_ne : s / t ≠ 0 := div_ne_zero (ne_of_gt hs) (ne_of_gt ht)
  have hmul : s ^ 2 / t ^ 2 = (s / t) * (s / t) := by
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hmul0 : s ^ 2 / t ^ 2 = s ^ 2 * (t ^ 2)⁻¹ := by
      simp [div_eq_mul_inv]
    rw [hmul0]
    field_simp [ht0]
  have hdivform : 2 * (s - t) / t = 2 * (s / t - 1) := by
    field_simp [ht.ne']
  calc
    -Real.log (s ^ 2) - (-Real.log (t ^ 2)) + 2 * (s - t) / t
        = -Real.log (s ^ 2) + Real.log (t ^ 2) + 2 * (s - t) / t := by simp
    _ = -(Real.log (s ^ 2) - Real.log (t ^ 2)) + 2 * (s - t) / t := by ring
    _ = -Real.log (s ^ 2 / t ^ 2) + 2 * (s - t) / t := by rw [hlogdiv]
    _ = -Real.log ((s / t) * (s / t)) + 2 * (s - t) / t := by rw [hmul]
    _ = - (Real.log (s / t) + Real.log (s / t)) + 2 * (s - t) / t := by
      rw [Real.log_mul hratio_ne hratio_ne]
    _ = -2 * Real.log (s / t) + 2 * (s / t - 1) := by
      rw [hdivform]
      ring
    _ = 2 * ((s / t) - Real.log (s / t) - 1) := by ring

/-- Nonnegativity of the scale divergence on the positive Weyl sector. -/
theorem weylScaleBregman_nonneg (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    0 ≤ weylScaleBregman s t := by
  rw [weylScaleBregman_eq _ _ hs ht]
  have hratio : 0 < s / t := div_pos hs ht
  have hlog : Real.log (s / t) ≤ (s / t) - 1 := Real.log_le_sub_one_of_pos hratio
  nlinarith [hlog]

/-- Boltzmann-weight style degeneracy: `W = exp(det)` (det as volume). -/
def boltzmannDegeneracy (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Real.exp (fvolume M)

theorem boltzmannDegeneracy_weylFlow_vacuum (t : ℝ) :
    boltzmannDegeneracy (weylLieFlow t (1 : Matrix (Fin 2) (Fin 2) ℝ))
      = Real.exp ((Real.exp t) ^ 2) := by
  simp [boltzmannDegeneracy, fvolume_weylLieFlow_vacuum]
