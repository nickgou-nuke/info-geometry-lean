import Mathlib.Tactic

/-!
# Section 12: Torsion Structure

#### BUCKET 1: CLOSED FINITE THEOREMS
Finite coefficient identities for vector torsion, the coefficient shadow of
Cartan's first structure equation, contorsion, spinor covariant-derivative
splitting, quaternion commutator torsion, and a `2x2` noncommuting-shift
witness.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The torsion-free and Cartan antisymmetry statements are conditional on explicit
lower-slot symmetry or `de` antisymmetry hypotheses.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not construct smooth manifolds, coframes, differential forms,
Levi-Civita uniqueness, Einstein-Cartan field equations, axial-current
couplings, propagating torsion, quantum anomalies, or emergent-spacetime
limits.  Those remain outside this finite coefficient owner.
-/

namespace InfoGeometry.Canonical.Torsion

noncomputable section

set_option linter.unusedSectionVars false

open BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coefficients `Γᵃ_bc` of an affine connection in a finite frame. -/
abbrev ConnectionCoeff (ι : Type*) := ι → ι → ι → ℝ

/-- Coefficients of a coframe `eᵈ_c`. -/
abbrev FrameCoeff (ι : Type*) := ι → ι → ℝ

/-- Coefficients of a connection one-form `ωᵃ_db`. -/
abbrev ConnectionFormCoeff (ι : Type*) := ι → ι → ι → ℝ

/-- Vector torsion: `Tᵃ_bc = Γᵃ_bc - Γᵃ_cb`. -/
def vectorTorsion (Γ : ConnectionCoeff ι) (a b c : ι) : ℝ :=
  Γ a b c - Γ a c b

/-- The lower slots of vector torsion are antisymmetric. -/
theorem vectorTorsion_lower_antisymm (Γ : ConnectionCoeff ι) (a b c : ι) :
    vectorTorsion Γ a c b = -vectorTorsion Γ a b c := by
  simp [vectorTorsion]

/-- Repeated lower indices give zero torsion. -/
@[simp] theorem vectorTorsion_same_lower (Γ : ConnectionCoeff ι) (a b : ι) :
    vectorTorsion Γ a b b = 0 := by
  simp [vectorTorsion]

/-- Torsion is twice the lower antisymmetric part of `Γ`. -/
theorem vectorTorsion_eq_two_lower_antisym
    (Γ : ConnectionCoeff ι) (a b c : ι) :
    vectorTorsion Γ a b c = 2 * ((Γ a b c - Γ a c b) / 2) := by
  simp [vectorTorsion]
  ring

/-- Lower-slot symmetry of the connection implies zero torsion. -/
theorem vectorTorsion_zero_of_lower_symmetric
    (Γ : ConnectionCoeff ι)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b)
    (a b c : ι) :
    vectorTorsion Γ a b c = 0 := by
  simp [vectorTorsion, hΓ a b c]

/--
Finite coefficient shadow of Cartan's first structure equation:

`Tᵃ_bc = deᵃ_bc + Σ d, (ωᵃ_db eᵈ_c - ωᵃ_dc eᵈ_b)`.
-/
def cartanTorsionCoeff
    (de : ConnectionCoeff ι)
    (ω : ConnectionFormCoeff ι)
    (e : FrameCoeff ι)
    (a b c : ι) : ℝ :=
  de a b c + ∑ d, (ω a d b * e d c - ω a d c * e d b)

/-- Cartan's coefficient expression is antisymmetric if `de` is. -/
theorem cartanTorsionCoeff_lower_antisymm
    (de : ConnectionCoeff ι)
    (ω : ConnectionFormCoeff ι)
    (e : FrameCoeff ι)
    (hde : ∀ a b c, de a c b = -de a b c)
    (a b c : ι) :
    cartanTorsionCoeff de ω e a c b =
      -cartanTorsionCoeff de ω e a b c := by
  unfold cartanTorsionCoeff
  rw [hde a b c]
  have hsum :
      (∑ d, (ω a d c * e d b - ω a d b * e d c)) =
        -∑ d, (ω a d b * e d c - ω a d c * e d b) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hsum]
  ring

/--
Coordinate-basis reduction.  With `de = 0`, identity coframe, and
`ωᵃ_d = Γᵃ_bd dxᵇ`, the coefficient formula reads out the usual vector
torsion tensor.
-/
theorem coordinate_cartanTorsionCoeff_eq_vectorTorsion
    (Γ : ConnectionCoeff ι) (a b c : ι) :
    cartanTorsionCoeff
        (fun _ _ _ => 0)
        (fun a d b => Γ a b d)
        (fun d c => if d = c then 1 else 0)
        a b c =
      vectorTorsion Γ a b c := by
  simp [cartanTorsionCoeff, vectorTorsion]

/-- Algebraic contorsion coefficient shape. -/
def contorsionCoeff (T : ConnectionCoeff ι) (a b c : ι) : ℝ :=
  (T a b c + T c a b - T b c a) / 2

/-- Zero torsion gives zero contorsion in the finite coefficient formula. -/
theorem contorsionCoeff_zero_of_torsion_zero
    (T : ConnectionCoeff ι)
    (hT : ∀ a b c, T a b c = 0)
    (a b c : ι) :
    contorsionCoeff T a b c = 0 := by
  simp [contorsionCoeff, hT]

/-- Total spin connection with contorsion: `ω_total = ω_LC + K`. -/
def spinConnectionWithContorsion {S : Type*} [Add S] (ωLC K : S) : S :=
  ωLC + K

/-- If contorsion is zero, the spin connection reduces to Levi-Civita. -/
@[simp] theorem spinConnectionWithContorsion_zero
    {S : Type*} [AddMonoid S] (ωLC : S) :
    spinConnectionWithContorsion ωLC 0 = ωLC := by
  simp [spinConnectionWithContorsion]

/-- Finite spinor covariant derivative shadow `Dψ = dψ + ωψ`. -/
def spinorCovariantDerivative {n : Type*} [Fintype n]
    (dψ : n → ℝ) (ω : Matrix n n ℝ) (ψ : n → ℝ) : n → ℝ :=
  dψ + ω.mulVec ψ

/-- Adding contorsion splits the finite spinor covariant derivative additively. -/
theorem spinorCovariantDerivative_contorsion_split
    {n : Type*} [Fintype n]
    (dψ : n → ℝ) (ωLC K : Matrix n n ℝ) (ψ : n → ℝ) :
    spinorCovariantDerivative dψ (ωLC + K) ψ =
      spinorCovariantDerivative dψ ωLC ψ + K.mulVec ψ := by
  ext i
  simp [spinorCovariantDerivative, Matrix.add_mulVec, add_assoc]

/--
Quaternion torsion shadow using a commutator connection action:
`T_q = dq + Ω*q - q*Ω`.
-/
def quaternionTorsion {Q : Type*} [Ring Q] (dq Ω q : Q) : Q :=
  dq + (Ω * q - q * Ω)

/-- Flat quaternion connection with a constant field has zero torsion. -/
@[simp] theorem quaternionTorsion_flat {Q : Type*} [Ring Q] (q : Q) :
    quaternionTorsion 0 0 q = 0 := by
  simp [quaternionTorsion]

/-- With zero connection, quaternion torsion is just the derivative term. -/
@[simp] theorem quaternionTorsion_zero_connection
    {Q : Type*} [Ring Q] (dq q : Q) :
    quaternionTorsion dq 0 q = dq := by
  simp [quaternionTorsion]

/-- A commuting connection/action pair has zero pure-connection torsion. -/
theorem quaternionTorsion_zero_of_commuting
    {Q : Type*} [Ring Q] (Ω q : Q)
    (hcomm : Ω * q = q * Ω) :
    quaternionTorsion 0 Ω q = 0 := by
  simp [quaternionTorsion, hcomm]

/-- Quaternionic two-form coefficient with left/right conjugate connection action. -/
def quaternionTwoFormCoeff
    {Q : Type*} [Ring Q]
    (conj : Q → Q)
    (de : ι → ι → Q)
    (Ω e : ι → Q)
    (μ ν : ι) : Q :=
  de μ ν + (Ω μ * e ν - Ω ν * e μ) +
    (e μ * conj (Ω ν) - e ν * conj (Ω μ))

/-- The quaternionic two-form coefficient is antisymmetric from antisymmetric `de`. -/
theorem quaternionTwoFormCoeff_antisymm
    {Q : Type*} [Ring Q]
    (conj : Q → Q)
    (de : ι → ι → Q)
    (Ω e : ι → Q)
    (hde : ∀ μ ν, de ν μ = -de μ ν)
    (μ ν : ι) :
    quaternionTwoFormCoeff conj de Ω e ν μ =
      -quaternionTwoFormCoeff conj de Ω e μ ν := by
  unfold quaternionTwoFormCoeff
  rw [hde μ ν]
  noncomm_ring

/-- Left finite shift. -/
def shiftL : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 0, 0]

/-- Right finite shift. -/
def shiftR : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0; 1, 0]

/-- The finite shift commutator is the diagonal obstruction witness. -/
theorem shift_commutator_eq_diag :
    shiftL * shiftR - shiftR * shiftL = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shiftL, shiftR, Matrix.mul_apply, Fin.sum_univ_two]

/-- The finite shift commutator is nonzero. -/
theorem shift_commutator_ne_zero :
    shiftL * shiftR - shiftR * shiftL ≠ 0 := by
  rw [shift_commutator_eq_diag]
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num at h00

end

end InfoGeometry.Canonical.Torsion
