import InfoGeometry.OperatorAlgebra.IndividuatedCasimir
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.ModularHamiltonianSignum
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.NoncommutativeModularSignum

Trace-free noncommutative roots for the modular-signum lane.

This file deliberately avoids finite diagonal models, traces, and matrix
normalization.  It proves:

* left/right multiplication laws in a noncommutative algebra;
* the full regular-module commutant characterization of left multiplication;
* the left/right relative modular operator `L_a R_{b⁻¹}` and its honest
  noncommutative product law;
* a two-point involution boost sector `K_a = a • S`;
* the doubled-space instantiation with the concrete repo operators
  `J = modular_j` and `S = spectral_epsilon`.

It does not claim a general theorem `sgn(log Δ)` from spectral functional
calculus.  The signum theorem here is the exact two-point involution calculus:
for `a > 0`, `sgn(a • S) = S`.
-/

namespace InfoGeometry.Canonical.NoncommutativeModularSignum

open InfoGeometry.OperatorAlgebra.IndividuatedCasimir
open InfoGeometry.Krein
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Canonical.ModularHamiltonianSignum

/-! ## Left/right multiplication in a noncommutative algebra -/

section LeftRight

variable {R A : Type*}
variable [CommSemiring R] [Semiring A] [Algebra R A]

/-- Left multiplication as a linear endomorphism: `x ↦ a*x`. -/
@[rep_depth operator]
def leftMul (a : A) : A →ₗ[R] A where
  toFun := fun x => a * x
  map_add' := by
    intro x y
    simp [left_distrib]
  map_smul' := by
    intro r x
    calc
      a * r • x = a * (algebraMap R A r * x) := by
        rw [Algebra.smul_def]
      _ = algebraMap R A r * (a * x) := by
        rw [← mul_assoc, ← (Algebra.commutes r a), mul_assoc]
      _ = (RingHom.id R) r • (a * x) := by
        rw [Algebra.smul_def]
        rfl

/-- Right multiplication as a linear endomorphism: `x ↦ x*b`. -/
@[rep_depth operator]
def rightMul (b : A) : A →ₗ[R] A where
  toFun := fun x => x * b
  map_add' := by
    intro x y
    simp [right_distrib]
  map_smul' := by
    intro r x
    simp [Algebra.smul_def, mul_assoc]

@[simp, rep_depth operator]
theorem leftMul_apply (a x : A) :
    leftMul (R := R) a x = a * x :=
  rfl

@[simp, rep_depth operator]
theorem rightMul_apply (b x : A) :
    rightMul (R := R) b x = x * b :=
  rfl

/-- `L_a L_b = L_{ab}`. -/
@[rep_depth operator]
theorem leftMul_mul_leftMul (a b : A) :
    leftMul (R := R) a * leftMul (R := R) b = leftMul (R := R) (a * b) := by
  ext x
  simp [leftMul, mul_assoc]

/-- `R_a R_b = R_{ba}` because endomorphism multiplication is composition. -/
@[rep_depth operator]
theorem rightMul_mul_rightMul (a b : A) :
    rightMul (R := R) a * rightMul (R := R) b = rightMul (R := R) (b * a) := by
  ext x
  simp [rightMul, mul_assoc]

/-- Left and right multiplication commute: `L_a R_b = R_b L_a`. -/
@[rep_depth operator]
theorem leftMul_comm_rightMul (a b : A) :
    leftMul (R := R) a * rightMul (R := R) b =
      rightMul (R := R) b * leftMul (R := R) a := by
  ext x
  simp [leftMul, rightMul, mul_assoc]

/--
Every regular-module endomorphism commuting with all left multiplications is
right multiplication by its value at the unit.
-/
@[rep_depth operator]
theorem eq_rightMul_apply_one_of_commutes_leftMul
    (T : A →ₗ[R] A)
    (hT : ∀ a : A,
      T * leftMul (R := R) a = leftMul (R := R) a * T) :
    T = rightMul (R := R) (T 1) := by
  ext x
  have hx := congrArg (fun F : A →ₗ[R] A => F 1) (hT x)
  simpa [leftMul, rightMul] using hx

/--
Full regular commutant theorem: an endomorphism commutes with the entire left
regular action exactly when it is right multiplication by its value at `1`.
-/
@[rep_depth operator]
theorem commutes_leftMul_iff_eq_rightMul_apply_one
    (T : A →ₗ[R] A) :
    (∀ a : A,
      T * leftMul (R := R) a = leftMul (R := R) a * T) ↔
      T = rightMul (R := R) (T 1) := by
  constructor
  · exact eq_rightMul_apply_one_of_commutes_leftMul (R := R) T
  · intro hT a
    rw [hT]
    exact (leftMul_comm_rightMul (R := R) a (T 1)).symm

/--
Trace-free left/right relative modular operator:
`Δ_{a|b} = L_a R_{b⁻¹}`.
-/
@[rep_depth operator]
def lrRelativeModular
    (a b : InvertibleTransport A) : A →ₗ[R] A :=
  leftMul (R := R) a.val * rightMul (R := R) b.inv

/-- Application law: `Δ_{a|b}(x)=a*x*b⁻¹`. -/
@[simp, rep_depth operator]
theorem lrRelativeModular_apply
    (a b : InvertibleTransport A) (x : A) :
    lrRelativeModular (R := R) a b x = a.val * x * b.inv := by
  simp [lrRelativeModular, leftMul, rightMul, mul_assoc]

/-- Noncommutative product law for left/right relative modular operators. -/
@[rep_depth operator]
theorem lrRelativeModular_mul
    (a b c d : InvertibleTransport A) :
    lrRelativeModular (R := R) a b * lrRelativeModular (R := R) c d =
      leftMul (R := R) (a.val * c.val) * rightMul (R := R) (d.inv * b.inv) := by
  ext x
  simp [lrRelativeModular, leftMul, rightMul, mul_assoc]

/--
The honest noncommutative product replacing the false diagonal cocycle:
`Δ_{a|b} Δ_{b|c} = L_{ab} R_{c⁻¹b⁻¹}`.
-/
@[rep_depth operator]
theorem lrRelativeModular_naive_cocycle_product
    (a b c : InvertibleTransport A) :
    lrRelativeModular (R := R) a b * lrRelativeModular (R := R) b c =
      leftMul (R := R) (a.val * b.val) * rightMul (R := R) (c.inv * b.inv) := by
  exact lrRelativeModular_mul (R := R) a b b c

end LeftRight

/-! ## Two-point involution boost signum -/

section BoostSignum

variable {A : Type*}

/-- Boost Hamiltonian in an involution sector: `K_a = a • S`. -/
@[rep_depth operator]
noncomputable def boostHamiltonian [SMul ℝ A] (a : ℝ) (S : A) : A :=
  a • S

/-- Boost modular operator proxy: `Δ_a = exp(a • S)`. -/
@[rep_depth operator]
noncomputable def boostDelta
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a : ℝ) (S : A) : A :=
  NormedSpace.exp (boostHamiltonian a S)

/--
Two-point signum calculus for an involution sector.

This is not a general spectral signum. It is the explicit sign of the scalar
coefficient in `a • S`.
-/
@[rep_depth operator]
noncomputable def boostSignum [Zero A] [Neg A] (a : ℝ) (S : A) : A :=
  if 0 < a then S else if a < 0 then -S else 0

@[simp, rep_depth operator]
theorem boostSignum_of_pos [Zero A] [Neg A] {a : ℝ} {S : A} (ha : 0 < a) :
    boostSignum a S = S := by
  simp [boostSignum, ha]

@[simp, rep_depth operator]
theorem boostSignum_of_neg [Zero A] [Neg A] {a : ℝ} {S : A} (ha : a < 0) :
    boostSignum a S = -S := by
  have hnot : ¬ 0 < a := not_lt.mpr (le_of_lt ha)
  simp [boostSignum, hnot, ha]

@[simp, rep_depth operator]
theorem boostSignum_of_zero [Zero A] [Neg A] {a : ℝ} {S : A} (ha : a = 0) :
    boostSignum a S = 0 := by
  simp [boostSignum, ha]

/-- If `S²=1` and `a≠0`, then the two-point boost signum squares to `1`. -/
@[rep_depth operator]
theorem boostSignum_sq_of_ne_zero
    [Ring A] {a : ℝ} {S : A}
    (hS : S * S = 1) (ha : a ≠ 0) :
    boostSignum a S * boostSignum a S = 1 := by
  by_cases hpos : 0 < a
  · rw [boostSignum_of_pos hpos, hS]
  · have hle : a ≤ 0 := not_lt.mp hpos
    have hlt : a < 0 := lt_of_le_of_ne hle ha
    rw [boostSignum_of_neg hlt]
    simp [hS]

variable [Ring A] [Algebra ℝ A]

/-- `J S J = -S` from `J²=1` and `JS=-SJ`. -/
@[rep_depth operator]
theorem conjugate_involution_axis
    {J S : A}
    (hJ : J * J = 1)
    (hJS : J * S = -(S * J)) :
    J * S * J = -S := by
  have hSJ : S * J = -(J * S) := by
    simpa using (congrArg Neg.neg hJS).symm
  calc
    J * S * J = J * (S * J) := by rw [mul_assoc]
    _ = J * (-(J * S)) := by rw [hSJ]
    _ = -((J * J) * S) := by noncomm_ring
    _ = -S := by rw [hJ]; simp

/-- `J (a•S) J = -(a•S)` from anticommutation. -/
@[rep_depth operator]
theorem conjugate_boostHamiltonian
    {J S : A} (a : ℝ)
    (hJ : J * J = 1)
    (hJS : J * S = -(S * J)) :
    J * boostHamiltonian a S * J = -boostHamiltonian a S := by
  let c : A := algebraMap ℝ A a
  have hcJ : J * c = c * J := by
    exact (Algebra.commutes a J).symm
  have hcalc : J * (c * S) * J = -(c * S) := by
    calc
      J * (c * S) * J = (J * c) * S * J := by simp [mul_assoc]
      _ = (c * J) * S * J := by rw [hcJ]
      _ = c * (J * S * J) := by simp [mul_assoc]
      _ = c * (-S) := by
              rw [conjugate_involution_axis (A := A) hJ hJS]
      _ = -(c * S) := by simp
  simpa [boostHamiltonian, Algebra.smul_def, c] using hcalc

end BoostSignum

/-! ## Concrete doubled-space boost sector -/

section Doubled

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "J" => modular_j (E := E)
local notation "ε" => spectral_epsilon (E := E)

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Concrete doubled boost Hamiltonian `K_a = a • ε`. -/
@[rep_depth krein]
noncomputable def doubledBoostHamiltonian (a : ℝ) : EndH :=
  boostHamiltonian a ε

/-- Concrete doubled boost modular operator `Δ_a = exp(a • ε)`. -/
@[rep_depth krein]
noncomputable def doubledBoostDelta (a : ℝ) : EndH :=
  boostDelta a ε

/-- Concrete two-point signum of the doubled boost sector. -/
@[rep_depth krein]
noncomputable def doubledBoostSignum (a : ℝ) : EndH :=
  boostSignum a ε

@[simp, rep_depth krein]
theorem doubledBoostSignum_of_pos {a : ℝ} (ha : 0 < a) :
    doubledBoostSignum (E := E) a = ε := by
  simp [doubledBoostSignum, ha]

@[simp, rep_depth krein]
theorem doubledBoostSignum_of_neg {a : ℝ} (ha : a < 0) :
    doubledBoostSignum (E := E) a = -ε := by
  exact boostSignum_of_neg (A := EndH) (S := ε) ha

@[simp, rep_depth krein]
theorem doubledBoostSignum_of_zero {a : ℝ} (ha : a = 0) :
    doubledBoostSignum (E := E) a = 0 := by
  simp [doubledBoostSignum, ha]

/-- For `a≠0`, the doubled boost signum is an involution. -/
@[rep_depth krein]
theorem doubledBoostSignum_sq_of_ne_zero {a : ℝ} (ha : a ≠ 0) :
    doubledBoostSignum (E := E) a * doubledBoostSignum (E := E) a = (1 : EndH) := by
  have hε : (ε : EndH) * ε = (1 : EndH) := by
    change (spectral_epsilon (E := E)).comp (spectral_epsilon (E := E)) =
      ContinuousLinearMap.id ℝ H₂
    simpa using spectral_epsilon_involution (E := E)
  exact boostSignum_sq_of_ne_zero (A := EndH) hε ha

/-- `J K_a J = -K_a` in the concrete doubled boost sector. -/
@[rep_depth krein]
theorem modular_j_conjugates_doubledBoostHamiltonian (a : ℝ) :
    J * doubledBoostHamiltonian (E := E) a * J =
      -doubledBoostHamiltonian (E := E) a := by
  have hJ : (J : EndH) * J = (1 : EndH) := by
    change (modular_j (E := E)).comp (modular_j (E := E)) =
      ContinuousLinearMap.id ℝ H₂
    simpa using modular_j_involution E
  have hJS : (J : EndH) * ε = -(ε * J) := by
    simpa using modular_j_spectral_epsilon_anticommute E
  exact conjugate_boostHamiltonian (A := EndH) a hJ hJS

/-- `J Δ_a J = Δ_{-a}` in the concrete doubled boost sector. -/
@[rep_depth krein]
theorem modular_j_conjugates_doubledBoostDelta (a : ℝ) :
    J * doubledBoostDelta (E := E) a * J =
      doubledBoostDelta (E := E) (-a) := by
  simpa [doubledBoostDelta, boostDelta, boostHamiltonian,
    TomitaTakesaki.modularConjugationJ, TomitaTakesaki.modularSignEpsilon] using
    (TomitaTakesaki.modularConjugationJ_exp_modularSignEpsilon (E := E) a)

/--
For positive scalar boost coefficient, the already proved signum-Clifford table
applies to the genuine two-point signum of `K_a = a • ε`.
-/
@[rep_depth krein]
theorem doubledBoostSignum_cl11_relations_of_pos {a : ℝ} (ha : 0 < a) :
    (J : EndH) * J = (1 : EndH) ∧
    doubledBoostSignum (E := E) a * doubledBoostSignum (E := E) a = (1 : EndH) ∧
    J * doubledBoostSignum (E := E) a =
      -(doubledBoostSignum (E := E) a * J) := by
  have hJ : (J : EndH) * J = (1 : EndH) := by
    change (modular_j (E := E)).comp (modular_j (E := E)) =
      ContinuousLinearMap.id ℝ H₂
    simpa using modular_j_involution E
  have hS : doubledBoostSignum (E := E) a * doubledBoostSignum (E := E) a =
      (1 : EndH) :=
    doubledBoostSignum_sq_of_ne_zero (E := E) (ne_of_gt ha)
  have hJS : (J : EndH) * doubledBoostSignum (E := E) a =
      -(doubledBoostSignum (E := E) a * J) := by
    simpa [doubledBoostSignum_of_pos (E := E) ha] using
      (modular_j_spectral_epsilon_anticommute E)
  exact ⟨hJ, hS, hJS⟩

end Doubled

end InfoGeometry.Canonical.NoncommutativeModularSignum
