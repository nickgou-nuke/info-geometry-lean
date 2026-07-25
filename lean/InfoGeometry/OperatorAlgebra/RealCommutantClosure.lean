import Mathlib.Tactic

/-!
# InfoGeometry.OperatorAlgebra.RealCommutantClosure

Finite real-operator commutant closure lemmas.

#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
[realCommutant_one_mem, realCommutant_zero_mem, realCommutant_add_mem,
 realCommutant_neg_mem, realCommutant_sub_mem, realCommutant_mul_mem,
 realCommutant_pow_mem, realCommutant_commutator_eq_zero,
 realCommutant_of_internal_commutative]

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
[Theorems that compile conditionally based on explicitly named premises. No hidden assumptions.]
[realCommutant_of_internal_commutative is conditional on a concrete internal
 commutativity premise for the carrier set.]

#### BUCKET 3: OPEN CLOSURE DEBT
[No Tomita--Takesaki theorem. No cyclic/separating theorem. No Type III/predual
 theorem. No KMS theorem. No modular conjugation theorem. This file proves only
 finite algebraic closure properties of the real commutant.]
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealCommutantClosure

variable {HR : Type*}
variable [NormedAddCommGroup HR] [InnerProductSpace ℝ HR]

local notation "EndR" => HR →L[ℝ] HR

noncomputable local instance : NormedRing EndR := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndR := inferInstance
local instance : IsTopologicalRing EndR := inferInstance

/-- Real commutant of a set of real bounded operators. -/
def realCommutant (A : Set EndR) : Set EndR :=
  {B | ∀ C : EndR, C ∈ A → B * C = C * B}

/-- The identity operator lies in every real commutant. -/
@[simp]
theorem realCommutant_one_mem
    (A : Set EndR) :
    (1 : EndR) ∈ realCommutant A := by
  intro C hC
  simp

/-- The zero operator lies in every real commutant. -/
@[simp]
theorem realCommutant_zero_mem
    (A : Set EndR) :
    (0 : EndR) ∈ realCommutant A := by
  intro C hC
  simp

/-- The real commutant is closed under addition. -/
theorem realCommutant_add_mem
    (A : Set EndR)
    {B D : EndR}
    (hB : B ∈ realCommutant A)
    (hD : D ∈ realCommutant A) :
    B + D ∈ realCommutant A := by
  intro C hC
  calc
    (B + D) * C = B * C + D * C := by
      rw [add_mul]
    _ = C * B + C * D := by
      rw [hB C hC, hD C hC]
    _ = C * (B + D) := by
      rw [mul_add]

/-- The real commutant is closed under negation. -/
theorem realCommutant_neg_mem
    (A : Set EndR)
    {B : EndR}
    (hB : B ∈ realCommutant A) :
    -B ∈ realCommutant A := by
  intro C hC
  calc
    (-B) * C = -(B * C) := by
      rw [neg_mul]
    _ = -(C * B) := by
      rw [hB C hC]
    _ = C * (-B) := by
      rw [mul_neg]

/-- The real commutant is closed under subtraction. -/
theorem realCommutant_sub_mem
    (A : Set EndR)
    {B D : EndR}
    (hB : B ∈ realCommutant A)
    (hD : D ∈ realCommutant A) :
    B - D ∈ realCommutant A := by
  simpa [sub_eq_add_neg] using
    realCommutant_add_mem A hB (realCommutant_neg_mem A hD)

/-- The real commutant is closed under real scalar multiplication. -/
theorem realCommutant_smul_mem
    (A : Set EndR)
    (r : ℝ)
    {B : EndR}
    (hB : B ∈ realCommutant A) :
    r • B ∈ realCommutant A := by
  intro C hC
  calc
    (r • B) * C = r • (B * C) := by
      rw [smul_mul_assoc]
    _ = r • (C * B) := by
      rw [hB C hC]
    _ = C * (r • B) := by
      rw [mul_smul_comm]

/-- The real commutant is closed under multiplication. -/
theorem realCommutant_mul_mem
    (A : Set EndR)
    {B D : EndR}
    (hB : B ∈ realCommutant A)
    (hD : D ∈ realCommutant A) :
    B * D ∈ realCommutant A := by
  intro C hC
  calc
    (B * D) * C = B * (D * C) := by
      rw [mul_assoc]
    _ = B * (C * D) := by
      rw [hD C hC]
    _ = (B * C) * D := by
      rw [mul_assoc]
    _ = (C * B) * D := by
      rw [hB C hC]
    _ = C * (B * D) := by
      rw [mul_assoc]

/-- Powers of a commutant element remain in the commutant. -/
theorem realCommutant_pow_mem
    (A : Set EndR)
    {B : EndR}
    (hB : B ∈ realCommutant A) :
    ∀ n : ℕ, B ^ n ∈ realCommutant A := by
  intro n
  induction n with
  | zero =>
      exact realCommutant_one_mem (HR := HR) A
  | succ n ih =>
      rw [pow_succ]
      exact realCommutant_mul_mem (HR := HR) A ih hB

/--
Finite carrier induction for additive closure: every finite list sum of
commutant elements remains in the commutant.
-/
theorem realCommutant_list_sum_mem
    (A : Set EndR)
    (Bs : List EndR)
    (hBs : ∀ B ∈ Bs, B ∈ realCommutant A) :
    Bs.sum ∈ realCommutant A := by
  induction Bs with
  | nil =>
      simp
  | cons B Bs ih =>
      have hB : B ∈ realCommutant A := hBs B (by simp)
      have htail : ∀ D ∈ Bs, D ∈ realCommutant A := by
        intro D hD
        exact hBs D (by simp [hD])
      simpa using realCommutant_add_mem (HR := HR) A hB (ih htail)

/--
Finite carrier induction for multiplicative closure: every finite list product
of commutant elements remains in the commutant.
-/
theorem realCommutant_list_prod_mem
    (A : Set EndR)
    (Bs : List EndR)
    (hBs : ∀ B ∈ Bs, B ∈ realCommutant A) :
    Bs.prod ∈ realCommutant A := by
  induction Bs with
  | nil =>
      simp
  | cons B Bs ih =>
      have hB : B ∈ realCommutant A := hBs B (by simp)
      have htail : ∀ D ∈ Bs, D ∈ realCommutant A := by
        intro D hD
        exact hBs D (by simp [hD])
      simpa using realCommutant_mul_mem (HR := HR) A hB (ih htail)

/--
Finite one-variable real operator polynomials, represented transparently as
lists of coefficient/exponent pairs.
-/
def finiteRealOperatorPolynomialEval
    (terms : List (ℝ × ℕ))
    (B : EndR) : EndR :=
  (terms.map fun term => term.1 • B ^ term.2).sum

/--
Finite polynomial closure: a real finite linear combination of powers of one
commutant element remains in the commutant.
-/
theorem realCommutant_finite_polynomial_mem
    (A : Set EndR)
    (terms : List (ℝ × ℕ))
    {B : EndR}
    (hB : B ∈ realCommutant A) :
    finiteRealOperatorPolynomialEval terms B ∈ realCommutant A := by
  unfold finiteRealOperatorPolynomialEval
  apply realCommutant_list_sum_mem (HR := HR) A
  intro T hT
  rcases List.mem_map.mp hT with ⟨term, hterm, rfl⟩
  exact realCommutant_smul_mem (HR := HR) A term.1
    (realCommutant_pow_mem (HR := HR) A hB term.2)

/--
Carrier induction, additive form: if every element of a proper finite carrier
is already in the commutant, then every finite carrier sum is in the commutant.
-/
theorem realCommutant_carrier_list_sum_mem
    (A Carrier : Set EndR)
    (hCarrier : Carrier ⊆ realCommutant A)
    (Bs : List EndR)
    (hBs : ∀ B ∈ Bs, B ∈ Carrier) :
    Bs.sum ∈ realCommutant A := by
  exact realCommutant_list_sum_mem (HR := HR) A Bs
    (by
      intro B hB
      exact hCarrier (hBs B hB))

/--
Carrier induction, multiplicative form: if every element of a proper finite
carrier is already in the commutant, then every finite carrier product is in
the commutant.
-/
theorem realCommutant_carrier_list_prod_mem
    (A Carrier : Set EndR)
    (hCarrier : Carrier ⊆ realCommutant A)
    (Bs : List EndR)
    (hBs : ∀ B ∈ Bs, B ∈ Carrier) :
    Bs.prod ∈ realCommutant A := by
  exact realCommutant_list_prod_mem (HR := HR) A Bs
    (by
      intro B hB
      exact hCarrier (hBs B hB))

/--
Commutator readout: if `B` lies in the commutant of `A`, then its associative
commutator with every element of `A` is zero.
-/
theorem realCommutant_commutator_eq_zero
    (A : Set EndR)
    {B C : EndR}
    (hB : B ∈ realCommutant A)
    (hC : C ∈ A) :
    B * C - C * B = 0 := by
  rw [hB C hC]
  simp

/--
If a carrier set is internally commutative, every carrier element belongs to
the carrier's real commutant.
-/
theorem realCommutant_of_internal_commutative
    (A : Set EndR)
    (hcomm : ∀ ⦃B C : EndR⦄, B ∈ A → C ∈ A → B * C = C * B)
    {B : EndR}
    (hB : B ∈ A) :
    B ∈ realCommutant A := by
  intro C hC
  exact hcomm hB hC

/--
The real commutant is a subsemiring-like closure theorem:
it contains `0`, `1`, and is closed under addition and multiplication.
-/
theorem realCommutant_basic_closure
    (A : Set EndR) :
    (0 : EndR) ∈ realCommutant A ∧
    (1 : EndR) ∈ realCommutant A ∧
    (∀ {B D : EndR},
      B ∈ realCommutant A →
      D ∈ realCommutant A →
      B + D ∈ realCommutant A) ∧
    (∀ {B D : EndR},
      B ∈ realCommutant A →
      D ∈ realCommutant A →
      B * D ∈ realCommutant A) :=
  ⟨realCommutant_zero_mem A,
    realCommutant_one_mem A,
    by
      intro B D hB hD
      exact realCommutant_add_mem A hB hD,
    by
      intro B D hB hD
      exact realCommutant_mul_mem A hB hD⟩

end InfoGeometry.OperatorAlgebra.RealCommutantClosure
