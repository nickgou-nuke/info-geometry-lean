/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms
import InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# The square-zero domain of the Peirce graded derivation

The total graded derivation squares to the inner derivation by V. Its
centralizer is invariant and carries a square-zero restriction. This states
the precise domain condition behind the transcript's cochain-complex claim.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

section CentralizerMultiplication

variable {B : Type*} [Ring B]

/-- The centralizer of any element in an associative ring is closed under
multiplication. -/
lemma genV_centralizer_mul {P A C : B}
    (X Y : {X : B // genV P A C * X = X * genV P A C}) :
    genV P A C * (X.val * Y.val) = (X.val * Y.val) * genV P A C := by
  calc genV P A C * (X.val * Y.val)
      = (genV P A C * X.val) * Y.val := by rw [mul_assoc]
    _ = (X.val * genV P A C) * Y.val := by rw [X.property]
    _ = X.val * (genV P A C * Y.val) := by rw [mul_assoc]
    _ = X.val * (Y.val * genV P A C) := by rw [Y.property]
    _ = (X.val * Y.val) * genV P A C := by rw [mul_assoc]

end CentralizerMultiplication

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)
include hP

theorem superDerivPhi_square (A C X : B) :
    superDerivPhi P A C (superDerivPhi P A C X) = connV P A C X := by
  simp only [superDerivPhi, superDerivPlus, superDerivMinus, parityConj, connV]
  peirce_nf hP

theorem superDerivPhi_square_zero_iff (A C X : B) :
    superDerivPhi P A C (superDerivPhi P A C X) = 0 ↔
      genV P A C * X = X * genV P A C := by
  rw [superDerivPhi_square hP, connV, comm, sub_eq_zero]

/-- The graded derivation preserves the kernel of its square. -/
theorem superDerivPhi_connV (A C X : B) :
    superDerivPhi P A C (connV P A C X) =
      connV P A C (superDerivPhi P A C X) := by
  rw [← superDerivPhi_square hP A C X,
    superDerivPhi_square hP A C (superDerivPhi P A C X)]

theorem superDerivPhi_preserves_centralizer (A C X : B)
    (hX : genV P A C * X = X * genV P A C) :
    genV P A C * superDerivPhi P A C X =
      superDerivPhi P A C X * genV P A C := by
  have hz : connV P A C X = 0 := by simp [connV, comm, hX]
  have h := superDerivPhi_connV hP A C X
  rw [hz] at h
  have hd : superDerivPhi P A C (0 : B) = 0 := by
    simp [superDerivPhi, superDerivPlus, superDerivMinus, parityConj]
  rw [hd] at h
  exact sub_eq_zero.mp h.symm

/-- The Peirce superderivation obeys the twisted Leibniz rule.  The twist is
the actual grading automorphism `parityConj`; this is the algebraic
compatibility needed before treating its square-zero restriction as a
graded differential. -/
theorem superDerivPhi_twisted_leibniz (A C X Y : B) :
    superDerivPhi P A C (X * Y) =
      superDerivPhi P A C X * Y + parityConj P X * superDerivPhi P A C Y := by
  have hS : invS P * invS P = 1 := by
    simp only [invS]
    noncomm_ring [hP]
  have htwist : parityConj P (X * Y) = parityConj P X * parityConj P Y :=
    (parityConj_involutive_ring_action hP X Y).2.1
  simp only [superDerivPhi, superDerivPlus, superDerivMinus]
  rw [htwist]
  noncomm_ring [hS]

/-- Parity conjugation preserves the centralizer of the even curvature term
`genV`, so it restricts to the same carrier on which `superDerivPhi` squares
to zero. -/
theorem parityConj_preserves_genV_centralizer (A C X : B)
    (hX : genV P A C * X = X * genV P A C) :
    genV P A C * parityConj P X = parityConj P X * genV P A C := by
  rcases archetype_A27_grading_parities hP A C with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hV, _, _, _⟩
  have hparity_mul (U V : B) :
      parityConj P (U * V) = parityConj P U * parityConj P V :=
    (parityConj_involutive_ring_action hP U V).2.1
  calc genV P A C * parityConj P X
      = parityConj P (genV P A C) * parityConj P X := by rw [hV]
    _ = parityConj P (genV P A C * X) := (hparity_mul _ _).symm
    _ = parityConj P (X * genV P A C) := congrArg (parityConj P) hX
    _ = parityConj P X * parityConj P (genV P A C) := hparity_mul _ _
    _ = parityConj P X * genV P A C := by rw [hV]

/-- Restriction to the invariant centralizer, with no assumption that V is
central in the ambient ring. -/
def centralizerDifferential (A C : B)
    (X : {X : B // genV P A C * X = X * genV P A C}) :
    {X : B // genV P A C * X = X * genV P A C} :=
  ⟨superDerivPhi P A C X.val,
    superDerivPhi_preserves_centralizer hP A C X.val X.property⟩

/-- On the `genV` centralizer, the square-zero Peirce differential is odd for
the restricted parity involution. -/
theorem centralizerDifferential_parity_odd (A C : B)
    (X : {X : B // genV P A C * X = X * genV P A C}) :
    parityConj P (centralizerDifferential hP A C X).val =
      -(centralizerDifferential hP A C ⟨parityConj P X.val,
        parityConj_preserves_genV_centralizer hP A C X.val X.property⟩).val := by
  have h := InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPhi_parity_odd
    (P := P) A C X.val hP
  change parityConj P (superDerivPhi P A C X.val) =
    -superDerivPhi P A C (parityConj P X.val) at h
  exact h

theorem centralizerDifferential_square_val (A C : B)
    (X : {X : B // genV P A C * X = X * genV P A C}) :
    (centralizerDifferential hP A C (centralizerDifferential hP A C X)).val = 0 :=
  (superDerivPhi_square_zero_iff hP A C X.val).2 X.property

/-- The restricted differential obeys the graded Leibniz rule on the
centralizer carrier, with parity acting on the left factor.  Together with
`centralizerDifferentialHom_comp_self`, this is the concrete Z/2 differential
algebra law available before any geometric form representation is chosen. -/
theorem centralizerDifferential_mul (A C : B)
    (X Y : {X : B // genV P A C * X = X * genV P A C}) :
    (centralizerDifferential hP A C
      ⟨X.val * Y.val, genV_centralizer_mul X Y⟩).val =
        (centralizerDifferential hP A C X).val * Y.val +
          parityConj P X.val * (centralizerDifferential hP A C Y).val := by
  change superDerivPhi P A C (X.val * Y.val) = _
  exact superDerivPhi_twisted_leibniz hP A C X.val Y.val

/-- The unital subring of operators centralizing `genV`. -/
def metricCentralizer (P A C : B) : Subring B where
  carrier := {X | genV P A C * X = X * genV P A C}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    change genV P A C * X = X * genV P A C at hX
    change genV P A C * Y = Y * genV P A C at hY
    change genV P A C * (X + Y) = (X + Y) * genV P A C
    simp only [mul_add, add_mul, hX, hY]
  neg_mem' := by
    intro X hX
    change genV P A C * X = X * genV P A C at hX
    change genV P A C * (-X) = (-X) * genV P A C
    simp only [mul_neg, neg_mul, hX]
  mul_mem' := by
    intro X Y hX hY
    exact genV_centralizer_mul ⟨X, hX⟩ ⟨Y, hY⟩

/-- The total graded derivation as an additive endomorphism on its invariant
centralizer. -/
def centralizerDifferentialHom (A C : B) :
    (metricCentralizer P A C).toAddSubgroup →+
      (metricCentralizer P A C).toAddSubgroup where
  toFun X := ⟨superDerivPhi P A C X.val,
    superDerivPhi_preserves_centralizer hP A C X.val X.property⟩
  map_zero' := by
    apply Subtype.ext
    change superDerivPhi P A C 0 = 0
    simp [superDerivPhi, superDerivPlus, superDerivMinus, parityConj]
  map_add' := by
    intro X Y
    apply Subtype.ext
    change superDerivPhi P A C (X.val + Y.val) =
      superDerivPhi P A C X.val + superDerivPhi P A C Y.val
    simp only [superDerivPhi, superDerivPlus, superDerivMinus, parityConj]
    noncomm_ring

/-- Composition of the centralizer differential with itself is the zero
additive homomorphism. -/
theorem centralizerDifferentialHom_comp_self (A C : B) :
    (centralizerDifferentialHom hP A C).comp (centralizerDifferentialHom hP A C) = 0 := by
  ext X
  change superDerivPhi P A C (superDerivPhi P A C X.val) = 0
  exact (superDerivPhi_square_zero_iff hP A C X.val).2 X.property

/-- Even parity elements in the invariant centralizer. -/
def centralizerParityEven (A C : B) :
    AddSubgroup ((metricCentralizer P A C).toAddSubgroup) where
  carrier := {X | parityConj P X.val = X.val}
  zero_mem' := by
    change parityConj P 0 = 0
    exact (parityConjRingEquiv hP).map_zero
  add_mem' := by
    intro X Y hX hY
    change parityConj P (X.val + Y.val) = X.val + Y.val
    rw [(parityConj_involutive_ring_action hP X.val Y.val).2.2.1, hX, hY]
  neg_mem' := by
    intro X hX
    change parityConj P (-X.val) = -X.val
    calc parityConj P (-X.val) = -parityConj P X.val :=
        (parityConjRingEquiv hP).map_neg X.val
      _ = -X.val := by rw [hX]

/-- Odd parity elements in the invariant centralizer. -/
def centralizerParityOdd (A C : B) :
    AddSubgroup ((metricCentralizer P A C).toAddSubgroup) where
  carrier := {X | parityConj P X.val = -X.val}
  zero_mem' := by
    change parityConj P 0 = -0
    rw [neg_zero]
    exact (parityConjRingEquiv hP).map_zero
  add_mem' := by
    intro X Y hX hY
    change parityConj P (X.val + Y.val) = -(X.val + Y.val)
    rw [(parityConj_involutive_ring_action hP X.val Y.val).2.2.1, hX, hY]
    abel
  neg_mem' := by
    intro X hX
    change parityConj P (-X.val) = -(-X.val)
    calc parityConj P (-X.val) = -parityConj P X.val :=
        (parityConjRingEquiv hP).map_neg X.val
      _ = -(-X.val) := by rw [hX]

/-- The parity-fixed part of the `genV` centralizer is a subring.  Its
multiplication is the degree-zero product for the Peirce grading. -/
def centralizerEvenSubring (A C : B) : Subring B where
  carrier := {x | genV P A C * x = x * genV P A C ∧ parityConj P x = x}
  zero_mem' := by
    constructor
    · simp
    · exact (parityConjRingEquiv hP).map_zero
  one_mem' := by
    constructor
    · simp
    · exact (parityConjRingEquiv hP).map_one
  add_mem' := by
    intro x y hx hy
    change genV P A C * x = x * genV P A C ∧ parityConj P x = x at hx
    change genV P A C * y = y * genV P A C ∧ parityConj P y = y at hy
    constructor
    · change genV P A C * (x + y) = (x + y) * genV P A C
      rw [mul_add, add_mul, hx.1, hy.1]
    · change parityConj P (x + y) = x + y
      rw [(parityConj_involutive_ring_action hP x y).2.2.1, hx.2, hy.2]
  neg_mem' := by
    intro x hx
    change genV P A C * x = x * genV P A C ∧ parityConj P x = x at hx
    constructor
    · change genV P A C * (-x) = (-x) * genV P A C
      rw [mul_neg, neg_mul, hx.1]
    · change parityConj P (-x) = -x
      calc parityConj P (-x) = -parityConj P x :=
          (parityConjRingEquiv hP).map_neg x
        _ = -x := by rw [hx.2]
  mul_mem' := by
    intro x y hx hy
    change genV P A C * x = x * genV P A C ∧ parityConj P x = x at hx
    change genV P A C * y = y * genV P A C ∧ parityConj P y = y at hy
    constructor
    · exact genV_centralizer_mul ⟨x, hx.1⟩ ⟨y, hy.1⟩
    · calc parityConj P (x * y)
          = parityConj P x * parityConj P y :=
            (parityConj_involutive_ring_action hP x y).2.1
        _ = x * y := by rw [hx.2, hy.2]

/-- Left action of the even centralizer on the odd centralizer.  This is a
carrier-level action, rather than an identification of the odd component with
an exterior-algebra one-form space. -/
def centralizerOddLeft (A C : B) (X : centralizerEvenSubring hP A C)
    (Y : centralizerParityOdd hP A C) : centralizerParityOdd hP A C := by
  refine ⟨⟨X.val * Y.val.val, ?_⟩, ?_⟩
  · exact genV_centralizer_mul ⟨X.val, X.property.1⟩ ⟨Y.val.val, Y.val.property⟩
  · change parityConj P (X.val * Y.val.val) = -(X.val * Y.val.val)
    rw [(parityConj_involutive_ring_action hP X.val Y.val.val).2.1,
      X.property.2, Y.property]
    noncomm_ring

/-- Right action of the even centralizer on the odd centralizer. -/
def centralizerOddRight (A C : B) (Y : centralizerParityOdd hP A C)
    (X : centralizerEvenSubring hP A C) : centralizerParityOdd hP A C := by
  refine ⟨⟨Y.val.val * X.val, ?_⟩, ?_⟩
  · exact genV_centralizer_mul ⟨Y.val.val, Y.val.property⟩ ⟨X.val, X.property.1⟩
  · change parityConj P (Y.val.val * X.val) = -(Y.val.val * X.val)
    rw [(parityConj_involutive_ring_action hP Y.val.val X.val).2.1,
      Y.property, X.property.2]
    noncomm_ring

/-- The Peirce odd component is a genuine bimodule over the even centralizer:
the two actions are multiplication in the ambient ring, hence satisfy the
unit, associativity, and commuting-action laws without a commutativity
assumption on either carrier. -/
theorem centralizerOdd_bimodule_laws (A C : B)
    (X X' : centralizerEvenSubring hP A C)
    (Y : centralizerParityOdd hP A C) :
    centralizerOddLeft hP A C 1 Y = Y ∧
    centralizerOddRight hP A C Y 1 = Y ∧
    centralizerOddLeft hP A C X (centralizerOddLeft hP A C X' Y) =
      centralizerOddLeft hP A C (X * X') Y ∧
    centralizerOddRight hP A C (centralizerOddRight hP A C Y X) X' =
      centralizerOddRight hP A C Y (X * X') ∧
    centralizerOddRight hP A C (centralizerOddLeft hP A C X Y) X' =
      centralizerOddLeft hP A C X (centralizerOddRight hP A C Y X') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> apply Subtype.ext <;> apply Subtype.ext <;>
    simp [centralizerOddLeft, centralizerOddRight] <;> noncomm_ring

/-- Both Peirce actions are additive in each variable, completing the
additive bimodule laws alongside `centralizerOdd_bimodule_laws`. -/
theorem centralizerOdd_actions_additive (A C : B)
    (X X' : centralizerEvenSubring hP A C)
    (Y Y' : centralizerParityOdd hP A C) :
    centralizerOddLeft hP A C (X + X') Y =
      centralizerOddLeft hP A C X Y + centralizerOddLeft hP A C X' Y ∧
    centralizerOddLeft hP A C X (Y + Y') =
      centralizerOddLeft hP A C X Y + centralizerOddLeft hP A C X Y' ∧
    centralizerOddRight hP A C (Y + Y') X =
      centralizerOddRight hP A C Y X + centralizerOddRight hP A C Y' X ∧
    centralizerOddRight hP A C Y (X + X') =
      centralizerOddRight hP A C Y X + centralizerOddRight hP A C Y X' := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Subtype.ext <;> apply Subtype.ext <;>
    simp [centralizerOddLeft, centralizerOddRight] <;> noncomm_ring

/-- The left bimodule action, bundled as a linear endomorphism of the odd
carrier. -/
def centralizerOddLeftLinear (A C : B)
    (X : centralizerEvenSubring hP A C) :
    Module.End ℤ (centralizerParityOdd hP A C) where
  toFun := centralizerOddLeft hP A C X
  map_add' Y Y' := by
    apply Subtype.ext
    apply Subtype.ext
    simp [centralizerOddLeft]
    noncomm_ring
  map_smul' n Y := by
    apply Subtype.ext
    apply Subtype.ext
    change X.val * (n • Y.val.val) = n • (X.val * Y.val.val)
    rw [zsmul_eq_mul, zsmul_eq_mul]
    calc X.val * ((n : B) * Y.val.val)
        = (X.val * (n : B)) * Y.val.val := by rw [mul_assoc]
      _ = ((n : B) * X.val) * Y.val.val := by
        rw [(Int.cast_commute n X.val).eq]
      _ = (n : B) * (X.val * Y.val.val) := by rw [← mul_assoc]

/-- The even Peirce algebra acts faithfully by left multiplication operators
on its odd centralizer bimodule.  This is the concrete algebra morphism that
records the carrier soldering at the source side. -/
def centralizerOddLeftRepresentation (A C : B) :
    centralizerEvenSubring hP A C →+* Module.End ℤ (centralizerParityOdd hP A C) where
  toFun := centralizerOddLeftLinear hP A C
  map_zero' := by
    ext Y
    simp [centralizerOddLeftLinear, centralizerOddLeft]
  map_add' X X' := by
    ext Y
    simp [centralizerOddLeftLinear, centralizerOddLeft]
    noncomm_ring
  map_one' := by
    ext Y
    simp [centralizerOddLeftLinear, centralizerOddLeft]
  map_mul' X X' := by
    ext Y
    simp [centralizerOddLeftLinear, centralizerOddLeft]
    noncomm_ring

/-- Evaluation of the left representation is precisely the Peirce module
action. -/
@[simp] theorem centralizerOddLeftRepresentation_apply (A C : B)
    (X : centralizerEvenSubring hP A C) (Y : centralizerParityOdd hP A C) :
    centralizerOddLeftRepresentation hP A C X Y = centralizerOddLeft hP A C X Y :=
  rfl

/-- Regard an element of the even subring as an element of the even parity
subgroup, retaining the centralizer witness. -/
def centralizerEvenToParity (A C : B)
    (X : centralizerEvenSubring hP A C) : centralizerParityEven hP A C :=
  ⟨⟨X.val, X.property.1⟩, X.property.2⟩

/-- On the even centralizer subring, the Peirce differential is an ordinary
Leibniz derivation (with values in the odd centralizer component).  This is
the precise algebraic input for the degree-zero-to-degree-one part of a
differential-form soldering. -/
theorem centralizerDifferential_even_leibniz (A C : B)
    (X Y : centralizerEvenSubring hP A C) :
    (centralizerDifferential hP A C
      ⟨X.val * Y.val, genV_centralizer_mul
        ⟨X.val, (show genV P A C * X.val = X.val * genV P A C ∧
          parityConj P X.val = X.val from X.property).1⟩
        ⟨Y.val, (show genV P A C * Y.val = Y.val * genV P A C ∧
          parityConj P Y.val = Y.val from Y.property).1⟩⟩).val =
      (centralizerDifferential hP A C
        ⟨X.val, (show genV P A C * X.val = X.val * genV P A C ∧
          parityConj P X.val = X.val from X.property).1⟩).val * Y.val +
        X.val * (centralizerDifferential hP A C
          ⟨Y.val, (show genV P A C * Y.val = Y.val * genV P A C ∧
            parityConj P Y.val = Y.val from Y.property).1⟩).val := by
  have hX : genV P A C * X.val = X.val * genV P A C ∧
      parityConj P X.val = X.val := by
    exact X.property
  have hY : genV P A C * Y.val = Y.val * genV P A C ∧
      parityConj P Y.val = Y.val := by
    exact Y.property
  have hDX : (centralizerDifferential hP A C
    ⟨X.val, hX.1⟩).val = superDerivPhi P A C X.val := rfl
  have hDY : (centralizerDifferential hP A C
    ⟨Y.val, hY.1⟩).val = superDerivPhi P A C Y.val := rfl
  rw [hDX, hDY]
  change superDerivPhi P A C (X.val * Y.val) = _
  rw [superDerivPhi_twisted_leibniz hP A C X.val Y.val, hX.2]

/-- The square-zero Peirce differential restricted to the even parity
subgroup, with its codomain refined to the odd parity subgroup. -/
def centralizerDifferentialEvenToOdd (A C : B) :
    centralizerParityEven hP A C → centralizerParityOdd hP A C := by
  intro X
  refine ⟨centralizerDifferentialHom hP A C X.val, ?_⟩
  have h := centralizerDifferential_parity_odd hP A C X.val
  have h_same : centralizerDifferential hP A C
      ⟨parityConj P X.val, parityConj_preserves_genV_centralizer hP A C X.val X.val.property⟩ =
      centralizerDifferential hP A C X.val := by
    apply Subtype.ext
    exact congrArg (superDerivPhi P A C) X.property
  change parityConj P (superDerivPhi P A C X.val) = -superDerivPhi P A C X.val
  change parityConj P (centralizerDifferential hP A C X.val).val = _ at h
  rw [h_same] at h
  exact h

/-- The square-zero Peirce differential restricted to the odd parity
subgroup, with its codomain refined to the even parity subgroup. -/
def centralizerDifferentialOddToEven (A C : B) :
    centralizerParityOdd hP A C → centralizerParityEven hP A C := by
  intro X
  refine ⟨centralizerDifferentialHom hP A C X.val, ?_⟩
  have h := centralizerDifferential_parity_odd hP A C X.val
  have h_par : parityConj P X.val = -X.val := X.property
  have h_neg : (centralizerDifferential hP A C
      ⟨parityConj P X.val, parityConj_preserves_genV_centralizer hP A C X.val X.val.property⟩).val =
      -(centralizerDifferential hP A C X.val).val := by
    change superDerivPhi P A C (parityConj P X.val) = -superDerivPhi P A C X.val
    rw [h_par]
    have hn := congrArg Subtype.val (map_neg (centralizerDifferentialHom hP A C) X.val)
    change superDerivPhi P A C (-X.val) = -superDerivPhi P A C X.val at hn
    exact hn
  change parityConj P (superDerivPhi P A C X.val) = superDerivPhi P A C X.val
  change parityConj P (centralizerDifferential hP A C X.val).val = _ at h
  rw [h_neg] at h
  simpa [centralizerDifferential] using h

/-- The Peirce differential from the even algebra, now with its codomain
refined to the odd bimodule. -/
def centralizerEvenBimoduleDeriv (A C : B)
    (X : centralizerEvenSubring hP A C) : centralizerParityOdd hP A C :=
  centralizerDifferentialEvenToOdd hP A C (centralizerEvenToParity hP A C X)

/-- The degree-zero Peirce differential is a derivation into the odd
bimodule: its Leibniz rule uses the actual left and right module actions. -/
theorem centralizerEvenBimoduleDeriv_leibniz (A C : B)
    (X Y : centralizerEvenSubring hP A C) :
    centralizerEvenBimoduleDeriv hP A C (X * Y) =
      centralizerOddLeft hP A C X (centralizerEvenBimoduleDeriv hP A C Y) +
        centralizerOddRight hP A C (centralizerEvenBimoduleDeriv hP A C X) Y := by
  apply Subtype.ext
  apply Subtype.ext
  change (centralizerDifferential hP A C
      ⟨X.val * Y.val, genV_centralizer_mul
        ⟨X.val, X.property.1⟩ ⟨Y.val, Y.property.1⟩⟩).val = _
  rw [centralizerDifferential_even_leibniz hP A C X Y]
  change (centralizerDifferential hP A C ⟨X.val, X.property.1⟩).val * Y.val +
      X.val * (centralizerDifferential hP A C ⟨Y.val, Y.property.1⟩).val =
    X.val * (centralizerDifferential hP A C ⟨Y.val, Y.property.1⟩).val +
      (centralizerDifferential hP A C ⟨X.val, X.property.1⟩).val * Y.val
  abel

/-- Pair an even Peirce element with the differential of a second element by
the left action on the odd centralizer. -/
def centralizerEvenBimoduleDerivAddHom (A C : B) :
    centralizerEvenSubring hP A C →+
      centralizerParityOdd hP A C where
  toFun := centralizerEvenBimoduleDeriv hP A C
  map_zero' := by
    apply Subtype.ext
    apply Subtype.ext
    simp [centralizerEvenBimoduleDeriv, centralizerDifferentialEvenToOdd,
      centralizerEvenToParity, centralizerDifferentialHom, superDerivPhi,
      superDerivPlus, superDerivMinus, parityConj]
  map_add' X Y := by
    apply Subtype.ext
    apply Subtype.ext
    change superDerivPhi P A C (X.val + Y.val) =
      superDerivPhi P A C X.val + superDerivPhi P A C Y.val
    simp only [superDerivPhi, superDerivPlus, superDerivMinus, parityConj]
    noncomm_ring

/-- Pair an even Peirce element with the differential of a second element by
the left action on the odd centralizer. -/
def centralizerEvenDerivPairing (A C : B) :
    centralizerEvenSubring hP A C →+
      centralizerEvenSubring hP A C →+
        centralizerParityOdd hP A C where
  toFun X := (centralizerOddLeftLinear hP A C X).toAddMonoidHom.comp
    (centralizerEvenBimoduleDerivAddHom hP A C)
  map_zero' := by
    apply AddMonoidHom.ext
    intro Y
    apply Subtype.ext
    apply Subtype.ext
    simp [centralizerOddLeftLinear, centralizerOddLeft]
  map_add' X X' := by
    apply AddMonoidHom.ext
    intro Y
    apply Subtype.ext
    apply Subtype.ext
    simp [centralizerOddLeftLinear, centralizerOddLeft]
    noncomm_ring

/-- Integer scalars can be moved between the two slots of the Peirce action
pairing, so it descends to the balanced tensor product over `ℤ`. -/
theorem centralizerEvenDerivPairing_balanced (A C : B)
    (n : ℤ) (X Y : centralizerEvenSubring hP A C) :
    centralizerEvenDerivPairing hP A C (n • X) Y =
      centralizerEvenDerivPairing hP A C X (n • Y) := by
  apply Subtype.ext
  apply Subtype.ext
  change (n • X.val) * (centralizerEvenBimoduleDeriv hP A C Y).val =
    X.val * (centralizerEvenBimoduleDeriv hP A C (n • Y)).val
  have hD :
      (centralizerEvenBimoduleDeriv hP A C (n • Y)).val.val =
        n • (centralizerEvenBimoduleDeriv hP A C Y).val.val := by
    change ((centralizerEvenBimoduleDerivAddHom hP A C) (n • Y)).val.val = _
    exact congrArg (fun Z : centralizerParityOdd hP A C => Z.val.val)
      ((centralizerEvenBimoduleDerivAddHom hP A C).map_zsmul n Y)
  rw [hD]
  rw [zsmul_eq_mul, zsmul_eq_mul]
  rw [(Int.cast_commute n X.val).eq]
  noncomm_ring

/-- The Peirce derivation of the unit in the even centralizer is zero. -/
theorem centralizerEvenBimoduleDeriv_one (A C : B) :
    centralizerEvenBimoduleDeriv hP A C (1 : centralizerEvenSubring hP A C) = 0 := by
  have hS : invS P * invS P = 1 := by
    simp only [invS]
    noncomm_ring [hP]
  apply Subtype.ext
  apply Subtype.ext
  simp [centralizerEvenBimoduleDeriv, centralizerDifferentialEvenToOdd,
    centralizerEvenToParity, centralizerDifferentialHom, superDerivPhi,
    superDerivPlus, superDerivMinus, parityConj, hS]

/-- Evaluation of universal noncommutative one-forms in the Peirce odd
bimodule, induced by the actual even left action and Peirce differential. -/
def centralizerUniversalFormEvaluation (A C : B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms.OneForms
        (centralizerEvenSubring hP A C) →+
      centralizerParityOdd hP A C where
  toFun ω :=
    InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms.tensorAddHom
      (centralizerEvenSubring hP A C) (centralizerEvenDerivPairing hP A C)
      (centralizerEvenDerivPairing_balanced hP A C) ω.val
  map_zero' := by
    simp [InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms.tensorAddHom]
  map_add' _ _ := by
    simp [InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms.tensorAddHom]

/-- On the universal differential, evaluation recovers the Peirce
derivation. This is the concrete carrier soldering from the centralizer
calculus to universal noncommutative one-forms. -/
theorem centralizerUniversalFormEvaluation_differential (A C : B)
    (X : centralizerEvenSubring hP A C) :
    centralizerUniversalFormEvaluation hP A C
      (InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms.differential
        (centralizerEvenSubring hP A C) X) =
      centralizerEvenBimoduleDeriv hP A C X := by
  have h_eval :=
    InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms.tensorAddHom_differential
      (centralizerEvenSubring hP A C) (centralizerEvenDerivPairing hP A C)
      (centralizerEvenDerivPairing_balanced hP A C) X
  have h_unit : centralizerEvenDerivPairing hP A C 1 X =
      centralizerEvenBimoduleDeriv hP A C X := by
    apply Subtype.ext
    apply Subtype.ext
    simp [centralizerEvenDerivPairing, centralizerOddLeftLinear,
      centralizerOddLeft, centralizerEvenBimoduleDerivAddHom]
  have h_right : centralizerEvenDerivPairing hP A C X 1 = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    change X.val * (centralizerEvenBimoduleDeriv hP A C 1).val = 0
    rw [centralizerEvenBimoduleDeriv_one hP A C]
    simp
  rw [h_unit, h_right, sub_zero] at h_eval
  change InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms.tensorAddHom
      (centralizerEvenSubring hP A C) (centralizerEvenDerivPairing hP A C)
      (centralizerEvenDerivPairing_balanced hP A C)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms.differential
        (centralizerEvenSubring hP A C) X).val = _
  exact h_eval

/-- The universal-form evaluation sends the generator `X · dᵤ Y` to the
actual left action `X · dY` on the Peirce odd bimodule. -/
theorem centralizerUniversalFormEvaluation_leftDifferential (A C : B)
    (X Y : centralizerEvenSubring hP A C) :
    centralizerUniversalFormEvaluation hP A C
        (InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms.leftDifferentialForm
          (centralizerEvenSubring hP A C) X Y) =
      centralizerOddLeft hP A C X (centralizerEvenBimoduleDeriv hP A C Y) := by
  have h_eval :=
    InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms.tensorAddHom_leftDifferentialTensor
      (centralizerEvenSubring hP A C) (centralizerEvenDerivPairing hP A C)
      (centralizerEvenDerivPairing_balanced hP A C) X Y
  have h_d_one := centralizerEvenBimoduleDeriv_one hP A C
  change InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms.tensorAddHom
      (centralizerEvenSubring hP A C) (centralizerEvenDerivPairing hP A C)
      (centralizerEvenDerivPairing_balanced hP A C)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms.leftDifferentialTensor
        (centralizerEvenSubring hP A C) X Y) = _
  rw [h_eval]
  simp [centralizerOddLeftLinear, centralizerOddLeft,
    centralizerEvenDerivPairing, centralizerEvenBimoduleDerivAddHom,
    h_d_one]

/-- The universal one-form evaluation sends the universal Leibniz split of
`dᵤ (XY)` to the actual left/right bimodule Leibniz rule of the Peirce
differential. This identifies the universal-form soldering with the source
connection calculus on products, not only on individual differentials. -/
theorem centralizerUniversalFormEvaluation_product (A C : B)
    (X Y : centralizerEvenSubring hP A C) :
    centralizerUniversalFormEvaluation hP A C
        (InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms.differential
          (centralizerEvenSubring hP A C) (X * Y)) =
      centralizerOddLeft hP A C X (centralizerEvenBimoduleDeriv hP A C Y) +
        centralizerOddRight hP A C (centralizerEvenBimoduleDeriv hP A C X) Y := by
  rw [centralizerUniversalFormEvaluation_differential]
  exact centralizerEvenBimoduleDeriv_leibniz hP A C X Y

/-- The two parity-restricted arrows compose to zero, giving a genuine
two-periodic chain complex on the Peirce centralizer. -/
theorem centralizerParityComplex_square_zero (A C : B) :
    (∀ X : centralizerParityEven hP A C,
      centralizerDifferentialOddToEven hP A C
        (centralizerDifferentialEvenToOdd hP A C X) = 0) ∧
    (∀ X : centralizerParityOdd hP A C,
      centralizerDifferentialEvenToOdd hP A C
        (centralizerDifferentialOddToEven hP A C X) = 0) := by
  have hsq := centralizerDifferentialHom_comp_self hP A C
  constructor <;> intro X <;> apply Subtype.ext <;> apply Subtype.ext
  · have h := congrArg (fun f : (metricCentralizer P A C).toAddSubgroup →+
      (metricCentralizer P A C).toAddSubgroup => f X.val) hsq
    have hv := congrArg Subtype.val h
    simpa [AddMonoidHom.comp_apply, centralizerDifferentialEvenToOdd,
      centralizerDifferentialOddToEven] using hv
  · have h := congrArg (fun f : (metricCentralizer P A C).toAddSubgroup →+
      (metricCentralizer P A C).toAddSubgroup => f X.val) hsq
    have hv := congrArg Subtype.val h
    simpa [AddMonoidHom.comp_apply, centralizerDifferentialEvenToOdd,
      centralizerDifferentialOddToEven] using hv

end InfoGeometry.OperatorAlgebra.PeirceSpine
