import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2UnipotentRootSubgroup

/-!
# A concrete finite split-Zorn automorphism

The coordinate transposition `0 ↔ 1` in both vector slots is an actual
automorphism of the characteristic-two Zorn multiplication.  This gives a
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

namespace InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def swap01Fun : SplitOctF2 → SplitOctF2
  | ⟨a, b, x0, x1, x2, y0, y1, y2⟩ =>
      ⟨a, b, x1, x0, x2, y1, y0, y2⟩

noncomputable def swap01Equiv : SplitOctF2 ≃ SplitOctF2 where
  toFun := swap01Fun
  invFun := swap01Fun
  left_inv := by intro X; cases X <;> rfl
  right_inv := by intro X; cases X <;> rfl

theorem swap01_add (X Y : SplitOctF2) :
    swap01Fun (add X Y) = add (swap01Fun X) (swap01Fun Y) := by
  rcases X with ⟨a1, b1, x01, x11, x21, y01, y11, y21⟩
  rcases Y with ⟨a2, b2, x02, x12, x22, y02, y12, y22⟩
  ext <;> simp [swap01Fun, add, add2]

theorem swap01_mul (X Y : SplitOctF2) :
    swap01Fun (mul X Y) = mul (swap01Fun X) (swap01Fun Y) := by
  rcases X with ⟨a1, b1, x01, x11, x21, y01, y11, y21⟩
  rcases Y with ⟨a2, b2, x02, x12, x22, y02, y12, y22⟩
  revert a1 b1 x01 x11 x21 y01 y11 y21 a2 b2 x02 x12 x22 y02 y12 y22
  native_decide

noncomputable def swap01Aut : SplitOctF2Aut :=
  ⟨swap01Equiv, by
    refine ⟨?_, ?_, ?_⟩
    · rfl
    · intro X Y
      exact swap01_add X Y
    · intro X Y
      exact swap01_mul X Y⟩

theorem swap01Aut_apply (X : SplitOctF2) :
    swap01Aut.1 X = swap01Fun X :=
  rfl

theorem swap01Aut_sq :
    swap01Aut * swap01Aut = (1 : SplitOctF2Aut) := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  cases X <;> rfl

theorem swap01Aut_ne_one :
    swap01Aut ≠ (1 : SplitOctF2Aut) := by
  intro h
  have h_apply := congrArg (fun f : SplitOctF2Aut => f.1 up0) h
  have hx := congrArg (fun X : SplitOctF2 => X.x0) h_apply
  change false = true at hx
  exact Bool.noConfusion hx

def cycle012Fun : SplitOctF2 → SplitOctF2
  | ⟨a, b, x0, x1, x2, y0, y1, y2⟩ =>
      ⟨a, b, x1, x2, x0, y1, y2, y0⟩

noncomputable def cycle012Equiv : SplitOctF2 ≃ SplitOctF2 where
  toFun := cycle012Fun
  invFun := fun ⟨a, b, x0, x1, x2, y0, y1, y2⟩ =>
    ⟨a, b, x2, x0, x1, y2, y0, y1⟩
  left_inv := by intro X; cases X <;> rfl
  right_inv := by intro X; cases X <;> rfl

theorem cycle012_add (X Y : SplitOctF2) :
    cycle012Fun (add X Y) = add (cycle012Fun X) (cycle012Fun Y) := by
  rcases X with ⟨a1, b1, x01, x11, x21, y01, y11, y21⟩
  rcases Y with ⟨a2, b2, x02, x12, x22, y02, y12, y22⟩
  ext <;> simp [cycle012Fun, add, add2]

theorem cycle012_mul (X Y : SplitOctF2) :
    cycle012Fun (mul X Y) = mul (cycle012Fun X) (cycle012Fun Y) := by
  rcases X with ⟨a1, b1, x01, x11, x21, y01, y11, y21⟩
  rcases Y with ⟨a2, b2, x02, x12, x22, y02, y12, y22⟩
  revert a1 b1 x01 x11 x21 y01 y11 y21 a2 b2 x02 x12 x22 y02 y12 y22
  native_decide

noncomputable def cycle012Aut : SplitOctF2Aut :=
  ⟨cycle012Equiv, by
    refine ⟨?_, ?_, ?_⟩
    · rfl
    · intro X Y
      exact cycle012_add X Y
    · intro X Y
      exact cycle012_mul X Y⟩

theorem cycle012Aut_apply (X : SplitOctF2) :
    cycle012Aut.1 X = cycle012Fun X :=
  rfl

theorem cycle012Aut_cube :
    cycle012Aut * cycle012Aut * cycle012Aut = (1 : SplitOctF2Aut) := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  cases X <;> rfl

theorem cycle012Aut_ne_one : cycle012Aut ≠ (1 : SplitOctF2Aut) := by
  intro h
  have h_apply := congrArg (fun f : SplitOctF2Aut => (f.1 up0).x2) h
  revert h_apply
  decide

end InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

namespace InfoGeometry.Algebra.Zorn.G2Unipotent

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem unipotentShortAut_true_ne_one :
    unipotentShortAut true ≠ (1 : SplitOctF2Aut) := by
  intro h
  have h_apply := congrArg (fun f : SplitOctF2Aut => (f.1 up1).x0) h
  revert h_apply
  decide

theorem unipotentLongAut_true_ne_one :
    unipotentLongAut true ≠ (1 : SplitOctF2Aut) := by
  intro h
  have h_apply := congrArg (fun f : SplitOctF2Aut => (f.1 up2).x1) h
  revert h_apply
  decide

theorem simple_root_generators_distinct :
    unipotentShortAut true ≠ unipotentLongAut true := by
  intro h
  have h_apply := congrArg (fun f : SplitOctF2Aut => (f.1 up1).x0) h
  revert h_apply
  decide

noncomputable def conjugateAut (g u : SplitOctF2Aut) : SplitOctF2Aut :=
  g * u * g⁻¹

noncomputable def automorphismCommutator (g h : SplitOctF2Aut) : SplitOctF2Aut :=
  g * h * g⁻¹ * h⁻¹

@[simp] theorem automorphism_mul_apply (g h : SplitOctF2Aut) (X : SplitOctF2) :
    (g * h).1 X = h.1 (g.1 X) := by
  rfl

@[simp] theorem automorphism_inv_apply (g : SplitOctF2Aut) (X : SplitOctF2) :
    g⁻¹.1 X = g.1.symm X := rfl

@[simp] theorem unipotentShortAut_apply (t : Bool) (X : SplitOctF2) :
    (unipotentShortAut t).1 X = unipotentShort t X := rfl

@[simp] theorem unipotentLongAut_apply (t : Bool) (X : SplitOctF2) :
    (unipotentLongAut t).1 X = unipotentLong t X := rfl

@[simp] theorem simpleRootProduct_apply (X : SplitOctF2) :
    (unipotentShortAut true * unipotentLongAut true).1 X =
      unipotentLong true (unipotentShort true X) := by
  rfl

theorem simpleRootProduct_four :
    (unipotentShortAut true * unipotentLongAut true) ^ 4 =
      (1 : SplitOctF2Aut) := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  have hone : (1 : SplitOctF2Aut).1 X = X := by rfl
  rw [hone]
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  revert a b x0 x1 x2 y0 y1 y2
  decide

theorem simpleRootProduct_ne_one :
        unipotentShortAut true * unipotentLongAut true ≠
          (1 : SplitOctF2Aut) := by
  intro h
  have h_apply := congrArg
    (fun f : SplitOctF2Aut => f.1 up1) h
  have hx := congrArg (fun Z : SplitOctF2 => Z.x0) h_apply
  change ((unipotentShortAut true * unipotentLongAut true).1 up1).x0 =
    up1.x0 at hx
  have hx' : false = true := by
    simpa [automorphism_mul_apply, simpleRootProduct_apply,
      unipotentShort, unipotentLong, add2, one, up1] using hx
  cases hx'

theorem simpleRootProduct_sq_ne_one :
        (unipotentShortAut true * unipotentLongAut true) ^ 2 ≠
          (1 : SplitOctF2Aut) := by
  intro h
  have h_apply := congrArg
    (fun f : SplitOctF2Aut => f.1 up2) h
  have hx := congrArg (fun Z : SplitOctF2 => Z.x0) h_apply
  change (((unipotentShortAut true * unipotentLongAut true) ^ 2).1 up2).x0 =
    up2.x0 at hx
  have hx' : false = true := by
    simpa [pow_succ, automorphism_mul_apply, simpleRootProduct_apply,
      unipotentShort, unipotentLong, add2, one, up2] using hx
  cases hx'

theorem simpleRootProduct_exact_order_four :
    (unipotentShortAut true * unipotentLongAut true) ^ 4 =
        (1 : SplitOctF2Aut) ∧
      (unipotentShortAut true * unipotentLongAut true) ^ 2 ≠
        (1 : SplitOctF2Aut) ∧
      unipotentShortAut true * unipotentLongAut true ≠
        (1 : SplitOctF2Aut) := by
  exact ⟨simpleRootProduct_four, simpleRootProduct_sq_ne_one,
    simpleRootProduct_ne_one⟩

theorem unipotentShortAut_inv (t : Bool) :
    (unipotentShortAut t)⁻¹ = unipotentShortAut t := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rfl

theorem unipotentLongAut_inv (t : Bool) :
    (unipotentLongAut t)⁻¹ = unipotentLongAut t := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rfl

theorem automorphismCommutator_eq_one_iff (g h : SplitOctF2Aut) :
    automorphismCommutator g h = 1 ↔ g * h = h * g := by
  constructor
  · intro hc
    have hc' := congrArg (fun z : SplitOctF2Aut => z * h * g) hc
    simpa [automorphismCommutator, mul_assoc] using hc'
  · intro hcomm
    calc
      automorphismCommutator g h = (g * h) * (g⁻¹ * h⁻¹) := by
        simp [automorphismCommutator, mul_assoc]
      _ = (h * g) * (g⁻¹ * h⁻¹) := by rw [hcomm]
      _ = 1 := by group

theorem conjugateAut_commutator (k g h : SplitOctF2Aut) :
    automorphismCommutator (conjugateAut k g) (conjugateAut k h) =
      conjugateAut k (automorphismCommutator g h) := by
  simp [automorphismCommutator, conjugateAut, mul_assoc]

theorem simple_root_commutator_ne_one :
    automorphismCommutator (unipotentShortAut true) (unipotentLongAut true) ≠
      (1 : SplitOctF2Aut) := by
  intro h
  have hcoord := congrArg
    (fun f : SplitOctF2Aut => (f.1 up2).x0) h
  revert hcoord
  decide

theorem simple_root_generators_do_not_commute :
    unipotentShortAut true * unipotentLongAut true ≠
      unipotentLongAut true * unipotentShortAut true := by
  intro h
  apply simple_root_commutator_ne_one
  exact (automorphismCommutator_eq_one_iff _ _).2 h

theorem conjugateAut_sq (g u : SplitOctF2Aut) (hu : u * u = 1) :
    conjugateAut g u * conjugateAut g u = 1 := by
  calc
    conjugateAut g u * conjugateAut g u = g * (u * u) * g⁻¹ := by
      simp [conjugateAut, mul_assoc]
    _ = 1 := by rw [hu]; simp

theorem conjugateAut_ne_one (g u : SplitOctF2Aut) (hu : u ≠ 1) :
    conjugateAut g u ≠ 1 := by
  intro h
  apply hu
  have h' := congrArg (fun z : SplitOctF2Aut => g⁻¹ * z * g) h
  simpa [conjugateAut, ← mul_assoc] using h'

theorem conjugateAut_add (g : SplitOctF2Aut) (u : Bool → SplitOctF2Aut)
    (hu : ∀ s t, u (s ^^ t) = u s * u t) (s t : Bool) :
    conjugateAut g (u (s ^^ t)) =
      conjugateAut g (u s) * conjugateAut g (u t) := by
  rw [hu]
  simp [conjugateAut, mul_assoc]

noncomputable def swapConjugatedShort : SplitOctF2Aut :=
  conjugateAut swap01Aut (unipotentShortAut true)

noncomputable def swapConjugatedLong : SplitOctF2Aut :=
  conjugateAut swap01Aut (unipotentLongAut true)

theorem swapConjugated_generator_packet :
    swapConjugatedShort * swapConjugatedShort = 1 ∧
    swapConjugatedLong * swapConjugatedLong = 1 ∧
    swapConjugatedShort ≠ (1 : SplitOctF2Aut) ∧
    swapConjugatedLong ≠ (1 : SplitOctF2Aut) := by
  exact ⟨conjugateAut_sq _ _ (unipotentShortAut_order true),
    conjugateAut_sq _ _ (unipotentLongAut_order true),
    conjugateAut_ne_one _ _ unipotentShortAut_true_ne_one,
    conjugateAut_ne_one _ _ unipotentLongAut_true_ne_one⟩

theorem unipotentShortAut_add (s t : Bool) :
    unipotentShortAut (s ^^ t) =
      unipotentShortAut s * unipotentShortAut t := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  cases s <;> cases t
  · rfl
  · rfl
  · rfl
  · change X = (unipotentShortAut true * unipotentShortAut true).1 X
    simpa using congrArg (fun f : SplitOctF2Aut => f.1 X)
      (unipotentShortAut_order true).symm

theorem unipotentLongAut_add (s t : Bool) :
    unipotentLongAut (s ^^ t) =
      unipotentLongAut s * unipotentLongAut t := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  cases s <;> cases t
  · rfl
  · rfl
  · rfl
  · change X = (unipotentLongAut true * unipotentLongAut true).1 X
    simpa using congrArg (fun f : SplitOctF2Aut => f.1 X)
      (unipotentLongAut_order true).symm

theorem swapConjugatedShort_add (s t : Bool) :
    conjugateAut swap01Aut (unipotentShortAut (s ^^ t)) =
      conjugateAut swap01Aut (unipotentShortAut s) *
        conjugateAut swap01Aut (unipotentShortAut t) := by
  exact conjugateAut_add swap01Aut unipotentShortAut
    unipotentShortAut_add s t

theorem swapConjugatedLong_add (s t : Bool) :
    conjugateAut swap01Aut (unipotentLongAut (s ^^ t)) =
      conjugateAut swap01Aut (unipotentLongAut s) *
        conjugateAut swap01Aut (unipotentLongAut t) := by
  exact conjugateAut_add swap01Aut unipotentLongAut
    unipotentLongAut_add s t

/-!
The cyclic Weyl representative produces further concrete root candidates by
conjugation.  These definitions record only consequences of group
conjugation; no claim of distinctness or of a completed BN-pair is made here.
-/

noncomputable def cycleConjugatedShort : Fin 3 → SplitOctF2Aut
  | 0 => unipotentShortAut true
  | 1 => conjugateAut cycle012Aut (unipotentShortAut true)
  | 2 => conjugateAut (cycle012Aut * cycle012Aut) (unipotentShortAut true)

noncomputable def cycleConjugatedLong : Fin 3 → SplitOctF2Aut
  | 0 => unipotentLongAut true
  | 1 => conjugateAut cycle012Aut (unipotentLongAut true)
  | 2 => conjugateAut (cycle012Aut * cycle012Aut) (unipotentLongAut true)

/-! The cyclic conjugation data already exhibits overlap between the two
families.  Thus these six candidates cannot by themselves be treated as six
independent positive-root coordinates. -/

theorem cycleConjugatedShort_one_eq_long_zero :
    cycleConjugatedShort 1 = cycleConjugatedLong 0 := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  cases X <;> rfl

theorem cycleConjugatedLong_injective :
    Function.Injective cycleConjugatedLong := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    have h0 := congrArg (fun f : SplitOctF2Aut => f.1 up0) h
    have h1 := congrArg (fun f : SplitOctF2Aut => f.1 up1) h
    have h2 := congrArg (fun f : SplitOctF2Aut => f.1 up2) h
    revert h0 h1 h2
    decide

theorem cycleConjugatedShort_packet (i : Fin 3) :
    cycleConjugatedShort i * cycleConjugatedShort i = 1 ∧
    cycleConjugatedShort i ≠ (1 : SplitOctF2Aut) := by
  fin_cases i
  · exact ⟨unipotentShortAut_order true, unipotentShortAut_true_ne_one⟩
  · exact ⟨conjugateAut_sq _ _ (unipotentShortAut_order true),
      conjugateAut_ne_one _ _ unipotentShortAut_true_ne_one⟩
  · exact ⟨conjugateAut_sq _ _ (unipotentShortAut_order true),
      conjugateAut_ne_one _ _ unipotentShortAut_true_ne_one⟩

theorem cycleConjugatedLong_packet (i : Fin 3) :
    cycleConjugatedLong i * cycleConjugatedLong i = 1 ∧
    cycleConjugatedLong i ≠ (1 : SplitOctF2Aut) := by
  fin_cases i
  · exact ⟨unipotentLongAut_order true, unipotentLongAut_true_ne_one⟩
  · exact ⟨conjugateAut_sq _ _ (unipotentLongAut_order true),
      conjugateAut_ne_one _ _ unipotentLongAut_true_ne_one⟩
  · exact ⟨conjugateAut_sq _ _ (unipotentLongAut_order true),
      conjugateAut_ne_one _ _ unipotentLongAut_true_ne_one⟩

noncomputable def cycleConjugatedShortParam (i : Fin 3) (t : Bool) :
    SplitOctF2Aut := if t then cycleConjugatedShort i else 1

noncomputable def cycleConjugatedLongParam (i : Fin 3) (t : Bool) :
    SplitOctF2Aut := if t then cycleConjugatedLong i else 1

theorem cycleConjugatedShortParam_add (i : Fin 3) (s t : Bool) :
    cycleConjugatedShortParam i (s ^^ t) =
      cycleConjugatedShortParam i s * cycleConjugatedShortParam i t := by
  cases s <;> cases t
  · rfl
  · simp [cycleConjugatedShortParam]
  · simp [cycleConjugatedShortParam]
  · simpa [cycleConjugatedShortParam] using
      (cycleConjugatedShort_packet i).1.symm

theorem cycleConjugatedLongParam_add (i : Fin 3) (s t : Bool) :
    cycleConjugatedLongParam i (s ^^ t) =
      cycleConjugatedLongParam i s * cycleConjugatedLongParam i t := by
  cases s <;> cases t
  · rfl
  · simp [cycleConjugatedLongParam]
  · simp [cycleConjugatedLongParam]
  · simpa [cycleConjugatedLongParam] using
      (cycleConjugatedLong_packet i).1.symm

theorem cycleConjugatedShortParam_comm (i : Fin 3) (s t : Bool) :
    cycleConjugatedShortParam i s * cycleConjugatedShortParam i t =
      cycleConjugatedShortParam i t * cycleConjugatedShortParam i s := by
  rw [← cycleConjugatedShortParam_add, ← cycleConjugatedShortParam_add,
    Bool.xor_comm]

theorem cycleConjugatedLongParam_comm (i : Fin 3) (s t : Bool) :
    cycleConjugatedLongParam i s * cycleConjugatedLongParam i t =
      cycleConjugatedLongParam i t * cycleConjugatedLongParam i s := by
  rw [← cycleConjugatedLongParam_add, ← cycleConjugatedLongParam_add,
    Bool.xor_comm]

theorem cycleConjugatedShortParam_commutator_eq_one (i : Fin 3) (s t : Bool) :
    automorphismCommutator (cycleConjugatedShortParam i s)
      (cycleConjugatedShortParam i t) = 1 := by
  exact (automorphismCommutator_eq_one_iff _ _).2
    (cycleConjugatedShortParam_comm i s t)

theorem cycleConjugatedLongParam_commutator_eq_one (i : Fin 3) (s t : Bool) :
    automorphismCommutator (cycleConjugatedLongParam i s)
      (cycleConjugatedLongParam i t) = 1 := by
  exact (automorphismCommutator_eq_one_iff _ _).2
    (cycleConjugatedLongParam_comm i s t)

/-! A single indexed interface for the six concrete root candidates. -/

noncomputable def candidateRootFamily : Fin 6 → Bool → SplitOctF2Aut
  | 0 => cycleConjugatedShortParam 0
  | 1 => cycleConjugatedShortParam 1
  | 2 => cycleConjugatedShortParam 2
  | 3 => cycleConjugatedLongParam 0
  | 4 => cycleConjugatedLongParam 1
  | 5 => cycleConjugatedLongParam 2

theorem candidateRootFamily_same_root_commutator (i : Fin 6) (s t : Bool) :
    automorphismCommutator (candidateRootFamily i s)
      (candidateRootFamily i t) = 1 := by
  fin_cases i
  · exact cycleConjugatedShortParam_commutator_eq_one 0 s t
  · exact cycleConjugatedShortParam_commutator_eq_one 1 s t
  · exact cycleConjugatedShortParam_commutator_eq_one 2 s t
  · exact cycleConjugatedLongParam_commutator_eq_one 0 s t
  · exact cycleConjugatedLongParam_commutator_eq_one 1 s t
  · exact cycleConjugatedLongParam_commutator_eq_one 2 s t

theorem candidateRootFamily_add (i : Fin 6) (s t : Bool) :
    candidateRootFamily i (s ^^ t) =
      candidateRootFamily i s * candidateRootFamily i t := by
  fin_cases i
  · exact cycleConjugatedShortParam_add 0 s t
  · exact cycleConjugatedShortParam_add 1 s t
  · exact cycleConjugatedShortParam_add 2 s t
  · exact cycleConjugatedLongParam_add 0 s t
  · exact cycleConjugatedLongParam_add 1 s t
  · exact cycleConjugatedLongParam_add 2 s t

theorem candidateRootFamily_true_square (i : Fin 6) :
    candidateRootFamily i true * candidateRootFamily i true = 1 := by
  have h := (candidateRootFamily_add i true true).symm
  fin_cases i <;>
    simpa [candidateRootFamily, cycleConjugatedShortParam,
      cycleConjugatedLongParam] using h

theorem candidateRootFamily_one_eq_three :
    candidateRootFamily 1 true = candidateRootFamily 3 true := by
  simpa [candidateRootFamily, cycleConjugatedShortParam,
    cycleConjugatedLongParam] using cycleConjugatedShort_one_eq_long_zero

theorem candidateRootFamily_not_injective :
    ¬ Function.Injective (fun i : Fin 6 => candidateRootFamily i true) := by
  intro hinj
  have hindex : (1 : Fin 6) = 3 :=
    hinj candidateRootFamily_one_eq_three
  omega

/-- The subgroup generated by the six explicit candidate root elements.

This is deliberately only a generated subgroup: no identification with a
unipotent radical or cardinality claim is made here. -/
noncomputable def candidateRootSubgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure (Set.range (fun i : Fin 6 => candidateRootFamily i true))

noncomputable instance : Finite candidateRootSubgroup :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance : Fintype candidateRootSubgroup :=
  Fintype.ofFinite _

theorem candidateRootFamily_mem (i : Fin 6) :
    candidateRootFamily i true ∈ candidateRootSubgroup := by
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem candidateRootFamily_commutator_mem (i j : Fin 6) :
    automorphismCommutator (candidateRootFamily i true)
        (candidateRootFamily j true) ∈ candidateRootSubgroup := by
  exact candidateRootSubgroup.mul_mem
    (candidateRootSubgroup.mul_mem
      (candidateRootSubgroup.mul_mem
        (candidateRootFamily_mem i) (candidateRootFamily_mem j))
      (candidateRootSubgroup.inv_mem (candidateRootFamily_mem i)))
    (candidateRootSubgroup.inv_mem (candidateRootFamily_mem j))

def simpleRootSubgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure
    ({unipotentShortAut true, unipotentLongAut true} : Set SplitOctF2Aut)

theorem simpleRootSubgroup_le_candidateRootSubgroup :
    simpleRootSubgroup ≤ candidateRootSubgroup := by
  apply Subgroup.closure_mono
  intro x hx
  rcases hx with rfl | rfl
  · refine ⟨0, ?_⟩
    simp [candidateRootFamily, cycleConjugatedShortParam, cycleConjugatedShort]
  · refine ⟨3, ?_⟩
    simp [candidateRootFamily, cycleConjugatedLongParam, cycleConjugatedLong]

theorem candidateRootSubgroup_has_noncommuting_generators :
    ∃ a b : candidateRootSubgroup, a * b ≠ b * a := by
  let a : candidateRootSubgroup :=
    ⟨candidateRootFamily 0 true, candidateRootFamily_mem 0⟩
  let b : candidateRootSubgroup :=
    ⟨candidateRootFamily 3 true, candidateRootFamily_mem 3⟩
  refine ⟨a, b, ?_⟩
  intro h
  have h' : (a : SplitOctF2Aut) * (b : SplitOctF2Aut) =
      (b : SplitOctF2Aut) * (a : SplitOctF2Aut) := by
    exact congrArg (fun z : candidateRootSubgroup =>
      (z : SplitOctF2Aut)) h
  apply simple_root_generators_do_not_commute
  simpa [a, b, candidateRootFamily, cycleConjugatedShortParam,
    cycleConjugatedLongParam, cycleConjugatedShort, cycleConjugatedLong] using h'

theorem simpleRootSubgroup_short_mem :
    unipotentShortAut true ∈ simpleRootSubgroup := by
  exact Subgroup.subset_closure (by simp [simpleRootSubgroup])

theorem simpleRootSubgroup_long_mem :
    unipotentLongAut true ∈ simpleRootSubgroup := by
  exact Subgroup.subset_closure (by simp [simpleRootSubgroup])

/-! A first genuinely derived root element is the commutator of the two
simple-root generators.  We keep it as a commutator object until the full
Steinberg commutator formula identifies its root-coordinate expansion. -/

noncomputable def simpleRootCommutator : SplitOctF2Aut :=
  automorphismCommutator (unipotentShortAut true) (unipotentLongAut true)

theorem simpleRootCommutator_mem :
    simpleRootCommutator ∈ simpleRootSubgroup := by
  exact simpleRootSubgroup.mul_mem
    (simpleRootSubgroup.mul_mem
      (simpleRootSubgroup.mul_mem
        simpleRootSubgroup_short_mem simpleRootSubgroup_long_mem)
      (simpleRootSubgroup.inv_mem simpleRootSubgroup_short_mem))
    (simpleRootSubgroup.inv_mem simpleRootSubgroup_long_mem)

theorem simpleRootCommutator_ne_one :
    simpleRootCommutator ≠ (1 : SplitOctF2Aut) := by
  exact simple_root_commutator_ne_one

theorem simpleRootSubgroup_contains_product :
    unipotentShortAut true * unipotentLongAut true ∈ simpleRootSubgroup := by
  exact simpleRootSubgroup.mul_mem
    simpleRootSubgroup_short_mem simpleRootSubgroup_long_mem

noncomputable def fourRootSubgroupWords : Fin 4 → simpleRootSubgroup
  | 0 => ⟨1, simpleRootSubgroup.one_mem⟩
  | 1 => ⟨unipotentShortAut true, simpleRootSubgroup_short_mem⟩
  | 2 => ⟨unipotentLongAut true, simpleRootSubgroup_long_mem⟩
  | 3 => ⟨unipotentShortAut true * unipotentLongAut true,
    simpleRootSubgroup_contains_product⟩

private lemma short_mul_long_ne_one :
    unipotentShortAut true * unipotentLongAut true ≠ (1 : SplitOctF2Aut) := by
  intro h
  have h' := congrArg
    (fun z : SplitOctF2Aut => unipotentShortAut true * z) h
  apply simple_root_generators_distinct
  symm
  simpa [← mul_assoc, unipotentShortAut_order true] using h'

private lemma short_mul_long_ne_short :
    unipotentShortAut true * unipotentLongAut true ≠ unipotentShortAut true := by
  intro h
  have h' := congrArg
    (fun z : SplitOctF2Aut => unipotentShortAut true * z) h
  apply unipotentLongAut_true_ne_one
  simpa [← mul_assoc, unipotentShortAut_order true] using h'

private lemma short_mul_long_ne_long :
    unipotentShortAut true * unipotentLongAut true ≠ unipotentLongAut true := by
  intro h
  have h' := congrArg
    (fun z : SplitOctF2Aut => z * unipotentLongAut true) h
  apply unipotentShortAut_true_ne_one
  simpa [mul_assoc, unipotentLongAut_order true] using h'

theorem fourRootSubgroupWords_injective :
    Function.Injective fourRootSubgroupWords := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    have h' := congrArg (fun z : simpleRootSubgroup => (z : SplitOctF2Aut)) h
    dsimp [fourRootSubgroupWords] at h'
    first
    | exact False.elim (unipotentShortAut_true_ne_one h')
    | exact False.elim (unipotentShortAut_true_ne_one h'.symm)
    | exact False.elim (unipotentLongAut_true_ne_one h')
    | exact False.elim (unipotentLongAut_true_ne_one h'.symm)
    | exact False.elim (simple_root_generators_distinct h')
    | exact False.elim (simple_root_generators_distinct h'.symm)
    | exact False.elim (short_mul_long_ne_one h')
    | exact False.elim (short_mul_long_ne_one h'.symm)
    | exact False.elim (short_mul_long_ne_short h')
    | exact False.elim (short_mul_long_ne_short h'.symm)
    | exact False.elim (short_mul_long_ne_long h')
    | exact False.elim (short_mul_long_ne_long h'.symm)

private lemma simpleRootSubgroup_product_sq_mem :
    (unipotentShortAut true * unipotentLongAut true) ^ 2 ∈
      simpleRootSubgroup := by
  exact simpleRootSubgroup.mul_mem
    simpleRootSubgroup_contains_product simpleRootSubgroup_contains_product

private lemma simpleRootSubgroup_product_cube_mem :
    (unipotentShortAut true * unipotentLongAut true) ^ 3 ∈
      simpleRootSubgroup := by
  exact simpleRootSubgroup.mul_mem
    simpleRootSubgroup_product_sq_mem simpleRootSubgroup_contains_product

private lemma simpleRootSubgroup_short_product_sq_mem :
    unipotentShortAut true *
        (unipotentShortAut true * unipotentLongAut true) ^ 2 ∈
      simpleRootSubgroup := by
  exact simpleRootSubgroup.mul_mem
    simpleRootSubgroup_short_mem simpleRootSubgroup_product_sq_mem

private lemma simpleRootSubgroup_short_product_cube_mem :
    unipotentShortAut true *
        (unipotentShortAut true * unipotentLongAut true) ^ 3 ∈
      simpleRootSubgroup := by
  exact simpleRootSubgroup.mul_mem
    simpleRootSubgroup_short_mem simpleRootSubgroup_product_cube_mem

noncomputable def eightRootSubgroupWords : Fin 8 → simpleRootSubgroup
  | 0 => ⟨1, simpleRootSubgroup.one_mem⟩
  | 1 => ⟨unipotentShortAut true * unipotentLongAut true,
    simpleRootSubgroup_contains_product⟩
  | 2 => ⟨(unipotentShortAut true * unipotentLongAut true) ^ 2,
    simpleRootSubgroup_product_sq_mem⟩
  | 3 => ⟨(unipotentShortAut true * unipotentLongAut true) ^ 3,
    simpleRootSubgroup_product_cube_mem⟩
  | 4 => ⟨unipotentShortAut true, simpleRootSubgroup_short_mem⟩
  | 5 => ⟨unipotentShortAut true *
      (unipotentShortAut true * unipotentLongAut true) ^ 2,
    simpleRootSubgroup_short_product_sq_mem⟩
  | 6 => ⟨unipotentShortAut true *
      (unipotentShortAut true * unipotentLongAut true) ^ 3,
    simpleRootSubgroup_short_product_cube_mem⟩
  | 7 => ⟨unipotentLongAut true, simpleRootSubgroup_long_mem⟩

theorem eightRootSubgroupWords_injective :
    Function.Injective eightRootSubgroupWords := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    have h' := congrArg (fun z : simpleRootSubgroup => (z : SplitOctF2Aut)) h
    dsimp [eightRootSubgroupWords] at h'
    have h0 := congrArg (fun f : SplitOctF2Aut => f.1 up0) h'
    have h1 := congrArg (fun f : SplitOctF2Aut => f.1 up1) h'
    have h2 := congrArg (fun f : SplitOctF2Aut => f.1 up2) h'
    revert h0 h1 h2
    decide

noncomputable instance : Finite simpleRootSubgroup :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance : Fintype simpleRootSubgroup := Fintype.ofFinite _

theorem simpleRootSubgroup_card_lower_bound_eight :
    8 ≤ Fintype.card simpleRootSubgroup := by
  have hc : Fintype.card (Fin 8) ≤ Fintype.card simpleRootSubgroup :=
    Fintype.card_le_of_injective eightRootSubgroupWords
      eightRootSubgroupWords_injective
  simpa using hc

def simpleRootSubgroupToCandidate (x : simpleRootSubgroup) : candidateRootSubgroup :=
  ⟨x.1, simpleRootSubgroup_le_candidateRootSubgroup x.2⟩

theorem simpleRootSubgroupToCandidate_injective :
    Function.Injective simpleRootSubgroupToCandidate := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : candidateRootSubgroup => (z : SplitOctF2Aut)) h

theorem candidateRootSubgroup_card_lower_bound_eight :
    8 ≤ Fintype.card candidateRootSubgroup := by
  have hc : Fintype.card simpleRootSubgroup ≤
      Fintype.card candidateRootSubgroup :=
    Fintype.card_le_of_injective simpleRootSubgroupToCandidate
      simpleRootSubgroupToCandidate_injective
  exact le_trans simpleRootSubgroup_card_lower_bound_eight hc

theorem simpleRootSubgroup_card_lower_bound :
    4 ≤ Fintype.card simpleRootSubgroup := by
  have hc : Fintype.card (Fin 4) ≤ Fintype.card simpleRootSubgroup :=
    Fintype.card_le_of_injective fourRootSubgroupWords
      fourRootSubgroupWords_injective
  simpa using hc

theorem finite_g2_carrier_card_lower_bound :
    4 ≤ Fintype.card SplitOctF2Aut := by
  exact le_trans simpleRootSubgroup_card_lower_bound
    (Fintype.card_subtype_le (fun f : SplitOctF2Aut =>
      f ∈ simpleRootSubgroup))

theorem finite_g2_carrier_card_lower_bound_eight :
    8 ≤ Fintype.card SplitOctF2Aut := by
  exact le_trans simpleRootSubgroup_card_lower_bound_eight
    (Fintype.card_subtype_le (fun f : SplitOctF2Aut =>
      f ∈ simpleRootSubgroup))

set_option maxHeartbeats 3000000

lemma word_inv (i : Fin 8) : ∃ j : Fin 8, (eightRootSubgroupWords i)⁻¹ = eightRootSubgroupWords j := by
  fin_cases i
  · refine ⟨0, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨3, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨2, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨1, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨4, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨5, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨6, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨7, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide

lemma word_mul (i j : Fin 8) : ∃ k : Fin 8, eightRootSubgroupWords i * eightRootSubgroupWords j = eightRootSubgroupWords k := by
  fin_cases i <;> fin_cases j
  · refine ⟨0, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨1, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨2, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨3, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨4, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨5, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨6, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨7, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨1, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨2, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨3, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨0, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨6, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨7, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨5, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨4, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨2, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨3, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨0, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨1, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨5, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨4, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨7, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨6, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨3, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨0, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨1, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨2, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨7, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨6, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨4, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨5, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨4, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨7, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨5, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨6, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨0, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨2, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨3, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨1, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨5, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨6, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨4, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨7, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨2, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨0, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨1, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨3, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨6, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨4, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨7, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨5, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨1, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨3, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨0, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨2, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨7, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨5, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨6, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨4, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨3, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨1, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨2, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide
  · refine ⟨0, ?_⟩; apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro ⟨a,b,x0,x1,x2,y0,y1,y2⟩; revert a b x0 x1 x2 y0 y1 y2; decide

theorem eightRootSubgroupWords_surjective :
    Function.Surjective eightRootSubgroupWords := by
  intro ⟨g, hg⟩
  have hmem : ∃ i : Fin 8, g = (eightRootSubgroupWords i).1 := by
    refine @Subgroup.closure_induction SplitOctF2Aut _
      {unipotentShortAut true, unipotentLongAut true}
      (fun x _ => ∃ i : Fin 8, x = (eightRootSubgroupWords i).1)
      ?_ ?_ ?_ ?_ g hg
    · intro x hx
      rcases hx with rfl | rfl
      · exact ⟨4, rfl⟩
      · exact ⟨7, rfl⟩
    · exact ⟨0, rfl⟩
    · intro x y _ _ ⟨ix, hx_eq⟩ ⟨iy, hy_eq⟩
      obtain ⟨k, hk⟩ := word_mul ix iy
      refine ⟨k, ?_⟩
      rw [hx_eq, hy_eq]
      exact congrArg Subtype.val hk
    · intro x _ ⟨ix, hx_eq⟩
      obtain ⟨k, hk⟩ := word_inv ix
      refine ⟨k, ?_⟩
      rw [hx_eq]
      exact congrArg Subtype.val hk
  obtain ⟨i, hi⟩ := hmem
  refine ⟨i, ?_⟩
  apply Subtype.ext
  exact hi.symm

theorem simpleRootSubgroup_card_eq_eight :
    Fintype.card simpleRootSubgroup = 8 := by
  have hequiv : Fin 8 ≃ simpleRootSubgroup :=
    Equiv.ofBijective eightRootSubgroupWords
      ⟨eightRootSubgroupWords_injective, eightRootSubgroupWords_surjective⟩
  rw [← Fintype.card_congr hequiv]
  simp

/-- The concrete two-generator subgroup has a genuine eight-element normal-form
equivalence.  This is stronger than a cardinality calculation and is the
reusable finite subgroup interface for later subgroup transport arguments. -/
noncomputable def simpleRootSubgroupEquivFin8 :
    Fin 8 ≃ simpleRootSubgroup :=
  Equiv.ofBijective eightRootSubgroupWords
    ⟨eightRootSubgroupWords_injective, eightRootSubgroupWords_surjective⟩

@[simp] theorem simpleRootSubgroupEquivFin8_apply (i : Fin 8) :
    simpleRootSubgroupEquivFin8 i = eightRootSubgroupWords i := rfl

theorem simpleRootSubgroupEquivFin8_card :
    Fintype.card simpleRootSubgroup = Fintype.card (Fin 8) := by
  exact Fintype.card_congr simpleRootSubgroupEquivFin8.symm


theorem simple_root_generator_packet :
    (unipotentShortAut true) * (unipotentShortAut true) = 1 ∧
    (unipotentLongAut true) * (unipotentLongAut true) = 1 ∧
    unipotentShortAut true ≠ (1 : SplitOctF2Aut) ∧
    unipotentLongAut true ≠ (1 : SplitOctF2Aut) := by
  exact ⟨unipotentShortAut_order true,
    unipotentLongAut_order true,
    unipotentShortAut_true_ne_one,
    unipotentLongAut_true_ne_one⟩

end InfoGeometry.Algebra.Zorn.G2Unipotent
