import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2UnipotentRootSubgroup

/-!
# A concrete finite split-Zorn automorphism

The coordinate transposition `0 ↔ 1` in both vector slots is an actual
automorphism of the characteristic-two Zorn multiplication.  This gives a
native nontrivial generator for subsequent orbit/stabilizer constructions.
-/

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
  native_decide +revert

theorem swap01_mul (X Y : SplitOctF2) :
    swap01Fun (mul X Y) = mul (swap01Fun X) (swap01Fun Y) := by
  native_decide +revert

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

def conjugateAut (g u : SplitOctF2Aut) : SplitOctF2Aut :=
  g * u * g⁻¹

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

def simpleRootSubgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure
    ({unipotentShortAut true, unipotentLongAut true} : Set SplitOctF2Aut)

theorem simpleRootSubgroup_short_mem :
    unipotentShortAut true ∈ simpleRootSubgroup := by
  exact Subgroup.subset_closure (by simp [simpleRootSubgroup])

theorem simpleRootSubgroup_long_mem :
    unipotentLongAut true ∈ simpleRootSubgroup := by
  exact Subgroup.subset_closure (by simp [simpleRootSubgroup])

theorem simpleRootSubgroup_contains_product :
    unipotentShortAut true * unipotentLongAut true ∈ simpleRootSubgroup := by
  exact simpleRootSubgroup.mul_mem
    simpleRootSubgroup_short_mem simpleRootSubgroup_long_mem

def fourRootSubgroupWords : Fin 4 → simpleRootSubgroup
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

noncomputable instance : Finite simpleRootSubgroup :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance : Fintype simpleRootSubgroup := Fintype.ofFinite _

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

theorem simple_root_product_pow_four :
    (unipotentShortAut true * unipotentLongAut true) ^ 4 =
      (1 : SplitOctF2Aut) := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  cases X <;> rfl

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
