import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Basis rigidity for finite split-Zorn automorphisms

An automorphism is determined by its values on the eight coordinate basis
elements.  The only finite computation here is the decomposition of one
256-element carrier element into those coordinates; no permutation of the
carrier is enumerated.
-/

namespace InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def basis8 : Fin 8 → SplitOctF2 :=
  ![ePlus, eMinus, up0, up1, up2, down0, down1, down2]

def basisExpansion (X : SplitOctF2) : SplitOctF2 :=
  add (add (add (add (add (add (add
    (if X.a then ePlus else zero)
    (if X.b then eMinus else zero))
    (if X.x0 then up0 else zero))
    (if X.x1 then up1 else zero))
    (if X.x2 then up2 else zero))
    (if X.y0 then down0 else zero))
    (if X.y1 then down1 else zero))
    (if X.y2 then down2 else zero)

lemma ite_a (c : Bool) (A B : SplitOctF2) : (if c then A else B).a = if c then A.a else B.a := by cases c <;> rfl
lemma ite_b (c : Bool) (A B : SplitOctF2) : (if c then A else B).b = if c then A.b else B.b := by cases c <;> rfl
lemma ite_x0 (c : Bool) (A B : SplitOctF2) : (if c then A else B).x0 = if c then A.x0 else B.x0 := by cases c <;> rfl
lemma ite_x1 (c : Bool) (A B : SplitOctF2) : (if c then A else B).x1 = if c then A.x1 else B.x1 := by cases c <;> rfl
lemma ite_x2 (c : Bool) (A B : SplitOctF2) : (if c then A else B).x2 = if c then A.x2 else B.x2 := by cases c <;> rfl
lemma ite_y0 (c : Bool) (A B : SplitOctF2) : (if c then A else B).y0 = if c then A.y0 else B.y0 := by cases c <;> rfl
lemma ite_y1 (c : Bool) (A B : SplitOctF2) : (if c then A else B).y1 = if c then A.y1 else B.y1 := by cases c <;> rfl
lemma ite_y2 (c : Bool) (A B : SplitOctF2) : (if c then A else B).y2 = if c then A.y2 else B.y2 := by cases c <;> rfl

theorem basisExpansion_eq (X : SplitOctF2) :
    basisExpansion X = X := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [basisExpansion, add, add2, zero, ePlus, eMinus, up0, up1, up2, down0, down1, down2]
  all_goals
    revert a b x0 x1 x2 y0 y1 y2
    decide

@[simp] theorem map_zero (f : SplitOctF2Aut) :
    f.1 zero = zero := by
  have h := f.2.2.1 zero zero
  rw [add_self] at h
  rw [add_self] at h
  exact h

lemma map_ite_zero (f : SplitOctF2Aut) (c : Bool) (E : SplitOctF2) :
    f.1 (if c then E else zero) = if c then f.1 E else zero := by
  cases c
  · simp [map_zero]
  · rfl

theorem map_basisExpansion (f : SplitOctF2Aut) (X : SplitOctF2) :
    f.1 (basisExpansion X) =
      add (add (add (add (add (add (add
        (if X.a then f.1 ePlus else zero)
        (if X.b then f.1 eMinus else zero))
        (if X.x0 then f.1 up0 else zero))
        (if X.x1 then f.1 up1 else zero))
        (if X.x2 then f.1 up2 else zero))
        (if X.y0 then f.1 down0 else zero))
        (if X.y1 then f.1 down1 else zero))
        (if X.y2 then f.1 down2 else zero) := by
  dsimp [basisExpansion]
  rw [f.2.2.1, f.2.2.1, f.2.2.1, f.2.2.1,
    f.2.2.1, f.2.2.1, f.2.2.1]
  simp only [map_ite_zero]

theorem automorphism_ext_of_basis
    (f g : SplitOctF2Aut)
    (h : ∀ i : Fin 8, f.1 (basis8 i) = g.1 (basis8 i)) :
    f = g := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  rw [← basisExpansion_eq X, map_basisExpansion, map_basisExpansion]
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  dsimp [basis8] at h0 h1 h2 h3 h4 h5 h6 h7
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

def basisRestriction (f : SplitOctF2Aut) : Fin 8 → SplitOctF2 :=
  fun i => f.1 (basis8 i)

def extendBasisMap (v : Fin 8 → SplitOctF2) (X : SplitOctF2) : SplitOctF2 :=
  add (add (add (add (add (add (add
    (if X.a then v 0 else zero)
    (if X.b then v 1 else zero))
    (if X.x0 then v 2 else zero))
    (if X.x1 then v 3 else zero))
    (if X.x2 then v 4 else zero))
    (if X.y0 then v 5 else zero))
    (if X.y1 then v 6 else zero))

    (if X.y2 then v 7 else zero)

/-! The coordinate extension has the prescribed values on the basis. -/

theorem extendBasisMap_basis
    (v : Fin 8 → SplitOctF2) (i : Fin 8) :
    extendBasisMap v (basis8 i) = v i := by
  fin_cases i <;>
    simp [extendBasisMap, basis8, zero, ePlus, eMinus, up0, up1, up2,
      down0, down1, down2, add, add2]

theorem extendBasisMap_basisRestriction (f : SplitOctF2Aut) (X : SplitOctF2) :
    f.1 X = extendBasisMap (basisRestriction f) X := by
  have h := map_basisExpansion f X
  rw [basisExpansion_eq X] at h
  exact h

theorem basis8_injective : Function.Injective basis8 := by
  intro i j h
  revert i j
  decide

theorem basisRestriction_injective_on_basis (f : SplitOctF2Aut) :
    Function.Injective (basisRestriction f) := by
  intro i j h
  apply basis8_injective
  apply f.1.injective
  exact h

theorem basisRestriction_injective :
    Function.Injective basisRestriction := by
  intro f g h
  apply automorphism_ext_of_basis f g
  intro i
  exact congrFun h i

/-- The carrier cardinality is bounded by the possible eight basis images. -/
theorem automorphism_card_le_basis_maps :
    Fintype.card SplitOctF2Aut ≤ Fintype.card (Fin 8 → SplitOctF2) := by
  exact Fintype.card_le_of_injective basisRestriction basisRestriction_injective

/- The coordinate encoding gives the explicit finite upper bound. -/
theorem automorphism_card_le_basis_maps_numeric :
    Fintype.card SplitOctF2Aut ≤ 256 ^ 8 := by
  calc
    Fintype.card SplitOctF2Aut ≤ Fintype.card (Fin 8 → SplitOctF2) :=
      automorphism_card_le_basis_maps
    _ = 256 ^ 8 := by simp [splitOctF2_card]

/-! The unit relation `1 = ePlus + eMinus` removes one free basis image. -/

theorem ePlus_add_eMinus_eq_one : add ePlus eMinus = one := by
  rfl

theorem map_eMinus_from_ePlus (f : SplitOctF2Aut) :
    f.1 eMinus = add one (f.1 ePlus) := by
  have h := f.2.2.1 ePlus eMinus
  rw [ePlus_add_eMinus_eq_one, f.2.1] at h
  calc
    f.1 eMinus = add zero (f.1 eMinus) := (zero_add _).symm
    _ = add (add (f.1 ePlus) (f.1 ePlus)) (f.1 eMinus) := by
      rw [add_self, zero_add]
    _ = add (f.1 ePlus) (add (f.1 ePlus) (f.1 eMinus)) := by
      rw [add_assoc]
    _ = add (f.1 ePlus) one := by rw [h]
    _ = add one (f.1 ePlus) := add_comm _ _

def basis7 : Fin 7 → SplitOctF2 :=
  ![ePlus, up0, up1, up2, down0, down1, down2]

def basisRestriction7 (f : SplitOctF2Aut) : Fin 7 → SplitOctF2 :=
  fun i => f.1 (basis7 i)

def basis8From7 (v : Fin 7 → SplitOctF2) : Fin 8 → SplitOctF2
  | 0 => v 0
  | 1 => add one (v 0)
  | 2 => v 1
  | 3 => v 2
  | 4 => v 3
  | 5 => v 4
  | 6 => v 5
  | 7 => v 6

def admissibleBasis7 (v : Fin 7 → SplitOctF2) : Prop :=
  Function.Injective (extendBasisMap (basis8From7 v)) ∧
    extendBasisMap (basis8From7 v) one = one ∧
    (∀ X Y : SplitOctF2,
      extendBasisMap (basis8From7 v) (add X Y) =
        add (extendBasisMap (basis8From7 v) X)
          (extendBasisMap (basis8From7 v) Y)) ∧
    (∀ X Y : SplitOctF2,
      extendBasisMap (basis8From7 v) (mul X Y) =
        mul (extendBasisMap (basis8From7 v) X)
          (extendBasisMap (basis8From7 v) Y))

lemma basis8From7_basisRestriction (f : SplitOctF2Aut) :
    basis8From7 (basisRestriction7 f) = basisRestriction f := by
  funext i
  fin_cases i
  · rfl
  · change add one (f.1 ePlus) = f.1 eMinus
    exact (map_eMinus_from_ePlus f).symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem basisRestriction7_admissible (f : SplitOctF2Aut) :
    admissibleBasis7 (basisRestriction7 f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y h
    rw [basis8From7_basisRestriction f] at h
    apply f.1.injective
    rw [extendBasisMap_basisRestriction f X,
      extendBasisMap_basisRestriction f Y, h]
  · rw [basis8From7_basisRestriction f]
    rw [← extendBasisMap_basisRestriction f one]
    exact f.2.1
  · intro X Y
    rw [basis8From7_basisRestriction f]
    rw [← extendBasisMap_basisRestriction f (add X Y)]
    rw [← extendBasisMap_basisRestriction f X,
      ← extendBasisMap_basisRestriction f Y]
    exact f.2.2.1 X Y
  · intro X Y
    rw [basis8From7_basisRestriction]
    rw [← extendBasisMap_basisRestriction f (mul X Y)]
    rw [← extendBasisMap_basisRestriction f X,
      ← extendBasisMap_basisRestriction f Y]
    exact f.2.2.2 X Y

noncomputable def admissibleBasis7_to_aut
    (v : Fin 7 → SplitOctF2)
    (hv : admissibleBasis7 v) : SplitOctF2Aut :=
  { val := Equiv.ofBijective (extendBasisMap (basis8From7 v))
      ⟨hv.1, Finite.surjective_of_injective hv.1⟩
    property := ⟨hv.2.1, hv.2.2.1, hv.2.2.2⟩ }

@[simp] theorem admissibleBasis7_to_aut_apply
    (v : Fin 7 → SplitOctF2)
    (hv : admissibleBasis7 v) (X : SplitOctF2) :
    (admissibleBasis7_to_aut v hv).1 X =
      extendBasisMap (basis8From7 v) X := by
  rfl

theorem automorphism_ext_of_basis7
    (f g : SplitOctF2Aut)
    (h : ∀ i : Fin 7, f.1 (basis7 i) = g.1 (basis7 i)) :
    f = g := by
  apply automorphism_ext_of_basis f g
  intro i
  fin_cases i
  · exact h 0
  · change f.1 eMinus = g.1 eMinus
    have h0 : f.1 ePlus = g.1 ePlus := by
      simpa [basis7] using h 0
    rw [map_eMinus_from_ePlus f, map_eMinus_from_ePlus g, h0]
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h 4
  · exact h 5
  · exact h 6

theorem basisRestriction7_injective :
    Function.Injective basisRestriction7 := by
  intro f g h
  apply automorphism_ext_of_basis7 f g
  intro i
  exact congrFun h i

theorem automorphism_eq_one_of_fixes_basis7
    (f : SplitOctF2Aut)
    (h : ∀ i : Fin 7, f.1 (basis7 i) = basis7 i) :
    f = 1 := by
  apply automorphism_ext_of_basis7 f 1
  intro i
  simpa using h i

/-! The seven-image parameterization is exact: admissible data are neither
under- nor over-counted.  This is a structural replacement for enumerating
all automorphisms by brute force; it does not evaluate the admissible subtype.
-/
noncomputable def admissibleBasis7Equiv :
    SplitOctF2Aut ≃ {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} where
  toFun f := ⟨basisRestriction7 f, basisRestriction7_admissible f⟩
  invFun v := admissibleBasis7_to_aut v.1 v.2
  left_inv f := by
    apply basisRestriction7_injective
    funext i
    dsimp [basisRestriction7]
    change (admissibleBasis7_to_aut (basisRestriction7 f)
        (basisRestriction7_admissible f)).1 (basis7 i) =
      f.1 (basis7 i)
    rw [admissibleBasis7_to_aut_apply]
    rw [basis8From7_basisRestriction f]
    exact (extendBasisMap_basisRestriction f (basis7 i)).symm
  right_inv v := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [basisRestriction7, basis7, admissibleBasis7_to_aut_apply,
        basis8From7, extendBasisMap, add, add2, zero, ePlus,
        up0, up1, up2, down0, down1, down2]

noncomputable instance admissibleBasis7Fintype :
    Fintype {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} :=
  Fintype.ofFinite _

theorem automorphism_card_eq_admissibleBasis7_card :
    Fintype.card SplitOctF2Aut =
      Fintype.card {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} := by
  exact Fintype.card_congr admissibleBasis7Equiv

/-- Route-B reduction: the concrete order claim is equivalent to the
cardinality claim for the exact admissible-basis subtype.  This theorem does
not assert either cardinality; it prevents an arithmetic order ledger from
being mistaken for a carrier classification. -/
theorem automorphism_card_eq_12096_iff_admissibleBasis7_card_eq_12096 :
    Fintype.card SplitOctF2Aut = 12096 ↔
      Fintype.card {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} = 12096 := by
  rw [automorphism_card_eq_admissibleBasis7_card]

/-! The admissible parameter space is closed under the concrete
automorphism-group action.  This is the structural input needed before any
orbit/stabilizer or BN-type counting argument; it is not itself a cardinality
calculation. -/

noncomputable def admissibleBasis7Action
    (f : SplitOctF2Aut)
  (v : Fin 7 → SplitOctF2)
  (hv : admissibleBasis7 v) : Fin 7 → SplitOctF2 :=
  basisRestriction7 (admissibleBasis7_to_aut v hv * f)

theorem admissibleBasis7Action_admissible
    (f : SplitOctF2Aut)
    (v : Fin 7 → SplitOctF2)
  (hv : admissibleBasis7 v) :
    admissibleBasis7 (admissibleBasis7Action f v hv) := by
  exact basisRestriction7_admissible
    (admissibleBasis7_to_aut v hv * f)

theorem admissibleBasis7Action_apply
    (f : SplitOctF2Aut)
    (v : Fin 7 → SplitOctF2)
    (hv : admissibleBasis7 v)
    (i : Fin 7) :
    admissibleBasis7Action f v hv i = f.1 (v i) := by
  have hbasis : ∀ j : Fin 7,
      (admissibleBasis7_to_aut v hv).1 (basis7 j) = v j := by
    intro j
    fin_cases j <;>
      simp [admissibleBasis7_to_aut_apply, basis7, basis8From7,
        extendBasisMap, add, add2, zero, ePlus, up0, up1, up2,
        down0, down1, down2]
  simp only [admissibleBasis7Action, basisRestriction7]
  have hcomp :
    (admissibleBasis7_to_aut v hv * f).1 (basis7 i) =
        f.1 ((admissibleBasis7_to_aut v hv).1 (basis7 i)) := by
    exact SplitOctF2Aut.mul_apply _ _ _
  rw [hcomp, hbasis]

theorem admissibleBasis7Action_comp
    (f g : SplitOctF2Aut)
    (v : Fin 7 → SplitOctF2)
    (hv : admissibleBasis7 v) :
    admissibleBasis7Action f
        (admissibleBasis7Action g v hv)
        (admissibleBasis7Action_admissible g v hv) =
      admissibleBasis7Action (g * f) v hv := by
  funext i
  rw [admissibleBasis7Action_apply,
    admissibleBasis7Action_apply,
    admissibleBasis7Action_apply]
  exact SplitOctF2Aut.mul_apply _ _ _

theorem admissibleBasis7Action_one
    (v : Fin 7 → SplitOctF2)
    (hv : admissibleBasis7 v) :
    admissibleBasis7Action (1 : SplitOctF2Aut) v hv = v := by
  funext i
  rw [admissibleBasis7Action_apply]
  rfl

theorem admissibleBasis7Action_inv
    (f : SplitOctF2Aut)
    (v : Fin 7 → SplitOctF2)
    (hv : admissibleBasis7 v) :
    admissibleBasis7Action f⁻¹
        (admissibleBasis7Action f v hv)
        (admissibleBasis7Action_admissible f v hv) = v := by
  funext i
  rw [admissibleBasis7Action_apply,
    admissibleBasis7Action_apply]
  exact f.1.left_inv (v i)

theorem automorphism_card_le_basis7_maps :
    Fintype.card SplitOctF2Aut ≤ Fintype.card (Fin 7 → SplitOctF2) := by
  exact Fintype.card_le_of_injective basisRestriction7 basisRestriction7_injective

theorem automorphism_card_le_basis7_maps_numeric :
    Fintype.card SplitOctF2Aut ≤ 256 ^ 7 := by
  calc
    Fintype.card SplitOctF2Aut ≤ Fintype.card (Fin 7 → SplitOctF2) :=
      automorphism_card_le_basis7_maps
    _ = 256 ^ 7 := by simp [splitOctF2_card]

theorem basisRestriction7_preserves_mul
    (f : SplitOctF2Aut) (i j : Fin 7) :
    f.1 (mul (basis7 i) (basis7 j)) =
      mul (basisRestriction7 f i) (basisRestriction7 f j) := by
  exact f.2.2.2 (basis7 i) (basis7 j)

theorem basisRestriction7_preserves_unit (f : SplitOctF2Aut) :
    f.1 one = one := by
  exact f.2.1

theorem basisRestriction_preserves_mul
    (f : SplitOctF2Aut) (i j : Fin 8) :
    f.1 (mul (basis8 i) (basis8 j)) =
      mul (basisRestriction f i) (basisRestriction f j) := by
  exact f.2.2.2 (basis8 i) (basis8 j)

theorem basisRestriction_preserves_unit :
    ∀ f : SplitOctF2Aut, f.1 one = one := by
  intro f
  exact f.2.1

/-!
## Structural classification: admissible 7-bases as a simply transitive G-torsor

The bijection `admissibleBasis7Equiv` transports the group structure of
`SplitOctF2Aut` to a simply transitive action on admissible 7-bases.  This
is the combinatorial core of a Bruhat decomposition: the admissible bases
form a principal homogeneous space under the automorphism group, with no
extra stabilizer data beyond the group law itself. -/

/-- The automorphism group acts on admissible 7-bases by transporting
left multiplication through `admissibleBasis7Equiv`. -/
noncomputable instance : MulAction SplitOctF2Aut {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} where
  smul g v := admissibleBasis7Equiv (g * admissibleBasis7Equiv.symm v)
  one_smul v := by
    change admissibleBasis7Equiv (1 * admissibleBasis7Equiv.symm v) = v
    rw [Monoid.one_mul]
    exact admissibleBasis7Equiv.right_inv v
  mul_smul g h v := by
    change admissibleBasis7Equiv ((g * h) * admissibleBasis7Equiv.symm v) =
           admissibleBasis7Equiv (g * admissibleBasis7Equiv.symm (admissibleBasis7Equiv (h * admissibleBasis7Equiv.symm v)))
    rw [mul_assoc, admissibleBasis7Equiv.symm_apply_apply]

/-- The action is transitive: any admissible 7-basis is reachable from any
other by a unique group element. -/
theorem admissibleBasis7_isPretransitive :
    MulAction.IsPretransitive SplitOctF2Aut {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} := by
  constructor
  intro v w
  refine ⟨admissibleBasis7Equiv.symm w * (admissibleBasis7Equiv.symm v)⁻¹, ?_⟩
  calc
    (admissibleBasis7Equiv.symm w * (admissibleBasis7Equiv.symm v)⁻¹) • v
        = admissibleBasis7Equiv ((admissibleBasis7Equiv.symm w * (admissibleBasis7Equiv.symm v)⁻¹) * admissibleBasis7Equiv.symm v) := rfl
    _ = admissibleBasis7Equiv (admissibleBasis7Equiv.symm w) := by
      rw [mul_assoc, inv_mul_cancel]
      simp
    _ = w := admissibleBasis7Equiv.right_inv w

/-- The action is free: the stabilizer of any admissible 7-basis is trivial. -/
theorem admissibleBasis7_smul_eq_iff (g h : SplitOctF2Aut)
    (v : {v : Fin 7 → SplitOctF2 // admissibleBasis7 v}) :
    g • v = h • v ↔ g = h := by
  constructor
  · intro hsmul
    change admissibleBasis7Equiv (g * admissibleBasis7Equiv.symm v) =
      admissibleBasis7Equiv (h * admissibleBasis7Equiv.symm v) at hsmul
    have h₁ := congrArg admissibleBasis7Equiv.symm hsmul
    simp only [admissibleBasis7Equiv.symm_apply_apply] at h₁
    exact mul_right_cancel h₁
  · intro rfl
    rfl

/-- The standard admissible 7-basis obtained by restricting the identity
automorphism. -/
noncomputable def standardAdmissibleBasis7 : {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} :=
  ⟨basisRestriction7 1, basisRestriction7_admissible 1⟩

/-- The stabilizer of the standard admissible basis is the trivial subgroup. -/
theorem standardAdmissibleBasis7_stabilizer_eq_bot :
    MulAction.stabilizer SplitOctF2Aut standardAdmissibleBasis7 = ⊥ := by
  ext g
  simp [MulAction.stabilizer]
  have h := admissibleBasis7_smul_eq_iff g 1 standardAdmissibleBasis7
  rw [one_smul] at h
  exact h

/-- The admissible bases form a simply transitive `SplitOctF2Aut`-torsor.
This is the structural replacement for enumerating all automorphisms:
each admissible basis labels a unique group element and vice versa. -/
theorem admissibleBasis7_simply_transitive :
    MulAction.IsPretransitive SplitOctF2Aut {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} ∧
    ∀ (g h : SplitOctF2Aut) (v : {v : Fin 7 → SplitOctF2 // admissibleBasis7 v}),
      g • v = h • v → g = h :=
  ⟨admissibleBasis7_isPretransitive, fun g h v hsmul => (admissibleBasis7_smul_eq_iff g h v).1 hsmul⟩

end InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
