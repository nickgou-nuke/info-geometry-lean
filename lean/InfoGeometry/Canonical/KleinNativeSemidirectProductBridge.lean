import Mathlib.GroupTheory.SemidirectProduct
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KleinPresentedGroup

/-!
# Native semidirect-product Klein carrier

This file constructs the algebraic semidirect product of two copies of
`Multiplicative ℤ`, where the acting copy acts by powers of negation on the
translation copy.  It proves the Klein conjugation relation for the canonical
generators.  No topological fundamental-group identification or C*-crossed
product is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.KleinNativeSemidirectProductBridge

open InfoGeometry.Canonical.KleinPresentedGroup

def integerNegMulAut : MulAut (Multiplicative ℤ) :=
  (AddEquiv.neg ℤ).toMultiplicative

def integerInversionAction : Multiplicative ℤ →* MulAut (Multiplicative ℤ) :=
  zpowersHom (MulAut (Multiplicative ℤ)) integerNegMulAut

abbrev NativeKleinSemidirect :=
  Multiplicative ℤ ⋊[integerInversionAction] Multiplicative ℤ

theorem integerNegMulAut_sq : integerNegMulAut ^ (2 : ℤ) = 1 := by
  ext a
  change integerNegMulAut (integerNegMulAut a) = a
  simp [integerNegMulAut]

theorem integerNegMulAut_zpow_eq_one_iff_even (n : ℤ) :
    integerNegMulAut ^ n = 1 ↔ Even n := by
  constructor
  · intro h
    rcases Int.even_or_odd n with hn | hn
    · exact hn
    · obtain ⟨k, hk⟩ := hn
      rw [hk, zpow_add, zpow_mul, integerNegMulAut_sq] at h
      simp at h
      have hne : integerNegMulAut ≠ 1 := by
        intro he
        have hv := congrArg
          (fun u : MulAut (Multiplicative ℤ) =>
            u (Multiplicative.ofAdd 1)) he
        have hv' := congrArg Multiplicative.toAdd hv
        simp [integerNegMulAut] at hv'
      exact False.elim (hne h)
  · intro hn
    obtain ⟨k, hk⟩ := hn
    rw [hk, show k + k = 2 * k by ring, zpow_mul, integerNegMulAut_sq]
    simp

theorem integerInversionAction_ofAdd_eq_one_iff_even (n : ℤ) :
    integerInversionAction (Multiplicative.ofAdd n) = 1 ↔ Even n := by
  change integerNegMulAut ^ n = 1 ↔ Even n
  exact integerNegMulAut_zpow_eq_one_iff_even n

def nativeKleinGlide : NativeKleinSemidirect :=
  SemidirectProduct.inr (Multiplicative.ofAdd 1)

def nativeKleinTranslation : NativeKleinSemidirect :=
  SemidirectProduct.inl (Multiplicative.ofAdd 1)

theorem nativeKlein_glide_square_zpow_eq_inr (k : ℤ) :
    (nativeKleinGlide ^ 2) ^ k =
      SemidirectProduct.inr (Multiplicative.ofAdd (2 * k)) := by
  change ((SemidirectProduct.inr (Multiplicative.ofAdd 1) :
      NativeKleinSemidirect) ^ 2) ^ k = _
  rw [← (SemidirectProduct.inr : Multiplicative ℤ →* NativeKleinSemidirect).map_pow]
  rw [← (SemidirectProduct.inr : Multiplicative ℤ →* NativeKleinSemidirect).map_zpow]
  apply congrArg SemidirectProduct.inr
  have hbase : (Multiplicative.ofAdd 1 : Multiplicative ℤ) ^ (2 : ℕ) =
      Multiplicative.ofAdd 2 := by
    rw [pow_two, ← ofAdd_add]
    norm_num
  rw [hbase]
  calc
    Multiplicative.ofAdd 2 ^ k = Multiplicative.ofAdd (k • (2 : ℤ)) :=
      (ofAdd_zsmul k 2).symm
    _ = Multiplicative.ofAdd (2 * k) := by
      congr 1
      simp [mul_comm]

theorem nativeKlein_glide_conjugates_translation :
    nativeKleinGlide * nativeKleinTranslation * nativeKleinGlide⁻¹ =
      nativeKleinTranslation⁻¹ := by
  apply SemidirectProduct.ext
  · simp [nativeKleinGlide, nativeKleinTranslation, integerInversionAction,
      integerNegMulAut]
  · simp [nativeKleinGlide, nativeKleinTranslation]

theorem nativeKlein_relator_eq_one :
    nativeKleinGlide * nativeKleinTranslation * nativeKleinGlide⁻¹ *
        nativeKleinTranslation = 1 := by
  rw [nativeKlein_glide_conjugates_translation]
  simp

theorem nativeKlein_even_glide_commutes :
    nativeKleinGlide ^ 2 * nativeKleinTranslation =
      nativeKleinTranslation * nativeKleinGlide ^ 2 := by
  let a := nativeKleinGlide
  let b := nativeKleinTranslation
  have hrel : a * b * a⁻¹ = b⁻¹ := by
    simpa [a, b] using nativeKlein_glide_conjugates_translation
  have hab : a * b = b⁻¹ * a := by
    calc
      a * b = (a * b * a⁻¹) * a := by simp [mul_assoc]
      _ = b⁻¹ * a := by rw [hrel]
  have hinv : a * b⁻¹ = b * a := by
    have hrelInv : a * b⁻¹ * a⁻¹ = b := by
      calc
        a * b⁻¹ * a⁻¹ = (a * b * a⁻¹)⁻¹ := by simp [mul_assoc]
        _ = (b⁻¹)⁻¹ := by rw [hrel]
        _ = b := by simp
    calc
      a * b⁻¹ = (a * b⁻¹ * a⁻¹) * a := by simp [mul_assoc]
      _ = b * a := by rw [hrelInv]
  change (a * a) * b = b * (a * a)
  calc
    (a * a) * b = a * (a * b) := by rw [mul_assoc]
    _ = a * (b⁻¹ * a) := by rw [hab]
    _ = (a * b⁻¹) * a := by rw [mul_assoc]
    _ = (b * a) * a := by rw [hinv]
    _ = b * (a * a) := by rw [mul_assoc]

/--
The even glide is central in the native semidirect-product carrier.  Its
conjugation action on the translation coordinate is the square of negation,
which is the identity; the acting `Multiplicative ℤ` coordinate is abelian.
This is an algebraic center witness, not a topological identification.
-/
theorem nativeKlein_glide_square_central
    (x : NativeKleinSemidirect) :
    nativeKleinGlide ^ 2 * x = x * nativeKleinGlide ^ 2 := by
  apply SemidirectProduct.ext
  · simp [nativeKleinGlide, integerInversionAction, integerNegMulAut, pow_two]
    change Multiplicative.ofAdd (-(-x.left.toAdd)) = x.left
    simp
  · simp [nativeKleinGlide, pow_two]
    rw [← ofAdd_add]
    simp [mul_comm]

theorem nativeKlein_glide_square_mem_center :
    nativeKleinGlide ^ 2 ∈ Subgroup.center NativeKleinSemidirect := by
  rw [Subgroup.mem_center_iff]
  intro x
  exact (nativeKlein_glide_square_central x).symm

theorem nativeKlein_center_left_eq_zero
    (x : NativeKleinSemidirect)
    (hx : x ∈ Subgroup.center NativeKleinSemidirect) :
    x.left = Multiplicative.ofAdd 0 := by
  rw [Subgroup.mem_center_iff] at hx
  have h := hx (SemidirectProduct.inr (Multiplicative.ofAdd 1))
  have h' := congrArg (fun y : NativeKleinSemidirect => y.left) h
  rw [SemidirectProduct.mul_def, SemidirectProduct.mul_def] at h'
  dsimp at h'
  change 1 * (integerInversionAction (Multiplicative.ofAdd 1)) x.left =
      x.left * (integerInversionAction x.right) 1 at h'
  simp only [one_mul, map_one, mul_one] at h'
  simp [integerInversionAction, integerNegMulAut] at h'
  apply Multiplicative.ext
  have h'' := congrArg Multiplicative.toAdd h'
  simp at h''
  simpa using (show x.left.toAdd = 0 by linarith [h''])

theorem nativeKlein_mem_center_iff
    (x : NativeKleinSemidirect) :
    x ∈ Subgroup.center NativeKleinSemidirect ↔
      x.left = Multiplicative.ofAdd 0 ∧
        ∀ a : Multiplicative ℤ,
          (integerInversionAction x.right) a = a := by
  constructor
  · intro hx
    have hleft := nativeKlein_center_left_eq_zero x hx
    refine ⟨hleft, ?_⟩
    intro a
    rw [Subgroup.mem_center_iff] at hx
    have h := hx (SemidirectProduct.inl a)
    have h' := congrArg (fun y : NativeKleinSemidirect => y.left) h
    rw [SemidirectProduct.mul_def, SemidirectProduct.mul_def] at h'
    dsimp at h'
    rw [hleft] at h'
    simp at h'
    exact h'.symm
  · rintro ⟨hleft, hact⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.mul_def, SemidirectProduct.mul_def]
      dsimp
      rw [hleft, hact]
      simp
    · rw [SemidirectProduct.mul_def, SemidirectProduct.mul_def]
      exact mul_comm _ _

def nativeKleinPresentationRep : KleinGroup →* NativeKleinSemidirect :=
  kleinRep nativeKleinGlide nativeKleinTranslation
    nativeKlein_glide_conjugates_translation

theorem nativeKleinPresentationRep_generators :
    nativeKleinPresentationRep (toKlein genA) = nativeKleinGlide ∧
    nativeKleinPresentationRep (toKlein genB) = nativeKleinTranslation := by
  exact kleinRep_relator_relation nativeKleinGlide nativeKleinTranslation
    nativeKlein_glide_conjugates_translation

theorem nativeKleinPresentationRep_surjective :
    Function.Surjective nativeKleinPresentationRep := by
  intro x
  refine ⟨toKlein genB ^ x.left.toAdd * toKlein genA ^ x.right.toAdd, ?_⟩
  rw [map_mul, map_zpow, map_zpow]
  have hg := nativeKleinPresentationRep_generators
  rw [hg.2, hg.1]
  change (SemidirectProduct.inl (Multiplicative.ofAdd 1) : NativeKleinSemidirect) ^
      x.left.toAdd *
      (SemidirectProduct.inr (Multiplicative.ofAdd 1) : NativeKleinSemidirect) ^
        x.right.toAdd = x
  rw [← (SemidirectProduct.inl : Multiplicative ℤ →* NativeKleinSemidirect).map_zpow,
    ← (SemidirectProduct.inr : Multiplicative ℤ →* NativeKleinSemidirect).map_zpow]
  rw [← ofAdd_zsmul, ← ofAdd_zsmul]
  simpa only [zsmul_one] using SemidirectProduct.inl_left_mul_inr_right x

theorem nativeKlein_integer_conjugation :
    ∀ n : ℤ,
      (toKlein genA) ^ n * toKlein genB * (toKlein genA ^ n)⁻¹ =
        (toKlein genB) ^
          ((integerNegMulAut ^ n) (Multiplicative.ofAdd 1)).toAdd := by
  let a : KleinGroup := toKlein genA
  let b : KleinGroup := toKlein genB
  have hrel : a * b * a⁻¹ = b⁻¹ := by
    simpa [a, b] using klein_generator_relation
  have hrelInv : a⁻¹ * b * a = b⁻¹ := by
    have hrel' : a * b⁻¹ * a⁻¹ = b := by
      simpa [mul_assoc] using congrArg Inv.inv hrel
    have h := congrArg (fun x : KleinGroup => a⁻¹ * x * a) hrel'
    simpa [mul_assoc] using h.symm
  have hneg_action : ∀ k : ℤ,
      ((integerNegMulAut ^ (k + 1))
          (Multiplicative.ofAdd 1)).toAdd =
        -((integerNegMulAut ^ k)
          (Multiplicative.ofAdd 1)).toAdd := by
    intro k
    rw [zpow_add, MulAut.mul_apply, zpow_one]
    have hk : Multiplicative.ofAdd (-1) =
        (Multiplicative.ofAdd 1)⁻¹ := by simp
    rw [show integerNegMulAut (Multiplicative.ofAdd 1) =
        Multiplicative.ofAdd (-1) by rfl, hk, map_inv]
    simp
  have hinvA : integerNegMulAut⁻¹ = integerNegMulAut := by
    ext x
    simp [integerNegMulAut]
  have haux : ∀ n : ℤ,
      ((MulAut.conj a) ^ n) b =
        b ^ ((integerNegMulAut ^ n) (Multiplicative.ofAdd 1)).toAdd := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ i hi =>
        rw [zpow_add, MulAut.mul_apply, zpow_one, MulAut.conj_apply, hrel,
          map_inv, hi]
        rw [← zpow_neg, hneg_action]
    | pred i hi =>
        have hpred :
            ((integerNegMulAut ^ (-((i : ℤ)) - 1))
                (Multiplicative.ofAdd 1)).toAdd =
              -((integerNegMulAut ^ (-((i : ℤ))))
                (Multiplicative.ofAdd 1)).toAdd := by
          calc
            ((integerNegMulAut ^ (-((i : ℤ)) - 1))
                (Multiplicative.ofAdd 1)).toAdd =
                ((integerNegMulAut ^ (-((i : ℤ))) *
                    integerNegMulAut⁻¹)
                  (Multiplicative.ofAdd 1)).toAdd := by
                    rw [show (-((i : ℤ)) - 1) =
                        (-((i : ℤ))) + (-1) by ring, zpow_add,
                      zpow_neg_one]
            _ = ((integerNegMulAut ^ (-((i : ℤ))) *
                    integerNegMulAut)
                  (Multiplicative.ofAdd 1)).toAdd := by rw [hinvA]
            _ = ((integerNegMulAut ^ (-((i : ℤ)) + 1))
                  (Multiplicative.ofAdd 1)).toAdd := by
                    rw [zpow_add, zpow_one]
            _ = -((integerNegMulAut ^ (-((i : ℤ))))
                (Multiplicative.ofAdd 1)).toAdd := hneg_action _
        rw [show (-((i : ℤ)) - 1) = (-((i : ℤ))) + (-1) by ring,
          zpow_add, MulAut.mul_apply, zpow_neg_one,
          MulAut.conj_inv_apply, hrelInv, map_inv, hi]
        have hpred' :
            ((integerNegMulAut ^ (-((i : ℤ)) + (-1)))
                (Multiplicative.ofAdd 1)).toAdd =
              -((integerNegMulAut ^ (-((i : ℤ))))
                (Multiplicative.ofAdd 1)).toAdd := by
          exact hpred
        rw [← zpow_neg, hpred']
  intro n
  rw [← haux n, ← map_zpow (MulAut.conj) a n]
  rfl

def nativeKleinTranslationHom : Multiplicative ℤ →* KleinGroup :=
  zpowersHom _ (toKlein genB)

def nativeKleinGlideHom : Multiplicative ℤ →* KleinGroup :=
  zpowersHom _ (toKlein genA)

theorem nativeKlein_lift_compatibility (g : Multiplicative ℤ) :
    nativeKleinTranslationHom.comp (integerInversionAction g).toMonoidHom =
      (MulAut.conj (nativeKleinGlideHom g)).toMonoidHom.comp
        nativeKleinTranslationHom := by
  apply MonoidHom.ext_mint
  change nativeKleinTranslationHom
      (integerInversionAction g (Multiplicative.ofAdd 1)) =
    (nativeKleinGlideHom g) *
      nativeKleinTranslationHom (Multiplicative.ofAdd 1) *
        (nativeKleinGlideHom g)⁻¹
  change (toKlein genB) ^
      (integerInversionAction g (Multiplicative.ofAdd 1)).toAdd =
    (toKlein genA) ^ g.toAdd * toKlein genB *
      ((toKlein genA) ^ g.toAdd)⁻¹
  exact (nativeKlein_integer_conjugation g.toAdd).symm

def nativeKleinPresentationInverse :
    NativeKleinSemidirect →* KleinGroup :=
  SemidirectProduct.lift nativeKleinTranslationHom nativeKleinGlideHom
    (fun g => nativeKlein_lift_compatibility g)

theorem nativeKlein_hom_ext {H : Type*} [Group H]
    {f g : KleinGroup →* H}
    (ha : f (toKlein genA) = g (toKlein genA))
    (hb : f (toKlein genB) = g (toKlein genB)) : f = g := by
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective KleinNormal x
  have hfg : f.comp toKlein = g.comp toKlein := by
    apply FreeGroup.ext_hom
    intro gen
    cases gen with
    | a => simpa [genA] using ha
    | b => simpa [genB] using hb
  exact congrArg (fun q => q y) hfg

theorem nativeKleinPresentationInverse_left :
    nativeKleinPresentationInverse.comp nativeKleinPresentationRep =
      MonoidHom.id KleinGroup := by
  apply nativeKlein_hom_ext
  · change nativeKleinPresentationInverse
        (nativeKleinPresentationRep (toKlein genA)) = toKlein genA
    rw [(nativeKleinPresentationRep_generators).1]
    simp [nativeKleinPresentationInverse, nativeKleinGlide,
      nativeKleinGlideHom]
  · change nativeKleinPresentationInverse
        (nativeKleinPresentationRep (toKlein genB)) = toKlein genB
    rw [(nativeKleinPresentationRep_generators).2]
    simp [nativeKleinPresentationInverse, nativeKleinTranslation,
      nativeKleinTranslationHom]

theorem nativeKleinPresentationInverse_right :
    nativeKleinPresentationRep.comp nativeKleinPresentationInverse =
      MonoidHom.id NativeKleinSemidirect := by
  apply SemidirectProduct.hom_ext
  · apply MonoidHom.ext
    intro n
    change nativeKleinPresentationRep
        (nativeKleinPresentationInverse (SemidirectProduct.inl n)) =
      SemidirectProduct.inl n
    simp only [nativeKleinPresentationInverse, SemidirectProduct.lift_inl]
    change nativeKleinPresentationRep
        ((zpowersHom KleinGroup (toKlein genB)) n) =
      SemidirectProduct.inl n
    rw [zpowersHom_apply, map_zpow, (nativeKleinPresentationRep_generators).2]
    change (SemidirectProduct.inl (Multiplicative.ofAdd 1) :
        NativeKleinSemidirect) ^ n.toAdd = SemidirectProduct.inl n
    rw [← (SemidirectProduct.inl : Multiplicative ℤ →* NativeKleinSemidirect).map_zpow]
    rw [← ofAdd_zsmul]
    simp
  · apply MonoidHom.ext
    intro g
    change nativeKleinPresentationRep
        (nativeKleinPresentationInverse (SemidirectProduct.inr g)) =
      SemidirectProduct.inr g
    simp only [nativeKleinPresentationInverse, SemidirectProduct.lift_inr]
    change nativeKleinPresentationRep
        ((zpowersHom KleinGroup (toKlein genA)) g) =
      SemidirectProduct.inr g
    rw [zpowersHom_apply, map_zpow, (nativeKleinPresentationRep_generators).1]
    change (SemidirectProduct.inr (Multiplicative.ofAdd 1) :
        NativeKleinSemidirect) ^ g.toAdd = SemidirectProduct.inr g
    rw [← (SemidirectProduct.inr : Multiplicative ℤ →* NativeKleinSemidirect).map_zpow]
    rw [← ofAdd_zsmul]
    simp

def nativeKleinPresentationEquiv :
    KleinGroup ≃* NativeKleinSemidirect :=
  MonoidHom.toMulEquiv nativeKleinPresentationRep
    nativeKleinPresentationInverse nativeKleinPresentationInverse_left
    nativeKleinPresentationInverse_right

theorem nativeKleinPresentationRep_injective :
    Function.Injective nativeKleinPresentationRep :=
  nativeKleinPresentationEquiv.injective

end InfoGeometry.Canonical.KleinNativeSemidirectProductBridge
