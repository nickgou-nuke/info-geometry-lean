import InfoGeometry.Projective.PuncturedAffineLogDifferential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.PuncturedAffineKleinInversionBridge
import InfoGeometry.Projective.KleinQuadricDeRhamComplex

/-!
# Algebraic logarithmic de Rham cohomology of the punctured affine line

This owner computes the two-term Laurent complex
`A --T∂_T→ A --0→ ℂ`, where `A = ℂ[T,T⁻¹]`.  The last copy of `ℂ`
is used only as a zero target.  The computation is constructive: division of
each nonzero Laurent mode supplies a finite-support primitive.
-/

namespace InfoGeometry.Projective.PuncturedAffineLogDeRhamBridge

open scoped LaurentPolynomial
open InfoGeometry.Projective.PuncturedAffineLogDifferential
open InfoGeometry.Projective.KleinQuadric.DeRhamComplex

abbrev LaurentRing := LaurentPolynomial ℂ

noncomputable def constantCoeff : LaurentRing →ₗ[ℂ] ℂ where
  toFun f := f 0
  map_add' f g := by simp
  map_smul' c f := by simp

@[simp] theorem constantCoeff_single (n : ℤ) (c : ℂ) :
    constantCoeff (AddMonoidAlgebra.single n c : LaurentRing) =
      if n = 0 then c else 0 := by
  change (AddMonoidAlgebra.single n c : LaurentRing) 0 = _
  exact AddMonoidAlgebra.single_apply

theorem C_eq_single (c : ℂ) :
    LaurentPolynomial.C c = (AddMonoidAlgebra.single 0 c : LaurentRing) := by
  ext n
  simp [LaurentPolynomial.C_apply]

@[simp] theorem constantCoeff_C (c : ℂ) :
    constantCoeff (LaurentPolynomial.C c) = c := by
  rw [C_eq_single, constantCoeff_single]
  simp

theorem constantCoeff_C_mul_T (c : ℂ) (n : ℤ) :
    constantCoeff (LaurentPolynomial.C c * LaurentPolynomial.T n) =
      if n = 0 then c else 0 := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  exact constantCoeff_single n c

noncomputable def logarithmicPrimitive : LaurentRing →ₗ[ℂ] LaurentRing :=
  Finsupp.lsum ℂ (fun n : ℤ =>
    (if n = 0 then 0 else ((n : ℂ)⁻¹)) •
      (Finsupp.lsingle n : ℂ →ₗ[ℂ] LaurentRing))

@[simp] theorem logarithmicPrimitive_single (n : ℤ) (c : ℂ) :
    logarithmicPrimitive (AddMonoidAlgebra.single n c : LaurentRing) =
      (if n = 0 then 0 else ((n : ℂ)⁻¹)) •
        (AddMonoidAlgebra.single n c : LaurentRing) := by
  change
    ((Finsupp.lsum ℂ) (fun k : ℤ =>
      (if k = 0 then 0 else ((k : ℂ)⁻¹)) •
        (Finsupp.lsingle k : ℂ →ₗ[ℂ] LaurentRing))
      (Finsupp.single n c)) = _
  rw [Finsupp.lsum_single]
  rfl

theorem logarithmicDifferential_primitive_single (n : ℤ) (c : ℂ) :
    logarithmicDifferential
        (logarithmicPrimitive (AddMonoidAlgebra.single n c : LaurentRing)) =
      (AddMonoidAlgebra.single n c : LaurentRing) -
        (AddMonoidAlgebra.single 0
          (constantCoeff (AddMonoidAlgebra.single n c : LaurentRing)) : LaurentRing) := by
  by_cases hn : n = 0
  · subst n
    rw [logarithmicPrimitive_single]
    simp
  · rw [logarithmicPrimitive_single, if_neg hn, map_smul,
      logarithmicDifferential_single, constantCoeff_single, if_neg hn]
    rw [smul_smul]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp [hnC]

theorem logarithmicDifferential_primitive (f : LaurentRing) :
    logarithmicDifferential (logarithmicPrimitive f) =
      f - LaurentPolynomial.C (constantCoeff f) := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
      simp only [map_add, hf, hg]
      ring
  | C_mul_T n c =>
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      rw [C_eq_single]
      exact logarithmicDifferential_primitive_single n c

theorem laurent_decomposition (f : LaurentRing) :
    f = LaurentPolynomial.C (constantCoeff f) +
      logarithmicDifferential (logarithmicPrimitive f) := by
  rw [logarithmicDifferential_primitive]
  abel

theorem constantCoeff_logarithmicDifferential (f : LaurentRing) :
    constantCoeff (logarithmicDifferential f) = 0 := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | C_mul_T n c =>
      rw [← LaurentPolynomial.single_eq_C_mul_T,
        logarithmicDifferential_single, map_smul, constantCoeff_single]
      by_cases hn : n = 0
      · subst n
        simp
      · simp [hn]

theorem range_logarithmicDifferential_eq_ker_constantCoeff :
    LinearMap.range logarithmicDifferential = LinearMap.ker constantCoeff := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact constantCoeff_logarithmicDifferential g
  · intro hf
    rw [LinearMap.mem_ker] at hf
    refine ⟨logarithmicPrimitive f, ?_⟩
    rw [logarithmicDifferential_primitive, hf, map_zero, sub_zero]

theorem logarithmicDifferential_apply (f : LaurentRing) (n : ℤ) :
    logarithmicDifferential f n = (n : ℂ) * f n := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
      rw [map_add]
      change logarithmicDifferential f n + logarithmicDifferential g n =
        (n : ℂ) * (f n + g n)
      rw [hf, hg]
      ring
  | C_mul_T m c =>
      simp only [← LaurentPolynomial.single_eq_C_mul_T]
      rw [logarithmicDifferential_single]
      by_cases hmn : m = n
      · subst n
        simp
      · have hnm : n ≠ m := Ne.symm hmn
        have hs : (Finsupp.single m c) n = 0 :=
          Finsupp.single_eq_of_ne hnm
        rw [Finsupp.smul_apply, hs, smul_zero, mul_zero]

theorem ker_logarithmicDifferential_eq_range_constantEmbedding :
    LinearMap.ker logarithmicDifferential =
      LinearMap.range constantInclusion := by
  ext f
  constructor
  · intro hf
    rw [LinearMap.mem_ker] at hf
    refine ⟨constantCoeff f, ?_⟩
    apply LaurentPolynomial.ext
    intro n
    by_cases hn : n = 0
    · subst n
      simp [constantInclusion, constantCoeff]
    · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hcoeff := congrArg (fun g : LaurentRing => g n) hf
      change logarithmicDifferential f n = 0 at hcoeff
      rw [logarithmicDifferential_apply] at hcoeff
      have hfn : f n = 0 := (mul_eq_zero.mp hcoeff).resolve_left hnC
      simp [constantInclusion, LaurentPolynomial.C_apply, hn, hfn]
  · rintro ⟨c, rfl⟩
    exact logarithmicDifferential_C c

theorem logarithmicDifferential_eq_zero_iff_constant (f : LaurentRing) :
    logarithmicDifferential f = 0 ↔
      ∃ c : ℂ, f = LaurentPolynomial.C c := by
  constructor
  · intro hf
    have hf' : f ∈ LinearMap.ker logarithmicDifferential := by
      exact (LinearMap.mem_ker).2 hf
    rw [ker_logarithmicDifferential_eq_range_constantEmbedding] at hf'
    rcases hf' with ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    exact logarithmicDifferential_C c

noncomputable abbrev puncturedAffineH0 := LinearMap.ker logarithmicDifferential

noncomputable def puncturedAffineH0ConstantFactor :
    puncturedAffineH0 →ₗ[ℂ] ℂ :=
  constantCoeff.domRestrict puncturedAffineH0

theorem puncturedAffineH0ConstantFactor_injective :
    Function.Injective puncturedAffineH0ConstantFactor := by
  intro x y hxy
  obtain ⟨cx, hcx⟩ :=
    (logarithmicDifferential_eq_zero_iff_constant x.1).mp x.2
  obtain ⟨cy, hcy⟩ :=
    (logarithmicDifferential_eq_zero_iff_constant y.1).mp y.2
  have hcoeff : constantCoeff x.1 = constantCoeff y.1 := by
    exact hxy
  rw [hcx, hcy, constantCoeff_C, constantCoeff_C] at hcoeff
  apply Subtype.ext
  rw [hcx, hcy, hcoeff]

theorem puncturedAffineH0ConstantFactor_surjective :
    Function.Surjective puncturedAffineH0ConstantFactor := by
  intro c
  refine ⟨⟨LaurentPolynomial.C c, logarithmicDifferential_C c⟩, ?_⟩
  exact constantCoeff_C c

noncomputable def puncturedAffineH0EquivComplex :
    puncturedAffineH0 ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective puncturedAffineH0ConstantFactor
    ⟨puncturedAffineH0ConstantFactor_injective,
      puncturedAffineH0ConstantFactor_surjective⟩

@[simp] theorem puncturedAffineH0EquivComplex_constant (c : ℂ) :
    puncturedAffineH0EquivComplex
        ⟨LaurentPolynomial.C c, logarithmicDifferential_C c⟩ = c := by
  rw [puncturedAffineH0EquivComplex, LinearEquiv.ofBijective_apply,
    puncturedAffineH0ConstantFactor]
  exact constantCoeff_C c

noncomputable def puncturedAffineD₁ : LaurentRing →ₗ[ℂ] ℂ := 0

theorem puncturedAffine_complex :
    puncturedAffineD₁.comp logarithmicDifferential = 0 := by
  ext f
  rfl

abbrev puncturedAffineH1 :=
  cohomologyModule logarithmicDifferential puncturedAffineD₁ puncturedAffine_complex

noncomputable def puncturedAffineH1ConstantFactor : puncturedAffineH1 →ₗ[ℂ] ℂ :=
  periodClassFactor logarithmicDifferential puncturedAffineD₁
    puncturedAffine_complex constantCoeff constantCoeff_logarithmicDifferential

theorem puncturedAffineH1ConstantFactor_surjective :
    Function.Surjective puncturedAffineH1ConstantFactor := by
  intro c
  refine ⟨closedClass logarithmicDifferential puncturedAffineD₁
    puncturedAffine_complex (LaurentPolynomial.C c) (by rfl), ?_⟩
  rw [puncturedAffineH1ConstantFactor, periodClassFactor_apply]
  exact constantCoeff_C c

theorem puncturedAffineH1ConstantFactor_injective :
    Function.Injective puncturedAffineH1ConstantFactor := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hfactor : puncturedAffineH1ConstantFactor (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := cycleQuotientMap_surjective
    logarithmicDifferential puncturedAffineD₁ puncturedAffine_complex (x - y)
  rw [← hz] at hfactor ⊢
  have hct : constantCoeff z.1 = 0 := by
    simpa [puncturedAffineH1ConstantFactor, periodClassFactor_apply] using hfactor
  have hrange : z.1 ∈ LinearMap.range logarithmicDifferential := by
    rw [range_logarithmicDifferential_eq_ker_constantCoeff, LinearMap.mem_ker]
    exact hct
  apply (Submodule.Quotient.mk_eq_zero _).2
  rw [Submodule.mem_comap]
  exact hrange

noncomputable def puncturedAffineH1EquivComplex : puncturedAffineH1 ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective puncturedAffineH1ConstantFactor
    ⟨puncturedAffineH1ConstantFactor_injective,
      puncturedAffineH1ConstantFactor_surjective⟩

noncomputable def dlogClass : puncturedAffineH1 :=
  closedClass logarithmicDifferential puncturedAffineD₁ puncturedAffine_complex
    1 (by rfl)

@[simp] theorem puncturedAffineH1EquivComplex_dlogClass :
    puncturedAffineH1EquivComplex dlogClass = 1 := by
  rw [puncturedAffineH1EquivComplex, LinearEquiv.ofBijective_apply,
    puncturedAffineH1ConstantFactor]
  unfold dlogClass
  rw [periodClassFactor_apply]
  exact constantCoeff_C 1

noncomputable def puncturedAffineWindingClass (n : ℤ) : puncturedAffineH1 :=
  (n : ℂ) • dlogClass

@[simp]
theorem puncturedAffineH1EquivComplex_windingClass (n : ℤ) :
    puncturedAffineH1EquivComplex (puncturedAffineWindingClass n) =
      (n : ℂ) := by
  unfold puncturedAffineWindingClass
  rw [map_smul, puncturedAffineH1EquivComplex_dlogClass]
  simp

@[simp] theorem puncturedAffineWindingClass_zero :
    puncturedAffineWindingClass 0 = 0 := by
  simp [puncturedAffineWindingClass]

theorem puncturedAffineWindingClass_add (m n : ℤ) :
    puncturedAffineWindingClass (m + n) =
      puncturedAffineWindingClass m + puncturedAffineWindingClass n := by
  unfold puncturedAffineWindingClass
  rw [Int.cast_add, add_smul]

noncomputable def puncturedAffineWindingAddHom : ℤ →+ puncturedAffineH1 where
  toFun n := puncturedAffineWindingClass n
  map_zero' := puncturedAffineWindingClass_zero
  map_add' m n := puncturedAffineWindingClass_add m n

@[simp]
theorem puncturedAffineWindingAddHom_apply (n : ℤ) :
    puncturedAffineWindingAddHom n = puncturedAffineWindingClass n :=
  rfl

theorem puncturedAffineWindingClass_neg (n : ℤ) :
    puncturedAffineWindingClass (-n) =
      -puncturedAffineWindingClass n := by
  unfold puncturedAffineWindingClass
  rw [Int.cast_neg, neg_smul]

theorem puncturedAffineWindingClass_ne_zero_iff (n : ℤ) :
    puncturedAffineWindingClass n ≠ 0 ↔ n ≠ 0 := by
  constructor
  · intro h hn
    apply h
    simp [puncturedAffineWindingClass, hn]
  · intro hn hzero
    have hmap := congrArg puncturedAffineH1EquivComplex hzero
    have hscalar : (n : ℂ) = 0 := by
      simpa [puncturedAffineWindingClass,
        map_smul, puncturedAffineH1EquivComplex_dlogClass] using hmap
    exact hn (by exact_mod_cast hscalar)

theorem puncturedAffineWindingAddHom_injective :
    Function.Injective puncturedAffineWindingAddHom := by
  intro m n hmn
  have hclass : puncturedAffineWindingClass m =
      puncturedAffineWindingClass n := by
    simpa only [puncturedAffineWindingAddHom_apply] using hmn
  by_contra hne
  have hdiff : m - n ≠ 0 := sub_ne_zero.mpr hne
  have hnonzero : puncturedAffineWindingClass (m - n) ≠ 0 :=
    (puncturedAffineWindingClass_ne_zero_iff (m - n)).2 hdiff
  apply hnonzero
  calc
    puncturedAffineWindingClass (m - n) =
        puncturedAffineWindingClass m -
          puncturedAffineWindingClass n := by
      rw [sub_eq_add_neg, puncturedAffineWindingClass_add,
        puncturedAffineWindingClass_neg]
      simp only [sub_eq_add_neg]
    _ = 0 := sub_eq_zero.mpr hclass

theorem puncturedAffineH1_eq_readout_smul_dlogClass
    (x : puncturedAffineH1) :
    x = puncturedAffineH1EquivComplex x • dlogClass := by
  apply puncturedAffineH1EquivComplex.injective
  rw [map_smul, puncturedAffineH1EquivComplex_dlogClass]
  simp

theorem closedClass_eq_constantCoeff_smul_dlog (f : LaurentRing) :
    closedClass logarithmicDifferential puncturedAffineD₁ puncturedAffine_complex
        f (by rfl) =
      constantCoeff f • dlogClass := by
  apply puncturedAffineH1EquivComplex.injective
  change constantCoeff f = constantCoeff f * constantCoeff 1
  have hOne : constantCoeff (1 : LaurentRing) = 1 := by
    exact constantCoeff_C 1
  rw [hOne, mul_one]

theorem closedClass_eq_zero_iff_constantCoeff_eq_zero (f : LaurentRing) :
    closedClass logarithmicDifferential puncturedAffineD₁ puncturedAffine_complex
        f (by rfl) = 0 ↔
      constantCoeff f = 0 := by
  rw [closedClass_eq_constantCoeff_smul_dlog]
  constructor
  · intro h
    have hmap := congrArg puncturedAffineH1EquivComplex h
    simpa [map_smul, puncturedAffineH1EquivComplex_dlogClass] using hmap
  · intro h
    simp [h]

theorem puncturedAffineH1EquivComplex_closedClass (f : LaurentRing) :
    puncturedAffineH1EquivComplex
        (closedClass logarithmicDifferential puncturedAffineD₁
          puncturedAffine_complex f (by rfl)) =
      constantCoeff f := by
  rw [closedClass_eq_constantCoeff_smul_dlog, map_smul,
    puncturedAffineH1EquivComplex_dlogClass]
  simp

noncomputable def puncturedAffineH1ToAlgebraicDeRhamH1 :
    puncturedAffineH1 ≃ₗ[ℂ] algebraicDeRhamH1 :=
  puncturedAffineH1EquivComplex.trans algebraicDeRhamH1Equiv.symm

theorem puncturedAffineH1ToAlgebraicDeRhamH1_closedClass (f : LaurentRing) :
    puncturedAffineH1ToAlgebraicDeRhamH1
        (closedClass logarithmicDifferential puncturedAffineD₁
          puncturedAffine_complex f (by rfl)) =
      Submodule.Quotient.mk f := by
  apply algebraicDeRhamH1Equiv.injective
  simp [puncturedAffineH1ToAlgebraicDeRhamH1,
    puncturedAffineH1EquivComplex_closedClass,
    algebraicDeRhamH1Equiv_mk]
  rfl

theorem puncturedAffineH1ToAlgebraicDeRhamH1_windingClass (n : ℤ) :
    puncturedAffineH1ToAlgebraicDeRhamH1 (puncturedAffineWindingClass n) =
      (n : ℂ) • Submodule.Quotient.mk (1 : LaurentRing) := by
  simp [puncturedAffineWindingClass,
    dlogClass, puncturedAffineH1ToAlgebraicDeRhamH1_closedClass]

noncomputable def kleinOneFormAction : LaurentRing →ₗ[ℂ] LaurentRing :=
  -PuncturedAffineKleinInversionBridge.inversion.toLinearMap

theorem constantCoeff_inversion (f : LaurentRing) :
    constantCoeff (PuncturedAffineKleinInversionBridge.inversion f) =
      constantCoeff f := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg]
  | C_mul_T n c =>
      rw [map_mul, PuncturedAffineKleinInversionBridge.inversion_T]
      simp only [PuncturedAffineKleinInversionBridge.inversion,
        LaurentPolynomial.invert_C]
      rw [constantCoeff_C_mul_T, constantCoeff_C_mul_T]
      by_cases hn : n = 0
      · subst n
        simp
      · have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
        simp [hn, hneg]

theorem constantCoeff_kleinOneFormAction (f : LaurentRing) :
    constantCoeff (kleinOneFormAction f) = -constantCoeff f := by
  change constantCoeff (-(PuncturedAffineKleinInversionBridge.inversion f)) = _
  rw [map_neg, constantCoeff_inversion]

noncomputable def algebraicDeRhamCochainDegreeZero : LaurentRing ≃ₐ[ℂ] LaurentRing :=
  PuncturedAffineKleinInversionBridge.inversion

noncomputable def algebraicDeRhamCochainDegreeOne : LaurentRing ≃ₗ[ℂ] LaurentRing :=
  (PuncturedAffineKleinInversionBridge.inversion.toLinearEquiv).trans
    (LinearEquiv.neg ℂ)

theorem algebraicDeRhamCochainDegreeZero_involutive :
    Function.Involutive algebraicDeRhamCochainDegreeZero := by
  intro f
  exact PuncturedAffineKleinInversionBridge.inversion_involutive f

theorem algebraicDeRhamCochainDegreeOne_involutive :
    Function.Involutive algebraicDeRhamCochainDegreeOne := by
  intro f
  simp [algebraicDeRhamCochainDegreeOne,
    PuncturedAffineKleinInversionBridge.inversion_involutive]

theorem algebraicDeRhamCochain_commutes (f : LaurentRing) :
    logarithmicDifferential (algebraicDeRhamCochainDegreeZero f) =
      algebraicDeRhamCochainDegreeOne (logarithmicDifferential f) := by
  exact PuncturedAffineKleinInversionBridge.logarithmicDifferential_inversion_anticommute f

noncomputable def algebraicDeRhamH1Inversion : puncturedAffineH1 ≃ₗ[ℂ] puncturedAffineH1 :=
  LinearEquiv.refl ℂ puncturedAffineH1

theorem algebraicDeRhamH1Inversion_closedClass (f : LaurentRing) :
    algebraicDeRhamH1Inversion
        (closedClass logarithmicDifferential puncturedAffineD₁ puncturedAffine_complex
          f (by rfl)) =
      closedClass logarithmicDifferential puncturedAffineD₁ puncturedAffine_complex
        (PuncturedAffineKleinInversionBridge.inversion f) (by rfl) := by
  rw [closedClass_eq_constantCoeff_smul_dlog,
    closedClass_eq_constantCoeff_smul_dlog, constantCoeff_inversion]
  rfl

noncomputable def algebraicDeRhamH1Pullback : puncturedAffineH1 ≃ₗ[ℂ] puncturedAffineH1 :=
  LinearEquiv.neg ℂ

@[simp] theorem algebraicDeRhamH1Pullback_apply (x : puncturedAffineH1) :
    algebraicDeRhamH1Pullback x = -x := rfl

@[simp] theorem algebraicDeRhamH1Pullback_dlogClass :
    algebraicDeRhamH1Pullback dlogClass = -dlogClass := rfl

theorem algebraicDeRhamH1Pullback_windingClass (n : ℤ) :
    algebraicDeRhamH1Pullback (puncturedAffineWindingClass n) =
      puncturedAffineWindingClass (-n) := by
  unfold puncturedAffineWindingClass
  rw [map_smul, algebraicDeRhamH1Pullback_dlogClass,
    Int.cast_neg, neg_smul]
  simp only [smul_neg]

theorem puncturedAffineH1EquivComplex_pullback (x : puncturedAffineH1) :
    puncturedAffineH1EquivComplex (algebraicDeRhamH1Pullback x) =
      -puncturedAffineH1EquivComplex x := by
  simp

theorem puncturedAffineH1ToAlgebraicDeRhamH1_pullback_closedClass
    (f : LaurentRing) :
    puncturedAffineH1ToAlgebraicDeRhamH1
        (algebraicDeRhamH1Pullback
          (closedClass logarithmicDifferential puncturedAffineD₁
            puncturedAffine_complex f (by rfl))) =
      InfoGeometry.Projective.PuncturedAffineLogDifferential.algebraicDeRhamH1Pullback
        (puncturedAffineH1ToAlgebraicDeRhamH1
          (closedClass logarithmicDifferential puncturedAffineD₁
            puncturedAffine_complex f (by rfl))) := by
  apply algebraicDeRhamH1Equiv.injective
  rw [puncturedAffineH1ToAlgebraicDeRhamH1_closedClass]
  rw [InfoGeometry.Projective.PuncturedAffineLogDifferential.algebraicDeRhamH1Pullback_readout]
  simp [puncturedAffineH1ToAlgebraicDeRhamH1,
    puncturedAffineH1EquivComplex_closedClass]
  rfl

end InfoGeometry.Projective.PuncturedAffineLogDeRhamBridge
