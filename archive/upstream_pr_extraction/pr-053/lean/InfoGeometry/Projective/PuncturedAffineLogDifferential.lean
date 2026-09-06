import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum

namespace InfoGeometry.Projective.PuncturedAffineLogDifferential

open scoped LaurentPolynomial

abbrev LaurentRing := LaurentPolynomial ℂ

noncomputable def logarithmicDifferential : LaurentRing →ₗ[ℂ] LaurentRing :=
  Finsupp.lsum ℂ (fun n : ℤ =>
    (n : ℂ) • (Finsupp.lsingle n : ℂ →ₗ[ℂ] LaurentRing))

@[simp] theorem logarithmicDifferential_single (n : ℤ) (c : ℂ) :
    logarithmicDifferential (Finsupp.single n c) =
      (n : ℂ) • Finsupp.single n c := by
  change
    ((Finsupp.lsum ℂ) (fun k : ℤ =>
      (k : ℂ) • (Finsupp.lsingle k : ℂ →ₗ[ℂ] LaurentRing))
      (Finsupp.single n c)) = _
  rw [Finsupp.lsum_single]
  rfl

@[simp] theorem logarithmicDifferential_zero :
    logarithmicDifferential (0 : LaurentRing) = 0 := by
  exact map_zero logarithmicDifferential

@[simp] theorem logarithmicDifferential_one :
    logarithmicDifferential (1 : LaurentRing) = 0 := by
  rw [← LaurentPolynomial.single_zero_one_eq_one]
  rw [logarithmicDifferential_single]
  simp

@[simp] theorem logarithmicDifferential_C (c : ℂ) :
    logarithmicDifferential (LaurentPolynomial.C c) = 0 := by
  change logarithmicDifferential (Finsupp.single (0 : ℤ) c) = 0
  rw [logarithmicDifferential_single]
  simp

theorem logarithmicDifferential_C_mul_T (c : ℂ) (n : ℤ) :
    logarithmicDifferential
        (LaurentPolynomial.C c * LaurentPolynomial.T n) =
      (n : ℂ) • (LaurentPolynomial.C c * LaurentPolynomial.T n) := by
  rw [← LaurentPolynomial.single_eq_C_mul_T,
    logarithmicDifferential_single]

theorem logarithmicDifferential_mul (f g : LaurentRing) :
    logarithmicDifferential (f * g) =
      logarithmicDifferential f * g + f * logarithmicDifferential g := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
      simp only [add_mul, map_add, hf, hg]
      ring
  | C_mul_T n c =>
      induction g using LaurentPolynomial.induction_on' with
      | add f g hf hg =>
          simp only [mul_add, map_add, hf, hg]
          ring
      | C_mul_T m d =>
          rw [← LaurentPolynomial.single_eq_C_mul_T,
            ← LaurentPolynomial.single_eq_C_mul_T,
            AddMonoidAlgebra.single_mul_single,
            logarithmicDifferential_single]
          simp only [logarithmicDifferential_single]
          rw [Int.cast_add, add_smul, smul_mul_assoc, mul_smul_comm,
            AddMonoidAlgebra.single_mul_single]

theorem logarithmicDifferential_derivation_leibniz (f g : LaurentRing) :
    logarithmicDifferential (f * g) =
      f • logarithmicDifferential g + g • logarithmicDifferential f := by
  rw [logarithmicDifferential_mul]
  simpa [Algebra.smul_def, mul_comm] using
    (add_comm (logarithmicDifferential f * g)
      (f * logarithmicDifferential g))

noncomputable def logarithmicDerivation :
    Derivation ℂ LaurentRing LaurentRing :=
  Derivation.mk' logarithmicDifferential logarithmicDifferential_derivation_leibniz

noncomputable def constantCoefficient : LaurentRing →ₗ[ℂ] ℂ :=
  Finsupp.lapply (R := ℂ) (M := ℂ) (0 : ℤ)

noncomputable def constantInclusion : ℂ →ₗ[ℂ] LaurentRing :=
  { toFun := LaurentPolynomial.C
    map_add' := by intro c d; simp
    map_smul' := by intro c d; simp [Algebra.smul_def] }

noncomputable def logarithmicPrimitive : LaurentRing →ₗ[ℂ] LaurentRing :=
  Finsupp.lsum ℂ (fun n : ℤ =>
    if n = 0 then 0
    else (n : ℂ)⁻¹ • (Finsupp.lsingle n : ℂ →ₗ[ℂ] LaurentRing))

@[simp] theorem constantCoefficient_single (n : ℤ) (c : ℂ) :
    constantCoefficient (Finsupp.single n c) = if n = 0 then c else 0 := by
  change (Finsupp.single n c : LaurentRing) 0 = _
  simp only [Finsupp.single_apply]

theorem constantCoefficient_C_mul_T (c : ℂ) (n : ℤ) :
    constantCoefficient (LaurentPolynomial.C c * LaurentPolynomial.T n) =
      if n = 0 then c else 0 := by
  simpa only [← LaurentPolynomial.single_eq_C_mul_T] using
    constantCoefficient_single n c

@[simp] theorem logarithmicPrimitive_single (n : ℤ) (c : ℂ) :
    logarithmicPrimitive (Finsupp.single n c) =
      if n = 0 then 0 else (n : ℂ)⁻¹ • Finsupp.single n c := by
  change
    Finsupp.lsum ℂ (fun n : ℤ =>
      if n = 0 then 0
      else (n : ℂ)⁻¹ • (Finsupp.lsingle n : ℂ →ₗ[ℂ] LaurentRing))
      (Finsupp.single n c) = _
  rw [Finsupp.lsum_single]
  by_cases h : n = 0
  · simp [h]
  · simp [h]

theorem logarithmicPrimitive_C_mul_T (c : ℂ) (n : ℤ) :
    logarithmicPrimitive (LaurentPolynomial.C c * LaurentPolynomial.T n) =
      if n = 0 then 0
      else (n : ℂ)⁻¹ • (LaurentPolynomial.C c * LaurentPolynomial.T n) := by
  simpa only [← LaurentPolynomial.single_eq_C_mul_T] using
    logarithmicPrimitive_single n c

theorem logarithmicDifferential_primitive (f : LaurentRing) :
    logarithmicDifferential (logarithmicPrimitive f) =
      f - LaurentPolynomial.C (constantCoefficient f) := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
      simp only [map_add, hf, hg, sub_add, add_sub]
      ring
  | C_mul_T n c =>
      rw [← LaurentPolynomial.single_eq_C_mul_T,
        logarithmicPrimitive_single, constantCoefficient_single]
      by_cases h : n = 0
      · simp [h]
      · simp only [h, if_false, LinearMap.map_smul]
        rw [logarithmicDifferential_single]
        simp only [map_zero, sub_zero]
        rw [smul_smul]
        have hn : (n : ℂ) ≠ 0 := by
          exact_mod_cast h
        rw [inv_mul_cancel₀ hn, one_smul]

theorem logarithmicDifferential_eq_zero_iff (f : LaurentRing) :
    logarithmicDifferential f = 0 ↔
      ∃ c : ℂ, f = LaurentPolynomial.C c := by
  constructor
  · intro hf
    refine ⟨constantCoefficient f, ?_⟩
    apply LaurentPolynomial.ext
    intro n
    by_cases hn : n = 0
    · subst n
      rw [LaurentPolynomial.C_apply]
      simp only [if_pos]
      exact (Finsupp.lapply_apply (R := ℂ) (M := ℂ) (0 : ℤ) f).symm
    · have hdn := congrArg (fun p : LaurentRing => p n) hf
      have hcoeff :
          logarithmicDifferential f n = (n : ℂ) * f n := by
        change
          (Finsupp.lsum ℂ (fun n : ℤ =>
            (n : ℂ) • (Finsupp.lsingle n : ℂ →ₗ[ℂ] LaurentRing)) f) n =
            (n : ℂ) * f n
        rw [Finsupp.lsum_apply, Finsupp.sum_apply]
        have hs := Finsupp.sum_eq_single (f := f)
          (g := fun b c =>
            ((b : ℂ) • (Finsupp.lsingle b : ℂ →ₗ[ℂ] LaurentRing)) c n) n
          (fun b hb hbn => by
            change (b : ℂ) • (Finsupp.single b (f b)) n = 0
            rw [Finsupp.single_eq_of_ne (Ne.symm hbn), smul_zero])
          (by
            intro hfn
            change (n : ℂ) • (Finsupp.single n (0 : ℂ)) n = 0
            simp)
        calc
          (Finsupp.sum f fun a b =>
              ((a : ℂ) • (Finsupp.single a b)) n) =
              ((n : ℂ) • (Finsupp.single n (f n))) n := hs
          _ = (n : ℂ) * f n := by
            rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul]
      change logarithmicDifferential f n = 0 at hdn
      rw [hcoeff] at hdn
      have hnC : (n : ℂ) ≠ 0 := by
        exact_mod_cast hn
      have hfn : f n = 0 := by
        apply (mul_eq_zero.mp hdn).resolve_left hnC
      rw [LaurentPolynomial.C_apply]
      simp [hn, hfn]
  · rintro ⟨c, rfl⟩
    exact logarithmicDifferential_C c

theorem logarithmicDifferential_ker_eq_constantInclusion_range :
    LinearMap.ker logarithmicDifferential =
      LinearMap.range constantInclusion := by
  apply le_antisymm
  · intro f hf
    rcases (logarithmicDifferential_eq_zero_iff f).mp hf with ⟨c, hc⟩
    exact ⟨c, by simpa [constantInclusion] using hc.symm⟩
  · rintro _ ⟨c, rfl⟩
    exact LinearMap.mem_ker.mpr (by
      simpa [constantInclusion] using (logarithmicDifferential_C c))

abbrev algebraicDeRhamH0 : Type := LinearMap.ker logarithmicDifferential

noncomputable def algebraicDeRhamH0Readout :
    algebraicDeRhamH0 →ₗ[ℂ] ℂ :=
  constantCoefficient.comp (LinearMap.ker logarithmicDifferential).subtype

@[simp] theorem algebraicDeRhamH0Readout_apply
    (f : LaurentRing) (hf : logarithmicDifferential f = 0) :
    algebraicDeRhamH0Readout ⟨f, hf⟩ = constantCoefficient f := rfl

noncomputable def algebraicDeRhamH0Equiv :
    algebraicDeRhamH0 ≃ₗ[ℂ] ℂ := by
  apply LinearEquiv.ofBijective algebraicDeRhamH0Readout
  constructor
  · intro x y hxy
    apply Subtype.ext
    rcases (logarithmicDifferential_eq_zero_iff x.1).mp x.2 with ⟨cx, hcx⟩
    rcases (logarithmicDifferential_eq_zero_iff y.1).mp y.2 with ⟨cy, hcy⟩
    have hxy' : constantCoefficient x.1 = constantCoefficient y.1 := hxy
    rw [hcx, hcy] at hxy'
    have hcx0 : constantCoefficient (LaurentPolynomial.C cx) = cx := by
      simpa using constantCoefficient_C_mul_T cx 0
    have hcy0 : constantCoefficient (LaurentPolynomial.C cy) = cy := by
      simpa using constantCoefficient_C_mul_T cy 0
    have hcc : cx = cy := hcx0.symm.trans (hxy'.trans hcy0)
    subst cy
    exact hcx.trans hcy.symm
  · intro c
    refine ⟨⟨LaurentPolynomial.C c, LinearMap.mem_ker.mpr (logarithmicDifferential_C c)⟩, ?_⟩
    change constantCoefficient (LaurentPolynomial.C c) = c
    simpa using constantCoefficient_C_mul_T c 0

@[simp] theorem algebraicDeRhamH0Equiv_apply
    (f : LaurentRing) (hf : logarithmicDifferential f = 0) :
    algebraicDeRhamH0Equiv ⟨f, hf⟩ = constantCoefficient f := by
  change algebraicDeRhamH0Readout ⟨f, hf⟩ = _
  rfl

theorem algebraicDeRhamH0_normal_form (x : algebraicDeRhamH0) :
    let oneH0 : algebraicDeRhamH0 :=
      ⟨1, LinearMap.mem_ker.mpr (by
        simpa using logarithmicDifferential_C (1 : ℂ))⟩
    x = (algebraicDeRhamH0Equiv x) • oneH0 := by
  let oneH0 : algebraicDeRhamH0 :=
    ⟨1, LinearMap.mem_ker.mpr (by
      simpa using logarithmicDifferential_C (1 : ℂ))⟩
  change x = (algebraicDeRhamH0Equiv x) • oneH0
  have hone : algebraicDeRhamH0Equiv oneH0 = 1 := by
    dsimp [oneH0]
    change constantCoefficient (1 : LaurentRing) = 1
    simpa using constantCoefficient_C_mul_T (1 : ℂ) 0
  apply algebraicDeRhamH0Equiv.injective
  rw [map_smul, hone, smul_eq_mul, mul_one]

theorem constantCoefficient_logarithmicDifferential (f : LaurentRing) :
    constantCoefficient (logarithmicDifferential f) = 0 := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
      simp only [map_add, hf, hg, add_zero]
  | C_mul_T n c =>
      rw [← LaurentPolynomial.single_eq_C_mul_T,
        logarithmicDifferential_single, map_smul,
        constantCoefficient_single]
      by_cases h : n = 0 <;> simp [h]

theorem logarithmicDifferential_range_eq_constantCoefficient_ker :
    LinearMap.range logarithmicDifferential =
      LinearMap.ker constantCoefficient := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact LinearMap.mem_ker.mpr (constantCoefficient_logarithmicDifferential f)
  · intro f hf
    refine ⟨logarithmicPrimitive f, ?_⟩
    simp [logarithmicDifferential_primitive, LinearMap.mem_ker.mp hf]

theorem constantCoefficient_surjective : Function.Surjective constantCoefficient := by
  intro c
  refine ⟨LaurentPolynomial.C c, ?_⟩
  simpa using constantCoefficient_C_mul_T c 0

abbrev algebraicDeRhamH1 : Type :=
  LaurentRing ⧸ LinearMap.range logarithmicDifferential

noncomputable def algebraicDeRhamH1Equiv :
    algebraicDeRhamH1 ≃ₗ[ℂ] ℂ :=
  (Submodule.quotEquivOfEq _ _
      logarithmicDifferential_range_eq_constantCoefficient_ker).trans
    (constantCoefficient.quotKerEquivOfSurjective constantCoefficient_surjective)

@[simp] theorem algebraicDeRhamH1Equiv_mk (f : LaurentRing) :
    algebraicDeRhamH1Equiv (Submodule.Quotient.mk f) =
      constantCoefficient f := by
  simp [algebraicDeRhamH1Equiv]

theorem algebraicDeRhamH1_mk_eq_zero_iff (f : LaurentRing) :
    Submodule.Quotient.mk f = (0 : algebraicDeRhamH1) ↔
      constantCoefficient f = 0 := by
  constructor
  · intro h
    have h' := congrArg algebraicDeRhamH1Equiv h
    simpa using h'
  · intro h
    apply algebraicDeRhamH1Equiv.injective
    rw [algebraicDeRhamH1Equiv_mk, map_zero]
    exact h

theorem algebraicDeRhamH1_normal_form (x : algebraicDeRhamH1) :
    x = (algebraicDeRhamH1Equiv x) •
      Submodule.Quotient.mk (1 : LaurentRing) := by
  apply algebraicDeRhamH1Equiv.injective
  have hconst : constantCoefficient (1 : LaurentRing) = 1 := by
    simpa using constantCoefficient_C_mul_T (1 : ℂ) 0
  rw [map_smul, algebraicDeRhamH1Equiv_mk, hconst, smul_eq_mul, mul_one]

noncomputable def algebraicDeRhamH1WindingClass (n : ℤ) : algebraicDeRhamH1 :=
  (n : ℂ) • Submodule.Quotient.mk (1 : LaurentRing)

@[simp] theorem algebraicDeRhamH1Equiv_windingClass (n : ℤ) :
    algebraicDeRhamH1Equiv (algebraicDeRhamH1WindingClass n) = (n : ℂ) := by
  rw [algebraicDeRhamH1WindingClass, map_smul,
    algebraicDeRhamH1Equiv_mk]
  have hOne : constantCoefficient (1 : LaurentRing) = 1 := by
    simpa using constantCoefficient_C_mul_T (1 : ℂ) 0
  rw [hOne, smul_eq_mul, mul_one]

theorem algebraicDeRhamH1WindingClass_eq_zero_iff (n : ℤ) :
    algebraicDeRhamH1WindingClass n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have h' := congrArg algebraicDeRhamH1Equiv h
    have hc : (n : ℂ) = 0 := by
      simpa using h'
    exact_mod_cast hc
  · intro h
    subst n
    simp [algebraicDeRhamH1WindingClass]

noncomputable def inversion : LaurentRing ≃ₗ[ℂ] LaurentRing :=
  Finsupp.mapDomain.linearEquiv ℂ ℂ (Equiv.neg ℤ)

@[simp] theorem inversion_single (n : ℤ) (c : ℂ) :
    inversion (Finsupp.single n c) = Finsupp.single (-n) c := by
  change Finsupp.mapDomain (fun k : ℤ => -k) (Finsupp.single n c) = _
  rw [Finsupp.mapDomain_single]

@[simp] theorem inversion_T (n : ℤ) :
    inversion (LaurentPolynomial.T n) = LaurentPolynomial.T (-n) := by
  change inversion (Finsupp.single n (1 : ℂ)) = Finsupp.single (-n) 1
  exact inversion_single n 1

@[simp] theorem inversion_one : inversion (1 : LaurentRing) = 1 := by
  change inversion (Finsupp.single (0 : ℤ) (1 : ℂ)) = Finsupp.single 0 1
  exact inversion_single 0 1

theorem inversion_mul (f g : LaurentRing) :
    inversion (f * g) = inversion f * inversion g := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
      simp only [add_mul, map_add, hf, hg]
  | C_mul_T n c =>
      induction g using LaurentPolynomial.induction_on' with
      | add f g hf hg =>
          simp only [mul_add, map_add, hf, hg]
      | C_mul_T m d =>
          rw [← LaurentPolynomial.single_eq_C_mul_T,
            ← LaurentPolynomial.single_eq_C_mul_T,
            AddMonoidAlgebra.single_mul_single,
            inversion_single, inversion_single, inversion_single,
            AddMonoidAlgebra.single_mul_single]
          simp only [Int.neg_add]

noncomputable def inversionAlgEquiv : LaurentRing ≃ₐ[ℂ] LaurentRing :=
  AlgEquiv.ofLinearEquiv inversion inversion_one inversion_mul

@[simp] theorem inversionAlgEquiv_apply (f : LaurentRing) :
    inversionAlgEquiv f = inversion f :=
  rfl

@[simp] theorem inversion_involutive (f : LaurentRing) :
    inversion (inversion f) = f := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
      simp only [map_add, hf, hg]
  | C_mul_T n c =>
      rw [← LaurentPolynomial.single_eq_C_mul_T,
        inversion_single, inversion_single]
      simp only [neg_neg]

theorem inversion_logarithmicDifferential (f : LaurentRing) :
    logarithmicDifferential (inversion f) =
      -inversion (logarithmicDifferential f) := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
      simp only [map_add, hf, hg, neg_add]
  | C_mul_T n c =>
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      simp only [inversion_single, logarithmicDifferential_single, map_smul,
        Int.cast_neg, neg_smul]

noncomputable def algebraicDeRhamH0Inversion :
    algebraicDeRhamH0 →ₗ[ℂ] algebraicDeRhamH0 where
  toFun f :=
    ⟨inversion f.1, by
      change logarithmicDifferential (inversion f.1) = 0
      rw [inversion_logarithmicDifferential, f.2, map_zero, neg_zero]⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

@[simp] theorem algebraicDeRhamH0Inversion_apply
    (f : LaurentRing) (hf : logarithmicDifferential f = 0) :
    algebraicDeRhamH0Inversion ⟨f, hf⟩ =
      ⟨inversion f, by
        change logarithmicDifferential (inversion f) = 0
        rw [inversion_logarithmicDifferential, hf, map_zero, neg_zero]⟩ := rfl

theorem algebraicDeRhamH0Inversion_involutive :
    Function.Involutive algebraicDeRhamH0Inversion := by
  intro x
  apply Subtype.ext
  exact inversion_involutive x.1

noncomputable def algebraicDeRhamH0InversionEquiv :
    algebraicDeRhamH0 ≃ₗ[ℂ] algebraicDeRhamH0 :=
  LinearEquiv.ofInvolutive algebraicDeRhamH0Inversion
    algebraicDeRhamH0Inversion_involutive

theorem logarithmicDifferential_range_le_comap_inversion :
    LinearMap.range logarithmicDifferential ≤
      (LinearMap.range logarithmicDifferential).comap inversion.toLinearMap := by
  rintro _ ⟨f, rfl⟩
  refine ⟨-inversion f, ?_⟩
  rw [map_neg, inversion_logarithmicDifferential]
  simp

noncomputable def algebraicDeRhamH1Inversion :
    algebraicDeRhamH1 →ₗ[ℂ] algebraicDeRhamH1 :=
  (LinearMap.range logarithmicDifferential).mapQ
    (LinearMap.range logarithmicDifferential) inversion.toLinearMap
    logarithmicDifferential_range_le_comap_inversion

@[simp] theorem algebraicDeRhamH1Inversion_mk (f : LaurentRing) :
    algebraicDeRhamH1Inversion (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (inversion f) := by
  rfl

theorem algebraicDeRhamH1Inversion_involutive :
    Function.Involutive algebraicDeRhamH1Inversion := by
  intro x
  refine Submodule.Quotient.induction_on (LinearMap.range logarithmicDifferential)
    x ?_
  intro f
  simp [inversion_involutive]

noncomputable def algebraicDeRhamH1InversionEquiv :
    algebraicDeRhamH1 ≃ₗ[ℂ] algebraicDeRhamH1 :=
  LinearEquiv.ofInvolutive algebraicDeRhamH1Inversion
    algebraicDeRhamH1Inversion_involutive

noncomputable def algebraicDeRhamH1Pullback :
    algebraicDeRhamH1 →ₗ[ℂ] algebraicDeRhamH1 :=
  -algebraicDeRhamH1Inversion

@[simp] theorem algebraicDeRhamH1Pullback_mk (f : LaurentRing) :
    algebraicDeRhamH1Pullback (Submodule.Quotient.mk f) =
      -(Submodule.Quotient.mk (inversion f)) := by
  simp [algebraicDeRhamH1Pullback]

theorem algebraicDeRhamH1Pullback_involutive :
    Function.Involutive algebraicDeRhamH1Pullback := by
  intro x
  change -(algebraicDeRhamH1Inversion
    (-algebraicDeRhamH1Inversion x)) = x
  rw [map_neg, neg_neg, algebraicDeRhamH1Inversion_involutive]

noncomputable def algebraicDeRhamH1PullbackEquiv :
    algebraicDeRhamH1 ≃ₗ[ℂ] algebraicDeRhamH1 :=
  LinearEquiv.ofInvolutive algebraicDeRhamH1Pullback
    algebraicDeRhamH1Pullback_involutive

@[simp] theorem algebraicDeRhamH1PullbackEquiv_mk (f : LaurentRing) :
    algebraicDeRhamH1PullbackEquiv (Submodule.Quotient.mk f) =
      -(Submodule.Quotient.mk (inversion f)) := by
  rfl

theorem constantCoefficient_inversion (f : LaurentRing) :
    constantCoefficient (inversion f) = constantCoefficient f := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
      simp only [map_add, hf, hg]
  | C_mul_T n c =>
      rw [← LaurentPolynomial.single_eq_C_mul_T,
        inversion_single, constantCoefficient_single,
        constantCoefficient_single]
      by_cases h : n = 0 <;> simp [h]

theorem algebraicDeRhamH0Equiv_inversion (x : algebraicDeRhamH0) :
    algebraicDeRhamH0Equiv (algebraicDeRhamH0Inversion x) =
      algebraicDeRhamH0Equiv x := by
  obtain ⟨f, hf⟩ := x
  rw [algebraicDeRhamH0Inversion_apply]
  rw [algebraicDeRhamH0Equiv_apply]
  rw [algebraicDeRhamH0Equiv_apply]
  exact constantCoefficient_inversion f

theorem algebraicDeRhamH1Pullback_readout (f : LaurentRing) :
    algebraicDeRhamH1Equiv
        (algebraicDeRhamH1Pullback (Submodule.Quotient.mk f)) =
      -constantCoefficient f := by
  simp [algebraicDeRhamH1Pullback, constantCoefficient_inversion]

theorem algebraicDeRhamH1_logarithmicClass_readout :
    algebraicDeRhamH1Equiv (Submodule.Quotient.mk (1 : LaurentRing)) = 1 := by
  simpa using constantCoefficient_C_mul_T (1 : ℂ) 0

theorem algebraicDeRhamH1_eq_readout_smul_logarithmicClass
    (x : algebraicDeRhamH1) :
    x = algebraicDeRhamH1Equiv x •
      Submodule.Quotient.mk (1 : LaurentRing) := by
  apply algebraicDeRhamH1Equiv.injective
  rw [map_smul, algebraicDeRhamH1_logarithmicClass_readout]
  simp

theorem algebraicDeRhamH1Pullback_logarithmicClass :
    algebraicDeRhamH1Pullback (Submodule.Quotient.mk (1 : LaurentRing)) =
      -(Submodule.Quotient.mk (1 : LaurentRing)) := by
  rw [algebraicDeRhamH1Pullback_mk, inversion_one]

theorem algebraicDeRhamH1Pullback_windingClass (n : ℤ) :
    algebraicDeRhamH1Pullback (algebraicDeRhamH1WindingClass n) =
      algebraicDeRhamH1WindingClass (-n) := by
  unfold algebraicDeRhamH1WindingClass
  rw [map_smul, algebraicDeRhamH1Pullback_logarithmicClass,
    Int.cast_neg, neg_smul]
  simp only [smul_neg]

@[simp] theorem logarithmicDifferential_T (n : ℤ) :
    logarithmicDifferential (LaurentPolynomial.T n) =
      (n : ℂ) • LaurentPolynomial.T n := by
  rw [LaurentPolynomial.T, logarithmicDifferential_single]

theorem logarithmicDifferential_T_add (m n : ℤ) :
    logarithmicDifferential (LaurentPolynomial.T (m + n)) =
      logarithmicDifferential (LaurentPolynomial.T m) * LaurentPolynomial.T n +
        LaurentPolynomial.T m * logarithmicDifferential (LaurentPolynomial.T n) := by
  rw [logarithmicDifferential_T, logarithmicDifferential_T,
    logarithmicDifferential_T, LaurentPolynomial.T_add]
  simp only [Algebra.smul_def, Int.cast_add, map_add, add_mul, mul_assoc]
  ring

theorem logarithmicDifferential_T_sub (m n : ℤ) :
    logarithmicDifferential (LaurentPolynomial.T (m - n)) =
      logarithmicDifferential (LaurentPolynomial.T m) * LaurentPolynomial.T (-n) +
        LaurentPolynomial.T m * logarithmicDifferential (LaurentPolynomial.T (-n)) := by
  rw [logarithmicDifferential_T, logarithmicDifferential_T,
    logarithmicDifferential_T, LaurentPolynomial.T_sub]
  simp only [Algebra.smul_def, Int.cast_sub, Int.cast_neg, map_sub, map_neg,
    sub_mul, mul_assoc]
  ring

theorem logarithmicDifferential_T_pow (m : ℤ) (n : ℕ) :
    logarithmicDifferential (LaurentPolynomial.T m ^ n) =
      ((n : ℂ) * (m : ℂ)) • LaurentPolynomial.T m ^ n := by
  rw [LaurentPolynomial.T_pow, logarithmicDifferential_T]
  norm_cast

end InfoGeometry.Projective.PuncturedAffineLogDifferential
