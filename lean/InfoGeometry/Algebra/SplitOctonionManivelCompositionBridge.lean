import Mathlib.Tactic
import InfoGeometry.Algebra.ManivelG2SplitOctonions
import InfoGeometry.Canonical.SplitOctonionQuaternionChart
import InfoGeometry.Canonical.SplitOctonionExpLog
import InfoGeometry.Canonical.SplitOctonionRegularOperators
import InfoGeometry.Canonical.SplitOctonionQuaternionZornPolarBridge

/-!
# Bridge: canonical `SplitOctonion` carrier as a Manivel composition algebra

Connects the abstract composition-algebra owner
(`InfoGeometry.Algebra.ManivelG2.CompositionAlgebra`) with the existing canonical
real model (`SplitOctonion`, the Cayley-Dickson pair `(a, b : ℍ)`), and transports
isotropy through the canonical linear equivalence
`splitOctonionCanonicalZornEquiv : SplitOctonion ≃ CanonicalZorn`.

All algebraic identities were verified symbolically (exact rational CAS, 2000
trials) in `scratch/verify_split_octonion_manivel_cas.py` before implementation.

Proof style: peeling — component goals are held at the quaternion level via
`SplitOctonion.ext`, the outer split-octonion product is peeled by
`SplitOctonion.mul_a` / `SplitOctonion.mul_b`, quaternion products are peeled one
factor per `mul_assoc` step, embedded scalars are extracted by `coe_re_mul_star`,
and additive cancellation is closed by `abel`.
-/

noncomputable section

namespace InfoGeometry.Algebra.SplitOctonionManivelBridge

open SplitOctonion InfoGeometry.Algebra.ManivelG2
open InfoGeometry.Canonical.SplitOctonionQuaternionZornPolarBridge

/-! ### Quaternion peeling lemmas -/

/-- Real parts of opposite quaternion products agree (cyclicity of `re`). -/
theorem re_mul_comm (p q : Quaternion ℝ) : (p * q).re = (q * p).re := by
  simp only [Quaternion.re_mul]
  ring

/-- Scalar multiplication agrees with multiplication by the embedded scalar. -/
theorem qsmul_eq_mul (r : ℝ) (q : Quaternion ℝ) : r • q = ↑r * q :=
  (Quaternion.coe_mul_eq_smul r q).symm

/-- Star of an embedded real scalar is itself. -/
theorem star_coe_real (r : ℝ) : star (↑r : Quaternion ℝ) = ↑r := by
  ext <;> simp

/-- A quaternion times its star is the embedded real part. -/
theorem coe_re_mul_star (u : Quaternion ℝ) : u * star u = ↑((u * star u).re) := by
  have h := Quaternion.star_mul_eq_coe (star u)
  rw [star_star] at h
  exact h

/-- Peel lemma: star of `u * star v` is `v * star u`. -/
theorem star_mul_star (u v : Quaternion ℝ) : star (u * star v) = v * star u := by
  rw [star_mul, star_star]

/-- Star equals twice-real-minus-self (componentwise on quaternions). -/
theorem star_eq_two_re_sub (x : Quaternion ℝ) :
    star x = ↑(2 * x.re) - x := by
  ext <;> simp

/-- Multiplicativity of the quaternion norm-square (not provided by mathlib). -/
theorem normSq_mul_quat (p q : Quaternion ℝ) :
    Quaternion.normSq (p * q) = Quaternion.normSq p * Quaternion.normSq q := by
  simp only [Quaternion.normSq_def']
  simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul]
  ring

/-- Norm-square additivity of the polar form `(q * star q).re`. -/
theorem normSq_re_add (u v : Quaternion ℝ) :
    ((u + v) * star (u + v)).re =
      (u * star u).re + (v * star v).re + 2 * (u * star v).re := by
  have hexpand : (u + v) * star (u + v)
      = (u * star u + v * star u) + (u * star v + v * star v) := by
    rw [star_add, add_mul, mul_add, mul_add]
    abel
  have hvsu : (v * star u).re = (u * star v).re := by
    rw [← star_mul_star u v, Quaternion.re_star]
  rw [hexpand]
  simp only [Quaternion.re_add]
  rw [hvsu]
  ring

/-! ### The concrete composition algebra structure on `SplitOctonion` -/

/-- Real part of a split octonion: the real part of its first quaternion slot. -/
def manivelRe (X : SplitOctonion) : ℝ := X.a.re

/-- Conjugation on split octonions: star the first slot, negate the second. -/
def manivelConj (X : SplitOctonion) : SplitOctonion := ⟨star X.a, -X.b⟩

@[simp] theorem manivelRe_apply (X : SplitOctonion) : manivelRe X = X.a.re := rfl
@[simp] theorem manivelConj_a (X : SplitOctonion) : (manivelConj X).a = star X.a := rfl
@[simp] theorem manivelConj_b (X : SplitOctonion) : (manivelConj X).b = -X.b := rfl

/-- The canonical split octonion carrier equipped with the full Manivel
composition-algebra interface. All fields are proven by peeling. -/
def splitOctonionCompositionAlgebra : CompositionAlgebra ℝ SplitOctonion where
  mul X Y := X * Y
  one := 1
  q := normSQ
  re := manivelRe
  conj := manivelConj
  mul_one := by
    intro X
    apply SplitOctonion.ext
    · show X.a * 1 + star (0 : Quaternion ℝ) * X.b = X.a
      simp
    · show 0 * X.a + X.b * star (1 : Quaternion ℝ) = X.b
      simp
  one_mul := by
    intro X
    apply SplitOctonion.ext
    · show 1 * X.a + star X.b * 0 = X.a
      simp
    · show X.b * 1 + 0 * star X.a = X.b
      simp
  mul_zero := by
    intro X
    apply SplitOctonion.ext <;> simp
  zero_mul := by
    intro X
    apply SplitOctonion.ext <;> simp
  mul_add := by
    intro x y z
    apply SplitOctonion.ext <;>
      simp [mul_a, mul_b, add_a, add_b, star_add, add_mul, mul_add] <;> abel
  add_mul := by
    intro x y z
    apply SplitOctonion.ext <;>
      simp [mul_a, mul_b, add_a, add_b, star_add, add_mul, mul_add] <;> abel
  mul_smul := by
    intro c x y
    apply SplitOctonion.ext <;>
      simp [mul_a, mul_b, smul_a, smul_b, SplitOctonion.mul_smul,
        SplitOctonion.smul_mul, star_smul, star_coe_real, smul_add]
  smul_mul := by
    intro c x y
    apply SplitOctonion.ext <;>
      simp [mul_a, mul_b, smul_a, smul_b, SplitOctonion.mul_smul,
        SplitOctonion.smul_mul, star_smul, star_coe_real, smul_add]
  q_mul := by
    intro X Y
    obtain ⟨a, b⟩ := X
    obtain ⟨c, d⟩ := Y
    have hs1 : star (star d * b) = star b * d := by rw [star_mul, star_star]
    have hs2 : star (b * star c) = c * star b := star_mul_star b c
    have hcross : ((a * c) * (star b * d)).re = ((d * a) * (c * star b)).re := by
      rw [re_mul_comm, mul_assoc (star b) d (a * c),
        re_mul_comm (star b) (d * (a * c)),
        ← mul_assoc d a c, ← mul_assoc (d * a) c (star b)]
    have h1 : ((a * c) * star (a * c)).re
        = (a * star a).re * (c * star c).re := by
      rw [← normSq_eq_re_mul_star, ← normSq_eq_re_mul_star, ← normSq_eq_re_mul_star,
        normSq_mul_quat]
    have h2 : ((star d * b) * star (star d * b)).re
        = (b * star b).re * (d * star d).re := by
      rw [← normSq_eq_re_mul_star, normSq_mul_quat, Quaternion.normSq_star,
        mul_comm (Quaternion.normSq d) (Quaternion.normSq b),
        ← normSq_eq_re_mul_star, ← normSq_eq_re_mul_star]
    have h3 : ((d * a) * star (d * a)).re
        = (a * star a).re * (d * star d).re := by
      rw [← normSq_eq_re_mul_star, normSq_mul_quat, mul_comm,
        ← normSq_eq_re_mul_star, ← normSq_eq_re_mul_star]
    have h4 : ((b * star c) * star (b * star c)).re
        = (b * star b).re * (c * star c).re := by
      rw [← normSq_eq_re_mul_star, normSq_mul_quat, Quaternion.normSq_star,
        ← normSq_eq_re_mul_star, ← normSq_eq_re_mul_star]
    show normSQ (⟨a, b⟩ * ⟨c, d⟩) = normSQ ⟨a, b⟩ * normSQ ⟨c, d⟩
    simp only [normSQ, SplitOctonion.mul_a, SplitOctonion.mul_b]
    rw [normSq_re_add (a * c) (star d * b), normSq_re_add (d * a) (b * star c),
      h1, h2, h3, h4, hcross]
    ring
  q_one := by simp [normSQ]
  q_zero := by simp [normSQ]
  re_add := by
    intro x y
    simp only [manivelRe, SplitOctonion.add_a, Quaternion.re_add]
  re_smul := by
    intro c x
    simp only [manivelRe, SplitOctonion.smul_a, Quaternion.re_smul, smul_eq_mul]
  re_one := rfl
  conj_def := by
    intro X
    apply SplitOctonion.ext
    · show star X.a = (2 * X.a.re) • (1 : Quaternion ℝ) - X.a
      rw [qsmul_eq_mul, mul_one]
      exact star_eq_two_re_sub X.a
    · show -X.b = (2 * X.a.re) • (0 : Quaternion ℝ) - X.b
      simp
  conj_conj := by
    intro X
    apply SplitOctonion.ext <;> simp [star_star, neg_neg]
  conj_mul_anti := by
    intro X Y
    apply SplitOctonion.ext
    · show star (X.a * Y.a + star Y.b * X.b)
        = star Y.a * star X.a + star (-X.b) * (-Y.b)
      simp only [star_add, star_mul, star_neg, neg_mul, neg_neg, star_star]
      abel
    · show -(Y.b * X.a + X.b * star Y.a)
        = (-X.b) * star Y.a + (-Y.b) * star (star X.a)
      simp only [neg_add_rev, neg_mul, star_star]
      abel
  mul_conj := by
    intro X
    apply SplitOctonion.ext
    · show X.a * star X.a + star (-X.b) * X.b = normSQ X • (1 : Quaternion ℝ)
      rw [star_neg, neg_mul]
      rw [show star X.b * X.b = ↑((X.b * star X.b).re) from
        coe_re_mul_star' X.b]
      rw [coe_re_mul_star, ← sub_eq_add_neg, ← coe_sub, qsmul_eq_mul]
      congr 1
      rfl
    · show (-X.b) * X.a + X.b * star (star X.a) = normSQ X • (0 : Quaternion ℝ)
      rw [star_star, neg_mul, neg_add_cancel]
      simp
  conj_mul := by
    intro X
    apply SplitOctonion.ext
    · show star X.a * X.a + star X.b * (-X.b) = normSQ X • (1 : Quaternion ℝ)
      rw [neg_mul]
      rw [show star X.a * X.a = ↑((X.a * star X.a).re) from
        coe_re_mul_star' X.a]
      rw [show star X.b * X.b = ↑((X.b * star X.b).re) from
        coe_re_mul_star' X.b]
      rw [← sub_eq_add_neg, ← coe_sub, qsmul_eq_mul]
      congr 1
      rfl
    · show X.b * star X.a + (-X.b) * star X.a = normSQ X • (0 : Quaternion ℝ)
      rw [neg_mul, add_neg_cancel]
      simp
  mul_mul_conj_right := by
    intro X Y
    apply SplitOctonion.ext
    have e1 : (X.a * Y.a + star Y.b * X.b) * star Y.a
        = X.a * (Y.a * star Y.a) + star Y.b * (X.b * star Y.a) := by
      rw [add_mul, mul_assoc, mul_assoc]
    have e2 : star Y.b * (Y.b * X.a + X.b * star Y.a)
        = (star Y.b * Y.b) * X.a + star Y.b * (X.b * star Y.a) := by
      rw [mul_add, ← mul_assoc]
    have e3 : X.a * (Y.a * star Y.a) = X.a * ↑((Y.a * star Y.a).re) := by
      rw [coe_re_mul_star]
    have e4 : (star Y.b * Y.b) * X.a = ↑((Y.b * star Y.b).re) * X.a := by
      rw [show star Y.b * Y.b = ↑((Y.b * star Y.b).re) from
        coe_re_mul_star' Y.b]
    · show (X * Y).a * star Y.a + star (-Y.b) * (X * Y).b = normSQ Y • X.a
      rw [SplitOctonion.mul_a, SplitOctonion.mul_b, manivelConj_b, manivelConj_a,
        star_neg, neg_mul, e1, e2, e3, e4]
      abel
      rw [mul_comm X.a (↑((Y.a * star Y.a).re)), ← mul_sub, ← coe_sub, qsmul_eq_mul]
      congr 1
      rfl
    · show (-Y.b) * (X * Y).a + (X * Y).b * star (star Y.a) = normSQ Y • X.b
      rw [SplitOctonion.mul_a, SplitOctonion.mul_b, manivelConj_b, manivelConj_a,
        star_star]
      have f1 : (-Y.b) * (X.a * Y.a + star Y.b * X.b)
          = -(Y.b * X.a * Y.a) - ↑((Y.b * star Y.b).re) * X.b := by
        rw [mul_add, neg_mul, neg_mul, mul_assoc, mul_assoc,
          show Y.b * (star Y.b * X.b) = ↑((Y.b * star Y.b).re) * X.b from by
            rw [← mul_assoc, coe_re_mul_star]]
      have f2 : (Y.b * X.a + X.b * star Y.a) * star (star Y.a)
          = Y.b * X.a * Y.a + ↑((Y.a * star Y.a).re) * X.b := by
        rw [add_mul, mul_assoc, ← mul_assoc X.b (star Y.a) Y.a,
          show star Y.a * Y.a = ↑((Y.a * star Y.a).re) from
            coe_re_mul_star' Y.a]
      rw [f1, f2]
      abel
      rw [← mul_sub, ← coe_sub, qsmul_eq_mul]
      congr 1
      rfl
  conj_mul_mul_left := by
    intro X Y
    apply SplitOctonion.ext
    have hA : star X.a * (X.a * Y.a + star Y.b * X.b)
        = ↑((X.a * star X.a).re) * Y.a + (star X.a * star Y.b) * X.b := by
      rw [add_mul, mul_assoc,
        show star X.a * X.a = ↑((X.a * star X.a).re) from
          coe_re_mul_star' X.a,
        mul_assoc]
    have hB : star (Y.b * X.a + X.b * star Y.a) * (-X.b)
        = -((star X.a * star Y.b) * X.b) - ↑((X.b * star X.b).re) * Y.a := by
      rw [star_add, star_mul, mul_assoc, star_mul, star_star]
      rw [neg_mul, neg_mul, ← mul_assoc Y.a (star X.b) X.b,
        show star X.b * X.b = ↑((X.b * star X.b).re) from
          coe_re_mul_star' X.b,
        mul_comm Y.a (↑((X.b * star X.b).re))]
      abel
    · show star X.a * (X * Y).a + star (X * Y).b * (-X.b) = normSQ X • Y.a
      rw [SplitOctonion.mul_a, SplitOctonion.mul_b, manivelConj_b, hA, hB]
      abel
      rw [← mul_sub, ← coe_sub, qsmul_eq_mul]
      congr 1
      rfl
    · show (X * Y).b * star X.a + (-X.b) * star (X * Y).a = normSQ X • Y.b
      rw [SplitOctonion.mul_b, SplitOctonion.mul_a, manivelConj_b]
      rw [show star (X.a * Y.a + star Y.b * X.b)
          = star Y.a * star X.a + star X.b * Y.b from by
        rw [star_add, star_mul, star_mul, star_mul_star Y.b X.b]]
      rw [neg_mul, mul_assoc, ← mul_assoc, mul_assoc, mul_assoc]
      rw [show X.b * (star Y.a * star X.a) = (X.b * star Y.a) * star X.a from
        (mul_assoc X.b (star Y.a) (star X.a)).symm]
      abel
      rw [show Y.b * (X.a * star X.a) = Y.b * ↑((X.a * star X.a).re) from by
        rw [coe_re_mul_star]]
      rw [mul_comm Y.b (↑((X.a * star X.a).re)),
        show X.b * (star X.b * Y.b) = (X.b * star X.b) * Y.b from mul_assoc _ _ _,
        coe_re_mul_star]
      rw [← mul_sub, ← coe_sub, qsmul_eq_mul]
      congr 1
      rfl

@[simp] theorem splitOctonionCompositionAlgebra_q (X : SplitOctonion) :
    splitOctonionCompositionAlgebra.q X = normSQ X := rfl

@[simp] theorem splitOctonionCompositionAlgebra_mul (X Y : SplitOctonion) :
    splitOctonionCompositionAlgebra.mul X Y = X * Y := rfl

/-! ### Isotropy transport through the canonical linear equivalence -/

/-- Manivel isotropy on the canonical carrier is exactly vanishing of `normSQ`. -/
theorem isIsotropic_iff_normSQ (X : SplitOctonion) :
    splitOctonionCompositionAlgebra.isIsotropic X ↔ normSQ X = 0 := Iff.rfl

/-- **Main transport theorem**: Manivel isotropy on the canonical split-octonion
carrier coincides with vanishing of the Zorn determinant after the canonical
linear equivalence to the Zorn carrier. -/
theorem isIsotropic_iff_detZ (X : SplitOctonion) :
    splitOctonionCompositionAlgebra.isIsotropic X ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        (splitOctonionCanonicalZornEquiv X) = 0 := by
  rw [isIsotropic_iff_normSQ, splitOctonionCanonicalZornEquiv_norm]

/-- Concrete zero-divisor corollary (Manivel Lemma 2.3.9 on the canonical carrier):
if `X * Y = 0` with `X ≠ 0` and `Y ≠ 0`, then both factors are isotropic, hence
null vectors of the canonical Zorn determinant under the linear equivalence. -/
theorem zero_divisor_isotropic_splitOctonion (X Y : SplitOctonion)
    (h_prod : X * Y = 0) (hx_ne : X ≠ 0) (hy_ne : Y ≠ 0) :
    normSQ X = 0 ∧ normSQ Y = 0 := by
  have h := zero_divisor_both_isotropic splitOctonionCompositionAlgebra X Y
    h_prod hx_ne hy_ne
  exact ⟨h.1, h.2⟩

/-! ### Consistency with the canonical regular-operator API -/

/-- The abstract left-multiplication operator of the Manivel interface coincides
with the pre-existing canonical `leftRegular` operator: no parallel API. -/
theorem mulLeftLinear_eq_leftRegular (X : SplitOctonion) :
    CompositionAlgebra.mulLeftLinear splitOctonionCompositionAlgebra X
      = leftRegular X := by
  funext y
  simp [CompositionAlgebra.mulLeftLinear]

end InfoGeometry.Algebra.SplitOctonionManivelBridge
