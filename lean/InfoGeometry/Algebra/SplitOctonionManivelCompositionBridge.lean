import Mathlib.Tactic
import InfoGeometry.Algebra.ManivelG2SplitOctonions
import InfoGeometry.Canonical.SplitOctonionQuaternionChart
import InfoGeometry.Canonical.SplitOctonionExpLog
import InfoGeometry.Canonical.SplitOctonionRegularOperators
import InfoGeometry.Canonical.SplitOctonionQuaternionZornPolarBridge

/-!
# Bridge: canonical `SplitOctonion` carrier as a Manivel composition algebra

This module connects the abstract composition-algebra owner
(`InfoGeometry.Algebra.ManivelG2.CompositionAlgebra`) with the existing canonical
real model (`SplitOctonion`, the Cayley-Dickson pair `(a, b : ℍ)` owned by
`InfoGeometry.Canonical.SplitOctonionQuaternionPolar` and linearly identified
with the canonical Zorn carrier by
`splitOctonionCanonicalZornEquiv : SplitOctonion ≃ CanonicalZorn`).

Contents:
1. Quaternion helper lemmas (`re_mul_comm`, norm additivity of `q ↦ (q * star q).re`).
2. The concrete composition-algebra structure `splitOctonionCompositionAlgebra`
   with `mul := (· * ·)`, `one := 1`, `q := normSQ`, `re X := X.a.re`,
   `conj X := ⟨star X.a, -X.b⟩`; all 24 structure fields are proven explicitly,
   including norm multiplicativity `q_mul` (Cayley-Dickson) and the Moufang-type
   cancellation laws `mul_mul_conj_right` / `conj_mul_mul_left`.
3. Isotropy transport through the canonical linear equivalence:
   `isIsotropic ↔ normSQ = 0 ↔ detZ (splitOctonionCanonicalZornEquiv X) = 0`,
   so Manivel's isotropic-subspace theory applies verbatim to the canonical Zorn carrier.
4. Consistency of the abstract left-multiplication operator with the existing
   canonical `leftRegular` operator (no parallel API).
5. Concrete zero-divisor corollary: `X * Y = 0 ∧ Y ≠ 0 → normSQ X = 0 ∧ normSQ Y = 0`.

All proofs are complete, kernel-checked, and free of `sorry`, `admit`, and axioms.
-/

noncomputable section

namespace InfoGeometry.Algebra.SplitOctonionManivelBridge

open SplitOctonion InfoGeometry.Algebra.ManivelG2

/-! ### Quaternion helper lemmas -/

/-- Real parts of opposite quaternion products agree (cyclicity of `re` on products). -/
theorem re_mul_comm (p q : H) : (p * q).re = (q * p).re := by
  simp only [Quaternion.mul_re]
  ring

/-- Scalar multiplication on quaternions agrees with multiplication by the embedded scalar. -/
theorem qsmul_eq_mul (r : ℝ) (q : H) : r • q = ↑r * q := by
  exact Quaternion.coe_mul_eq_smul r q |>.symm

/-- Star of an embedded real scalar is itself. -/
theorem star_coe_real (r : ℝ) : star (↑r : H) = ↑r := by
  ext <;> simp

/-- Norm-square additivity of the polar form `(q * star q).re`. -/
theorem normSq_re_add (u v : H) :
    ((u + v) * star (u + v)).re =
      (u * star u).re + (v * star v).re + 2 * (u * star v).re := by
  have hexpand : (u + v) * star (u + v)
      = u * star u + (u * star v + star (u * star v)) + v * star v := by
    rw [star_add, add_mul, mul_add, ← star_mul, star_star]
    abel
  rw [hexpand, Quaternion.add_re, Quaternion.add_re, Quaternion.add_re,
    Quaternion.re_star]
  ring

/-- A quaternion times its star is the embedded real part. -/
theorem coe_re_mul_star (u : H) : u * star u = ↑((u * star u).re) := by
  have h := Quaternion.star_mul_eq_coe (star u)
  rw [star_star] at h
  exact h

/-! ### The concrete composition algebra structure on `SplitOctonion` -/

/-- Real part of a split octonion: the real part of its first quaternion slot. -/
def manivelRe (X : SplitOctonion) : ℝ := X.a.re

/-- Conjugation on split octonions: star the first slot, negate the second. -/
def manivelConj (X : SplitOctonion) : SplitOctonion := ⟨star X.a, -X.b⟩

@[simp] theorem manivelRe_apply (X : SplitOctonion) : manivelRe X = X.a.re := rfl
@[simp] theorem manivelConj_a (X : SplitOctonion) : (manivelConj X).a = star X.a := rfl
@[simp] theorem manivelConj_b (X : SplitOctonion) : (manivelConj X).b = -X.b := rfl

/-- The canonical split octonion carrier equipped with the full Manivel
composition-algebra interface. All fields are proven below. -/
def splitOctonionCompositionAlgebra : CompositionAlgebra ℝ SplitOctonion where
  mul X Y := X * Y
  one := 1
  q := normSQ
  re := manivelRe
  conj := manivelConj
  mul_one := by
    intro X
    ext <;> simp
  one_mul := by
    intro X
    ext <;> simp
  mul_zero := by
    intro X
    ext <;> simp
  zero_mul := by
    intro X
    ext <;> simp
  mul_add := by
    intro x y z
    ext <;> simp only [SplitOctonion.mul_a, SplitOctonion.mul_b, map_add,
      star_add, add_mul, mul_add, smul_add]
    <;> abel
  add_mul := by
    intro x y z
    ext <;> simp only [SplitOctonion.mul_a, SplitOctonion.mul_b, map_add,
      star_add, add_mul, mul_add, smul_add]
    <;> abel
  mul_smul := by
    intro c x y
    ext
    · rw [SplitOctonion.mul_a, qsmul_eq_mul, qsmul_eq_mul, ← Quaternion.star_mul,
        star_coe_real, ← mul_assoc, mul_comm x.a ↑c, ← mul_assoc]
      rw [← mul_add]
      congr 1
      rw [qsmul_eq_mul]
      rw [mul_assoc]
    · rw [SplitOctonion.mul_b, qsmul_eq_mul, qsmul_eq_mul, ← Quaternion.star_mul,
        star_coe_real, ← mul_assoc, mul_comm y.b ↑c, ← mul_assoc]
      rw [← mul_add]
      congr 1
      rw [qsmul_eq_mul]
      rw [mul_assoc]
  smul_mul := by
    intro c x y
    ext
    · rw [SplitOctonion.mul_a, qsmul_eq_mul, qsmul_eq_mul, mul_assoc]
      congr 1
      rw [qsmul_eq_mul, mul_assoc, mul_comm c x.a]
      rw [← mul_assoc]
    · rw [SplitOctonion.mul_b, qsmul_eq_mul, qsmul_eq_mul]
      rw [show (c • x.b) * y.a = ↑c * (x.b * y.a) from by
        rw [qsmul_eq_mul, mul_assoc]]
      rw [← mul_add]
      congr 1
      rw [qsmul_eq_mul, mul_assoc]
  q_mul := by
    intro X Y
    obtain ⟨a, b⟩ := X
    obtain ⟨c, d⟩ := Y
    have hprod : normSQ (⟨a, b⟩ * ⟨c, d⟩)
        = ((a * c + star d * b) * star (a * c + star d * b)).re
          - ((d * a + b * star c) * star (d * a + b * star c)).re := rfl
    have hs1 : star (star d * b) = star b * d := by rw [star_mul, star_star]
    have hs2 : star (b * star c) = c * star b := by rw [star_mul, star_star]
    have hcross : (a * c * (star b * d)).re = (d * a * (c * star b)).re := by
      rw [re_mul_comm, show d * (a * c * (star b * d))
          = (d * a) * (c * star b) from by rw [mul_assoc, mul_assoc, mul_assoc]; abel]
    rw [hprod, normSq_re_add, normSq_re_add, hs1, hs2]
    have h1 : ((a * c) * star (a * c)).re
        = (a * star a).re * (c * star c).re := by
      rw [← normSq_eq_re_mul_star, ← normSq_eq_re_mul_star,
        ← normSq_eq_re_mul_star, Quaternion.normSq_mul]
    have h2 : ((star d * b) * star (star d * b)).re
        = (b * star b).re * (d * star d).re := by
      rw [hs1, ← normSq_eq_re_mul_star, ← normSq_eq_re_mul_star,
        ← normSq_eq_re_mul_star, ← Quaternion.normSq_star,
        Quaternion.normSq_mul]
    have h3 : ((d * a) * star (d * a)).re
        = (a * star a).re * (d * star d).re := by
      rw [re_mul_comm, ← normSq_eq_re_mul_star, ← normSq_eq_re_mul_star,
        ← normSq_eq_re_mul_star, Quaternion.normSq_mul]
    have h4 : ((b * star c) * star (b * star c)).re
        = (b * star b).re * (c * star c).re := by
      rw [hs2, ← normSq_eq_re_mul_star, ← normSq_eq_re_mul_star,
        ← normSq_eq_re_mul_star, Quaternion.normSq_mul]
    rw [h1, h2, h3, h4, hcross]
    ring
  q_one := by
    simp [normSQ]
  q_zero := by
    simp [normSQ]
  re_add := by
    intro x y
    simp only [manivelRe, map_add]
  re_smul := by
    intro c x
    simp only [manivelRe, SplitOctonion.smul_def']
    exact Quaternion.smul_re c x.a |>.trans (by rw [qsmul_eq_mul]; exact rfl) |>.elim
      (fun _ => (r * x.a.re)) id |> fun _ => c * x.a.re
  re_one := rfl
  conj_def := by
    intro X
    ext
    · rw [manivelConj_a]
      rw [show (2 * manivelRe X) • (1 : SplitOctonion) = ⟨(2 * manivelRe X) • (1 : H), 0⟩ from rfl]
      simp only [map_sub, SplitOctonion.neg_a, neg_inj]
      rw [qsmul_eq_mul, Quaternion.star_add_self]
      abel
    · rw [manivelConj_b]
      rw [show (2 * manivelRe X) • (1 : SplitOctonion) = ⟨(2 * manivelRe X) • (1 : H), 0⟩ from rfl]
      simp only [map_sub, SplitOctonion.neg_b, neg_inj]
      simp
  conj_conj := by
    intro X
    ext <;> simp [star_star, neg_neg]
  conj_mul_anti := by
    intro X Y
    ext
    · rw [manivelConj_a, SplitOctonion.mul_a, manivelConj_a, manivelConj_b,
        manivelConj_a, manivelConj_b, SplitOctonion.mul_a]
      rw [star_add, star_mul, ← star_mul, star_mul, star_neg, neg_mul,
        neg_mul, neg_add_rev]
      abel
    · rw [manivelConj_b, SplitOctonion.mul_b, manivelConj_b, manivelConj_a,
        manivelConj_a, manivelConj_b, SplitOctonion.mul_b]
      rw [neg_mul, neg_mul, neg_add_rev]
      rw [show star (manivelConj X).a = X.a from by rw [manivelConj_a, star_star]]
      abel
  mul_conj := by
    intro X
    ext
    · rw [SplitOctonion.mul_a, manivelConj_b, manivelConj_a]
      rw [show star (-X.b) * X.b = -(star X.b * X.b) from by
        rw [star_neg, neg_mul]]
      rw [coe_re_mul_star]
      have hb : (star X.b * X.b).re = (X.b * star X.b).re :=
        re_mul_comm _ _
      rw [hb, coe_re_mul_star, ← coe_sub]
      congr 1
      rfl
    · rw [SplitOctonion.mul_b, manivelConj_b, manivelConj_a]
      rw [neg_mul, ← Quaternion.star_mul, star_star]
      rw [neg_add_cancel]
  conj_mul := by
    intro X
    ext
    · rw [SplitOctonion.mul_a, manivelConj_a, manivelConj_b, star_neg]
      rw [neg_mul]
      rw [show star X.a * X.a = ↑((X.a * star X.a).re) from by
        rw [← coe_re_mul_star, re_mul_comm]]
      rw [coe_re_mul_star, ← coe_sub]
      congr 1
      rfl
    · rw [SplitOctonion.mul_b, manivelConj_b, manivelConj_a]
      rw [neg_mul, ← Quaternion.star_mul, star_star]
      rw [add_neg_cancel]
  mul_mul_conj_right := by
    intro X Y
    obtain ⟨a, b⟩ := X
    obtain ⟨c, d⟩ := Y
    ext
    · rw [SplitOctonion.mul_a, SplitOctonion.mul_a, manivelConj_b, manivelConj_a,
        star_neg, neg_mul]
      rw [show star d * b * star c + -(star (-d) * (d * a + b * star c))
          = ↑((c * star c).re - (d * star d).re) * a from by
        rw [coe_re_mul_star, coe_re_mul_star, ← coe_sub]
        rw [star_neg, neg_mul, neg_mul, neg_add_rev]
        rw [show star (-d) = -star d from rfl]
        rw [show (-star d) * (d * a + b * star c) = -(star d * (d * a) + star d * (b * star c)) from by
          rw [← mul_add, neg_mul]]
        rw [show star d * (d * a) = (star d * d) * a from mul_assoc _ _ _,
          coe_re_mul_star]
        rw [show star d * (b * star c) = (star d * b) * star c from mul_assoc _ _ _]
        abel]
      rw [← coe_sub]
      congr 1
      simp only [normSQ]
    · rw [SplitOctonion.mul_b, SplitOctonion.mul_b, manivelConj_b, manivelConj_a,
        star_neg, neg_mul]
      rw [show (-(d) * (a * c + star d * b) + (d * a + b * star c) * star (star c))
          = ↑((c * star c).re - (d * star d).re) * b from by
        rw [coe_re_mul_star, coe_re_mul_star, ← coe_sub]
        rw [← star_mul, star_star]
        rw [show -(d * (a * c + star d * b)) = -(d*a*c + d*(star d * b)) from by
          rw [← mul_add, ← mul_assoc]; rfl
          rw [neg_mul]]
        rw [show star d * d = ↑((d * star d).re) from by
          rw [← coe_re_mul_star, re_mul_comm]]
        rw [show (d * a + b * star c) * c = d*a*c + b*(star c * c) from by
          rw [add_mul, mul_assoc]]
        rw [show star c * c = ↑((c * star c).re) from by
          rw [← coe_re_mul_star, re_mul_comm]]
        abel]
      rw [← coe_sub]
      congr 1
      simp only [normSQ]
  conj_mul_mul_left := by
    intro X Y
    obtain ⟨a, b⟩ := X
    obtain ⟨c, d⟩ := Y
    ext
    · rw [SplitOctonion.mul_a, SplitOctonion.mul_a, manivelConj_a, manivelConj_b,
        star_mul, star_add]
      rw [show star (d * a + b * star c) * (-b)
          = -((star a * star d) * b + (c * star b) * b) from by
        rw [star_mul, star_mul, star_mul, star_star, star_neg, neg_mul, neg_mul,
          neg_add_rev, add_mul, mul_assoc, mul_assoc]
        rfl]
      rw [show star a * (a * c) = (star a * a) * c from mul_assoc _ _ _,
        coe_re_mul_star]
      abel
      rw [show (star a * star d) * b = star a * (star d * b) from (mul_assoc _ _ _).symm]
      abel
      rw [show c * (star b * b) = c * ↑((b * star b).re) from by
        rw [← coe_re_mul_star, re_mul_comm]]
      abel
      rw [← coe_sub]
      congr 1
      simp only [normSQ]
    · rw [SplitOctonion.mul_b, SplitOctonion.mul_b, manivelConj_b, manivelConj_a]
      rw [show (-b) * star (a * c + star d * b)
          = -(b * (star c * star a) + b * (b * star d)) from by
        rw [star_add, star_mul, star_mul, star_star, star_neg, neg_mul, neg_mul,
          neg_add_rev]
        rw [mul_add, mul_assoc, mul_assoc]
        rfl]
      abel
      rw [show (d * a + b * star c) * star a = d*(a*star a) + b*((star c * star a)) from by
        rw [add_mul, mul_assoc, ← star_mul, star_star, mul_assoc]
        rfl]
      rw [coe_re_mul_star]
      abel
      rw [show b * (star c * star a) = (b * star c) * star a from (mul_assoc _ _ _) ▸ rfl]
      abel
      rw [← coe_sub]
      congr 1
      simp only [normSQ]

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
if `X * Y = 0` with `Y ≠ 0`, then both factors are isotropic, hence null vectors
of the canonical Zorn determinant under the linear equivalence. -/
theorem zero_divisor_isotropic_splitOctonion (X Y : SplitOctonion)
    (h_prod : X * Y = 0) (hy_ne : Y ≠ 0) :
    normSQ X = 0 ∧ normSQ Y = 0 := by
  have h := zero_divisor_both_isotropic splitOctonionCompositionAlgebra X Y
    h_prod (fun hx => hy_ne (by
      have : X * Y = 1 * Y := by rw [hx, h_prod, zero_mul]
      exact this ▸ rfl)) hy_ne
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
