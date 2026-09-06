import InfoGeometry.Algebra.AlternativeDerivations
import InfoGeometry.Algebra.KingdonSplitOctonion

/-!
# Baez's `G₂` derivations in the native alternative-algebra owner

This module formalizes the final derivation formula in John C. Baez,
*The Octonions*, §4.1 (`node14.html`):

`D_{x,y}(z) = [[x,y],z] - 3 [x,y,z]`.

For the alternative Kingdon algebra, the operator is proved equal to the
standard multiplication-operator expression, proved to satisfy Leibniz, and
bundled as `NonAssocDerivation`.

The result specializes to the repository's real split-octonion Kingdon owner.
It does not identify the compact division-octonion automorphism group with the
real split form `G_{2(2)}`, nor with the finite Chevalley group `G₂(2)`.
-/

namespace InfoGeometry.Algebra.Kingdon.Algebra

open InfoGeometry.Algebra

universe u v
variable {R : Type u} {V : Type v}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable (B : LinearMap.BilinForm R V)

set_option pp.universes false in
set_option pp.all false in
/-- Baez's formula for the standard endomorphism of a Kingdon algebra. -/
theorem stanDerMap_apply_baez_formula
    (x y z : Algebra R V B) :
    stanDerMap (R := R) x y z =
      (x * y - y * x) * z - z * (x * y - y * x) -
        (3 : ℕ) • associator x y z := by
  change
    (x * (y * z) - y * (x * z)) +
      (x * (z * y) - (x * z) * y) +
      ((z * y) * x - (z * x) * y) = _
  have h12 := associator_swap12_native B x y z
  have h23 := associator_swap23_native B x y z
  have hzyx : associator z y x = -associator x y z := by
    calc
      associator z y x = -associator y z x := associator_swap12_native B z y x
      _ = -associator x y z := by
        congr 1
        calc
          associator y z x = -associator z y x := associator_swap12_native B y z x
          _ = associator z x y := by rw [associator_swap23_native B z y x]; simp
          _ = -associator x z y := associator_swap12_native B z x y
          _ = associator x y z := by rw [associator_swap23_native B x z y]; simp
  have hzxy : associator z x y = associator x y z := by
    calc
      associator z x y = -associator x z y := associator_swap12_native B z x y
      _ = associator x y z := by rw [associator_swap23_native B x z y]; simp
  simp only [associator_apply] at h12 h23 hzyx hzxy ⊢
  simp only [sub_mul, mul_sub]
  linear_combination (norm := abel) h12 - h23 + hzyx - hzxy

/-- The associator product identity underlying the standard-derivation theorem. -/
theorem associator_product_rule (x y a b : Algebra R V B) :
    associator x y (a * b) - associator x y a * b - a * associator x y b =
      -associator a b (x * y - y * x) := by
  have h1 := associator_teichmueller B x y a b
  have h2 := associator_teichmueller B x y b a
  have h3 := associator_teichmueller B y x b a
  have h4 := associator_teichmueller B y a x b
  have h5 := associator_teichmueller B a x y b
  have cyc (p q r : Algebra R V B) : associator p q r = associator q r p := by
    calc
      associator p q r = -associator q p r := associator_swap12_native B p q r
      _ = associator q r p := by rw [associator_swap23_native B q p r]; simp
  have cyc2 (p q r : Algebra R V B) : associator p q r = associator r p q := by
    rw [cyc p q r, cyc q r p]
  have rev (p q r : Algebra R V B) : associator p q r = -associator r q p := by
    rw [associator_swap23_native B p q r, cyc p r q]
  rw [cyc y a b, cyc x (y * a) b, cyc2 x y (a * b), cyc2 x y a] at h1
  rw [rev y b a, rev (x * y) b a, cyc2 a b (x * y), cyc x (y * b) a,
    cyc2 x y (b * a), cyc2 x y b] at h2
  rw [rev x b a, rev (y * x) b a, cyc2 a b (y * x), cyc y (x * b) a,
    rev y x (b * a), rev y x b] at h3
  rw [rev a x b, cyc2 b x a, rev (y * a) x b, cyc2 b x (y * a),
    cyc y (a * x) b, rev y a (x * b), cyc y a x] at h4
  rw [cyc2 x y b, rev (a * x) y b, cyc2 b y (a * x), rev a (x * y) b,
    cyc b (x * y) a, cyc2 a x (y * b)] at h5
  have hsub : associator a b (x * y - y * x) =
      associator a b (x * y) - associator a b (y * x) := by
    simp only [associator_apply, mul_sub]
    abel
  rw [hsub, cyc2 x y (a * b), cyc2 x y a, cyc2 x y b,
    cyc2 a b (x * y), cyc2 a b (y * x)]
  rw [sub_eq_add_neg]
  have hcancel₁ :
      x * associator a b y + x * (-associator a b y) = 0 := by
    rw [← mul_add, add_neg_cancel, mul_zero]
  have hcancel₂ :
      associator b x y * a + (-associator b x y) * a = 0 := by
    rw [← add_mul, add_neg_cancel, zero_mul]
  linear_combination (norm := abel)
    -h1 - h2 - h3 + h4 - h5 + hcancel₁ + hcancel₂

/-- Baez's standard operator satisfies Leibniz on the alternative Kingdon algebra. -/
theorem stanDerMap_leibniz
    (x y a b : Algebra R V B) :
    stanDerMap (R := R) x y (a * b) =
      stanDerMap (R := R) x y a * b +
        a * stanDerMap (R := R) x y b := by
  let c : Algebra R V B := x * y - y * x
  let Axy : Algebra R V B → Algebra R V B := fun z => associator x y z
  have hcyc (p q r : Algebra R V B) :
      associator p q r = associator q r p := by
    calc
      associator p q r = -associator q p r := associator_swap12_native B p q r
      _ = associator q r p := by
        rw [associator_swap23_native B q p r]
        simp
  have hcomm :
      c * (a * b) - (a * b) * c -
          ((c * a - a * c) * b + a * (c * b - b * c)) =
        -(associator a b c + associator a b c + associator a b c) := by
    have hraw :
        c * (a * b) - (a * b) * c -
            ((c * a - a * c) * b + a * (c * b - b * c)) =
          -associator c a b + associator a c b - associator a b c := by
      simp only [associator_apply, sub_mul, mul_sub]
      abel
    rw [hcyc c a b, associator_swap23_native B a c b] at hraw
    rw [hraw]
    abel
  have hassoc := associator_product_rule B x y a b
  rw [stanDerMap_apply_baez_formula B x y (a * b),
    stanDerMap_apply_baez_formula B x y a,
    stanDerMap_apply_baez_formula B x y b]
  change
    c * (a * b) - (a * b) * c - (3 : ℕ) • Axy (a * b) =
      (c * a - a * c - (3 : ℕ) • Axy a) * b +
        a * (c * b - b * c - (3 : ℕ) • Axy b)
  dsimp [c, Axy] at hcomm hassoc ⊢
  have hleft (z : Algebra R V B) :
      ((3 : ℕ) • z) * b = (3 : ℕ) • (z * b) := by
    exact map_nsmul (R_map (R := R) b) 3 z
  have hright (z : Algebra R V B) :
      a * ((3 : ℕ) • z) = (3 : ℕ) • (a * z) := by
    exact map_nsmul (L_map (R := R) a) 3 z
  simp only [sub_mul, mul_sub, hleft, hright] at hcomm hassoc ⊢
  linear_combination (norm := abel) hcomm - hassoc - hassoc - hassoc

/-- The bundled native derivation defined by Baez's formula. -/
noncomputable def baezDerivation
    (x y : Algebra R V B) :
    NonAssocDerivation R (Algebra R V B) where
  toLinearMap := stanDerMap (R := R) x y
  leibniz' := stanDerMap_leibniz B x y

@[simp] theorem baezDerivation_apply
    (x y z : Algebra R V B) :
    baezDerivation B x y z =
      (x * y - y * x) * z - z * (x * y - y * x) -
        (3 : ℕ) • associator x y z :=
  stanDerMap_apply_baez_formula B x y z

end InfoGeometry.Algebra.Kingdon.Algebra

namespace InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Kingdon

/-- Baez's derivation on the repository's eight-dimensional real split-octonion
Kingdon owner. -/
noncomputable def baezSplitDerivation
    (x y : AbstractKingdon) : NonAssocDerivation ℝ AbstractKingdon :=
  Algebra.baezDerivation formedBilin x y

@[simp] theorem baezSplitDerivation_apply
    (x y z : AbstractKingdon) :
    baezSplitDerivation x y z =
      (x * y - y * x) * z - z * (x * y - y * x) -
        (3 : ℕ) • associator x y z :=
  Algebra.baezDerivation_apply formedBilin x y z

end InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion
