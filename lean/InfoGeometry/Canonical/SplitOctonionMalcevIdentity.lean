import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.AlternativeDerivations

/-!
# Synthetic Coordinate-Free Proof of the Malcev Identity for Split Octonions

In this module, we formalize the coordinate-free proof of the Malcev identity:
  `J(X, Y, [X, Z]) = [J(X, Y, Z), X]`
for any split-octonion vector matrix over an arbitrary commutative ring `R`.

The proof proceeds through the algebraic symmetries of the associator and commutator:
1. Symmetries of the associator: `associator_swap12`, `associator_swap23`, `associator_cycle`
   derived from left and right alternativity and flexibility.
2. Teichmüller 4-identity and the Bruck-Kleinfeld associator calculus:
   - `associator X Y (Z * X) = X * associator X Y Z`
   - `associator (X * Y) Z X = associator X Y Z * X`
   - `associator X Y (X * Z) = associator X Y Z * X`
3. Left-multiplication commutator identity:
   `associator X Y [X, Z] = [associator X Y Z, X]`
4. Jacobiator reduction:
   `commutatorJacobiator X Y Z` expresses linearly via permutations of `associator X Y Z`.
5. Combining these yields `malcevDefect X Y Z = zero` without coordinate expansions,
   without characteristic restrictions, and with minimal heartbeats.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

def malcevDefect (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  sub
    (commutatorJacobiator X Y (commutator X Z))
    (commutator (commutatorJacobiator X Y Z) X)

/-! ## 1. Associator algebraic symmetries -/

lemma associator_eq_sub_mul (X Y Z : ZornVectorMatrix R) :
    associator X Y Z = (X * Y) * Z - X * (Y * Z) := rfl

lemma associator_add_left (X Y Z W : ZornVectorMatrix R) :
    associator (X + Y) Z W = associator X Z W + associator Y Z W := by
  simp only [associator_eq_sub_mul, _root_.add_mul]
  abel

lemma associator_add_mid (X Y Z W : ZornVectorMatrix R) :
    associator X (Y + Z) W = associator X Y W + associator X Z W := by
  simp only [associator_eq_sub_mul, _root_.add_mul, _root_.mul_add]
  abel

lemma associator_add_right (X Y Z W : ZornVectorMatrix R) :
    associator X Y (Z + W) = associator X Y Z + associator X Y W := by
  simp only [associator_eq_sub_mul, _root_.mul_add]
  abel

lemma associator_sub_right (X Y Z W : ZornVectorMatrix R) :
    associator X Y (Z - W) = associator X Y Z - associator X Y W := by
  simp only [associator_eq_sub_mul, _root_.mul_sub]
  abel

lemma associator_left_alt (X Y : ZornVectorMatrix R) :
    associator X X Y = 0 := by
  have h := associator_left_alternative X Y
  exact h

lemma associator_right_alt (X Y : ZornVectorMatrix R) :
    associator X Y Y = 0 := by
  have h := associator_right_alternative X Y
  exact h

lemma associator_flex (X Y : ZornVectorMatrix R) :
    associator X Y X = 0 := by
  have h := associator_flexible X Y
  exact h

lemma associator_swap12 (X Y Z : ZornVectorMatrix R) :
    associator X Y Z = -associator Y X Z := by
  have h := associator_left_alt (X + Y) Z
  rw [associator_add_left, associator_add_mid,
    associator_add_mid, associator_left_alt,
    associator_left_alt] at h
  have h' : associator X Y Z + associator Y X Z = 0 := by
    abel_nf at h ⊢
    exact h
  exact eq_neg_of_add_eq_zero_left h'

lemma associator_swap23 (X Y Z : ZornVectorMatrix R) :
    associator X Y Z = -associator X Z Y := by
  have h := associator_right_alt X (Y + Z)
  rw [associator_add_mid, associator_add_right,
    associator_add_right, associator_right_alt,
    associator_right_alt] at h
  have h' : associator X Y Z + associator X Z Y = 0 := by
    abel_nf at h ⊢
    exact h
  exact eq_neg_of_add_eq_zero_left h'

lemma associator_cycle (X Y Z : ZornVectorMatrix R) :
    associator Y Z X = associator X Y Z := by
  rw [associator_swap23, associator_swap12]
  abel

/-! ## 2. Teichmüller identity and Bruck-Kleinfeld calculus -/

lemma teichmuller_ident (A B C D : ZornVectorMatrix R) :
    associator (A * B) C D - associator A (B * C) D +
      associator A B (C * D) - A * associator B C D -
      associator A B C * D = 0 := by
  simp only [associator_eq_sub_mul]
  noncomm_ring

lemma associator_right_product (X Y Z : ZornVectorMatrix R) :
    associator X Y (Z * X) = X * associator X Y Z := by
  have h1 := teichmuller_ident X X Y Z
  have h2 := teichmuller_ident X X Z Y
  have h3 := teichmuller_ident X Z X Y
  have e1 :
      associator (X * X) Y Z - associator X (X * Y) Z -
        X * associator X Y Z = 0 := by
    rw [associator_left_alt X (Y * Z),
      associator_left_alt X Y] at h1
    rw [show (0 : ZornVectorMatrix R) * Z = 0 from zero_mul Z] at h1
    simpa only [_root_.add_zero, _root_.sub_zero] using h1
  rw [associator_swap23 (X * X) Z Y,
    associator_swap23 X (X * Z) Y, associator_left_alt,
    associator_swap23 X Z Y, associator_left_alt] at h2
  have e2 :
      -associator (X * X) Y Z + associator X Y (X * Z) +
        X * associator X Y Z = 0 := by
    rw [show (0 : ZornVectorMatrix R) * Y = 0 from zero_mul Y] at h2
    simpa only [neg_neg, _root_.add_zero, _root_.sub_zero,
      _root_.mul_neg, sub_neg_eq_add] using h2
  have hfirst :
      associator (X * Z) X Y = associator X Y (X * Z) := by
    rw [associator_swap12, associator_swap23]
    abel
  have hcycle : associator Z X Y = associator X Y Z :=
    (associator_cycle Z X Y).symm
  rw [hfirst, associator_swap23 X (Z * X) Y,
    associator_swap23 X Z (X * Y), hcycle,
    associator_flex] at h3
  have e4 :
      associator X Y (X * Z) + associator X Y (Z * X) -
        associator X (X * Y) Z - X * associator X Y Z = 0 := by
    rw [show (0 : ZornVectorMatrix R) * Y = 0 from zero_mul Y] at h3
    simpa only [neg_neg, _root_.add_zero, _root_.sub_zero,
      _root_.mul_neg, sub_neg_eq_add] using h3
  have hs :
      (associator (X * X) Y Z - associator X (X * Y) Z -
          X * associator X Y Z) +
        (-associator (X * X) Y Z + associator X Y (X * Z) +
          X * associator X Y Z) = 0 := by
    rw [e1, e2, _root_.zero_add]
  have e3 : associator X Y (X * Z) = associator X (X * Y) Z := by
    have hz :
        associator X Y (X * Z) - associator X (X * Y) Z = 0 := by
      abel_nf at hs ⊢
      exact hs
    exact sub_eq_zero.mp hz
  rw [e3] at e4
  have hz : associator X Y (Z * X) - X * associator X Y Z = 0 := by
    abel_nf at e4 ⊢
    exact e4
  exact sub_eq_zero.mp hz

lemma associator_mul_right (X Y Z : ZornVectorMatrix R) :
    associator (X * Y) Z X = associator X Y Z * X := by
  have h := teichmuller_ident X Y Z X
  rw [associator_flex X (Y * Z),
    associator_right_product X Y Z, associator_cycle X Y Z] at h
  simp only [_root_.sub_zero] at h
  have hz : associator (X * Y) Z X - associator X Y Z * X = 0 := by
    abel_nf at h ⊢
    exact h
  exact sub_eq_zero.mp hz

lemma associator_left_product (X Y Z : ZornVectorMatrix R) :
    associator X Y (X * Z) = associator X Y Z * X := by
  have h1 := teichmuller_ident X X Y Z
  have h2 := teichmuller_ident X X Z Y
  rw [associator_left_alt X (Y * Z), associator_left_alt X Y] at h1
  rw [show (0 : ZornVectorMatrix R) * Z = 0 from zero_mul Z] at h1
  have e1 : associator (X * X) Y Z - associator X (X * Y) Z - X * associator X Y Z = 0 := by
    simpa only [_root_.add_zero, _root_.sub_zero] using h1
  rw [associator_swap23 (X * X) Z Y, associator_swap23 X (X * Z) Y,
    associator_left_alt, associator_swap23 X Z Y, associator_left_alt] at h2
  have e2 : -associator (X * X) Y Z + associator X Y (X * Z) + X * associator X Y Z = 0 := by
    rw [show (0 : ZornVectorMatrix R) * Y = 0 from zero_mul Y] at h2
    simpa only [neg_neg, _root_.add_zero, _root_.sub_zero, _root_.mul_neg, sub_neg_eq_add] using h2
  have hs : (associator (X * X) Y Z - associator X (X * Y) Z - X * associator X Y Z) +
    (-associator (X * X) Y Z + associator X Y (X * Z) + X * associator X Y Z) = 0 := by
    rw [e1, e2, _root_.zero_add]
  have e3 : associator X Y (X * Z) = associator X (X * Y) Z := by
    have hz : associator X Y (X * Z) - associator X (X * Y) Z = 0 := by
      abel_nf at hs ⊢
      exact hs
    exact sub_eq_zero.mp hz
  have hcyc : associator X (X * Y) Z = associator (X * Y) Z X := by
    rw [associator_swap12, associator_swap23]
    abel
  rw [e3, hcyc, associator_mul_right]

/-! ## 3. Commutator identities -/

lemma commutator_def' (A B : ZornVectorMatrix R) :
    commutator A B = A * B - B * A := rfl

lemma commutator_add_left' (A B C : ZornVectorMatrix R) :
    commutator (A + B) C = commutator A C + commutator B C := by
  simp only [commutator_def', _root_.add_mul, _root_.mul_add]
  abel

lemma commutator_sub_left' (A B C : ZornVectorMatrix R) :
    commutator (A - B) C = commutator A C - commutator B C := by
  simp only [commutator_def', _root_.sub_mul, _root_.mul_sub]
  abel

lemma commutator_neg_left' (A B : ZornVectorMatrix R) :
    commutator (-A) B = -commutator A B := by
  simp only [commutator_def', _root_.neg_mul, _root_.mul_neg]
  abel

lemma associator_commutator_right (X Y Z : ZornVectorMatrix R) :
    associator X Y (commutator X Z) = commutator (associator X Y Z) X := by
  change associator X Y (X * Z - Z * X) = (associator X Y Z) * X - X * (associator X Y Z)
  rw [associator_sub_right, associator_left_product, associator_right_product]

/-! ## 4. Jacobiator alternating normal form and Malcev identity -/

lemma commutatorJacobiator_normal_form (A B C : ZornVectorMatrix R) :
    commutatorJacobiator A B C =
      (-associator A B C - associator A B C - associator A B C) -
        (associator A B C + associator A B C + associator A B C) := by
  have h := commutatorJacobiator_eq_associator_alternating A B C
  have h1 : associator A C B = -associator A B C := associator_swap23 A C B
  have h2 : associator B A C = -associator A B C := associator_swap12 B A C
  have h4 : associator B C A = associator A B C := associator_cycle A B C
  have h5 : associator C A B = associator A B C := (associator_cycle B C A).trans h4
  have h3 : associator C B A = -associator A B C := by rw [associator_swap23 C B A, h5]
  change commutatorJacobiator A B C =
    (associator A C B + associator B A C + associator C B A) -
      (associator A B C + associator B C A + associator C A B) at h
  rw [h1, h2, h3, h4, h5] at h
  rw [h]
  abel

/-- The synthetic, coordinate-free proof of the Malcev identity for the split octonions.
    This replaces the brute-force component expansion and avoids `maxHeartbeats`. -/
theorem malcev_identity (X Y Z : ZornVectorMatrix R) :
    malcevDefect X Y Z = zero := by
  unfold malcevDefect
  have hL := commutatorJacobiator_normal_form X Y (commutator X Z)
  have hR := commutatorJacobiator_normal_form X Y Z
  change commutatorJacobiator X Y (commutator X Z) -
    commutator (commutatorJacobiator X Y Z) X = 0
  rw [hR]
  simp only [commutator_sub_left', commutator_add_left', commutator_neg_left']
  rw [hL]
  rw [associator_commutator_right]
  abel

end InfoGeometry.Algebra.ZornVectorMatrix
