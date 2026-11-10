/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CliffordBraidingInterfaces
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# Ordered Majorana quartic interaction

Four generators from the existing `MajoranaSystem` interface determine an
ordered quartic involution. If the generators are self-adjoint, the quartic
is self-adjoint. An operator anticommuting with every generator commutes with
the quartic and its centrally scaled Hamiltonian.

The native algebraic spectrum of `H = -g • (γ₀ γ₁ γ₂ γ₃)` is contained in
`{g, -g}`. This is an algebraic consequence of `H² = g² • 1`; neither the
existence nor the multiplicity of either spectral value is asserted here.
There is no claim of a phase transition, a topological invariant, or a
many-body gap for a sum of interactions.
-/

namespace InfoGeometry.Algebra.MajoranaQuartic

variable {A : Type*} [Ring A]

/-- Four Majorana generators multiplied in the fixed order `0, 1, 2, 3`. -/
def quartet (s : MajoranaSystem 4 A) : A :=
  (s.gamma 0 * s.gamma 1) * (s.gamma 2 * s.gamma 3)

private theorem commute_pair_of_anticommute {p a b : A}
    (ha : p * a = -(a * p)) (hb : p * b = -(b * p)) :
    Commute p (a * b) := by
  change p * (a * b) = (a * b) * p
  calc
    p * (a * b) = (p * a) * b := (mul_assoc p a b).symm
    _ = (-(a * p)) * b := by rw [ha]
    _ = -(a * (p * b)) := by rw [neg_mul, mul_assoc]
    _ = -(a * (-(b * p))) := by rw [hb]
    _ = (a * b) * p := by rw [mul_neg, neg_neg, mul_assoc]

private theorem gamma_commute_pair (s : MajoranaSystem 4 A)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) :
    Commute (s.gamma i) (s.gamma j * s.gamma k) :=
  commute_pair_of_anticommute (s.anti_comm i j hij) (s.anti_comm i k hik)

private theorem disjoint_pairs_commute (s : MajoranaSystem 4 A) :
    Commute (s.gamma 0 * s.gamma 1) (s.gamma 2 * s.gamma 3) :=
  (gamma_commute_pair s 0 2 3 (by decide) (by decide)).mul_left
    (gamma_commute_pair s 1 2 3 (by decide) (by decide))

private theorem pair_square (s : MajoranaSystem 4 A) (i j : Fin 4)
    (hij : i ≠ j) : (s.gamma i * s.gamma j) ^ 2 = -1 := by
  calc
    (s.gamma i * s.gamma j) ^ 2 =
        s.gamma i * (s.gamma j * s.gamma i) * s.gamma j := by
      simp only [pow_two, mul_assoc]
    _ = s.gamma i * (-(s.gamma i * s.gamma j)) * s.gamma j := by
      rw [s.anti_comm j i hij.symm]
    _ = -1 := by
      simp only [mul_neg, neg_mul, ← mul_assoc, s.square_one i,
        one_mul, s.square_one j]

/-- Six anticommuting swaps give the positive square of the ordered quartet. -/
theorem quartet_sq (s : MajoranaSystem 4 A) : quartet s ^ 2 = 1 := by
  rw [quartet, (disjoint_pairs_commute s).mul_pow,
    pair_square s 0 1 (by decide), pair_square s 2 3 (by decide)]
  simp only [neg_mul_neg, one_mul]

private theorem pair_anticommute_left {a b : A} (hba : b * a = -(a * b)) :
    (a * b) * a = -(a * (a * b)) := by
  rw [mul_assoc, hba, mul_neg]

private theorem pair_anticommute_right {a b : A} (hba : b * a = -(a * b)) :
    (a * b) * b = -(b * (a * b)) := by
  rw [← mul_assoc b a b, hba, neg_mul, neg_neg]

private theorem mul_anticommute_of_anticommute_commute {a b p : A}
    (ha : a * p = -(p * a)) (hb : Commute b p) :
    (a * b) * p = -(p * (a * b)) := by
  calc
    (a * b) * p = a * (b * p) := mul_assoc a b p
    _ = a * (p * b) := by rw [hb.eq]
    _ = (a * p) * b := (mul_assoc a p b).symm
    _ = (-(p * a)) * b := by rw [ha]
    _ = -(p * (a * b)) := by rw [neg_mul, mul_assoc]

private theorem mul_anticommute_of_commute_anticommute {a b p : A}
    (ha : Commute a p) (hb : b * p = -(p * b)) :
    (a * b) * p = -(p * (a * b)) := by
  calc
    (a * b) * p = a * (b * p) := mul_assoc a b p
    _ = a * (-(p * b)) := by rw [hb]
    _ = -((a * p) * b) := by rw [mul_neg, mul_assoc]
    _ = -((p * a) * b) := by rw [ha.eq]
    _ = -(p * (a * b)) := by rw [mul_assoc]

/-- The even quartic is odd under conjugation by any one of its four generators. -/
theorem quartet_anticommute_gamma (s : MajoranaSystem 4 A) (i : Fin 4) :
    quartet s * s.gamma i = -(s.gamma i * quartet s) := by
  fin_cases i
  · exact mul_anticommute_of_anticommute_commute
      (pair_anticommute_left (s.anti_comm 1 0 (by decide)))
      (gamma_commute_pair s 0 2 3 (by decide) (by decide)).symm
  · exact mul_anticommute_of_anticommute_commute
      (pair_anticommute_right (s.anti_comm 1 0 (by decide)))
      (gamma_commute_pair s 1 2 3 (by decide) (by decide)).symm
  · exact mul_anticommute_of_commute_anticommute
      (gamma_commute_pair s 2 0 1 (by decide) (by decide)).symm
      (pair_anticommute_left (s.anti_comm 3 2 (by decide)))
  · exact mul_anticommute_of_commute_anticommute
      (gamma_commute_pair s 3 0 1 (by decide) (by decide)).symm
      (pair_anticommute_right (s.anti_comm 3 2 (by decide)))

/-- An operator odd against all four generators commutes with their quartet.
For a global parity operator, this is the algebraic conservation statement. -/
theorem commute_quartet_of_anticommute (s : MajoranaSystem 4 A) (p : A)
    (hp : ∀ i, p * s.gamma i = -(s.gamma i * p)) :
    Commute p (quartet s) :=
  (commute_pair_of_anticommute (hp 0) (hp 1)).mul_right
    (commute_pair_of_anticommute (hp 2) (hp 3))

/-- Reversal under star contributes six signs, so the quartet is self-adjoint. -/
theorem quartet_isSelfAdjoint [StarRing A] (s : MajoranaSystem 4 A)
    (hstar : ∀ i, IsSelfAdjoint (s.gamma i)) : IsSelfAdjoint (quartet s) := by
  change star (quartet s) = quartet s
  simp only [quartet, star_mul, (hstar 0).star_eq, (hstar 1).star_eq,
    (hstar 2).star_eq, (hstar 3).star_eq]
  rw [s.anti_comm 3 2 (by decide), s.anti_comm 1 0 (by decide), neg_mul_neg]
  exact (disjoint_pairs_commute s).symm.eq

section Hamiltonian

variable {K : Type*} [CommRing K] [Algebra K A]

/-- A single quartic interaction with central scalar coupling. -/
def hamiltonian (s : MajoranaSystem 4 A) (g : K) : A :=
  (-g) • quartet s

/-- The actual ordered operator, rather than a scalar surrogate, squares to `g²`. -/
theorem hamiltonian_sq (s : MajoranaSystem 4 A) (g : K) :
    hamiltonian s g ^ 2 = g ^ 2 • (1 : A) := by
  simp only [hamiltonian, smul_pow, neg_pow_two, quartet_sq]

/-- Central scalar scaling preserves the global parity commutator. -/
theorem commute_hamiltonian_of_anticommute (s : MajoranaSystem 4 A)
    (p : A) (hp : ∀ i, p * s.gamma i = -(s.gamma i * p)) (g : K) :
    Commute p (hamiltonian s g) := by
  change p * ((-g) • quartet s) = ((-g) • quartet s) * p
  rw [mul_smul_comm, smul_mul_assoc, (commute_quartet_of_anticommute s p hp).eq]

/-- Self-adjoint scalar couplings preserve self-adjointness. Real couplings
have this premise automatically under the standard star operation. -/
theorem hamiltonian_isSelfAdjoint [StarRing K] [StarRing A] [StarModule K A]
    (s : MajoranaSystem 4 A) (hstar : ∀ i, IsSelfAdjoint (s.gamma i))
    (g : K) (hg : IsSelfAdjoint g) : IsSelfAdjoint (hamiltonian s g) :=
  hg.neg.smul (quartet_isSelfAdjoint s hstar)

/-- Native algebraic spectral containment for the quartic interaction.
This asserts neither existence nor multiplicity of the two allowed values. -/
theorem hamiltonian_spectrum_subset {K : Type*} [Field K] [Algebra K A] [Nontrivial A]
    (s : MajoranaSystem 4 A) (g : K) :
    spectrum K (hamiltonian s g) ⊆ {g, -g} := by
  intro z hz
  have hzsq := spectrum.pow_mem_pow (hamiltonian s g) 2 hz
  rw [hamiltonian_sq, ← Algebra.algebraMap_eq_smul_one, spectrum.scalar_eq,
    Set.mem_singleton_iff] at hzsq
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
    (sq_eq_sq_iff_eq_or_eq_neg.mp hzsq)

end Hamiltonian

end InfoGeometry.Algebra.MajoranaQuartic
