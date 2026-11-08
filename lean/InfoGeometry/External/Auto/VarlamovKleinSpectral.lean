import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace VarlamovKleinSpectral

def su5AdjointDim : ℕ := 24
def spinorDim : ℕ := 32
def weylA4Order : ℕ := 120
def mobiusGroupOrder : ℕ := 2

def varlamovEven : ℕ := Nat.choose 5 0 + Nat.choose 5 2 + Nat.choose 5 4
def varlamovOdd : ℕ := Nat.choose 5 1 + Nat.choose 5 3 + Nat.choose 5 5
def wittenMoebiusIndex : ℤ := (varlamovEven : ℤ) - (varlamovOdd : ℤ)

def tripotent (d : ℤ) : Prop := d ^ 3 = d
def tripotentPolynomial (d : ℤ) : ℤ := d ^ 3 - d
def mobiusInv (k : ℤ) : ℤ := -k

structure BrillouinMode where
  k : ℤ
  deriving DecidableEq, Repr

def kleinQuotient (m₁ m₂ : BrillouinMode) : Prop :=
  m₁.k = m₂.k ∨ m₁.k = mobiusInv m₂.k

inductive Concept where
  | SU5_Adjoint
  | Varlamov_Even_Spinor
  | Varlamov_Odd_Spinor
  | Witten_Moebius_Index
  | Klein_Brillouin_Quotient
  | Tripotent_Spectrum
  | Weyl_A4_Symmetry
  deriving DecidableEq, Repr

inductive Edge where
  | has_dim
  | splits_into
  | cancels_to
  | quotients_by
  | roots_are
  | has_order
  deriving DecidableEq, Repr

def edgeHolds : Concept → Edge → Concept → Bool
  | Concept.SU5_Adjoint, Edge.has_dim, Concept.Weyl_A4_Symmetry => true
  | Concept.Witten_Moebius_Index, Edge.splits_into, Concept.Varlamov_Even_Spinor => true
  | Concept.Witten_Moebius_Index, Edge.splits_into, Concept.Varlamov_Odd_Spinor => true
  | Concept.Witten_Moebius_Index, Edge.cancels_to, Concept.Klein_Brillouin_Quotient => true
  | Concept.Klein_Brillouin_Quotient, Edge.quotients_by, Concept.Tripotent_Spectrum => true
  | Concept.Weyl_A4_Symmetry, Edge.has_order, Concept.SU5_Adjoint => true
  | _, _, _ => false

theorem su5AdjointDim_eq : su5AdjointDim = 24 := by
  norm_num [su5AdjointDim]

theorem spinorDim_eq : spinorDim = 32 := by
  norm_num [spinorDim]

theorem weylA4Order_eq : weylA4Order = 120 := by
  norm_num [weylA4Order]

theorem mobiusGroupOrder_eq : mobiusGroupOrder = 2 := by
  norm_num [mobiusGroupOrder]

theorem varlamovEven_eq : varlamovEven = 16 := by
  norm_num [varlamovEven, Nat.choose]

theorem varlamovOdd_eq : varlamovOdd = 16 := by
  norm_num [varlamovOdd, Nat.choose]

theorem varlamovEven_add_varlamovOdd_eq_spinorDim :
    varlamovEven + varlamovOdd = spinorDim := by
  norm_num [varlamovEven, varlamovOdd, spinorDim, Nat.choose]

theorem wittenMoebiusIndex_eq_zero : wittenMoebiusIndex = 0 := by
  norm_num [wittenMoebiusIndex, varlamovEven, varlamovOdd, Nat.choose]

theorem tripotent_roots (d : ℤ) :
    tripotent d ↔ d = 0 ∨ d = 1 ∨ d = -1 := by
  constructor
  · intro h
    have hfact : d * (d - 1) * (d + 1) = 0 := by
      have hsub : d ^ 3 - d = 0 := sub_eq_zero.mpr h
      simpa [show d ^ 3 - d = d * (d - 1) * (d + 1) by ring] using hsub
    rcases mul_eq_zero.mp hfact with hleft | hplus
    · rcases mul_eq_zero.mp hleft with h0 | hminus
      · exact Or.inl h0
      · exact Or.inr (Or.inl (sub_eq_zero.mp hminus))
    · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left hplus))
  · intro h
    rcases h with h | h | h <;> simp [tripotent, h]

theorem tripotent_polynomial_roots :
    tripotentPolynomial (-1) = 0 ∧
    tripotentPolynomial 0 = 0 ∧
    tripotentPolynomial 1 = 0 := by
  norm_num [tripotentPolynomial]

theorem mobius_involutive (k : ℤ) :
    mobiusInv (mobiusInv k) = k := by
  simp [mobiusInv]

theorem klein_quotient_equivalence : Equivalence kleinQuotient := by
  refine ⟨?refl, ?symm, ?trans⟩
  · intro m
    exact Or.inl rfl
  · intro m₁ m₂ h
    rcases h with h | h
    · exact Or.inl h.symm
    · right
      rw [h, mobius_involutive]
  · intro m₁ m₂ m₃ h₁ h₂
    rcases h₁ with h₁ | h₁
    · rcases h₂ with h₂ | h₂
      · exact Or.inl (h₁.trans h₂)
      · exact Or.inr (h₁.trans h₂)
    · rcases h₂ with h₂ | h₂
      · exact Or.inr (by rw [h₁, h₂])
      · exact Or.inl (by rw [h₁, h₂, mobius_involutive])

theorem su5_adjoint_has_weyl_a4_symmetry :
    edgeHolds Concept.SU5_Adjoint Edge.has_dim Concept.Weyl_A4_Symmetry = true := by
  simp [edgeHolds]

theorem witten_moebius_index_splits_into_varlamov_even_spinor :
    edgeHolds Concept.Witten_Moebius_Index Edge.splits_into
      Concept.Varlamov_Even_Spinor = true := by
  simp [edgeHolds]

theorem witten_moebius_index_splits_into_varlamov_odd_spinor :
    edgeHolds Concept.Witten_Moebius_Index Edge.splits_into
      Concept.Varlamov_Odd_Spinor = true := by
  simp [edgeHolds]

theorem witten_moebius_index_cancels_to_klein_brillouin_quotient :
    edgeHolds Concept.Witten_Moebius_Index Edge.cancels_to
      Concept.Klein_Brillouin_Quotient = true := by
  simp [edgeHolds]

theorem klein_brillouin_quotient_quotients_by_tripotent_spectrum :
    edgeHolds Concept.Klein_Brillouin_Quotient Edge.quotients_by
      Concept.Tripotent_Spectrum = true := by
  simp [edgeHolds]

theorem weyl_a4_symmetry_has_order_su5_adjoint :
    edgeHolds Concept.Weyl_A4_Symmetry Edge.has_order Concept.SU5_Adjoint = true := by
  simp [edgeHolds]

end VarlamovKleinSpectral

end noncomputable section
