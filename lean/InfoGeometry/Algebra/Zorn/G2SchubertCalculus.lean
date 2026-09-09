import InfoGeometry.Algebra.Zorn.G2BruhatCardinalities
import InfoGeometry.Algebra.Zorn.G2CyclotomicPoincareFactorization
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Finite Schubert indexing data for the `G₂` Bruhat development

This owner deliberately records only finite indexing and coefficient data.  It
does not claim a Schubert ring, quantum cohomology, Gromov--Witten invariants,
Bruhat coverage, or associativity of any supplied multiplication table.
Those are separate theorem owners and require their own proof-producing input.
-/

namespace InfoGeometry.Algebra.Zorn.G2SchubertCalculus

abbrev SchubertBasisIndex := Fin 12
abbrev SchubertCoefficients := SchubertBasisIndex → ℤ

def schubertDegree (w : SchubertBasisIndex) : ℕ :=
  G2BruhatCardinalities.weylLength w

def schubertCellCardinality (q : ℕ) (w : SchubertBasisIndex) : ℕ :=
  q ^ schubertDegree w

theorem schubertCellCardinality_eq_bruhatCellSize (q : ℕ) (w : SchubertBasisIndex) :
    schubertCellCardinality q w = G2BruhatCardinalities.bruhatCellSize q w := by
  rfl

theorem schubertCellCardinality_sum_two :
    (∑ w : SchubertBasisIndex, schubertCellCardinality 2 w) = 189 := by
  simpa [schubertCellCardinality] using
    G2BruhatCardinalities.full_flag_coset_sum_189

def schubertBruhatWeight (q : ℕ) (w : SchubertBasisIndex) : ℕ :=
  64 * schubertCellCardinality q w

theorem schubertBruhatWeight_eq_bruhatCellWeight (q : ℕ) (w : SchubertBasisIndex) :
    schubertBruhatWeight q w =
      64 * G2BruhatCardinalities.bruhatCellSize q w := by
  rfl

theorem schubertBruhatWeight_sum_two :
    (∑ w : SchubertBasisIndex, schubertBruhatWeight 2 w) = 12096 := by
  simp only [schubertBruhatWeight]
  rw [← Finset.mul_sum]
  rw [schubertCellCardinality_sum_two]
  norm_num [schubertBruhatWeight]

structure SchubertDatum where
  coefficients : SchubertCoefficients

def schubertAdd (a b : SchubertCoefficients) : SchubertCoefficients :=
  fun i => a i + b i

/-- The coordinate vector of a Schubert index in the free coefficient module. -/
def schubertBasisVector (w : SchubertBasisIndex) : SchubertCoefficients :=
  Pi.single w 1

theorem schubertBasisVector_same (w : SchubertBasisIndex) :
    schubertBasisVector w w = 1 := by
  simp [schubertBasisVector]

theorem schubertBasisVector_ne {w v : SchubertBasisIndex} (h : w ≠ v) :
    schubertBasisVector w v = 0 := by
  simp [schubertBasisVector, h]

theorem schubertBasisVector_injective :
    Function.Injective schubertBasisVector := by
  intro w v h
  by_contra hne
  have hv := congrFun h w
  simp [schubertBasisVector, hne] at hv

theorem schubert_coefficients_eq_sum_basis (a : SchubertCoefficients) :
    (∑ w : SchubertBasisIndex, a w • schubertBasisVector w) = a := by
  classical
  funext v
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single v]
  · simp [schubertBasisVector]
  · intro b hb hne
    simp [schubertBasisVector, hne]
  · simp

theorem schubertBasisVector_apply (w v : SchubertBasisIndex) :
    schubertBasisVector w v = if w = v then 1 else 0 := by
  by_cases h : w = v
  · subst h
    simp [schubertBasisVector]
  · simp [schubertBasisVector, h]

theorem schubert_index_card : Fintype.card SchubertBasisIndex = 12 := by
  rfl

theorem schubertDegree_nonnegative (w : SchubertBasisIndex) :
    0 ≤ schubertDegree w := by
  exact Nat.zero_le _

theorem schubertAdd_apply (a b : SchubertCoefficients) (i : SchubertBasisIndex) :
    schubertAdd a b i = a i + b i := by
  rfl

/-! The finite Schubert indexing has the same Poincare enumerator as the
    certified Weyl-length owner.  This is an internal coefficient-level bridge;
    it does not assert a cup product or a geometric cell realization. -/

open Polynomial

noncomputable section

def schubertPoincarePolyZ : ℤ[X] :=
  ∑ w : SchubertBasisIndex, X ^ schubertDegree w

theorem schubertPoincarePolyZ_eval_two :
    schubertPoincarePolyZ.eval 2 = 189 := by
  simp [schubertPoincarePolyZ, schubertDegree,
    G2BruhatCardinalities.weylLength, Fin.sum_univ_succ]

theorem schubertPoincarePolyZ_eq_length_enumerator :
    schubertPoincarePolyZ =
      1 + 2 * X + 2 * X ^ 2 + 2 * X ^ 3 +
        2 * X ^ 4 + 2 * X ^ 5 + X ^ 6 := by
  classical
  simp [schubertPoincarePolyZ, schubertDegree,
    G2BruhatCardinalities.weylLength, Fin.sum_univ_succ]
  ring

end

/-! The following facts are the finite Weyl-indexing shadow of the Schubert
    decomposition.  They make no claim about a cup product or a quantum
    deformation: they only record the certified length distribution. -/

theorem schubert_degree_zero_card :
    (Finset.univ.filter (fun w : SchubertBasisIndex => schubertDegree w = 0)).card = 1 := by
  decide

theorem schubert_degree_one_card :
    (Finset.univ.filter (fun w : SchubertBasisIndex => schubertDegree w = 1)).card = 2 := by
  decide

theorem schubert_degree_two_card :
    (Finset.univ.filter (fun w : SchubertBasisIndex => schubertDegree w = 2)).card = 2 := by
  decide

theorem schubert_degree_three_card :
    (Finset.univ.filter (fun w : SchubertBasisIndex => schubertDegree w = 3)).card = 2 := by
  decide

theorem schubert_degree_four_card :
    (Finset.univ.filter (fun w : SchubertBasisIndex => schubertDegree w = 4)).card = 2 := by
  decide

theorem schubert_degree_five_card :
    (Finset.univ.filter (fun w : SchubertBasisIndex => schubertDegree w = 5)).card = 2 := by
  decide

theorem schubert_degree_six_card :
    (Finset.univ.filter (fun w : SchubertBasisIndex => schubertDegree w = 6)).card = 1 := by
  decide

theorem schubert_degree_card_sum :
    ∑ d : Fin 7,
      (Finset.univ.filter (fun w : SchubertBasisIndex => schubertDegree w = d)).card = 12 := by
  decide

/-! A future multiplication owner may consume this finite datum, but no
    multiplication law is asserted here. -/

end InfoGeometry.Algebra.Zorn.G2SchubertCalculus
