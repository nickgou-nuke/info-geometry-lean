import Mathlib.Analysis.PSeries
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.SumPrimeReciprocals
import InfoGeometry.Canonical.VarlamovDiscreteSymmetry

/-!
# Bost-Connes Criticality

This owner file keeps only theorem-backed finite arithmetic and Varlamov
projector facts used by downstream Bost-Connes criticality modules.

The harmonic-series and prime-reciprocal divergence facts are imported directly
from mathlib.  The Varlamov projectors are constructed from the repository owner
`InfoGeometry.Canonical.VarlamovDiscreteSymmetry`.
-/

open Real

namespace InfoGeometry.Arithmetic.BostConnesCriticality

/-- Harmonic-series divergence in the normalization that removes the zero term. -/
lemma harmonic_series_diverges :
    ¬ Summable (fun (n : ℕ) => if n = 0 then 0 else (1 : ℝ) / (n : ℝ)) := by
  intro h
  exact Real.not_summable_one_div_natCast
    (h.congr (fun n => by
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn, one_div]))

/-- Mathlib's divergence theorem for reciprocals of primes. -/
theorem prime_reciprocal_series_diverges :
    ¬ Summable (fun p : Nat.Primes => (1 / (p : ℝ))) :=
  Nat.Primes.not_summable_one_div

/-- Diagonal eigenvalue model for `exp (-βH)` on the natural-number basis. -/
noncomputable def bc_eigenvalues (β : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (n : ℝ) ^ (-β)

lemma bc_eigenvalues_one_eq (n : ℕ) :
    bc_eigenvalues 1 n = if n = 0 then 0 else (1 : ℝ) / (n : ℝ) := by
  by_cases hn : n = 0
  · simp [bc_eigenvalues, hn]
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    simp [bc_eigenvalues, hn, Real.rpow_neg_one, one_div]

/-- At `β = 1`, the diagonal model is not summable. -/
lemma operator_not_trace_class_at_critical :
    ¬ Summable (bc_eigenvalues 1) := by
  intro h
  exact harmonic_series_diverges (h.congr (fun n => bc_eigenvalues_one_eq n))

lemma strict_contraction_on_non_vacuum (n : ℕ) (hn : n ≥ 2) :
    bc_eigenvalues 1 n ≤ 1 / 2 := by
  have hn0 : n ≠ 0 := by omega
  have h2n_nat : 2 ≤ n := hn
  have hpos : 0 < (2 : ℝ) := by norm_num
  have hle : (2 : ℝ) ≤ n := by exact_mod_cast h2n_nat
  rw [bc_eigenvalues_one_eq, if_neg hn0]
  exact one_div_le_one_div_of_le hpos hle

lemma vacuum_eigenvalue_one :
    bc_eigenvalues 1 1 = 1 := by
  simp [bc_eigenvalues, Real.rpow_neg_one]

open InfoGeometry.Canonical

/-- The positive Varlamov idempotent associated to the involution `W`. -/
noncomputable def e_plus (X : KreinDoubledAtom) : X →ₗ[ℝ] X :=
  (2 : ℝ)⁻¹ • (LinearMap.id + KreinDoubledAtom.varlamovW X)

/-- The negative Varlamov idempotent associated to the involution `W`. -/
noncomputable def e_minus (X : KreinDoubledAtom) : X →ₗ[ℝ] X :=
  (2 : ℝ)⁻¹ • (LinearMap.id - KreinDoubledAtom.varlamovW X)

lemma varlamovW_apply_apply (X : KreinDoubledAtom) (x : X) :
    KreinDoubledAtom.varlamovW X (KreinDoubledAtom.varlamovW X x) = x := by
  exact LinearMap.congr_fun (KreinDoubledAtom.varlamovW_sq X) x

lemma varlamov_idempotents_sum (X : KreinDoubledAtom) :
    e_plus X + e_minus X = LinearMap.id := by
  ext x
  simp [e_plus, e_minus]
  module

lemma varlamov_idempotents_diff (X : KreinDoubledAtom) :
    e_plus X - e_minus X = KreinDoubledAtom.varlamovW X := by
  ext x
  simp [e_plus, e_minus]
  module

lemma varlamov_e_plus_idempotent (X : KreinDoubledAtom) :
    (e_plus X).comp (e_plus X) = e_plus X := by
  ext x
  simp [e_plus, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    varlamovW_apply_apply]
  module

lemma varlamov_e_minus_idempotent (X : KreinDoubledAtom) :
    (e_minus X).comp (e_minus X) = e_minus X := by
  ext x
  simp [e_minus, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    varlamovW_apply_apply]
  module

end InfoGeometry.Arithmetic.BostConnesCriticality
