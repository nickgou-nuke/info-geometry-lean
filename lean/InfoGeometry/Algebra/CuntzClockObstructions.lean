import InfoGeometry.Algebra.CuntzClifford22

/-!
# Exact scope obstructions for clock, commutant, and Cuntz constructions

These results do not identify a linear fundamental symmetry with Tomita's
antiunitary modular conjugation. A Weyl relation belongs inside one algebra,
not between mutually commuting invertible operators. The trace obstruction
uses only additivity and cyclicity, so it applies a fortiori to normalized
finite linear traces. It does not exclude KMS states or traces on subalgebras.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzClockObstructions

open scoped Matrix

section Clock

variable {A : Type*} [Ring A] [Algebra ℂ A]

omit [Algebra ℂ A] in
/-- Ordinary left and right multiplication commute by associativity.
Right multiplication is naturally a representation of the opposite algebra. -/
theorem left_right_commute (a b : A) :
    Function.Commute (fun x : A => a * x) (fun x : A => x * b) :=
  fun x => (mul_assoc a x b).symm

/-- The commutator of a Weyl pair has its exact scalar coefficient. -/
theorem clock_commutator (X Z : A) (q : ℂ) (h : Z * X = q • (X * Z)) :
    X * Z - Z * X = (1 - q) • (X * Z) := by
  rw [h, sub_smul, one_smul]

/-- Cubic clock relations are not Clifford anticommutation relations. -/
theorem clock_anticommutator (X Z : A) (q : ℂ) (h : Z * X = q • (X * Z)) :
    X * Z + Z * X = (1 + q) • (X * Z) := by
  rw [h, add_smul, one_smul]

/-- An invertible commuting Weyl pair has trivial Weyl scalar. -/
theorem commuting_clock_scalar_eq_one [Nontrivial A]
    (X Z : Aˣ) (q : ℂ)
    (hc : Commute (X : A) (Z : A))
    (hq : (Z : A) * (X : A) = q • ((X : A) * (Z : A))) : q = 1 := by
  have hp : (X : A) * (Z : A) = q • ((X : A) * (Z : A)) := hc.eq.trans hq
  have hh := congrArg (fun a : A => a * ((Z⁻¹ : Aˣ) : A) * ((X⁻¹ : Aˣ) : A)) hp
  have h1 : (1 : A) = q • (1 : A) := by
    simpa [smul_mul_assoc, mul_assoc] using hh
  apply (algebraMap ℂ A).injective
  simpa [Algebra.algebraMap_eq_smul_one] using h1.symm

/-- The proposed cross-commutant clock relation is impossible for nontrivial q. -/
theorem no_nontrivial_commuting_clock [Nontrivial A]
    (X Z : Aˣ) (q : ℂ) (hq : q ≠ 1) (hc : Commute (X : A) (Z : A)) :
    (Z : A) * (X : A) ≠ q • ((X : A) * (Z : A)) := by
  intro h
  exact hq (commuting_clock_scalar_eq_one X Z q hc h)

end Clock

open InfoGeometry.Algebra.CuntzClifford22
open InfoGeometry.Algebra.CuntzTensorQuotient

/-- The original block built from a single isometry. -/
def rawBlock : Block := !![0, cuntzS 2 0; cuntzSdag 2 0, 0]

/-- Its square contains a range projector, not an identity in both corners. -/
theorem rawBlock_square :
    rawBlock * rawBlock = !![e 0 0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawBlock, e, InfoGeometry.Algebra.CuntzMatrixUnits.E,
      Matrix.mul_apply, Fin.sum_univ_two, cuntz_isometry]

/-- The omitted range projection is nonzero in every nontrivial realization. -/
theorem other_range_nonzero (h1 : (1 : Coeff) ≠ 0) : e 1 1 ≠ 0 := by
  intro he
  have hh := congrArg (fun a : Coeff => cuntzSdag 2 1 * a * cuntzS 2 1) he
  apply h1
  simpa [e, InfoGeometry.Algebra.CuntzMatrixUnits.E, mul_assoc, cuntz_isometry] using hh

/-- A proper isometry cannot replace a square-one Clifford generator. -/
theorem rawBlock_square_ne_one (h1 : (1 : Coeff) ≠ 0) : rawBlock * rawBlock ≠ 1 := by
  intro h
  rw [rawBlock_square] at h
  have he : e 0 0 = 1 := by simpa using congrArg (fun B : Block => B 0 0) h
  have hh := congrArg (fun a : Coeff => e 1 1 * a) he
  apply other_range_nonzero h1
  simpa using hh.symm

/-- No normalized additive cyclic trace exists on the two-generator quotient. -/
theorem no_normalized_cyclic_trace
    (τ : Coeff →+ ℂ) (hcyc : ∀ a b, τ (a * b) = τ (b * a)) : τ 1 ≠ 1 := by
  intro hn
  have hdiag (i : Fin 2) : τ (e i i) = τ 1 := by
    change τ (cuntzS 2 i * cuntzSdag 2 i) = τ 1
    rw [hcyc, cuntz_isometry]
  have hsum := congrArg τ diagonal_sum
  rw [map_add, hdiag 0, hdiag 1, hn] at hsum
  norm_num at hsum

end InfoGeometry.Algebra.CuntzClockObstructions
