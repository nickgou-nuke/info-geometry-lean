import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupportStateLinear

/-!
# Algebra congruence of the finite-support GNS quotient

This continues the finite Lean reimplementation of AFP
`Gelfand_Naimark_Segal`.  The zero-inner equivalence is stable under the
algebra operations, so the quotient algebra operations are well-defined.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupportQuotientAlgebra

open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupport

variable {n : ℕ} (p : Fin n → Prop) [DecidablePred p]

/-- GNS equivalence: same active-support restriction. -/
def SameGNS (a b : Alg n) : Prop := restrict p a = restrict p b

theorem sameGNS_refl (a : Alg n) : SameGNS p a a := by
  rfl

theorem sameGNS_symm {a b : Alg n} (h : SameGNS p a b) : SameGNS p b a := by
  exact h.symm

theorem sameGNS_trans {a b c : Alg n} (hab : SameGNS p a b) (hbc : SameGNS p b c) :
    SameGNS p a c := by
  exact hab.trans hbc

/-- Equivalence is exactly nullity of the difference. -/
theorem sameGNS_iff_null_difference (a b : Alg n) :
    SameGNS p a b ↔ nullSubspace p (a - b) := by
  exact same_gns_iff_null_difference p a b

/-- Addition respects GNS equivalence. -/
theorem sameGNS_add {a a' b b' : Alg n}
    (ha : SameGNS p a a') (hb : SameGNS p b b') :
    SameGNS p (a + b) (a' + b') := by
  funext i
  have hai := congrFun ha i
  have hbi := congrFun hb i
  simp [restrict] at hai hbi ⊢
  rw [hai, hbi]

/-- Negation respects GNS equivalence. -/
theorem sameGNS_neg {a a' : Alg n} (ha : SameGNS p a a') :
    SameGNS p (-a) (-a') := by
  funext i
  have hai := congrFun ha i
  simp [restrict] at hai ⊢
  rw [hai]

/-- Scalar multiplication respects GNS equivalence. -/
theorem sameGNS_smul (c : ℂ) {a a' : Alg n} (ha : SameGNS p a a') :
    SameGNS p (c • a) (c • a') := by
  funext i
  have hai := congrFun ha i
  simp [restrict] at hai
  change c * a i.1 = c * a' i.1
  rw [hai]

/-- Pointwise multiplication respects GNS equivalence. -/
theorem sameGNS_mul {a a' b b' : Alg n}
    (ha : SameGNS p a a') (hb : SameGNS p b b') :
    SameGNS p (fun i => a i * b i) (fun i => a' i * b' i) := by
  funext i
  have hai := congrFun ha i
  have hbi := congrFun hb i
  simp [restrict] at hai hbi ⊢
  rw [hai, hbi]

/-- Involution respects GNS equivalence. -/
theorem sameGNS_involution {a a' : Alg n} (ha : SameGNS p a a') :
    SameGNS p (involution a) (involution a') := by
  funext i
  have hai := congrFun ha i
  simp [restrict, involution] at hai ⊢
  rw [hai]

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupportQuotientAlgebra
