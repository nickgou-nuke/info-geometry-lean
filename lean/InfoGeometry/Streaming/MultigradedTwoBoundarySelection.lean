import InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

/-!
# Multigraded two-boundary selection rules

A normalized two-boundary matrix coefficient does not by itself define a
current.  It does, however, obey an exact weight-selection theorem whenever
the pre-boundary vector, post-boundary covector, and probed operator are
homogeneous for a commuting family of grading operators.

No positivity, unitarity, time evolution, or physical measurement model is
assumed.
-/

noncomputable section

namespace InfoGeometry.Streaming.MultigradedTwoBoundarySelection

open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

variable {ι 𝔞 : Type*} [Fintype ι]

abbrev State := FiniteTwoBoundaryWeakFunctional.State ι
abbrev Operator := FiniteTwoBoundaryWeakFunctional.Operator ι
abbrev BoundaryPair := RegularBoundaryPair ι

/-- Right weight of a vector for a family of grading operators. -/
def IsRightWeight (H : 𝔞 → Operator) (α : 𝔞 → ℂ) (v : State) : Prop :=
  ∀ a, H a v = α a • v

/-- Left weight expressed directly through the Dirac pairing.  This avoids
silently assuming that the grading operators are self-adjoint. -/
def IsLeftWeight (H : 𝔞 → Operator) (β : 𝔞 → ℂ) (post : State) : Prop :=
  ∀ a x, pairing post (H a x) = β a * pairing post x

/-- Adjoint weight of an operator: `[Hₐ,A]=μₐ A`. -/
def IsOperatorMultiweight
    (H : 𝔞 → Operator) (μ : 𝔞 → ℂ) (A : Operator) : Prop :=
  ∀ a, H a * A - A * H a = μ a • A

/-- Weight difference selected by a left/right boundary pair. -/
def boundaryWeightDifference (α β : 𝔞 → ℂ) : 𝔞 → ℂ :=
  fun a => β a - α a

/-- Pairing the operator weight equation with homogeneous boundaries gives the
scalar selection identity `(βₐ-αₐ-μₐ) <post|A|pre> = 0`. -/
theorem numerator_weight_equation
    (p : BoundaryPair) (H : 𝔞 → Operator)
    (α β μ : 𝔞 → ℂ) (A : Operator)
    (hpre : IsRightWeight H α p.pre)
    (hpost : IsLeftWeight H β p.post)
    (hA : IsOperatorMultiweight H μ A)
    (a : 𝔞) :
    (β a - α a - μ a) * numerator p A = 0 := by
  have hcomm := congrArg
    (fun T : Operator => pairing p.post (T p.pre)) (hA a)
  have hleft : pairing p.post (H a (A p.pre)) =
      β a * pairing p.post (A p.pre) := hpost a (A p.pre)
  have hright : pairing p.post (A (H a p.pre)) =
      α a * pairing p.post (A p.pre) := by
    rw [hpre a, A.map_smul, pairing_smul_right]
  have hscaled : pairing p.post ((μ a • A) p.pre) =
      μ a * pairing p.post (A p.pre) := by
    simp [pairing_smul_right]
  have heq :
      β a * pairing p.post (A p.pre) -
          α a * pairing p.post (A p.pre) =
        μ a * pairing p.post (A p.pre) := by
    simpa [Module.End.mul_apply, hleft, hright, hscaled,
      pairing_add_right] using hcomm
  change (β a - α a - μ a) * pairing p.post (A p.pre) = 0
  calc
    (β a - α a - μ a) * pairing p.post (A p.pre) =
        (β a * pairing p.post (A p.pre) -
          α a * pairing p.post (A p.pre)) -
            μ a * pairing p.post (A p.pre) := by ring
    _ = 0 := sub_eq_zero.mpr heq

/-- A mismatch in any grading coordinate forces the unnormalized matrix
coefficient to vanish. -/
theorem numerator_eq_zero_of_weight_mismatch
    (p : BoundaryPair) (H : 𝔞 → Operator)
    (α β μ : 𝔞 → ℂ) (A : Operator)
    (hpre : IsRightWeight H α p.pre)
    (hpost : IsLeftWeight H β p.post)
    (hA : IsOperatorMultiweight H μ A)
    (a : 𝔞) (hmismatch : β a - α a - μ a ≠ 0) :
    numerator p A = 0 := by
  exact (mul_eq_zero.mp
    (numerator_weight_equation p H α β μ A hpre hpost hA a)).resolve_left
      hmismatch

/-- The normalized two-boundary coefficient obeys the same selection rule. -/
theorem weakValue_eq_zero_of_weight_mismatch
    (p : BoundaryPair) (H : 𝔞 → Operator)
    (α β μ : 𝔞 → ℂ) (A : Operator)
    (hpre : IsRightWeight H α p.pre)
    (hpost : IsLeftWeight H β p.post)
    (hA : IsOperatorMultiweight H μ A)
    (a : 𝔞) (hmismatch : β a - α a - μ a ≠ 0) :
    weakValue p A = 0 := by
  simp [weakValue,
    numerator_eq_zero_of_weight_mismatch p H α β μ A hpre hpost hA a hmismatch]

/-- A nonzero readout can occur only at the exact multidegree selected by the
boundary weight difference. -/
theorem weakValue_ne_zero_implies_weight_match
    (p : BoundaryPair) (H : 𝔞 → Operator)
    (α β μ : 𝔞 → ℂ) (A : Operator)
    (hpre : IsRightWeight H α p.pre)
    (hpost : IsLeftWeight H β p.post)
    (hA : IsOperatorMultiweight H μ A)
    (hread : weakValue p A ≠ 0) :
    μ = boundaryWeightDifference α β := by
  funext a
  by_contra hne
  have hmismatch : β a - α a - μ a ≠ 0 := by
    intro hz
    apply hne
    dsimp [boundaryWeightDifference]
    linear_combination hz
  exact hread
    (weakValue_eq_zero_of_weight_mismatch
      p H α β μ A hpre hpost hA a hmismatch)

/-- Coordinatewise operator homogeneity is stable under nonzero scalar
multiplication. -/
theorem operatorMultiweight_smul
    (H : 𝔞 → Operator) (μ : 𝔞 → ℂ) (A : Operator)
    (hA : IsOperatorMultiweight H μ A) (c : ℂ) :
    IsOperatorMultiweight H μ (c • A) := by
  intro a
  rw [mul_smul_comm, smul_mul_assoc, hA a]
  simp [smul_smul]

/-- Brackets add multidegrees in the associative endomorphism algebra. -/
theorem operatorMultiweight_commutator
    (H : 𝔞 → Operator) (μ ν : 𝔞 → ℂ) (A B : Operator)
    (hA : IsOperatorMultiweight H μ A)
    (hB : IsOperatorMultiweight H ν B) :
    IsOperatorMultiweight H (fun a => μ a + ν a) (A * B - B * A) := by
  intro a
  have hAa := hA a
  have hBa := hB a
  calc
    H a * (A * B - B * A) - (A * B - B * A) * H a =
        (H a * A - A * H a) * B +
          A * (H a * B - B * H a) -
        ((H a * B - B * H a) * A +
          B * (H a * A - A * H a)) := by noncomm_ring
    _ = (μ a • A) * B + A * (ν a • B) -
        ((ν a • B) * A + B * (μ a • A)) := by rw [hAa, hBa]
    _ = (μ a + ν a) • (A * B - B * A) := by
      ext x
      simp [Module.End.mul_apply]
      module

/-- The complete algebraic selection packet. -/
theorem multigraded_two_boundary_packet
    (p : BoundaryPair) (H : 𝔞 → Operator)
    (α β μ : 𝔞 → ℂ) (A : Operator)
    (hpre : IsRightWeight H α p.pre)
    (hpost : IsLeftWeight H β p.post)
    (hA : IsOperatorMultiweight H μ A) :
    (∀ a, (β a - α a - μ a) * numerator p A = 0) ∧
      (weakValue p A ≠ 0 → μ = boundaryWeightDifference α β) := by
  exact ⟨fun a => numerator_weight_equation
      p H α β μ A hpre hpost hA a,
    fun hread => weakValue_ne_zero_implies_weight_match
      p H α β μ A hpre hpost hA hread⟩

end InfoGeometry.Streaming.MultigradedTwoBoundarySelection

end noncomputable section
