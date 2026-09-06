import InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

/-!
# Six circular weights of the traceless axial Cartan plane

The six circular Zorn channels form a six-dimensional representation carrier,
whereas their weights are linear functionals on the already proved rank-two
traceless Cartan plane.  This owner records that distinction concretely.  It
does not assert the twelve-root adjoint `G₂` decomposition.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCartanSixWeights

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

/-- The `i`th weight is coordinate evaluation on the native traceless Cartan
plane. -/
def weightFunctional (i : Fin 3) : TracelessWeight →ₗ[ℝ] ℝ where
  toFun k := k.1 i
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem weightFunctional_apply (i : Fin 3) (k : TracelessWeight) :
    weightFunctional i k = k.1 i := rfl

/-- The three positive weights sum to zero as functionals on the traceless
Cartan plane. -/
theorem weightFunctional_sum_zero :
    ∑ i : Fin 3, weightFunctional i = 0 := by
  apply LinearMap.ext
  intro k
  change ∑ i : Fin 3, k.1 i = 0
  exact k.2

/-- Six signed weight labels: three positive and three negative channels. -/
abbrev SignedWeightIndex := Fin 2 × Fin 3

def signedWeight (p : SignedWeightIndex) : TracelessWeight →ₗ[ℝ] ℝ :=
  if p.1 = 0 then weightFunctional p.2 else -weightFunctional p.2

@[simp] theorem signedWeight_positive (i : Fin 3) :
    signedWeight (0, i) = weightFunctional i := by
  simp [signedWeight]

@[simp] theorem signedWeight_negative (i : Fin 3) :
    signedWeight (1, i) = -weightFunctional i := by
  simp [signedWeight]

theorem signedWeightIndex_card : Fintype.card SignedWeightIndex = 6 := by
  native_decide

/-- The concrete Cartan generator acts on the upper circular channel with
weight `k i`. -/
theorem axialCartanEnd_rootPlus (k : Fin 3 → ℝ) (i : Fin 3) :
    axialCartanEnd k (cartesianZornLinearEquiv (rootPlus i)) =
      k i • cartesianZornLinearEquiv (rootPlus i) := by
  rw [cartesianZorn_rootPlus]
  ext j <;>
    simp [axialCartanEnd, chiralUpperBasis, Equiv.smul_def, coordEquiv,
      Pi.single_apply]
  by_cases h : j = i <;> simp [h]

/-- The lower circular channel carries the opposite weight. -/
theorem axialCartanEnd_rootMinus (k : Fin 3 → ℝ) (i : Fin 3) :
    axialCartanEnd k (cartesianZornLinearEquiv (rootMinus i)) =
      (-k i) • cartesianZornLinearEquiv (rootMinus i) := by
  rw [cartesianZorn_rootMinus]
  ext j <;>
    simp [axialCartanEnd, chiralLowerBasis, Equiv.smul_def, coordEquiv,
      Pi.single_apply]
  by_cases h : j = i <;> simp [h]

/-- Bundled six-channel eigenvalue readout for a point of the native
traceless Cartan plane. -/
theorem axialCartanEnd_signed_channel
    (k : TracelessWeight) (p : SignedWeightIndex) :
    axialCartanEnd k.1
        (if p.1 = 0 then cartesianZornLinearEquiv (rootPlus p.2)
          else cartesianZornLinearEquiv (rootMinus p.2)) =
      signedWeight p k •
        (if p.1 = 0 then cartesianZornLinearEquiv (rootPlus p.2)
          else cartesianZornLinearEquiv (rootMinus p.2)) := by
  rcases p with ⟨s, i⟩
  fin_cases s
  · simpa using axialCartanEnd_rootPlus k.1 i
  · simpa [signedWeight] using axialCartanEnd_rootMinus k.1 i

end InfoGeometry.Lie.SplitOctonionCartanSixWeights
