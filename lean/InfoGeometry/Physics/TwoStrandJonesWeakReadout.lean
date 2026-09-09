import InfoGeometry.Physics.TwoStrandJonesCasimir
import InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

/-!
# Two-strand Jones operators and finite two-boundary readout

This file keeps the physical readout on the repository's existing regular
two-boundary functional.  The algebraic statements are deliberately phrased
for an arbitrary finite carrier, so they do not introduce a second weak-value
implementation.
-/

namespace InfoGeometry.Physics.TwoStrandJonesWeakReadout

open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional
open InfoGeometry.Physics.TwoStrandJonesCasimir

variable {ι : Type*} [Fintype ι]

abbrev Op := Operator ι

abbrev FlatTwoStrandState := State (Fin 2 × Fin 2)
abbrev FlatTwoStrandOperator := Operator (Fin 2 × Fin 2)

/-- Canonical flattening of the curried tensor carrier into the finite
two-boundary carrier used by the streaming weak-value owner. -/
def flattenTwoStrand : TwoStrandState ≃ₗ[ℂ] FlatTwoStrandState where
  toFun ψ ij := ψ ij.1 ij.2
  invFun f i j := f (i, j)
  left_inv ψ := by
    funext i j
    rfl
  right_inv f := by
    funext ij
    cases ij
    rfl
  map_add' ψ φ := by
    funext ij
    rfl
  map_smul' c ψ := by
    funext ij
    rfl

/-- Transport an operator on the two-strand tensor carrier to the flat
finite carrier. -/
noncomputable def flattenOperator (A : TwoStrandOperator) : FlatTwoStrandOperator :=
  flattenTwoStrand.toLinearMap.comp
    (A.comp flattenTwoStrand.symm.toLinearMap)

/-- The Jones linear braid operator `q 1 - q² e`. -/
noncomputable def jonesBraid {ι : Type*} [Fintype ι] (q : ℂ) (e : Operator ι) : Operator ι :=
  q • (1 : Op) - q ^ 2 • e

theorem weakValue_projector_casimir
    (p : RegularBoundaryPair ι) (M : ℂ) (e : Op)
    (C : Op) (hC : C = (-2 * M ^ 2) • ((1 : Op) - e)) :
    weakValue p C = (-2 * M ^ 2) * (1 - weakValue p e) := by
  rw [hC, weakValue_smul, weakValue_sub, weakValue_one]

theorem flatten_casimir_polynomial (M : ℂ) :
    flattenOperator (twoStrandCasimir M) =
      (-2 * M ^ 2) • ((1 : FlatTwoStrandOperator) -
        flattenOperator singletProjector) := by
  unfold flattenOperator
  rw [twoStrandCasimir_eq_projector_polynomial]
  ext ψ ij
  simp [LinearMap.comp_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.apply_symm_apply]

theorem twoStrandCasimir_weakValue
    (p : RegularBoundaryPair (Fin 2 × Fin 2)) (M : ℂ) :
    weakValue p (flattenOperator (twoStrandCasimir M)) =
      (-2 * M ^ 2) *
        (1 - weakValue p (flattenOperator singletProjector)) := by
  apply weakValue_projector_casimir p M (flattenOperator singletProjector)
    (flattenOperator (twoStrandCasimir M))
  exact flatten_casimir_polynomial M

theorem jonesBraid_on_singlet
    (q : ℂ) (e : Op) (v : State ι) (he : e v = v) :
    jonesBraid q e v = (q - q ^ 2) • v := by
  simp [jonesBraid, he, sub_smul]

theorem jonesBraid_on_complement
    (q : ℂ) (e : Op) (v : State ι) (he : e v = 0) :
    jonesBraid q e v = q • v := by
  simp [jonesBraid, he]

end InfoGeometry.Physics.TwoStrandJonesWeakReadout
