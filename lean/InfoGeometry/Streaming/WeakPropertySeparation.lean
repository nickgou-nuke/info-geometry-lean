import InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

/-!
# A finite weak-property separation witness

This file constructs the exact finite algebraic pattern often described as a
"quantum Cheshire Cat": a path-support projector has weak value zero while a
nonzero operator supported in that same path sector has nonzero weak value.

The theorem is deliberately static.  It does not identify the supported
operator with an angular-momentum current and does not prove transport through
a spacetime region.  A current interpretation additionally requires a
Hamiltonian, a continuity equation, and a current operator.
-/

noncomputable section

namespace InfoGeometry.Streaming.WeakPropertySeparation

open scoped BigOperators
open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

abbrev PathSpinState := State (Fin 4)
abbrev PathSpinOperator := Operator (Fin 4)

/-- Basis order: left-up, left-down, corridor-up, corridor-down. -/
def preState : PathSpinState :=
  ![(1 : ℂ), 0, 1, 1]

/-- The two corridor amplitudes have opposite post-selected signs. -/
def postState : PathSpinState :=
  ![(1 : ℂ), 0, 1, -1]

@[simp] theorem post_pre_overlap :
    pairing postState preState = 1 := by
  norm_num [pairing, postState, preState, Fin.sum_univ_four]

/-- The explicit regular two-boundary pair. -/
def boundaryPair : RegularBoundaryPair (Fin 4) where
  pre := preState
  post := postState
  overlap_ne := by
    rw [post_pre_overlap]
    norm_num

@[simp] theorem boundaryPair_overlap :
    overlap boundaryPair = 1 := by
  simpa [overlap, boundaryPair] using post_pre_overlap

/-- Project onto the two-dimensional corridor path sector. -/
def corridorProjector : PathSpinOperator where
  toFun ψ := ![0, 0, ψ 2, ψ 3]
  map_add' ψ φ := by
    ext i
    fin_cases i <;> simp
  map_smul' c ψ := by
    ext i
    fin_cases i <;> simp

/-- Spin-z inside the corridor and zero outside it. -/
def corridorSpinZ : PathSpinOperator where
  toFun ψ := ![0, 0, ψ 2, -ψ 3]
  map_add' ψ φ := by
    ext i
    fin_cases i <;> simp
  map_smul' c ψ := by
    ext i
    fin_cases i <;> simp

@[simp] theorem corridorProjector_apply (ψ : PathSpinState) :
    corridorProjector ψ = ![0, 0, ψ 2, ψ 3] := rfl

@[simp] theorem corridorSpinZ_apply (ψ : PathSpinState) :
    corridorSpinZ ψ = ![0, 0, ψ 2, -ψ 3] := rfl

/-- The path observable is a genuine idempotent. -/
theorem corridorProjector_sq :
    corridorProjector * corridorProjector = corridorProjector := by
  apply LinearMap.ext
  intro ψ
  funext i
  fin_cases i <;> rfl

/-- The spin observable is supported on the corridor on the left. -/
theorem corridorProjector_mul_spinZ :
    corridorProjector * corridorSpinZ = corridorSpinZ := by
  apply LinearMap.ext
  intro ψ
  funext i
  fin_cases i <;> rfl

/-- The spin observable is supported on the corridor on the right. -/
theorem corridorSpinZ_mul_projector :
    corridorSpinZ * corridorProjector = corridorSpinZ := by
  apply LinearMap.ext
  intro ψ
  funext i
  fin_cases i <;> rfl

/-- Squaring the signed corridor observable forgets spin and returns path
support. -/
theorem corridorSpinZ_sq :
    corridorSpinZ * corridorSpinZ = corridorProjector := by
  apply LinearMap.ext
  intro ψ
  funext i
  fin_cases i <;> simp [corridorSpinZ, corridorProjector]

@[simp] theorem corridorProjector_numerator :
    numerator boundaryPair corridorProjector = 0 := by
  norm_num [numerator, boundaryPair, pairing, corridorProjector,
    postState, preState, Fin.sum_univ_four]

@[simp] theorem corridorSpinZ_numerator :
    numerator boundaryPair corridorSpinZ = 2 := by
  norm_num [numerator, boundaryPair, pairing, corridorSpinZ,
    postState, preState, Fin.sum_univ_four]

/-- Destructive interference makes the corridor-support weak value vanish. -/
@[simp] theorem corridorProjector_weakValue :
    weakValue boundaryPair corridorProjector = 0 := by
  simp [weakValue]

/-- The signed property in the same corridor has nonzero weak value. -/
@[simp] theorem corridorSpinZ_weakValue :
    weakValue boundaryPair corridorSpinZ = 2 := by
  simp [weakValue]

/-- Proof-carrying static weak-property separation. -/
structure WeakPropertySeparation (ι : Type*) [Fintype ι] where
  boundary : RegularBoundaryPair ι
  support : Operator ι
  property : Operator ι
  support_idempotent : support * support = support
  support_mul_property : support * property = property
  property_mul_support : property * support = property
  support_weak_zero : weakValue boundary support = 0
  property_weak_ne_zero : weakValue boundary property ≠ 0

/-- The explicit four-coordinate witness. -/
def cheshireWitness : WeakPropertySeparation (Fin 4) where
  boundary := boundaryPair
  support := corridorProjector
  property := corridorSpinZ
  support_idempotent := corridorProjector_sq
  support_mul_property := corridorProjector_mul_spinZ
  property_mul_support := corridorSpinZ_mul_projector
  support_weak_zero := corridorProjector_weakValue
  property_weak_ne_zero := by
    rw [corridorSpinZ_weakValue]
    norm_num

/-- The weak functional is not multiplicative: the property has weak value
`2`, although its square has weak value zero.  Thus it is not a positive state
or an algebra character. -/
theorem corridorSpinZ_square_weakValue :
    weakValue boundaryPair (corridorSpinZ * corridorSpinZ) = 0 := by
  rw [corridorSpinZ_sq, corridorProjector_weakValue]

theorem weakValue_not_multiplicative :
    weakValue boundaryPair (corridorSpinZ * corridorSpinZ) ≠
      weakValue boundaryPair corridorSpinZ *
        weakValue boundaryPair corridorSpinZ := by
  rw [corridorSpinZ_square_weakValue, corridorSpinZ_weakValue]
  norm_num

/-- The complete finite separation packet. -/
theorem weak_property_separation_packet :
    corridorProjector * corridorProjector = corridorProjector ∧
      corridorProjector * corridorSpinZ = corridorSpinZ ∧
      corridorSpinZ * corridorProjector = corridorSpinZ ∧
      weakValue boundaryPair corridorProjector = 0 ∧
      weakValue boundaryPair corridorSpinZ = 2 ∧
      weakValue boundaryPair (corridorSpinZ * corridorSpinZ) = 0 := by
  exact ⟨corridorProjector_sq,
    corridorProjector_mul_spinZ,
    corridorSpinZ_mul_projector,
    corridorProjector_weakValue,
    corridorSpinZ_weakValue,
    corridorSpinZ_square_weakValue⟩

end InfoGeometry.Streaming.WeakPropertySeparation

end noncomputable section
