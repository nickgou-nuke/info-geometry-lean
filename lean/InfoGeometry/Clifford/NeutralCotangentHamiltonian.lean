/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Cotangent Hamiltonians on the neutral phase-space owner

The carrier is the existing `E × Module.Dual ℝ E`, with no finite-dimensional
or commutativity assumption on `Module.End ℝ E`. For an arbitrary endomorphism
`A`, its infinitesimal cotangent lift is `(x, ξ) ↦ (A x, -ξ ∘ A)`.

The constructed Hamiltonian is `H_A (x, ξ) = ξ (A x)`, using the existing
convention `ω(X, Y) = Y.2 X.1 - X.2 Y.1`. Thus
`d H_A(X)[V] = ω(L_A X, V)`. Here the derivative is proved as a native
`HasDerivAt` statement along every real affine line. No topology on `E` is
needed: the restriction to each such line is an exact quadratic polynomial.

The lift preserves the ordered commutator `A * B - B * A`, and the
corresponding Hamiltonians satisfy `ω(L_A X, L_B X) = H_[A,B](X)`.
The symmetric diagonal `B(X, L_A X)` vanishes and therefore cannot serve as
this Hamiltonian. This module constructs no Gibbs integral, spin-group
representation, global Hamiltonian flow, or manifold-level momentum map.
-/

namespace InfoGeometry.Clifford.NeutralCotangentHamiltonian

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The infinitesimal cotangent lift, with the contragredient minus sign. -/
noncomputable def cotangentLift (A : Module.End ℝ E) :
    Module.End ℝ (PhaseSpaceCarrier E) where
  toFun X := (A X.1, -(X.2.comp A))
  map_add' := by
    intro X Y
    apply Prod.ext
    · exact map_add A _ _
    · apply LinearMap.ext
      intro x
      simp [add_comm]
  map_smul' := by
    intro r X
    apply Prod.ext
    · exact map_smul A r _
    · apply LinearMap.ext
      intro x
      simp

@[simp] theorem cotangentLift_apply (A : Module.End ℝ E)
    (X : PhaseSpaceCarrier E) :
    cotangentLift A X = (A X.1, -(X.2.comp A)) := rfl

/-- Evaluation of the covector on the actual ordered operator action. -/
noncomputable def hamiltonian (A : Module.End ℝ E)
    (X : PhaseSpaceCarrier E) : ℝ :=
  X.2 (A X.1)

@[simp] theorem hamiltonian_apply (A : Module.End ℝ E)
    (X : PhaseSpaceCarrier E) :
    hamiltonian A X = X.2 (A X.1) := rfl

/-- The algebraic moment functional takes values in the dual of the full
endomorphism algebra. No identification with spinor-coordinate gradients is
assumed. -/
noncomputable def momentFunctional (X : PhaseSpaceCarrier E) :
    Module.Dual ℝ (Module.End ℝ E) where
  toFun A := hamiltonian A X
  map_add' := by
    intro A B
    simp [hamiltonian]
  map_smul' := by
    intro r A
    simp [hamiltonian]

@[simp] theorem momentFunctional_apply (X : PhaseSpaceCarrier E)
    (A : Module.End ℝ E) :
    momentFunctional X A = hamiltonian A X := rfl

/-- The lifted operator is skew for the symmetric neutral pairing. -/
theorem cotangentLift_neutral_skew (A : Module.End ℝ E)
    (X Y : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (cotangentLift A X) Y =
      -canonicalNeutralBilin X (cotangentLift A Y) := by
  simp [canonicalNeutralBilin_apply, add_comm]

/-- The same lift is infinitesimally symplectic. -/
theorem cotangentLift_omega_skew (A : Module.End ℝ E)
    (X Y : PhaseSpaceCarrier E) :
    neutralOmega (cotangentLift A X) Y =
      -neutralOmega X (cotangentLift A Y) := by
  simp [neutralOmega_apply, add_comm]

/-- The cotangent action preserves the chosen para-complex polarization. -/
theorem cotangentLift_commutes_para (A : Module.End ℝ E) :
    cotangentLift A * neutralParaInvolution =
      neutralParaInvolution * cotangentLift A := by
  apply LinearMap.ext
  intro X
  apply Prod.ext
  · rfl
  · apply LinearMap.ext
    intro x
    simp [Module.End.mul_apply]

/-- The proposed neutral skew-generator diagonal is identically zero. -/
theorem neutral_diagonal_cotangentLift_eq_zero (A : Module.End ℝ E)
    (X : PhaseSpaceCarrier E) :
    canonicalNeutralBilin X (cotangentLift A X) = 0 := by
  simp [canonicalNeutralBilin_apply]

theorem half_neutral_diagonal_cotangentLift_eq_zero (A : Module.End ℝ E)
    (X : PhaseSpaceCarrier E) :
    (1 / 2 : ℝ) * canonicalNeutralBilin X (cotangentLift A X) = 0 := by
  rw [neutral_diagonal_cotangentLift_eq_zero, mul_zero]

/-- The symplectic diagonal, with the lifted operator in the first slot,
recovers the nontrivial quadratic Hamiltonian. -/
theorem hamiltonian_eq_half_omega (A : Module.End ℝ E)
    (X : PhaseSpaceCarrier E) :
    hamiltonian A X =
      (1 / 2 : ℝ) * neutralOmega (cotangentLift A X) X := by
  simp only [hamiltonian_apply, neutralOmega_apply, cotangentLift_apply,
    LinearMap.neg_apply, LinearMap.comp_apply]
  rw [sub_neg_eq_add, ← two_mul, ← mul_assoc]
  norm_num

/-- Exact affine-line expansion. This identity precedes, and is used to prove,
the native directional derivative below. -/
theorem hamiltonian_add_smul (A : Module.End ℝ E)
    (X V : PhaseSpaceCarrier E) (t : ℝ) :
    hamiltonian A (X + t • V) = hamiltonian A X +
      t * neutralOmega (cotangentLift A X) V + t ^ 2 * hamiltonian A V := by
  simp [hamiltonian, map_add, map_smul, smul_eq_mul, pow_two,
    mul_add, mul_assoc, add_comm, add_left_comm, add_assoc]

/-- Native scalar directional differentiability on every affine line.
This states `d H_A(X)[V] = ω(L_A X,V)` without adding a norm to `E`. -/
theorem hamiltonian_hasDerivAt (A : Module.End ℝ E)
    (X V : PhaseSpaceCarrier E) :
    HasDerivAt (fun t : ℝ => hamiltonian A (X + t • V))
      (neutralOmega (cotangentLift A X) V) 0 := by
  have hpoly :
      HasDerivAt (fun t : ℝ => hamiltonian A X +
          t * neutralOmega (cotangentLift A X) V + t ^ 2 * hamiltonian A V)
        (neutralOmega (cotangentLift A X) V) 0 := by
    convert ((hasDerivAt_const (0 : ℝ) (hamiltonian A X)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const
        (neutralOmega (cotangentLift A X) V))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (hamiltonian A V)) using 1
    · funext t
      rfl
    · simp
  simpa only [hamiltonian_add_smul] using hpoly

/-- The infinitesimal cotangent lift is faithful. -/
theorem cotangentLift_injective : Function.Injective (cotangentLift (E := E)) := by
  intro A B hAB
  apply LinearMap.ext
  intro x
  have h := congrArg
    (fun L : Module.End ℝ (PhaseSpaceCarrier E) => (L (x, 0)).1) hAB
  simpa using h

/-- Composition reverses on covectors. The contragredient minus sign makes
the commutator lift preserve the original, noncommuting operator order. -/
theorem cotangentLift_commutator (A B : Module.End ℝ E) :
    cotangentLift (A * B - B * A) =
      cotangentLift A * cotangentLift B - cotangentLift B * cotangentLift A := by
  apply LinearMap.ext
  intro X
  apply Prod.ext
  · simp [Module.End.mul_apply]
  · apply LinearMap.ext
    intro x
    simp [Module.End.mul_apply, LinearMap.comp_apply, sub_eq_add_neg]

/-- Noncommuting endomorphisms remain noncommuting on the neutral carrier. -/
theorem cotangentLift_preserves_noncommutation (A B : Module.End ℝ E)
    (hAB : A * B ≠ B * A) :
    cotangentLift A * cotangentLift B ≠ cotangentLift B * cotangentLift A := by
  intro h
  apply hAB
  apply LinearMap.ext
  intro x
  have hx := congrArg
    (fun L : Module.End ℝ (PhaseSpaceCarrier E) => (L (x, 0)).1) h
  simpa [Module.End.mul_apply] using hx

/-- The Hamiltonian bracket has the exact ordered commutator sign:
`{H_A,H_B}(X) := ω(L_A X,L_B X) = H_[A,B](X)`. -/
theorem omega_lifts_eq_hamiltonian_commutator (A B : Module.End ℝ E)
    (X : PhaseSpaceCarrier E) :
    neutralOmega (cotangentLift A X) (cotangentLift B X) =
      hamiltonian (A * B - B * A) X := by
  simp [hamiltonian, Module.End.mul_apply, LinearMap.comp_apply,
    sub_eq_add_neg, add_comm]

/-- Differentiating `H_A` along the linear vector field of `H_B` gives
`H_[A,B]`, for the symplectic convention fixed in the owner. -/
theorem hamiltonian_hasDerivAt_cotangentLift (A B : Module.End ℝ E)
    (X : PhaseSpaceCarrier E) :
    HasDerivAt (fun t : ℝ => hamiltonian A (X + t • cotangentLift B X))
      (hamiltonian (A * B - B * A) X) 0 := by
  simpa only [omega_lifts_eq_hamiltonian_commutator] using
    hamiltonian_hasDerivAt A X (cotangentLift B X)

end InfoGeometry.Clifford.NeutralCotangentHamiltonian
