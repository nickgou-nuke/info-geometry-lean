/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Canonical.SouriauContragredientPairing
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Prod

/-!
# Linear symmetries of the neutral primal/dual phase space

The inverse-dual lift of a real linear equivalence acts on the existing
`PhaseSpaceCarrier E = E × Module.Dual ℝ E`. It preserves the neutral symmetric
form, the alternating form, and the canonical grading from
`NeutralPhaseSpaceCore`. Its infinitesimal version sends `D` to `(D, -D*)`
and preserves endomorphism commutators.

The native quadratic form `hamiltonian D` evaluates to `λ (D v)`. Its polar
bilinear map gives the algebraic directional differential, which is contraction
with the lifted generator for the convention `Ω((v,λ),(w,η)) = η(v) - λ(w)`.
The exact expansion along an affine line makes this differential statement
explicit without asserting a Fréchet derivative on an untopologized carrier.

The evaluation momentum map takes values in the algebraic dual of the full
endomorphism algebra. Its equivariance yields stabilizer containment and
surjective maps of orbits and their native coset models. These are set-level
maps; no smooth quotient or quotient-group structure is asserted. Endomorphism
commutators here are distinct from brackets of fundamental vector fields.
-/

noncomputable section

namespace InfoGeometry.Clifford.NeutralPhaseSpaceSymmetry

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Canonical.SouriauContragredientPairing

attribute [local instance 100] LieRing.ofAssociativeRing

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The existing contragredient representation transported from general-linear
units to native linear equivalences. -/
def contragredientLinearEquivHom :
    (E ≃ₗ[ℝ] E) →* (Module.Dual ℝ E ≃ₗ[ℝ] Module.Dual ℝ E) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv
      ℝ (Module.Dual ℝ E)).toMonoidHom.comp
    ((contragredientGeneralLinearRepresentation (R := ℝ) (V := E)).comp
      (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ E).symm.toMonoidHom)

@[simp] theorem contragredientLinearEquivHom_apply
    (e : E ≃ₗ[ℝ] E) (μ : Module.Dual ℝ E) (x : E) :
    contragredientLinearEquivHom e μ x = μ (e.symm x) := rfl

/-- The primal action together with the inverse-dual action. -/
def dualLift (e : E ≃ₗ[ℝ] E) :
    PhaseSpaceCarrier E ≃ₗ[ℝ] PhaseSpaceCarrier E :=
  e.prodCongr (contragredientLinearEquivHom e)

@[simp] theorem dualLift_apply (e : E ≃ₗ[ℝ] E) (X : PhaseSpaceCarrier E) :
    dualLift e X = (e X.1, X.2.comp e.symm.toLinearMap) := rfl

/-- The inverse-dual lift is a native group homomorphism. -/
def dualLiftHom :
    (E ≃ₗ[ℝ] E) →* (PhaseSpaceCarrier E ≃ₗ[ℝ] PhaseSpaceCarrier E) where
  toFun := dualLift
  map_one' := by
    apply LinearEquiv.ext
    intro X
    apply Prod.ext
    · rfl
    · exact congrArg
        (fun f : Module.Dual ℝ E ≃ₗ[ℝ] Module.Dual ℝ E => f X.2)
        (map_one (contragredientLinearEquivHom (E := E)))
  map_mul' e f := by
    apply LinearEquiv.ext
    intro X
    apply Prod.ext
    · rfl
    · exact congrArg
        (fun u : Module.Dual ℝ E ≃ₗ[ℝ] Module.Dual ℝ E => u X.2)
        (map_mul (contragredientLinearEquivHom (E := E)) e f)

@[simp] theorem dualLift_one :
    dualLift (1 : E ≃ₗ[ℝ] E) = 1 :=
  (dualLiftHom (E := E)).map_one

@[simp] theorem dualLift_mul (e f : E ≃ₗ[ℝ] E) :
    dualLift (e * f) = dualLift e * dualLift f :=
  (dualLiftHom (E := E)).map_mul e f

/-- The primal component makes the lifted representation faithful. -/
theorem dualLift_injective : Function.Injective (dualLift (E := E)) := by
  intro e f h
  apply LinearEquiv.ext
  intro x
  exact congrArg
    (fun u : PhaseSpaceCarrier E ≃ₗ[ℝ] PhaseSpaceCarrier E => (u (x, 0)).1) h

/-- The unscaled neutral symmetric pairing is invariant. -/
theorem dualLift_preserves_neutralBilin (e : E ≃ₗ[ℝ] E)
    (X Y : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (dualLift e X) (dualLift e Y) =
      canonicalNeutralBilin X Y := by
  simp [canonicalNeutralBilin_apply, dualLift_apply]

/-- The alternating form is invariant with the sign convention of the core. -/
theorem dualLift_preserves_omega (e : E ≃ₗ[ℝ] E)
    (X Y : PhaseSpaceCarrier E) :
    neutralOmega (dualLift e X) (dualLift e Y) = neutralOmega X Y := by
  simp [neutralOmega_apply, dualLift_apply]

/-- The lift commutes with the canonical primal/dual grading. -/
theorem dualLift_commutes_grading (e : E ≃ₗ[ℝ] E)
    (X : PhaseSpaceCarrier E) :
    dualLift e (neutralParaInvolution X) =
      neutralParaInvolution (dualLift e X) := by
  apply Prod.ext
  · rfl
  · apply LinearMap.ext
    intro x
    rfl

/-- The infinitesimal inverse-dual action uses the negative algebraic transpose. -/
def infinitesimalLift (D : Module.End ℝ E) :
    Module.End ℝ (PhaseSpaceCarrier E) :=
  D.prodMap (-D.dualMap)

@[simp] theorem infinitesimalLift_apply
    (D : Module.End ℝ E) (X : PhaseSpaceCarrier E) :
    infinitesimalLift D X = (D X.1, -X.2.comp D) := rfl

/-- The lifted operators preserve noncommutative endomorphism commutators. -/
theorem infinitesimalLift_lie (D F : Module.End ℝ E) :
    infinitesimalLift ⁅D, F⁆ = ⁅infinitesimalLift D, infinitesimalLift F⁆ := by
  apply LinearMap.ext
  intro X
  apply Prod.ext
  · simp [Ring.lie_def, infinitesimalLift_apply, Module.End.mul_apply]
  · apply LinearMap.ext
    intro x
    simp [Ring.lie_def, infinitesimalLift_apply, Module.End.mul_apply]

/-- The infinitesimal lift as a native morphism of real Lie algebras. -/
def infinitesimalLiftLieHom :
    Module.End ℝ E →ₗ⁅ℝ⁆ Module.End ℝ (PhaseSpaceCarrier E) where
  toFun := infinitesimalLift
  map_add' D F := by
    apply LinearMap.ext
    intro X
    apply Prod.ext
    · simp [infinitesimalLift_apply]
    · apply LinearMap.ext
      intro x
      simp [infinitesimalLift_apply]
      exact add_comm _ _
  map_smul' r D := by
    apply LinearMap.ext
    intro X
    apply Prod.ext
    · simp [infinitesimalLift_apply]
    · apply LinearMap.ext
      intro x
      simp [infinitesimalLift_apply]
  map_lie' {D F} := infinitesimalLift_lie D F

/-- Infinitesimal invariance of the symmetric pairing. -/
theorem infinitesimalLift_preserves_neutralBilin
    (D : Module.End ℝ E) (X Y : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (infinitesimalLift D X) Y +
      canonicalNeutralBilin X (infinitesimalLift D Y) = 0 := by
  simp [canonicalNeutralBilin_apply, infinitesimalLift_apply]
  abel

/-- Infinitesimal invariance of the alternating pairing. -/
theorem infinitesimalLift_preserves_omega
    (D : Module.End ℝ E) (X Y : PhaseSpaceCarrier E) :
    neutralOmega (infinitesimalLift D X) Y +
      neutralOmega X (infinitesimalLift D Y) = 0 := by
  simp [neutralOmega_apply, infinitesimalLift_apply]

/-- Conjugation of the generator intertwines the corresponding lifted operators. -/
theorem dualLift_infinitesimalLift (e : E ≃ₗ[ℝ] E)
    (D : Module.End ℝ E) (X : PhaseSpaceCarrier E) :
    dualLift e (infinitesimalLift D X) =
      infinitesimalLift (e.conj D) (dualLift e X) := by
  apply Prod.ext
  · simp [dualLift_apply, infinitesimalLift_apply]
  · apply LinearMap.ext
    intro x
    simp [dualLift_apply, infinitesimalLift_apply]

/-- The generator Hamiltonian is the core quadratic form pulled back along
the linear map `(v,λ) ↦ (D v,λ)`. -/
def hamiltonian (D : Module.End ℝ E) :
    QuadraticForm ℝ (PhaseSpaceCarrier E) :=
  (canonicalNeutralFormUnscaled (E := E)).comp
    (D.prodMap (LinearMap.id : Module.Dual ℝ E →ₗ[ℝ] Module.Dual ℝ E))

@[simp] theorem hamiltonian_apply (D : Module.End ℝ E)
    (X : PhaseSpaceCarrier E) :
    hamiltonian D X = X.2 (D X.1) := by
  simp [hamiltonian]

/-- Polarization identifies the algebraic directional differential with
contraction of the alternating form by the lifted generator. -/
theorem hamiltonian_polar (D : Module.End ℝ E) (X Y : PhaseSpaceCarrier E) :
    QuadraticMap.polar (hamiltonian D) X Y =
      neutralOmega (infinitesimalLift D X) Y := by
  simp [QuadraticMap.polar, hamiltonian_apply, infinitesimalLift_apply, map_add]
  abel

/-- The algebraic differential of the quadratic Hamiltonian at a point.
This uses native quadratic polarization and asserts no analytic regularity. -/
def hamiltonianDifferential (D : Module.End ℝ E) (X : PhaseSpaceCarrier E) :
    Module.Dual ℝ (PhaseSpaceCarrier E) :=
  (hamiltonian D).polarBilin X

@[simp] theorem hamiltonianDifferential_apply
    (D : Module.End ℝ E) (X Y : PhaseSpaceCarrier E) :
    hamiltonianDifferential D X Y = Y.2 (D X.1) + X.2 (D Y.1) := by
  change QuadraticMap.polar (hamiltonian D) X Y = _
  rw [hamiltonian_polar]
  simp [infinitesimalLift_apply]

/-- The Hamiltonian differential identity as equality of native linear forms. -/
theorem hamiltonian_differential_identity (D : Module.End ℝ E)
    (X : PhaseSpaceCarrier E) :
    hamiltonianDifferential D X = neutralOmega (infinitesimalLift D X) := by
  apply LinearMap.ext
  intro Y
  exact hamiltonian_polar D X Y

/-- The exact affine-line expansion certifies the first-order coefficient and
quadratic remainder, without imposing a topology on `E`. -/
theorem hamiltonian_line_expansion (D : Module.End ℝ E)
    (X Y : PhaseSpaceCarrier E) (t : ℝ) :
    hamiltonian D (X + t • Y) =
      hamiltonian D X + t * hamiltonianDifferential D X Y + t ^ 2 * hamiltonian D Y := by
  rw [QuadraticMap.map_add (hamiltonian D) X (t • Y),
    (hamiltonian D).map_smul t Y,
    (hamiltonian D).polar_smul_right t X Y]
  change hamiltonian D X + (t * t) * hamiltonian D Y +
      t * hamiltonianDifferential D X Y =
    hamiltonian D X + t * hamiltonianDifferential D X Y + t ^ 2 * hamiltonian D Y
  rw [pow_two]
  exact add_right_comm _ _ _

/-- The symplectic pairing of lifted generators is the Hamiltonian of their
endomorphism commutator. Operator order is retained in both compositions. -/
theorem hamiltonian_commutator (D F : Module.End ℝ E) (X : PhaseSpaceCarrier E) :
    neutralOmega (infinitesimalLift D X) (infinitesimalLift F X) =
      hamiltonian ⁅D, F⁆ X := by
  simp [neutralOmega_apply, infinitesimalLift_apply, hamiltonian_apply,
    Ring.lie_def, Module.End.mul_apply]
  abel

/-- Conjugation is a group homomorphism into linear equivalences of the
endomorphism algebra. -/
def conjugationLinearEquivHom :
    (E ≃ₗ[ℝ] E) →* (Module.End ℝ E ≃ₗ[ℝ] Module.End ℝ E) where
  toFun e := e.conj
  map_one' := by ext D x; rfl
  map_mul' e f := by ext D x; rfl

/-- The inverse-dual action of conjugation on functionals of endomorphisms. -/
def momentumTransport :
    (E ≃ₗ[ℝ] E) →*
      (Module.Dual ℝ (Module.End ℝ E) ≃ₗ[ℝ] Module.Dual ℝ (Module.End ℝ E)) :=
  (contragredientLinearEquivHom (E := Module.End ℝ E)).comp
    (conjugationLinearEquivHom (E := E))

@[simp] theorem momentumTransport_apply (e : E ≃ₗ[ℝ] E)
    (μ : Module.Dual ℝ (Module.End ℝ E)) (D : Module.End ℝ E) :
    momentumTransport e μ D = μ (e.symm.conj D) := rfl

/-- Each phase-space point defines a native linear functional on the full
endomorphism algebra. The dependence on the phase-space point is quadratic. -/
def momentum (X : PhaseSpaceCarrier E) : Module.Dual ℝ (Module.End ℝ E) where
  toFun D := X.2 (D X.1)
  map_add' D F := by simp
  map_smul' r D := by simp

@[simp] theorem momentum_apply (X : PhaseSpaceCarrier E) (D : Module.End ℝ E) :
    momentum X D = X.2 (D X.1) := rfl

/-- Evaluating the momentum map at a generator recovers its Hamiltonian. -/
theorem momentum_eq_hamiltonian (X : PhaseSpaceCarrier E) (D : Module.End ℝ E) :
    momentum X D = hamiltonian D X := by
  simp

/-- Equivariance of the momentum map under the inverse-dual lift. -/
theorem momentum_dualLift (e : E ≃ₗ[ℝ] E) (X : PhaseSpaceCarrier E) :
    momentum (dualLift e X) = momentumTransport e (momentum X) := by
  apply LinearMap.ext
  intro D
  simp [momentum_apply, dualLift_apply, momentumTransport_apply]

/-- Transporting the point pulls the generator back by inverse conjugation. -/
theorem hamiltonian_dualLift (e : E ≃ₗ[ℝ] E)
    (D : Module.End ℝ E) (X : PhaseSpaceCarrier E) :
    hamiltonian D (dualLift e X) = hamiltonian (e.symm.conj D) X := by
  simp [hamiltonian_apply, dualLift_apply]

/-- Simultaneous transport of a generator and a point preserves evaluation. -/
theorem hamiltonian_conjugation_invariant (e : E ≃ₗ[ℝ] E)
    (D : Module.End ℝ E) (X : PhaseSpaceCarrier E) :
    hamiltonian (e.conj D) (dualLift e X) = hamiltonian D X := by
  simp

/-- A named action, activated locally below to avoid a global overlapping instance. -/
@[instance_reducible]
def phaseSpaceAction : MulAction (E ≃ₗ[ℝ] E) (PhaseSpaceCarrier E) :=
  MulAction.compHom _ (dualLiftHom (E := E))

/-- The corresponding named action on momentum values. -/
@[instance_reducible]
def momentumAction :
    MulAction (E ≃ₗ[ℝ] E) (Module.Dual ℝ (Module.End ℝ E)) :=
  MulAction.compHom _ (momentumTransport (E := E))

attribute [local instance] phaseSpaceAction momentumAction

@[simp] theorem phaseSpace_smul (e : E ≃ₗ[ℝ] E) (X : PhaseSpaceCarrier E) :
    e • X = dualLift e X := rfl

@[simp] theorem momentum_smul (e : E ≃ₗ[ℝ] E)
    (μ : Module.Dual ℝ (Module.End ℝ E)) :
    e • μ = momentumTransport e μ := rfl

/-- The momentum map bundled as a native equivariant map. -/
def momentumEquivariant :
    PhaseSpaceCarrier E →[E ≃ₗ[ℝ] E] Module.Dual ℝ (Module.End ℝ E) where
  toFun := momentum
  map_smul' e X := momentum_dualLift e X

/-- A symmetry fixing the state also fixes its momentum value. -/
theorem stabilizer_le_momentum_stabilizer (X : PhaseSpaceCarrier E) :
    MulAction.stabilizer (E ≃ₗ[ℝ] E) X ≤
      MulAction.stabilizer (E ≃ₗ[ℝ] E) (momentum X) := by
  intro e he
  rw [MulAction.mem_stabilizer_iff] at he ⊢
  change dualLift e X = X at he
  change momentumTransport e (momentum X) = momentum X
  calc
    _ = momentum (dualLift e X) := (momentum_dualLift e X).symm
    _ = momentum X := congrArg momentum he

/-- The actual map from the state orbit to the orbit of its momentum value. -/
def momentumOrbitMap (X : PhaseSpaceCarrier E) :
    MulAction.orbit (E ≃ₗ[ℝ] E) X →
      MulAction.orbit (E ≃ₗ[ℝ] E) (momentum X) :=
  fun Y => ⟨momentum Y.1, by
    obtain ⟨e, he⟩ := MulAction.mem_orbit_iff.mp Y.2
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨e, ?_⟩
    change dualLift e X = Y.1 at he
    change momentumTransport e (momentum X) = momentum Y.1
    calc
      _ = momentum (dualLift e X) := (momentum_dualLift e X).symm
      _ = momentum Y.1 := congrArg momentum he⟩

@[simp] theorem momentumOrbitMap_apply (X : PhaseSpaceCarrier E)
    (Y : MulAction.orbit (E ≃ₗ[ℝ] E) X) :
    (momentumOrbitMap X Y).1 = momentum Y.1 := rfl

/-- Every momentum-orbit point comes from a state-orbit point. -/
theorem momentumOrbitMap_surjective (X : PhaseSpaceCarrier E) :
    Function.Surjective (momentumOrbitMap X) := by
  rintro ⟨μ, hμ⟩
  obtain ⟨e, he⟩ := MulAction.mem_orbit_iff.mp hμ
  refine ⟨⟨dualLift e X, ?_⟩, ?_⟩
  · exact MulAction.mem_orbit_iff.mpr ⟨e, rfl⟩
  · apply Subtype.ext
    change momentum (dualLift e X) = μ
    rw [momentum_dualLift]
    exact he

/-- The orbit map transported to native left-coset spaces by the
orbit/stabilizer equivalences. No normality hypothesis is imposed. -/
def momentumQuotientMap (X : PhaseSpaceCarrier E) :
    (E ≃ₗ[ℝ] E) ⧸ MulAction.stabilizer (E ≃ₗ[ℝ] E) X →
      (E ≃ₗ[ℝ] E) ⧸ MulAction.stabilizer (E ≃ₗ[ℝ] E) (momentum X) :=
  fun q => MulAction.orbitEquivQuotientStabilizer (E ≃ₗ[ℝ] E) (momentum X)
    (momentumOrbitMap X
      ((MulAction.orbitEquivQuotientStabilizer (E ≃ₗ[ℝ] E) X).symm q))

/-- The state/momentum orbit square commutes with its coset models. -/
theorem momentumQuotientMap_orbit (X : PhaseSpaceCarrier E)
    (Y : MulAction.orbit (E ≃ₗ[ℝ] E) X) :
    momentumQuotientMap X
        (MulAction.orbitEquivQuotientStabilizer (E ≃ₗ[ℝ] E) X Y) =
      MulAction.orbitEquivQuotientStabilizer (E ≃ₗ[ℝ] E) (momentum X)
        (momentumOrbitMap X Y) := by
  simp [momentumQuotientMap]

/-- The induced map of coset spaces is surjective. -/
theorem momentumQuotientMap_surjective (X : PhaseSpaceCarrier E) :
    Function.Surjective (momentumQuotientMap X) := by
  intro q
  obtain ⟨Y, hY⟩ := momentumOrbitMap_surjective X
    ((MulAction.orbitEquivQuotientStabilizer (E ≃ₗ[ℝ] E) (momentum X)).symm q)
  refine ⟨MulAction.orbitEquivQuotientStabilizer (E ≃ₗ[ℝ] E) X Y, ?_⟩
  simp [momentumQuotientMap, hY]

end InfoGeometry.Clifford.NeutralPhaseSpaceSymmetry
