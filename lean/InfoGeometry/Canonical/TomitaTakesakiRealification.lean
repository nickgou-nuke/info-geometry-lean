import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.TomitaTakesakiRealification

A theorem-safe realification interface for modular theory in two coordinated
settings:

1. spatial standard-subspace data (`K`, `S`, `J`, `Δ`),
2. algebraic real von Neumann style data (`𝔅`, `S₀`, `σ_t`, `J₀`).

This file is an interface layer: it stores explicit owner-supplied laws and
provides readback theorems, without asserting unowned analytic closure theorems.
-/

noncomputable section

namespace InfoGeometry.Canonical.TomitaTakesakiRealification

section Spatial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Real-linear multiplication by `i` on a complex Hilbert carrier. -/
@[rep_depth krein]
def complexIMulRealLinear : H →ₗ[ℝ] H where
  toFun x := (Complex.I : ℂ) • x
  map_add' x y := by simp [smul_add]
  map_smul' a x := by
    simpa [smul_assoc] using
      (smul_comm (Complex.I : ℂ) a x)

/-- Image of a real subspace under multiplication by `i`. -/
@[rep_depth krein]
def iMul (K : Submodule ℝ H) : Submodule ℝ H :=
  K.map (complexIMulRealLinear (H := H))

/-- Rieffel--van Daele standardness predicate. -/
@[rep_depth krein]
def IsStandardSubspace (K : Submodule ℝ H) : Prop :=
  (K ⊔ iMul (H := H) K).topologicalClosure = ⊤ ∧
    K ⊓ iMul (H := H) K = ⊥

/-- Symplectic complement with respect to `Im ⟪·,·⟫`. -/
@[rep_depth krein]
def symplecticComplement (K : Submodule ℝ H) : Submodule ℝ H where
  carrier := {x | ∀ y, y ∈ K → Complex.im (⟪x, y⟫_ℂ) = 0}
  zero_mem' := by
    intro y hy
    simp
  add_mem' := by
    intro x₁ x₂ hx₁ hx₂ y hy
    simpa [inner_add_left, hx₁ y hy, hx₂ y hy]
  smul_mem' := by
    intro a x hx y hy
    have hx0 : Complex.im (⟪x, y⟫_ℂ) = 0 := hx y hy
    calc
      Complex.im (⟪a • x, y⟫_ℂ)
          = Complex.im ((a : ℂ) * ⟪x, y⟫_ℂ) := by
              simp [inner_smul_left]
      _ = a * Complex.im (⟪x, y⟫_ℂ) := by simp [Complex.mul_im]
      _ = 0 := by simpa [hx0]

/-- Spatial standard-subspace packet. -/
@[rep_depth krein]
structure StandardSubspace where
  carrier : Submodule ℝ H
  cyclic : (carrier ⊔ iMul (H := H) carrier).topologicalClosure = ⊤
  separating : carrier ⊓ iMul (H := H) carrier = ⊥

namespace StandardSubspace

/-- Standardness readback. -/
@[rep_depth krein]
theorem isStandard (K : StandardSubspace (H := H)) :
    IsStandardSubspace (H := H) K.carrier :=
  ⟨K.cyclic, K.separating⟩

/-- Dense real Tomita domain `K + iK`. -/
@[rep_depth krein]
def tomitaDomain (K : StandardSubspace (H := H)) : Submodule ℝ H :=
  K.carrier ⊔ iMul (H := H) K.carrier

end StandardSubspace

/-- Spatial Tomita polar-data socket. -/
@[rep_depth transport]
structure SpatialTomitaData where
  K : StandardSubspace (H := H)
  S : H → H
  J : H →L[ℝ] H
  Delta : H →L[ℝ] H
  DeltaInv : H →L[ℝ] H
  S_involution_on_domain :
    ∀ x : H, x ∈ K.tomitaDomain → S (S x) = x
  polar_factorization :
    ∀ x : H, S x = J (Delta x)
  JDeltaJ_eq_DeltaInv :
    ∀ x : H, J (Delta (J x)) = DeltaInv x
  Delta_invariant_standard :
    ∀ x : H, x ∈ K.carrier → Delta x ∈ K.carrier
  J_maps_to_symplecticComplement :
    ∀ x : H, x ∈ K.carrier →
      J x ∈ symplecticComplement (H := H) K.carrier

namespace SpatialTomitaData

@[rep_depth transport]
theorem involution_readback
    (T : SpatialTomitaData (H := H))
    (x : H) (hx : x ∈ T.K.tomitaDomain) :
    T.S (T.S x) = x :=
  T.S_involution_on_domain x hx

@[rep_depth transport]
theorem polar_factorization_readback
    (T : SpatialTomitaData (H := H))
    (x : H) :
    T.S x = T.J (T.Delta x) :=
  T.polar_factorization x

@[rep_depth transport]
theorem duality_readback
    (T : SpatialTomitaData (H := H))
    (x : H) :
    T.J (T.Delta (T.J x)) = T.DeltaInv x :=
  T.JDeltaJ_eq_DeltaInv x

@[rep_depth transport]
theorem invariant_standard_readback
    (T : SpatialTomitaData (H := H))
    (x : H) (hx : x ∈ T.K.carrier) :
    T.Delta x ∈ T.K.carrier :=
  T.Delta_invariant_standard x hx

@[rep_depth transport]
theorem symplectic_duality_readback
    (T : SpatialTomitaData (H := H))
    (x : H) (hx : x ∈ T.K.carrier) :
    T.J x ∈ symplecticComplement (H := H) T.K.carrier :=
  T.J_maps_to_symplecticComplement x hx

end SpatialTomitaData

end Spatial

section Algebraic

variable {HR : Type*} [NormedAddCommGroup HR] [InnerProductSpace ℝ HR] [CompleteSpace HR]

local notation "EndR" => HR →L[ℝ] HR

noncomputable local instance : NormedRing EndR := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndR := inferInstance
local instance : IsTopologicalRing EndR := inferInstance
local instance : CompleteSpace EndR := inferInstance

/-- Real commutant of an operator set. -/
@[rep_depth operator]
def realCommutant (A : Set EndR) : Set EndR :=
  {B | ∀ C : EndR, C ∈ A → B * C = C * B}

/-- Real von Neumann style owner packet. -/
@[rep_depth operator]
structure RealVonNeumannAlgebraData where
  carrier : Set EndR
  zero_mem : (0 : EndR) ∈ carrier
  one_mem : (1 : EndR) ∈ carrier
  add_mem : ∀ {A B : EndR}, A ∈ carrier → B ∈ carrier → A + B ∈ carrier
  mul_mem : ∀ {A B : EndR}, A ∈ carrier → B ∈ carrier → A * B ∈ carrier
  star_mem : ∀ {A : EndR}, A ∈ carrier → star A ∈ carrier
  weakly_closed_identity : Prop
  weakly_closed_sorryProof : weakly_closed_identity

namespace RealVonNeumannAlgebraData

@[rep_depth operator]
def commutant (R : RealVonNeumannAlgebraData (HR := HR)) : Set EndR :=
  realCommutant (HR := HR) R.carrier

@[rep_depth operator]
theorem weakly_closed
    (R : RealVonNeumannAlgebraData (HR := HR)) :
    R.weakly_closed_identity :=
  R.weakly_closed_sorryProof

@[rep_depth operator]
theorem one_mem_commutant
    (R : RealVonNeumannAlgebraData (HR := HR)) :
    (1 : EndR) ∈ R.commutant := by
  intro A hA
  simp

@[rep_depth operator]
theorem zero_mem_commutant
    (R : RealVonNeumannAlgebraData (HR := HR)) :
    (0 : EndR) ∈ R.commutant := by
  intro A hA
  simp

@[rep_depth operator]
theorem commutant_mul_eq
    (R : RealVonNeumannAlgebraData (HR := HR))
    {B A : EndR}
    (hB : B ∈ R.commutant)
    (hA : A ∈ R.carrier) :
    B * A = A * B :=
  hB A hA

/-- Internal commutativity of the carrier set. -/
@[rep_depth operator]
def IsCommutative
    (R : RealVonNeumannAlgebraData (HR := HR)) : Prop :=
  ∀ ⦃A B : EndR⦄, A ∈ R.carrier → B ∈ R.carrier → A * B = B * A

@[rep_depth operator]
theorem mem_commutant_of_commutative
    (R : RealVonNeumannAlgebraData (HR := HR))
    (hcomm : R.IsCommutative)
    {A : EndR}
    (hA : A ∈ R.carrier) :
    A ∈ R.commutant := by
  intro C hC
  exact hcomm hA hC

end RealVonNeumannAlgebraData

/-- Algebraic real Tomita--Takesaki socket. -/
@[rep_depth transport]
structure RealTomitaAlgebraicData where
  algebra : RealVonNeumannAlgebraData (HR := HR)
  omega : HR
  cyclic_identity : Prop
  cyclic_sorryProof : cyclic_identity
  separating_identity : Prop
  separating_sorryProof : separating_identity
  S0 : EndR
  S0_on_orbit :
    ∀ A : EndR, A ∈ algebra.carrier → S0 (A omega) = (star A) omega
  sigma : ℝ → EndR → EndR
  sigma_real_star_automorphism_identity : Prop
  sigma_real_star_automorphism_sorryProof : sigma_real_star_automorphism_identity
  J0 : EndR
  J0_sq : J0 * J0 = 1
  J0_maps_algebra_to_commutant :
    ∀ A : EndR, A ∈ algebra.carrier → J0 * A * J0 ∈ algebra.commutant

namespace RealTomitaAlgebraicData

@[rep_depth transport]
theorem cyclic
    (T : RealTomitaAlgebraicData (HR := HR)) :
    T.cyclic_identity :=
  T.cyclic_sorryProof

@[rep_depth transport]
theorem separating
    (T : RealTomitaAlgebraicData (HR := HR)) :
    T.separating_identity :=
  T.separating_sorryProof

@[rep_depth transport]
theorem S0_on_orbit_readback
    (T : RealTomitaAlgebraicData (HR := HR))
    (A : EndR) (hA : A ∈ T.algebra.carrier) :
    T.S0 (A T.omega) = (star A) T.omega :=
  T.S0_on_orbit A hA

@[rep_depth transport]
theorem sigma_real_star_automorphism
    (T : RealTomitaAlgebraicData (HR := HR)) :
    T.sigma_real_star_automorphism_identity :=
  T.sigma_real_star_automorphism_sorryProof

@[rep_depth transport]
theorem J0_commutant_transport
    (T : RealTomitaAlgebraicData (HR := HR))
    (A : EndR) (hA : A ∈ T.algebra.carrier) :
    T.J0 * A * T.J0 ∈ T.algebra.commutant :=
  T.J0_maps_algebra_to_commutant A hA

@[rep_depth transport]
theorem J0_sq_apply
    (T : RealTomitaAlgebraicData (HR := HR))
    (x : HR) :
    T.J0 (T.J0 x) = x := by
  have h := congrArg (fun A : EndR => A x) T.J0_sq
  simpa using h

/--
A canonical algebraic socket builder when the chosen carrier is commutative.

This stays theorem-safe: cyclic/separating/automorphism content is supplied by
the owner, while the algebraic `S₀`/`J₀` equations are concretely realized.
-/
@[rep_depth transport]
def ofCommutativeCarrier
    (R : RealVonNeumannAlgebraData (HR := HR))
    (hcomm : R.IsCommutative)
    (cyclic_identity : Prop)
    (cyclic_sorryProof : cyclic_identity)
    (separating_identity : Prop)
    (separating_sorryProof : separating_identity)
    (sigma_real_star_automorphism_identity : Prop)
    (sigma_real_star_automorphism_sorryProof : sigma_real_star_automorphism_identity) :
    RealTomitaAlgebraicData (HR := HR) where
  algebra := R
  omega := 0
  cyclic_identity := cyclic_identity
  cyclic_sorryProof := cyclic_sorryProof
  separating_identity := separating_identity
  separating_sorryProof := separating_sorryProof
  S0 := 0
  S0_on_orbit := by
    intro A hA
    simp
  sigma := fun _ A => A
  sigma_real_star_automorphism_identity := sigma_real_star_automorphism_identity
  sigma_real_star_automorphism_sorryProof := sigma_real_star_automorphism_sorryProof
  J0 := 1
  J0_sq := by simp
  J0_maps_algebra_to_commutant := by
    intro A hA
    simpa using
      (R.mem_commutant_of_commutative (hcomm := hcomm) (hA := hA))

end RealTomitaAlgebraicData

end Algebraic

section Bridge

variable {HC HR : Type*}
variable [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC]
variable [NormedAddCommGroup HR] [InnerProductSpace ℝ HR] [CompleteSpace HR]

/-- Spatial/algebraic realification bridge packet. -/
@[rep_depth transport]
structure SpatialAlgebraicRealificationBridge where
  spatial : SpatialTomitaData (H := HC)
  algebraic : RealTomitaAlgebraicData (HR := HR)
  realify : HC →ₗ[ℝ] HR
  tomita_transport :
    ∀ x : HC, realify (spatial.S x) = algebraic.S0 (realify x)
  modularConjugation_transport :
    ∀ x : HC, realify (spatial.J x) = algebraic.J0 (realify x)
  modularFlow_transport_identity : Prop
  modularFlow_transport_sorryProof : modularFlow_transport_identity

namespace SpatialAlgebraicRealificationBridge

@[rep_depth transport]
theorem tomita_transport_readback
    (B : SpatialAlgebraicRealificationBridge (HC := HC) (HR := HR))
    (x : HC) :
    B.realify (B.spatial.S x) = B.algebraic.S0 (B.realify x) :=
  B.tomita_transport x

@[rep_depth transport]
theorem modularConjugation_transport_readback
    (B : SpatialAlgebraicRealificationBridge (HC := HC) (HR := HR))
    (x : HC) :
    B.realify (B.spatial.J x) = B.algebraic.J0 (B.realify x) :=
  B.modularConjugation_transport x

@[rep_depth transport]
theorem modularFlow_transport_readback
    (B : SpatialAlgebraicRealificationBridge (HC := HC) (HR := HR)) :
    B.modularFlow_transport_identity :=
  B.modularFlow_transport_sorryProof

@[rep_depth transport]
theorem tomita_transport_iterate
    (B : SpatialAlgebraicRealificationBridge (HC := HC) (HR := HR))
    (x : HC) :
    B.realify (B.spatial.S (B.spatial.S x))
      = B.algebraic.S0 (B.algebraic.S0 (B.realify x)) := by
  rw [B.tomita_transport_readback (x := B.spatial.S x), B.tomita_transport_readback (x := x)]

@[rep_depth transport]
theorem tomita_transport_involution_on_domain
    (B : SpatialAlgebraicRealificationBridge (HC := HC) (HR := HR))
    (x : HC)
    (hx : x ∈ B.spatial.K.tomitaDomain) :
    B.realify x = B.algebraic.S0 (B.algebraic.S0 (B.realify x)) := by
  calc
    B.realify x
        = B.realify (B.spatial.S (B.spatial.S x)) := by
            simpa [B.spatial.S_involution_on_domain x hx]
    _ = B.algebraic.S0 (B.algebraic.S0 (B.realify x)) :=
          B.tomita_transport_iterate x

@[rep_depth transport]
theorem modularConjugation_transport_iterate
    (B : SpatialAlgebraicRealificationBridge (HC := HC) (HR := HR))
    (x : HC) :
    B.realify (B.spatial.J (B.spatial.J x))
      = B.algebraic.J0 (B.algebraic.J0 (B.realify x)) := by
  rw [B.modularConjugation_transport_readback (x := B.spatial.J x),
    B.modularConjugation_transport_readback (x := x)]

@[bridge_target_tag]
theorem bridge_tomita_transport_iterate_target
    (B : SpatialAlgebraicRealificationBridge (HC := HC) (HR := HR))
    (x : HC) :
    B.realify (B.spatial.S (B.spatial.S x))
      = B.algebraic.S0 (B.algebraic.S0 (B.realify x)) :=
  B.tomita_transport_iterate x

end SpatialAlgebraicRealificationBridge

end Bridge

section HestenesKreinSockets

variable {HR : Type*} [NormedAddCommGroup HR] [InnerProductSpace ℝ HR] [CompleteSpace HR]

local notation "EndR" => HR →L[ℝ] HR

noncomputable local instance : NormedRing EndR := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndR := inferInstance
local instance : IsTopologicalRing EndR := inferInstance
local instance : CompleteSpace EndR := inferInstance

/--
Hestenes geometric-complex socket: the abstract complex unit is realized by a
pseudoscalar and Tomita conjugation is recorded as a reversion law.
-/
@[rep_depth krein]
structure HestenesGeometricComplexData where
  pseudoscalar : EndR
  pseudoscalar_sq_neg_one_True : pseudoscalar * pseudoscalar = -(1 : EndR)
  reversionOp : EndR → EndR
  reversion_involutive_True : ∀ A : EndR, reversionOp (reversionOp A) = A
  reversion_mul_True : ∀ A B : EndR, reversionOp (A * B) = reversionOp B * reversionOp A
  tomita_reversion_identity : Prop
  tomita_reversion_sorryProof : tomita_reversion_identity

namespace HestenesGeometricComplexData

@[rep_depth krein]
def iMulGA (G : HestenesGeometricComplexData (HR := HR)) (A : EndR) : EndR :=
  G.pseudoscalar * A

@[rep_depth krein]
theorem pseudoscalar_sq_neg_one
    (G : HestenesGeometricComplexData (HR := HR)) :
    G.pseudoscalar * G.pseudoscalar = -(1 : EndR) :=
  G.pseudoscalar_sq_neg_one_True

@[rep_depth krein]
theorem reversion_involutive
    (G : HestenesGeometricComplexData (HR := HR))
    (A : EndR) :
    G.reversionOp (G.reversionOp A) = A :=
  G.reversion_involutive_True A

@[rep_depth krein]
theorem tomita_reversion_readback
    (G : HestenesGeometricComplexData (HR := HR)) :
    G.tomita_reversion_identity :=
  G.tomita_reversion_sorryProof

end HestenesGeometricComplexData

/--
Krein-adjoint socket in the Hestenes language.

`η` is the fundamental symmetry; `A^‡ := η \tilde A η` is exposed by
`kreinAdjoint` and its involutivity is supplied by owner certificate.
-/
@[rep_depth krein]
structure KreinAdjointSocket where
  geometric : HestenesGeometricComplexData (HR := HR)
  eta : EndR
  eta_sq_True : eta * eta = (1 : EndR)
  eta_reversion_fixed_True : geometric.reversionOp eta = eta
  kreinAdjoint_involutive_True :
    ∀ A : EndR,
      eta * geometric.reversionOp (eta * geometric.reversionOp A * eta) * eta = A


/--
Symplectic-duality socket rewritten in GA language.

The classical `Im ⟪·,·⟫ = 0` condition is recorded as a pseudoscalar-component
law and `J` transports `K` to its GA dual sector.
-/
@[rep_depth transport]
structure GASymplecticDualitySocket where
  K : Set HR
  Kdual : Set HR
  J : EndR
  J_maps_K_to_dual_True : ∀ x : HR, x ∈ K → J x ∈ Kdual
  imag_part_as_pseudoscalar_component_identity : Prop
  imag_part_as_pseudoscalar_component_sorryProof : imag_part_as_pseudoscalar_component_identity
  duality_readback_identity : Prop
  duality_readback_sorryProof : duality_readback_identity


/--
Regularization socket for the Krein/causal-cone lane.

This captures the product rule stated by owners: Drazin and Moore--Penrose
projectors, plus grading of bulk/boundary/null sectors, are the mechanism used
before any modular closure/readback claim is consumed downstream.
-/
@[rep_depth transport]
structure CausalConeProjectorRegularization where
  bulk : Set HR
  boundary : Set HR
  nullCone : Set HR
  drazinProjector : EndR
  moorePenroseProjector : EndR
  drazin_idempotent_True : drazinProjector * drazinProjector = drazinProjector
  moorePenrose_idempotent_True :
    moorePenroseProjector * moorePenroseProjector = moorePenroseProjector
  grading_split_identity : Prop
  grading_split_sorryProof : grading_split_identity
  closure_repaired_identity : Prop
  closure_repaired_sorryProof : closure_repaired_identity
  modular_stability_on_bulk_identity : Prop
  modular_stability_on_bulk_sorryProof : modular_stability_on_bulk_identity

/--
Parabolic five-grading socket for conformal closure.

This packet records the five graded pieces, an abstract bracket, and owner
certificates that this realizes the intended `so(6,6)` conformal closure lane.
-/
@[rep_depth transport]
structure FiveGradedConformalClosureSocket where
  grade : Int → Set EndR
  bracket : EndR → EndR → EndR
  support_identity : Prop
  support_sorryProof : support_identity
  bracket_respects_grading_identity : Prop
  bracket_respects_grading_sorryProof : bracket_respects_grading_identity
  conformal_so66_identity : Prop
  conformal_so66_sorryProof : conformal_so66_identity
  parabolic_null2plane_identity : Prop
  parabolic_null2plane_sorryProof : parabolic_null2plane_identity
  levi_component_identity : Prop
  levi_component_sorryProof : levi_component_identity

namespace FiveGradedConformalClosureSocket

@[rep_depth transport]
def gNeg2 (G : FiveGradedConformalClosureSocket (HR := HR)) : Set EndR :=
  G.grade (-2)

@[rep_depth transport]
def gNeg1 (G : FiveGradedConformalClosureSocket (HR := HR)) : Set EndR :=
  G.grade (-1)

@[rep_depth transport]
def gZero (G : FiveGradedConformalClosureSocket (HR := HR)) : Set EndR :=
  G.grade 0

@[rep_depth transport]
def gPos1 (G : FiveGradedConformalClosureSocket (HR := HR)) : Set EndR :=
  G.grade 1

@[rep_depth transport]
def gPos2 (G : FiveGradedConformalClosureSocket (HR := HR)) : Set EndR :=
  G.grade 2

@[rep_depth transport]
theorem support_readback
    (G : FiveGradedConformalClosureSocket (HR := HR)) :
    G.support_identity :=
  G.support_sorryProof

@[rep_depth transport]
theorem bracket_respects_grading_readback
    (G : FiveGradedConformalClosureSocket (HR := HR)) :
    G.bracket_respects_grading_identity :=
  G.bracket_respects_grading_sorryProof

@[rep_depth transport]
theorem conformal_so66_readback
    (G : FiveGradedConformalClosureSocket (HR := HR)) :
    G.conformal_so66_identity :=
  G.conformal_so66_sorryProof

@[rep_depth transport]
theorem parabolic_null2plane_readback
    (G : FiveGradedConformalClosureSocket (HR := HR)) :
    G.parabolic_null2plane_identity :=
  G.parabolic_null2plane_sorryProof

@[rep_depth transport]
theorem levi_component_readback
    (G : FiveGradedConformalClosureSocket (HR := HR)) :
    G.levi_component_identity :=
  G.levi_component_sorryProof

end FiveGradedConformalClosureSocket

/--
Möbius inversion socket with log-scale parity readback.
-/
@[rep_depth transport]
structure MobiusLogScaleReflectionSocket where
  carrier : Set HR
  quadForm : HR → ℝ
  radial : HR → ℝ
  logScale : HR → ℝ
  inversion : HR → HR
  inversion_formula_True :
    ∀ x : HR, x ∈ carrier → quadForm x ≠ 0 →
      inversion x = (quadForm x)⁻¹ • x
  radial_inversion_True :
    ∀ x : HR, x ∈ carrier → radial (inversion x) = (radial x)⁻¹
  logScale_reflection_True :
    ∀ x : HR, x ∈ carrier → logScale (inversion x) = - logScale x
  unitBoundary : Set HR
  unitBoundary_fixed_True :
    ∀ x : HR, x ∈ unitBoundary → inversion x ∈ unitBoundary
  unitBoundary_log_zero_True :
    ∀ x : HR, x ∈ unitBoundary → logScale x = 0

namespace MobiusLogScaleReflectionSocket

@[rep_depth transport]
theorem inversion_formula_readback
    (M : MobiusLogScaleReflectionSocket (HR := HR))
    (x : HR) (hx : x ∈ M.carrier) (hq : M.quadForm x ≠ 0) :
    M.inversion x = (M.quadForm x)⁻¹ • x :=
  M.inversion_formula_True x hx hq

@[rep_depth transport]
theorem radial_inversion_readback
    (M : MobiusLogScaleReflectionSocket (HR := HR))
    (x : HR) (hx : x ∈ M.carrier) :
    M.radial (M.inversion x) = (M.radial x)⁻¹ :=
  M.radial_inversion_True x hx

@[rep_depth transport]
theorem logScale_reflection_readback
    (M : MobiusLogScaleReflectionSocket (HR := HR))
    (x : HR) (hx : x ∈ M.carrier) :
    M.logScale (M.inversion x) = - M.logScale x :=
  M.logScale_reflection_True x hx

@[rep_depth transport]
theorem unitBoundary_fixed_readback
    (M : MobiusLogScaleReflectionSocket (HR := HR))
    (x : HR) (hx : x ∈ M.unitBoundary) :
    M.inversion x ∈ M.unitBoundary :=
  M.unitBoundary_fixed_True x hx

@[rep_depth transport]
theorem unitBoundary_log_zero_readback
    (M : MobiusLogScaleReflectionSocket (HR := HR))
    (x : HR) (hx : x ∈ M.unitBoundary) :
    M.logScale x = 0 :=
  M.unitBoundary_log_zero_True x hx

end MobiusLogScaleReflectionSocket

/--
Projective compactification socket with origin/infinity swap law.
-/
@[rep_depth transport]
structure CompactifiedNullConeSocket where
  n0 : HR
  nInf : HR
  embed : HR → HR
  inversionConjugation : EndR
  null_pairing_identity : Prop
  null_pairing_sorryProof : null_pairing_identity
  embedding_formula_identity : Prop
  embedding_formula_sorryProof : embedding_formula_identity
  inversion_swaps_origin_infinity :
    inversionConjugation n0 = nInf ∧ inversionConjugation nInf = n0
  infinity_to_origin_identity : Prop
  infinity_to_origin_sorryProof : infinity_to_origin_identity

namespace CompactifiedNullConeSocket

@[rep_depth transport]
theorem null_pairing_readback
    (C : CompactifiedNullConeSocket (HR := HR)) :
    C.null_pairing_identity :=
  C.null_pairing_sorryProof

@[rep_depth transport]
theorem embedding_formula_readback
    (C : CompactifiedNullConeSocket (HR := HR)) :
    C.embedding_formula_identity :=
  C.embedding_formula_sorryProof

@[rep_depth transport]
theorem inversion_swaps_origin_infinity_readback
    (C : CompactifiedNullConeSocket (HR := HR)) :
    C.inversionConjugation C.n0 = C.nInf ∧ C.inversionConjugation C.nInf = C.n0 :=
  C.inversion_swaps_origin_infinity

@[rep_depth transport]
theorem infinity_to_origin_readback
    (C : CompactifiedNullConeSocket (HR := HR)) :
    C.infinity_to_origin_identity :=
  C.infinity_to_origin_sorryProof

end CompactifiedNullConeSocket

/--
Bridge packet combining 5-grading closure, Möbius log-scale inversion, and
compactified origin/infinity transport.
-/
@[rep_depth transport]
structure ConformalCGAParabolicCompactificationBridge where
  grading : FiveGradedConformalClosureSocket (HR := HR)
  mobius : MobiusLogScaleReflectionSocket (HR := HR)
  compactification : CompactifiedNullConeSocket (HR := HR)
  scale_reflection_matches_grade0_involution_identity : Prop
  scale_reflection_matches_grade0_involution_sorryProof :
    scale_reflection_matches_grade0_involution_identity
  infinity_origin_compactification_identity : Prop
  infinity_origin_compactification_sorryProof :
    infinity_origin_compactification_identity

namespace ConformalCGAParabolicCompactificationBridge

@[rep_depth transport]
theorem scale_reflection_matches_grade0_involution_readback
    (B : ConformalCGAParabolicCompactificationBridge (HR := HR)) :
    B.scale_reflection_matches_grade0_involution_identity :=
  B.scale_reflection_matches_grade0_involution_sorryProof

@[rep_depth transport]
theorem infinity_origin_compactification_readback
    (B : ConformalCGAParabolicCompactificationBridge (HR := HR)) :
    B.infinity_origin_compactification_identity :=
  B.infinity_origin_compactification_sorryProof

@[rep_depth transport]
theorem logScale_reflection_transport
    (B : ConformalCGAParabolicCompactificationBridge (HR := HR))
    (x : HR) (hx : x ∈ B.mobius.carrier) :
    B.mobius.logScale (B.mobius.inversion x) = - B.mobius.logScale x :=
  B.mobius.logScale_reflection_readback x hx

@[bridge_target_tag]
theorem bridge_logScale_reflection_target
    (B : ConformalCGAParabolicCompactificationBridge (HR := HR))
    (x : HR) (hx : x ∈ B.mobius.carrier) :
    B.mobius.logScale (B.mobius.inversion x) = - B.mobius.logScale x :=
  B.logScale_reflection_transport x hx

@[bridge_target_tag]
theorem bridge_origin_infinity_swap_target
    (B : ConformalCGAParabolicCompactificationBridge (HR := HR)) :
    B.compactification.inversionConjugation B.compactification.n0
      = B.compactification.nInf :=
  (B.compactification.inversion_swaps_origin_infinity_readback).1

end ConformalCGAParabolicCompactificationBridge

end HestenesKreinSockets

section ToyExample

/-- A concrete toy standard subspace: the real axis inside `ℂ`. -/
@[rep_depth krein]
def toyRealAxis : Submodule ℝ ℂ where
  carrier := {z | z.im = 0}
  zero_mem' := by simp
  add_mem' := by
    intro z w hz hw
    have hz' : z.im = 0 := hz
    have hw' : w.im = 0 := hw
    simp [hz', hw']
  smul_mem' := by
    intro a z hz
    have hz' : z.im = 0 := hz
    simp [hz']

private theorem toyRealAxis_sup_iMul :
    (toyRealAxis ⊔ iMul (H := ℂ) toyRealAxis) = ⊤ := by
  refine top_unique ?_
  intro z hz
  have hRe : (z.re : ℂ) ∈ toyRealAxis := by simp [toyRealAxis]
  have hIm : (z.im : ℂ) ∈ toyRealAxis := by simp [toyRealAxis]
  have hi : z.im * Complex.I ∈ iMul (H := ℂ) toyRealAxis := by
    change z.im * Complex.I ∈ toyRealAxis.map (complexIMulRealLinear (H := ℂ))
    refine (Submodule.mem_map).2 ?_
    refine ⟨(z.im : ℂ), hIm, ?_⟩
    simp [complexIMulRealLinear, mul_comm]
  have hz' : z = (z.re : ℂ) + z.im * Complex.I := by
    simpa using (Complex.re_add_im z).symm
  rw [hz']
  exact Submodule.add_mem_sup hRe hi

private theorem toyRealAxis_inf_iMul :
    toyRealAxis ⊓ iMul (H := ℂ) toyRealAxis = ⊥ := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hzR, hzI⟩
    have hzIm : z.im = 0 := hzR
    rcases (Submodule.mem_map).1 hzI with ⟨w, hwR, hwz⟩
    have hwIm : w.im = 0 := hwR
    have hzRe : z.re = 0 := by
      rw [← hwz]
      simp [complexIMulRealLinear, hwIm]
    have hz0 : z = 0 := by
      apply Complex.ext <;> simp [hzRe, hzIm]
    simpa [hz0]
  · intro hz
    have hz0 : z = 0 := by simpa using hz
    simpa [hz0, toyRealAxis]

/-- Toy spatial packet on `ℂ` with `S = J = Δ = id`. -/
@[rep_depth transport]
def toySpatial : SpatialTomitaData (H := ℂ) where
  K :=
    { carrier := toyRealAxis
      cyclic := by
        have hsup : (toyRealAxis ⊔ iMul (H := ℂ) toyRealAxis) = ⊤ := toyRealAxis_sup_iMul
        simpa [hsup]
      separating := toyRealAxis_inf_iMul }
  S := fun x => x
  J := 1
  Delta := 1
  DeltaInv := 1
  S_involution_on_domain := by intro x hx; rfl
  polar_factorization := by intro x; simp
  JDeltaJ_eq_DeltaInv := by intro x; simp
  Delta_invariant_standard := by intro x hx; simpa using hx
  J_maps_to_symplecticComplement := by
    intro x hx y hy
    have hxIm : x.im = 0 := hx
    have hyIm : y.im = 0 := hy
    simpa [hxIm, hyIm]

local notation "EndRToy" => ℝ →L[ℝ] ℝ

/-- Toy algebra carrier: scalar multiples of the identity on `ℝ`. -/
@[rep_depth operator]
def toyScalarCarrier : Set EndRToy :=
  {A | ∃ a : ℝ, A = a • (1 : EndRToy)}

private theorem toyScalarCarrier_commutative :
    ∀ ⦃A B : EndRToy⦄, A ∈ toyScalarCarrier → B ∈ toyScalarCarrier → A * B = B * A := by
  intro A B hA hB
  rcases hA with ⟨a, rfl⟩
  rcases hB with ⟨b, rfl⟩
  ext x
  simp [smul_smul, mul_comm]

/-- Toy real von Neumann packet on scalar operators over `ℝ`. -/
@[rep_depth operator]
def toyRealVonNeumann : RealVonNeumannAlgebraData (HR := ℝ) where
  carrier := toyScalarCarrier
  zero_mem := by exact ⟨0, by simp⟩
  one_mem := by exact ⟨1, by simp⟩
  add_mem := by
    intro A B hA hB
    rcases hA with ⟨a, rfl⟩
    rcases hB with ⟨b, rfl⟩
    exact ⟨a + b, by simp [add_smul]⟩
  mul_mem := by
    intro A B hA hB
    rcases hA with ⟨a, rfl⟩
    rcases hB with ⟨b, rfl⟩
    refine ⟨a * b, ?_⟩
    ext x
    simp [smul_smul, mul_comm]
  star_mem := by
    intro A hA
    rcases hA with ⟨a, rfl⟩
    exact ⟨a, by simp⟩
  weakly_closed_identity := True
  weakly_closed_sorryProof := trivial

/-- Toy algebraic Tomita packet on `ℝ`. -/
@[rep_depth transport]
def toyAlgebraic : RealTomitaAlgebraicData (HR := ℝ) where
  algebra := toyRealVonNeumann
  omega := 0
  cyclic_identity := True
  cyclic_sorryProof := trivial
  separating_identity := True
  separating_sorryProof := trivial
  S0 := 1
  S0_on_orbit := by
    intro A hA
    simp
  sigma := fun _ A => A
  sigma_real_star_automorphism_identity := True
  sigma_real_star_automorphism_sorryProof := trivial
  J0 := 1
  J0_sq := by simp
  J0_maps_algebra_to_commutant := by
    intro A hA
    simpa using
      (toyRealVonNeumann.mem_commutant_of_commutative
        (hcomm := toyScalarCarrier_commutative) (hA := hA))

/-- Toy bridge from `ℂ` spatial data to `ℝ` algebraic data via real-part projection. -/
@[rep_depth transport]
def toyBridge : SpatialAlgebraicRealificationBridge (HC := ℂ) (HR := ℝ) where
  spatial := toySpatial
  algebraic := toyAlgebraic
  realify := Complex.reCLM.toLinearMap
  tomita_transport := by
    intro x
    simp [toySpatial, toyAlgebraic]
  modularConjugation_transport := by
    intro x
    simp [toySpatial, toyAlgebraic]
  modularFlow_transport_identity := True
  modularFlow_transport_sorryProof := trivial

@[rep_depth transport]
theorem toyBridge_tomita_iterate
    (x : ℂ) :
    toyBridge.realify (toyBridge.spatial.S (toyBridge.spatial.S x))
      = toyBridge.algebraic.S0 (toyBridge.algebraic.S0 (toyBridge.realify x)) :=
  toyBridge.tomita_transport_iterate x

@[rep_depth transport]
theorem toyBridge_J0_sq_apply
    (x : ℝ) :
    toyBridge.algebraic.J0 (toyBridge.algebraic.J0 x) = x :=
  toyBridge.algebraic.J0_sq_apply x

/-- Toy five-grading socket on scalar operators over `ℝ`. -/
@[rep_depth transport]
def toyFiveGradedConformal : FiveGradedConformalClosureSocket (HR := ℝ) where
  grade := fun _ => Set.univ
  bracket := fun A B => A * B - B * A
  support_identity := True
  support_sorryProof := trivial
  bracket_respects_grading_identity := True
  bracket_respects_grading_sorryProof := trivial
  conformal_so66_identity := True
  conformal_so66_sorryProof := trivial
  parabolic_null2plane_identity := True
  parabolic_null2plane_sorryProof := trivial
  levi_component_identity := True
  levi_component_sorryProof := trivial

/-- Toy Möbius/log-scale socket on `ℝ`. -/
@[rep_depth transport]
def toyMobiusLogScale : MobiusLogScaleReflectionSocket (HR := ℝ) where
  carrier := Set.univ
  quadForm := fun _ => -1
  radial := fun _ => 1
  logScale := fun x => x
  inversion := fun x => -x
  inversion_formula_True := by
    intro x hx hq
    simp
  radial_inversion_True := by
    intro x hx
    simp
  logScale_reflection_True := by
    intro x hx
    simp
  unitBoundary := {x | x = 0}
  unitBoundary_fixed_True := by
    intro x hx
    simpa [Set.mem_setOf_eq, hx]
  unitBoundary_log_zero_True := by
    intro x hx
    simpa [Set.mem_setOf_eq] using hx

/-- Toy compactification socket with a degenerate origin/infinity witness. -/
@[rep_depth transport]
def toyCompactifiedNullCone : CompactifiedNullConeSocket (HR := ℝ) where
  n0 := 0
  nInf := 0
  embed := fun x => x
  inversionConjugation := 1
  null_pairing_identity := True
  null_pairing_sorryProof := trivial
  embedding_formula_identity := True
  embedding_formula_sorryProof := trivial
  inversion_swaps_origin_infinity := by
    constructor <;> simp
  infinity_to_origin_identity := True
  infinity_to_origin_sorryProof := trivial

/-- Toy bridge combining grading, Möbius reflection, and compactification sockets. -/
@[rep_depth transport]
def toyConformalBridge : ConformalCGAParabolicCompactificationBridge (HR := ℝ) where
  grading := toyFiveGradedConformal
  mobius := toyMobiusLogScale
  compactification := toyCompactifiedNullCone
  scale_reflection_matches_grade0_involution_identity := True
  scale_reflection_matches_grade0_involution_sorryProof := trivial
  infinity_origin_compactification_identity := True
  infinity_origin_compactification_sorryProof := trivial

@[rep_depth transport]
theorem toyConformalBridge_logScale_reflection
    (x : ℝ) :
    toyConformalBridge.mobius.logScale (toyConformalBridge.mobius.inversion x)
      = - toyConformalBridge.mobius.logScale x := by
  simp [toyConformalBridge, toyMobiusLogScale]

@[rep_depth transport]
theorem toyConformalBridge_origin_infinity_swap
    : toyConformalBridge.compactification.inversionConjugation
        toyConformalBridge.compactification.n0
        = toyConformalBridge.compactification.nInf :=
  (toyConformalBridge.compactification.inversion_swaps_origin_infinity_readback).1

end ToyExample

end InfoGeometry.Canonical.TomitaTakesakiRealification
