import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget

open scoped InnerProductSpace

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
- `symplecticComplement`: Constructive definition satisfying submodule axioms exactly.
- `one_mem_commutant`, `zero_mem_commutant`, `commutant_mul_eq`, `mem_commutant_of_commutative`: Exact algebraic relations for the real commutant.
- `J_maps_K_to_dual`: Trivial set-image membership.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[Theorems that compile conditionally based on explicitly named, valid premises or external verified witnesses. No hidden assumptions.]
- `tomita_transport_iterate`, `tomita_transport_involution_on_domain`, `modularConjugation_transport_iterate`: Theorems that compile and chain conditionally by composing downstream structural readback theorems.

#### BUCKET 3: OPEN CLOSURE DEBT
[Identified gaps, missing structural steps, or unverified steps. This defines the exact remaining debt line. No overclaims permitted.]
- Tomita--Takesaki structural readbacks: `isStandard`, `involution_readback`, `polar_factorization_readback`, `duality_readback`, `invariant_standard_readback`, `symplectic_duality_readback`, `weakly_closed`, `cyclic`, `separating`, `S0_on_orbit_readback`, `sigma_real_star_automorphism`, `J0_commutant_transport`, `J0_sq_apply`.
- Realification bridge readbacks: `tomita_transport_readback`, `modularConjugation_transport_readback`, `modularFlow_transport_readback`.
- Hestenes--Krein and CGA closure readbacks: `pseudoscalar_sq_neg_one_readback`, `reversion_involutive_readback`, `reversion_mul_readback`, `tomita_reversion_readback`, `kreinAdjoint_involutive`, `imag_part_as_pseudoscalar_component`, `drazin_idempotent`, `moorePenrose_idempotent`, `grading_split`, `closure_repaired`, `modular_stability_on_bulk`.
- Conformal/Parabolic closure readbacks: `support`, `bracket_respects_grading`, `conformal_so66`, `parabolic_null2plane`, `levi_component`.
- Mobius/Log-Scale and Infinity readbacks: `inversion_formula`, `radial_inversion`, `logScale_reflection`, `unitBoundary_fixed`, `unitBoundary_log_zero`, `null_pairing`, `embedding_formula`, `inversion_swaps_origin_infinity_readback`.
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

namespace StandardSubspace

/-- Standardness readback. -/
@[rep_depth krein]
theorem isStandard (K : StandardSubspace (H := H)) :
    IsStandardSubspace (H := H) K.carrier := by
  sorry

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

namespace SpatialTomitaData

@[rep_depth transport]
theorem involution_readback
    (T : SpatialTomitaData (H := H))
    (x : H) (hx : x ∈ T.K.tomitaDomain) :
    T.S (T.S x) = x := by
  sorry

@[rep_depth transport]
theorem polar_factorization_readback
    (T : SpatialTomitaData (H := H))
    (x : H) :
    T.S x = T.J (T.Delta x) := by
  sorry

@[rep_depth transport]
theorem duality_readback
    (T : SpatialTomitaData (H := H))
    (x : H) :
    T.J (T.Delta (T.J x)) = T.DeltaInv x := by
  sorry

@[rep_depth transport]
theorem invariant_standard_readback
    (T : SpatialTomitaData (H := H))
    (x : H) (hx : x ∈ T.K.carrier) :
    T.Delta x ∈ T.K.carrier := by
  sorry

@[rep_depth transport]
theorem symplectic_duality_readback
    (T : SpatialTomitaData (H := H))
    (x : H) (hx : x ∈ T.K.carrier) :
    T.J x ∈ symplecticComplement (H := H) T.K.carrier := by
  sorry

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

namespace RealVonNeumannAlgebraData

@[rep_depth operator]
def commutant (R : RealVonNeumannAlgebraData (HR := HR)) : Set EndR :=
  realCommutant (HR := HR) R.carrier

@[rep_depth operator]
theorem weakly_closed
    (R : RealVonNeumannAlgebraData (HR := HR)) :
    closure R.carrier = R.carrier := by
  sorry

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
  S0 : EndR
  sigma : ℝ → EndR → EndR
  J0 : EndR

namespace RealTomitaAlgebraicData

@[rep_depth transport]
theorem cyclic
    (T : RealTomitaAlgebraicData (HR := HR)) :
    (Submodule.span ℝ (Set.image (λ A : EndR => A T.omega) T.algebra.carrier)).topologicalClosure = ⊤ := by
  sorry

@[rep_depth transport]
theorem separating
    (T : RealTomitaAlgebraicData (HR := HR)) :
    ∀ A : EndR, A ∈ T.algebra.carrier → A T.omega = 0 → A = 0 := by
  sorry

@[rep_depth transport]
theorem S0_on_orbit_readback
    (T : RealTomitaAlgebraicData (HR := HR))
    (A : EndR) (hA : A ∈ T.algebra.carrier) :
    T.S0 (A T.omega) = (star A) T.omega := by
  sorry

@[rep_depth transport]
theorem sigma_real_star_automorphism
    (T : RealTomitaAlgebraicData (HR := HR)) :
    (∀ t : ℝ, T.sigma t (1 : EndR) = (1 : EndR)) ∧
    (∀ t : ℝ, ∀ A B : EndR, T.sigma t (A * B) = T.sigma t A * T.sigma t B) ∧
    (∀ t : ℝ, ∀ A : EndR, T.sigma t (star A) = star (T.sigma t A)) ∧
    (∀ t : ℝ, ∀ A : EndR, A ∈ T.algebra.carrier → T.sigma t A ∈ T.algebra.carrier) := by
  sorry

@[rep_depth transport]
theorem J0_commutant_transport
    (T : RealTomitaAlgebraicData (HR := HR))
    (A : EndR) (hA : A ∈ T.algebra.carrier) :
    T.J0 * A * T.J0 ∈ T.algebra.commutant := by
  sorry

@[rep_depth transport]
theorem J0_sq_apply
    (T : RealTomitaAlgebraicData (HR := HR))
    (x : HR) :
    T.J0 (T.J0 x) = x := by
  sorry

/--
A minimal algebraic socket builder from a carrier.  The Tomita/KMS laws are
explicit theorem owners on `RealTomitaAlgebraicData`, not fields supplied here.
-/
@[rep_depth transport]
def ofCommutativeCarrier
    (R : RealVonNeumannAlgebraData (HR := HR)) :
    RealTomitaAlgebraicData (HR := HR) where
  algebra := R
  omega := 0
  S0 := 0
  sigma := fun _ A => A
  J0 := 1

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

namespace SpatialAlgebraicRealificationBridge

@[rep_depth transport]
theorem tomita_transport_readback
    (B : SpatialAlgebraicRealificationBridge (HC := HC) (HR := HR))
    (x : HC) :
    B.realify (B.spatial.S x) = B.algebraic.S0 (B.realify x) := by
  sorry

@[rep_depth transport]
theorem modularConjugation_transport_readback
    (B : SpatialAlgebraicRealificationBridge (HC := HC) (HR := HR))
    (x : HC) :
    B.realify (B.spatial.J x) = B.algebraic.J0 (B.realify x) := by
  sorry

@[rep_depth transport]
theorem modularFlow_transport_readback
    (B : SpatialAlgebraicRealificationBridge (HC := HC) (HR := HR))
    (x : HC) :
    B.realify (B.spatial.Delta (B.spatial.J x)) =
      B.algebraic.J0 (B.realify (B.spatial.Delta x)) := by
  sorry

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
            simpa [B.spatial.involution_readback x hx]
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
  reversionOp : EndR → EndR

namespace HestenesGeometricComplexData

@[rep_depth krein]
def iMulGA (G : HestenesGeometricComplexData (HR := HR)) (A : EndR) : EndR :=
  G.pseudoscalar * A

@[rep_depth krein]
theorem pseudoscalar_sq_neg_one_readback
    (G : HestenesGeometricComplexData (HR := HR)) :
    G.pseudoscalar * G.pseudoscalar = -(1 : EndR) := by
  sorry

@[rep_depth krein]
theorem reversion_involutive_readback
    (G : HestenesGeometricComplexData (HR := HR))
    (A : EndR) :
    G.reversionOp (G.reversionOp A) = A := by
  sorry

@[rep_depth krein]
theorem reversion_mul_readback
    (G : HestenesGeometricComplexData (HR := HR))
    (A B : EndR) :
    G.reversionOp (A * B) = G.reversionOp B * G.reversionOp A := by
  sorry

@[rep_depth krein]
theorem tomita_reversion_readback
    (G : HestenesGeometricComplexData (HR := HR))
    (A : EndR) :
    G.reversionOp (G.pseudoscalar * A * G.pseudoscalar) =
      G.pseudoscalar * G.reversionOp A * G.pseudoscalar := by
  sorry

end HestenesGeometricComplexData

/--
Krein-adjoint socket in the Hestenes language.

`η` is the fundamental symmetry. The carrier stores only the primitive
conjugation data; involutivity of the Krein adjoint is a theorem.
-/
@[rep_depth krein]
structure KreinAdjointSocket where
  geometric : HestenesGeometricComplexData (HR := HR)
  eta : EndR

namespace KreinAdjointSocket

@[rep_depth krein]
def kreinAdjoint
    (K : KreinAdjointSocket (HR := HR))
    (A : EndR) : EndR :=
  K.eta * K.geometric.reversionOp A * K.eta

@[rep_depth krein]
theorem kreinAdjoint_involutive
    (K : KreinAdjointSocket (HR := HR))
    (A : EndR) :
    K.kreinAdjoint (K.kreinAdjoint A) = A := by
  sorry

end KreinAdjointSocket


/--
Symplectic-duality socket rewritten in GA language.

The classical `Im ⟪·,·⟫ = 0` condition is recorded as a pseudoscalar-component
law and `J` transports `K` to its GA dual sector.
-/
@[rep_depth transport]
structure GASymplecticDualitySocket where
  K : Set HR
  J : EndR

namespace GASymplecticDualitySocket

@[rep_depth transport]
def Kdual
    (S : GASymplecticDualitySocket (HR := HR)) : Set HR :=
  S.J '' S.K

@[rep_depth transport]
theorem J_maps_K_to_dual
    (S : GASymplecticDualitySocket (HR := HR))
    (x : HR)
    (hx : x ∈ S.K) :
    S.J x ∈ S.Kdual := by
  exact ⟨x, hx, rfl⟩

@[rep_depth transport]
theorem imag_part_as_pseudoscalar_component
    (S : GASymplecticDualitySocket (HR := HR))
    (x y : HR) :
    ⟪x, S.J y⟫_ℝ = -⟪S.J x, y⟫_ℝ := by
  sorry

end GASymplecticDualitySocket


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

namespace CausalConeProjectorRegularization

@[rep_depth transport]
theorem drazin_idempotent
    (C : CausalConeProjectorRegularization (HR := HR)) :
    C.drazinProjector * C.drazinProjector = C.drazinProjector := by
  sorry

@[rep_depth transport]
theorem moorePenrose_idempotent
    (C : CausalConeProjectorRegularization (HR := HR)) :
    C.moorePenroseProjector * C.moorePenroseProjector = C.moorePenroseProjector := by
  sorry

@[rep_depth transport]
theorem grading_split
    (C : CausalConeProjectorRegularization (HR := HR)) :
    C.drazinProjector + C.moorePenroseProjector = 1 := by
  sorry

@[rep_depth transport]
theorem closure_repaired
    (C : CausalConeProjectorRegularization (HR := HR)) :
    C.moorePenroseProjector * C.drazinProjector = 0 ∧
      C.drazinProjector * C.moorePenroseProjector = 0 := by
  sorry

@[rep_depth transport]
theorem modular_stability_on_bulk
    (C : CausalConeProjectorRegularization (HR := HR)) :
    C.drazinProjector * C.moorePenroseProjector = 0 ∧
      C.moorePenroseProjector * C.drazinProjector = 0 := by
  sorry

end CausalConeProjectorRegularization

/--
Parabolic five-grading socket for conformal closure.

This packet records only the five graded pieces and an abstract bracket.  The
closure laws below are theorem owners: either proved in this file or left as
explicit `sorry` debt.
-/
@[rep_depth transport]
structure FiveGradedConformalClosureSocket where
  grade : Int → Set EndR
  bracket : EndR → EndR → EndR

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
theorem support
    (G : FiveGradedConformalClosureSocket (HR := HR)) :
    ∀ A : EndR, A ∈ Submodule.span ℝ (⋃ (i : Int), G.grade i) := by
  sorry

@[rep_depth transport]
theorem bracket_respects_grading
    (G : FiveGradedConformalClosureSocket (HR := HR)) :
    ∀ (i j : Int) (A B : EndR),
      A ∈ G.grade i → B ∈ G.grade j → G.bracket A B ∈ G.grade (i + j) := by
  sorry

@[rep_depth transport]
theorem conformal_so66
    (G : FiveGradedConformalClosureSocket (HR := HR)) :
    (∀ A B C : EndR,
      G.bracket A (G.bracket B C) +
          G.bracket B (G.bracket C A) +
          G.bracket C (G.bracket A B) = 0) ∧
      (G.grade (-2)).Nonempty ∧ (G.grade 2).Nonempty ∧
        (G.grade (-1)).Nonempty ∧ (G.grade 1).Nonempty ∧
          (G.grade 0).Nonempty := by
  sorry

@[rep_depth transport]
theorem parabolic_null2plane
    (G : FiveGradedConformalClosureSocket (HR := HR)) :
    (∀ (A : EndR) (B : EndR),
      A ∈ G.grade 0 → B ∈ G.grade 1 → G.bracket A B ∈ G.grade 1) ∧
      (∀ (A : EndR) (B : EndR),
        A ∈ G.grade 0 → B ∈ G.grade 2 → G.bracket A B ∈ G.grade 2) := by
  sorry

@[rep_depth transport]
theorem levi_component
    (G : FiveGradedConformalClosureSocket (HR := HR)) :
    (∀ (A B : EndR),
      A ∈ G.grade 0 → B ∈ G.grade 0 → G.bracket A B ∈ G.grade 0) ∧
      (∀ (A B : EndR),
        A ∈ G.grade 1 → B ∈ G.grade 1 → G.bracket A B ∈ G.grade 2) := by
  sorry

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
  unitBoundary : Set HR

namespace MobiusLogScaleReflectionSocket

@[rep_depth transport]
theorem inversion_formula
    (M : MobiusLogScaleReflectionSocket (HR := HR))
    (x : HR) (hx : x ∈ M.carrier) (hq : M.quadForm x ≠ 0) :
    M.inversion x = (M.quadForm x)⁻¹ • x := by
  sorry

@[rep_depth transport]
theorem radial_inversion
    (M : MobiusLogScaleReflectionSocket (HR := HR))
    (x : HR) (hx : x ∈ M.carrier) :
    M.radial (M.inversion x) = (M.radial x)⁻¹ := by
  sorry

@[rep_depth transport]
theorem logScale_reflection
    (M : MobiusLogScaleReflectionSocket (HR := HR))
    (x : HR) (hx : x ∈ M.carrier) :
    M.logScale (M.inversion x) = - M.logScale x := by
  sorry

@[rep_depth transport]
theorem unitBoundary_fixed
    (M : MobiusLogScaleReflectionSocket (HR := HR))
    (x : HR) (hx : x ∈ M.unitBoundary) :
    M.inversion x ∈ M.unitBoundary := by
  sorry

@[rep_depth transport]
theorem unitBoundary_log_zero
    (M : MobiusLogScaleReflectionSocket (HR := HR))
    (x : HR) (hx : x ∈ M.unitBoundary) :
    M.logScale x = 0 := by
  sorry

end MobiusLogScaleReflectionSocket

/--
Projective compactification data.  The origin/infinity swap is a theorem owner
below, not a proof field of the data.
-/
@[rep_depth transport]
structure CompactifiedNullConeSocket where
  n0 : HR
  nInf : HR
  embed : HR → HR
  inversionConjugation : EndR

namespace CompactifiedNullConeSocket

@[rep_depth transport]
theorem null_pairing
    (C : CompactifiedNullConeSocket (HR := HR)) :
    ⟪C.n0, C.nInf⟫_ℝ = 0 := by
  sorry

@[rep_depth transport]
theorem embedding_formula
    (C : CompactifiedNullConeSocket (HR := HR)) :
    ⟪C.embed C.n0, C.nInf⟫_ℝ = 0 := by
  sorry

@[rep_depth transport]
theorem inversion_swaps_origin_infinity_readback
    (C : CompactifiedNullConeSocket (HR := HR)) :
    C.inversionConjugation C.n0 = C.nInf ∧ C.inversionConjugation C.nInf = C.n0 := by
  sorry

@[rep_depth transport]
theorem infinity_to_origin
    (C : CompactifiedNullConeSocket (HR := HR)) :
    C.inversionConjugation C.nInf = C.n0 :=
  C.inversion_swaps_origin_infinity_readback.2

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

namespace ConformalCGAParabolicCompactificationBridge

@[rep_depth transport]
theorem scale_reflection_matches_grade0_involution
    (B : ConformalCGAParabolicCompactificationBridge (HR := HR)) :
    ∀ x : HR, x ∈ B.mobius.unitBoundary → B.mobius.inversion x ∈ B.mobius.unitBoundary :=
  B.mobius.unitBoundary_fixed

@[rep_depth transport]
theorem infinity_origin_compactification
    (B : ConformalCGAParabolicCompactificationBridge (HR := HR)) :
    B.compactification.inversionConjugation B.compactification.n0 =
      B.compactification.nInf :=
  B.compactification.inversion_swaps_origin_infinity_readback.1

@[rep_depth transport]
theorem logScale_reflection_transport
    (B : ConformalCGAParabolicCompactificationBridge (HR := HR))
    (x : HR) (hx : x ∈ B.mobius.carrier) :
    B.mobius.logScale (B.mobius.inversion x) = - B.mobius.logScale x :=
  B.mobius.logScale_reflection x hx

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

end InfoGeometry.Canonical.TomitaTakesakiRealification
