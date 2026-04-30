/-
InfoGeometry/Canonical/PauliHestenesSpinMomentum.lean

Pauli/Hestenes spin-momentum dictionary.

This module records the precise representation-theoretic socket:

* energy-momentum is a paravector readout;
* the Pauli matrix determinant is the Minkowski norm;
* null momentum is singular/projective, not automatically nilpotent;
* spin is a bivector/rotor readout carried by the spinor frame;
* spin-momentum coupling is supplied by a proof-carrying Lorentz/spin
  calibration.
-/

import Mathlib
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Canonical.HestenesKreinModularGeometry
import InfoGeometry.OperatorAlgebra.OperatorChiralLightcone
import InfoGeometry.Meta.Architecture

noncomputable section

namespace InfoGeometry.Canonical.PauliHestenesSpinMomentum

open scoped Matrix

/-! ## 1. Pauli/Hestenes paravectors -/

/--
Energy-momentum paravector coordinates.

This is the real Hestenes/Pauli shadow of `P = E + p`.
-/
@[rep_depth operator]
structure PauliParavector where
  /-- Energy/time component. -/
  energy : ℝ
  /-- Spatial `x` momentum component. -/
  px : ℝ
  /-- Spatial `y` momentum component. -/
  py : ℝ
  /-- Spatial `z` momentum component. -/
  pz : ℝ

namespace PauliParavector

/-- Minkowski norm square `E² - |p|²`. -/
def minkowskiNormSq
    (P : PauliParavector) : ℝ :=
  P.energy ^ 2 - P.px ^ 2 - P.py ^ 2 - P.pz ^ 2

/--
Hermitian Pauli matrix of a real paravector:

`[[E + pz, px - i py], [px + i py, E - pz]]`.
-/
def pauliMatrix
    (P : PauliParavector) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![((P.energy + P.pz : ℝ) : ℂ),
      ((P.px : ℂ) - Complex.I * (P.py : ℂ));
     ((P.px : ℂ) + Complex.I * (P.py : ℂ)),
      ((P.energy - P.pz : ℝ) : ℂ)]

/--
The determinant of the Pauli matrix is the Minkowski norm.
-/
theorem det_pauliMatrix_eq_minkowskiNormSq
    (P : PauliParavector) :
    Matrix.det P.pauliMatrix = (P.minkowskiNormSq : ℂ) := by
  simp [pauliMatrix, minkowskiNormSq, Matrix.det_fin_two]
  ring_nf
  rw [Complex.I_sq]
  ring

/--
Null/lightlike momentum means zero Minkowski norm.
-/
def IsNull
    (P : PauliParavector) : Prop :=
  P.minkowskiNormSq = 0

/--
The Pauli representative is singular when its determinant vanishes.
-/
def IsSingularPauli
    (P : PauliParavector) : Prop :=
  Matrix.det P.pauliMatrix = 0

/--
Null paravectors are exactly singular Pauli representatives.

This is the safe replacement for the overstrong slogan
"null momentum is nilpotent."
-/
theorem isNull_iff_isSingularPauli
    (P : PauliParavector) :
    P.IsNull ↔ P.IsSingularPauli := by
  constructor
  · intro h
    dsimp [IsNull, IsSingularPauli] at h ⊢
    rw [det_pauliMatrix_eq_minkowskiNormSq, h]
    norm_num
  · intro h
    dsimp [IsNull, IsSingularPauli] at h ⊢
    rw [det_pauliMatrix_eq_minkowskiNormSq] at h
    exact_mod_cast h

/--
A mass-shell certificate.

The equation is `P P̄ = m²`, expressed in the Pauli/Hestenes paravector lane as
`E² - |p|² = m²`.
-/
def OnMassShell
    (P : PauliParavector)
    (mass : ℝ) : Prop :=
  P.minkowskiNormSq = mass ^ 2

/--
The massless shell is exactly the null shell.
-/
theorem onMassShell_zero_iff_isNull
    (P : PauliParavector) :
    P.OnMassShell 0 ↔ P.IsNull := by
  simp [OnMassShell, IsNull]

end PauliParavector

/-! ## 2. Abstract Pauli/paravector bridge -/

/--
Abstract Pauli/paravector bridge.

This is the generic socket for models that do not want to commit to the
concrete `2 × 2` complex matrix representation immediately.
-/
@[rep_depth operator]
structure PauliParavectorBridge
    (V Herm2 : Type*) where
  /-- Pauli/Hermitian representative of a vector/paravector. -/
  pauliMap : V → Herm2

  /-- Minkowski/paravector norm readout. -/
  minkowskiNorm : V → ℝ

  /-- Determinant readout on the Hermitian representative. -/
  det : Herm2 → ℝ

  /-- The determinant recovers the Minkowski norm. -/
  det_pauliMap :
    ∀ X : V, det (pauliMap X) = minkowskiNorm X

namespace PauliParavectorBridge

variable {V Herm2 : Type*}
variable (B : PauliParavectorBridge V Herm2)

/-- Null vectors/paravectors are zero-norm elements. -/
def IsNull
    (X : V) : Prop :=
  B.minkowskiNorm X = 0

/-- Singular Pauli/Hermitian representatives have zero determinant. -/
def IsSingularRepresentative
    (X : V) : Prop :=
  B.det (B.pauliMap X) = 0

/--
Nullness is equivalent to singularity of the Pauli representative.
-/
theorem isNull_iff_isSingularRepresentative
    (X : V) :
    B.IsNull X ↔ B.IsSingularRepresentative X := by
  unfold IsNull IsSingularRepresentative
  rw [B.det_pauliMap X]

end PauliParavectorBridge

/--
The concrete Pauli matrix construction as an instance of the abstract bridge.
-/
def concretePauliParavectorBridge :
    PauliParavectorBridge PauliParavector (Matrix (Fin 2) (Fin 2) ℂ) where
  pauliMap := PauliParavector.pauliMatrix
  minkowskiNorm := PauliParavector.minkowskiNormSq
  det := fun M => (Matrix.det M).re
  det_pauliMap := by
    intro P
    rw [PauliParavector.det_pauliMatrix_eq_minkowskiNormSq]
    simp

/-! ## 3. Lorentz-spin action and spinor-helicity sockets -/

/--
Lorentz-spin action on a Pauli/paravector bridge.

This abstracts the formula `X ↦ L X L†` with `L ∈ SL(2,ℂ)`.  The essential
law at this layer is determinant/Minkowski-norm preservation.
-/
@[rep_depth operator]
structure LorentzSpinActionBridge
    (SpinGroup V Herm2 : Type*)
    (B : PauliParavectorBridge V Herm2) where
  /-- Spin-group action on vector/paravector data. -/
  actVector : SpinGroup → V → V

  /-- Induced action on Pauli/Hermitian representatives. -/
  actHermitian : SpinGroup → Herm2 → Herm2

  /-- Compatibility of the vector and Hermitian actions. -/
  pauliMap_equivariant :
    ∀ (L : SpinGroup) (X : V),
      B.pauliMap (actVector L X) = actHermitian L (B.pauliMap X)

  /-- Determinant/Minkowski norm is preserved by the spin action. -/
  det_preserved :
    ∀ (L : SpinGroup) (X : V),
      B.det (B.pauliMap (actVector L X)) = B.det (B.pauliMap X)

  /--
  Double-cover law.

  Intended concrete meaning: `L` and `-L` induce the same Lorentz action.
  -/
  double_cover_law : Prop

  /-- Proof of the double-cover law. -/
  double_cover_certificate :
    double_cover_law

namespace LorentzSpinActionBridge

variable {SpinGroup V Herm2 : Type*}
variable {B : PauliParavectorBridge V Herm2}
variable (A : LorentzSpinActionBridge SpinGroup V Herm2 B)

/-- The spin action preserves the Minkowski/paravector norm. -/
theorem minkowskiNorm_preserved
    (L : SpinGroup)
    (X : V) :
    B.minkowskiNorm (A.actVector L X) = B.minkowskiNorm X := by
  calc
    B.minkowskiNorm (A.actVector L X)
        = B.det (B.pauliMap (A.actVector L X)) :=
            (B.det_pauliMap (A.actVector L X)).symm
    _ = B.det (B.pauliMap X) :=
            A.det_preserved L X
    _ = B.minkowskiNorm X :=
            B.det_pauliMap X

/-- The spin action preserves nullness. -/
theorem isNull_of_isNull
    (L : SpinGroup)
    {X : V}
    (hX : B.IsNull X) :
    B.IsNull (A.actVector L X) := by
  unfold PauliParavectorBridge.IsNull at hX ⊢
  rw [A.minkowskiNorm_preserved L X]
  exact hX

/-- The stored double-cover law. -/
theorem double_cover_valid :
    A.double_cover_law :=
  A.double_cover_certificate

end LorentzSpinActionBridge

/--
Spinor-helicity factorization of a null Pauli representative.

For a massless branch, the Hermitian momentum representative is generated by a
spinor line, morally `P = λ λ†`.  This is carried as a witness because the
concrete conjugation/outer-product API is model-specific.
-/
@[rep_depth operator]
structure SpinorHelicityFactorization
    (Spinor V Herm2 : Type*)
    (B : PauliParavectorBridge V Herm2) where
  /-- Momentum/paravector readout of a spinor. -/
  momentumOf : Spinor → V

  /-- Outer-product representative, morally `λ λ†`. -/
  outerProduct : Spinor → Herm2

  /-- Spinor-helicity factorization of the Pauli representative. -/
  pauli_eq_outerProduct :
    ∀ lam : Spinor,
      B.pauliMap (momentumOf lam) = outerProduct lam

  /-- The spinor-helicity branch is null. -/
  momentum_null :
    ∀ lam : Spinor,
      B.IsNull (momentumOf lam)

  /-- The outer-product/rank-one interpretation law. -/
  rank_one_law : Prop

  /-- Proof of the rank-one interpretation law. -/
  rank_one_certificate :
    rank_one_law

namespace SpinorHelicityFactorization

variable {Spinor V Herm2 : Type*}
variable {B : PauliParavectorBridge V Herm2}
variable (F : SpinorHelicityFactorization Spinor V Herm2 B)

/-- Spinor-helicity representatives are singular. -/
theorem singular_representative
    (lam : Spinor) :
    B.IsSingularRepresentative (F.momentumOf lam) :=
  (B.isNull_iff_isSingularRepresentative (F.momentumOf lam)).mp
    (F.momentum_null lam)

/-- The stored rank-one law. -/
theorem rank_one_valid :
    F.rank_one_law :=
  F.rank_one_certificate

end SpinorHelicityFactorization

/-! ## 4. Spin is a rotor/bivector readout, not a paravector component -/

/--
Operator-valued Pauli paravector datum.

This is the abstract operator socket for a four-momentum/paravector
representative. It deliberately does not include spin data.
-/
@[rep_depth operator]
structure PauliParavectorDatum
    (Op : Type*) where
  /-- Operator/paravector representative of four-momentum. -/
  P : Op

  /-- Minkowski norm or mass-shell readout. -/
  minkowskiNorm : ℝ

  /-- Determinant/metric calibration law. -/
  determinant_metric_law : Prop

  /-- Proof of the determinant/metric calibration law. -/
  determinant_metric_certificate :
    determinant_metric_law

namespace PauliParavectorDatum

variable {Op : Type*}
variable (P : PauliParavectorDatum Op)

/-- The stored determinant/metric calibration law. -/
theorem determinant_metric_valid :
    P.determinant_metric_law :=
  P.determinant_metric_certificate

end PauliParavectorDatum

/--
Spin-momentum frame.

Momentum is the paravector datum. Spin is a bivector/rotor-frame datum. They
are coupled because the same rotor frame transports both.
-/
@[rep_depth operator]
structure SpinMomentumFrame
    (Op : Type*) where
  /-- Four-momentum/paravector datum. -/
  momentum : PauliParavectorDatum Op

  /-- Rotor/spinor frame element. -/
  rotor : Op

  /-- Spin plane/bivector readout. -/
  spinBivector : Op

  /-- Law saying the rotor transports the momentum paravector. -/
  momentum_transport_law : Prop

  /-- Proof of the momentum transport law. -/
  momentum_transport :
    momentum_transport_law

  /-- Law saying the same rotor transports the spin bivector/plane. -/
  spin_transport_law : Prop

  /-- Proof of the spin transport law. -/
  spin_transport :
    spin_transport_law

namespace SpinMomentumFrame

variable {Op : Type*}
variable (F : SpinMomentumFrame Op)

/-- The stored momentum transport law. -/
theorem momentum_transport_valid :
    F.momentum_transport_law :=
  F.momentum_transport

/-- The stored spin transport law. -/
theorem spin_transport_valid :
    F.spin_transport_law :=
  F.spin_transport

end SpinMomentumFrame

/--
Representation-theoretic spin-momentum coupling.

This records the precise reason momentum and spin are inseparable in the
Pauli/Hestenes picture: the same Lorentz spin group transports the paravector
momentum datum and the spin bivector datum.

It does not identify spin with a component of the momentum paravector.
-/
@[rep_depth operator]
structure LorentzSpinRepresentationCoupling
    (SpinGroup Op : Type*) where
  /-- The spin-momentum frame being transported. -/
  frame : SpinMomentumFrame Op

  /-- Spin-group action on momentum/paravector data. -/
  actMomentum :
    SpinGroup → PauliParavectorDatum Op → PauliParavectorDatum Op

  /-- Spin-group action on the spin bivector/plane readout. -/
  actSpinBivector :
    SpinGroup → Op → Op

  /--
  Shared-action law.

  Intended concrete meaning: the same `SL(2,C)`/`Spin⁺(1,3)` element transports
  the momentum paravector and the spin bivector.
  -/
  shared_spin_action_law : Prop

  /-- Proof of the shared-action law. -/
  shared_spin_action :
    shared_spin_action_law

  /--
  Representation-coupling law.

  Intended concrete meaning: momentum and spin are coupled by the common
  Lorentz-spin representation, not by being different parts of one matrix.
  -/
  representation_coupling_law : Prop

  /-- Proof of the representation-coupling law. -/
  representation_coupling :
    representation_coupling_law

namespace LorentzSpinRepresentationCoupling

variable {SpinGroup Op : Type*}
variable (C : LorentzSpinRepresentationCoupling SpinGroup Op)

/-- The stored shared spin-group action law. -/
theorem shared_spin_action_valid :
    C.shared_spin_action_law :=
  C.shared_spin_action

/-- The stored representation-theoretic coupling law. -/
theorem representation_coupling_valid :
    C.representation_coupling_law :=
  C.representation_coupling

end LorentzSpinRepresentationCoupling

/--
Massless spin-momentum frame.

For massless/null branches, the momentum datum has zero Minkowski norm and the
spin readout is helicity locked to the null momentum direction.
-/
@[rep_depth operator]
structure MasslessSpinMomentumFrame
    (Op : Type*) where
  /-- Underlying spin-momentum frame. -/
  frame : SpinMomentumFrame Op

  /-- Null/massless determinant condition. -/
  detP_eq_zero :
    frame.momentum.minkowskiNorm = 0

  /-- Helicity is locked to the null momentum direction. -/
  helicity_locked_to_momentum_law : Prop

  /-- Proof of the helicity-lock law. -/
  helicity_locked_to_momentum :
    helicity_locked_to_momentum_law

namespace MasslessSpinMomentumFrame

variable {Op : Type*}
variable (F : MasslessSpinMomentumFrame Op)

/-- The underlying momentum datum is null/massless. -/
theorem momentum_null :
    F.frame.momentum.minkowskiNorm = 0 :=
  F.detP_eq_zero

/-- The stored helicity-lock law. -/
theorem helicity_locked_valid :
    F.helicity_locked_to_momentum_law :=
  F.helicity_locked_to_momentum

end MasslessSpinMomentumFrame

/--
Hestenes spinor/rotor readout datum.

The same spinor frame supplies both:

* a momentum/paravector readout;
* a rotor readout;
* a spin bivector/plane readout.

The fields are proof-carrying because the concrete Clifford/STA extraction is
model-specific.
-/
@[rep_depth operator]
structure HestenesSpinorRotorDatum
    (Spinor Rotor Bivector : Type*) where
  /-- Momentum/paravector readout from the spinor frame. -/
  momentumReadout : Spinor → PauliParavector

  /-- Rotor/moving-frame readout. -/
  rotorReadout : Spinor → Rotor

  /-- Spin plane/bivector readout. -/
  spinBivector : Spinor → Bivector

  /-- Law saying the paravector readout has the intended current/momentum meaning. -/
  momentum_readout_law : Prop

  /-- Proof of the momentum readout law. -/
  momentum_readout_certificate :
    momentum_readout_law

  /-- Law saying the bivector readout has the intended spin-plane meaning. -/
  spin_bivector_law : Prop

  /-- Proof of the spin-bivector law. -/
  spin_bivector_certificate :
    spin_bivector_law

  /-- Law saying the rotor transports momentum and spin in the same Lorentz frame. -/
  rotor_transport_law : Prop

  /-- Proof of the rotor-transport law. -/
  rotor_transport_certificate :
    rotor_transport_law

namespace HestenesSpinorRotorDatum

variable {Spinor Rotor Bivector : Type*}
variable (D : HestenesSpinorRotorDatum Spinor Rotor Bivector)

/-- The stored momentum-readout law. -/
theorem momentum_readout_valid :
    D.momentum_readout_law :=
  D.momentum_readout_certificate

/-- The stored spin-bivector law. -/
theorem spin_bivector_valid :
    D.spin_bivector_law :=
  D.spin_bivector_certificate

/-- The stored rotor-transport law. -/
theorem rotor_transport_valid :
    D.rotor_transport_law :=
  D.rotor_transport_certificate

end HestenesSpinorRotorDatum

/-! ## 5. Spin-momentum coupling and helicity sockets -/

/--
Abstract spin-momentum bridge.

Momentum and spin are not identified. They are separate readouts from the same
spinor/rotor source, and their inseparability is carried by the shared-frame
certificate.
-/
@[rep_depth operator]
structure SpinMomentumBridge
    (Spinor Momentum SpinPlane : Type*) where
  /-- Vector/paravector momentum readout. -/
  momentumOf : Spinor → Momentum

  /-- Bivector/spin-plane readout. -/
  spinPlaneOf : Spinor → SpinPlane

  /-- Minkowski/mass-shell norm of the momentum readout. -/
  minkowskiNorm : Momentum → ℝ

  /-- Spinor norm whose square generates the mass shell. -/
  spinorNorm : Spinor → ℝ

  /--
  Mass-shell / scalar invariant compatibility.

  This is a field of the bridge, not a theorem-shaped placeholder returning
  only `Prop`.
  -/
  mass_shell :
    ∀ ψ : Spinor,
      minkowskiNorm (momentumOf ψ) = (spinorNorm ψ) ^ (2 : ℕ)

  /-- Law saying both readouts are taken in the same rotor/Lorentz frame. -/
  sameRotorFrame_law : Prop

  /-- Proof of the same-rotor-frame law. -/
  sameRotorFrame :
    sameRotorFrame_law

namespace SpinMomentumBridge

variable {Spinor Momentum SpinPlane : Type*}
variable (B : SpinMomentumBridge Spinor Momentum SpinPlane)

/-- The stored same-rotor-frame law. -/
theorem sameRotorFrame_valid :
    B.sameRotorFrame_law :=
  B.sameRotorFrame

/-- The mass-shell compatibility carried by the spin-momentum bridge. -/
theorem mass_is_scalar_invariant
    (ψ : Spinor) :
    B.minkowskiNorm (B.momentumOf ψ) = (B.spinorNorm ψ) ^ (2 : ℕ) :=
  B.mass_shell ψ

end SpinMomentumBridge

/--
Massless/null specialization of a spin-momentum bridge.

Massive spinor states can still have coupled spin and momentum readouts.  The
null momentum condition belongs only to a chosen massless branch.
-/
@[rep_depth operator]
structure MasslessSpinMomentumBranch
    (Spinor Momentum SpinPlane : Type*)
    (B : SpinMomentumBridge Spinor Momentum SpinPlane) where
  /-- Null/massless branch condition. -/
  nullMomentumCondition_law : Prop

  /-- Proof of the null/massless branch condition. -/
  nullMomentumCondition :
    nullMomentumCondition_law

namespace MasslessSpinMomentumBranch

variable {Spinor Momentum SpinPlane : Type*}
variable {B : SpinMomentumBridge Spinor Momentum SpinPlane}
variable (M : MasslessSpinMomentumBranch Spinor Momentum SpinPlane B)

/-- The stored null/massless branch law. -/
theorem nullMomentumCondition_valid :
    M.nullMomentumCondition_law :=
  M.nullMomentumCondition

end MasslessSpinMomentumBranch

/--
Covariant spinor/rotor readout packet.

This is the Lean-safe form of the slogan:

* momentum is the paravector/vector readout;
* spin is the bivector/plane readout;
* both are extracted from one spinor/rotor source.

The packet deliberately does not identify spin with a component of the
energy-momentum paravector.
-/
@[rep_depth operator]
structure CovariantSpinorRotorReadouts
    (Spinor Momentum SpinPlane : Type*) where
  /-- Underlying spin-momentum bridge. -/
  bridge : SpinMomentumBridge Spinor Momentum SpinPlane

  /-- Law saying the two readouts have the same spinor/rotor source. -/
  common_source_law : Prop

  /-- Proof of the common-source law. -/
  common_source :
    common_source_law

  /--
  Separation law.

  Intended meaning: momentum and spin are different covariant readouts, not
  different grade-parts of one momentum matrix.
  -/
  distinct_readout_law : Prop

  /-- Proof of the separation law. -/
  distinct_readout :
    distinct_readout_law

namespace CovariantSpinorRotorReadouts

variable {Spinor Momentum SpinPlane : Type*}
variable (R : CovariantSpinorRotorReadouts Spinor Momentum SpinPlane)

/-- The stored common spinor/rotor source law. -/
theorem common_source_valid :
    R.common_source_law :=
  R.common_source

/-- The stored different-readouts law. -/
theorem distinct_readout_valid :
    R.distinct_readout_law :=
  R.distinct_readout

/-- The momentum readout inherited from the underlying bridge. -/
def momentumOf :
    Spinor → Momentum :=
  R.bridge.momentumOf

/-- The spin-plane readout inherited from the underlying bridge. -/
def spinPlaneOf :
    Spinor → SpinPlane :=
  R.bridge.spinPlaneOf

end CovariantSpinorRotorReadouts

/--
Uncertainty-principle guardrail for this bridge.

This records that any uncertainty statement must concern a supplied
noncommuting pair, not a false claim that scalar energy and vector momentum
are automatically noncommuting components of the paravector readout.
-/
@[rep_depth operator]
structure UncertaintyReadoutGuard
    (Observable : Type*) where
  /-- Chosen first observable. -/
  first : Observable

  /-- Chosen second observable. -/
  second : Observable

  /-- Noncommutation/uncertainty law for the chosen pair. -/
  noncommuting_pair_law : Prop

  /-- Proof of the noncommutation/uncertainty law. -/
  noncommuting_pair :
    noncommuting_pair_law

namespace UncertaintyReadoutGuard

variable {Observable : Type*}
variable (U : UncertaintyReadoutGuard Observable)

/-- The stored uncertainty law for the explicitly chosen pair. -/
theorem noncommuting_pair_valid :
    U.noncommuting_pair_law :=
  U.noncommuting_pair

end UncertaintyReadoutGuard

/--
Pauli-Lubanski/helicity style spin-momentum coupling.

This does not identify spin with momentum. It records the representation
theoretic fact that the spin readout is classified relative to the momentum
readout and the chosen Lorentz-spin frame.
-/
@[rep_depth operator]
structure SpinMomentumCoupling
    (Spinor Rotor Bivector SpinInvariant : Type*)
    (D : HestenesSpinorRotorDatum Spinor Rotor Bivector) where
  /-- Pauli-Lubanski or analogous invariant readout. -/
  invariantReadout : Spinor → SpinInvariant

  /--
  Momentum-spin coupling law.

  Intended concrete meaning: the invariant readout is built from the spin
  plane/angular momentum data and the four-momentum, as in Pauli-Lubanski
  classification.
  -/
  momentum_spin_coupling_law : Prop

  /-- Proof of the coupling law. -/
  momentum_spin_coupling :
    momentum_spin_coupling_law

  /--
  Lorentz/spin-frame transport law.

  Changing momentum changes the frame in which spin is read.
  -/
  frame_transport_law : Prop

  /-- Proof of the frame-transport law. -/
  frame_transport :
    frame_transport_law

namespace SpinMomentumCoupling

variable {Spinor Rotor Bivector SpinInvariant : Type*}
variable {D : HestenesSpinorRotorDatum Spinor Rotor Bivector}
variable (C : SpinMomentumCoupling Spinor Rotor Bivector SpinInvariant D)

/-- The stored spin-momentum coupling law. -/
theorem coupling_valid :
    C.momentum_spin_coupling_law :=
  C.momentum_spin_coupling

/-- The stored Lorentz/spin-frame transport law. -/
theorem frame_transport_valid :
    C.frame_transport_law :=
  C.frame_transport

end SpinMomentumCoupling

/--
Helicity calibration for a massless/null spinor branch.

For massless particles there is no rest frame; the invariant spin readout is
helicity, i.e. spin read relative to the null momentum direction.
-/
@[rep_depth operator]
structure HelicityCalibration
    (Spinor Rotor Bivector : Type*)
    (D : HestenesSpinorRotorDatum Spinor Rotor Bivector) where
  /-- Helicity readout. -/
  helicity : Spinor → ℝ

  /-- The branch is massless/null at the momentum readout. -/
  null_momentum :
    ∀ ψ : Spinor, (D.momentumReadout ψ).IsNull

  /--
  Helicity law.

  Intended concrete meaning: helicity is spin projected along the null
  momentum direction.
  -/
  helicity_law : Prop

  /-- Proof of the helicity law. -/
  helicity_certificate :
    helicity_law

namespace HelicityCalibration

variable {Spinor Rotor Bivector : Type*}
variable {D : HestenesSpinorRotorDatum Spinor Rotor Bivector}
variable (H : HelicityCalibration Spinor Rotor Bivector D)

include H

/--
Massless momentum readouts have singular Pauli representatives.
-/
theorem singular_pauli_of_null_momentum
    (ψ : Spinor) :
    (D.momentumReadout ψ).IsSingularPauli :=
  (PauliParavector.isNull_iff_isSingularPauli (D.momentumReadout ψ)).mp
    (H.null_momentum ψ)

/-- The stored helicity law. -/
theorem helicity_valid :
    H.helicity_law :=
  H.helicity_certificate

end HelicityCalibration

/-! ## 6. Chiral lightcone compatibility -/

/--
Compatibility between Pauli/Hestenes null momentum and a chiral lightcone
carrier readout.

This is the bridge into `OperatorChiralLightcone`: null paravectors are read as
carrier lightcone data only after a calibration is supplied.
-/
@[rep_depth operator]
structure PauliHestenesChiralLightconeBridge
    (Spinor Rotor Bivector Carrier : Type*)
    [AddCommGroup Carrier] [Module ℝ Carrier]
    (Q : InfoGeometry.OperatorAlgebra.KreinIsotropicCone.KreinQuadraticDatum Carrier)
    (C : InfoGeometry.OperatorAlgebra.ModuleCircularPolarization Carrier)
    (D : HestenesSpinorRotorDatum Spinor Rotor Bivector) where
  /-- Carrier readout of a spinor. -/
  carrierReadout : Spinor → Carrier

  /--
  Null momentum is represented on one of the chiral lightcone branches.
  -/
  null_momentum_hits_chiral_lightcone :
    ∀ ψ : Spinor,
      (D.momentumReadout ψ).IsNull →
        ∃ side : InfoGeometry.OperatorAlgebra.OperatorChiralLightcone.ChiralSide,
          carrierReadout ψ ∈
            InfoGeometry.OperatorAlgebra.OperatorChiralLightcone.ChiralLightcone Q C side

namespace PauliHestenesChiralLightconeBridge

variable {Spinor Rotor Bivector Carrier : Type*}
variable [AddCommGroup Carrier] [Module ℝ Carrier]
variable {Q : InfoGeometry.OperatorAlgebra.KreinIsotropicCone.KreinQuadraticDatum Carrier}
variable {C : InfoGeometry.OperatorAlgebra.ModuleCircularPolarization Carrier}
variable {D : HestenesSpinorRotorDatum Spinor Rotor Bivector}
variable (B : PauliHestenesChiralLightconeBridge Spinor Rotor Bivector Carrier Q C D)

/--
A massless/null spinor branch has a calibrated chiral-lightcone carrier
readout.
-/
theorem chiral_lightcone_readout_of_null_momentum
    {ψ : Spinor}
    (hψ : (D.momentumReadout ψ).IsNull) :
    ∃ side : InfoGeometry.OperatorAlgebra.OperatorChiralLightcone.ChiralSide,
      B.carrierReadout ψ ∈
        InfoGeometry.OperatorAlgebra.OperatorChiralLightcone.ChiralLightcone Q C side :=
  B.null_momentum_hits_chiral_lightcone ψ hψ

end PauliHestenesChiralLightconeBridge

attribute [rep_depth operator]
  PauliParavector
  PauliParavector.minkowskiNormSq
  PauliParavector.pauliMatrix
  PauliParavector.det_pauliMatrix_eq_minkowskiNormSq
  PauliParavector.IsNull
  PauliParavector.IsSingularPauli
  PauliParavector.isNull_iff_isSingularPauli
  PauliParavector.OnMassShell
  PauliParavector.onMassShell_zero_iff_isNull
  PauliParavectorBridge
  PauliParavectorBridge.IsNull
  PauliParavectorBridge.IsSingularRepresentative
  PauliParavectorBridge.isNull_iff_isSingularRepresentative
  concretePauliParavectorBridge
  LorentzSpinActionBridge
  LorentzSpinActionBridge.minkowskiNorm_preserved
  LorentzSpinActionBridge.isNull_of_isNull
  LorentzSpinActionBridge.double_cover_valid
  SpinorHelicityFactorization
  SpinorHelicityFactorization.singular_representative
  SpinorHelicityFactorization.rank_one_valid
  PauliParavectorDatum
  PauliParavectorDatum.determinant_metric_valid
  SpinMomentumFrame
  SpinMomentumFrame.momentum_transport_valid
  SpinMomentumFrame.spin_transport_valid
  LorentzSpinRepresentationCoupling
  LorentzSpinRepresentationCoupling.shared_spin_action_valid
  LorentzSpinRepresentationCoupling.representation_coupling_valid
  MasslessSpinMomentumFrame
  MasslessSpinMomentumFrame.momentum_null
  MasslessSpinMomentumFrame.helicity_locked_valid
  HestenesSpinorRotorDatum
  HestenesSpinorRotorDatum.momentum_readout_valid
  HestenesSpinorRotorDatum.spin_bivector_valid
  HestenesSpinorRotorDatum.rotor_transport_valid
  SpinMomentumBridge
  SpinMomentumBridge.sameRotorFrame_valid
  SpinMomentumBridge.mass_is_scalar_invariant
  MasslessSpinMomentumBranch
  MasslessSpinMomentumBranch.nullMomentumCondition_valid
  CovariantSpinorRotorReadouts
  CovariantSpinorRotorReadouts.common_source_valid
  CovariantSpinorRotorReadouts.distinct_readout_valid
  CovariantSpinorRotorReadouts.momentumOf
  CovariantSpinorRotorReadouts.spinPlaneOf
  UncertaintyReadoutGuard
  UncertaintyReadoutGuard.noncommuting_pair_valid
  SpinMomentumCoupling
  SpinMomentumCoupling.coupling_valid
  SpinMomentumCoupling.frame_transport_valid
  HelicityCalibration
  HelicityCalibration.singular_pauli_of_null_momentum
  HelicityCalibration.helicity_valid
  PauliHestenesChiralLightconeBridge
  PauliHestenesChiralLightconeBridge.chiral_lightcone_readout_of_null_momentum

end InfoGeometry.Canonical.PauliHestenesSpinMomentum
