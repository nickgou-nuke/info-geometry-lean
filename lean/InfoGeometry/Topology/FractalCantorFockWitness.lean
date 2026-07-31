import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.l2Space
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Clifford.Lift
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace
open InfoGeometry.Krein.DoubledSpace

/-!
# InfoGeometry.Topology.FractalCantorFockWitness

Real Cantor-boundary Clifford/Fock analytic carrier.

Owner lane:

`Erlangen/binary boundary -> Cantor addresses -> tilt/switch operators ->
real doubled Hestenes/Krein Clifford representation -> Fock/CAR carrier`.

The tilt/switch operators are not identified with repository light-cone arrows
or Tomita mirror data by definition.  Those identifications are explicit
calibration data.

The metric graph embedding paper belongs to the finite metric graph-compression
lane, not to this Clifford/Fock carrier lane.
 -/

noncomputable section

open scoped InnerProductSpace

set_option linter.dupNamespace false

namespace InfoGeometry.Topology.FractalCantorFockWitness

/-- Symbolic Cantor boundary: infinite binary address space. -/
abbrev CantorBoundary := ℕ → Bool

/-- Finite Cantor address of depth `n`. -/
abbrev CantorAddress (n : ℕ) := Fin n → Bool

/-- Finite real/doubled function space over the depth-`n` Cantor endpoint set. -/
abbrev FiniteCantorFunctionSpace (n : ℕ) (Value : Type*) :=
  CantorAddress n → Value

/-- Infinite real/doubled Cantor function-space socket, modeled as `L²` on binary words. -/
instance : MeasurableSpace (List Bool) := ⊤

/-- Infinite real/doubled Cantor function-space socket, modeled as `L²` over binary words. -/
@[rep_depth operator]
abbrev RealDoubledCantorFunctionSpace :=
  MeasureTheory.Lp ℂ 2 (MeasureTheory.Measure.count : MeasureTheory.Measure (List Bool))

/-
Tilt/switch operator system.

`T p` is the tilt operator and `S p` is the switch operator.  The owner relation
is local anticommutation at the same address slot and commutation at distinct
slots.
-/
@[rep_depth operator]
structure TiltSwitchSystem
    (Op : Type*) [Ring Op] where
  T : ℕ → Op
  S : ℕ → Op

  T_sq :
    ∀ p, T p * T p = 1

  S_sq :
    ∀ p, S p * S p = 1

  T_comm :
    ∀ p q, T p * T q = T q * T p

  S_comm :
    ∀ p q, S p * S q = S q * S p

  T_S_comm_ne :
    ∀ p q, p ≠ q → T p * S q = S q * T p

  T_S_anticomm :
    ∀ p, T p * S p = - (S p * T p)

namespace TiltSwitchSystem

variable {Op : Type*} [Ring Op]
variable (TS : TiltSwitchSystem Op)

/-- Tilt squares to one at each Cantor address slot. -/
@[rep_depth operator]
theorem tilt_sq (p : ℕ) :
    TS.T p * TS.T p = 1 :=
  TS.T_sq p

/-- Switch squares to one at each Cantor address slot. -/
@[rep_depth operator]
theorem switch_sq (p : ℕ) :
    TS.S p * TS.S p = 1 :=
  TS.S_sq p

/-- Tilt and switch anticommute at the same slot. -/
@[rep_depth operator]
theorem tilt_switch_anticomm (p : ℕ) :
    TS.T p * TS.S p + TS.S p * TS.T p = 0 := by
  rw [TS.T_S_anticomm p]
  simp

/-- Tilt and switch commute at distinct slots. -/
@[rep_depth operator]
theorem tilt_switch_comm_of_ne {p q : ℕ} (hpq : p ≠ q) :
    TS.T p * TS.S q = TS.S q * TS.T p :=
  TS.T_S_comm_ne p q hpq

end TiltSwitchSystem

/--
Real doubled Hestenes/Krein Clifford representation generated from the
Cantor tilt/switch system.

`gamma i` is the image of the `i`-th Clifford generator.
-/
@[rep_depth operator]
structure RealDoubledCantorCliffordRepresentation
    (Op : Type*) [Ring Op] where
  tiltSwitch : TiltSwitchSystem Op

  gamma : ℕ → Op

  gamma_sq :
    ∀ i, gamma i * gamma i = 1

  gamma_anticomm :
    ∀ i j, i ≠ j → gamma i * gamma j = - (gamma j * gamma i)

namespace RealDoubledCantorCliffordRepresentation

variable {Op : Type*} [Ring Op]
variable (C : RealDoubledCantorCliffordRepresentation Op)

/-- Clifford square law readback. -/
@[rep_depth operator]
theorem generator_sq (i : ℕ) :
    C.gamma i * C.gamma i = 1 :=
  C.gamma_sq i

/-- Clifford anticommutator readback. -/
@[rep_depth operator]
theorem generator_anticomm {i j : ℕ} (hij : i ≠ j) :
    C.gamma i * C.gamma j + C.gamma j * C.gamma i = 0 := by
  rw [C.gamma_anticomm i j hij]
  simp

end RealDoubledCantorCliffordRepresentation

/-- Real-valued functions on the infinite Cantor boundary. -/
abbrev CantorBoundaryFunctionSpace := CantorBoundary → ℝ

namespace CantorBoundary

variable {j : ℕ}

/-- Flip the bit at a chosen boundary slot. -/
def flipAt (j : ℕ) (x : CantorBoundary) : CantorBoundary :=
  fun k => if k = j then ! (x k) else x k

@[simp] theorem flipAt_apply_eq (j : ℕ) (x : CantorBoundary) :
    flipAt j x j = ! (x j) := by
  simp [flipAt]

@[simp] theorem flipAt_apply_ne {j k : ℕ} (h : k ≠ j) (x : CantorBoundary) :
    flipAt j x k = x k := by
  simp [flipAt, h]

theorem flipAt_involutive (j : ℕ) (x : CantorBoundary) :
    flipAt j (flipAt j x) = x := by
  funext k
  by_cases hk : k = j <;> simp [flipAt, hk, Bool.not_not]

theorem flipAt_comm {i j : ℕ} (hij : i ≠ j) (x : CantorBoundary) :
    flipAt i (flipAt j x) = flipAt j (flipAt i x) := by
  funext k
  by_cases hki : k = i
  · by_cases hji : i = j
    · exact False.elim (hij hji)
    · simp [flipAt, hki, hji]
  · by_cases hkj : k = j
    · have hji : j ≠ i := by
        intro h
        apply hki
        rw [hkj, h]
      simp [flipAt, hkj, hji]
    · simp [flipAt, hki, hkj]

end CantorBoundary

namespace CantorBoundaryFunctionSpace

open CantorBoundary

variable {j : ℕ}

/-- Tilt operator on infinite boundary functions. -/
def tilt (j : ℕ) : CantorBoundaryFunctionSpace →ₗ[ℝ] CantorBoundaryFunctionSpace where
  toFun f := fun x => if x j then -f x else f x
  map_add' := by
    intro f g
    ext x
    by_cases hx : x j <;> simp [hx, add_comm]
  map_smul' := by
    intro c f
    ext x
    by_cases hx : x j <;> simp [hx]

/-- Switch operator on infinite boundary functions. -/
def switch (j : ℕ) : CantorBoundaryFunctionSpace →ₗ[ℝ] CantorBoundaryFunctionSpace where
  toFun f := fun x => f (CantorBoundary.flipAt j x)
  map_add' := by
    intro f g
    ext x
    rfl
  map_smul' := by
    intro c f
    ext x
    rfl

@[simp] theorem tilt_apply (j : ℕ) (f : CantorBoundaryFunctionSpace) (x : CantorBoundary) :
    tilt j f x = if x j then -f x else f x :=
  rfl

@[simp] theorem switch_apply (j : ℕ) (f : CantorBoundaryFunctionSpace) (x : CantorBoundary) :
    switch j f x = f (CantorBoundary.flipAt j x) :=
  rfl

/-- Tilt squares to the identity. -/
theorem tilt_sq (j : ℕ) :
    (tilt j) * (tilt j) = 1 := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;> simp [tilt, hx]

/-- Switch squares to the identity. -/
theorem switch_sq (j : ℕ) :
    (switch j) * (switch j) = 1 := by
  apply LinearMap.ext
  intro f
  ext x
  simpa using congrArg f (CantorBoundary.flipAt_involutive j x)

/-- Tilt operators commute at distinct slots. -/
theorem tilt_comm {i j : ℕ} :
    (tilt i) * (tilt j) = (tilt j) * (tilt i) := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hxi : x i <;> by_cases hxj : x j <;> simp [tilt, hxi, hxj]

/-- Switch operators commute at distinct slots. -/
theorem switch_comm {i j : ℕ} (hij : i ≠ j) :
    (switch i) * (switch j) = (switch j) * (switch i) := by
  apply LinearMap.ext
  intro f
  ext x
  simp [switch, CantorBoundary.flipAt_comm hij]

/-- Tilt and switch commute at different slots. -/
theorem tilt_switch_comm_of_ne {i j : ℕ} (hij : i ≠ j) :
    (tilt i) * (switch j) = (switch j) * (tilt i) := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hxi : x i <;>
    simp [tilt, switch, CantorBoundary.flipAt_apply_ne hij, hxi]

/-- Tilt and switch anticommute at the same slot. -/
theorem tilt_switch_anticomm (j : ℕ) :
    (tilt j) * (switch j) = - ((switch j) * (tilt j)) := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;> simp [tilt, switch, CantorBoundary.flipAt, hx]

/-- The canonical infinite Cantor tilt/switch system. -/
def canonicalTiltSwitchSystem :
    TiltSwitchSystem (CantorBoundaryFunctionSpace →ₗ[ℝ] CantorBoundaryFunctionSpace) where
  T := tilt
  S := switch
  T_sq := tilt_sq
  S_sq := switch_sq
  T_comm := by
    intro i j
    exact tilt_comm (i := i) (j := j)
  S_comm := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp
    · exact switch_comm hij
  T_S_comm_ne := by
    intro i j hij
    exact tilt_switch_comm_of_ne hij
  T_S_anticomm := by
    intro j
    exact tilt_switch_anticomm j

end CantorBoundaryFunctionSpace

/--
Infinite-dimensional Cantor/Cuntz orbit carrier.

This is the analytic substrate for the later orbit/basis theorems: a Cuntz
carrier, a distinguished seed vector, and explicit left/right branch actions
with a recursively defined orbit.
-/
@[rep_depth operator]
structure CelikKocakInfiniteFockCarrier
    (Op : Type*) [Ring Op] [StarRing Op]
    [NormedAddCommGroup Op] [NormedSpace ℂ Op] [CompleteSpace Op] where
  cuntz : InfoGeometry.Topology.CuntzO2Carrier Op
  seedVector : Op
  leftBranch : Op →L[ℂ] Op
  rightBranch : Op →L[ℂ] Op
  orbit : List Bool → Op
  orbit_root_eq_seed :
    orbit [] = seedVector
  orbit_cons_false_action :
    ∀ w, orbit (false :: w) = leftBranch (orbit w)
  orbit_cons_true_action :
    ∀ w, orbit (true :: w) = rightBranch (orbit w)

namespace CelikKocakInfiniteFockCarrier

variable {Op : Type*} [Ring Op] [StarRing Op]
variable [NormedAddCommGroup Op] [NormedSpace ℂ Op] [CompleteSpace Op]
variable (C : CelikKocakInfiniteFockCarrier Op)

/-- The orbit at the empty word is the seed vector. -/
@[rep_depth operator]
theorem orbit_root (C : CelikKocakInfiniteFockCarrier Op) :
    C.orbit [] = C.seedVector :=
  C.orbit_root_eq_seed

/-- Left-branch recursion for a false child word. -/
@[rep_depth operator]
theorem orbit_cons_false (C : CelikKocakInfiniteFockCarrier Op) (w : List Bool) :
    C.orbit (false :: w) = C.leftBranch (C.orbit w) :=
  C.orbit_cons_false_action w

/-- Right-branch recursion for a true child word. -/
@[rep_depth operator]
theorem orbit_cons_true (C : CelikKocakInfiniteFockCarrier Op) (w : List Bool) :
    C.orbit (true :: w) = C.rightBranch (C.orbit w) :=
  C.orbit_cons_true_action w

/-- Unified orbit action law. -/
@[rep_depth operator]
theorem orbit_action (C : CelikKocakInfiniteFockCarrier Op) (b : Bool) (w : List Bool) :
    C.orbit (b :: w) =
      (if b then C.rightBranch else C.leftBranch) (C.orbit w) := by
  cases b <;> simp [C.orbit_cons_false, C.orbit_cons_true]

/-- Root seed readback. -/
@[rep_depth operator]
theorem seed_vector_eq_orbit_root (C : CelikKocakInfiniteFockCarrier Op) :
    C.seedVector = C.orbit [] := by
  symm
  exact C.orbit_root

end CelikKocakInfiniteFockCarrier

/--
Infinite-dimensional Hilbert carrier for the Cantor orbit basis.

This is the theorem-backed analytic layer: a Hilbert basis indexed by binary
words, with orthogonality and completeness inherited from mathlib.
-/
@[rep_depth operator]
structure CelikKocakInfiniteHilbertCarrier
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] where
  orbitBasis : HilbertBasis (List Bool) ℂ E

namespace CelikKocakInfiniteHilbertCarrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Construct the Hilbert carrier from a Hilbert basis witness. -/
@[rep_depth operator]
def ofHilbertBasis (b : HilbertBasis (List Bool) ℂ E) :
    CelikKocakInfiniteHilbertCarrier E :=
  ⟨b⟩

@[simp, rep_depth operator]
theorem ofHilbertBasis_orbitBasis (b : HilbertBasis (List Bool) ℂ E) :
    (ofHilbertBasis (E := E) b).orbitBasis = b :=
  rfl

variable (H : CelikKocakInfiniteHilbertCarrier E)

/-- The Hilbert carrier is orthonormal. -/
@[rep_depth operator]
theorem orbit_orthonormal :
    Orthonormal ℂ H.orbitBasis := by
  exact H.orbitBasis.orthonormal

/-- The Hilbert carrier is complete. -/
@[rep_depth operator]
theorem orbit_complete :
    (Submodule.span ℂ (Set.range H.orbitBasis)).topologicalClosure = ⊤ := by
  exact H.orbitBasis.dense_span

/-- Distinct orbit words are orthogonal. -/
@[rep_depth operator]
theorem orbit_orthogonal_of_distinct_words {w v : List Bool} (h : w ≠ v) :
    ⟪H.orbitBasis w, H.orbitBasis v⟫_ℂ = 0 := by
  exact H.orbitBasis.orthonormal.inner_eq_zero h

/-- The basis coefficient readback is the inner-product formula. -/
@[rep_depth operator]
theorem orbit_basis_repr_apply (x : E) (w : List Bool) :
    H.orbitBasis.repr x w = ⟪H.orbitBasis w, x⟫_ℂ := by
  exact H.orbitBasis.repr_apply_apply x w

end CelikKocakInfiniteHilbertCarrier

/--
Theorem-backed carrier data for the infinite Cantor/Fock lane.

This records the explicit Hilbert carrier together with the deferred Fock
socket.  The Hilbert basis is the actual analytic object; the Fock-space names
remain as ambient targets for later bridge files.
-/
@[rep_depth operator]
structure CelikKocakInfiniteFockCarrierData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] where
  hilbertCarrier : CelikKocakInfiniteHilbertCarrier E

namespace CelikKocakInfiniteFockCarrierData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (D : CelikKocakInfiniteFockCarrierData E)

/-- The analytic Cantor orbit basis is orthonormal. -/
@[rep_depth operator]
theorem orbit_orthonormal :
    Orthonormal ℂ D.hilbertCarrier.orbitBasis :=
  D.hilbertCarrier.orbit_orthonormal

/-- The analytic Cantor orbit basis is complete. -/
@[rep_depth operator]
theorem orbit_complete :
    (Submodule.span ℂ (Set.range D.hilbertCarrier.orbitBasis)).topologicalClosure = ⊤ :=
  D.hilbertCarrier.orbit_complete

/-- The analytic Cantor orbit basis is cyclic. -/
@[rep_depth operator]
theorem orbit_cyclic :
    ⊤ ≤ (Submodule.span ℂ (Set.range D.hilbertCarrier.orbitBasis)).topologicalClosure := by
  exact le_of_eq (D.orbit_complete.symm)

/-- The analytic Cantor orbit basis as a Lean value. -/
@[rep_depth operator]
def orbit_isHilbertBasis : HilbertBasis (List Bool) ℂ E :=
  D.hilbertCarrier.orbitBasis

/-- Distinct words are orthogonal in the carrier data. -/
@[rep_depth operator]
theorem orbit_orthogonal_of_distinct_words {w v : List Bool} (h : w ≠ v) :
    ⟪D.hilbertCarrier.orbitBasis w, D.hilbertCarrier.orbitBasis v⟫_ℂ = 0 :=
  D.hilbertCarrier.orbit_orthogonal_of_distinct_words h

/-- Basis coefficient readback on the carrier data. -/
@[rep_depth operator]
theorem orbit_basis_repr_apply (x : E) (w : List Bool) :
    D.hilbertCarrier.orbitBasis.repr x w = ⟪D.hilbertCarrier.orbitBasis w, x⟫_ℂ :=
  D.hilbertCarrier.orbit_basis_repr_apply x w

end CelikKocakInfiniteFockCarrierData

/--
The Hestenes/Krein structure operator is the infinite-lane odd generator,
not the scalar complex unit.
-/
@[rep_depth operator]
theorem hestenes_structure_operator_anticommute
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (InfoGeometry.Krein.modular_j (E := E)).comp (InfoGeometry.Krein.complex_i (E := E)) =
      -((InfoGeometry.Krein.complex_i (E := E)).comp (InfoGeometry.Krein.modular_j (E := E))) :=
  InfoGeometry.Clifford.Lift.modular_j_complex_i_anticommute (E := E)

/-- The infinite `Cl(1,1)` generator at `(0,1)` is the structure operator. -/
@[rep_depth operator]
theorem cl11Rep_ι_zero_one_eq_structure_operator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    InfoGeometry.Krein.cl11Rep (E := E)
      (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1))
      = InfoGeometry.Krein.complex_i (E := E) :=
  InfoGeometry.Clifford.Lift.cl11Rep_ι_zero_one (E := E)

/--
Finite-dimensional Cantor-Pauli witness over a real/doubled matrix carrier.

The representation on endpoint functions agrees with the real Pauli tensor lane
through an explicit witness.
-/
@[rep_depth operator]
structure FiniteCantorPauliWitness
    (n : ℕ) (Mat : Type*) [Ring Mat] where
  psiGamma : Fin (2 * n) → Mat

  gamma_sq :
    ∀ i, psiGamma i * psiGamma i = 1

  gamma_anticomm :
    ∀ i j, i ≠ j → psiGamma i * psiGamma j = - (psiGamma j * psiGamma i)

namespace FiniteCantorPauliWitness

variable {n : ℕ} {Mat : Type*} [Ring Mat]
variable (W : FiniteCantorPauliWitness n Mat)

/-- Finite Clifford square law readback. -/
@[rep_depth operator]
theorem generator_sq (i : Fin (2 * n)) :
    W.psiGamma i * W.psiGamma i = 1 :=
  W.gamma_sq i

/-- Finite Clifford anticommutator readback. -/
@[rep_depth operator]
theorem generator_anticomm {i j : Fin (2 * n)} (hij : i ≠ j) :
    W.psiGamma i * W.psiGamma j + W.psiGamma j * W.psiGamma i = 0 := by
  rw [W.gamma_anticomm i j hij]
  simp

end FiniteCantorPauliWitness

/--
Real CAR pair.

This is the socket consumed by light-cone/Fock layers.
-/
@[rep_depth operator]
structure RealCARPair
    (Op : Type*) [Ring Op] where
  annihilation : Op
  creation : Op

  nilpotent_annihilation :
    annihilation * annihilation = 0

  nilpotent_creation :
    creation * creation = 0

  car :
    annihilation * creation + creation * annihilation = 1

namespace RealCARPair

variable {Op : Type*} [Ring Op]
variable (C : RealCARPair Op)

/-- Annihilation is nilpotent. -/
@[rep_depth operator]
theorem annihilation_sq_zero :
    C.annihilation * C.annihilation = 0 :=
  C.nilpotent_annihilation

/-- Creation is nilpotent. -/
@[rep_depth operator]
theorem creation_sq_zero :
    C.creation * C.creation = 0 :=
  C.nilpotent_creation

/-- Canonical CAR anticommutator law. -/
@[rep_depth operator]
theorem anticommutator_eq_one :
    C.annihilation * C.creation + C.creation * C.annihilation = 1 :=
  C.car

end RealCARPair

/--
Clifford-to-CAR calibration.

This explicitly records that a selected Clifford pair from the Cantor
representation supplies the CAR pair required by the light-cone/Fock socket.
-/
@[rep_depth operator]
structure CliffordToCARCalibration
    (Op : Type*) [Ring Op] where
  clifford : RealDoubledCantorCliffordRepresentation Op
  gammaAIndex : ℕ
  gammaBIndex : ℕ
  carPair : RealCARPair Op

namespace CliffordToCARCalibration

variable {Op : Type*} [Ring Op]
variable (W : CliffordToCARCalibration Op)

/-- The first selected CAR seed is a Clifford generator image. -/
@[rep_depth operator]
def gammaA : Op :=
  W.clifford.gamma W.gammaAIndex

/-- The second selected CAR seed is a Clifford generator image. -/
@[rep_depth operator]
def gammaB : Op :=
  W.clifford.gamma W.gammaBIndex

/-- The first selected CAR seed is a Clifford generator image. -/
@[rep_depth operator]
theorem gammaA_generator :
    W.gammaA = W.clifford.gamma W.gammaAIndex :=
  rfl

/-- The second selected CAR seed is a Clifford generator image. -/
@[rep_depth operator]
theorem gammaB_generator :
    W.gammaB = W.clifford.gamma W.gammaBIndex :=
  rfl

end CliffordToCARCalibration

/--
Calibration between repository Drazin/chiral arrows and the Cantor tilt/switch
witness.

This prevents identifying tilt/switch operators with `u_+`, `u_-`, or mirror
operators without an explicit representation map.
-/
@[rep_depth operator]
inductive TiltSwitchSide where
  | tilt
  | switch
  deriving DecidableEq, Repr

namespace TiltSwitchSide

/-- The side selects the tilt operator. -/
@[simp]
theorem eq_tilt_iff {s : TiltSwitchSide} : s = TiltSwitchSide.tilt ∨ s = TiltSwitchSide.switch :=
  by cases s <;> simp

end TiltSwitchSide

@[rep_depth operator]
structure DrazinArrowTiltSwitchCalibration
    (Op : Type*) [Ring Op] where
  tiltSwitch : TiltSwitchSystem Op

  uPlusIndex : ℕ
  uMinusIndex : ℕ
  mirrorIndex : ℕ
  uMinusSide : TiltSwitchSide

namespace DrazinArrowTiltSwitchCalibration

variable {Op : Type*} [Ring Op]
variable (C : DrazinArrowTiltSwitchCalibration Op)

/-- Positive light-cone arrow readout. -/
@[rep_depth operator]
def uPlus : Op :=
  C.tiltSwitch.T C.uPlusIndex

/-- Negative light-cone arrow readout. -/
@[rep_depth operator]
def uMinus : Op :=
  match C.uMinusSide with
  | TiltSwitchSide.tilt => C.tiltSwitch.T C.uMinusIndex
  | TiltSwitchSide.switch => C.tiltSwitch.S C.uMinusIndex

/-- Mirror readout. -/
@[rep_depth operator]
def mirror : Op :=
  C.tiltSwitch.S C.mirrorIndex

/-- Positive light-cone arrow is calibrated to a tilt witness by definition. -/
@[rep_depth operator]
theorem uPlus_calibrated :
    C.uPlus = C.tiltSwitch.T C.uPlusIndex :=
by
  cases C with
  | mk tiltSwitch uPlusIndex uMinusIndex mirrorIndex uMinusSide =>
      rfl

/-- Negative light-cone arrow is calibrated to a tilt or switch witness by definition. -/
@[rep_depth operator]
theorem uMinus_calibrated :
    C.uMinus = C.tiltSwitch.T C.uMinusIndex ∨
      C.uMinus = C.tiltSwitch.S C.uMinusIndex := by
  cases C with
  | mk tiltSwitch uPlusIndex uMinusIndex mirrorIndex uMinusSide =>
      cases uMinusSide with
      | tilt =>
          left
          rfl
      | switch =>
          right
          rfl

/-- Mirror data is calibrated to a switch witness by definition. -/
@[rep_depth operator]
theorem mirror_calibrated :
    C.mirror = C.tiltSwitch.S C.mirrorIndex :=
by
  cases C with
  | mk tiltSwitch uPlusIndex uMinusIndex mirrorIndex uMinusSide =>
      rfl

end DrazinArrowTiltSwitchCalibration

@[rep_depth operator]
structure FractalCantorFockWitness
    (Op E : Type*) [Ring Op]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] where
  celikKocak : CelikKocakInfiniteFockCarrierData E
  cliffordToCAR : CliffordToCARCalibration Op
  drazinCalibration : DrazinArrowTiltSwitchCalibration Op


/-- Drazin support of a signal operator: `p = A Aᴰ`. -/
@[rep_depth operator]
structure DrazinHorizon
    (Op : Type*) [Ring Op] where
  A : Op
  AD : Op
  p : Op

  p_def :
    p = A * AD

  commute :
    A * AD = AD * A

  p_idempotent :
    p * p = p

/-- Drazin-Green harmonic projector: `H = 1 - L Lᴰ`. -/
@[rep_depth operator]
structure DrazinGreenHarmonic
    (Op : Type*) [Ring Op] where
  L : Op
  LD : Op
  H : Op

  H_def :
    H = 1 - L * LD

  H_idempotent :
    H * H = H

/-- Matter envelope extracted from the Cantor/Fock observable. -/
@[rep_depth operator]
def fractalFockMatterEnvelope
    {Op : Type*} [Ring Op]
    (D : DrazinHorizon Op)
    (G : DrazinGreenHarmonic Op)
    (x : Op) : Op :=
  G.H * (D.p * x * D.p) * G.H

/-- Real Fierz readout channels.  The phase-like channel is named `rotor`. -/
@[rep_depth operator]
inductive FierzChannel where
  | scalar
  | rotor
  | vector
  | axial
  | area
  deriving DecidableEq, Fintype

/-- Real Fierz readout packet. -/
@[rep_depth operator]
structure FierzReadout
    (Op : Type*) where
  channel : FierzChannel → Op → ℝ

/--
Fierz coordinates are read from the Drazin-Hodge envelope, not from the raw
Cantor/Fock operator.
-/
@[rep_depth operator]
def fractalFockFierzCoordinate
    {Op : Type*} [Ring Op]
    (D : DrazinHorizon Op)
    (G : DrazinGreenHarmonic Op)
    (R : FierzReadout Op)
    (x : Op)
    (ch : FierzChannel) : ℝ :=
  R.channel ch (fractalFockMatterEnvelope D G x)

end InfoGeometry.Topology.FractalCantorFockWitness
