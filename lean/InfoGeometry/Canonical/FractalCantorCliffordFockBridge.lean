import Mathlib
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Topology.FractalCantorFockWitness
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Canonical.CantorCuntzCliffordBridge
import InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
import InfoGeometry.Canonical.CelikKocakFractalFockBridge
import InfoGeometry.Canonical.FractalFockEquivalenceBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.FractalCantorCliffordFockBridge

Theorem-safe bridge for the core chain:

* infinite binary Cantor boundary;
* finite binary cylinder refinement;
* Cuntz `O₂` branching and CAR readout;
* infinite Clifford/Fock witness packet;
* spectral-dimension / Hausdorff-calibration readout.

This file does not construct a new ultrametric on the Cantor boundary, nor
does it build the full infinite tensor product `Cl(1,1)^∞` analytically.  It
reuses the repo-owned boundary, Cuntz, Clifford, and Fock owner surfaces and
packages their theorem-safe consequences.
-/

noncomputable section

namespace InfoGeometry.Canonical.FractalCantorCliffordFockBridge

open InfoGeometry.Topology
open InfoGeometry.Topology.FractalCantorFockWitness
open InfoGeometry.Canonical.TypeIIIModularCantorSystem
open InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
open InfoGeometry.Canonical.CelikKocakFractalFockBridge
open InfoGeometry.Canonical.FractalFockEquivalenceBridge

/-! ## 1. Boundary and cylinder carriers -/

/-- Infinite binary word space used as the symbolic Cantor boundary. -/
@[rep_depth operator]
abbrev InfiniteBinaryWordSpace := CantorBoundary

/-- Finite binary path codes used as Cantor cylinders. -/
@[rep_depth operator]
abbrev FiniteBinaryWord := TypeIIIModularCantorSystem.BinaryWord

/-- A canonical infinite binary boundary carrier. -/
@[rep_depth operator]
abbrev CantorBoundarySpace := InfiniteBinaryWordSpace

/-- The first boundary symbol readout. -/
@[rep_depth operator]
def boundaryHead (ξ : InfiniteBinaryWordSpace) : Bool :=
  ξ 0

/-- Prepend one binary symbol to an infinite boundary code. -/
@[rep_depth operator]
def boundaryCons (a : Bool) (ξ : InfiniteBinaryWordSpace) : InfiniteBinaryWordSpace :=
  fun n =>
    match n with
    | 0 => a
    | Nat.succ m => ξ m

/-- Remove the first binary symbol from an infinite boundary code. -/
@[rep_depth operator]
def boundaryTail (ξ : InfiniteBinaryWordSpace) : InfiniteBinaryWordSpace :=
  fun n => ξ (n + 1)

@[simp, rep_depth operator]
theorem boundaryHead_boundaryCons
    (a : Bool) (ξ : InfiniteBinaryWordSpace) :
    boundaryHead (boundaryCons a ξ) = a := by
  rfl

@[simp, rep_depth operator]
theorem boundaryTail_boundaryCons
    (a : Bool) (ξ : InfiniteBinaryWordSpace) :
    boundaryTail (boundaryCons a ξ) = ξ := by
  funext n
  rfl

/-- Re-export of the binary child map. -/
@[rep_depth operator]
def binaryChild (w : FiniteBinaryWord) (b : Bool) : FiniteBinaryWord :=
  BinaryWord.child w b

/-- Re-export of the binary closed cylinder. -/
@[rep_depth operator]
def binaryClosedCylinder (w : FiniteBinaryWord) : Set FiniteBinaryWord :=
  BinaryWord.closedCylinder w

@[simp, rep_depth operator]
theorem binaryWord_child_length (w : FiniteBinaryWord) (b : Bool) :
    (binaryChild w b).length = w.length + 1 := by
  simp [binaryChild, TypeIIIModularCantorSystem.BinaryWord.child]

@[simp, rep_depth operator]
theorem binaryWord_mem_closedCylinder_self (w : FiniteBinaryWord) :
    w ∈ binaryClosedCylinder w := by
  simpa [binaryClosedCylinder] using (TypeIIIModularCantorSystem.BinaryWord.mem_closedCylinder_self w)

@[rep_depth operator]
theorem binaryWord_closedCylinder_split (w : FiniteBinaryWord) :
    binaryClosedCylinder w =
      ({w} : Set FiniteBinaryWord)
        ∪ binaryClosedCylinder (binaryChild w false)
        ∪ binaryClosedCylinder (binaryChild w true) := by
  simpa [binaryClosedCylinder, binaryChild] using
    (TypeIIIModularCantorSystem.BinaryWord.closedCylinder_split w)

/-! ## 2. Hausdorff / spectral calibration readout -/

/--
The symbolic Hausdorff readout is carried by the Cuntz/Cantor spectral triple.

This is the repo-safe replacement for a literal metric instance on the infinite
binary boundary.
-/
@[rep_depth operator]
def cantorHausdorffReadout
    {Op H : Type*} [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]
    (T : CuntzCantorSpectralTriple Op H) : ℝ :=
  T.spectralDimension

@[rep_depth operator]
theorem cantorHausdorffReadout_eq_middleThirdsCantor
    {Op H : Type*} [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]
    (T : CuntzCantorSpectralTriple Op H) :
    cantorHausdorffReadout T = Real.log 2 / Real.log 3 := by
  simp [cantorHausdorffReadout, T.spectralDimension_eq_middleThirdsCantor]

/-! ## 3. Cuntz / CAR / Clifford readouts -/

/-- Re-export of the Cuntz range-projection partition of unity. -/
@[rep_depth operator]
theorem cuntz_rangeProjection_sum_one
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) :
    C.leftRangeProjection + C.rightRangeProjection = 1 :=
  C.rangeProjection_sum_one

/-- Re-export of the derived CAR nilpotency law. -/
@[rep_depth operator]
theorem carFromCuntz_sq_eq_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) :
    carFromCuntz C * carFromCuntz C = 0 :=
  InfoGeometry.Canonical.carFromCuntz_sq_eq_zero C

/-- Re-export of the derived CAR anticommutator law. -/
@[rep_depth operator]
theorem carFromCuntz_anticommutator_star_eq_one
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) :
    cantorAnticommutator (carFromCuntz C) (star (carFromCuntz C)) = 1 :=
  InfoGeometry.Canonical.carFromCuntz_anticommutator_star_eq_one C

/-- Re-export of the infinite Clifford square law from the paper witness. -/
@[rep_depth operator]
theorem infiniteClifford_generator_sq
    {Op : Type*} [Ring Op]
    (W : CelikKocakInfiniteFockWitness Op) (i : ℕ) :
    W.clifford.gamma i * W.clifford.gamma i = 1 :=
  W.clifford.gamma_sq i

/-- Re-export of the infinite Clifford anticommutation law from the paper witness. -/
@[rep_depth operator]
theorem infiniteClifford_generator_anticomm
    {Op : Type*} [Ring Op]
    (W : CelikKocakInfiniteFockWitness Op) {i j : ℕ} (hij : i ≠ j) :
    W.clifford.gamma i * W.clifford.gamma j +
      W.clifford.gamma j * W.clifford.gamma i = 0 := by
  rw [W.clifford.gamma_anticomm (i := i) (j := j) hij]
  simp

/-! ## 4. Fock equivalence readout -/

/-- Re-export of the explicit equivalence-to-Fock witness. -/
@[rep_depth operator]
theorem equivalent_to_fock
    {Op : Type*} [Ring Op]
    (W : CelikKocakInfiniteFockWitness Op) :
    W.equivalentToFock :=
  W.equivalentToFock_witness

/-! ## 5. Chain packet -/

/--
The theorem-safe chain packet for the requested framework.

This packages:

* an infinite binary boundary point;
* a finite binary word address;
* the Cuntz/Cantor spectral triple;
* a CAR generator readout;
* the infinite Clifford/Fock witness;
* the paper-facing Fock equivalence bridge.

The packet is intentionally a witness container, not a claim that the analytic
substrate has been reconstructed from scratch in this file.
-/
@[rep_depth operator]
structure FractalCantorCliffordFockChain
    (Op H : Type*) [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] where
  boundary : InfiniteBinaryWordSpace
  finiteWord : FiniteBinaryWord
  spectralTriple : CuntzCantorSpectralTriple Op H
  car : CARGenerator Op
  car_eq : car.a = carFromCuntz (spectralTriple.cuntz)
  cliffordFock : CelikKocakInfiniteFockWitness Op
  fractalFockBridge : FractalFockBridge Op

namespace FractalCantorCliffordFockChain

variable {Op H : Type*} [Ring Op] [StarRing Op]
variable [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]
variable (B : FractalCantorCliffordFockChain Op H)

/-- The finite word is a binary Cantor word. -/
@[rep_depth operator]
theorem finiteWord_child_length (b : Bool) :
    (binaryChild B.finiteWord b).length = B.finiteWord.length + 1 :=
  binaryWord_child_length (w := B.finiteWord) b

/-- The finite word lies in its own closed cylinder. -/
@[rep_depth operator]
theorem finiteWord_mem_closedCylinder_self :
    B.finiteWord ∈ binaryClosedCylinder B.finiteWord :=
  binaryWord_mem_closedCylinder_self (w := B.finiteWord)

/-- The finite binary cylinder splits into root, false child, and true child. -/
@[rep_depth operator]
theorem finiteWord_closedCylinder_split :
    binaryClosedCylinder B.finiteWord =
      ({B.finiteWord} : Set FiniteBinaryWord)
        ∪ binaryClosedCylinder (binaryChild B.finiteWord false)
        ∪ binaryClosedCylinder (binaryChild B.finiteWord true) :=
  binaryWord_closedCylinder_split (w := B.finiteWord)

/-- The Cuntz range projections sum to one. -/
@[rep_depth operator]
theorem spectralTriple_firstLevel_sum_one :
    B.spectralTriple.cuntz.leftRangeProjection +
      B.spectralTriple.cuntz.rightRangeProjection = 1 :=
  B.spectralTriple.firstLevelCylinder_sum_one

/-- The spectral/Hausdorff readout is calibrated to the Cantor dimension. -/
@[rep_depth operator]
theorem spectralTriple_cantorDimension :
    cantorHausdorffReadout B.spectralTriple = Real.log 2 / Real.log 3 :=
  cantorHausdorffReadout_eq_middleThirdsCantor B.spectralTriple

/-- The CAR generator from Cuntz data is nilpotent. -/
@[rep_depth operator]
theorem car_sq_eq_zero :
    B.car.a * B.car.a = 0 :=
  B.car.nilpotent

/-- The CAR generator and its adjoint satisfy the expected anticommutator law. -/
@[rep_depth operator]
theorem car_anticommutator_star_eq_one :
    cantorAnticommutator B.car.a (star B.car.a) = 1 :=
  B.car.car

/-- The infinite Clifford generators square to one. -/
@[rep_depth operator]
theorem clifford_generator_sq (i : ℕ) :
    B.cliffordFock.clifford.gamma i * B.cliffordFock.clifford.gamma i = 1 :=
  infiniteClifford_generator_sq B.cliffordFock i

/-- Distinct infinite Clifford generators anticommute. -/
@[rep_depth operator]
theorem clifford_generator_anticomm {i j : ℕ} (hij : i ≠ j) :
    B.cliffordFock.clifford.gamma i * B.cliffordFock.clifford.gamma j +
      B.cliffordFock.clifford.gamma j * B.cliffordFock.clifford.gamma i = 0 :=
  infiniteClifford_generator_anticomm B.cliffordFock hij

/-- The infinite Clifford/Fock packet is equivalent to the classical Fock socket. -/
@[rep_depth operator]
theorem equivalent_to_fock :
    B.cliffordFock.equivalentToFock :=
  B.cliffordFock.equivalent_to_fock

end FractalCantorCliffordFockChain

/-! ## 6. Combined owner target -/

/--
Combined theorem-safe owner target for the requested framework.

This records the chain as a conjunction of already-owned theorem surfaces:

* finite binary Cantor cylinder refinement;
* Cuntz partition of unity;
* derived CAR from Cuntz;
* infinite Clifford generator laws;
* Fock equivalence;
* Cantor-dimension calibration.
-/
@[rep_depth operator]
structure FractalCantorCliffordFockOwnerTarget
    (Op H : Type*) [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] where
  binaryWord_closedCylinder_split :
    ∀ w : FiniteBinaryWord,
      binaryClosedCylinder w =
        ({w} : Set FiniteBinaryWord)
          ∪ binaryClosedCylinder (binaryChild w false)
          ∪ binaryClosedCylinder (binaryChild w true)

  cuntz_rangeProjection_sum_one :
    ∀ (C : CuntzO2Carrier Op),
      C.leftRangeProjection + C.rightRangeProjection = 1

  carFromCuntz_laws :
    ∀ (C : CantorCuntzO2Carrier Op),
      carFromCuntz C * carFromCuntz C = 0 ∧
        cantorAnticommutator (carFromCuntz C) (star (carFromCuntz C)) = 1

  infiniteClifford_laws :
    ∀ (W : CelikKocakInfiniteFockWitness Op),
      W.equivalentToFock ∧
        (∀ i : ℕ, W.clifford.gamma i * W.clifford.gamma i = 1) ∧
        (∀ {i j : ℕ}, i ≠ j →
          W.clifford.gamma i * W.clifford.gamma j +
            W.clifford.gamma j * W.clifford.gamma i = 0)

  spectralDimension_eq :
    ∀ (T : CuntzCantorSpectralTriple Op H),
      cantorHausdorffReadout T = Real.log 2 / Real.log 3

/-- The combined owner target follows from the existing owner surfaces. -/
@[rep_depth operator]
theorem fractalCantorCliffordFockOwnerTarget
    (Op H : Type*) [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] :
    FractalCantorCliffordFockOwnerTarget Op H := by
  refine { binaryWord_closedCylinder_split := ?_,
           cuntz_rangeProjection_sum_one := ?_,
           carFromCuntz_laws := ?_,
           infiniteClifford_laws := ?_,
           spectralDimension_eq := ?_ }
  · intro w
    exact binaryWord_closedCylinder_split (w := w)
  · intro C
    exact C.rangeProjection_sum_one
  · intro C
    exact ⟨carFromCuntz_sq_eq_zero C, carFromCuntz_anticommutator_star_eq_one C⟩
  · intro W
    constructor
    · exact W.equivalent_to_fock
    · constructor
      · intro i
        exact W.clifford.gamma_sq i
      · intro i j hij
        rw [W.clifford.gamma_anticomm (i := i) (j := j) hij]
        simp
  · intro T
    exact cantorHausdorffReadout_eq_middleThirdsCantor T

end FractalCantorCliffordFockBridge
