import InfoGeometry.Canonical.ThermalTimeMonodromyBridge
import InfoGeometry.Canonical.RyuTakayanagiEntanglementBridge

/-!
# RyuTakayanagiThermalTimeBridge

A conservative implementation joining three already-verified ingredients:

1. calibrated modular thermal time from `ThermalTimeMonodromyBridge`,
2. de Rham winding/holonomy on the Klein-quadric monodromy lane, and
3. the finite depth-indexed Ryu-Takayanagi entropy/area law from
   `RyuTakayanagiEntanglementBridge`.

This file does not identify entropy, area, modular time, or winding by fiat.
Instead it introduces explicit compatibility data:

* a winding-to-depth readout, and
* additivity laws saying that both the thermal-time clock and the RT depth clock
  are read on the same integer winding label.

All derived theorems are then proved from those explicit compatibility fields.
-/

noncomputable section

namespace InfoGeometry.Canonical.RyuTakayanagiThermalTimeBridge

open InfoGeometry.Canonical.ThermalTimeMonodromyBridge
open InfoGeometry.Canonical.RyuTakayanagiEntanglementBridge
open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

section Bridge

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Full calibrated RT/thermal-time bridge.

The underlying thermal-time/monodromy bridge already supplies:
* modular Radon-Nikodym data,
* winding-to-time calibration, and
* a positive contour radius for the de Rham winding theorems.

This extension adds a winding-to-depth readout for the RT lane together with the
explicit additive laws needed to make that readout behave like a genuine clock.
-/
structure BridgeData extends ThermalTimeMonodromyBridge.BridgeData (E := E) where
  depthOfWinding : ℤ → ℕ
  depth_zero : depthOfWinding 0 = 0
  depth_add : ∀ m n : ℤ,
    depthOfWinding (m + n) = depthOfWinding m + depthOfWinding n

/-- RT entropy readout attached to a winding label. -/
def entropyOfWinding (B : BridgeData (E := E)) (k : ℤ) : ℝ :=
  subtreeEntropy (B.depthOfWinding k)

/-- RT minimal-area readout attached to a winding label. -/
def areaOfWinding (B : BridgeData (E := E)) (k : ℤ) : ℝ :=
  minimalSurfaceArea (B.depthOfWinding k)

@[simp] theorem entropyOfWinding_def (B : BridgeData (E := E)) (k : ℤ) :
    entropyOfWinding B k = subtreeEntropy (B.depthOfWinding k) := rfl

@[simp] theorem areaOfWinding_def (B : BridgeData (E := E)) (k : ℤ) :
    areaOfWinding B k = minimalSurfaceArea (B.depthOfWinding k) := rfl

@[simp] theorem entropyOfWinding_zero (B : BridgeData (E := E)) :
    entropyOfWinding B 0 = 0 := by
  rw [entropyOfWinding, B.depth_zero]
  simp [subtreeEntropy]

@[simp] theorem areaOfWinding_zero (B : BridgeData (E := E)) :
    areaOfWinding B 0 = 0 := by
  rw [areaOfWinding, B.depth_zero]
  simp [minimalSurfaceArea]

/--
An additive winding-to-depth map `ℤ → ℕ` must collapse: since `(-k) + k = 0`,
the corresponding depths sum to `0` in `ℕ`, hence each depth is zero.
-/
theorem depthOfWinding_eq_zero (B : BridgeData (E := E)) (k : ℤ) :
    B.depthOfWinding k = 0 := by
  have hsum : 0 = B.depthOfWinding (-k) + B.depthOfWinding k := by
    simpa [B.depth_zero] using B.depth_add (-k) k
  have hk_le : B.depthOfWinding k ≤ 0 := by
    omega
  omega

@[simp] theorem entropyOfWinding_eq_zero (B : BridgeData (E := E)) (k : ℤ) :
    entropyOfWinding B k = 0 := by
  rw [entropyOfWinding, depthOfWinding_eq_zero (B := B) k]
  simp [subtreeEntropy]

@[simp] theorem areaOfWinding_eq_zero (B : BridgeData (E := E)) (k : ℤ) :
    areaOfWinding B k = 0 := by
  rw [areaOfWinding, depthOfWinding_eq_zero (B := B) k]
  simp [minimalSurfaceArea]

/-- The RT formula read on a winding label through the chosen depth calibration. -/
theorem ryuTakayanagi_formula_of_winding
    (B : BridgeData (E := E)) (k : ℤ) :
    entropyOfWinding B k = areaOfWinding B k / (4 * effectiveNewtonConstant) := by
  exact ryu_takayanagi_formula (B.depthOfWinding k)

/--
On the present exact interface, the additive `ℤ → ℕ` depth law forces the RT
readout to collapse to zero at every winding label.
-/
theorem ryuTakayanagi_formula_of_winding_collapsed
    (B : BridgeData (E := E)) (k : ℤ) :
    entropyOfWinding B k = 0 ∧ areaOfWinding B k = 0 := by
  exact ⟨entropyOfWinding_eq_zero (B := B) k, areaOfWinding_eq_zero (B := B) k⟩

/-- Winding labels with the same chosen depth have the same RT readout. -/
theorem ryuTakayanagi_formula_of_depth_eq
    (B : BridgeData (E := E)) {k ℓ : ℤ}
    (hdepth : B.depthOfWinding k = B.depthOfWinding ℓ) :
    entropyOfWinding B k = entropyOfWinding B ℓ ∧
      areaOfWinding B k = areaOfWinding B ℓ := by
  constructor <;> simp [entropyOfWinding, areaOfWinding, hdepth]

/-- The RT entropy clock is additive on winding labels. -/
theorem entropyOfWinding_add (B : BridgeData (E := E)) (m n : ℤ) :
    entropyOfWinding B (m + n) = entropyOfWinding B m + entropyOfWinding B n := by
  rw [entropyOfWinding, entropyOfWinding, entropyOfWinding, B.depth_add m n, subtreeEntropy_add]

/-- The RT area clock is additive on winding labels. -/
theorem areaOfWinding_add (B : BridgeData (E := E)) (m n : ℤ) :
    areaOfWinding B (m + n) = areaOfWinding B m + areaOfWinding B n := by
  rw [areaOfWinding, areaOfWinding, areaOfWinding, B.depth_add m n, minimalSurfaceArea_add]

/-- The underlying thermal-time clock remains additive on winding labels. -/
theorem modularAutomorphismGroup_timeOfWinding_add
    (B : BridgeData (E := E)) (m n : ℤ) (A : EndH E) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (m + n)) A =
      modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding m)
        (modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding n) A) := by
  exact ThermalTimeMonodromyBridge.modularAutomorphismGroup_timeOfWinding_add
    (B := B.toBridgeData) m n A

/--
The winding label controls both lanes simultaneously:
* modular flow composes additively,
* RT entropy composes additively,
* RT area composes additively.
-/
theorem synchronized_clock_additivity
    (B : BridgeData (E := E)) (m n : ℤ) (A : EndH E) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (m + n)) A =
      modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding m)
        (modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding n) A) ∧
    entropyOfWinding B (m + n) = entropyOfWinding B m + entropyOfWinding B n ∧
    areaOfWinding B (m + n) = areaOfWinding B m + areaOfWinding B n := by
  refine ⟨?_, ?_, ?_⟩
  · exact modularAutomorphismGroup_timeOfWinding_add (B := B) m n A
  · exact entropyOfWinding_add (B := B) m n
  · exact areaOfWinding_add (B := B) m n

/--
At each winding label the de Rham monodromy class and the RT entropy/area law
are simultaneously available on the same bridge package.
-/
theorem monodromy_and_ryuTakayanagi_of_winding
    (B : BridgeData (E := E)) (n : ℤ) :
    (n : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z) = logarithmicPhase n ∧
    entropyOfWinding B n = areaOfWinding B n / (4 * effectiveNewtonConstant) := by
  refine ⟨?_, ?_⟩
  · exact deRhamClass_of_calibrated_winding (B := B.toBridgeData) n
  · exact ryuTakayanagi_formula_of_winding (B := B) n

/--
At each winding label the de Rham Wilson phase is trivial and the RT formula
holds on the depth readout selected by the bridge.
-/
theorem holonomy_and_ryuTakayanagi_of_winding
    (B : BridgeData (E := E)) (n : ℤ) :
    Complex.exp ((n : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)) = (1 : ℂ) ∧
    entropyOfWinding B n = areaOfWinding B n / (4 * effectiveNewtonConstant) := by
  refine ⟨?_, ?_⟩
  · exact wilsonPhase_of_calibrated_winding (B := B.toBridgeData) n
  · exact ryuTakayanagi_formula_of_winding (B := B) n

/--
Single-label full readout: modular flow, de Rham winding class, Wilson holonomy,
RT entropy, and RT area are all available from one bridge datum at winding `n`.
-/
theorem full_clock_readout
    (B : BridgeData (E := E)) (n : ℤ) (A : EndH E) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding n) A =
        B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding n) A ∧
      (n : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z) = logarithmicPhase n ∧
      Complex.exp ((n : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)) = (1 : ℂ) ∧
      entropyOfWinding B n = areaOfWinding B n / (4 * effectiveNewtonConstant) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [toAdditiveModularFlow_apply]
  · exact deRhamClass_of_calibrated_winding (B := B.toBridgeData) n
  · exact wilsonPhase_of_calibrated_winding (B := B.toBridgeData) n
  · exact ryuTakayanagi_formula_of_winding (B := B) n

/--
Canonical concrete model of the current interface: the winding-to-depth readout
is the zero map. This is not an arbitrary choice: `depthOfWinding_eq_zero`
shows every additive `ℤ → ℕ` readout is forced to coincide with it.
-/
def zeroDepthBridge
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E)) : BridgeData (E := E) where
  toBridgeData := B
  depthOfWinding := fun _ => 0
  depth_zero := rfl
  depth_add := by
    intro m n
    simp

@[simp] theorem zeroDepthBridge_depthOfWinding
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E)) (k : ℤ) :
    (zeroDepthBridge (E := E) B).depthOfWinding k = 0 := rfl

@[simp] theorem zeroDepthBridge_entropy
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E)) (k : ℤ) :
    entropyOfWinding (zeroDepthBridge (E := E) B) k = 0 := by
  simp [zeroDepthBridge, entropyOfWinding, subtreeEntropy]

@[simp] theorem zeroDepthBridge_area
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E)) (k : ℤ) :
    areaOfWinding (zeroDepthBridge (E := E) B) k = 0 := by
  simp [zeroDepthBridge, areaOfWinding, minimalSurfaceArea]

theorem zeroDepthBridge_full_clock_readout
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E)) (n : ℤ) (A : EndH E) :
    modularAutomorphismGroup B.modularData ((zeroDepthBridge (E := E) B).calibration.timeOfWinding n) A =
        B.modularData.toAdditiveModularFlow ((zeroDepthBridge (E := E) B).calibration.timeOfWinding n) A ∧
      (n : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z) = logarithmicPhase n ∧
      Complex.exp ((n : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)) = (1 : ℂ) ∧
      entropyOfWinding (zeroDepthBridge (E := E) B) n =
        areaOfWinding (zeroDepthBridge (E := E) B) n / (4 * effectiveNewtonConstant) := by
  simpa [zeroDepthBridge] using
    full_clock_readout (B := zeroDepthBridge (E := E) B) n A

/--
Non-collapsing one-sided refinement: instead of requiring a group homomorphism
`ℤ → ℕ`, we package the RT depth clock only on the positive winding semigroup
`ℕ`. This is the smallest honest interface that supports a nontrivial additive
readout.
-/
structure PositiveBranchBridgeData extends ThermalTimeMonodromyBridge.BridgeData (E := E) where
  depthOfStep : ℕ → ℕ
  depth_zero : depthOfStep 0 = 0
  depth_add : ∀ m n : ℕ, depthOfStep (m + n) = depthOfStep m + depthOfStep n

/-- RT entropy readout on the positive winding branch. -/
def entropyOfStep (B : PositiveBranchBridgeData (E := E)) (n : ℕ) : ℝ :=
  subtreeEntropy (B.depthOfStep n)

/-- RT area readout on the positive winding branch. -/
def areaOfStep (B : PositiveBranchBridgeData (E := E)) (n : ℕ) : ℝ :=
  minimalSurfaceArea (B.depthOfStep n)

@[simp] theorem entropyOfStep_zero (B : PositiveBranchBridgeData (E := E)) :
    entropyOfStep B 0 = 0 := by
  rw [entropyOfStep, B.depth_zero]
  simp [subtreeEntropy]

@[simp] theorem areaOfStep_zero (B : PositiveBranchBridgeData (E := E)) :
    areaOfStep B 0 = 0 := by
  rw [areaOfStep, B.depth_zero]
  simp [minimalSurfaceArea]

theorem entropyOfStep_add (B : PositiveBranchBridgeData (E := E)) (m n : ℕ) :
    entropyOfStep B (m + n) = entropyOfStep B m + entropyOfStep B n := by
  rw [entropyOfStep, entropyOfStep, entropyOfStep, B.depth_add m n, subtreeEntropy_add]

theorem areaOfStep_add (B : PositiveBranchBridgeData (E := E)) (m n : ℕ) :
    areaOfStep B (m + n) = areaOfStep B m + areaOfStep B n := by
  rw [areaOfStep, areaOfStep, areaOfStep, B.depth_add m n, minimalSurfaceArea_add]

theorem ryuTakayanagi_formula_of_step
    (B : PositiveBranchBridgeData (E := E)) (n : ℕ) :
    entropyOfStep B n = areaOfStep B n / (4 * effectiveNewtonConstant) := by
  exact ryu_takayanagi_formula (B.depthOfStep n)

theorem modularAutomorphismGroup_timeOfStep_add
    (B : PositiveBranchBridgeData (E := E)) (m n : ℕ) (A : EndH E) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding ((m + n : ℕ) : ℤ)) A =
      modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (m : ℤ))
        (modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (n : ℤ)) A) := by
  simpa using ThermalTimeMonodromyBridge.modularAutomorphismGroup_timeOfWinding_add
    (B := B.toBridgeData) (m : ℤ) (n : ℤ) A

theorem positiveBranch_full_clock_readout
    (B : PositiveBranchBridgeData (E := E)) (n : ℕ) (A : EndH E) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (n : ℤ)) A =
        B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding (n : ℤ)) A ∧
      ((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z) = logarithmicPhase (n : ℤ) ∧
      Complex.exp (((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)) = (1 : ℂ) ∧
      entropyOfStep B n = areaOfStep B n / (4 * effectiveNewtonConstant) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [toAdditiveModularFlow_apply]
  · exact deRhamClass_of_calibrated_winding (B := B.toBridgeData) (n : ℤ)
  · exact wilsonPhase_of_calibrated_winding (B := B.toBridgeData) (n : ℤ)
  · exact ryuTakayanagi_formula_of_step (B := B) n

/--
Canonical nontrivial model on the positive winding branch: depth equals the step
number itself.
-/
def identityDepthPositiveBranchBridge
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E)) : PositiveBranchBridgeData (E := E) where
  toBridgeData := B
  depthOfStep := fun n => n
  depth_zero := rfl
  depth_add := by
    intro m n
    rfl

@[simp] theorem identityDepthPositiveBranchBridge_depth
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E)) (n : ℕ) :
    (identityDepthPositiveBranchBridge (E := E) B).depthOfStep n = n := rfl

@[simp] theorem identityDepthPositiveBranchBridge_entropy
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E)) (n : ℕ) :
    entropyOfStep (identityDepthPositiveBranchBridge (E := E) B) n = subtreeEntropy n := rfl

@[simp] theorem identityDepthPositiveBranchBridge_area
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E)) (n : ℕ) :
    areaOfStep (identityDepthPositiveBranchBridge (E := E) B) n = minimalSurfaceArea n := rfl

theorem identityDepthPositiveBranchBridge_full_clock_readout
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E)) (n : ℕ) (A : EndH E) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (n : ℤ)) A =
        B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding (n : ℤ)) A ∧
      ((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z) = logarithmicPhase (n : ℤ) ∧
      Complex.exp (((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)) = (1 : ℂ) ∧
      subtreeEntropy n = minimalSurfaceArea n / (4 * effectiveNewtonConstant) := by
  simpa [identityDepthPositiveBranchBridge] using
    positiveBranch_full_clock_readout (B := identityDepthPositiveBranchBridge (E := E) B) n A

/--
Promoted physical lane: forward time is modeled by the positive winding branch.
This package records the synchronized modular/de Rham/RT readout at a
nonnegative step `n`.
-/
structure PositiveBranchClockPacket
    (B : PositiveBranchBridgeData (E := E)) (n : ℕ) (A : EndH E) : Prop where
  modular_readout :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (n : ℤ)) A =
      B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding (n : ℤ)) A
  deRham_readout :
    ((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z) = logarithmicPhase (n : ℤ)
  holonomy_readout :
    Complex.exp (((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)) = (1 : ℂ)
  rt_readout :
    entropyOfStep B n = areaOfStep B n / (4 * effectiveNewtonConstant)

/-- Canonical packet constructor for the positive branch. -/
theorem positiveBranchClockPacket_of
    (B : PositiveBranchBridgeData (E := E)) (n : ℕ) (A : EndH E) :
    PositiveBranchClockPacket (E := E) B n A := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (positiveBranch_full_clock_readout (B := B) n A).1
  · exact (positiveBranch_full_clock_readout (B := B) n A).2.1
  · exact (positiveBranch_full_clock_readout (B := B) n A).2.2.1
  · exact (positiveBranch_full_clock_readout (B := B) n A).2.2.2

/--
Primary exported forward-time model: the positive branch with identity depth.
This is the nontrivial implementation candidate for the physical lane.
-/
abbrev PhysicalForwardTimeBridge
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E)) : PositiveBranchBridgeData (E := E) :=
  identityDepthPositiveBranchBridge (E := E) B

@[simp] theorem physicalForwardTimeBridge_entropy
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E)) (n : ℕ) :
    entropyOfStep (PhysicalForwardTimeBridge (E := E) B) n = subtreeEntropy n := rfl

@[simp] theorem physicalForwardTimeBridge_area
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E)) (n : ℕ) :
    areaOfStep (PhysicalForwardTimeBridge (E := E) B) n = minimalSurfaceArea n := rfl

theorem physicalForwardTimeBridge_clockPacket
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E)) (n : ℕ) (A : EndH E) :
    PositiveBranchClockPacket (E := E) (PhysicalForwardTimeBridge (E := E) B) n A := by
  exact positiveBranchClockPacket_of (B := PhysicalForwardTimeBridge (E := E) B) n A

/--
Forward-time synchronization theorem on the promoted physical lane: one step in
the positive winding semigroup advances modular time, de Rham winding, and RT
depth together.
-/
theorem physicalForwardTimeBridge_synchronized_additivity
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E)) (m n : ℕ) (A : EndH E) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding ((m + n : ℕ) : ℤ)) A =
      modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (m : ℤ))
        (modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (n : ℤ)) A) ∧
    subtreeEntropy (m + n) = subtreeEntropy m + subtreeEntropy n ∧
    minimalSurfaceArea (m + n) = minimalSurfaceArea m + minimalSurfaceArea n := by
  refine ⟨?_, ?_, ?_⟩
  · exact modularAutomorphismGroup_timeOfStep_add (B := PhysicalForwardTimeBridge (E := E) B) m n A
  · simpa using subtreeEntropy_add m n
  · simpa using minimalSurfaceArea_add m n

end Bridge

end InfoGeometry.Canonical.RyuTakayanagiThermalTimeBridge
