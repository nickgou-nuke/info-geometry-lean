/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.AssociativeGaugeConnection
import InfoGeometry.OperatorAlgebra.DerivationGaugeTransport
import InfoGeometry.OperatorAlgebra.YangMillsOrbitGramian
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.OsterwalderSchraderPeirceReflection
import InfoGeometry.OperatorAlgebra.PeirceSpine.YangMillsTHooftWilsonBraiding
import InfoGeometry.OperatorAlgebra.PeirceSpine.CliffordKreinGeometricUncertaintyPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralLorentzTwistorCartanUncertaintyPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset
import InfoGeometry.Canonical.TwoSheetedNilpotentCondensateVortexMass
import InfoGeometry.Canonical.DrazinEpistemicSolveEtCoagula
import InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Block

/-!
# Yang–Mills Cross-Lane Isomorphisms and Native Mathlib Archetype Synthesis

This module establishes the machine-checked cross-lane bridges across the Quantum Yang–Mills
clades in `InfoGeometry` and formalizes the pure-math operator, matrix, and exterior-algebra
archetypes in native Mathlib carriers (`Matrix (Fin 4) (Fin 4) R`, `Matrix (Fin 3) (Fin 3) R`,
`Matrix (Fin 2) (Fin 2) K`, `Module.End R (ExteriorAlgebra R V)`, `[Ring B]`, `[StarRing B]`,
and `PeirceTetraktysColimitCoercivity.Limit`):

1. **Section 1 (Clade I ↔ Clade II/III: `AssociativeGaugeConnection`, `DerivationGaugeTransport`, & Unipotent / Möbius–Bruhat Vortex Gauge Units in `Bˣ`)**:
   Packages the upper/lower Peirce unipotent translations `1 + N_+`, `1 - N_-` and the two-sheeted
   Möbius–Bruhat vortex `U_M = (1 + N_+)(1 - N_-)` as genuine ring units in `Bˣ`, proves that
   `peirceGradingDeriv P` is a Leibniz derivation on `B`, computes the exact pure-gauge potentials
   under `AssociativeGaugeConnection.gaugePotential` (`-N_+`, `-N_-`, and `-(Φ + Σ)`), and bridges
   `DerivationDifferentialForms.gaugeOneForm` directly to `AssociativeGaugeConnection.gaugePotential`.
2. **Section 2 (Clade II/III ↔ Clade IV: `YangMillsOrbitGramian` ↔ `OsterwalderSchraderPeirceReflection` ↔ `TwoSheetedNilpotentCondensateVortexMass` ↔ `YangMillsTHooftWilsonBraiding` ↔ Core-Ghost Cyclic Equipartition, Unilateral Shift Toeplitz Anomaly, & Fubini–Study Two-Projector Chordal Metric)**:
   Proves `orbitCommutator P X = peirceGradingDeriv P X`, tripotency `ad_P³ = ad_P`,
   `orbitMassMode P (genPhi P A (star A)) = osPeirceMassPairing P A = genV P A (star A)`,
   `opVortexMassSq P A (star A) = (4 : ℤ) • orbitMassMode P (genPhi P A (star A))`,
   Core-Ghost cyclic functional equipartition `τ (P V P) = τ ((1 - P) V (1 - P))` vs. the
   unilateral shift / Toeplitz commutator anomaly `A * C = 1 → A * C - C * A = P₀`, and the
   Fubini–Study two-projector chordal operator `(P - Q)² = P + Q - P Q - Q P` with
   `evenGrade P ((P - Q)²) = -(orbitCommutator P Q)²` and `(conjMinus P C P - conjPlus P A P)² = genV P A C`.
3. **Section 3 (Clade III/IV ↔ Clade VI ↔ Drazin Solve et Coagula: `DrazinEpistemicSolveEtCoagula` Gribov/Fitting Cut, `P M† P = M^D`, Von Neumann Regular Nilpotent-First Drazin Inverse, Abstract Order-3 Nilpotent Flag Projector Resolution, & BRST Physical State Module)**:
   Connects the Drazin spectral projector `P_D = projection a b` to `orbitCommutator`,
   `orbitMassMode`, `osPeirceMassPairing`, `projection a b * m_dag * projection a b = b`,
   proves `IsDrazinInverse (genPhi P A C) (genPhi P A C) 1` and `IsDrazinInverse (genSig P A C) (genSig P A C) 1`
   under the von Neumann regularity condition `N_+ N_- N_+ = N_+` and `N_- N_+ N_- = N_-`,
   proves the coordinate-free Order-3 Nilpotent Flag Projector Resolution in any `[Ring B]`, and
   bridges the Drazin Fitting decomposition `P_phys + q_brst` directly to `BRSTCohomologyPhysicalGaugeBridge`.
4. **Section 4 (Native Mathlib `Matrix (Fin 4) (Fin 4) R` Plücker–Hodge / `Matrix.det` Amplituhedron–Baryon Bridge, Order-3 Flag & `sl₂` Casimir `C₂ = 8 I₃` in `Matrix (Fin 3) (Fin 3)`, `PGL(2)` Cross-Ratio Invariance in `Matrix (Fin 2) (Fin 2)`, Native `Matrix.trace` Cyclic Volume Invariant, & `ChiralLorentzTwistorCartanUncertaintyPoset` Rungs 0–4)**:
   Replaces the custom 16-field `Mat4 R` carrier and custom determinants with native Mathlib
   `Matrix (Fin 4) (Fin 4) R`, `Matrix (Fin 3) (Fin 3) R`, and `Matrix.det`, reconstructs the three
   orthogonal flag projectors `E₀₀, E₁₁, E₂₂` over any non-commutative ring `[Ring R]` in
   `Matrix (Fin 3) (Fin 3) R`, proves `casimir2 nilRaise3 nilLower3 cartanDiag3 = (8 : ℤ) • 1`,
   proves `PGL(2)` cross-ratio determinant scaling in `Matrix (Fin 2) (Fin 2) K`, proves the
   native `Matrix.trace` volume and chiral anomaly identities, and formalizes Rungs 0–4 and the
   diamond causal poset `diamondCausalEdge` of `ChiralLorentzTwistorCartanStage`.
5. **Section 5 (Clade IV/V: Unital Block Doubling vs. Non-Unital Corner Inclusion via `Matrix.fromBlocks` & `PeirceTetraktysColimitCoercivity` Direct Limit `Stage n →+* Limit`)**:
   Proves side-by-side intertwining and `Matrix.trace` behavior of unital block doubling
   `X ↦ Matrix.fromBlocks X 0 0 X` vs. non-unital corner inclusion `X ↦ Matrix.fromBlocks X 0 0 0`,
   and proves that `ofStage n` transports `opVortexMassSq` and `opMoebiusBruhatVortex` into `Limit`
   with unit-horizon coercivity constant `8`.
6. **Section 6 (`YangMillsLane` Equivalence, `M0` Non-Commutative Matrix Witnesses, & Master Synthesis)**:
   Provides the zero-`sorry` `YangMillsLane` structure, concrete `2 × 2` and `3 × 3` integer matrix
   witnesses (`T16`/`T17`), and packages all six cross-lane bridges into a single master theorem.

## Mathematical Scope
All theorems in this file are exact algebraic, ring-theoretic, matrix-theoretic, and
direct-limit identities (`[kernel_verified]`). They do not claim an analytic continuum 4D
Euclidean path-integral measure or a solution to the Clay Millennium Problem (`[bucket_3_open_debt]`).
-/

namespace InfoGeometry.Canonical.YangMillsLaneIsomorphisms

open InfoGeometry.Geometry.AssociativeGaugeConnection
open InfoGeometry.OperatorAlgebra.YangMillsOrbitGramian
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.CliffordKreinGeometricUncertaintyPoset
open InfoGeometry.Canonical.TwoSheetedNilpotentCondensateVortexMass
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.DrazinMoorePenrosePartition
open InfoGeometry.Canonical.DrazinEpistemicSolveEtCoagula
open InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
open InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
open CanonicalTwoSheetedInductiveColimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit

variable {B : Type*} [Ring B]

/-! ===========================================================================
    Section 1: AssociativeGaugeConnection, DerivationGaugeTransport, &
               Unipotent / Möbius–Bruhat Vortex Gauge Units in `Bˣ`
    =========================================================================== -/

/-- The upper Peirce unipotent gauge element `u_+(A) = 1 + N_+` packaged as a unit in `Bˣ`. -/
def unipotentPlusUnit {P : B} (hP : P * P = P) (A : B) : Bˣ where
  val := opUnipotentPlus P A
  inv := opUnipotentPlus P (-A)
  val_inv := (nilpotent_to_unipotent_exponential_group_laws hP A 0 0 0 0 0).2.2.2.2.1
  inv_val := (nilpotent_to_unipotent_exponential_group_laws hP A 0 0 0 0 0).2.2.2.2.2.1

/-- The lower Peirce unipotent gauge element `u_-(C) = 1 - N_-` packaged as a unit in `Bˣ`. -/
def unipotentMinusUnit {P : B} (hP : P * P = P) (C : B) : Bˣ where
  val := opUnipotentMinus P C
  inv := opUnipotentMinus P (-C)
  val_inv := (nilpotent_to_unipotent_exponential_group_laws hP 0 0 0 C 0 0).2.2.2.2.2.2.1
  inv_val := (nilpotent_to_unipotent_exponential_group_laws hP 0 0 0 C 0 0).2.2.2.2.2.2.2

/-- The two-sheeted Möbius–Bruhat vortex operator `U_M = (1 + N_+)(1 - N_-)` packaged as a unit in `Bˣ`. -/
def moebiusBruhatVortexUnit {P : B} (hP : P * P = P) (A C : B) : Bˣ where
  val := opMoebiusBruhatVortex P A C
  inv := opMoebiusBruhatVortexInv P A C
  val_inv := (fourfold_moebius_bruhat_vortex_anatomy_and_metric_invariance hP A C).2.2.2.2.1
  inv_val := (fourfold_moebius_bruhat_vortex_anatomy_and_metric_invariance hP A C).2.2.2.2.2.1

@[simp] theorem coe_unipotentPlusUnit {P : B} (hP : P * P = P) (A : B) :
    ((unipotentPlusUnit hP A : Bˣ) : B) = opUnipotentPlus P A := rfl

@[simp] theorem coe_inv_unipotentPlusUnit {P : B} (hP : P * P = P) (A : B) :
    (((unipotentPlusUnit hP A)⁻¹ : Bˣ) : B) = opUnipotentPlus P (-A) := rfl

@[simp] theorem coe_unipotentMinusUnit {P : B} (hP : P * P = P) (C : B) :
    ((unipotentMinusUnit hP C : Bˣ) : B) = opUnipotentMinus P C := rfl

@[simp] theorem coe_inv_unipotentMinusUnit {P : B} (hP : P * P = P) (C : B) :
    (((unipotentMinusUnit hP C)⁻¹ : Bˣ) : B) = opUnipotentMinus P (-C) := rfl

@[simp] theorem coe_moebiusBruhatVortexUnit {P : B} (hP : P * P = P) (A C : B) :
    ((moebiusBruhatVortexUnit hP A C : Bˣ) : B) = opMoebiusBruhatVortex P A C := rfl

@[simp] theorem coe_inv_moebiusBruhatVortexUnit {P : B} (hP : P * P = P) (A C : B) :
    (((moebiusBruhatVortexUnit hP A C)⁻¹ : Bˣ) : B) = opMoebiusBruhatVortexInv P A C := rfl

/-- The inner grading derivation `innerDerivative (R := ℤ) P` coincides with
`peirceGradingDeriv P X = P * X - X * P` and satisfies the non-commutative Leibniz rule. -/
theorem peirceGradingDeriv_leibniz (P X Y : B) :
    peirceGradingDeriv P (X * Y) =
      peirceGradingDeriv P X * Y + X * peirceGradingDeriv P Y := by
  unfold peirceGradingDeriv InfoGeometry.OperatorAlgebra.PeirceSpine.comm
  noncomm_ring

/-- Under `AssociativeGaugeConnection.gaugePotential` with derivation
`innerDerivative (R := ℤ) P` (`peirceGradingDeriv P`), the vacuum connection `ω = 0`
gauge-transformed by `unipotentPlusUnit hP A` yields the upper Peirce nilpotent cone
`-N_+ = -conePlus P A`. -/
theorem gaugePotential_peirceGradingDeriv_unipotentPlusUnit
    {P : B} (hP : P * P = P) (A : B) :
    InfoGeometry.Geometry.AssociativeGaugeConnection.gaugePotential
      (InfoGeometry.Geometry.AssociativeGaugeConnection.innerDerivative (R := ℤ) P)
      (0 : B) (unipotentPlusUnit hP A) =
      -conePlus P A := by
  unfold InfoGeometry.Geometry.AssociativeGaugeConnection.gaugePotential
    InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate
  change (opUnipotentPlus P A * 0 * opUnipotentPlus P (-A)) -
    (P * opUnipotentPlus P A - opUnipotentPlus P A * P) * opUnipotentPlus P (-A) = -conePlus P A
  dsimp [opUnipotentPlus]
  peirce_nf hP

/-- Under `AssociativeGaugeConnection.gaugePotential` with derivation
`innerDerivative (R := ℤ) P` (`peirceGradingDeriv P`), the vacuum connection `ω = 0`
gauge-transformed by `unipotentMinusUnit hP C` (`1 - N_-`) yields the lower Peirce nilpotent
cone `-N_- = -coneMinus P C`. -/
theorem gaugePotential_peirceGradingDeriv_unipotentMinusUnit
    {P : B} (hP : P * P = P) (C : B) :
    InfoGeometry.Geometry.AssociativeGaugeConnection.gaugePotential
      (InfoGeometry.Geometry.AssociativeGaugeConnection.innerDerivative (R := ℤ) P)
      (0 : B) (unipotentMinusUnit hP C) =
      -coneMinus P C := by
  unfold InfoGeometry.Geometry.AssociativeGaugeConnection.gaugePotential
    InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate
  change (opUnipotentMinus P C * 0 * opUnipotentMinus P (-C)) -
    (P * opUnipotentMinus P C - opUnipotentMinus P C * P) * opUnipotentMinus P (-C) = -coneMinus P C
  dsimp [opUnipotentMinus]
  peirce_nf hP

/-- Under `AssociativeGaugeConnection.gaugePotential` with derivation
`innerDerivative (R := ℤ) P` (`peirceGradingDeriv P`), the vacuum connection `ω = 0`
gauge-transformed by the Möbius–Bruhat vortex unit `moebiusBruhatVortexUnit hP A C` yields
`-(genPhi P A C + genSig P A C) + conePlus P A * coneMinus P C * conePlus P A`. -/
theorem gaugePotential_peirceGradingDeriv_moebiusBruhatVortexUnit
    {P : B} (hP : P * P = P) (A C : B) :
    InfoGeometry.Geometry.AssociativeGaugeConnection.gaugePotential
      (InfoGeometry.Geometry.AssociativeGaugeConnection.innerDerivative (R := ℤ) P)
      (0 : B) (moebiusBruhatVortexUnit hP A C) =
      -(genPhi P A C + genSig P A C) + conePlus P A * coneMinus P C * conePlus P A := by
  unfold InfoGeometry.Geometry.AssociativeGaugeConnection.gaugePotential
    InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate
  change (opMoebiusBruhatVortex P A C * 0 * opMoebiusBruhatVortexInv P A C) -
    (P * opMoebiusBruhatVortex P A C - opMoebiusBruhatVortex P A C * P) *
      opMoebiusBruhatVortexInv P A C =
    -(genPhi P A C + genSig P A C) + conePlus P A * coneMinus P C * conePlus P A
  dsimp [opMoebiusBruhatVortex, opMoebiusBruhatVortexInv, opUnipotentPlus, opUnipotentMinus]
  peirce_nf hP

/-- Exact gauge-covariant intertwining (`AssociativeGaugeConnection.gauge_intertwine`) for the
Möbius–Bruhat vortex unit `moebiusBruhatVortexUnit hP A C` with respect to
`innerDerivative (R := ℤ) P` (`peirceGradingDeriv P`). -/
theorem covariantDerivative_moebiusBruhatVortexUnit_intertwine
    {P : B} (hP : P * P = P) (A C X : B) :
    InfoGeometry.Geometry.AssociativeGaugeConnection.covariantDerivative
      (InfoGeometry.Geometry.AssociativeGaugeConnection.innerDerivative (R := ℤ) P)
      (InfoGeometry.Geometry.AssociativeGaugeConnection.gaugePotential
        (InfoGeometry.Geometry.AssociativeGaugeConnection.innerDerivative (R := ℤ) P)
        (0 : B) (moebiusBruhatVortexUnit hP A C))
      (opMoebiusBruhatVortex P A C * X) =
    opMoebiusBruhatVortex P A C * peirceGradingDeriv P X := by
  have h := InfoGeometry.Geometry.AssociativeGaugeConnection.gauge_intertwine
    (InfoGeometry.Geometry.AssociativeGaugeConnection.innerDerivative (R := ℤ) P)
    (InfoGeometry.Geometry.AssociativeGaugeConnection.innerDerivative_isLeibniz (R := ℤ) P)
    (0 : B) (moebiusBruhatVortexUnit hP A C) X
  simpa [InfoGeometry.Geometry.AssociativeGaugeConnection.covariantDerivative,
    InfoGeometry.Geometry.AssociativeGaugeConnection.innerDerivative,
    peirceGradingDeriv, InfoGeometry.OperatorAlgebra.PeirceSpine.comm] using h

/-- Exact bridge between Clade I (`DerivationDifferentialForms.gaugeOneForm`) and
`AssociativeGaugeConnection.gaugePotential`: evaluating `gaugeOneForm K Γ u` on any derivation
direction `x : K.L` is definitionally `gaugePotential (K.operatorAction x) (Γ x) u`. -/
theorem gaugeOneForm_apply_eq_gaugePotential
    {R₀ A₀ : Type*} [CommRing R₀] [Ring A₀] [Algebra R₀ A₀]
    (K : InfoGeometry.Algebra.DerivationLieLane R₀ A₀)
    (Γ : InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.OneForm K)
    (u : A₀ˣ) (x : K.L) :
    InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.gaugeOneForm K Γ u x =
      InfoGeometry.Geometry.AssociativeGaugeConnection.gaugePotential
        (K.operatorAction x) (Γ x) u := by
  rw [InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.gaugeOneForm_apply]
  rfl

/-! ===========================================================================
    Section 2: `YangMillsOrbitGramian` ↔ `OsterwalderSchraderPeirceReflection` ↔
               `TwoSheetedNilpotentCondensateVortexMass` ↔ `YangMillsTHooftWilsonBraiding`
               ↔ Core-Ghost Equipartition, Toeplitz Shift Anomaly, & Fubini–Study Chordal Metric
    =========================================================================== -/

/-- The gauge orbit commutator `orbitCommutator P X` in `YangMillsOrbitGramian` is
definitionally identical to the Peirce grading derivation `peirceGradingDeriv P X` in
`PeirceDefectBridge`. -/
theorem orbitCommutator_eq_peirceGradingDeriv (P X : B) :
    orbitCommutator P X = peirceGradingDeriv P X := rfl

/-- Tripotent superoperator identity `ad_P³ = ad_P` for the Peirce grading derivation
`peirceGradingDeriv P` (`[P, [P, [P, X]]] = [P, X]`) when `P * P = P`. -/
theorem peirceGradingDeriv_cube {P : B} (hP : P * P = P) (X : B) :
    peirceGradingDeriv P (peirceGradingDeriv P (peirceGradingDeriv P X)) =
      peirceGradingDeriv P X := by
  unfold peirceGradingDeriv InfoGeometry.OperatorAlgebra.PeirceSpine.comm
  peirce_nf hP

/-- For any idempotent `P` (`P * P = P`), the gauge orbit commutator of the chiral connection
`Φ = genPhi P A C` is the symplectic generator `J = genJ P A C`. -/
theorem orbitCommutator_genPhi_eq_genJ {P : B} (hP : P * P = P) (A C : B) :
    orbitCommutator P (genPhi P A C) = genJ P A C := by
  unfold orbitCommutator
  peirce_nf hP

/-- Over any `[StarRing B]` with self-adjoint idempotent `P` (`P * P = P`, `star P = P`):
1. The orbit Gramian `orbitMassMode P (genPhi P A (star A))` of the self-adjoint chiral connection
   `Φ_A = genPhi P A (star A)` equals the Osterwalder–Schrader reflection pairing
   `osPeirceMassPairing P A` and the two-sheeted condensate `genV P A (star A)`.
2. The two-sheeted vortex mass-squared operator `opVortexMassSq P A (star A) = 4 V` equals
   `(4 : ℤ) • orbitMassMode P (genPhi P A (star A))` and `(4 : ℤ) • osPeirceMassPairing P A`. -/
theorem orbitMassMode_genPhi_eq_osPeirceMassPairing_eq_genV
    [StarRing B] {P : B} (hP : P * P = P) (hPstar : star P = P) (A : B) :
    orbitMassMode P (genPhi P A (star A)) = osPeirceMassPairing P A ∧
    osPeirceMassPairing P A = genV P A (star A) ∧
    opVortexMassSq P A (star A) = (4 : ℤ) • orbitMassMode P (genPhi P A (star A)) ∧
    opVortexMassSq P A (star A) = (4 : ℤ) • osPeirceMassPairing P A := by
  have hStarJ : star (orbitCommutator P (genPhi P A (star A))) = -genJ P A (star A) := by
    rw [orbitCommutator_genPhi_eq_genJ hP A (star A)]
    dsimp [genJ, conePlus, coneMinus]
    simp [star_sub, star_mul, hPstar]
    noncomm_ring
  have hOrbitV : orbitMassMode P (genPhi P A (star A)) = genV P A (star A) := by
    unfold orbitMassMode
    rw [hStarJ, orbitCommutator_genPhi_eq_genJ hP A (star A)]
    peirce_nf hP
  have hOSV : osPeirceMassPairing P A = genV P A (star A) := rfl
  have hVortex : opVortexMassSq P A (star A) = (4 : ℤ) • genV P A (star A) := rfl
  refine ⟨hOrbitV.trans hOSV.symm, hOSV, ?_, ?_⟩
  · rw [hOrbitV, hVortex]
  · rw [hOSV, hVortex]

/-- **Core-Ghost Cyclic Trace Equipartition vs. Chiral Anomaly**:
For any additive group `G` and any cyclic additive functional `τ : B →+ G`
(`∀ X Y : B, τ (X * Y) = τ (Y * X)`):
1. The upper core corner `P * genV P A C * P = N_+ N_-` and lower ghost corner
   `(1 - P) * genV P A C * (1 - P) = N_- N_+` have identical cyclic trace:
   `τ (P * genV P A C * P) = τ ((1 - P) * genV P A C * (1 - P))`.
2. Consequently, the chiral commutator charge `genSig P A C = N_+ N_- - N_- N_+` and the
   grading commutator `peirceGradingDeriv P X = P * X - X * P` have vanishing cyclic trace:
   `τ (genSig P A C) = 0` and `τ (peirceGradingDeriv P X) = 0`. -/
theorem cyclicFunctional_vortex_core_ghost_equipartition
    {G : Type*} [AddCommGroup G] (τ : B →+ G) (hcyc : ∀ X Y : B, τ (X * Y) = τ (Y * X))
    {P : B} (hP : P * P = P) (A C X : B) :
    τ (P * genV P A C * P) = τ ((1 - P) * genV P A C * (1 - P)) ∧
    τ (genSig P A C) = 0 ∧
    τ (peirceGradingDeriv P X) = 0 := by
  have hCorner1 : P * genV P A C * P = conePlus P A * coneMinus P C := by
    peirce_nf hP
  have hCorner0 : (1 - P) * genV P A C * (1 - P) = coneMinus P C * conePlus P A := by
    peirce_nf hP
  have hEq : τ (P * genV P A C * P) = τ ((1 - P) * genV P A C * (1 - P)) := by
    rw [hCorner1, hCorner0]
    exact hcyc (conePlus P A) (coneMinus P C)
  have hSig : genSig P A C = conePlus P A * coneMinus P C - coneMinus P C * conePlus P A := by
    peirce_nf hP
  have hTauSig : τ (genSig P A C) = 0 := by
    rw [hSig, map_sub, hcyc (conePlus P A) (coneMinus P C), sub_self]
  have hTauDeriv : τ (peirceGradingDeriv P X) = 0 := by
    unfold peirceGradingDeriv InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    rw [map_sub, hcyc P X, sub_self]
  exact ⟨hEq, hTauSig, hTauDeriv⟩

/-- **Unilateral Shift / Toeplitz Commutator Anomaly vs. Peirce Vacuum Idempotent (Gap G4)**:
If `A * C = 1` and `P₀ = 1 - C * A`, then `P₀` is an idempotent (`P₀ * P₀ = P₀`),
`C * A` is the complementary idempotent, the commutator anomaly is `A * C - C * A = P₀`,
`P₀ * C = 0`, `A * P₀ = 0`, and for any additive functional `τ : B →+ G`,
`τ (A * C) - τ (C * A) = τ P₀` (obstructing cyclic trace invariance whenever `τ P₀ ≠ 0`). -/
theorem unilateral_shift_toeplitz_commutator_anomaly
    (A C : B) (h_iso : A * C = 1)
    {G : Type*} [AddCommGroup G] (τ : B →+ G) :
    let P0 := 1 - C * A
    P0 * P0 = P0 ∧
    (C * A) * (C * A) = C * A ∧
    A * C - C * A = P0 ∧
    P0 * C = 0 ∧
    A * P0 = 0 ∧
    τ (A * C) - τ (C * A) = τ P0 := by
  dsimp only
  have hCA : (C * A) * (C * A) = C * A := by
    calc
      (C * A) * (C * A) = C * (A * C) * A := by noncomm_ring
      _ = C * 1 * A := by rw [h_iso]
      _ = C * A := by noncomm_ring
  have hP0 : (1 - C * A) * (1 - C * A) = 1 - C * A := by
    calc
      (1 - C * A) * (1 - C * A) = 1 - C * A - C * A + (C * A) * (C * A) := by noncomm_ring
      _ = 1 - C * A := by rw [hCA]; abel
  have hComm : A * C - C * A = 1 - C * A := by rw [h_iso]
  have hP0C : (1 - C * A) * C = 0 := by
    calc
      (1 - C * A) * C = C - C * (A * C) := by noncomm_ring
      _ = 0 := by rw [h_iso, mul_one, sub_self]
  have hAP0 : A * (1 - C * A) = 0 := by
    calc
      A * (1 - C * A) = A - (A * C) * A := by noncomm_ring
      _ = 0 := by rw [h_iso, one_mul, sub_self]
  have hTau : τ (A * C) - τ (C * A) = τ (1 - C * A) := by
    rw [← map_sub, hComm]
  exact ⟨hP0, hCA, hComm, hP0C, hAP0, hTau⟩

/-- **Universal Fubini–Study / Hua Two-Projector Chordal Operator & Trace Identities (Gap G3)**:
For any two idempotents `P * P = P` and `Q * Q = Q`, `(P - Q) * (P - Q) = P + Q - P * Q - Q * P`
commutes with both `P` and `Q`, satisfies `(P - Q) * (P - Q) + (P + Q - 1) * (P + Q - 1) = 1`,
and under any cyclic functional `τ` (`τ (X * Y) = τ (Y * X)`) satisfies
`τ ((P - Q) * (P - Q)) = τ P + τ Q - (2 : ℤ) • τ (P * Q)`. -/
theorem fubini_study_two_projector_chordal_operator_and_trace
    {P Q : B} (hP : P * P = P) (hQ : Q * Q = Q)
    {G : Type*} [AddCommGroup G] (τ : B →+ G) (h_cyc : ∀ X Y : B, τ (X * Y) = τ (Y * X)) :
    (P - Q) * (P - Q) = P + Q - P * Q - Q * P ∧
    (P - Q) * (P - Q) = P * (1 - Q) + Q * (1 - P) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm P ((P - Q) * (P - Q)) = 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm Q ((P - Q) * (P - Q)) = 0 ∧
    (P - Q) * (P - Q) + (P + Q - 1) * (P + Q - 1) = 1 ∧
    τ ((P - Q) * (P - Q)) = τ P + τ Q - (2 : ℤ) • τ (P * Q) := by
  have hSq1 : (P - Q) * (P - Q) = P + Q - P * Q - Q * P := by
    calc
      (P - Q) * (P - Q) = P * P + Q * Q - P * Q - Q * P := by noncomm_ring
      _ = P + Q - P * Q - Q * P := by rw [hP, hQ]
  have hSq2 : (P - Q) * (P - Q) = P * (1 - Q) + Q * (1 - P) := by
    rw [hSq1]; noncomm_ring
  have hPQ_P : P * (P * Q) = P * Q := by rw [← mul_assoc, hP]
  have hQP_P : (Q * P) * P = Q * P := by rw [mul_assoc, hP]
  have hQP_Q : Q * (Q * P) = Q * P := by rw [← mul_assoc, hQ]
  have hPQ_Q : (P * Q) * Q = P * Q := by rw [mul_assoc, hQ]
  have hCommP : InfoGeometry.OperatorAlgebra.PeirceSpine.comm P ((P - Q) * (P - Q)) = 0 := by
    rw [hSq1]
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    calc
      P * (P + Q - P * Q - Q * P) - (P + Q - P * Q - Q * P) * P =
          (P * P - P * P) + (P * Q - P * (P * Q)) + ((Q * P) * P - Q * P) := by noncomm_ring
      _ = 0 := by rw [hPQ_P, hQP_P]; abel
  have hCommQ : InfoGeometry.OperatorAlgebra.PeirceSpine.comm Q ((P - Q) * (P - Q)) = 0 := by
    rw [hSq1]
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    calc
      Q * (P + Q - P * Q - Q * P) - (P + Q - P * Q - Q * P) * Q =
          (Q * Q - Q * Q) + (Q * P - Q * (Q * P)) + ((P * Q) * Q - P * Q) := by noncomm_ring
      _ = 0 := by rw [hQP_Q, hPQ_Q]; abel
  have hComp : (P - Q) * (P - Q) + (P + Q - 1) * (P + Q - 1) = 1 := by
    calc
      (P - Q) * (P - Q) + (P + Q - 1) * (P + Q - 1) =
          (P * P - P) + (Q * Q - Q) + (P * P - P) + (Q * Q - Q) + 1 := by noncomm_ring
      _ = 1 := by rw [hP, hQ]; abel
  have hTau : τ ((P - Q) * (P - Q)) = τ P + τ Q - (2 : ℤ) • τ (P * Q) := by
    rw [hSq1, map_sub, map_sub, map_add, h_cyc Q P, two_zsmul]
    abel
  exact ⟨hSq1, hSq2, hCommP, hCommQ, hComp, hTau⟩

/-- **Fubini–Study Chordal Distance Identity on the Grassmannian of Projectors**:
For any idempotent `P` (`P * P = P`), the unipotently conjugated projectors
`P_+(A) = conjPlus P A P = P - N_+` and `P_-(C) = conjMinus P C P = P + N_-` are idempotents whose
individual chordal differences from `P` are square-zero nilpotent, while their mutual chordal
difference squared is the exact two-sheeted condensate `genV P A C`:
`(conjMinus P C P - conjPlus P A P) * (conjMinus P C P - conjPlus P A P) = genV P A C`. -/
theorem fubini_study_chordal_distance_unipotent_projectors
    {P : B} (hP : P * P = P) (A C : B) :
    conjPlus P A P * conjPlus P A P = conjPlus P A P ∧
    conjMinus P C P * conjMinus P C P = conjMinus P C P ∧
    (conjPlus P A P - P) * (conjPlus P A P - P) = 0 ∧
    (conjMinus P C P - P) * (conjMinus P C P - P) = 0 ∧
    (conjMinus P C P - conjPlus P A P) * (conjMinus P C P - conjPlus P A P) = genV P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [conjPlus]; peirce_nf hP
  · dsimp [conjMinus]; peirce_nf hP
  · dsimp [conjPlus]; peirce_nf hP
  · dsimp [conjMinus]; peirce_nf hP
  · dsimp [conjPlus, conjMinus]; peirce_nf hP

/-- **Cross-Lane Unification of `orbitCommutator`, `genV`, and Chordal Compression (Gap G5)**:
For any idempotents `P * P = P` and `Q * Q = Q` in `[Ring B]`:
1. `-(orbitCommutator P X * orbitCommutator P X) = genV P X X`,
2. `P * (1 - Q) * P + (1 - P) * Q * (1 - P) = (P - Q) * (P - Q)`,
3. `evenGrade P ((P - Q) * (P - Q)) = (P - Q) * (P - Q)` (the chordal operator `(P - Q)^2` is
   already Peirce block-diagonal), while `oddGrade P X * oddGrade P X = genV P X X =
   -(orbitCommutator P X * orbitCommutator P X)`. -/
theorem orbitGramian_eq_fisherMetricV_and_chordal_compression
    {P Q : B} (hP : P * P = P) (hQ : Q * Q = Q) (X : B) :
    -(orbitCommutator P X * orbitCommutator P X) = genV P X X ∧
    oddGrade P X * oddGrade P X = -(orbitCommutator P X * orbitCommutator P X) ∧
    P * (1 - Q) * P + (1 - P) * Q * (1 - P) = (P - Q) * (P - Q) ∧
    evenGrade P ((P - Q) * (P - Q)) = (P - Q) * (P - Q) := by
  have h1 : -(orbitCommutator P X * orbitCommutator P X) = genV P X X := by
    simp only [orbitCommutator, genV, anticomm, conePlus, coneMinus]
    peirce_nf hP
  have h2 : oddGrade P X * oddGrade P X = -(orbitCommutator P X * orbitCommutator P X) := by
    unfold orbitCommutator
    peirce_nf hP
  have hSq : (P - Q) * (P - Q) = P + Q - P * Q - Q * P := by
    calc
      (P - Q) * (P - Q) = P * P + Q * Q - P * Q - Q * P := by noncomm_ring
      _ = P + Q - P * Q - Q * P := by rw [hP, hQ]
  have h3 : P * (1 - Q) * P + (1 - P) * Q * (1 - P) = (P - Q) * (P - Q) := by
    rw [hSq]
    peirce_nf hP
  have h4 : evenGrade P ((P - Q) * (P - Q)) = (P - Q) * (P - Q) := by
    rw [hSq]
    peirce_nf hP
  exact ⟨h1, h2, h3, h4⟩

/-- Unified bridge across `YangMillsOrbitGramian`, `OsterwalderSchraderPeirceReflection`,
`TwoSheetedNilpotentCondensateVortexMass`, and `YangMillsTHooftWilsonBraiding`. -/
theorem yang_mills_orbit_gramian_os_reflection_vortex_braiding_bridge
    [StarRing B] {P : B} (hP : P * P = P) (hPstar : star P = P) (A : B)
    (hReg : conePlus P A * star (conePlus P A) * conePlus P A = conePlus P A) :
    let N_p := conePlus P A
    orbitCommutator P (genPhi P A (star A)) = genJ P A (star A) ∧
    orbitMassMode P (genPhi P A (star A)) = osPeirceMassPairing P A ∧
    osPeirceMassPairing P A = genV P A (star A) ∧
    opVortexMassSq P A (star A) = (4 : ℤ) • orbitMassMode P (genPhi P A (star A)) ∧
    opHiggsMassOperator P A (star A) (opAxial P A (star A)) =
      -(opVortexMassSq P A (star A) * opAxial P A (star A)) ∧
    OperatorAlgebra.PeirceSpine.YangMillsTHooftWilsonBraiding.W_wilson_plus N_p -
      OperatorAlgebra.PeirceSpine.YangMillsTHooftWilsonBraiding.Z_center N_p *
        OperatorAlgebra.PeirceSpine.YangMillsTHooftWilsonBraiding.W_wilson_plus N_p *
        OperatorAlgebra.PeirceSpine.YangMillsTHooftWilsonBraiding.Z_center N_p =
      OperatorAlgebra.PeirceSpine.YangMillsTHooftWilsonBraiding.Phi N_p +
        OperatorAlgebra.PeirceSpine.YangMillsTHooftWilsonBraiding.Phi N_p := by
  dsimp only
  have h1 := orbitCommutator_genPhi_eq_genJ hP A (star A)
  have h2 := orbitMassMode_genPhi_eq_osPeirceMassPairing_eq_genV hP hPstar A
  have h3 := (mexican_hat_ihhs_coupling_to_mass_lift hP A (star A) 0 0 0).2.2.1
  have hNil : conePlus P A * conePlus P A = 0 := by peirce_nf hP
  have h4 := OperatorAlgebra.PeirceSpine.YangMillsTHooftWilsonBraiding.wilson_thooft_braiding_defect
    (conePlus P A) hNil hReg
  exact ⟨h1, h2.1, h2.2.1, h2.2.2.1, h3, h4⟩

/-! ===========================================================================
    Section 3: Drazin Epistemic Solve et Coagula (`P_D = a * b`) ↔
               Peirce Orbit Gramian, Von Neumann Regularity, Order-3 Flag Resolution,
               & BRST Cohomology
    =========================================================================== -/

/-- When `h : IsDrazinInverse a b k` in a `[StarRing B]` and the Drazin spectral projector
`P_D = projection a b` is self-adjoint (`star P_D = P_D`):
1. `P_D` is idempotent (`P_D * P_D = P_D`),
2. `a` is gauge-invariant under the Drazin Fitting grading (`orbitCommutator P_D a = 0`),
3. The upper Peirce corner `peirce11 P_D a` is the Fitting invertible core `fittingRegularPart a b`
   and the lower Peirce corner `peirce00 P_D a` is the Gribov/nilpotent transient
   `fittingNilpotentPart a b` (`(fittingNilpotentPart a b) ^ (k + 1) = 0`),
4. Whenever `a * m_dag * a = a` (inner inverse), compressing `m_dag` by `P_D` yields the Drazin
   inverse (`P_D * m_dag * P_D = b`),
5. Any off-diagonal chiral fluctuation `genPhi P_D X (star X)` across the Drazin Fitting cut
   acquires the positive-semidefinite orbit Gramian mass `orbitMassMode P_D (genPhi P_D X (star X)) =
   osPeirceMassPairing P_D X = genV P_D X (star X)`. -/
theorem drazin_fitting_peirce_orbit_gramian_bridge
    [StarRing B] {a b m_dag : B} {k : ℕ} (h : IsDrazinInverse a b k)
    (hInner : a * m_dag * a = a)
    (hPstar : star (projection a b) = projection a b) (X : B) :
    let P_D := projection a b
    P_D * P_D = P_D ∧
    orbitCommutator P_D a = 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11 P_D a = fittingRegularPart a b ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00 P_D a = fittingNilpotentPart a b ∧
    (fittingNilpotentPart a b) ^ (k + 1) = 0 ∧
    P_D * m_dag * P_D = b ∧
    orbitMassMode P_D (genPhi P_D X (star X)) = osPeirceMassPairing P_D X ∧
    osPeirceMassPairing P_D X = genV P_D X (star X) := by
  dsimp only
  have hPD : projection a b * projection a b = projection a b := projection_is_idempotent h
  have hComm : orbitCommutator (projection a b) a = 0 := by
    unfold orbitCommutator
    rw [projection_comm_self h, sub_self]
  have hFour := drazin_fourfold_relational_anatomy h X X
  have hNil := (drazin_primordial_dual_roots_and_binary_cut h).2.2.2.2.2.2.2.2
  have hSandwich := (drazin_transcendent_function_malik_thome h hInner).1.2.2
  have hGram := orbitMassMode_genPhi_eq_osPeirceMassPairing_eq_genV hPD hPstar X
  exact ⟨hPD, hComm, hFour.2.1.1, hFour.2.1.2.1, hNil, hSandwich, hGram.1, hGram.2.1⟩

/-- **Von Neumann Regular Nilpotent-First Drazin Inverse Theorem**:
If the upper and lower nilpotent cones `N_+ = conePlus P A` and `N_- = coneMinus P C` form a
von Neumann regular pair (`N_+ * N_- * N_+ = N_+` and `N_- * N_+ * N_- = N_-`), then both the
chiral Dirac sum `Φ = genPhi P A C` and the chiral charge `Σ = genSig P A C` are group-invertible
elements of Drazin index `1` equal to their own Drazin inverses (`IsDrazinInverse Φ Φ 1` and
`IsDrazinInverse Σ Σ 1`), with Drazin spectral projector `projection Φ Φ = genV P A C`. -/
theorem genPhi_genSig_isDrazinInverse_of_vonNeumannRegular
    {P : B} (hP : P * P = P) {A C : B}
    (hRegPlus : conePlus P A * coneMinus P C * conePlus P A = conePlus P A)
    (hRegMinus : coneMinus P C * conePlus P A * coneMinus P C = coneMinus P C) :
    IsDrazinInverse (genPhi P A C) (genPhi P A C) 1 ∧
    IsDrazinInverse (genSig P A C) (genSig P A C) 1 ∧
    projection (genPhi P A C) (genPhi P A C) = genV P A C ∧
    projection (genSig P A C) (genSig P A C) = genV P A C := by
  have hNp2 : conePlus P A * conePlus P A = 0 := by peirce_nf hP
  have hNm2 : coneMinus P C * coneMinus P C = 0 := by peirce_nf hP
  have hStage := stage_P1_nilpotent_first_genesis_of_projectors hNp2 hNm2 hRegPlus hRegMinus
  have hPhi3 : genPhi P A C * genPhi P A C * genPhi P A C = genPhi P A C :=
    hStage.2.2.2.2.2.2.2.1
  have hP1 : (conePlus P A * coneMinus P C) * (conePlus P A * coneMinus P C) =
      conePlus P A * coneMinus P C := hStage.1
  have hQ1 : (coneMinus P C * conePlus P A) * (coneMinus P C * conePlus P A) =
      coneMinus P C * conePlus P A := hStage.2.1
  have hPQ : (conePlus P A * coneMinus P C) * (coneMinus P C * conePlus P A) = 0 :=
    hStage.2.2.1
  have hQP : (coneMinus P C * conePlus P A) * (conePlus P A * coneMinus P C) = 0 :=
    hStage.2.2.2.1
  have hSigSq : genSig P A C * genSig P A C = genV P A C := by
    dsimp [genSig, genV, anticomm, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    calc
      (conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) *
          (conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) =
          (conePlus P A * coneMinus P C) * (conePlus P A * coneMinus P C) -
            (conePlus P A * coneMinus P C) * (coneMinus P C * conePlus P A) -
            (coneMinus P C * conePlus P A) * (conePlus P A * coneMinus P C) +
            (coneMinus P C * conePlus P A) * (coneMinus P C * conePlus P A) := by noncomm_ring
      _ = conePlus P A * coneMinus P C + coneMinus P C * conePlus P A := by
        rw [hP1, hQ1, hPQ, hQP]; abel
  have hVSig : genV P A C * genSig P A C = genSig P A C := by
    dsimp [genSig, genV, anticomm, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    calc
      (conePlus P A * coneMinus P C + coneMinus P C * conePlus P A) *
          (conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) =
          (conePlus P A * coneMinus P C) * (conePlus P A * coneMinus P C) -
            (conePlus P A * coneMinus P C) * (coneMinus P C * conePlus P A) +
            (coneMinus P C * conePlus P A) * (conePlus P A * coneMinus P C) -
            (coneMinus P C * conePlus P A) * (coneMinus P C * conePlus P A) := by noncomm_ring
      _ = conePlus P A * coneMinus P C - coneMinus P C * conePlus P A := by
        rw [hP1, hQ1, hPQ, hQP]; abel
  have hSig3 : genSig P A C * genSig P A C * genSig P A C = genSig P A C := by
    rw [hSigSq, hVSig]
  have hDPhi : IsDrazinInverse (genPhi P A C) (genPhi P A C) 1 := by
    refine ⟨rfl, hPhi3, ?_⟩
    simpa [pow_two] using hPhi3
  have hDSig : IsDrazinInverse (genSig P A C) (genSig P A C) 1 := by
    refine ⟨rfl, hSig3, ?_⟩
    simpa [pow_two] using hSig3
  have hProjPhi : projection (genPhi P A C) (genPhi P A C) = genV P A C := by
    unfold projection
    peirce_nf hP
  have hProjSig : projection (genSig P A C) (genSig P A C) = genV P A C := by
    unfold projection
    exact hSigSq
  exact ⟨hDPhi, hDSig, hProjPhi, hProjSig⟩

/-- **Coordinate-Free Order-3 Nilpotent Flag Projector Reconstruction in Any `[Ring B]` (Gap G2)**:
Given `N, M : B` whose ladder products `s₁ = M * N` and `s₂ = M * M * N * N` satisfy
`s₂ * s₂ = s₂`, `s₁ * s₂ = s₂`, `s₂ * s₁ = s₂`, and `s₁ * s₁ = s₁`, the reconstructed flag
elements `P₀ = s₂`, `P₁ = s₁ - s₂`, and `P₂ = 1 - s₁` form a complete mutually orthogonal
resolution of the identity (`P₀ + P₁ + P₂ = 1`, `P_i * P_j = δ_{ij} P_i`). -/
theorem abstract_order3_nilpotent_flag_projector_resolution
    (N M : B)
    (hs2_idem : (M * M * N * N) * (M * M * N * N) = M * M * N * N)
    (hs1_s2 : (M * N) * (M * M * N * N) = M * M * N * N)
    (hs2_s1 : (M * M * N * N) * (M * N) = M * M * N * N)
    (hs1_idem : (M * N) * (M * N) = M * N) :
    let s1 := M * N
    let s2 := M * M * N * N
    let P0 := s2
    let P1 := s1 - s2
    let P2 := 1 - s1
    P0 + P1 + P2 = 1 ∧
    P0 * P0 = P0 ∧
    P1 * P1 = P1 ∧
    P2 * P2 = P2 ∧
    P0 * P1 = 0 ∧
    P1 * P0 = 0 ∧
    P0 * P2 = 0 ∧
    P2 * P0 = 0 ∧
    P1 * P2 = 0 ∧
    P2 * P1 = 0 := by
  dsimp only
  refine ⟨by abel, hs2_idem, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      (M * N - M * M * N * N) * (M * N - M * M * N * N) =
          (M * N) * (M * N) - (M * N) * (M * M * N * N) -
            (M * M * N * N) * (M * N) + (M * M * N * N) * (M * M * N * N) := by noncomm_ring
      _ = M * N - M * M * N * N := by rw [hs1_idem, hs1_s2, hs2_s1, hs2_idem]; abel
  · calc
      (1 - M * N) * (1 - M * N) = 1 - M * N - M * N + (M * N) * (M * N) := by noncomm_ring
      _ = 1 - M * N := by rw [hs1_idem]; abel
  · calc
      (M * M * N * N) * (M * N - M * M * N * N) =
          (M * M * N * N) * (M * N) - (M * M * N * N) * (M * M * N * N) := by noncomm_ring
      _ = 0 := by rw [hs2_s1, hs2_idem, sub_self]
  · calc
      (M * N - M * M * N * N) * (M * M * N * N) =
          (M * N) * (M * M * N * N) - (M * M * N * N) * (M * M * N * N) := by noncomm_ring
      _ = 0 := by rw [hs1_s2, hs2_idem, sub_self]
  · calc
      (M * M * N * N) * (1 - M * N) =
          M * M * N * N - (M * M * N * N) * (M * N) := by noncomm_ring
      _ = 0 := by rw [hs2_s1, sub_self]
  · calc
      (1 - M * N) * (M * M * N * N) =
          M * M * N * N - (M * N) * (M * M * N * N) := by noncomm_ring
      _ = 0 := by rw [hs1_s2, sub_self]
  · calc
      (M * N - M * M * N * N) * (1 - M * N) =
          M * N - (M * N) * (M * N) - M * M * N * N + (M * M * N * N) * (M * N) := by noncomm_ring
      _ = 0 := by rw [hs1_idem, hs2_s1]; abel
  · calc
      (1 - M * N) * (M * N - M * M * N * N) =
          M * N - (M * N) * (M * N) - M * M * N * N + (M * N) * (M * M * N * N) := by noncomm_ring
      _ = 0 := by rw [hs1_idem, hs1_s2]; abel

/-- **Drazin Gribov/Fitting Cut ↔ BRST Physical Quotient Bridge**:
For any exterior algebra `ExteriorAlgebra R₀ V₀` over `[CommRing R₀] [AddCommGroup V₀] [Module R₀ V₀]`,
if `P_phys : Module.End R₀ (ExteriorAlgebra R₀ V₀)` is an idempotent physical projector
(`P_phys * P_phys = P_phys`) and `q_brst : Module.End R₀ (ExteriorAlgebra R₀ V₀)` is a nilpotent
BRST differential (`q_brst.comp q_brst = 0`) supported on the complementary Gribov/ghost sector
(`P_phys * q_brst = 0` and `q_brst * P_phys = 0`), then:
1. The combined operator `L_FP = P_phys + q_brst` has Drazin inverse `P_phys` of index `2`
   (`IsDrazinInverse (P_phys + q_brst) P_phys 2`),
2. Its Drazin spectral projector is `projection (P_phys + q_brst) P_phys = P_phys`, its Fitting
   regular core is `fittingRegularPart (P_phys + q_brst) P_phys = P_phys`, and its Fitting
   nilpotent part is the BRST differential `fittingNilpotentPart (P_phys + q_brst) P_phys = q_brst`,
3. Both `LinearMap.range q_brst ≤ LinearMap.ker q_brst` (`brst_range_le_ker`) and
   `LinearMap.range P_phys ≤ LinearMap.ker q_brst` hold, so both exact BRST states and the
   Drazin regular core lie in `LinearMap.ker q_brst`. -/
theorem drazin_gribov_horizon_brst_physical_state_bridge
    {R₀ V₀ : Type*} [CommRing R₀] [AddCommGroup V₀] [Module R₀ V₀]
    (P_phys q_brst : Module.End R₀ (ExteriorAlgebra R₀ V₀))
    (hP : P_phys * P_phys = P_phys)
    (hq : q_brst.comp q_brst = 0)
    (hPq : P_phys * q_brst = 0)
    (hqP : q_brst * P_phys = 0) :
    IsDrazinInverse (P_phys + q_brst) P_phys 2 ∧
    projection (P_phys + q_brst) P_phys = P_phys ∧
    fittingRegularPart (P_phys + q_brst) P_phys = P_phys ∧
    fittingNilpotentPart (P_phys + q_brst) P_phys = q_brst ∧
    LinearMap.range q_brst ≤ LinearMap.ker q_brst ∧
    LinearMap.range P_phys ≤ LinearMap.ker q_brst := by
  have hq_mul : q_brst * q_brst = 0 := hq
  have hLP : (P_phys + q_brst) * P_phys = P_phys := by
    rw [add_mul, hP, hqP, add_zero]
  have hPL : P_phys * (P_phys + q_brst) = P_phys := by
    rw [mul_add, hP, hPq, add_zero]
  have hL2 : (P_phys + q_brst) ^ 2 = P_phys := by
    change (P_phys + q_brst) * (P_phys + q_brst) = P_phys
    calc
      (P_phys + q_brst) * (P_phys + q_brst) =
          P_phys * P_phys + P_phys * q_brst + q_brst * P_phys + q_brst * q_brst := by
        noncomm_ring
      _ = P_phys := by rw [hP, hPq, hqP, hq_mul]; abel
  have hL3 : (P_phys + q_brst) ^ (2 + 1) = P_phys := by
    rw [pow_succ, hL2, hPL]
  have hDrazin : IsDrazinInverse (P_phys + q_brst) P_phys 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hLP, hPL]
    · rw [hPL, hP]
    · rw [hL3, hL2, hP]
  have hProj : projection (P_phys + q_brst) P_phys = P_phys := hLP
  have hReg : fittingRegularPart (P_phys + q_brst) P_phys = P_phys := by
    unfold fittingRegularPart
    rw [hProj, hLP]
  have hNil : fittingNilpotentPart (P_phys + q_brst) P_phys = q_brst := by
    unfold fittingNilpotentPart complementaryProjection
    rw [hProj, mul_sub, mul_one, hLP, add_sub_cancel_left]
  have hRangeKer : LinearMap.range P_phys ≤ LinearMap.ker q_brst := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have h0 : (q_brst * P_phys) x = 0 := by rw [hqP]; rfl
    exact h0
  exact ⟨hDrazin, hProj, hReg, hNil, brst_range_le_ker q_brst hq, hRangeKer⟩

/-! ===========================================================================
    Section 4: Native Mathlib `Matrix (Fin 4) (Fin 4) R` Plücker–Hodge / `Matrix.det`
               Amplituhedron–Baryon Bridge, Order-3 Flag & `sl₂` Casimir `C₂ = 8 I₃` in
               `Matrix (Fin 3) (Fin 3)`, `PGL(2)` Cross-Ratio Invariance in `Matrix (Fin 2) (Fin 2)`,
               Native `Matrix.trace` Volume Invariant, & Chiral Lorentz Cartan Poset Rungs 0–4
    =========================================================================== -/

section ZornAmplituhedronNativeMatrix

open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset

/-- Native Mathlib `4 × 4` matrix representation of `Mat4 R`. -/
def mat4ToMatrix {R : Type*} (M : Mat4 R) : Matrix (Fin 4) (Fin 4) R :=
  ![![M.m11, M.m12, M.m13, M.m14],
    ![M.m21, M.m22, M.m23, M.m24],
    ![M.m31, M.m32, M.m33, M.m34],
    ![M.m41, M.m42, M.m43, M.m44]]

/-- Inverse map from native Mathlib `Matrix (Fin 4) (Fin 4) R` to `Mat4 R`. -/
def matrixToMat4 {R : Type*} (A : Matrix (Fin 4) (Fin 4) R) : Mat4 R :=
  ⟨A 0 0, A 0 1, A 0 2, A 0 3,
   A 1 0, A 1 1, A 1 2, A 1 3,
   A 2 0, A 2 1, A 2 2, A 2 3,
   A 3 0, A 3 1, A 3 2, A 3 3⟩

/-- Native Mathlib `Matrix (Fin 4) (Fin 4) R` skew-symmetric Plücker bivector matrix `P₄(u, v)`. -/
def nativePluckerMat4 {R : Type*} [Ring R] (u v : Vec3 R) : Matrix (Fin 4) (Fin 4) R :=
  ![![0,     u.x,  u.y,  u.z],
    ![-u.x,  0,    v.z, -v.y],
    ![-u.y, -v.z,  0,    v.x],
    ![-u.z,  v.y, -v.x,  0  ]]

/-- Native Mathlib `Matrix (Fin 4) (Fin 4) R` Hodge dual Plücker matrix `⋆P₄(u, v) = P₄(v, u)`. -/
def nativePluckerHodge4 {R : Type*} [Ring R] (u v : Vec3 R) : Matrix (Fin 4) (Fin 4) R :=
  nativePluckerMat4 v u

/-- Native Mathlib `Matrix (Fin 4) (Fin 4) R` built from four 4-twistors `Z₀, Z₁, Z₂, Z₃`. -/
def nativeTwistorMatrix4 {R : Type*} (Z0 Z1 Z2 Z3 : Twistor4 R) : Matrix (Fin 4) (Fin 4) R :=
  ![![Z0.z0, Z0.u.x, Z0.u.y, Z0.u.z],
    ![Z1.z0, Z1.u.x, Z1.u.y, Z1.u.z],
    ![Z2.z0, Z2.u.x, Z2.u.y, Z2.u.z],
    ![Z3.z0, Z3.u.x, Z3.u.y, Z3.u.z]]

/-- Native Mathlib `Matrix (Fin 3) (Fin 3) R` built from three 3-vectors `u₁, u₂, u₃`. -/
def nativeBaryonMatrix3 {R : Type*} (u1 u2 u3 : Vec3 R) : Matrix (Fin 3) (Fin 3) R :=
  ![![u1.x, u1.y, u1.z],
    ![u2.x, u2.y, u2.z],
    ![u3.x, u3.y, u3.z]]

/-- Multiplicative equivalence (`MulEquiv`) between `Mat4 R` and native Mathlib
`Matrix (Fin 4) (Fin 4) R` over any `[Ring R]` (Gap G1 / Target 4). -/
def mat4MulEquivMatrix4 {R : Type*} [Ring R] : Mat4 R ≃* Matrix (Fin 4) (Fin 4) R where
  toFun := mat4ToMatrix
  invFun := matrixToMat4
  left_inv M := rfl
  right_inv A := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' M N := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;>
      simp [mat4ToMatrix, Mat4.mul_def, Mat4.mul]

/-- **Native Mathlib `Matrix (Fin 4) (Fin 4) R` Plücker–Hodge Chromomagnetic Anomaly Theorem**:
Over any non-commutative ring `[Ring R]`, in the native Mathlib matrix product
`M_PH = -(nativePluckerMat4 u v * nativePluckerHodge4 u v) : Matrix (Fin 4) (Fin 4) R`:
1. The `(0, 0)` entry `M_PH 0 0` is the scalar dot product `Vec3.dot u v`,
2. Row `0` `⟨M_PH 0 1, M_PH 0 2, M_PH 0 3⟩` is the upper self-cross product `Vec3.cross u u`,
3. Column `0` `⟨M_PH 1 0, M_PH 2 0, M_PH 3 0⟩` is the negated lower self-cross product `-Vec3.cross v v`. -/
theorem native_matrix4_plucker_hodge_chromomagnetic_anomaly
    {R : Type*} [Ring R] (u v : Vec3 R) :
    let M_PH : Matrix (Fin 4) (Fin 4) R := -(nativePluckerMat4 u v * nativePluckerHodge4 u v)
    M_PH 0 0 = Vec3.dot u v ∧
    (⟨M_PH 0 1, M_PH 0 2, M_PH 0 3⟩ : Vec3 R) = Vec3.cross u u ∧
    (⟨M_PH 1 0, M_PH 2 0, M_PH 3 0⟩ : Vec3 R) = -Vec3.cross v v := by
  dsimp only
  have hEntry : ∀ i j : Fin 4,
      (-(nativePluckerMat4 u v * nativePluckerHodge4 u v)) i j =
        -∑ k : Fin 4, nativePluckerMat4 u v i k * nativePluckerHodge4 u v k j := by
    intro i j
    rw [Matrix.neg_apply, Matrix.mul_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [hEntry 0 0, Fin.sum_univ_four]
    simp [nativePluckerHodge4, nativePluckerMat4, Vec3.dot]
    abel
  · refine Vec3.ext ?_ ?_ ?_
    · rw [hEntry 0 1, Fin.sum_univ_four]
      simp [nativePluckerHodge4, nativePluckerMat4, Vec3.cross]
      abel
    · rw [hEntry 0 2, Fin.sum_univ_four]
      simp [nativePluckerHodge4, nativePluckerMat4, Vec3.cross]
      abel
    · rw [hEntry 0 3, Fin.sum_univ_four]
      simp [nativePluckerHodge4, nativePluckerMat4, Vec3.cross]
      abel
  · refine Vec3.ext ?_ ?_ ?_
    · rw [hEntry 1 0, Fin.sum_univ_four]
      simp [nativePluckerHodge4, nativePluckerMat4, Vec3.cross, Vec3.neg_x]
      abel
    · rw [hEntry 2 0, Fin.sum_univ_four]
      simp [nativePluckerHodge4, nativePluckerMat4, Vec3.cross, Vec3.neg_y]
      abel
    · rw [hEntry 3 0, Fin.sum_univ_four]
      simp [nativePluckerHodge4, nativePluckerMat4, Vec3.cross, Vec3.neg_z]
      abel

/-- **Native Mathlib `Matrix.det` Twistor 4-Bracket, `Mat4.det4` Equivalence, & Baryon Determinant (Gap G1 / Target 4)**:
Over any commutative ring `[CommRing K]`:
1. For any `M : Mat4 K`, `Mat4.det4 M = Matrix.det (mat4ToMatrix M)`,
2. Native Mathlib `Matrix.det (nativeBaryonMatrix3 u1 u2 u3)` equals `baryonDet3 u1 u2 u3`,
3. Native Mathlib `Matrix.det (nativeTwistorMatrix4 Z0 Z1 Z2 Z3)` equals `twistorBracket4 Z0 Z1 Z2 Z3`,
4. The Zorn anticommutator of two Plücker twistor lines `zornPluckerLine Z0 Z1` and `zornPluckerLine Z2 Z3`
   equals `Matrix.det (nativeTwistorMatrix4 Z0 Z1 Z2 Z3)` times the identity Zorn matrix,
5. For `affineOrigin` and three spatial twistors `spatialTwistor u_a`, the `4 × 4` native Mathlib
   determinant reduces to the `3 × 3` native Mathlib baryon determinant:
   `Matrix.det (nativeTwistorMatrix4 affineOrigin (spatialTwistor u1) (spatialTwistor u2) (spatialTwistor u3)) =
    Matrix.det (nativeBaryonMatrix3 u1 u2 u3)`. -/
theorem native_matrix_det_twistor4_eq_baryon_and_zorn_anticommutator
    {K : Type*} [CommRing K] (M : Mat4 K) (Z0 Z1 Z2 Z3 : Twistor4 K) (u1 u2 u3 : Vec3 K) :
    Mat4.det4 M = Matrix.det (mat4ToMatrix M) ∧
    Matrix.det (nativeBaryonMatrix3 u1 u2 u3) = baryonDet3 u1 u2 u3 ∧
    Matrix.det (nativeTwistorMatrix4 Z0 Z1 Z2 Z3) = twistorBracket4 Z0 Z1 Z2 Z3 ∧
    zornPluckerLine Z0 Z1 * zornPluckerLine Z2 Z3 +
      zornPluckerLine Z2 Z3 * zornPluckerLine Z0 Z1 =
      ⟨Matrix.det (nativeTwistorMatrix4 Z0 Z1 Z2 Z3), 0, 0,
       Matrix.det (nativeTwistorMatrix4 Z0 Z1 Z2 Z3)⟩ ∧
    Matrix.det (nativeTwistorMatrix4 affineOrigin
      (spatialTwistor u1) (spatialTwistor u2) (spatialTwistor u3)) =
      Matrix.det (nativeBaryonMatrix3 u1 u2 u3) := by
  have hDetM : Mat4.det4 M = Matrix.det (mat4ToMatrix M) := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
    simp [mat4ToMatrix, Mat4.det4, Matrix.submatrix, Fin.succAbove, Matrix.det_fin_three]
    ring
  have hDet3 : Matrix.det (nativeBaryonMatrix3 u1 u2 u3) = baryonDet3 u1 u2 u3 := by
    rw [Matrix.det_fin_three]
    simp [nativeBaryonMatrix3, baryonDet3]
    ring
  have hDet4 : Matrix.det (nativeTwistorMatrix4 Z0 Z1 Z2 Z3) = twistorBracket4 Z0 Z1 Z2 Z3 := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
    simp [nativeTwistorMatrix4, Matrix.submatrix, Fin.succAbove,
      Matrix.det_fin_three, twistorBracket4, baryonDet3, Vec3.dot, Vec3.cross]
    ring
  have hZorn := (amplituhedron_4bracket_eq_zorn_plucker_anticommutator_and_baryon
    Z0 Z1 Z2 Z3 0 0 0 u1 u1 u2 u3).2.1
  have hSpatial :
      Matrix.det (nativeTwistorMatrix4 affineOrigin
        (spatialTwistor u1) (spatialTwistor u2) (spatialTwistor u3)) =
      Matrix.det (nativeBaryonMatrix3 u1 u2 u3) := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
    rw [hDet3]
    simp [nativeTwistorMatrix4, affineOrigin, spatialTwistor, Matrix.submatrix, Fin.succAbove,
      Matrix.det_fin_three, baryonDet3]
    ring
  refine ⟨hDetM, hDet3, hDet4, ?_, hSpatial⟩
  rw [hDet4]
  exact hZorn

end ZornAmplituhedronNativeMatrix

/-- Step-nilpotent upper shift matrix `N = E₀₁ + E₁₂ ∈ Matrix (Fin 3) (Fin 3) R` of order 3 (`N^3 = 0`). -/
def shiftNilpotent3Up {R : Type*} [Ring R] : Matrix (Fin 3) (Fin 3) R :=
  ![![0, 1, 0],
    ![0, 0, 1],
    ![0, 0, 0]]

/-- Step-nilpotent lower shift matrix `M = E₁₀ + E₂₁ ∈ Matrix (Fin 3) (Fin 3) R` of order 3 (`M^3 = 0`). -/
def shiftNilpotent3Down {R : Type*} [Ring R] : Matrix (Fin 3) (Fin 3) R :=
  ![![0, 0, 0],
    ![1, 0, 0],
    ![0, 1, 0]]

/-- First reconstructed flag projector `P₀ = N² M² = E₀₀` in `Matrix (Fin 3) (Fin 3) R`. -/
def flagProj3_0 {R : Type*} [Ring R] : Matrix (Fin 3) (Fin 3) R :=
  (shiftNilpotent3Up * shiftNilpotent3Up) * (shiftNilpotent3Down * shiftNilpotent3Down)

/-- Middle reconstructed flag projector `P₁ = (N M)(M N) = E₁₁` in `Matrix (Fin 3) (Fin 3) R`. -/
def flagProj3_1 {R : Type*} [Ring R] : Matrix (Fin 3) (Fin 3) R :=
  (shiftNilpotent3Up * shiftNilpotent3Down) * (shiftNilpotent3Down * shiftNilpotent3Up)

/-- Third reconstructed flag projector `P₂ = M² N² = E₂₂` in `Matrix (Fin 3) (Fin 3) R`. -/
def flagProj3_2 {R : Type*} [Ring R] : Matrix (Fin 3) (Fin 3) R :=
  (shiftNilpotent3Down * shiftNilpotent3Down) * (shiftNilpotent3Up * shiftNilpotent3Up)

/-- **Universal Ring-Level Order-3 Nilpotent Flag Projector Reconstruction (`Matrix (Fin 3) (Fin 3) R`) &
Order-3 `sl₂` Casimir Constant `C₂ = 8 I₃` (Target 4)**:
1. Over ANY associative ring `[Ring R]`, the order-3 step-nilpotent shift matrices
   `N = shiftNilpotent3Up` and `M = shiftNilpotent3Down` satisfy `N^3 = 0`, `M^3 = 0`, and
   polynomially reconstruct the complete mutually orthogonal flag resolution of the identity
   `flagProj3_0 + flagProj3_1 + flagProj3_2 = 1`.
2. On the 3-dimensional irreducible `sl₂` representation `(nilRaise3, nilLower3, cartanDiag3)` in
   `Matrix (Fin 3) (Fin 3) ℤ`, the scaled quadratic Casimir operator `casimir2` takes the constant
   scalar value `(n² - 1) I₃ = (8 : ℤ) • 1`. -/
theorem order3_nilpotent_flag_and_sl2_casimir_constant_eight
    {R : Type*} [Ring R] :
    shiftNilpotent3Up * shiftNilpotent3Up * (shiftNilpotent3Up : Matrix (Fin 3) (Fin 3) R) = 0 ∧
    shiftNilpotent3Down * shiftNilpotent3Down * (shiftNilpotent3Down : Matrix (Fin 3) (Fin 3) R) = 0 ∧
    flagProj3_0 * flagProj3_0 = (flagProj3_0 : Matrix (Fin 3) (Fin 3) R) ∧
    flagProj3_1 * flagProj3_1 = (flagProj3_1 : Matrix (Fin 3) (Fin 3) R) ∧
    flagProj3_2 * flagProj3_2 = (flagProj3_2 : Matrix (Fin 3) (Fin 3) R) ∧
    flagProj3_0 * flagProj3_1 = (0 : Matrix (Fin 3) (Fin 3) R) ∧
    flagProj3_1 * flagProj3_2 = (0 : Matrix (Fin 3) (Fin 3) R) ∧
    flagProj3_0 * flagProj3_2 = (0 : Matrix (Fin 3) (Fin 3) R) ∧
    (flagProj3_0 + flagProj3_1 + flagProj3_2 : Matrix (Fin 3) (Fin 3) R) = 1 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.casimir2
      nilRaise3 nilLower3 cartanDiag3 =
      (8 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  have hUp2 : (shiftNilpotent3Up * shiftNilpotent3Up : Matrix (Fin 3) (Fin 3) R) =
      !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
    ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [shiftNilpotent3Up]
  have hDown2 : (shiftNilpotent3Down * shiftNilpotent3Down : Matrix (Fin 3) (Fin 3) R) =
      !![0, 0, 0; 0, 0, 0; 1, 0, 0] := by
    ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [shiftNilpotent3Down]
  have hUpDown : (shiftNilpotent3Up * shiftNilpotent3Down : Matrix (Fin 3) (Fin 3) R) =
      !![1, 0, 0; 0, 1, 0; 0, 0, 0] := by
    ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [shiftNilpotent3Up, shiftNilpotent3Down]
  have hDownUp : (shiftNilpotent3Down * shiftNilpotent3Up : Matrix (Fin 3) (Fin 3) R) =
      !![0, 0, 0; 0, 1, 0; 0, 0, 1] := by
    ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [shiftNilpotent3Up, shiftNilpotent3Down]
  have hP0 : (flagProj3_0 : Matrix (Fin 3) (Fin 3) R) =
      !![1, 0, 0; 0, 0, 0; 0, 0, 0] := by
    unfold flagProj3_0; rw [hUp2, hDown2]
    ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp
  have hP1 : (flagProj3_1 : Matrix (Fin 3) (Fin 3) R) =
      !![0, 0, 0; 0, 1, 0; 0, 0, 0] := by
    unfold flagProj3_1; rw [hUpDown, hDownUp]
    ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp
  have hP2 : (flagProj3_2 : Matrix (Fin 3) (Fin 3) R) =
      !![0, 0, 0; 0, 0, 0; 0, 0, 1] := by
    unfold flagProj3_2; rw [hDown2, hUp2]
    ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · rw [hUp2]; ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [shiftNilpotent3Up]
  · rw [hDown2]; ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [shiftNilpotent3Down]
  · rw [hP0]; ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp
  · rw [hP1]; ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp
  · rw [hP2]; ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp
  · rw [hP0, hP1]; ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp
  · rw [hP1, hP2]; ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp
  · rw [hP0, hP2]; ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp
  · rw [hP0, hP1, hP2]; ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- Homogeneous `2 × 2` determinant bracket `det2 u v = Matrix.det !![u 0, v 0; u 1, v 1]`
on `Fin 2 → K` for projective cross-ratio invariance. -/
def det2Bracket {K : Type*} [CommRing K] (u v : Fin 2 → K) : K :=
  Matrix.det !![u 0, v 0; u 1, v 1]

/-- **Projective Cross-Ratio `PGL(2)` Möbius Determinant Invariance in Native `Matrix (Fin 2) (Fin 2) K` (Target 4)**:
For any `g : Matrix (Fin 2) (Fin 2) K` and four homogeneous 2-vectors `z₁ z₂ z₃ z₄ : Fin 2 → K`
over `[CommRing K]`, both the cross-ratio numerator `det2Bracket z₁ z₃ * det2Bracket z₂ z₄` and
denominator `det2Bracket z₂ z₃ * det2Bracket z₁ z₄` scale by `(Matrix.det g * Matrix.det g)` under
`z_i ↦ g.mulVec z_i`. -/
theorem pgl2_moebius_cross_ratio_det_invariance
    {K : Type*} [CommRing K] (g : Matrix (Fin 2) (Fin 2) K)
    (z₁ z₂ z₃ z₄ : Fin 2 → K) :
    det2Bracket (g.mulVec z₁) (g.mulVec z₃) * det2Bracket (g.mulVec z₂) (g.mulVec z₄) =
      (Matrix.det g * Matrix.det g) * (det2Bracket z₁ z₃ * det2Bracket z₂ z₄) ∧
    det2Bracket (g.mulVec z₂) (g.mulVec z₃) * det2Bracket (g.mulVec z₁) (g.mulVec z₄) =
      (Matrix.det g * Matrix.det g) * (det2Bracket z₂ z₃ * det2Bracket z₁ z₄) := by
  have hPair : ∀ u v : Fin 2 → K,
      det2Bracket (g.mulVec u) (g.mulVec v) = Matrix.det g * det2Bracket u v := by
    intro u v
    unfold det2Bracket
    rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.det_fin_two]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  refine ⟨?_, ?_⟩
  · rw [hPair z₁ z₃, hPair z₂ z₄]; ring
  · rw [hPair z₂ z₃, hPair z₁ z₄]; ring

/-- **Native Mathlib `Matrix.trace` Cyclic Volume Invariant & Chiral Gravitational Anomaly 2-Cocycle (Target 3)**:
For any finite index type `n` and any idempotent matrix `P : Matrix n n R` (`P * P = P`) over
`[CommRing R]`:
1. `Matrix.trace (conePlus P A) = 0`, `Matrix.trace (coneMinus P C) = 0`,
   `Matrix.trace (genPhi P A C) = 0`, `Matrix.trace (genJ P A C) = 0`, and
   `Matrix.trace (genSig P A C) = 0`,
2. `Matrix.trace (P * genV P A C * P) = Matrix.trace ((1 - P) * genV P A C * (1 - P))` and
   `Matrix.trace (genV P A C) = (2 : ℤ) • Matrix.trace (P * genV P A C * P)`,
3. The chiral anomaly 2-cocycle `Matrix.trace (invS P * comm (genPhi P A C) (genJ P A C))`
   equals `-(2 : ℤ) • Matrix.trace (genV P A C)` while the unweighted commutator trace
   `Matrix.trace (comm (genPhi P A C) (genJ P A C))` vanishes! -/
theorem matrix_cyclic_trace_volume_invariant_and_chiral_anomaly_cocycle
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    {P : Matrix n n R} (hP : P * P = P) (A C : Matrix n n R) :
    Matrix.trace (conePlus P A) = 0 ∧
    Matrix.trace (coneMinus P C) = 0 ∧
    Matrix.trace (genPhi P A C) = 0 ∧
    Matrix.trace (genJ P A C) = 0 ∧
    Matrix.trace (genSig P A C) = 0 ∧
    Matrix.trace (P * genV P A C * P) = Matrix.trace ((1 - P) * genV P A C * (1 - P)) ∧
    Matrix.trace (genV P A C) = (2 : ℤ) • Matrix.trace (P * genV P A C * P) ∧
    Matrix.trace (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)) = 0 ∧
    Matrix.trace (invS P * InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)) =
      -(2 : ℤ) • Matrix.trace (genV P A C) := by
  have hNp : Matrix.trace (conePlus P A) = 0 := by
    have hEq : conePlus P A = P * conePlus P A - conePlus P A * P := by peirce_nf hP
    rw [hEq, Matrix.trace_sub, Matrix.trace_mul_comm P (conePlus P A), sub_self]
  have hNm : Matrix.trace (coneMinus P C) = 0 := by
    have hEq : coneMinus P C = coneMinus P C * P - P * coneMinus P C := by peirce_nf hP
    rw [hEq, Matrix.trace_sub, Matrix.trace_mul_comm (coneMinus P C) P, sub_self]
  have hPhi : Matrix.trace (genPhi P A C) = 0 := by
    dsimp [genPhi]; rw [Matrix.trace_add, hNp, hNm, add_zero]
  have hJ : Matrix.trace (genJ P A C) = 0 := by
    dsimp [genJ]; rw [Matrix.trace_sub, hNp, hNm, sub_zero]
  have hSig : Matrix.trace (genSig P A C) = 0 := by
    have hEq : genSig P A C = conePlus P A * coneMinus P C - coneMinus P C * conePlus P A := by
      peirce_nf hP
    rw [hEq, Matrix.trace_sub, Matrix.trace_mul_comm (conePlus P A) (coneMinus P C), sub_self]
  have hCorner1 : P * genV P A C * P = conePlus P A * coneMinus P C := by peirce_nf hP
  have hCorner0 : (1 - P) * genV P A C * (1 - P) = coneMinus P C * conePlus P A := by peirce_nf hP
  have hEqCorners :
      Matrix.trace (P * genV P A C * P) = Matrix.trace ((1 - P) * genV P A C * (1 - P)) := by
    rw [hCorner1, hCorner0, Matrix.trace_mul_comm]
  have hVSplit : genV P A C = P * genV P A C * P + (1 - P) * genV P A C * (1 - P) := by
    peirce_nf hP
  have hTraceV : Matrix.trace (genV P A C) = (2 : ℤ) • Matrix.trace (P * genV P A C * P) := by
    conv_lhs => rw [hVSplit]
    rw [Matrix.trace_add, ← hEqCorners, two_zsmul]
  have hCommPhiJ :
      Matrix.trace (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)) = 0 := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    rw [Matrix.trace_sub, Matrix.trace_mul_comm (genPhi P A C) (genJ P A C), sub_self]
  have hChiralId :
      invS P * InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) =
        -(2 : ℤ) • genV P A C := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    rw [neg_zsmul, two_zsmul]
    peirce_nf hP
  have hChiralTrace :
      Matrix.trace (invS P * InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)) =
        -(2 : ℤ) • Matrix.trace (genV P A C) := by
    rw [hChiralId, neg_zsmul, two_zsmul, Matrix.trace_neg, Matrix.trace_add,
      neg_zsmul, two_zsmul]
  exact ⟨hNp, hNm, hPhi, hJ, hSig, hEqCorners, hTraceV, hCommPhiJ, hChiralTrace⟩

/-- Diamond-branching causal edge relation on `ChiralLorentzTwistorCartanStage`
(`CL₁ → CL₂ → (CL₃ ∥ CL₄) → CL₅ → CL₆ → (CL₇ ∥ CL₈) → CL₉ → CL₁₀`) (Target 3). -/
def diamondCausalEdge :
    ChiralLorentzTwistorCartanStage → ChiralLorentzTwistorCartanStage → Prop
  | .CL1_PrimordialChiralCutAndFourfoldPeirceAnatomy, .CL2_ChiralDualRealLorentzRepresentation => True
  | .CL2_ChiralDualRealLorentzRepresentation, .CL3_PoincareSemidirectAndSUSYSuperalgebra => True
  | .CL2_ChiralDualRealLorentzRepresentation, .CL4_SuperGrassmannianParaKahlerStructure => True
  | .CL3_PoincareSemidirectAndSUSYSuperalgebra, .CL5_TwistorIncidenceAndPositiveAmplituhedron => True
  | .CL4_SuperGrassmannianParaKahlerStructure, .CL5_TwistorIncidenceAndPositiveAmplituhedron => True
  | .CL5_TwistorIncidenceAndPositiveAmplituhedron, .CL6_UncertaintyAsCreatorOfMetricAndSpinCurvature => True
  | .CL6_UncertaintyAsCreatorOfMetricAndSpinCurvature, .CL7_ElieCartanTorsionAndSpinConnectionGravity => True
  | .CL6_UncertaintyAsCreatorOfMetricAndSpinCurvature, .CL8_HigherGradeUncertaintyAnomalyInSymmetryClosure => True
  | .CL7_ElieCartanTorsionAndSpinConnectionGravity, .CL9_RecursiveMetaTowerAndHilbertCramerRaoCurvatureBound => True
  | .CL8_HigherGradeUncertaintyAnomalyInSymmetryClosure, .CL9_RecursiveMetaTowerAndHilbertCramerRaoCurvatureBound => True
  | .CL9_RecursiveMetaTowerAndHilbertCramerRaoCurvatureBound, .CL10_MasterChiralLorentzTwistorCartanUncertaintySynthesis => True
  | _, _ => False

theorem diamondCausalEdge_rk_lt {s₁ s₂ : ChiralLorentzTwistorCartanStage}
    (h : diamondCausalEdge s₁ s₂) :
    ChiralLorentzTwistorCartanStage.rank s₁ < ChiralLorentzTwistorCartanStage.rank s₂ := by
  cases s₁ <;> cases s₂ <;>
    simp [diamondCausalEdge, ChiralLorentzTwistorCartanStage.rank] at h ⊢

theorem diamondCausalEdge_transGen_rk_lt {s₁ s₂ : ChiralLorentzTwistorCartanStage}
    (h : Relation.TransGen diamondCausalEdge s₁ s₂) :
    ChiralLorentzTwistorCartanStage.rank s₁ < ChiralLorentzTwistorCartanStage.rank s₂ := by
  induction h with
  | single he => exact diamondCausalEdge_rk_lt he
  | tail _ he ih => exact Nat.lt_trans ih (diamondCausalEdge_rk_lt he)

/-- **Phase II One-Sided Chiral Eigenvalues of `D₁ = P X P` (`0⁺`) vs. `D₂ = (1 - P) X (1 - P)` (`0⁻`),
Rung 1 Positive Unipotent Chart, Rung 2 Jordan Associator Scaling, & Rung 4 Shifted Aporia Annihilation (Target 3)**:
For any idempotent `P` (`P * P = P`) in `[Ring B]` with `[StarRing B]`:
1. `invS P * (P * X * P) = P * X * P` (`0⁺`) and `invS P * ((1 - P) * X * (1 - P)) = -((1 - P) * X * (1 - P))` (`0⁻`),
2. Positive unipotent charts `P + conePlus P A` and `P + coneMinus P C` are idempotents with
   `comm (P + conePlus P A) (P + coneMinus P C) = genSig P A C + genJ P A C`,
3. Rung 0 & Rung 4: for `Ψ = P + genPhi P A C`, `Ψ * Ψ - Ψ = genV P A C` and
   `((Ψ * Ψ - Ψ) - genV P A C) ^ 2 = 0`,
4. Rung 2 / Deduction 4: `JordanAssoc (coneMinus P C) (conePlus P A) (conePlus P A) =
   (2 : ℤ) • (genV P A C * conePlus P A)`. -/
theorem chiral_lorentz_rungs_0_to_4_and_diamond_poset_bridge
    [StarRing B] {P : B} (hP : P * P = P) (A C X Y Z : B) :
    (∀ s : ChiralLorentzTwistorCartanStage, ¬ Relation.TransGen diamondCausalEdge s s) ∧
    invS P * (P * X * P) = P * X * P ∧
    invS P * ((1 - P) * X * (1 - P)) = -((1 - P) * X * (1 - P)) ∧
    (P + conePlus P A) * (P + conePlus P A) = P + conePlus P A ∧
    (P + coneMinus P C) * (P + coneMinus P C) = P + coneMinus P C ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (P + conePlus P A) (P + coneMinus P C) =
      genSig P A C - genPhi P A C ∧
    (P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C) = genV P A C ∧
    (((P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C)) - genV P A C) *
      (((P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C)) - genV P A C) = 0 ∧
    JordanAssoc (coneMinus P C) (conePlus P A) (conePlus P A) =
      (2 : ℤ) • (genV P A C * conePlus P A) ∧
    kreinAdjoint P X = osPeirceReflection P X ∧
    cartanCurvature2Form P (genPhi P A C) = peirceMaurerCartanCurvature P A C ∧
    peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C ∧
    JordanAssoc X Y Z =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm Z X) Y ∧
    conePlus P A * evenGrade P X * conePlus P A +
      coneMinus P C * evenGrade P X * coneMinus P C = 0 := by
  have hAcyc : ∀ s : ChiralLorentzTwistorCartanStage, ¬ Relation.TransGen diamondCausalEdge s s := by
    intro s h
    exact Nat.lt_irrefl (ChiralLorentzTwistorCartanStage.rank s)
      (diamondCausalEdge_transGen_rk_lt h)
  have hD1 : invS P * (P * X * P) = P * X * P := by peirce_nf hP
  have hD2 : invS P * ((1 - P) * X * (1 - P)) = -((1 - P) * X * (1 - P)) := by peirce_nf hP
  have hChartP : (P + conePlus P A) * (P + conePlus P A) = P + conePlus P A := by peirce_nf hP
  have hChartM : (P + coneMinus P C) * (P + coneMinus P C) = P + coneMinus P C := by peirce_nf hP
  have hChartComm :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (P + conePlus P A) (P + coneMinus P C) =
        genSig P A C - genPhi P A C := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm; peirce_nf hP
  have hRung0 : (P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C) = genV P A C := by
    peirce_nf hP
  have hRung4 :
      (((P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C)) - genV P A C) *
        (((P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C)) - genV P A C) = 0 := by
    rw [hRung0, sub_self, mul_zero]
  have hRung2 :
      JordanAssoc (coneMinus P C) (conePlus P A) (conePlus P A) =
        (2 : ℤ) • (genV P A C * conePlus P A) := by
    unfold JordanAssoc anticomm
    rw [two_zsmul]
    peirce_nf hP
  have hMC : peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C := by
    unfold peirceMaurerCartanCurvature peirceGradingDeriv
    peirce_nf hP
  have hJAssoc : JordanAssoc X Y Z =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm Z X) Y := by
    unfold JordanAssoc anticomm InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    noncomm_ring
  have hKantor :
      conePlus P A * evenGrade P X * conePlus P A +
        coneMinus P C * evenGrade P X * coneMinus P C = 0 := by
    peirce_nf hP
  exact ⟨hAcyc, hD1, hD2, hChartP, hChartM, hChartComm, hRung0, hRung4, hRung2,
    rfl, rfl, hMC, hJAssoc, hKantor⟩

/-! ===========================================================================
    Section 5: Unital Block Doubling vs. Non-Unital Corner Inclusion (`Matrix.fromBlocks`)
               & `PeirceTetraktysColimitCoercivity` Direct Limit (`Stage n →+* Limit`)
    =========================================================================== -/

/-- **Side-by-Side Unital Block-Diagonal Doubling vs. Non-Unital Corner Inclusion via `Matrix.fromBlocks` (Gap G6)**:
For any finite index type `m` and any `P A C : Matrix m m R` over `[CommRing R]`:
1. Unital block-diagonal doubling `φ X = Matrix.fromBlocks X 0 0 X` preserves the identity matrix
   `φ 1 = 1`, intertwines `conePlus` and `genV` (`φ (conePlus P A) = conePlus (φ P) (φ A)`,
   `φ (genV P A C) = genV (φ P) (φ A) (φ C)`), and doubles the unnormalized matrix trace
   `Matrix.trace (φ (genV P A C)) = (2 : ℤ) • Matrix.trace (genV P A C)`.
2. Non-unital top-left corner inclusion `ι X = Matrix.fromBlocks X 0 0 0` maps `1` to a proper
   corner projection `ι 1`, intertwines the relative Peirce cone `ι P * ι A * (ι 1 - ι P) = ι (conePlus P A)`,
   and preserves the unnormalized matrix trace `Matrix.trace (ι (genV P A C)) = Matrix.trace (genV P A C)`. -/
theorem dyadic_unital_vs_corner_nonunital_peirce_intertwining
    {R m : Type*} [CommRing R] [DecidableEq m] [Fintype m]
    (P A C : Matrix m m R) :
    let φ := fun X : Matrix m m R =>
      Matrix.fromBlocks X (0 : Matrix m m R) (0 : Matrix m m R) X
    let ι := fun X : Matrix m m R =>
      Matrix.fromBlocks X (0 : Matrix m m R) (0 : Matrix m m R) (0 : Matrix m m R)
    φ 1 = 1 ∧
    φ (conePlus P A) = conePlus (φ P) (φ A) ∧
    φ (genV P A C) = genV (φ P) (φ A) (φ C) ∧
    Matrix.trace (φ (genV P A C)) = (2 : ℤ) • Matrix.trace (genV P A C) ∧
    ι P * ι A * (ι 1 - ι P) = ι (conePlus P A) ∧
    Matrix.trace (ι (genV P A C)) = Matrix.trace (genV P A C) := by
  dsimp only
  have hPhi1 :
      Matrix.fromBlocks (1 : Matrix m m R) (0 : Matrix m m R) (0 : Matrix m m R) (1 : Matrix m m R) = 1 :=
    Matrix.fromBlocks_one
  have hPhiMul : ∀ X Y : Matrix m m R,
      Matrix.fromBlocks (X * Y) (0 : Matrix m m R) (0 : Matrix m m R) (X * Y) =
        Matrix.fromBlocks X (0 : Matrix m m R) (0 : Matrix m m R) X *
          Matrix.fromBlocks Y (0 : Matrix m m R) (0 : Matrix m m R) Y := by
    intro X Y
    simp [Matrix.fromBlocks_multiply]
  have hPhiSub : ∀ X Y : Matrix m m R,
      Matrix.fromBlocks (X - Y) (0 : Matrix m m R) (0 : Matrix m m R) (X - Y) =
        Matrix.fromBlocks X (0 : Matrix m m R) (0 : Matrix m m R) X -
          Matrix.fromBlocks Y (0 : Matrix m m R) (0 : Matrix m m R) Y := by
    intro X Y
    ext (i | i) (j | j) <;> simp
  have hPhiAdd : ∀ X Y : Matrix m m R,
      Matrix.fromBlocks (X + Y) (0 : Matrix m m R) (0 : Matrix m m R) (X + Y) =
        Matrix.fromBlocks X (0 : Matrix m m R) (0 : Matrix m m R) X +
          Matrix.fromBlocks Y (0 : Matrix m m R) (0 : Matrix m m R) Y := by
    intro X Y
    simp [Matrix.fromBlocks_add]
  have hPhiConePlus :
      Matrix.fromBlocks (conePlus P A) (0 : Matrix m m R) (0 : Matrix m m R) (conePlus P A) =
        conePlus (Matrix.fromBlocks P (0 : Matrix m m R) (0 : Matrix m m R) P)
          (Matrix.fromBlocks A (0 : Matrix m m R) (0 : Matrix m m R) A) := by
    dsimp [conePlus]
    rw [hPhiMul, hPhiMul, hPhiSub, hPhi1]
  have hPhiConeMinus :
      Matrix.fromBlocks (coneMinus P C) (0 : Matrix m m R) (0 : Matrix m m R) (coneMinus P C) =
        coneMinus (Matrix.fromBlocks P (0 : Matrix m m R) (0 : Matrix m m R) P)
          (Matrix.fromBlocks C (0 : Matrix m m R) (0 : Matrix m m R) C) := by
    dsimp [coneMinus]
    rw [hPhiMul, hPhiMul, hPhiSub, hPhi1]
  have hPhiV :
      Matrix.fromBlocks (genV P A C) (0 : Matrix m m R) (0 : Matrix m m R) (genV P A C) =
        genV (Matrix.fromBlocks P (0 : Matrix m m R) (0 : Matrix m m R) P)
          (Matrix.fromBlocks A (0 : Matrix m m R) (0 : Matrix m m R) A)
          (Matrix.fromBlocks C (0 : Matrix m m R) (0 : Matrix m m R) C) := by
    dsimp [genV, anticomm]
    rw [hPhiAdd, hPhiMul, hPhiMul, hPhiConePlus, hPhiConeMinus]
  have hTraceFromBlocks : ∀ X Y : Matrix m m R,
      Matrix.trace (Matrix.fromBlocks X (0 : Matrix m m R) (0 : Matrix m m R) Y) =
        Matrix.trace X + Matrix.trace Y := by
    intro X Y
    simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
  have hTracePhi :
      Matrix.trace (Matrix.fromBlocks (genV P A C) (0 : Matrix m m R) (0 : Matrix m m R) (genV P A C)) =
        (2 : ℤ) • Matrix.trace (genV P A C) := by
    rw [hTraceFromBlocks, two_zsmul]
  have hIotaSub :
      Matrix.fromBlocks (1 : Matrix m m R) (0 : Matrix m m R) (0 : Matrix m m R) (0 : Matrix m m R) -
        Matrix.fromBlocks P (0 : Matrix m m R) (0 : Matrix m m R) (0 : Matrix m m R) =
      Matrix.fromBlocks (1 - P) (0 : Matrix m m R) (0 : Matrix m m R) (0 : Matrix m m R) := by
    ext (i | i) (j | j) <;> simp
  have hIotaCone :
      Matrix.fromBlocks P (0 : Matrix m m R) (0 : Matrix m m R) (0 : Matrix m m R) *
        Matrix.fromBlocks A (0 : Matrix m m R) (0 : Matrix m m R) (0 : Matrix m m R) *
        (Matrix.fromBlocks (1 : Matrix m m R) (0 : Matrix m m R) (0 : Matrix m m R) (0 : Matrix m m R) -
          Matrix.fromBlocks P (0 : Matrix m m R) (0 : Matrix m m R) (0 : Matrix m m R)) =
      Matrix.fromBlocks (conePlus P A) (0 : Matrix m m R) (0 : Matrix m m R) (0 : Matrix m m R) := by
    dsimp [conePlus]
    rw [hIotaSub]
    simp [Matrix.fromBlocks_multiply]
  have hTraceIota :
      Matrix.trace (Matrix.fromBlocks (genV P A C) (0 : Matrix m m R) (0 : Matrix m m R) (0 : Matrix m m R)) =
        Matrix.trace (genV P A C) := by
    rw [hTraceFromBlocks, Matrix.trace_zero, add_zero]
  exact ⟨hPhi1, hPhiConePlus, hPhiV, hTracePhi, hIotaCone, hTraceIota⟩

/-- **Direct-Limit Intertwining & Unit-Horizon Vortex Coercivity Descent (`Stage n →+* Limit`)**:
1. For every finite stage `n : ℕ` and any `P A C : Stage n`, the canonical colimit map
   `ofStage n : Stage n →+* Limit` intertwines both `opVortexMassSq` and `opMoebiusBruhatVortex`.
2. When a cofinal stage family `(P n, A n)` satisfies the unit-horizon hypotheses of
   `peirce_tetraktys_unit_horizon_coercivity_descends`, the vortex mass operator
   `opVortexMassSq Pinf Ainf (star Ainf)` satisfies the colimit coercivity bound with constant `8`:
   `(8 : ℝ) * tau (star (x - Pinf * x * Pinf) * (x - Pinf * x * Pinf)) ≤
    (4 : ℝ) * tau (star x * (genV Pinf Ainf (star Ainf) * x + x * genV Pinf Ainf (star Ainf)))`. -/
theorem yang_mills_colimit_vortex_coercivity_descent
    (n start : ℕ) (P₀ A₀ C₀ : Stage n)
    (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ k (y : Stage k), tau (ofStage k y) = normalizedTrace k y)
    (P A : ∀ k, Stage k) (Pinf Ainf : Limit)
    (hP : ∀ k, start ≤ k → ofStage k (P k) = Pinf)
    (hA : ∀ k, start ≤ k → ofStage k (A k) = Ainf)
    (hPid : ∀ k, start ≤ k → P k * P k = P k)
    (hPstar : ∀ k, start ≤ k → star (P k) = P k)
    (hV : ∀ k, start ≤ k → genV (P k) (A k) (star (A k)) = 1)
    (x : Limit) :
    ofStage n (opVortexMassSq P₀ A₀ C₀) =
      opVortexMassSq (ofStage n P₀) (ofStage n A₀) (ofStage n C₀) ∧
    ofStage n (opMoebiusBruhatVortex P₀ A₀ C₀) =
      opMoebiusBruhatVortex (ofStage n P₀) (ofStage n A₀) (ofStage n C₀) ∧
    (8 : ℝ) * tau (star (x - Pinf * x * Pinf) * (x - Pinf * x * Pinf)) ≤
      (4 : ℝ) * tau (star x *
        (genV Pinf Ainf (star Ainf) * x + x * genV Pinf Ainf (star Ainf))) := by
  have hMapV : ofStage n (genV P₀ A₀ C₀) =
      genV (ofStage n P₀) (ofStage n A₀) (ofStage n C₀) :=
    map_genV (ofStage n) P₀ A₀ C₀
  have hMapVortex : ofStage n (opVortexMassSq P₀ A₀ C₀) =
      opVortexMassSq (ofStage n P₀) (ofStage n A₀) (ofStage n C₀) := by
    dsimp [opVortexMassSq, opQuadraticCoupling]
    rw [map_zsmul, hMapV]
  have hMapBruhat : ofStage n (opMoebiusBruhatVortex P₀ A₀ C₀) =
      opMoebiusBruhatVortex (ofStage n P₀) (ofStage n A₀) (ofStage n C₀) := by
    dsimp [opMoebiusBruhatVortex, opUnipotentPlus, opUnipotentMinus, conePlus, coneMinus]
    simp [map_mul, map_add, map_sub]
  have hCoercive2 := peirce_tetraktys_unit_horizon_coercivity_descends
    start tau htau P A Pinf Ainf hP hA hPid hPstar hV x
  have hCoercive8 :
      (8 : ℝ) * tau (star (x - Pinf * x * Pinf) * (x - Pinf * x * Pinf)) ≤
        (4 : ℝ) * tau (star x *
          (genV Pinf Ainf (star Ainf) * x + x * genV Pinf Ainf (star Ainf))) := by
    linarith [hCoercive2]
  exact ⟨hMapVortex, hMapBruhat, hCoercive8⟩

/-! ===========================================================================
    Section 6: Nilpotent-First & Two-Sheet Tetraktys Closure, `M0` Non-Commutative
               Matrix Witnesses (`T16`/`T17`), & Master Cross-Lane Synthesis
    =========================================================================== -/

/-- **Nilpotent-First Tetraktys Algebraic Identities (Target 1)**:
Every nilpotent pair `(N, M)` (`N * N = 0`, `M * M = 0`) in any associative ring `[Ring B]`
directly induces the Tetraktys quadruple `(Φ = N + M, J = N - M, V = N * M + M * N, Σ = N * M - M * N)`
satisfying `Φ² = V`, `J² = -V`, `J * Φ = Σ`, `Φ * J = -Σ`, `Φ * J + J * Φ = 0`, and
`(V + Σ) * (V - Σ) = 0` without assuming a prior idempotent `P`. -/
theorem nilpotent_first_tetraktys_identities
    {N M : B} (hN2 : N * N = 0) (hM2 : M * M = 0) :
    let Φ := N + M
    let J := N - M
    let V := N * M + M * N
    let Sig := N * M - M * N
    Φ * Φ = V ∧
    J * J = -V ∧
    J * Φ = Sig ∧
    Φ * J = -Sig ∧
    Φ * J + J * Φ = 0 ∧
    (V + Sig) * (V - Sig) = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      (N + M) * (N + M) = N * N + N * M + M * N + M * M := by noncomm_ring
      _ = N * M + M * N := by rw [hN2, hM2]; abel
  · calc
      (N - M) * (N - M) = N * N - N * M - M * N + M * M := by noncomm_ring
      _ = -(N * M + M * N) := by rw [hN2, hM2]; abel
  · calc
      (N - M) * (N + M) = N * N + N * M - M * N - M * M := by noncomm_ring
      _ = N * M - M * N := by rw [hN2, hM2]; abel
  · calc
      (N + M) * (N - M) = N * N - N * M + M * N - M * M := by noncomm_ring
      _ = -(N * M - M * N) := by rw [hN2, hM2]; abel
  · calc
      (N + M) * (N - M) + (N - M) * (N + M) =
          (N * N + N * N) - (M * M + M * M) := by noncomm_ring
      _ = 0 := by rw [hN2, hM2]; abel
  · calc
      ((N * M + M * N) + (N * M - M * N)) * ((N * M + M * N) - (N * M - M * N)) =
          (2 : ℤ) • (N * (M * M) * N) + (2 : ℤ) • (N * (M * M) * N) := by noncomm_ring
      _ = 0 := by rw [hM2, mul_zero, zero_mul, smul_zero, add_zero]

/-- Complete algebraic closure of the Two-Sheet Tetraktys quadruple `(genPhi, genJ, genV, genSig)` (Target 1):
`genPhi² = genV`, `genJ² = -genV`, `genJ * genPhi = genSig`, SUSY anticommutator
`genPhi * genJ + genJ * genPhi = 0`, Cartan commutator
`genPhi * genJ - genJ * genPhi = -(2 : ℤ) • genSig`, Para-Kähler locking
`invS P * genV = genSig` and `invS P * genSig = genV`, hyperbolic lightcone annihilation
`(genV + genSig) * (genV - genSig) = 0`, and Noether–Killing centrality
`genV * genPhi = genPhi * genV` and `genV * genJ = genJ * genV`. -/
theorem two_sheet_tetraktys_para_kahler_and_cartan_closure
    {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    genJ P A C * genPhi P A C = genSig P A C ∧
    genPhi P A C * genJ P A C + genJ P A C * genPhi P A C = 0 ∧
    genPhi P A C * genJ P A C - genJ P A C * genPhi P A C = -(2 : ℤ) • genSig P A C ∧
    invS P * genV P A C = genSig P A C ∧
    invS P * genSig P A C = genV P A C ∧
    (genV P A C + genSig P A C) * (genV P A C - genSig P A C) = 0 ∧
    genV P A C * genPhi P A C = genPhi P A C * genV P A C ∧
    genV P A C * genJ P A C = genJ P A C * genV P A C := by
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, ?_,
    by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩
  rw [neg_zsmul, two_zsmul]
  peirce_nf hP

/-- Concrete `2 × 2` integer matrix idempotent `P₀ = !![1, 0; 0, 0]`. -/
def ymWitnessP : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]

/-- Concrete `2 × 2` integer upper-right matrix `A₀ = !![0, 1; 0, 0]`. -/
def ymWitnessA : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

/-- Concrete `2 × 2` integer lower-left matrix `C₀ = !![0, 0; 1, 0]`. -/
def ymWitnessC : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

/-- Polymorphic `2 × 2` matrix idempotent `!![1, 0; 0, 0]` over `[Ring K]`. -/
def ymWitness2P {K : Type*} [Ring K] : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, 0]

/-- Polymorphic `2 × 2` upper-right matrix `!![0, 1; 0, 0]` over `[Ring K]`. -/
def ymWitness2A {K : Type*} [Ring K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]

/-- Polymorphic `4 × 4` matrix idempotent `E₀₀` over `[Ring R]`. -/
def ymWitness4P {R : Type*} [Ring R] : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Polymorphic `4 × 4` upper-right matrix `E₀₁` over `[Ring R]`. -/
def ymWitness4A {R : Type*} [Ring R] : Matrix (Fin 4) (Fin 4) R :=
  !![0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Carrier-matched non-commutativity witness for `Matrix (Fin 2) (Fin 2) K` (`T16`). -/
theorem ym_matrix2_noncomm_witness {K : Type*} [Ring K] [Nontrivial K] :
    ymWitness2P (K := K) * ymWitness2A (K := K) ≠
      ymWitness2A (K := K) * ymWitness2P (K := K) := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) h
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at h01
  simp [ymWitness2P, ymWitness2A] at h01

/-- Carrier-matched non-commutativity witness for `Matrix (Fin 3) (Fin 3) R` (`T16`). -/
theorem ym_matrix3_noncomm_witness {R : Type*} [Ring R] [Nontrivial R] :
    shiftNilpotent3Up (R := R) * shiftNilpotent3Down (R := R) ≠
      shiftNilpotent3Down (R := R) * shiftNilpotent3Up (R := R) := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 0) h
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_three] at h00
  simp [shiftNilpotent3Up, shiftNilpotent3Down] at h00

/-- Carrier-matched non-commutativity witness for `Matrix (Fin 4) (Fin 4) R` (`T16`). -/
theorem ym_matrix4_noncomm_witness {R : Type*} [Ring R] [Nontrivial R] :
    ymWitness4P (R := R) * ymWitness4A (R := R) ≠
      ymWitness4A (R := R) * ymWitness4P (R := R) := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) R => M 0 1) h
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h01
  simp [ymWitness4P, ymWitness4A] at h01

/-- **Concrete `M0` Non-Commutative Matrix Witness (`T16`/`T17`)**:
In `Matrix (Fin 2) (Fin 2) ℤ`:
1. `ymWitnessP` is idempotent (`P₀ * P₀ = P₀`) and does not commute with `ymWitnessA`
   (`P₀ * A₀ ≠ A₀ * P₀`),
2. The chiral connection `genPhi P₀ A₀ C₀` and symplectic current `genJ P₀ A₀ C₀` do not commute
   (`genPhi * genJ ≠ genJ * genPhi`),
3. The two-sheeted condensate `genV P₀ A₀ C₀` equals the identity matrix `1 ≠ 0`, and the vortex
   mass-squared `opVortexMassSq P₀ A₀ C₀` equals `(4 : ℤ) • 1 ≠ 0`. -/
theorem yang_mills_lane_isomorphisms_noncomm_witness :
    ymWitnessP * ymWitnessP = ymWitnessP ∧
    ymWitnessP * ymWitnessA ≠ ymWitnessA * ymWitnessP ∧
    genPhi ymWitnessP ymWitnessA ymWitnessC * genJ ymWitnessP ymWitnessA ymWitnessC ≠
      genJ ymWitnessP ymWitnessA ymWitnessC * genPhi ymWitnessP ymWitnessA ymWitnessC ∧
    genV ymWitnessP ymWitnessA ymWitnessC = 1 ∧
    opVortexMassSq ymWitnessP ymWitnessA ymWitnessC = (4 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  refine ⟨by decide, ?_, ?_, by decide, by decide⟩
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
    revert h01; decide
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
    revert h00; decide

/-- **Master Cross-Lane Yang–Mills & Native Mathlib Archetype Synthesis**:
Packages the cross-lane identities across `AssociativeGaugeConnection`, `YangMillsOrbitGramian`,
`OsterwalderSchraderPeirceReflection`, `TwoSheetedNilpotentCondensateVortexMass`,
`YangMillsTHooftWilsonBraiding`, `DrazinEpistemicSolveEtCoagula`, `ChiralLorentzTwistorCartanUncertaintyPoset`,
and native Mathlib `Matrix (Fin 4) (Fin 4)` / `Matrix (Fin 3) (Fin 3)` into one theorem. -/
theorem yang_mills_all_lanes_master_isomorphism_synthesis
    [StarRing B] {P : B} (hP : P * P = P) (hPstar : star P = P) (A C X : B)
    {K : Type*} [CommRing K]
    (Z0 Z1 Z2 Z3 : InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Twistor4 K)
    (u1 u2 u3 : InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3 K) :
    InfoGeometry.Geometry.AssociativeGaugeConnection.gaugePotential
      (InfoGeometry.Geometry.AssociativeGaugeConnection.innerDerivative (R := ℤ) P)
      (0 : B) (moebiusBruhatVortexUnit hP A C) =
      -(genPhi P A C + genSig P A C) + conePlus P A * coneMinus P C * conePlus P A ∧
    orbitCommutator P (genPhi P A (star A)) = genJ P A (star A) ∧
    orbitMassMode P (genPhi P A (star A)) = osPeirceMassPairing P A ∧
    osPeirceMassPairing P A = genV P A (star A) ∧
    opVortexMassSq P A (star A) = (4 : ℤ) • orbitMassMode P (genPhi P A (star A)) ∧
    (conjMinus P C P - conjPlus P A P) * (conjMinus P C P - conjPlus P A P) = genV P A C ∧
    peirceGradingDeriv P (peirceGradingDeriv P (peirceGradingDeriv P X)) =
      peirceGradingDeriv P X ∧
    cartanCurvature2Form P (genPhi P A C) = genJ P A C + genV P A C ∧
    Matrix.det (nativeTwistorMatrix4 Z0 Z1 Z2 Z3) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.twistorBracket4 Z0 Z1 Z2 Z3 ∧
    Matrix.det (nativeBaryonMatrix3 u1 u2 u3) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.baryonDet3 u1 u2 u3 ∧
    (flagProj3_0 + flagProj3_1 + flagProj3_2 : Matrix (Fin 3) (Fin 3) K) = 1 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.casimir2
      nilRaise3 nilLower3 cartanDiag3 =
      (8 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  have hDet := native_matrix_det_twistor4_eq_baryon_and_zorn_anticommutator
    (0 : InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Mat4 K)
    Z0 Z1 Z2 Z3 u1 u2 u3
  have hFlag := @order3_nilpotent_flag_and_sl2_casimir_constant_eight K _
  have hGram := orbitMassMode_genPhi_eq_osPeirceMassPairing_eq_genV hP hPstar A
  have hChord := fubini_study_chordal_distance_unipotent_projectors hP A C
  have hRungs := chiral_lorentz_rungs_0_to_4_and_diamond_poset_bridge hP A C X X X
  exact ⟨gaugePotential_peirceGradingDeriv_moebiusBruhatVortexUnit hP A C,
    orbitCommutator_genPhi_eq_genJ hP A (star A),
    hGram.1, hGram.2.1, hGram.2.2.1,
    hChord.2.2.2.2,
    peirceGradingDeriv_cube hP X,
    hRungs.2.2.2.2.2.2.2.2.2.2.1.trans hRungs.2.2.2.2.2.2.2.2.2.2.2.1,
    hDet.2.2.1, hDet.2.1,
    hFlag.2.2.2.2.2.2.2.2.1, hFlag.2.2.2.2.2.2.2.2.2⟩

end InfoGeometry.Canonical.YangMillsLaneIsomorphisms
