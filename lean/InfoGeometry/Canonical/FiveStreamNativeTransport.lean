/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.IdempotentOrbitContracts
import InfoGeometry.Canonical.RootsOfZeroUnityMoebiusModularG22
import InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance
import InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis
import InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
import InfoGeometry.Core.InnerConjugationJet

/-!
# Native consumers of the five canonical streams

The circle-normalized rotor is an ambient unit. Its moving pole belongs to
an actual stabilizer orbit, its quarter turn is a represented modular-group
generator, its weighted readouts obey joint covariance, and its first jet is
the native square-zero conjugation law. No new algebra carrier or state notion.
-/

namespace InfoGeometry.Canonical.FiveStreamNativeTransport

open DeBruijnRotorAlternationCycle
open InfoGeometry.OperatorAlgebra.TracialCARDensity
open InfoGeometry.Core.ParabolicModularRepresentation

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable {d B : A}

/-- Native CAR supplies the four seed laws, without an extra inverse assumption. -/
theorem carPair_isDualSeedPair (P : SplitClifford.CARPair A) :
    IsDualSeedPair P.ann P.cre := by
  refine ⟨P.ann_sq, P.cre_sq, ?_, ?_⟩
  · simpa only [mul_assoc] using ann_cre_ann P
  · simpa only [mul_assoc] using cre_ann_cre P

/-- Promote the existing supported rotor to an actual ambient unit. -/
def phaseRotorUnit (h : IsDualSeedPair d B) (c s : R)
    (hc : c * c + s * s = 1) : Aˣ where
  val := phaseRotor c s d B
  inv := phaseRotor c (-s) d B
  val_inv := ReflexiveNilpotentFlows.rotor_inverse h.d_sq h.B_sq h.dBd h.BdB c s hc
  inv_val := by
    change ReflexiveNilpotentFlows.rotor c (-s) d B *
      ReflexiveNilpotentFlows.rotor c s d B = 1
    simpa only [neg_mul_neg, neg_neg] using
      ReflexiveNilpotentFlows.rotor_inverse h.d_sq h.B_sq h.dBd h.BdB c (-s)
        (by simpa only [neg_mul_neg] using hc)

/-- Stream 5 motion lies in Stream 1's existing unit orbit. -/
theorem movingPolePlus_mem_unitOrbit (h : IsDualSeedPair d B) (c s : R)
    (hc : c * c + s * s = 1) :
    movingPolePlus c s d B ∈
      Set.range (GrassmannianBundleCyclotomicOrientability.unitOrbitMap (polePlus d B)) := by
  exact ⟨phaseRotorUnit h c s hc, rfl⟩

attribute [local instance] IdempotentOrbitContracts.unitConjugation
local instance conjugationSMul : SMul Aˣ A := IdempotentOrbitContracts.unitConjugation.toSMul

/-- The moving pole has a preimage in the native quotient by the stabilizer. -/
theorem movingPolePlus_stabilizer_quotient (h : IsDualSeedPair d B) (c s : R)
    (hc : c * c + s * s = 1) :
    ∃ q : Aˣ ⧸ MulAction.stabilizer Aˣ (polePlus d B),
      ((IdempotentOrbitContracts.quotientEquivOrbit (polePlus d B)) q : A) =
        movingPolePlus c s d B := by
  have hm : movingPolePlus c s d B ∈ MulAction.orbit Aˣ (polePlus d B) := by
    rw [IdempotentOrbitContracts.orbit_eq_existing_range]
    exact movingPolePlus_mem_unitOrbit h c s hc
  obtain ⟨q, hq⟩ := (IdempotentOrbitContracts.quotientEquivOrbit (polePlus d B)).surjective
    ⟨movingPolePlus c s d B, hm⟩
  exact ⟨q, congrArg Subtype.val hq⟩

/-- Stream 2's factorization identifies the rotor with the actual PR #206 generator. -/
theorem quarterTurn_eq_modular_generator (h : IsDualSeedPair d B) :
    phaseRotorUnit h (0 : R) 1 (by simp) =
      representation h.d_sq h.B_sq h.dBd h.BdB (PresentedGroup.of false) := by
  simp only [representation, ofRelations_s]
  apply Units.ext
  change phaseRotor (0 : R) 1 d B = (1 + d) * (1 - B) * (1 + d)
  rw [RootsOfZeroUnityMoebiusModularG22.tits_bruhat_moufang_factorization h.d_sq h.dBd]
  simp only [phaseRotor, zero_smul, one_smul, add_zero]
  rfl

/-- Stream 4's double-shear cube is the square of that represented rotor unit. -/
theorem doubleShear_cube_eq_quarterTurn_square (h : IsDualSeedPair d B) :
    ModularParabolicCyclotomicSynthesis.parabolicHexalityOp d B ^ 3 =
      ((phaseRotorUnit h (0 : R) 1 (by simp) : Aˣ) : A) ^ 2 := by
  rw [quarterTurn_eq_modular_generator]
  simp only [representation, ofRelations_s]
  exact congrArg (fun u : Aˣ => (u : A)) (unit_relations h.d_sq h.B_sq h.dBd h.BdB).2.symm

/-- The transported Stream 3 density is the same weighted sum of moving poles. -/
theorem transportedWeight (u v c s : R) :
    phaseRotor c s d B * UnifiedGeometryOperatorSignificance.kmsModularWeight u v d B *
        phaseRotor c (-s) d B =
      (u * u) • movingPoleMinus c s d B + (v * v) • movingPolePlus c s d B := by
  simp only [UnifiedGeometryOperatorSignificance.kmsModularWeight,
    UnifiedGeometryOperatorSignificance.projMinus, UnifiedGeometryOperatorSignificance.projPlus,
    movingPoleMinus, movingPolePlus, poleMinus, polePlus,
    mul_add, add_mul, mul_smul_comm, smul_mul_assoc]

/-- Actual native tracial readouts are invariant under joint density/observable transport. -/
theorem movingWeight_joint_covariance (τ : InfoGeometry.NCG.TracialFunctional R A)
    (h : IsDualSeedPair d B) (u v c s : R) (hc : c * c + s * s = 1) (X : A) :
    weighted τ ((u * u) • movingPoleMinus c s d B + (v * v) • movingPolePlus c s d B)
      (phaseRotor c s d B * X * phaseRotor c (-s) d B) =
    weighted τ (UnifiedGeometryOperatorSignificance.kmsModularWeight u v d B) X := by
  rw [← transportedWeight]
  exact joint_covariance τ (phaseRotorUnit h c s hc) _ X

/-- Exact algebraic first-order projector motion, rather than a supplied derivative field. -/
theorem movingPole_firstJet (h : IsDualSeedPair d B) :
    (InfoGeometry.Core.InnerConjugationJet.unit (wheelGenerator d B) : DualNumber A) *
      TrivSqZeroExt.inl (polePlus d B) *
        (↑(InfoGeometry.Core.InnerConjugationJet.unit (wheelGenerator d B))⁻¹ : DualNumber A) =
      TrivSqZeroExt.inl (polePlus d B) + TrivSqZeroExt.inr (-transitionVelocity d B) := by
  have hj := InfoGeometry.Core.InnerConjugationJet.conjugate
    (wheelGenerator d B) (polePlus d B) 0
  simp only [TrivSqZeroExt.inr_zero, add_zero, zero_add] at hj
  change _ = TrivSqZeroExt.inl (polePlus d B) +
    TrivSqZeroExt.inr (lieBracket (wheelGenerator d B) (polePlus d B)) at hj
  rw [lieBracket_wheel_polePlus h] at hj
  exact hj

/-- Rotor construction commutes with actual algebra maps, including stage embeddings. -/
theorem map_phaseRotor {C : Type*} [Ring C] [Algebra R C]
    (f : A →ₐ[R] C) (c s : R) (d B : A) :
    f (phaseRotor c s d B) = phaseRotor c s (f d) (f B) := by
  simp only [phaseRotor, zeroModeSupport, carrierSupport, polePlus, poleMinus,
    wheelGenerator, map_add, map_sub, map_mul, map_one, map_smul]

/-- Moving idempotents commute with the same algebra maps. -/
theorem map_movingPolePlus {C : Type*} [Ring C] [Algebra R C]
    (f : A →ₐ[R] C) (c s : R) (d B : A) :
    f (movingPolePlus c s d B) = movingPolePlus c s (f d) (f B) := by
  simp only [movingPolePlus, polePlus, map_mul, map_phaseRotor]

end InfoGeometry.Canonical.FiveStreamNativeTransport
