/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DoubledCARIntertwiner
import InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Existing doubled phase flow, actual Zorn right CAR, and the Fock intertwiner

For each selected mode the multiplicity space is the actual annihilation
kernel. CAR proves that it has dimension four. The sole basis choice is its
linear identification with `EuclideanSpace ℝ (Fin 4)`. The total carrier map
is then the explicit CAR splitting, not a dimension-only map of eight spaces.

The equivalences below are linear, not asserted isometric for an unprovided
Zorn metric. They do not preserve the nonassociative Zorn multiplication.
-/

noncomputable section
namespace InfoGeometry.Canonical.ZornBdGPhaseFlowBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.ProjectorEquivariance
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.RealDoubledWaveplate
open InfoGeometry.Algebra.CARModuleDecomposition
open InfoGeometry.Canonical.DoubledCARIntertwiner
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
open InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonionExteriorGradePeirceParityBridge
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

abbrev Exterior3 := InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.Exterior3
abbrev Multiplicity := EuclideanSpace ℝ (Fin 4)
abbrev ZornCarrier := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev ModeKernel (i : Fin 3) := (rightRegularCARPair i).ann.ker

/-- Eight-dimensional Zorn CAR has a four-dimensional one-mode multiplicity. -/
theorem modeKernel_finrank (i : Fin 3) : Module.finrank ℝ (ModeKernel i) = 4 := by
  have h := finrank_twice_kernel (rightRegularCARPair i)
  rw [cz_finrank] at h
  change 8 = Module.finrank ℝ (ModeKernel i) + Module.finrank ℝ (ModeKernel i) at h
  omega

/-- A declared noncanonical basis choice only on the four-dimensional kernel. -/
def multiplicityEquiv (i : Fin 3) : Multiplicity ≃ₗ[ℝ] ModeKernel i :=
  LinearEquiv.ofFinrankEq _ _ (by rw [modeKernel_finrank]; exact finrank_euclideanSpace_fin)

/-- The explicit occupied/unoccupied CAR splitting on the actual Zorn carrier. -/
def doubledZornEquiv (i : Fin 3) : DoubledSpace Multiplicity ≃ₗ[ℝ] ZornCarrier :=
  doubledCAREquiv (rightRegularCARPair i) (multiplicityEquiv i)

theorem doubled_finrank : Module.finrank ℝ (DoubledSpace Multiplicity) = 8 := by
  have h := (doubledZornEquiv 0).finrank_eq
  simpa only [cz_finrank] using h

/-- The existing right-regular pair, not a new pair assumed equivalent. -/
theorem annihilation_intertwiner (i : Fin 3) (x : DoubledSpace Multiplicity) :
    (rightRegularCARPair i).ann (doubledZornEquiv i x) =
      doubledZornEquiv i (concreteCARAnnihilation x) :=
  annihilation_intertwines (rightRegularCARPair i) (multiplicityEquiv i) x

theorem creation_intertwiner (i : Fin 3) (x : DoubledSpace Multiplicity) :
    (rightRegularCARPair i).cre (doubledZornEquiv i x) =
      doubledZornEquiv i (concreteCARCreation x) :=
  creation_intertwines (rightRegularCARPair i) (multiplicityEquiv i) x

theorem grading_intertwiner (i : Fin 3) (x : DoubledSpace Multiplicity) :
    ((rightRegularCARPair i).cre * (rightRegularCARPair i).ann -
      (rightRegularCARPair i).ann * (rightRegularCARPair i).cre) (doubledZornEquiv i x) =
      doubledZornEquiv i (spectral_epsilon x) :=
  grading_intertwines (rightRegularCARPair i) (multiplicityEquiv i) x

/-- Genuine operator on Zorn; the mode dependence is explicit. -/
def zornPhase (i : Fin 3) (θ : ℝ) : Module.End ℝ ZornCarrier :=
  carPhase (rightRegularCARPair i) θ

theorem phaseFlow_intertwiner (i : Fin 3) (θ : ℝ) (x : DoubledSpace Multiplicity) :
    zornPhase i θ (doubledZornEquiv i x) =
      doubledZornEquiv i (phaseFlow θ x) :=
  phase_intertwines (rightRegularCARPair i) (multiplicityEquiv i) θ x

theorem zornPhase_inverse (i : Fin 3) (θ : ℝ) :
    zornPhase i (-θ) * zornPhase i θ = 1 := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (doubledZornEquiv i).surjective z
  change zornPhase i (-θ) (zornPhase i θ (doubledZornEquiv i x)) = doubledZornEquiv i x
  rw [phaseFlow_intertwiner, phaseFlow_intertwiner, phaseFlow_left_inverse_apply]

/-- Fock-side operator uses the actual exterior contraction and wedge owners. -/
def fockPhase (i : Fin 3) (θ : ℝ) : Module.End ℝ Exterior3 :=
  Real.cos θ • 1 + Real.sin θ •
    (exteriorContract3 (modeCovector i) - exteriorWedge3 (modeVector i))

theorem fockBdG_phase_intertwiner (i : Fin 3) (θ : ℝ) (ψ : Exterior3) :
    zornPhase i θ (fockBdGEquiv ψ) = fockBdGEquiv (fockPhase i θ ψ) := by
  have hc := LinearMap.congr_fun (fockBdGEquiv_creation_intertwines i) ψ
  have ha := LinearMap.congr_fun (fockBdGEquiv_annihilation_intertwines i) ψ
  change (rightRegularCARPair i).cre (fockBdGEquiv ψ) =
    fockBdGEquiv (exteriorWedge3 (modeVector i) ψ) at hc
  change (rightRegularCARPair i).ann (fockBdGEquiv ψ) =
    fockBdGEquiv (exteriorContract3 (modeCovector i) ψ) at ha
  change Real.cos θ • fockBdGEquiv ψ +
    Real.sin θ • ((rightRegularCARPair i).ann (fockBdGEquiv ψ) -
      (rightRegularCARPair i).cre (fockBdGEquiv ψ)) = _
  rw [ha, hc, ← map_sub, ← map_smul, ← map_smul, ← map_add]
  rfl

/-- The comparison triangle uses the existing universal Fock/BdG equivalence. -/
def doubledFockEquiv (i : Fin 3) : DoubledSpace Multiplicity ≃ₗ[ℝ] Exterior3 :=
  (doubledZornEquiv i).trans fockBdGEquiv.symm

@[simp] theorem comparison_triangle (i : Fin 3) (x : DoubledSpace Multiplicity) :
    fockBdGEquiv (doubledFockEquiv i x) = doubledZornEquiv i x :=
  fockBdGEquiv.apply_symm_apply _

theorem doubledFock_phase_intertwiner (i : Fin 3) (θ : ℝ)
    (x : DoubledSpace Multiplicity) :
    fockPhase i θ (doubledFockEquiv i x) = doubledFockEquiv i (phaseFlow θ x) := by
  apply fockBdGEquiv.injective
  rw [← fockBdG_phase_intertwiner, comparison_triangle, comparison_triangle,
    phaseFlow_intertwiner]

/-- Transported annihilation covariance on the actual Zorn target. -/
theorem phaseConjugation_annihilation (i : Fin 3) (θ : ℝ)
    (x : DoubledSpace Multiplicity) :
    zornPhase i (-θ) ((rightRegularCARPair i).ann
      (zornPhase i θ (doubledZornEquiv i x))) =
      doubledZornEquiv i (phaseConjugation θ (concreteCARAnnihilation) x) := by
  rw [phaseFlow_intertwiner, annihilation_intertwiner, phaseFlow_intertwiner]
  rfl

/-- Transported creation covariance, with the same orientation convention. -/
theorem phaseConjugation_creation (i : Fin 3) (θ : ℝ)
    (x : DoubledSpace Multiplicity) :
    zornPhase i (-θ) ((rightRegularCARPair i).cre
      (zornPhase i θ (doubledZornEquiv i x))) =
      doubledZornEquiv i (phaseConjugation θ (concreteCARCreation) x) := by
  rw [phaseFlow_intertwiner, creation_intertwiner, phaseFlow_intertwiner]
  rfl

end InfoGeometry.Canonical.ZornBdGPhaseFlowBridge
