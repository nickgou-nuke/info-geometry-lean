import Architect
import InfoGeometry.Canonical.Geometry
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field

namespace InfoGeometry.Canonical.Cayley

open scoped Topology

open InfoGeometry.Geometry.DualFlat

/-- Structure `Transport`. -/
@[blueprint "def:cayley-transport"]
abbrev Transport (U B : Type*) := U → B

/-- Structure `Bridge`. -/
@[blueprint "def:cayley-bridge"]
abbrev Bridge (U B : Type*) := U ≃ B

/-- Forward map induced by a reversible bridge. -/
abbrev Bridge.toBounded (C : Bridge U B) : U → B := C

/-- Backward map induced by a reversible bridge. -/
abbrev Bridge.toUnbounded (C : Bridge U B) : B → U := C.symm

/-- Forget reversibility and keep only forward transport. -/
abbrev Bridge.toTransport (C : Bridge U B) : Transport U B := C

@[simp] theorem Bridge.left_inv (C : Bridge U B) :
    Function.LeftInverse C.toUnbounded C.toBounded := by
  intro x
  exact Equiv.left_inv C x

@[simp] theorem Bridge.right_inv (C : Bridge U B) :
    Function.RightInverse C.toUnbounded C.toBounded := by
  intro x
  exact Equiv.right_inv C x

/-- Canonical name for a Cayley transport equivalence. -/
abbrev CayleyBridge (U B : Type*) := Bridge U B

/-- Canonical naming alias for a Cayley transport equivalence. -/
abbrev CayleyEquivalence (U B : Type*) := CayleyBridge U B

/-- Structure `CompatibleDualFlat`. -/
@[blueprint "def:compatible-dual-flat"]
structure CompatibleDualFlat
    {U B : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (T : Transport U B) (SU : DualFlatStructure U) where
  SB : DualFlatStructure B
  D_transport : ∀ x y : U, divergence SB (T x) (T y) = divergence SU x y
  grad_transport : ∀ x : U, T (nabla SU x) = nabla SB (T x)

/-- Canonical name for dual-flat compatibility under Cayley transport. -/
abbrev CayleyCompatibleDualFlat
    {U B : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (C : CayleyBridge U B) (SU : DualFlatStructure U) :=
  CompatibleDualFlat C.toTransport SU

/-- Canonical naming alias for dual-flat compatibility under Cayley transport. -/
abbrev CayleyDualFlatCompatibility
    {U B : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (C : CayleyBridge U B) (SU : DualFlatStructure U) :=
  CayleyCompatibleDualFlat C SU

/-- Definition `cayleyIdentityBridge`. -/
def cayleyIdentityBridge (E : Type*) : CayleyBridge E E := Equiv.refl E

/-- Definition `cayleyIdentityTransport`. -/
abbrev cayleyIdentityTransport (E : Type*) : Transport E E :=
  cayleyIdentityBridge E

/-- Definition `cayleyIdentityCompatibleGeometry`. -/
def cayleyIdentityCompatibleGeometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : DualFlatStructure E) : CayleyCompatibleDualFlat (cayleyIdentityBridge E) S where
  SB := S
  D_transport _ _ := rfl
  grad_transport _ := rfl

/-! ## Thermal-ray compactification -/

/-- Direct real thermal-ray Cayley compactification coordinate. -/
@[rep_depth thermo]
noncomputable def thermalCayley (β : ℝ) : ℝ :=
  (β - 1) / (β + 1)

/-- Algebraic normal form of the thermal Cayley coordinate away from its pole. -/
@[rep_depth thermo]
theorem thermalCayley_eq_one_sub (β : ℝ) (hβ : β + 1 ≠ 0) :
    thermalCayley β = 1 - 2 / (β + 1) := by
  unfold thermalCayley
  field_simp [hβ]
  ring

/--
The thermal-ray Cayley compactification tends to the boundary point `1` at
zero temperature (`β -> +∞`).

This theorem proves only the real compactification limit.  It does not identify
the full zero-temperature state accumulation set with the Cantor boundary.
-/
@[rep_depth thermo]
theorem thermalCayley_tendsto_atTop_one :
    Filter.Tendsto thermalCayley Filter.atTop (𝓝 1) := by
  have hden :
      Filter.Tendsto (fun β : ℝ => β + 1) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, ?_⟩
    intro β hβ
    linarith
  have hzero :
      Filter.Tendsto (fun β : ℝ => (2 : ℝ) / (β + 1)) Filter.atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hmain :
      Filter.Tendsto (fun β : ℝ => 1 - (2 : ℝ) / (β + 1))
        Filter.atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hzero
  have heq :
      thermalCayley =ᶠ[Filter.atTop]
        fun β : ℝ => 1 - (2 : ℝ) / (β + 1) := by
    filter_upwards [Filter.eventually_gt_atTop (-1 : ℝ)] with β hβ
    exact thermalCayley_eq_one_sub β (by linarith)
  simpa using hmain.congr' heq.symm

/-- Legacy compatibility alias for `cayleyIdentityBridge`. -/
abbrev identityBridge (E : Type*) : CayleyBridge E E := cayleyIdentityBridge E

attribute [deprecated cayleyIdentityBridge (since := "2026-02-26")] identityBridge

/-- Legacy compatibility alias for `cayleyIdentityCompatibleGeometry`. -/
abbrev identityCompatibleGeometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : DualFlatStructure E) : CayleyCompatibleDualFlat (cayleyIdentityBridge E) S :=
  cayleyIdentityCompatibleGeometry S

attribute [deprecated cayleyIdentityCompatibleGeometry (since := "2026-02-26")]
  identityCompatibleGeometry

/-- Theorem `cayley_pythagorean_invariance`. -/
@[blueprint "thm:cayley-pythagorean-invariance"]
theorem cayley_pythagorean_invariance
    {U B : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (T : Transport U B) (SU : DualFlatStructure U)
    (hT : CompatibleDualFlat T SU)
    (Prior Posterior Alt : U)
    (hproj : inner ℝ (nabla SU Prior - nabla SU Posterior) (Alt - Posterior) = 0) :
    divergence hT.SB (T Alt) (T Prior)
      = divergence hT.SB (T Alt) (T Posterior)
      + divergence hT.SB (T Posterior) (T Prior) := by
  have hU : divergence SU Alt Prior = divergence SU Alt Posterior + divergence SU Posterior Prior :=
    bregman_pythagorean SU Alt Posterior Prior hproj
  calc
    divergence hT.SB (T Alt) (T Prior)
        = divergence SU Alt Prior := by rw [hT.D_transport]
    _ = divergence SU Alt Posterior + divergence SU Posterior Prior := hU
    _ = divergence hT.SB (T Alt) (T Posterior)
        + divergence hT.SB (T Posterior) (T Prior) := by
          rw [hT.D_transport, hT.D_transport]

/-- Backward transport of the gradient along a reversible bridge. -/
theorem grad_transport_back
    {U B : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (C : CayleyBridge U B) (SU : DualFlatStructure U)
    (hC : CayleyCompatibleDualFlat C SU) (x : U) :
    C.toUnbounded (nabla hC.SB (C.toBounded x)) = nabla SU x := by
  have h := congrArg C.toUnbounded (hC.grad_transport x)
  simpa [Bridge.toTransport, Bridge.toBounded, Bridge.toUnbounded] using h.symm

/-- Compatibility camelCase alias for Cayley Pythagorean invariance. -/
theorem cayleyPythagoreanInvariance
    {U B : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (T : Transport U B) (SU : DualFlatStructure U)
    (hT : CompatibleDualFlat T SU)
    (prior posterior alt : U)
    (hproj : inner ℝ (nabla SU prior - nabla SU posterior) (alt - posterior) = 0) :
    divergence hT.SB (T alt) (T prior)
      = divergence hT.SB (T alt) (T posterior)
      + divergence hT.SB (T posterior) (T prior) := by
  have hInv :=
    cayley_pythagorean_invariance
      (T := T) (SU := SU) (hT := hT)
      (Prior := prior) (Posterior := posterior) (Alt := alt) hproj
  simpa using hInv

section RealInstances

/-- Quadratic potential on `ℝ`, used as a concrete transport test case. -/
def quadraticPotential (x : ℝ) : ℝ := x ^ (2 : ℕ)

/-- Dual-flat structure generated by the quadratic potential on `ℝ`. -/
def quadraticDualFlat : DualFlatStructure ℝ where
  ψ := quadraticPotential
  h_convex := by
    simpa [quadraticPotential] using
      (Even.strictConvexOn_pow (n := 2) (by decide : Even 2) (by decide : (2 : ℕ) ≠ 0))
  h_diff := by
    exact differentiable_pow 2

theorem quadraticPotential_deriv (x : ℝ) :
    deriv quadraticPotential x = 2 * x := by
  unfold quadraticPotential
  calc
    deriv (fun y : ℝ => y ^ 2) x = (2 : ℝ) * x ^ (2 - 1) := by
      exact deriv_pow_field (x := x) (n := 2)
    _ = 2 * x := by simp

theorem quadraticDualFlat_nabla (x : ℝ) :
    nabla quadraticDualFlat x = 2 * x := by
  have hdual :
      (InfoGeometry.Geometry.dualCoord (toHessianGeometry quadraticDualFlat) x) 1 = 2 * x := by
    have h := dualCoord_apply_sub_eq_deriv_mul (SR := quadraticDualFlat) (x := x + 1) (y := x)
    simpa [quadraticDualFlat, quadraticPotential_deriv] using h
  have hspec :=
    InfoGeometry.Geometry.dualCoordVec_spec
      (H := toHessianGeometry quadraticDualFlat) (x := x) (y := (1 : ℝ))
  have hinner : inner ℝ (nabla quadraticDualFlat x) 1 = 2 * x := by
    simpa [nabla, toHessianGeometry] using hspec.trans hdual
  simpa using hinner

theorem quadraticDualFlat_divergence (x y : ℝ) :
    divergence quadraticDualFlat x y = (x - y) ^ (2 : ℕ) := by
  rw [divergence_eq_bregmanDiv_real]
  change x ^ (2 : ℕ) - y ^ (2 : ℕ) - deriv (fun t : ℝ => t ^ (2 : ℕ)) y * (x - y) = (x - y) ^ (2 : ℕ)
  rw [deriv_pow_field]
  ring_nf

/-- Negation is a nontrivial reversible transport preserving the quadratic dual-flat geometry. -/
def cayleyNegationBridge : CayleyBridge ℝ ℝ := Equiv.neg ℝ

/-- The quadratic dual-flat structure is invariant under negation transport. -/
def cayleyNegationCompatibleGeometry :
    CayleyCompatibleDualFlat cayleyNegationBridge quadraticDualFlat where
  SB := quadraticDualFlat
  D_transport x y := by
    simp [cayleyNegationBridge, Bridge.toTransport]
    rw [quadraticDualFlat_divergence, quadraticDualFlat_divergence]
    ring
  grad_transport x := by
    simp [cayleyNegationBridge, Bridge.toTransport, quadraticDualFlat_nabla]

/-- Concrete Pythagorean invariance for the quadratic negation bridge. -/
theorem cayleyNegationPythagoreanInvariance
    (prior posterior alt : ℝ)
    (hproj : inner ℝ (nabla quadraticDualFlat prior - nabla quadraticDualFlat posterior)
      (alt - posterior) = 0) :
    divergence quadraticDualFlat (-alt) (-prior)
      = divergence quadraticDualFlat (-alt) (-posterior)
      + divergence quadraticDualFlat (-posterior) (-prior) := by
  simpa only [cayleyNegationBridge, Bridge.toTransport, Bridge.toBounded] using
    cayley_pythagorean_invariance
      (T := cayleyNegationBridge.toTransport) (SU := quadraticDualFlat)
      (hT := cayleyNegationCompatibleGeometry)
      (Prior := prior) (Posterior := posterior) (Alt := alt) hproj

end RealInstances

end InfoGeometry.Canonical.Cayley
