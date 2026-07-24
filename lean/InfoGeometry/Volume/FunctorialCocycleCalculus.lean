import InfoGeometry.Cocycle.ActionCocycle
import InfoGeometry.Canonical.Algebraic.ModularRotorCocycle
import InfoGeometry.Canonical.ProjectiveFoundation
import InfoGeometry.Volume.RadonNikodym
import InfoGeometry.Volume.ConnesCocycle
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Tactic

/-!
# Functorial Cocycle Calculus

This module is the volume/Radon-Nikodym/Connes consumer of the abstract
cocycle layer. The generic primitives live in:

* `InfoGeometry.Cocycle.GroupoidCocycle`;
* `InfoGeometry.Cocycle.LogCocycle`;
* `InfoGeometry.Cocycle.ActionCocycle`;
* `InfoGeometry.Cocycle.Infinitesimal`.

This file adds the volume-facing readouts:

* determinant as a `MulActionCocycle` over the trivial base;
* scalar RN bridges as additive action cocycles;
* Connes cocycle identity as the twisted additive-time cocycle law;
* multiplicative `2`-cocycles as mathlib `H²` classes, with vanishing exactly
  when they are coboundaries;
* projective multipliers as the canonical central-extension `2`-cocycle layer.

No von Neumann algebraic Radon-Nikodym theorem is asserted here.  The Connes
entry is the already-existing `IsConnesCocycle` interface from
`InfoGeometry.Volume.ConnesCocycle`.
-/

noncomputable section

namespace InfoGeometry.Volume.FunctorialCocycleCalculus

open InfoGeometry.Canonical.Algebraic
open InfoGeometry.Canonical.ProjectiveFoundation
open InfoGeometry.Cocycle
open InfoGeometry.Volume.RadonNikodym

/-! ## Determinant as scalar cocycle -/

section Determinant

variable {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]

/-- Matrix determinant is the basic multiplicative chain-rule cocycle. -/
theorem matrix_det_multiplicative_chain_rule (A B : Matrix n n R) :
    (A * B).det = A.det * B.det :=
  Matrix.det_mul A B

section RealLogDeterminant

variable {n : Type*} [DecidableEq n] [Fintype n]

/--
The logarithmic determinant chain rule.

This is the finite-dimensional scalar model for additive log-Jacobians in a
normalizing-flow/Radon-Nikodym chain rule.
-/
theorem matrix_logAbs_det_chain_rule (A B : Matrix n n ℝ)
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    Real.log |(A * B).det| = Real.log |A.det| + Real.log |B.det| := by
  rw [Matrix.det_mul, abs_mul]
  exact Real.log_mul (abs_ne_zero.mpr hA) (abs_ne_zero.mpr hB)

end RealLogDeterminant

/-- The determinant on `GL(n,R)` as a multiplicative action cocycle over `PUnit`. -/
def determinantCocycle : MulActionCocycle (Matrix.GeneralLinearGroup n R) PUnit Rˣ :=
  groupHomAsMulActionCocycle Matrix.GeneralLinearGroup.det

@[simp] theorem determinantCocycle_apply (A : Matrix.GeneralLinearGroup n R) (x : PUnit) :
    determinantCocycle (n := n) (R := R) A x = Matrix.GeneralLinearGroup.det A := rfl

/-- Determinant cocycle chain rule on `GL(n,R)`. -/
theorem determinantCocycle_chain_rule (A B : Matrix.GeneralLinearGroup n R) :
    determinantCocycle (n := n) (R := R) (A * B) PUnit.unit =
      determinantCocycle (n := n) (R := R) A PUnit.unit *
        determinantCocycle (n := n) (R := R) B PUnit.unit := by
  simp [determinantCocycle, groupHomAsMulActionCocycle]

end Determinant

/-! ## Scalar RN bridge as logarithmic additive cocycle -/

section RN

variable {A : Type*} [Group A]

/--
A scalar Radon-Nikodym bridge is an additive action cocycle over the trivial
base.
-/
noncomputable def rnBridgeAsAdditiveCocycle (B : HasScalarRNBridge A) :
    AddActionCocycle A PUnit.{1} ℝ where
  toFun a _ := B.rn a
  map_one := by
    intro x
    simp [HasScalarRNBridge.rn, scalarRN]
  map_mul := by
    intro a b x
    exact B.rn_chain_rule a b

/-- The RN bridge chain rule in additive cocycle form. -/
theorem rnBridgeAsAdditiveCocycle_chain_rule (B : HasScalarRNBridge A) (a b : A) :
    rnBridgeAsAdditiveCocycle B (a * b) PUnit.unit =
      rnBridgeAsAdditiveCocycle B a PUnit.unit +
        rnBridgeAsAdditiveCocycle B b PUnit.unit := by
  exact B.rn_chain_rule a b

end RN

/-! ## Connes cocycle as twisted noncommutative cocycle -/

section Connes

open InfoGeometry.Volume.ConnesCocycle

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Existing Connes cocycles are exactly twisted additive-time cocycles. -/
theorem connesCocycle_is_twisted_additive_time_cocycle
    (σ : AdditiveModularFlow (H := H)) (u : ℝ -> AlgebraEnd H) :
    IsConnesCocycle σ u ↔ ∀ s t : ℝ, u (s + t) = u s * σ s (u t) := Iff.rfl

/-- A modular automorphism flow preserves multiplication at each time. -/
theorem modularFlow_preserves_mul
    (σ : AdditiveModularFlow (H := H)) (t : ℝ) (A B : AlgebraEnd H) :
    σ t (A * B) = σ t A * σ t B := by
  exact (σ t).map_mul A B

end Connes

/-! ## Higher cocycles as anomaly/cohomology classes -/

section HigherCocycles

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]

/--
The multiplicative `2`-cocycle identity is the higher chain rule
controlling projective multipliers and central-extension anomalies.
-/
theorem multiplicative_two_cocycle_chain_rule {ω : G × G -> M}
    (hω : groupCohomology.IsMulCocycle₂ ω) (g h j : G) :
    ω (g * h, j) * ω (g, h) = g • ω (h, j) * ω (g, h * j) :=
  hω g h j

/--
A mathlib multiplicative `2`-cocycle determines a canonical `H²` class.

This is the precise cohomological target for the statement that an anomaly is
a nontrivial higher cocycle.
-/
noncomputable def multiplicativeTwoCocycleClass {ω : G × G -> M}
    (hω : groupCohomology.IsMulCocycle₂ ω) :
    groupCohomology.H2 (Rep.ofMulDistribMulAction G M) :=
  groupCohomology.H2π (Rep.ofMulDistribMulAction G M)
    (groupCohomology.cocyclesOfIsMulCocycle₂ hω)

/--
The `H²` class of a multiplicative `2`-cocycle vanishes exactly when the
cocycle is a multiplicative coboundary.

This formalizes the normalization/anomaly split:
removable defects are coboundaries; nonzero classes are genuine anomalies.
-/
theorem multiplicativeTwoCocycleClass_eq_zero_iff_isCoboundary {ω : G × G -> M}
    (hω : groupCohomology.IsMulCocycle₂ ω) :
    multiplicativeTwoCocycleClass hω = 0 ↔
      groupCohomology.IsMulCoboundary₂ ω := by
  constructor
  · intro h
    have hm :
        ⇑(groupCohomology.cocyclesOfIsMulCocycle₂ hω) ∈
          groupCohomology.coboundaries₂ (Rep.ofMulDistribMulAction G M) :=
      (groupCohomology.H2π_eq_zero_iff
        (A := Rep.ofMulDistribMulAction G M)
        (x := groupCohomology.cocyclesOfIsMulCocycle₂ hω)).mp h
    exact groupCohomology.isMulCoboundary₂_of_mem_coboundaries₂ (f := ω) hm
  · intro h
    refine (groupCohomology.H2π_eq_zero_iff
      (A := Rep.ofMulDistribMulAction G M)
      (x := groupCohomology.cocyclesOfIsMulCocycle₂ hω)).mpr ?_
    simpa using
      (groupCohomology.coboundariesOfIsMulCoboundary₂ (f := ω) h).2

end HigherCocycles

/-! ## Projective multipliers as central-extension 2-cocycles -/

section ProjectiveMultipliers

variable {K G V : Type} [Group G] [Field K] [AddCommGroup V] [Module K V]

local instance : MulDistribMulAction G Kˣ where
  smul := fun _ x => x
  mul_smul := by
    intro g h x
    rfl
  one_smul := by
    intro x
    rfl
  smul_mul := by
    intro g x y
    rfl
  smul_one := by
    intro g
    rfl

/--
The scalar multiplier of a projective representation is the canonical
mathlib multiplicative `2`-cocycle.

This is the owner-file bridge from projective/central-extension language to
the `H²` cocycle calculus above.
-/
theorem projectiveMultiplier_is_mathlib_two_cocycle
    (P : ProjectiveRepresentation K G V) :
    groupCohomology.IsMulCocycle₂
      (fun p : G × G => P.multiplier p.1 p.2) :=
  P.multiplier_isMulCocycle₂

/-- The projective multiplier defines the same canonical `H²` class. -/
noncomputable def projectiveMultiplierClass
    (P : ProjectiveRepresentation K G V) :
    groupCohomology.H2 (Rep.ofMulDistribMulAction G Kˣ) :=
  P.multiplierClass (G := G) (K := K) (V := V)

/--
The projective anomaly vanishes exactly when the multiplier is a
multiplicative coboundary.
-/
theorem projectiveMultiplierClass_eq_zero_iff_isCoboundary
    (P : ProjectiveRepresentation K G V) :
    projectiveMultiplierClass (G := G) (K := K) (V := V) P = 0 ↔
      groupCohomology.IsMulCoboundary₂
        (f := fun p : G × G => P.multiplier p.1 p.2) := by
  simpa [projectiveMultiplierClass] using
    (P.multiplierClass_eq_zero_iff_isMulCoboundary₂
      (G := G) (K := K) (V := V))

/--
Equivalently, the projective anomaly vanishes exactly when the attached
central extension splits.
-/
theorem projectiveMultiplierClass_eq_zero_iff_centralExtension_splits
    (P : ProjectiveRepresentation K G V) :
    projectiveMultiplierClass (G := G) (K := K) (V := V) P = 0 ↔
      ∃ s : G →* P.centralExtension,
        Function.RightInverse s (ProjectiveRepresentation.centralExtension.proj (P := P)) := by
  simpa [projectiveMultiplierClass] using
    (ProjectiveRepresentation.centralExtension.multiplierClass_eq_zero_iff_exists_splitSection
      (P := P))

end ProjectiveMultipliers

end InfoGeometry.Volume.FunctorialCocycleCalculus
