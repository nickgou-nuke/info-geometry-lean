import InfoGeometry.Canonical.Algebraic.ModularRotorCocycle
import InfoGeometry.Canonical.ProjectiveFoundation
import InfoGeometry.Volume.RadonNikodym
import InfoGeometry.Volume.ConnesCocycle
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-!
# Functorial Cocycle Calculus

This module collects the mathlib-backed algebraic substrate common to
determinants, logarithmic Radon-Nikodym characters, action cocycles,
Connes-style twisted cocycles, and infinitesimal commutator derivations.

The intentionally proved layer is algebraic:

* multiplicative cocycles for coefficient actions;
* additive logarithmic cocycles for coefficient actions;
* action cocycles over a transformation space;
* coboundaries as canonical trivial cocycles;
* determinant as a `MulActionCocycle` over the trivial base;
* scalar RN bridges as additive cocycles;
* commutator/derivation Leibniz rules;
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
open InfoGeometry.Volume.RadonNikodym

/-! ## Coefficient-action 1-cocycles -/

/--
A multiplicative 1-cocycle for a monoid action on coefficient units.

The law is the abstract chain rule `c (g*h) = c g * g • c h`.
-/
structure MultiplicativeOneCocycle (G U : Type*) [Monoid G] [Group U]
    [MulDistribMulAction G U] where
  toFun : G -> U
  map_one : toFun 1 = 1
  map_mul : forall g h : G, toFun (g * h) = toFun g * g • toFun h

instance {G U : Type*} [Monoid G] [Group U] [MulDistribMulAction G U] :
    CoeFun (MultiplicativeOneCocycle G U) (fun _ => G -> U) where
  coe := MultiplicativeOneCocycle.toFun

namespace MultiplicativeOneCocycle

variable {G U : Type*} [Monoid G] [Group U] [MulDistribMulAction G U]

@[simp] theorem map_one_apply (C : MultiplicativeOneCocycle G U) : C 1 = 1 :=
  C.map_one

/-- The multiplicative cocycle chain rule. -/
theorem chain_rule (C : MultiplicativeOneCocycle G U) (g h : G) :
    C (g * h) = C g * g • C h :=
  C.map_mul g h

/--
The canonical multiplicative coboundary `b⁻¹ * g • b`.

This is the algebraic form of changing normalization/trivialization.
-/
def coboundary (b : U) : MultiplicativeOneCocycle G U where
  toFun g := b⁻¹ * g • b
  map_one := by simp
  map_mul := by
    intro g h
    simp [mul_smul, mul_assoc]

end MultiplicativeOneCocycle

/--
An additive 1-cocycle for a monoid action on additive coefficients.

The law is the logarithmic chain rule `ℓ (g*h) = ℓ g + g • ℓ h`.
-/
structure AdditiveOneCocycle (G V : Type*) [Monoid G] [AddGroup V]
    [DistribMulAction G V] where
  toFun : G -> V
  map_one : toFun 1 = 0
  map_mul : forall g h : G, toFun (g * h) = toFun g + g • toFun h

instance {G V : Type*} [Monoid G] [AddGroup V] [DistribMulAction G V] :
    CoeFun (AdditiveOneCocycle G V) (fun _ => G -> V) where
  coe := AdditiveOneCocycle.toFun

namespace AdditiveOneCocycle

variable {G V : Type*} [Monoid G] [AddGroup V] [DistribMulAction G V]

@[simp] theorem map_one_apply (C : AdditiveOneCocycle G V) : C 1 = 0 :=
  C.map_one

/-- The additive/logarithmic cocycle chain rule. -/
theorem chain_rule (C : AdditiveOneCocycle G V) (g h : G) :
    C (g * h) = C g + g • C h :=
  C.map_mul g h

/-- The canonical additive coboundary `-B + g • B`. -/
def coboundary (B : V) : AdditiveOneCocycle G V where
  toFun g := -B + g • B
  map_one := by simp
  map_mul := by
    intro g h
    simp [mul_smul, add_assoc]

end AdditiveOneCocycle

/-! ## Transformation-space action cocycles -/

/--
An additive action cocycle over a transformation space.

The base action supplies the pullback/twist:
`L (γ*δ) x = L γ (δ • x) + L δ x`.
-/
structure AddActionCocycle (Γ X V : Type*) [Group Γ] [MulAction Γ X] [AddGroup V] where
  toFun : Γ -> X -> V
  map_one : forall x, toFun 1 x = 0
  map_mul : forall γ δ x, toFun (γ * δ) x = toFun γ (δ • x) + toFun δ x

instance {Γ X V : Type*} [Group Γ] [MulAction Γ X] [AddGroup V] :
    CoeFun (AddActionCocycle Γ X V) (fun _ => Γ -> X -> V) where
  coe := AddActionCocycle.toFun

namespace AddActionCocycle

variable {Γ X V : Type*} [Group Γ] [MulAction Γ X] [AddGroup V]

@[simp] theorem map_one_apply (C : AddActionCocycle Γ X V) (x : X) : C 1 x = 0 :=
  C.map_one x

/-- The additive action-cocycle chain rule. -/
theorem chain_rule (C : AddActionCocycle Γ X V) (γ δ : Γ) (x : X) :
    C (γ * δ) x = C γ (δ • x) + C δ x :=
  C.map_mul γ δ x

end AddActionCocycle

/-- A group homomorphism is an action cocycle over the trivial base. -/
def groupHomAsMulActionCocycle {Γ R : Type*} [Group Γ] [Group R] (φ : Γ →* R) :
    MulActionCocycle Γ PUnit R where
  toFun γ _ := φ γ
  map_one := by simp
  map_mul := by
    intro γ δ x
    simp [φ.map_mul γ δ]

@[simp] theorem groupHomAsMulActionCocycle_apply {Γ R : Type*} [Group Γ] [Group R]
    (φ : Γ →* R) (γ : Γ) (x : PUnit) :
    groupHomAsMulActionCocycle φ γ x = φ γ := rfl

namespace MulActionCocycle

variable {Γ X R : Type*} [Group Γ] [MulAction Γ X] [Group R]

/--
The canonical action-cocycle coboundary `b(γ • x) * b(x)⁻¹`.

This is the transformation-space version of changing local trivialization.
-/
def coboundary (b : X -> R) : MulActionCocycle Γ X R where
  toFun γ x := b (γ • x) * (b x)⁻¹
  map_one := by
    intro x
    simp
  map_mul := by
    intro γ δ x
    simp [mul_smul, mul_assoc]

@[simp] theorem coboundary_apply (b : X -> R) (γ : Γ) (x : X) :
    coboundary b γ x = b (γ • x) * (b x)⁻¹ := rfl

/--
Taking `log |-|` of a real-unit action cocycle gives an additive action
cocycle.
-/
noncomputable def logAbsUnits (C : MulActionCocycle Γ X ℝˣ) :
    AddActionCocycle Γ X ℝ where
  toFun γ x := Real.log |((C γ x : ℝˣ) : ℝ)|
  map_one := by
    intro x
    rw [C.map_one x]
    simp
  map_mul := by
    intro γ δ x
    rw [C.map_mul]
    simp only [Units.val_mul]
    rw [abs_mul]
    have hγ : |((C γ (δ • x) : ℝˣ) : ℝ)| ≠ 0 := by
      exact abs_ne_zero.mpr (Units.ne_zero (C γ (δ • x)))
    have hδ : |((C δ x : ℝˣ) : ℝ)| ≠ 0 := by
      exact abs_ne_zero.mpr (Units.ne_zero (C δ x))
    rw [Real.log_mul hγ hδ]

end MulActionCocycle

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
    rw [B.rn_eq_logAbs_vol]
    simp
  map_mul := by
    intro a b x
    exact rn_chain_rule B a b

/-- The RN bridge chain rule in additive cocycle form. -/
theorem rnBridgeAsAdditiveCocycle_chain_rule (B : HasScalarRNBridge A) (a b : A) :
    rnBridgeAsAdditiveCocycle B (a * b) PUnit.unit =
      rnBridgeAsAdditiveCocycle B a PUnit.unit +
        rnBridgeAsAdditiveCocycle B b PUnit.unit := by
  exact rn_chain_rule B a b

end RN

/-! ## Infinitesimal logarithms as derivations -/

section Derivation

variable {A : Type*} [Ring A]

/-- Inner commutator generator `[K,-]`. -/
def innerCommutatorDerivation (K X : A) : A := K * X - X * K

/-- The commutator generator satisfies the Leibniz rule. -/
theorem innerCommutatorDerivation_mul (K X Y : A) :
    innerCommutatorDerivation K (X * Y) =
      innerCommutatorDerivation K X * Y + X * innerCommutatorDerivation K Y := by
  unfold innerCommutatorDerivation
  noncomm_ring

end Derivation

section MathlibDerivation

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- Mathlib derivations expose the same Leibniz chain rule. -/
theorem mathlib_derivation_leibniz (D : Derivation R A A) (a b : A) :
    D (a * b) = a * D b + b * D a := by
  simp [D.leibniz a b]

end MathlibDerivation

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
