import InfoGeometry.Cocycle.ActionCocycle
import InfoGeometry.Cocycle.LogCocycle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Logarithmic Order Parameters

This module isolates the scalar/logarithmic shadow of positive density
cocycles.

The noncommutative Connes cocycle is not identified with a scalar field here.
Instead, this file formalizes the common scalar mechanism:

* a multiplicative density cocycle gives a chain rule;
* `log |ρ|` is the additive logarithmic cocycle;
* `-log |ρ|` is the additive surprisal/modular-Hamiltonian convention;
* a Weyl order parameter is the normalized logarithmic density.

The current layer remains an `H²`/normal-ordering construction; this file owns
only the `H¹` density/Jacobian/Radon--Nikodym/Weyl side.
-/

noncomputable section

namespace InfoGeometry.Cocycle

open CategoryTheory
open InfoGeometry.Canonical.Algebraic

/-! ## Compatibility name for explicit twisted multiplicative cocycles -/

/--
Compatibility alias for the explicit-action multiplicative cocycle
`c (g*h) = c g * α g (c h)`.

The implementation is the existing repo canonical `TwistedGroupCocycle`; this
name matches the mathematical "multiplicative density cocycle" terminology.
-/
abbrev MultiplicativeCocycle (G U : Type*) [Group G] [Group U]
    (α : G →* MulAut U) :=
  TwistedGroupCocycle G U α

/-! ## Category/groupoid scalar unit cocycles -/

universe u

section Category

variable {Ω : Type u} [Category Ω]

/--
The scalar logarithmic density `log |ρ|` of a constant-coefficient
category/groupoid real-unit cocycle.
-/
def categoryLogAbsDensity
    (C : CategoryMultiplicativeCocycle Ω ℝˣ)
    {X Y : Ω} (f : X ⟶ Y) : ℝ :=
  Real.log |((show ℝˣ from C.map f) : ℝ)|

/--
The negative logarithm of a constant-coefficient category/groupoid real-unit
cocycle.
-/
def categoryNegativeLogDensity
    (C : CategoryMultiplicativeCocycle Ω ℝˣ)
    {X Y : Ω} (f : X ⟶ Y) : ℝ :=
  -categoryLogAbsDensity C f

@[simp]
theorem categoryNegativeLogDensity_apply
    (C : CategoryMultiplicativeCocycle Ω ℝˣ)
    {X Y : Ω} (f : X ⟶ Y) :
    categoryNegativeLogDensity C f = -categoryLogAbsDensity C f :=
  rfl

/--
The constant-coefficient category/groupoid negative-log density chain rule.

Mathlib's `SingleObj` convention gives
`C.map (f ≫ g) = C.map g * C.map f`; the target is additive and commutative,
so the logarithmic chain rule is stated in the usual `f` then `g` order.
-/
theorem categoryNegativeLogDensity_chain_rule
    (C : CategoryMultiplicativeCocycle Ω ℝˣ)
    {X Y Z : Ω} (f : X ⟶ Y) (g : Y ⟶ Z) :
    categoryNegativeLogDensity C (f ≫ g) =
      categoryNegativeLogDensity C f + categoryNegativeLogDensity C g := by
  unfold categoryNegativeLogDensity categoryLogAbsDensity
  rw [categoryMultiplicativeCocycle_chain_rule C f g]
  change
    -Real.log |(((show ℝˣ from C.map g) : ℝ) * ((show ℝˣ from C.map f) : ℝ))| =
      -Real.log |((show ℝˣ from C.map f) : ℝ)| +
        -Real.log |((show ℝˣ from C.map g) : ℝ)|
  rw [abs_mul]
  have hg : |((show ℝˣ from C.map g) : ℝ)| ≠ 0 := by
    exact abs_ne_zero.mpr (Units.ne_zero (show ℝˣ from C.map g))
  have hf : |((show ℝˣ from C.map f) : ℝ)| ≠ 0 := by
    exact abs_ne_zero.mpr (Units.ne_zero (show ℝˣ from C.map f))
  rw [Real.log_mul hg hf]
  ring

end Category

/-! ## Negative logarithm of scalar unit cocycles -/

variable {Γ X : Type*} [Group Γ] [MulAction Γ X]

/-! ## Positive scalar density cocycles -/

/--
Abstract positive multiplicative density cocycle.

This is the bare `H¹` transport carrier behind Jacobians, Radon-Nikodym
densities, Weyl scaling, and modular time.  The multiplicative law is the
input; the logarithmic potential is the additive output.
-/
structure PositiveMultiplicativeCocycle (G : Type*) [Group G] where
  c : G → ℝ
  pos : ∀ g, 0 < c g
  mul : ∀ g h, c (g * h) = c g * c h

namespace PositiveMultiplicativeCocycle

variable {G : Type*} [Group G]

/-- The negative logarithmic potential attached to a positive multiplicative cocycle. -/
noncomputable def logPotential (C : PositiveMultiplicativeCocycle G) : G → ℝ :=
  fun g => -Real.log (C.c g)

@[simp] theorem logPotential_apply (C : PositiveMultiplicativeCocycle G) (g : G) :
    logPotential C g = -Real.log (C.c g) :=
  rfl

/--
The additive chain rule for the logarithmic density transport.

This is the abstract version of
`c(g*h) = c(g) * c(h)  ⟹  -log c(g*h) = -log c(g) + -log c(h)`.
-/
theorem logPotential_additive
    (C : PositiveMultiplicativeCocycle G) (g h : G) :
    logPotential C (g * h) = logPotential C g + logPotential C h := by
  unfold logPotential
  rw [C.mul g h]
  rw [Real.log_mul (ne_of_gt (C.pos g)) (ne_of_gt (C.pos h))]
  ring

end PositiveMultiplicativeCocycle

/--
Pointwise negative logarithmic potential attached to a positive scalar density
readout.

This is the direct scalar formula `S = -log ρ`.
-/
def logPotential (ρ : Γ → X → ℝ) (γ : Γ) (x : X) : ℝ :=
  -Real.log (ρ γ x)

/--
The chain rule for the negative logarithm of a positive scalar density cocycle.

The property `hmul` is the transformation-space density law
`ρ (γδ) x = ρ γ (δ • x) * ρ δ x`.
-/
theorem logPotential_chain
    (ρ : Γ → X → ℝ)
    (hpos : ∀ γ x, 0 < ρ γ x)
    (hmul : ∀ γ δ x, ρ (γ * δ) x = ρ γ (δ • x) * ρ δ x)
    (γ δ : Γ) (x : X) :
    logPotential ρ (γ * δ) x =
      logPotential ρ γ (δ • x) + logPotential ρ δ x := by
  unfold logPotential
  rw [hmul]
  rw [Real.log_mul (ne_of_gt (hpos γ (δ • x))) (ne_of_gt (hpos δ x))]
  ring

/-- The scalar logarithmic density extracted from a real-unit action cocycle. -/
def logAbsDensityOfUnits (C : MulActionCocycle Γ X ℝˣ) (γ : Γ) (x : X) : ℝ :=
  Real.log |((C γ x : ℝˣ) : ℝ)|

/-- The scalar surprisal / negative-log-density extracted from a unit cocycle. -/
def negativeLogDensityOfUnitsFun (C : MulActionCocycle Γ X ℝˣ)
    (γ : Γ) (x : X) : ℝ :=
  -logAbsDensityOfUnits C γ x

/--
Taking `-log |-|` of a real-unit action cocycle gives an additive action
cocycle. This is the scalar version of passing from multiplicative density
transport to additive surprisal/modular Hamiltonian transport.
-/
def negativeLogDensityOfUnits (C : MulActionCocycle Γ X ℝˣ) :
    AddActionCocycle Γ X ℝ where
  toFun γ x := negativeLogDensityOfUnitsFun C γ x
  map_one := by
    intro x
    unfold negativeLogDensityOfUnitsFun logAbsDensityOfUnits
    rw [C.map_one x]
    simp
  map_mul := by
    intro γ δ x
    unfold negativeLogDensityOfUnitsFun logAbsDensityOfUnits
    rw [C.map_mul]
    simp only [Units.val_mul]
    rw [abs_mul]
    have hγ : |((C γ (δ • x) : ℝˣ) : ℝ)| ≠ 0 := by
      exact abs_ne_zero.mpr (Units.ne_zero (C γ (δ • x)))
    have hδ : |((C δ x : ℝˣ) : ℝ)| ≠ 0 := by
      exact abs_ne_zero.mpr (Units.ne_zero (C δ x))
    rw [Real.log_mul hγ hδ]
    ring

@[simp]
theorem negativeLogDensityOfUnits_apply (C : MulActionCocycle Γ X ℝˣ)
    (γ : Γ) (x : X) :
    negativeLogDensityOfUnits C γ x = -logAbsDensityOfUnits C γ x :=
  rfl

/-- The negative-log density chain rule. -/
theorem negativeLogDensityOfUnits_chain_rule (C : MulActionCocycle Γ X ℝˣ)
    (γ δ : Γ) (x : X) :
    negativeLogDensityOfUnits C (γ * δ) x =
      negativeLogDensityOfUnits C γ (δ • x) + negativeLogDensityOfUnits C δ x :=
  AddActionCocycle.chain_rule (negativeLogDensityOfUnits C) γ δ x

/-! ## Weyl scalar as normalized logarithmic density -/

/--
The scalar Weyl order parameter extracted from a density cocycle in dimension
`n`: `φ = (1/n) log |ρ|`.
-/
def weylOrderParameterOfUnits (n : ℝ) (C : MulActionCocycle Γ X ℝˣ)
    (γ : Γ) (x : X) : ℝ :=
  logAbsDensityOfUnits C γ x / n

theorem dim_mul_weylOrderParameterOfUnits_eq_logAbsDensity
    (n : ℝ) (hn : n ≠ 0) (C : MulActionCocycle Γ X ℝˣ)
    (γ : Γ) (x : X) :
    n * weylOrderParameterOfUnits n C γ x = logAbsDensityOfUnits C γ x := by
  unfold weylOrderParameterOfUnits
  field_simp [hn]

theorem negativeLogDensity_eq_neg_dim_mul_weylOrderParameterOfUnits
    (n : ℝ) (hn : n ≠ 0) (C : MulActionCocycle Γ X ℝˣ)
    (γ : Γ) (x : X) :
    negativeLogDensityOfUnits C γ x =
      -n * weylOrderParameterOfUnits n C γ x := by
  rw [negativeLogDensityOfUnits_apply]
  rw [← dim_mul_weylOrderParameterOfUnits_eq_logAbsDensity n hn C γ x]
  ring

/--
Named synthesis theorem: the Weyl order parameter is the normalized
logarithmic representative of the density cocycle, equivalently the negative
surprisal divided by dimension.
-/
theorem weylOrderParameter_eq_negative_log_density_cocycle
    (n : ℝ) (C : MulActionCocycle Γ X ℝˣ)
    (γ : Γ) (x : X) :
    weylOrderParameterOfUnits n C γ x =
      -(negativeLogDensityOfUnits C γ x) / n := by
  rw [negativeLogDensityOfUnits_apply]
  unfold weylOrderParameterOfUnits
  ring

/-- Weyl volume density for a scalar Weyl field `φ` in dimension `n`. -/
def weylVolumeDensity (n : ℕ) (φ : X → ℝ) (x : X) : ℝ :=
  Real.exp ((n : ℝ) * φ x)

/--
The Weyl volume logarithm is `nφ`, i.e.
`dvol_{e^{2φ}g} / dvol_g = e^{nφ}` has logarithmic representative `nφ`.
-/
theorem weyl_volume_log_cocycle (n : ℕ) (φ : X → ℝ) (x : X) :
    Real.log (weylVolumeDensity n φ x) = (n : ℝ) * φ x := by
  simp [weylVolumeDensity]

/--
Finite scalar Weyl-volume scaling packet.

This is the Lean-local form of
`dvol_{e^{2χ}g} / dvol_g = exp(nχ)`.  It records only the scalar density
readout; a concrete metric/volume-form construction must live in a geometry
module.
-/
structure WeylVolumeScaling where
  dim : ℕ
  chi : ℝ
  volumeScale : ℝ
  volumeScale_eq : volumeScale = Real.exp ((dim : ℝ) * chi)

namespace WeylVolumeScaling

/-- Logarithmic Weyl density readout `log(volumeScale)`. -/
def weylLogDensity (W : WeylVolumeScaling) : ℝ :=
  Real.log W.volumeScale

/-- The logarithmic Weyl density of `exp(nχ)` is `nχ`. -/
theorem weylLogDensity_eq_dim_mul_chi (W : WeylVolumeScaling) :
    W.weylLogDensity = (W.dim : ℝ) * W.chi := by
  unfold weylLogDensity
  rw [W.volumeScale_eq]
  rw [Real.log_exp]

/-- In nonzero dimension, the Weyl scalar is the normalized logarithmic density. -/
theorem chi_eq_weylLogDensity_div_dim
    (W : WeylVolumeScaling) (hdim : (W.dim : ℝ) ≠ 0) :
    W.chi = W.weylLogDensity / (W.dim : ℝ) := by
  rw [W.weylLogDensity_eq_dim_mul_chi]
  field_simp [hdim]

end WeylVolumeScaling

/-! ## Reference-over-transport sign convention -/

/--
If `ρ` is the transported-over-reference density, then
`referenceOverTransportDensity ρ` is the reciprocal convention
`c = reference / transported`.
-/
def referenceOverTransportDensity (ρ : Γ → X → ℝ) : Γ → X → ℝ :=
  fun γ x => (ρ γ x)⁻¹

/--
The logarithmic density transport attached to the reciprocal convention
`c = reference / transported`: `ℓ = -log c`.
-/
def logarithmicDensityTransport (c : Γ → X → ℝ) (γ : Γ) (x : X) : ℝ :=
  -Real.log (c γ x)

/--
For reciprocal conventions, `ℓ = -log(reference/transported)` is the positive
logarithm of the transported-over-reference density.
-/
theorem logarithmicDensityTransport_eq_log_transportedOverReference
    {Γ₀ X₀ : Type*} {γ : Γ₀} {x : X₀} (ρ : Γ₀ → X₀ → ℝ) :
    logarithmicDensityTransport (referenceOverTransportDensity ρ) γ x =
      Real.log (ρ γ x) := by
  unfold logarithmicDensityTransport referenceOverTransportDensity
  rw [Real.log_inv (ρ γ x)]
  ring

/--
Reference-over-transport Weyl density.  With the convention
`cχ = dvol_g / dvol_{e^{2χ}g}`, one has `cχ = exp(-nχ)`.
-/
def weylReferenceOverTransportDensity (n : ℕ) (χ : X → ℝ) (x : X) : ℝ :=
  Real.exp (-(n : ℝ) * χ x)

/--
With `cχ = dvol_g / dvol_{e^{2χ}g}`, the logarithmic density transport is
`ℓχ = -log cχ = nχ`.
-/
theorem weyl_logarithmicDensityTransport_referenceOverTransport
    {Γ₀ X₀ : Type*} [Group Γ₀] (n : ℕ) (χ : X₀ → ℝ) (x : X₀) :
    logarithmicDensityTransport (fun _ x => weylReferenceOverTransportDensity n χ x)
        (1 : Γ₀) x =
      (n : ℝ) * χ x := by
  unfold logarithmicDensityTransport weylReferenceOverTransportDensity
  simp

/--
With the transported-over-reference convention
`dvol_{e^{2χ}g} / dvol_g = exp(nχ)`, the negative-log potential has the
opposite sign.
-/
theorem weyl_logPotential_transportedOverReference
    {Γ₀ X₀ : Type*} (n : ℕ) (χ : X₀ → ℝ) (γ : Γ₀) (x : X₀) :
    logPotential (fun _ x => weylVolumeDensity n χ x) γ x =
      -((n : ℝ) * χ x) := by
  unfold logPotential weylVolumeDensity
  simp

/-! ## Kähler/Gromov--Witten logarithmic weight shadows -/

/--
Schematic A-model/Gromov--Witten curve weight
`q^β = exp(-<t,β>)`, represented by its scalar action readout.
-/
def kahlerCurveWeight (action : ℝ) : ℝ :=
  Real.exp (-action)

/-- The negative logarithm of the curve weight recovers the additive Kähler action. -/
theorem negativeLog_kahlerCurveWeight (action : ℝ) :
    -Real.log (kahlerCurveWeight action) = action := by
  unfold kahlerCurveWeight
  simp

/--
Uniform Weyl scaling of a Kähler area readout:
`areaχ = exp(2χ) area`.
-/
def scaledKahlerArea (χ area : ℝ) : ℝ :=
  Real.exp (2 * χ) * area

@[simp]
theorem scaledKahlerArea_zero (area : ℝ) :
    scaledKahlerArea 0 area = area := by
  simp [scaledKahlerArea]

/--
The logarithmic scale response of a positive Kähler area under
`ωχ = exp(2χ)ω` is additive: `log areaχ = 2χ + log area`.
-/
theorem log_scaledKahlerArea_of_pos
    (χ area : ℝ) (harea : 0 < area) :
    Real.log (scaledKahlerArea χ area) = 2 * χ + Real.log area := by
  unfold scaledKahlerArea
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt harea)]
  rw [Real.log_exp]

/--
The scaled curve weight is again an exponential geometric weight; taking
`-log` recovers the scaled Kähler area/action.
-/
theorem negativeLog_kahlerCurveWeight_scaledArea
    (χ area : ℝ) :
    -Real.log (kahlerCurveWeight (scaledKahlerArea χ area)) =
      scaledKahlerArea χ area :=
  negativeLog_kahlerCurveWeight (scaledKahlerArea χ area)

/-- Logarithmic moduli-volume/free-energy potential `F = log Z`. -/
def logarithmicVolumePotential (Z : ℝ) : ℝ :=
  Real.log Z

/-- Compatibility name for Gromov--Witten/topological-string free energy. -/
abbrev gromovWittenFreeEnergy (Z_GW : ℝ) : ℝ :=
  logarithmicVolumePotential Z_GW

@[simp]
theorem gromovWittenFreeEnergy_eq_log (Z_GW : ℝ) :
    gromovWittenFreeEnergy Z_GW = Real.log Z_GW :=
  rfl

/-- Uniform length scaling used for scalar Weil--Petersson volume responses. -/
def uniformLengthScale (χ L : ℝ) : ℝ :=
  Real.exp χ * L

@[simp]
theorem uniformLengthScale_zero (L : ℝ) :
    uniformLengthScale 0 L = L := by
  simp [uniformLengthScale]

/--
For a positive length parameter, uniform scaling turns multiplicative length
transport into an additive logarithmic response.
-/
theorem log_uniformLengthScale_of_pos
    (χ L : ℝ) (hL : 0 < L) :
    Real.log (uniformLengthScale χ L) = χ + Real.log L := by
  unfold uniformLengthScale
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hL)]
  rw [Real.log_exp]

/-! ## Abstract GW partition-weight interface -/

/-!
The GW partition-weight lane is exactly the existing positive multiplicative
cocycle owner.  No additional semantic marker is needed: positivity and the
multiplicative law are the mathematical content of the interface.
-/
abbrev GWPartitionWeight (G : Type*) [Group G] :=
  PositiveMultiplicativeCocycle G

namespace GWPartitionWeight

variable {G : Type*} [Group G]

/--
GW free-energy/surprisal convention attached to a positive partition weight:
`F = -log Z`.
-/
noncomputable def gwFreeEnergy (Z : GWPartitionWeight G) : G → ℝ :=
  PositiveMultiplicativeCocycle.logPotential Z

@[simp]
theorem gwFreeEnergy_apply (Z : GWPartitionWeight G) (g : G) :
    gwFreeEnergy Z g = -Real.log (Z.c g) :=
  rfl

/-- Multiplicativity of the partition weight gives additivity of `-log Z`. -/
theorem gwFreeEnergy_additive (Z : GWPartitionWeight G) (g h : G) :
    gwFreeEnergy Z (g * h) = gwFreeEnergy Z g + gwFreeEnergy Z h :=
  PositiveMultiplicativeCocycle.logPotential_additive
    Z g h

/--
If a proposed Weyl scalar/order-parameter readout is definitionally tied to
the GW free-energy convention, then it is exactly the negative logarithm of the
positive partition weight.
-/
theorem weylScalar_eq_gw_surprisal
    (Z : GWPartitionWeight G) (phi : G → ℝ)
    (hphi : ∀ g, phi g = gwFreeEnergy Z g) (g : G) :
    phi g = -Real.log (Z.c g) := by
  rw [hphi g]
  rfl

end GWPartitionWeight

/-! ## Scalar modular Hamiltonian and finite log-barrier shadows -/

/--
Scalar commutative shadow of the modular Hamiltonian convention `K = -log Δ`.

This is deliberately a scalar readout.  A genuine operator logarithm or Connes
relative modular operator must be supplied by a separate operator-algebraic
module.
-/
def scalarModularHamiltonian (Δ : X → ℝ) (x : X) : ℝ :=
  -Real.log (Δ x)

/-- Compatibility name for the scalar modular Hamiltonian shadow. -/
abbrev modularHamiltonian (Δ : X → ℝ) (x : X) : ℝ :=
  scalarModularHamiltonian Δ x

@[simp]
theorem scalarModularHamiltonian_eq_negativeLog (Δ : X → ℝ) (x : X) :
    scalarModularHamiltonian Δ x = -Real.log (Δ x) :=
  rfl

/-- Log-generating identity: the modular Hamiltonian of a product is additive. -/
theorem scalarModularHamiltonian_mul (Δ₁ Δ₂ : X → ℝ)
    (h₁ : ∀ x, 0 < Δ₁ x) (h₂ : ∀ x, 0 < Δ₂ x) (x : X) :
    scalarModularHamiltonian (fun x => Δ₁ x * Δ₂ x) x =
      scalarModularHamiltonian Δ₁ x + scalarModularHamiltonian Δ₂ x := by
  unfold scalarModularHamiltonian
  rw [Real.log_mul (ne_of_gt (h₁ x)) (ne_of_gt (h₂ x))]
  ring

/-- Log-generating identity: the modular Hamiltonian of an inverse flips sign. -/
theorem scalarModularHamiltonian_inv (Δ : X → ℝ) (x : X) :
    scalarModularHamiltonian (fun x => (Δ x)⁻¹) x =
      -scalarModularHamiltonian Δ x := by
  unfold scalarModularHamiltonian
  simp [Real.log_inv]

/--
Finite determinant/log-barrier shadow: `B(A) = -log |det(A)|`.

The determinant readout is supplied abstractly so this theorem can be reused for
matrices, Jacobians, and regularized determinant proxies.
-/
def logdetBarrier {A : Type*} (detReadout : A → ℝ) (a : A) : ℝ :=
  -Real.log |detReadout a|

/-- Multiplicativity of the determinant readout makes the log-barrier additive. -/
theorem logdetBarrier_mul_of_det_mul {A : Type*} [Mul A]
    (detReadout : A → ℝ)
    (hmul : ∀ a b : A, detReadout (a * b) = detReadout a * detReadout b)
    (hne : ∀ a : A, detReadout a ≠ 0) (a b : A) :
    logdetBarrier detReadout (a * b) =
      logdetBarrier detReadout a + logdetBarrier detReadout b := by
  unfold logdetBarrier
  rw [hmul, abs_mul]
  rw [Real.log_mul (abs_ne_zero.mpr (hne a)) (abs_ne_zero.mpr (hne b))]
  ring

section MatrixBarrier

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- Matrix log-det barrier `B(X) = -log |det X|`. -/
def matrixLogdetBarrier (X : Matrix ι ι ℝ) : ℝ :=
  logdetBarrier Matrix.det X

/-- The identity matrix has zero finite deformation entropy. -/
@[simp]
theorem matrixLogdetBarrier_one :
    matrixLogdetBarrier (1 : Matrix ι ι ℝ) = 0 := by
  simp [matrixLogdetBarrier, logdetBarrier]

/--
Finite deformation entropy is additive under composition of nonsingular
linear deformations.
-/
theorem matrixLogdetBarrier_mul
    (A B : Matrix ι ι ℝ)
    (hA : A.det ≠ 0)
    (hB : B.det ≠ 0) :
    matrixLogdetBarrier (A * B) =
      matrixLogdetBarrier A + matrixLogdetBarrier B := by
  unfold matrixLogdetBarrier logdetBarrier
  rw [Matrix.det_mul, abs_mul,
    Real.log_mul (abs_ne_zero.mpr hA) (abs_ne_zero.mpr hB)]
  ring

/-- A volume-preserving deformation has zero finite deformation entropy. -/
theorem matrixLogdetBarrier_eq_zero_of_abs_det_eq_one
    (J : Matrix ι ι ℝ)
    (hJ : |J.det| = 1) :
    matrixLogdetBarrier J = 0 := by
  simp [matrixLogdetBarrier, logdetBarrier, hJ]

/--
On the orientation-preserving stratum, deformation entropy is the ordinary
negative logarithm of the determinant.
-/
theorem matrixLogdetBarrier_eq_neg_log_det_of_det_pos
    (J : Matrix ι ι ℝ)
    (hJ : 0 < J.det) :
    matrixLogdetBarrier J = -Real.log J.det := by
  rw [matrixLogdetBarrier, logdetBarrier, abs_of_pos hJ]

/--
A nonsingular volume-compressing deformation has nonnegative finite
deformation entropy.
-/
theorem matrixLogdetBarrier_nonneg_of_abs_det_le_one
    (J : Matrix ι ι ℝ)
    (hJ₀ : J.det ≠ 0)
    (hJ₁ : |J.det| ≤ 1) :
    0 ≤ matrixLogdetBarrier J := by
  unfold matrixLogdetBarrier logdetBarrier
  exact neg_nonneg.mpr
    (Real.log_nonpos (abs_pos.mpr hJ₀).le hJ₁)

/--
A volume-expanding deformation has nonpositive finite deformation entropy.
-/
theorem matrixLogdetBarrier_nonpos_of_one_le_abs_det
    (J : Matrix ι ι ℝ)
    (hJ : 1 ≤ |J.det|) :
    matrixLogdetBarrier J ≤ 0 := by
  unfold matrixLogdetBarrier logdetBarrier
  exact neg_nonpos.mpr (Real.log_nonneg hJ)

/--
Congruence transformation law for the finite log-det barrier:
`B(A X Aᵀ) = B(X) - 2 log |det A|`.
-/
theorem matrixLogdetBarrier_congruence (A X : Matrix ι ι ℝ)
    (hA : A.det ≠ 0) (hX : X.det ≠ 0) :
    matrixLogdetBarrier (A * X * Matrix.transpose A) =
      matrixLogdetBarrier X - 2 * Real.log |A.det| := by
  unfold matrixLogdetBarrier logdetBarrier
  have hAt : (Matrix.transpose A).det = A.det := by
    simp
  have hAabs : |A.det| ≠ 0 := abs_ne_zero.mpr hA
  have hXabs : |X.det| ≠ 0 := abs_ne_zero.mpr hX
  rw [Matrix.det_mul, Matrix.det_mul, hAt, abs_mul, abs_mul]
  rw [mul_assoc]
  rw [Real.log_mul hAabs (mul_ne_zero hXabs hAabs)]
  rw [Real.log_mul hXabs hAabs]
  ring_nf

end MatrixBarrier

/--
Summary theorem for the scalar layer: negative-log unit density, Weyl order
parameter, scalar modular Hamiltonian, and log-det barrier are all the same
`-log` construction after choosing the corresponding density readout.
-/
theorem logarithmicCocycle_unifies_volume_entropy_modularGenerator
    {A : Type*} (n : ℝ) (hn : n ≠ 0)
    (C : MulActionCocycle Γ X ℝˣ) (γ : Γ) (x : X)
    (Δ : X → ℝ) (detReadout : A → ℝ) (a : A) :
    negativeLogDensityOfUnits C γ x = -logAbsDensityOfUnits C γ x ∧
      n * weylOrderParameterOfUnits n C γ x = logAbsDensityOfUnits C γ x ∧
      scalarModularHamiltonian Δ x = -Real.log (Δ x) ∧
      logdetBarrier detReadout a = -Real.log |detReadout a| := by
  exact ⟨negativeLogDensityOfUnits_apply C γ x,
    dim_mul_weylOrderParameterOfUnits_eq_logAbsDensity n hn C γ x,
    scalarModularHamiltonian_eq_negativeLog Δ x,
    rfl⟩

end InfoGeometry.Cocycle
