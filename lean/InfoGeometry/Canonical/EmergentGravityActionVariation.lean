import InfoGeometry.Canonical.EmergentGravity
import InfoGeometry.Canonical.StressEnergyTensor

noncomputable section

namespace InfoGeometry.Canonical.EmergentGravity

open Complex BigOperators

/-!
Finite action-variation bridge for the emergent-gravity lane.

This file stays at the algebraic shadow level owned by the repo:

* the effective action density is split into Dirac, mass, curvature, and
  torsion-norm slots;
* the torsion contribution is isolated as an explicit additive variation;
* the Belinfante-Rosenfeld tensor is re-exported as a symmetric finite readout
  through the existing stress-energy owner file.
* the modified Einstein equation is represented by a transparent finite
  residual, and the torsion-quadratic source is proved symmetric from explicit
  metric symmetry.

#### BUCKET 1: CLOSED FINITE THEOREMS
`effectiveActionVariation_zero_torsion`,
`effectiveActionVariation_torsion_split`, `belinfanteReadout_symmetric`,
`torsionQuadraticContraction_symmetric`, `torsionQuadraticSource_symmetric`,
`totalFiniteSource_symmetric`, and `modifiedEinsteinResidual_eq_zero_iff`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`torsionQuadraticSource_symmetric` depends on the explicit metric symmetry
premise `hg`.  `totalFiniteSource_symmetric` depends on explicit source
symmetry premises.

#### BUCKET 3: OPEN CLOSURE DEBT
Continuum variational calculus, tensor-density integration, Bianchi identities,
diffeomorphism invariance, covariant stress-energy conservation, Bach tensor
derivation, spinor bundle geometry, Einstein-Cartan existence/uniqueness, and
physical dynamics.

It does not derive the field equations from a continuum variational calculus.
-/

/-- Finite action-density variation packet. -/
structure EffectiveActionPacket where
  dirac : ℂ
  mass : ℂ
  curvature : ℂ
  torsionNorm : ℂ
  κInv : ℂ
  α : ℂ

/-- The finite emergent-gravity action density. -/
def effectiveActionVariation (p : EffectiveActionPacket) : ℂ :=
  p.dirac - p.mass + ((p.κInv / 2) * p.curvature) + ((p.α / 4) * p.torsionNorm)

/-- Zero torsion removes the torsion contribution from the action density. -/
theorem effectiveActionVariation_zero_torsion (p : EffectiveActionPacket) :
    effectiveActionVariation { p with torsionNorm := 0 } =
      p.dirac - p.mass + ((p.κInv / 2) * p.curvature) := by
  simp [effectiveActionVariation]

/-- The torsion part splits additively from the finite action density. -/
theorem effectiveActionVariation_torsion_split (p : EffectiveActionPacket) :
    effectiveActionVariation p =
      (p.dirac - p.mass + ((p.κInv / 2) * p.curvature)) + ((p.α / 4) * p.torsionNorm) := by
  simp [effectiveActionVariation]

/-- A finite Belinfante readout packaged from the owner tensor. -/
def belinfanteReadout {M : Type*} [AddCommGroup M] [Module ℂ M]
    (tensor : SpinorBilinearTensor M) (mu nu : ℕ) : M :=
  stress_energy_tensor tensor mu nu

/-- The finite Belinfante readout is symmetric in the two indices. -/
theorem belinfanteReadout_symmetric {M : Type*} [AddCommGroup M] [Module ℂ M]
    (tensor : SpinorBilinearTensor M) (mu nu : ℕ) :
    belinfanteReadout tensor mu nu = belinfanteReadout tensor nu mu := by
  simpa [belinfanteReadout] using stress_energy_symmetry tensor mu nu

/-! ## Finite modified-Einstein residual algebra -/

section FiniteModifiedEinstein

variable {idx : Type*}

/--
Finite contraction shadow of the quadratic torsion source:
`C_μν = Σ_ab T_μab T_νab`.
-/
def torsionQuadraticContraction [Fintype idx]
    (T : idx → idx → idx → ℂ) (mu nu : idx) : ℂ :=
  ∑ a, ∑ b, T mu a b * T nu a b

/-- The finite quadratic torsion contraction is symmetric in its free slots. -/
theorem torsionQuadraticContraction_symmetric [Fintype idx]
    (T : idx → idx → idx → ℂ) (mu nu : idx) :
    torsionQuadraticContraction T mu nu =
      torsionQuadraticContraction T nu mu := by
  simp [torsionQuadraticContraction, mul_comm]

/-- Finite scalar torsion norm shadow `Σ_μab T_μab T_μab`. -/
def torsionNormFinite [Fintype idx] (T : idx → idx → idx → ℂ) : ℂ :=
  ∑ mu, ∑ a, ∑ b, T mu a b * T mu a b

/--
Finite torsion-quadratic stress source shadow:
`Θ_μν = 2α(C_μν - 1/4 g_μν |T|²)`.
-/
def torsionQuadraticSource [Fintype idx]
    (α : ℂ) (g : idx → idx → ℂ) (T : idx → idx → idx → ℂ)
    (mu nu : idx) : ℂ :=
  (2 : ℂ) * α *
    (torsionQuadraticContraction T mu nu -
      (1 / 4 : ℂ) * g mu nu * torsionNormFinite T)

/--
The finite torsion-quadratic stress source is symmetric once the metric readout
is explicitly symmetric.
-/
theorem torsionQuadraticSource_symmetric [Fintype idx]
    (α : ℂ) (g : idx → idx → ℂ) (T : idx → idx → idx → ℂ)
    (hg : ∀ mu nu, g mu nu = g nu mu) (mu nu : idx) :
    torsionQuadraticSource α g T mu nu =
      torsionQuadraticSource α g T nu mu := by
  simp [torsionQuadraticSource, torsionQuadraticContraction_symmetric, hg mu nu]

/-- Total finite source `Stress + Θ`. -/
def totalFiniteSource (Stress Theta : idx → idx → ℂ) (mu nu : idx) : ℂ :=
  Stress mu nu + Theta mu nu

/-- The total finite source is symmetric if both summands are symmetric. -/
theorem totalFiniteSource_symmetric
    (Stress Theta : idx → idx → ℂ)
    (hS : ∀ mu nu, Stress mu nu = Stress nu mu)
    (hT : ∀ mu nu, Theta mu nu = Theta nu mu) (mu nu : idx) :
    totalFiniteSource Stress Theta mu nu =
      totalFiniteSource Stress Theta nu mu := by
  simp [totalFiniteSource, hS mu nu, hT mu nu]

/--
Finite modified-Einstein residual:
`G_μν + Λg_μν + αH_μν - κ(Stress_μν + Θ_μν)`.
-/
def modifiedEinsteinResidual
    (G g H Stress Theta : idx → idx → ℂ) (Λ κ α : ℂ)
    (mu nu : idx) : ℂ :=
  G mu nu + Λ * g mu nu + α * H mu nu -
    κ * totalFiniteSource Stress Theta mu nu

/-- Vanishing residual is exactly the finite modified-Einstein equation. -/
theorem modifiedEinsteinResidual_eq_zero_iff
    (G g H Stress Theta : idx → idx → ℂ) (Λ κ α : ℂ) (mu nu : idx) :
    modifiedEinsteinResidual G g H Stress Theta Λ κ α mu nu = 0 ↔
      G mu nu + Λ * g mu nu + α * H mu nu =
        κ * totalFiniteSource Stress Theta mu nu := by
  unfold modifiedEinsteinResidual
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    exact sub_eq_zero.mpr h

end FiniteModifiedEinstein

end InfoGeometry.Canonical.EmergentGravity
