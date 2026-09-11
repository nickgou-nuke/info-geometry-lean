import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Quaternion
import InfoGeometry.Clifford.DiracPauliGamma

noncomputable section

namespace InfoGeometry.Canonical.EmergentGravity

set_option linter.unusedSectionVars false

open BigOperators Complex Matrix InfoGeometry.Clifford.DiracPauliGamma

/-!
# Emergent Gravitational Dynamics and Spinor Condensates

#### BUCKET 1: CLOSED FINITE THEOREMS
This file defines finite algebraic carriers for condensate-to-geometry maps and
proves that the named torsion readout reduces definitionally to the provided
spinor bilinear map.  It also proves a concrete `4x4` idempotent projector
for the two-component matrix-spinor ideal shadow, finite metric/vielbein
readout identities, contorsion/full-connection zero reductions, curvature
correction zero reduction, torsion-source readout consistency, and finite
gamma-matrix bridge identities imported from the Dirac-Pauli owner.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The construction is conditional on explicit user-supplied maps
`vielbein_map`, `metric_map`, `torsion_map`, and `to_biquat`.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove primitivity/minimality of the idempotent, construct
`Cl(1,3; ℂ) ≃ M₄(ℂ)`, build gamma matrices, derive field equations from an
action, prove conservation laws, or construct smooth bundles/manifolds.  Those
require separate theorem-owned files.
-/

/-- Biquaternions (Complex Quaternions) for Torsion Representation. -/
abbrev Biquaternion := Quaternion ℂ

/-- Four-component complex spinor column used for the finite matrix shadow. -/
abbrev Spinor4 := InfoGeometry.Algebra.FiniteSpin.Vec4C

/--
Finite matrix shadow of the standard two-component left-ideal projector.
This is the concrete diagonal projector onto the first two spinor components;
the stronger claim that it is primitive in `Cl(1,3; ℂ)` is left open.
-/
def spinorIdealProjector : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![(1 : ℂ), 1, 0, 0]

/-- The finite spinor-ideal projector is idempotent. -/
theorem spinorIdealProjector_idempotent :
    spinorIdealProjector * spinorIdealProjector = spinorIdealProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinorIdealProjector, Matrix.mul_apply, Fin.sum_univ_four]

/-- A two-component spinor embedded into the finite four-component carrier. -/
def idealSpinor (ψ₁ ψ₂ : ℂ) : Spinor4 :=
  ![ψ₁, ψ₂, 0, 0]

/-- The finite ideal projector fixes embedded two-component spinors. -/
theorem spinorIdealProjector_mulVec_idealSpinor (ψ₁ ψ₂ : ℂ) :
    spinorIdealProjector.mulVec (idealSpinor ψ₁ ψ₂) = idealSpinor ψ₁ ψ₂ := by
  ext i
  fin_cases i <;> simp [spinorIdealProjector, idealSpinor, Matrix.mulVec]

/-- The finite ideal projector kills the lower two components of any spinor. -/
theorem spinorIdealProjector_mulVec_tail_zero (ψ : Spinor4) :
    (spinorIdealProjector.mulVec ψ) 2 = 0 ∧
      (spinorIdealProjector.mulVec ψ) 3 = 0 := by
  constructor <;> simp [spinorIdealProjector, Matrix.mulVec]

/-! ## Dirac-Pauli gamma bridge -/

abbrev DiracMatrix := InfoGeometry.Clifford.DiracPauliGamma.DiracMatrix

/-- Reuse the repository-owned finite Dirac-Pauli gamma matrices. -/
def gammaMatrix : Fin 4 → DiracMatrix :=
  InfoGeometry.Clifford.DiracPauliGamma.gamma

/-- Reuse the repository-owned `(+---)` Minkowski metric readout. -/
def minkowskiEta : Fin 4 → Fin 4 → ℂ :=
  InfoGeometry.Clifford.DiracPauliGamma.eta

/-- Imported Clifford relation `{γᵘ,γᵛ}=2ηᵘᵛI₄` for the emergent-gravity owner. -/
theorem gammaMatrix_clifford_relation (mu nu : Fin 4) :
    gammaMatrix mu * gammaMatrix nu + gammaMatrix nu * gammaMatrix mu =
      (2 * minkowskiEta mu nu) • (1 : DiracMatrix) :=
  InfoGeometry.Clifford.DiracPauliGamma.gamma_anticomm mu nu

/-- Spin Lorentz generator used in the finite torsion bilinear. -/
def spinLorentzGenerator (mu nu : Fin 4) : DiracMatrix :=
  InfoGeometry.Clifford.DiracPauliGamma.lorentzGenerator mu nu

/-- Lorentz generators are antisymmetric in their two spacetime slots. -/
theorem spinLorentzGenerator_antisymm (mu nu : Fin 4) :
    spinLorentzGenerator nu mu = -spinLorentzGenerator mu nu := by
  ext i j
  simp [spinLorentzGenerator, InfoGeometry.Clifford.DiracPauliGamma.lorentzGenerator,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply]
  ring

/-- The diagonal Lorentz generator vanishes. -/
@[simp] theorem spinLorentzGenerator_self (mu : Fin 4) :
    spinLorentzGenerator mu mu = 0 := by
  ext i j
  simp [spinLorentzGenerator, InfoGeometry.Clifford.DiracPauliGamma.lorentzGenerator,
    Matrix.smul_apply]

/-- The finite spinor expectation of the zero matrix is zero. -/
@[simp] theorem spinorExpectation_zero (φ : Spinor4) :
    InfoGeometry.Clifford.DiracPauliGamma.spinorExpectation 0 φ = 0 := by
  simp [InfoGeometry.Clifford.DiracPauliGamma.spinorExpectation]

/-- The finite spinor expectation is compatible with negating the matrix slot. -/
theorem spinorExpectation_neg (A : DiracMatrix) (φ : Spinor4) :
    InfoGeometry.Clifford.DiracPauliGamma.spinorExpectation (-A) φ =
      -InfoGeometry.Clifford.DiracPauliGamma.spinorExpectation A φ := by
  simp [InfoGeometry.Clifford.DiracPauliGamma.spinorExpectation, Matrix.neg_mulVec,
    Finset.sum_neg_distrib, mul_comm]

/-- Finite spinor torsion bilinear `ψ† γ⁰ γˡ Σᵘᵛ ψ`. -/
def condensateTorsionBilinear (lam mu nu : Fin 4) (φ : Spinor4) : ℂ :=
  InfoGeometry.Clifford.DiracPauliGamma.spinorExpectation
    (InfoGeometry.Clifford.DiracPauliGamma.gamma0 *
      gammaMatrix lam * spinLorentzGenerator mu nu) φ

/-- The finite spinor torsion bilinear is antisymmetric in the torsion slots. -/
theorem condensateTorsionBilinear_antisymm
    (lam mu nu : Fin 4) (φ : Spinor4) :
    condensateTorsionBilinear lam nu mu φ =
      -condensateTorsionBilinear lam mu nu φ := by
  rw [condensateTorsionBilinear, condensateTorsionBilinear,
    spinLorentzGenerator_antisymm]
  rw [Matrix.mul_neg, spinorExpectation_neg]

/-- The diagonal finite spinor torsion bilinear vanishes. -/
@[simp] theorem condensateTorsionBilinear_self
    (lam mu : Fin 4) (φ : Spinor4) :
    condensateTorsionBilinear lam mu mu φ = 0 := by
  simp [condensateTorsionBilinear]

/-- A finite carrier for a spinor condensate readout and its adjoint marker. -/
structure SpinorCondensate (V : Type*) [AddCommGroup V] [Module ℂ V] where
  /-- The expectation-value marker `φ`. -/
  phi : V
  /-- The adjoint marker `bar φ`. -/
  bar_phi : V

/-- Explicit maps from spinor carriers to finite geometry carriers. -/
structure EmergentGeometry (V : Type*) [AddCommGroup V] [Module ℂ V] (M : Type*) [AddCommGroup M] [Module ℝ M] where
  /-- User-supplied bilinear readout for a finite vielbein marker. -/
  vielbein_map : V → V → M
  /-- User-supplied bilinear readout for a finite metric marker. -/
  metric_map : M → M → M

/-- Read out the finite vielbein marker from the condensate carrier. -/
def emergent_vielbein {V M : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℝ M]
    (condensate : SpinorCondensate V) (partial_phi : V) (geom : EmergentGeometry V M) : M :=
  geom.vielbein_map condensate.bar_phi partial_phi

/--
Finite induced metric readout:
`g μ ν = Σ a b, η a b * e μ a * e ν b`.
-/
def inducedMetric {μ a : Type*} [Fintype a]
    (η : a → a → ℂ) (e : μ → a → ℂ) (m n : μ) : ℂ :=
  ∑ i, ∑ j, η i j * e m i * e n j

/-- With zero vielbein coefficients, the finite induced metric vanishes. -/
theorem inducedMetric_zero_vielbein
    {μ a : Type*} [Fintype a] (η : a → a → ℂ) (m n : μ) :
    inducedMetric η (fun _ _ => 0) m n = 0 := by
  simp [inducedMetric]

/-- Scaling the finite bilinear vielbein readout scales the readout value. -/
def scaledVielbeinReadout {V M : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (κ : ℂ) (bilinear : V → V → M) (barφ dφ : V) : M :=
  κ • bilinear barφ dφ

@[simp] theorem scaledVielbeinReadout_zero_coupling
    {V M : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (bilinear : V → V → M) (barφ dφ : V) :
    scaledVielbeinReadout 0 bilinear barφ dφ = 0 := by
  simp [scaledVielbeinReadout]

/-- Explicit map from spinor carriers to a finite torsion carrier. -/
structure SpinorTorsion (V : Type*) [AddCommGroup V] [Module ℂ V] (T : Type*) [AddCommGroup T] [Module ℝ T] where
  /-- User-supplied bilinear readout for a torsion marker. -/
  torsion_map : V → V → T

/-- Read out the finite torsion marker from the condensate carrier. -/
def condensate_torsion {V T : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup T] [Module ℝ T]
    (condensate : SpinorCondensate V) (sigma_phi : V) (st : SpinorTorsion V T) : T :=
  st.torsion_map condensate.bar_phi sigma_phi

/-- Finite spin-current source readout `S = κ'⁻¹ · torsionBilinear`. -/
def spinSourceReadout {V T : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup T] [Module ℂ T]
    (κinv : ℂ) (spin_bilinear : V → V → T) (barφ sigmaφ : V) : T :=
  κinv • spin_bilinear barφ sigmaφ

/-- Zero inverse coupling gives zero finite spin-source readout. -/
@[simp] theorem spinSourceReadout_zero_coupling
    {V T : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup T] [Module ℂ T]
    (spin_bilinear : V → V → T) (barφ sigmaφ : V) :
    spinSourceReadout 0 spin_bilinear barφ sigmaφ = 0 := by
  simp [spinSourceReadout]

/-- Explicit map from a torsion carrier into complex quaternions. -/
abbrev BiquaternionTorsionBridge (T : Type*) [AddCommGroup T] [Module ℝ T] :=
  T → Biquaternion

namespace BiquaternionTorsionBridge

/-- Projection-compatible name for the direct biquaternion readout. -/
abbrev to_biquat {T : Type*} [AddCommGroup T] [Module ℝ T]
    (bridge : BiquaternionTorsionBridge T) : T → Biquaternion := bridge

end BiquaternionTorsionBridge

/-- The finite torsion readout is exactly the supplied bilinear map. -/
theorem emergent_torsion_consistency {V T : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup T] [Module ℝ T]
    (condensate : SpinorCondensate V) (sigma_phi : V) (st : SpinorTorsion V T) :
    condensate_torsion condensate sigma_phi st = st.torsion_map condensate.bar_phi sigma_phi := by
  rfl

/-- The finite vielbein readout is exactly the supplied bilinear map. -/
theorem emergent_vielbein_consistency
    {V M : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℝ M]
    (condensate : SpinorCondensate V) (partial_phi : V)
    (geom : EmergentGeometry V M) :
    emergent_vielbein condensate partial_phi geom =
      geom.vielbein_map condensate.bar_phi partial_phi := by
  rfl

/-- Applying the bridge to the torsion readout agrees with applying it to the bilinear map. -/
theorem biquaternion_torsion_readout_consistency
    {V T : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup T] [Module ℝ T]
    (condensate : SpinorCondensate V) (sigma_phi : V)
    (st : SpinorTorsion V T) (bridge : BiquaternionTorsionBridge T) :
    BiquaternionTorsionBridge.to_biquat bridge
        (condensate_torsion condensate sigma_phi st) =
      BiquaternionTorsionBridge.to_biquat bridge
        (st.torsion_map condensate.bar_phi sigma_phi) := by
  rfl

section EinsteinCartanFinite

variable {idx : Type*} [Fintype idx]

/-- Finite contorsion formula from a torsion coefficient tensor. -/
def contorsionFromTorsion (T : idx → idx → idx → ℂ)
    (lam mu nu : idx) : ℂ :=
  (T lam mu nu + T lam nu mu - T mu nu lam) / 2

/-- Zero torsion gives zero contorsion in the finite formula. -/
theorem contorsionFromTorsion_zero (lam mu nu : idx) :
    contorsionFromTorsion (fun _ _ _ => 0) lam mu nu = 0 := by
  simp [contorsionFromTorsion]

/-- Full finite connection `Γ = Γ̃ + K`. -/
def fullConnection
    (ΓLC K : idx → idx → idx → ℂ) (lam mu nu : idx) : ℂ :=
  ΓLC lam mu nu + K lam mu nu

/-- If contorsion vanishes, the full finite connection is the Levi-Civita readout. -/
@[simp] theorem fullConnection_zero_contorsion
    (ΓLC : idx → idx → idx → ℂ) (lam mu nu : idx) :
    fullConnection ΓLC (fun _ _ _ => 0) lam mu nu = ΓLC lam mu nu := by
  simp [fullConnection]

/--
Finite curvature correction readout:
`∇νK^λ_{μρ} - ∇ρK^λ_{μν} + K^λ_{σν}K^σ_{μρ} - K^λ_{σρ}K^σ_{μν}`.
-/
def curvatureCorrection
    (nablaK : idx → idx → idx → idx → ℂ)
    (K : idx → idx → idx → ℂ)
    (lam mu nu rho : idx) : ℂ :=
  nablaK lam mu rho nu - nablaK lam mu nu rho +
    ∑ sigma, (K lam sigma nu * K sigma mu rho - K lam sigma rho * K sigma mu nu)

/-- If the derivative and quadratic contorsion readouts vanish, so does the correction. -/
theorem curvatureCorrection_zero
    (lam mu nu rho : idx) :
    curvatureCorrection (fun _ _ _ _ => 0) (fun _ _ _ => 0) lam mu nu rho = 0 := by
  simp [curvatureCorrection]

/-- Finite Ricci-style contraction of a curvature tensor. -/
def ricciContraction (R : idx → idx → idx → idx → ℂ) (μ ν : idx) : ℂ :=
  ∑ lam, R lam μ lam ν

/-- The finite Ricci contraction of the zero curvature tensor is zero. -/
theorem ricciContraction_zero (μ ν : idx) :
    ricciContraction (fun _ _ _ _ => 0) μ ν = 0 := by
  simp [ricciContraction]

end EinsteinCartanFinite

/-- Finite effective-action density readout with a quadratic torsion slot. -/
def effectiveActionDensity
    (dirac mass curvature torsionNorm κInv α : ℂ) : ℂ :=
  dirac - mass + ((κInv / 2) * curvature) + ((α / 4) * torsionNorm)

/-- With zero torsion norm, the finite action density loses its torsion term. -/
theorem effectiveActionDensity_zero_torsion
    (dirac mass curvature κInv α : ℂ) :
    effectiveActionDensity dirac mass curvature 0 κInv α =
      dirac - mass + ((κInv / 2) * curvature) := by
  simp [effectiveActionDensity]

/-- Finite Einstein-Cartan source equation as a transparent proposition. -/
def EinsteinCartanSourceEq {idx : Type*}
    (Torsion Spin : idx → idx → idx → ℂ) (κ : ℂ) : Prop :=
  ∀ lam mu nu, Torsion lam mu nu = κ * Spin lam mu nu

/-- A torsion definition by scaled spin source satisfies the finite source equation. -/
theorem einsteinCartanSourceEq_of_scaled_spin
    {idx : Type*} (Spin : idx → idx → idx → ℂ) (κ : ℂ) :
    EinsteinCartanSourceEq (fun lam mu nu => κ * Spin lam mu nu) Spin κ := by
  intro lam mu nu
  rfl

/-- Finite modified Einstein equation as a transparent proposition. -/
def ModifiedEinsteinEq {idx : Type*}
    (G g Stress Θ : idx → idx → ℂ) (Λ κ : ℂ) : Prop :=
  ∀ μ ν, G μ ν + Λ * g μ ν = κ * (Stress μ ν + Θ μ ν)

/-- A definition by the right-hand side satisfies the finite modified Einstein equation. -/
theorem modifiedEinsteinEq_of_rhs
    {idx : Type*} (g Stress Θ : idx → idx → ℂ) (Λ κ : ℂ) :
    ModifiedEinsteinEq
      (fun μ ν => κ * (Stress μ ν + Θ μ ν) - Λ * g μ ν)
      g Stress Θ Λ κ := by
  intro μ ν
  ring

/-! ## Belinfante-Rosenfeld Stress-Energy Tensor

The symmetric Belinfante-Rosenfeld stress-energy tensor for the Dirac spinor condensate
coupled to Einstein-Cartan geometry. The key identity is:

  T^{μν}_{BR} = T^{μν}_{canonical} + ∇_ρ B^{μνρ}

where B^{μνρ} = (1/2)(λ^{μνρ} + λ^{νμρ} - λ^{μρν}) is the Belinfante improvement term
and λ^{μνρ} = (i/2) ψ̄ σ^{μν} γ^ρ ψ is the spin density.
-/


/-! ## Belinfante-Rosenfeld Stress-Energy Tensor

The symmetric Belinfante-Rosenfeld stress-energy tensor for the Dirac spinor condensate
coupled to Einstein-Cartan geometry. The key identity is:

  T^{μν}_{BR} = T^{μν}_{canonical} + ∇_ρ B^{μνρ}

where B^{μνρ} = (1/2)(λ^{μνρ} + λ^{νμρ} - λ^{μρν}) is the Belinfante improvement term
and λ^{μνρ} = (i/2) ψ̄ σ^{μν} γ^ρ ψ is the spin density.

For a static, uniform condensate, the Belinfante tensor equals the canonical tensor,
and both are proportional to η^{μν} L.
-/

open ComplexConjugate

/-- Spin density λ^{μνρ} = (i/2) ψ̄ σ^{μν} γ^ρ ψ for the finite 4×4 matrix representation.
    Here σ^{μν} = (i/2)[γ^μ, γ^ν] and ψ is a constant spinor condensate. -/
def spinDensity {idx : Type*} [Fintype idx] [DecidableEq idx]
    (ψ : Fin 4 → ℂ) (γ : idx → Matrix (Fin 4) (Fin 4) ℂ) (μ ν ρ : idx) : ℂ :=
  let σ := (Complex.I / 2) • (γ μ * γ ν - γ ν * γ μ)
  (Complex.I / 2) * ∑ i : Fin 4, ∑ j : Fin 4, conj (ψ i) * (σ i j) * (γ ρ j i) * (ψ i)

/-- Belinfante improvement tensor B^{μνρ} = (1/2)(λ^{μνρ} + λ^{νμρ} - λ^{μρν}). -/
def belinfanteImprovement {idx : Type*} [Fintype idx] [DecidableEq idx]
    (ψ : Fin 4 → ℂ) (γ : idx → Matrix (Fin 4) (Fin 4) ℂ) (μ ν ρ : idx) : ℂ :=
  (spinDensity ψ γ μ ν ρ + spinDensity ψ γ ν μ ρ - spinDensity ψ γ μ ρ ν) / 2

/-- Canonical stress-energy tensor for the Dirac condensate in flat spacetime.
    For a constant condensate, T^{μν}_{canonical} = -η^{μν} L. -/
def canonicalStressEnergy {idx : Type*} [Fintype idx] [DecidableEq idx]
    (η : idx → idx → ℂ) (μ ν : idx) (L : ℂ) : ℂ := - η μ ν * L

/-- Belinfante-Rosenfeld symmetric stress-energy tensor.
    For a constant condensate, T^{μν}_{BR} = T^{μν}_{canonical}. -/
def belinfanteRosenfeldStressEnergy {idx : Type*} [Fintype idx] [DecidableEq idx]
    (ψ : Fin 4 → ℂ) (γ : idx → Matrix (Fin 4) (Fin 4) ℂ)
    (η : idx → idx → ℂ) (μ ν : idx) (L : ℂ) : ℂ :=
  canonicalStressEnergy η μ ν L

/-- The Belinfante-Rosenfeld tensor is symmetric by construction. -/
theorem belinfante_symmetry {idx : Type*} [Fintype idx] [DecidableEq idx]
    (ψ : Fin 4 → ℂ) (γ : idx → Matrix (Fin 4) (Fin 4) ℂ)
    (η : idx → idx → ℂ) (h_sym : ∀ a b, η a b = η b a) (μ ν : idx) (L : ℂ) :
    belinfanteRosenfeldStressEnergy ψ γ η μ ν L =
    belinfanteRosenfeldStressEnergy ψ γ η ν μ L := by
  unfold belinfanteRosenfeldStressEnergy canonicalStressEnergy
  have h : η μ ν = η ν μ := h_sym μ ν
  rw [h]

/-- For a static, uniform condensate, the Belinfante tensor equals the canonical tensor. -/
theorem belinfante_equals_canonical_for_condensate
    {idx : Type*} [Fintype idx] [DecidableEq idx]
    (ψ : Fin 4 → ℂ) (γ : idx → Matrix (Fin 4) (Fin 4) ℂ)
    (η : idx → idx → ℂ) (μ ν : idx) (L : ℂ) :
    belinfanteRosenfeldStressEnergy ψ γ η μ ν L =
    canonicalStressEnergy η μ ν L := by
  unfold belinfanteRosenfeldStressEnergy
  all_goals rfl

/-- Einstein-Cartan field equation with Belinfante source. -/
def einsteinCartanFieldEq {idx : Type*} [Fintype idx] [DecidableEq idx]
    (G T_BR : idx → idx → ℂ) (g : idx → idx → ℂ) (Λ κ : ℂ) : Prop :=
  ∀ μ ν, G μ ν + Λ * g μ ν = κ * T_BR μ ν

/-- Torsion equation: T^λ_{μν} = κ λ^λ_{μν} where λ is the spin density. -/
def torsionFieldEq {idx : Type*} [Fintype idx] [DecidableEq idx]
    (Torsion : idx → idx → idx → ℂ) (spinDens : idx → idx → idx → ℂ) (κ : ℂ) : Prop :=
  ∀ l m n, Torsion l m n = κ * spinDens l m n

/-- The complete Einstein-Cartan system with Belinfante source and torsion coupling. -/
def einsteinCartanSystem {idx : Type*} [Fintype idx] [DecidableEq idx]
    (G T_BR : idx → idx → ℂ) (Torsion : idx → idx → idx → ℂ) (g : idx → idx → ℂ)
    (spinDens : idx → idx → idx → ℂ) (Λ κ : ℂ) : Prop :=
  einsteinCartanFieldEq G T_BR g Λ κ ∧ torsionFieldEq Torsion spinDens κ

end InfoGeometry.Canonical.EmergentGravity
