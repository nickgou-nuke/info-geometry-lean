import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic

import InfoGeometry.Canonical.ParaHyperkahlerHodgeDecompositionBridge
import InfoGeometry.Canonical.CanonicalZornModularAAVBridge

/-!
# Harmonic Weak Horizon & Chiral Charge Transfer Bridge

This module formalizes the canonical mathematical bridge uniting:
1. **Harmonic Vanishing & Kinetic Flow Freezing**:
   On the modular horizon seam (the Klein bottle cross-cap $t=0$), the Dirac-Kähler kinetic
   operator $\mathcal{D} = d - \delta$ and the Hodge Laplacian $\Delta = -(d\delta + \delta d)$
   vanish identically on harmonic forms $\mathcal{H}_\Delta$.

2. **Kinetic-Mass Operator Splitting & Anticommutation**:
   The Bogoliubov-de Gennes / Dirac-Zorn bi-wave operator $\hat{Z}_{\mathrm{BdG}}(m)$ decomposes
   uniquely into pure kinetic flow $\hat{Z}_{\mathrm{kin}}$ and mass condensation $\hat{Z}_{\mathrm{mass}}(m)$:
   $$\hat{Z}_{\mathrm{BdG}}(m) = \hat{Z}_{\mathrm{kin}} + \hat{Z}_{\mathrm{mass}}(m)$$
   These operators strictly anticommute:
   $$\{\hat{Z}_{\mathrm{kin}}, \hat{Z}_{\mathrm{mass}}(m)\} = 0$$
   guaranteeing cross-term cancellation in relativistic Klein-Gordon dispersion.

3. **Horizon Mass Condensation & Doublet Reflection**:
   On harmonic doublets $(\gamma_1, \gamma_2) \in \mathcal{H}_\Delta \times \mathcal{H}_\Delta$,
   the kinetic flow freezes out completely: $\hat{Z}_{\mathrm{kin}}(\gamma_1, \gamma_2) = (0, 0)$.
   The bi-wave operator reduces purely to the mass condensate:
   $$\hat{Z}_{\mathrm{BdG}}(m)(\gamma_1, \gamma_2) = (m \cdot \gamma_2, \; m \cdot \gamma_1)$$
   swapping the forward and backward chiral twin modes across the modular throat.
   Its double application reproduces the squared mass: $\hat{Z}_{\mathrm{BdG}}(m)^2 \Psi = m^2 \cdot \Psi$.

4. **Indefinite Krein Horizon Matrix Elements**:
   The bi-wave Krein pairing:
   $$\langle \Phi, \Psi \rangle_{\mathcal{K}, 2} = \langle \phi_1, \psi_1 \rangle_{\mathcal{K}} + \langle \phi_2, \psi_2 \rangle_{\mathcal{K}}$$
   evaluates on harmonic horizon transitions to:
   $$\langle \Phi, \hat{Z}_{\mathrm{BdG}}(m) \Psi \rangle_{\mathcal{K}, 2} = m \cdot \big(\langle \phi_1, \psi_2 \rangle_{\mathcal{K}} + \langle \phi_2, \psi_1 \rangle_{\mathcal{K}}\big)$$
   recovering $m \cdot \langle \Psi, \Psi \rangle_{\mathcal{K}, 2}$ under twin-swap post-selection.

5. **Aharonov Weak Value Amplification across the Horizon**:
   The transition amplitude is governed by the Aharonov-Albert-Vaidman weak value:
   $$\Omega_w(\Phi, \Psi; m) = \frac{\langle \Phi, \hat{Z}_{\mathrm{BdG}}(m) \Psi \rangle_{\mathcal{K}, 2}}{\langle \Phi, \Psi \rangle_{\mathcal{K}, 2}}$$
   When the horizon overlap contracts to $\epsilon \neq 0$:
   $$\epsilon \cdot \Omega_w = \mathrm{Num}$$
   transferring mass and charge between chiral sectors through super-weak amplification.

6. **Cohomological Stability & Chiral Charge Invariance**:
   The harmonic projector is strictly invariant under arbitrary exact and coexact perturbations,
   and the chiral charge $Q_\Gamma(\gamma) = \gamma_{h+}^2 - \gamma_{h-}^2$ provides a topological index
   for the horizon ground state.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace InfoGeometry.Canonical.HarmonicWeakHorizon

open InfoGeometry.Canonical.ParaHyperkahlerHodgeDecompositionBridge
open InfoGeometry.Canonical.ZornModularAAV

variable {R : Type*} [CommRing R]

local notation "Form" => PolarizedHodgeForm R

/-! ## 1. Harmonic Doublets & Bi-Wave Krein Space -/

/-- Relativistic bi-wave doublet of differential forms:
    Doublet $(\psi, \phi)$ representing forward-in-time and backward-in-time wave modes. -/
abbrev BiWaveForm (R : Type*) [CommRing R] := PolarizedHodgeForm R × PolarizedHodgeForm R

/-- Indefinite Krein inner product on bi-wave doublets:
    $\langle (\phi_1, \phi_2), (\psi_1, \psi_2) \rangle_{\mathcal{K}, 2} = \langle \phi_1, \psi_1 \rangle_{\mathcal{K}} + \langle \phi_2, \psi_2 \rangle_{\mathcal{K}}$. -/
def biwaveKreinPairing (p q : BiWaveForm R) : R :=
  PolarizedHodgeForm.kreinInnerProduct p.1 q.1 + PolarizedHodgeForm.kreinInnerProduct p.2 q.2

/-- **Symmetry**: The bi-wave Krein pairing is symmetric: $\langle p, q \rangle = \langle q, p \rangle$. -/
theorem biwaveKreinPairing_symm (p q : BiWaveForm R) :
    biwaveKreinPairing p q = biwaveKreinPairing q p := by
  dsimp [biwaveKreinPairing]
  rw [PolarizedHodgeForm.krein_symm p.1 q.1, PolarizedHodgeForm.krein_symm p.2 q.2]

/-- Additivity of the bi-wave Krein pairing in the first argument. -/
theorem biwaveKreinPairing_add_left (p₁ p₂ q : BiWaveForm R) :
    biwaveKreinPairing (p₁.1 + p₂.1, p₁.2 + p₂.2) q =
      biwaveKreinPairing p₁ q + biwaveKreinPairing p₂ q := by
  dsimp [biwaveKreinPairing]
  rw [PolarizedHodgeForm.krein_add_left, PolarizedHodgeForm.krein_add_left]
  ring

/-- Left scalar multiplication in the bi-wave Krein pairing. -/
theorem biwaveKreinPairing_smul_left (c : R) (p q : BiWaveForm R) :
    biwaveKreinPairing (c • p.1, c • p.2) q = c * biwaveKreinPairing p q := by
  dsimp [biwaveKreinPairing]
  rw [PolarizedHodgeForm.krein_smul_left, PolarizedHodgeForm.krein_smul_left]
  ring

/-- Right scalar multiplication in the Krein inner product on individual forms. -/
theorem krein_smul_right (c : R) (ω η : Form) :
    PolarizedHodgeForm.kreinInnerProduct ω (c • η) = c * PolarizedHodgeForm.kreinInnerProduct ω η := by
  dsimp [PolarizedHodgeForm.kreinInnerProduct]
  ring

/-! ## 2. Harmonic Annihilation of Kinetic Flow -/

/-- **Theorem**: The Dirac-Kähler kinetic operator $\mathcal{D} = d - \delta$ vanishes identically
    on the harmonic sector: $\mathcal{D}(\gamma_h) = 0$. -/
theorem diracKaehler_on_harmonic (ω : Form) :
    PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projHarmonic ω) = 0 := by
  ext <;> (dsimp [PolarizedHodgeForm.projHarmonic, PolarizedHodgeForm.diracKaehler]; try ring)

/-- **Theorem**: The Hodge-de Rham Laplacian $\Delta = d\delta + \delta d$ vanishes identically
    on the harmonic sector: $\Delta(\gamma_h) = 0$. -/
theorem hodgeLaplacian_on_harmonic (ω : Form) :
    PolarizedHodgeForm.hodgeLaplacian (PolarizedHodgeForm.projHarmonic ω) = 0 := by
  ext <;> (dsimp [PolarizedHodgeForm.projHarmonic, PolarizedHodgeForm.hodgeLaplacian]; try ring)

/-! ## 3. Kinetic-Mass Splitting and Anticommutation -/

/-- Pure kinetic flow part of the BdG-Zorn operator:
    $\hat{Z}_{\mathrm{kin}}(\omega, \eta) = (\mathcal{D}\omega, -\mathcal{D}\eta)$. -/
def bdgKinetic (p : BiWaveForm R) : BiWaveForm R :=
  (PolarizedHodgeForm.diracKaehler p.1, - PolarizedHodgeForm.diracKaehler p.2)

/-- Pure mass condensation part of the BdG-Zorn operator:
    $\hat{Z}_{\mathrm{mass}}(m)(\omega, \eta) = (m \cdot \eta, m \cdot \omega)$. -/
def bdgMass (m : R) (p : BiWaveForm R) : BiWaveForm R :=
  (m • p.2, m • p.1)

/-- **Theorem**: The BdG-Zorn operator is the exact sum of kinetic flow and mass condensation:
    $\hat{Z}_{\mathrm{BdG}}(m) = \hat{Z}_{\mathrm{kin}} + \hat{Z}_{\mathrm{mass}}(m)$. -/
theorem bdgZorn_eq_kinetic_add_mass (m : R) (p : BiWaveForm R) :
    PolarizedHodgeForm.bdgZorn m p =
      ((bdgKinetic p).1 + (bdgMass m p).1,
       (bdgKinetic p).2 + (bdgMass m p).2) := by
  obtain ⟨ω, η⟩ := p
  ext <;> simp [PolarizedHodgeForm.bdgZorn, bdgKinetic, bdgMass] <;> ring

/-- **Anticommutation of Kinetic and Mass Operators**:
    $\{\hat{Z}_{\mathrm{kin}}, \hat{Z}_{\mathrm{mass}}(m)\} = 0$ on all bi-wave doublets.
    This guarantees the absence of first-order cross terms in relativistic Klein-Gordon dispersion. -/
theorem kinetic_mass_anticommutation (m : R) (p : BiWaveForm R) :
    (bdgKinetic (bdgMass m p)).1 + (bdgMass m (bdgKinetic p)).1 = 0 ∧
    (bdgKinetic (bdgMass m p)).2 + (bdgMass m (bdgKinetic p)).2 = 0 := by
  obtain ⟨ω, η⟩ := p
  dsimp [bdgKinetic, bdgMass]
  constructor
  · ext <;> (dsimp [PolarizedHodgeForm.diracKaehler]; try ring)
  · ext <;> (dsimp [PolarizedHodgeForm.diracKaehler]; try ring)

/-! ## 4. Horizon Seam Dynamics: Pure Mass Condensation -/

/-- **Theorem**: On the modular horizon seam, the kinetic operator vanishes identically on harmonic doublets:
    $\hat{Z}_{\mathrm{kin}}(\gamma_1, \gamma_2) = (0, 0)$. -/
theorem bdgKinetic_harmonic_vanishes (γ1 γ2 : Form) :
    bdgKinetic (PolarizedHodgeForm.projHarmonic γ1, PolarizedHodgeForm.projHarmonic γ2) = (0, 0) := by
  dsimp [bdgKinetic]
  rw [diracKaehler_on_harmonic γ1, diracKaehler_on_harmonic γ2]
  simp

/-- **Theorem**: On harmonic doublets, the BdG-Zorn operator reduces purely to the mass operator:
    $\hat{Z}_{\mathrm{BdG}}(m)(\gamma_1, \gamma_2) = \hat{Z}_{\mathrm{mass}}(m)(\gamma_1, \gamma_2)$. -/
theorem bdgZorn_on_harmonic_eq_mass (m : R) (γ1 γ2 : Form) :
    PolarizedHodgeForm.bdgZorn m
      (PolarizedHodgeForm.projHarmonic γ1, PolarizedHodgeForm.projHarmonic γ2) =
      bdgMass m (PolarizedHodgeForm.projHarmonic γ1, PolarizedHodgeForm.projHarmonic γ2) := by
  dsimp [PolarizedHodgeForm.bdgZorn, bdgMass]
  rw [diracKaehler_on_harmonic γ1, diracKaehler_on_harmonic γ2]
  simp

/-- **Explicit Action**: The BdG-Zorn operator on harmonic doublets acts as:
    $\hat{Z}_{\mathrm{BdG}}(m)(\gamma_1, \gamma_2) = (m \cdot \gamma_2, \; m \cdot \gamma_1)$. -/
theorem bdgZorn_on_harmonic_doublet (m : R) (γ1 γ2 : Form) :
    PolarizedHodgeForm.bdgZorn m
      (PolarizedHodgeForm.projHarmonic γ1, PolarizedHodgeForm.projHarmonic γ2) =
      (m • PolarizedHodgeForm.projHarmonic γ2, m • PolarizedHodgeForm.projHarmonic γ1) := by
  rw [bdgZorn_on_harmonic_eq_mass]
  rfl

/-- **Horizon Massless Freeze**: In the massless limit $m = 0$, all horizon dynamics freezes:
    $\hat{Z}_{\mathrm{BdG}}(0)(\gamma_1, \gamma_2) = (0, 0)$. -/
theorem bdgZorn_harmonic_massless_freezes (γ1 γ2 : Form) :
    PolarizedHodgeForm.bdgZorn 0
      (PolarizedHodgeForm.projHarmonic γ1, PolarizedHodgeForm.projHarmonic γ2) = (0, 0) := by
  rw [bdgZorn_on_harmonic_doublet]
  simp

/-- **Relativistic Dispersion on the Horizon**: Double application of the BdG-Zorn operator
    on harmonic modes recovers the mass square: $\hat{Z}_{\mathrm{BdG}}(m)^2 \Psi = m^2 \cdot \Psi$. -/
theorem bdgZorn_harmonic_sq (m : R) (γ1 γ2 : Form) :
    PolarizedHodgeForm.bdgZorn m
      (PolarizedHodgeForm.bdgZorn m
        (PolarizedHodgeForm.projHarmonic γ1, PolarizedHodgeForm.projHarmonic γ2)) =
      ((m * m) • PolarizedHodgeForm.projHarmonic γ1,
       (m * m) • PolarizedHodgeForm.projHarmonic γ2) := by
  rw [PolarizedHodgeForm.bdgZorn_sq_eq_klein_gordon]
  rw [hodgeLaplacian_on_harmonic γ1, hodgeLaplacian_on_harmonic γ2]
  simp

/-! ## 5. Krein Horizon Matrix Elements & Twin Swap -/

/-- Twin swap operation interchanging forward and backward chiral waves: $(p_1, p_2) \mapsto (p_2, p_1)$. -/
def twinSwap (p : BiWaveForm R) : BiWaveForm R :=
  (p.2, p.1)

/-- Twin swap is an involution: $\mathrm{twinSwap}(\mathrm{twinSwap}(p)) = p$. -/
theorem twinSwap_involutive (p : BiWaveForm R) :
    twinSwap (twinSwap p) = p := by
  dsimp [twinSwap]

/-- The mass operator is scalar multiplication by $m$ composed with the twin swap:
    $\hat{Z}_{\mathrm{mass}}(m) p = m \cdot \mathrm{twinSwap}(p)$. -/
theorem bdgMass_eq_smul_twinSwap (m : R) (p : BiWaveForm R) :
    bdgMass m p = (m • (twinSwap p).1, m • (twinSwap p).2) := by
  dsimp [bdgMass, twinSwap]

/-- **Krein Transition Matrix Element**:
    The matrix element of $\hat{Z}_{\mathrm{BdG}}(m)$ between harmonic doublets evaluates to:
    $\langle \Phi, \hat{Z}_{\mathrm{BdG}}(m) \Psi \rangle_{\mathcal{K}, 2} = m \cdot (\langle \phi_1, \psi_2 \rangle_{\mathcal{K}} + \langle \phi_2, \psi_1 \rangle_{\mathcal{K}})$. -/
theorem krein_harmonic_matrix_element (m : R) (ϕ1 ϕ2 ψ1 ψ2 : Form) :
    biwaveKreinPairing
      (PolarizedHodgeForm.projHarmonic ϕ1, PolarizedHodgeForm.projHarmonic ϕ2)
      (PolarizedHodgeForm.bdgZorn m
        (PolarizedHodgeForm.projHarmonic ψ1, PolarizedHodgeForm.projHarmonic ψ2)) =
      m * (PolarizedHodgeForm.kreinInnerProduct (PolarizedHodgeForm.projHarmonic ϕ1)
                                               (PolarizedHodgeForm.projHarmonic ψ2) +
           PolarizedHodgeForm.kreinInnerProduct (PolarizedHodgeForm.projHarmonic ϕ2)
                                               (PolarizedHodgeForm.projHarmonic ψ1)) := by
  rw [bdgZorn_on_harmonic_doublet]
  dsimp [biwaveKreinPairing]
  rw [krein_smul_right, krein_smul_right]
  ring

/-- **Twin-Swapped Horizon Matrix Element**:
    When the post-selected state is the twin swap of the pre-selected harmonic doublet,
    the transition matrix element recovers $m$ times the Krein norm:
    $\langle \mathrm{twinSwap}(\Psi), \hat{Z}_{\mathrm{BdG}}(m) \Psi \rangle_{\mathcal{K}, 2} = m \cdot \langle \Psi, \Psi \rangle_{\mathcal{K}, 2}$. -/
theorem krein_harmonic_twin_swap_matrix_element (m : R) (γ1 γ2 : Form) :
    let Ψ := (PolarizedHodgeForm.projHarmonic γ1, PolarizedHodgeForm.projHarmonic γ2)
    biwaveKreinPairing (twinSwap Ψ) (PolarizedHodgeForm.bdgZorn m Ψ) =
      m * biwaveKreinPairing Ψ Ψ := by
  intro Ψ
  dsimp [Ψ, twinSwap]
  rw [krein_harmonic_matrix_element]
  dsimp [biwaveKreinPairing]
  ring

/-! ## 6. Aharonov Weak Measurement & Amplification -/

/-- Real Aharonov weak value across the modular horizon seam: $\Omega_w = \mathrm{Num} / \mathrm{Den}$. -/
def horizonWeakValue (num den : ℝ) : ℝ :=
  aharonovWeakValue num den

/-- **Weak Value Scaling on the Horizon Seam**:
    Multiplying the weak value by the horizon overlap denominator $\epsilon \neq 0$ recovers the exact numerator:
    $\epsilon \cdot \Omega_w = \mathrm{Num}$. -/
theorem horizon_weak_value_scaling (num den eps : ℝ) (h_den : den = eps) (h_eps : eps ≠ 0) :
    eps * horizonWeakValue num den = num := by
  dsimp [horizonWeakValue]
  exact weak_value_amplification_scaling num den eps h_den h_eps

/-- **Mass Transfer Weak Value**:
    For twin-swapped harmonic doublets with overlap $\epsilon \neq 0$, the weak value
    amplifies the mass parameter $m$:
    $\epsilon \cdot \Omega_w(m \cdot N, \epsilon) = m \cdot N$. -/
theorem horizon_mass_transfer_weak_value (m eps norm_val : ℝ) (h_eps : eps ≠ 0) :
    eps * horizonWeakValue (m * norm_val) eps = m * norm_val := by
  exact horizon_weak_value_scaling (m * norm_val) eps eps rfl h_eps

/-! ## 7. Chiral Charge and Cohomological Stability -/

/-- Total chiral charge of a polarized Hodge form:
    $Q_\Gamma(\omega) = \langle \Gamma \omega, \omega \rangle_{\mathcal{K}}$. -/
def chiralCharge (ω : Form) : R :=
  PolarizedHodgeForm.kreinInnerProduct (PolarizedHodgeForm.chirality ω) ω

/-- **Theorem**: On harmonic forms, the chiral charge evaluates to the difference of chiral harmonic squares:
    $Q_\Gamma(\gamma_h) = \gamma_{h+}^2 - \gamma_{h-}^2$. -/
theorem chiralCharge_on_harmonic (ω : Form) :
    chiralCharge (PolarizedHodgeForm.projHarmonic ω) =
      ω.harmonic_plus * ω.harmonic_plus - ω.harmonic_minus * ω.harmonic_minus := by
  dsimp [chiralCharge, PolarizedHodgeForm.chirality, PolarizedHodgeForm.projHarmonic,
         PolarizedHodgeForm.kreinInnerProduct]
  ring

/-- **Cohomological Stability**: Under arbitrary exact gradients and coexact curls,
    the harmonic projection is strictly invariant:
    $\mathrm{projHarmonic}(\gamma_h + d\alpha + \delta\beta) = \gamma_h$. -/
theorem harmonic_cohomological_stability (γ α β : Form) :
    PolarizedHodgeForm.projHarmonic
      (PolarizedHodgeForm.projHarmonic γ +
       PolarizedHodgeForm.projExact α +
       PolarizedHodgeForm.projCoexact β) =
      PolarizedHodgeForm.projHarmonic γ := by
  ext <;> dsimp [PolarizedHodgeForm.projHarmonic, PolarizedHodgeForm.projExact, PolarizedHodgeForm.projCoexact] <;> ring

/-! ## 8. Master Synthesis Structure -/

/-- Certified synthesis structure summarizing the Harmonic Weak Horizon and
    Chiral Charge Transfer formalization. -/
structure HarmonicWeakHorizonSynthesis where
  dirac_on_harmonic :
    ∀ {R : Type*} [CommRing R] (ω : PolarizedHodgeForm R),
      PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projHarmonic ω) = 0
  laplacian_on_harmonic :
    ∀ {R : Type*} [CommRing R] (ω : PolarizedHodgeForm R),
      PolarizedHodgeForm.hodgeLaplacian (PolarizedHodgeForm.projHarmonic ω) = 0
  kinetic_mass_anticomm :
    ∀ {R : Type*} [CommRing R] (m : R) (p : BiWaveForm R),
      (bdgKinetic (bdgMass m p)).1 + (bdgMass m (bdgKinetic p)).1 = 0 ∧
      (bdgKinetic (bdgMass m p)).2 + (bdgMass m (bdgKinetic p)).2 = 0
  bdg_harmonic_doublet :
    ∀ {R : Type*} [CommRing R] (m : R) (γ1 γ2 : PolarizedHodgeForm R),
      PolarizedHodgeForm.bdgZorn m
        (PolarizedHodgeForm.projHarmonic γ1, PolarizedHodgeForm.projHarmonic γ2) =
        (m • PolarizedHodgeForm.projHarmonic γ2, m • PolarizedHodgeForm.projHarmonic γ1)
  bdg_massless_freeze :
    ∀ {R : Type*} [CommRing R] (γ1 γ2 : PolarizedHodgeForm R),
      PolarizedHodgeForm.bdgZorn 0
        (PolarizedHodgeForm.projHarmonic γ1, PolarizedHodgeForm.projHarmonic γ2) = (0, 0)
  bdg_harmonic_dispersion :
    ∀ {R : Type*} [CommRing R] (m : R) (γ1 γ2 : PolarizedHodgeForm R),
      PolarizedHodgeForm.bdgZorn m
        (PolarizedHodgeForm.bdgZorn m
          (PolarizedHodgeForm.projHarmonic γ1, PolarizedHodgeForm.projHarmonic γ2)) =
        ((m * m) • PolarizedHodgeForm.projHarmonic γ1,
         (m * m) • PolarizedHodgeForm.projHarmonic γ2)
  krein_harmonic_matrix :
    ∀ {R : Type*} [CommRing R] (m : R) (ϕ1 ϕ2 ψ1 ψ2 : PolarizedHodgeForm R),
      biwaveKreinPairing
        (PolarizedHodgeForm.projHarmonic ϕ1, PolarizedHodgeForm.projHarmonic ϕ2)
        (PolarizedHodgeForm.bdgZorn m
          (PolarizedHodgeForm.projHarmonic ψ1, PolarizedHodgeForm.projHarmonic ψ2)) =
        m * (PolarizedHodgeForm.kreinInnerProduct (PolarizedHodgeForm.projHarmonic ϕ1)
                                                 (PolarizedHodgeForm.projHarmonic ψ2) +
             PolarizedHodgeForm.kreinInnerProduct (PolarizedHodgeForm.projHarmonic ϕ2)
                                                 (PolarizedHodgeForm.projHarmonic ψ1))
  krein_twin_swap_matrix :
    ∀ {R : Type*} [CommRing R] (m : R) (γ1 γ2 : PolarizedHodgeForm R),
      let Ψ := (PolarizedHodgeForm.projHarmonic γ1, PolarizedHodgeForm.projHarmonic γ2)
      biwaveKreinPairing (twinSwap Ψ) (PolarizedHodgeForm.bdgZorn m Ψ) =
        m * biwaveKreinPairing Ψ Ψ
  wva_horizon_scaling :
    ∀ num den eps : ℝ, den = eps → eps ≠ 0 → eps * horizonWeakValue num den = num
  mass_transfer_wva :
    ∀ m eps norm_val : ℝ, eps ≠ 0 → eps * horizonWeakValue (m * norm_val) eps = m * norm_val
  chiral_charge_harmonic :
    ∀ {R : Type*} [CommRing R] (ω : PolarizedHodgeForm R),
      chiralCharge (PolarizedHodgeForm.projHarmonic ω) =
        ω.harmonic_plus * ω.harmonic_plus - ω.harmonic_minus * ω.harmonic_minus
  cohomological_stability :
    ∀ {R : Type*} [CommRing R] (γ α β : PolarizedHodgeForm R),
      PolarizedHodgeForm.projHarmonic
        (PolarizedHodgeForm.projHarmonic γ +
         PolarizedHodgeForm.projExact α +
         PolarizedHodgeForm.projCoexact β) =
        PolarizedHodgeForm.projHarmonic γ

/-- Verified synthesis instance. -/
def harmonic_weak_horizon_synthesis : HarmonicWeakHorizonSynthesis where
  dirac_on_harmonic := diracKaehler_on_harmonic
  laplacian_on_harmonic := hodgeLaplacian_on_harmonic
  kinetic_mass_anticomm := kinetic_mass_anticommutation
  bdg_harmonic_doublet := bdgZorn_on_harmonic_doublet
  bdg_massless_freeze := bdgZorn_harmonic_massless_freezes
  bdg_harmonic_dispersion := bdgZorn_harmonic_sq
  krein_harmonic_matrix := krein_harmonic_matrix_element
  krein_twin_swap_matrix := krein_harmonic_twin_swap_matrix_element
  wva_horizon_scaling := horizon_weak_value_scaling
  mass_transfer_wva := horizon_mass_transfer_weak_value
  chiral_charge_harmonic := chiralCharge_on_harmonic
  cohomological_stability := harmonic_cohomological_stability

end InfoGeometry.Canonical.HarmonicWeakHorizon
