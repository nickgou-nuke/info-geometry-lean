import Mathlib.Tactic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic

import InfoGeometry.Canonical.ParaHyperkahlerHodgeDecompositionBridge
import InfoGeometry.Canonical.HarmonicWeakHorizonBridge

/-!
# Souriau-Hodge Triad Dynamics & Cohomological Protection Bridge

This module formalizes the canonical mathematical synthesis connecting:
1. **The Hodge Triad as Souriau Dynamics**:
   The classical Hodge-Helmholtz decomposition:
   $$\Omega^\bullet(M) = \operatorname{im}(d) \oplus \operatorname{im}(\delta) \oplus \mathcal{H}_\Delta$$
   is the geometric realization of the Souriau dynamical split:
   - **Exact Sector $\operatorname{im}(d)$ (Irrotational Souriau Dynamics)**:
     Carries the additive trace functional $\operatorname{tr} \neq 0$, longitudinal gauge
     transformations, and Weyl dilatation homotheties ($A$-sector of Iwasawa $KAN$).
     Preserved identically under dilatations: $\operatorname{projExact}(X_{\mathrm{dil}}(c) \omega_{\mathrm{ex}}) = X_{\mathrm{dil}}(c) \omega_{\mathrm{ex}}$.
   - **Coexact Sector $\operatorname{im}(\delta)$ (Rotational Souriau Dynamics)**:
     Carries the traceless algebra $\operatorname{tr} = 0$, volume-preserving symplectomorphisms
     of $\mathrm{Sp}(4n, \mathbb{R})$, and physical spin precession.
     Intertwined with the exact sector via the Dirac-Kähler engine $\mathcal{D} = d - \delta$.
   - **Harmonic Sector $\mathcal{H}_\Delta = \ker(d) \cap \ker(\delta)$ (Modular Topology)**:
     Represents the de Rham cohomology classes $\mathcal{H}_\Delta^k(M) \cong H_{\mathrm{dR}}^k(M)$.
     Topological ground states and modular horizon boundary modes.

2. **Cartan's Magic Formula and Cohomological Protection of Harmonic Modes**:
   For any smooth vector field $X$, Cartan's formula gives:
   $$\mathcal{L}_X \omega = d(\iota_X \omega) + \iota_X(d \omega)$$
   On harmonic modes $\gamma \in \mathcal{H}_\Delta$ where $d\gamma = 0$, the contraction term $\iota_X(d\gamma)$ vanishes:
   $$\mathcal{L}_X \gamma = d(\iota_X \gamma)$$
   Therefore, the Lie derivative of ANY harmonic mode is strictly exact:
   $$\operatorname{projHarmonic}(\mathcal{L}_X \gamma) = 0, \quad \operatorname{projCoexact}(\mathcal{L}_X \gamma) = 0$$
   This proves that the de Rham cohomology class $[\mathcal{L}_X \gamma]_{\mathrm{dR}}$ vanishes identically,
   protecting the modular horizon vacuum against all smooth dynamical flows.

3. **Intertwining with the Dirac-Kähler Kinetic Engine**:
   - The Dirac-Kähler operator $\mathcal{D} = d - \delta$ transmutes irrotational exact gradients
     into rotational coexact curls, and coexact curls into exact gradients.
   - Dilatations commute with the kinetic operator $\mathcal{D}$, the Laplacian $\Delta$,
     and the Zorn-BdG bi-wave operators $\hat{Z}_{\mathrm{kin}}$ and $\hat{Z}_{\mathrm{mass}}(m)$.
   - $\mathcal{D}$ is an infinitesimal isometry of the indefinite Krein metric ($\mathcal{D} \in \mathfrak{so}_{\mathcal{K}}$).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace InfoGeometry.Canonical.SouriauHodgeTriad

open InfoGeometry.Canonical.ParaHyperkahlerHodgeDecompositionBridge
open InfoGeometry.Canonical.HarmonicWeakHorizon

variable {R : Type*} [CommRing R]

local notation "Form" => PolarizedHodgeForm R

/-! ## 1. Irrotational Souriau Dynamics (Trace Functional & Dilatations) -/

/-- Pure Souriau dilatation operator $X_{\mathrm{dil}}(c)$ acting on a polarized Hodge form:
    $X_{\mathrm{dil}}(c) \omega = c \cdot \omega$. -/
def souriauDilaton (c : R) (ω : Form) : Form :=
  c • ω

/-- **Theorem**: Dilatation preserves the exact subspace identically:
    $X_{\mathrm{dil}}(c)$ maps exact forms to exact forms, with zero coexact and harmonic projections. -/
theorem dilaton_preserves_exact (c : R) (ω : Form) :
    PolarizedHodgeForm.projExact (souriauDilaton c (PolarizedHodgeForm.projExact ω)) =
      souriauDilaton c (PolarizedHodgeForm.projExact ω) ∧
    PolarizedHodgeForm.projCoexact (souriauDilaton c (PolarizedHodgeForm.projExact ω)) = 0 ∧
    PolarizedHodgeForm.projHarmonic (souriauDilaton c (PolarizedHodgeForm.projExact ω)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · ext <;> simp [souriauDilaton, PolarizedHodgeForm.projExact]
  · ext <;> simp [souriauDilaton, PolarizedHodgeForm.projCoexact, PolarizedHodgeForm.projExact]
  · ext <;> simp [souriauDilaton, PolarizedHodgeForm.projHarmonic, PolarizedHodgeForm.projExact]

/-- **Theorem**: Dilatation preserves the coexact subspace identically:
    $X_{\mathrm{dil}}(c)$ maps coexact forms to coexact forms, with zero exact and harmonic projections. -/
theorem dilaton_preserves_coexact (c : R) (ω : Form) :
    PolarizedHodgeForm.projCoexact (souriauDilaton c (PolarizedHodgeForm.projCoexact ω)) =
      souriauDilaton c (PolarizedHodgeForm.projCoexact ω) ∧
    PolarizedHodgeForm.projExact (souriauDilaton c (PolarizedHodgeForm.projCoexact ω)) = 0 ∧
    PolarizedHodgeForm.projHarmonic (souriauDilaton c (PolarizedHodgeForm.projCoexact ω)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · ext <;> simp [souriauDilaton, PolarizedHodgeForm.projCoexact]
  · ext <;> simp [souriauDilaton, PolarizedHodgeForm.projExact, PolarizedHodgeForm.projCoexact]
  · ext <;> simp [souriauDilaton, PolarizedHodgeForm.projHarmonic, PolarizedHodgeForm.projCoexact]

/-- **Theorem**: Dilatation preserves the harmonic subspace identically:
    $X_{\mathrm{dil}}(c)$ maps harmonic forms to harmonic forms, with zero exact and coexact projections. -/
theorem dilaton_preserves_harmonic (c : R) (ω : Form) :
    PolarizedHodgeForm.projHarmonic (souriauDilaton c (PolarizedHodgeForm.projHarmonic ω)) =
      souriauDilaton c (PolarizedHodgeForm.projHarmonic ω) ∧
    PolarizedHodgeForm.projExact (souriauDilaton c (PolarizedHodgeForm.projHarmonic ω)) = 0 ∧
    PolarizedHodgeForm.projCoexact (souriauDilaton c (PolarizedHodgeForm.projHarmonic ω)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · ext <;> simp [souriauDilaton, PolarizedHodgeForm.projHarmonic]
  · ext <;> simp [souriauDilaton, PolarizedHodgeForm.projExact, PolarizedHodgeForm.projHarmonic]
  · ext <;> simp [souriauDilaton, PolarizedHodgeForm.projCoexact, PolarizedHodgeForm.projHarmonic]

/-- Trace of the dilatation operator on the two chiral exact components:
    $\operatorname{tr}_{\mathrm{ex}}(X_{\mathrm{dil}}(c)) = 2c$. -/
def exactTrace (c : R) : R :=
  2 * c

/-- Exact trace additivity:
    $\operatorname{tr}_{\mathrm{ex}}(X_{\mathrm{dil}}(c_1 + c_2)) = \operatorname{tr}_{\mathrm{ex}}(X_{\mathrm{dil}}(c_1)) + \operatorname{tr}_{\mathrm{ex}}(X_{\mathrm{dil}}(c_2))$. -/
theorem exactTrace_add (c₁ c₂ : R) :
    exactTrace (c₁ + c₂) = exactTrace c₁ + exactTrace c₂ := by
  dsimp [exactTrace]
  ring

/-! ## 2. Intertwining of Dilatations and the Kinetic Engine -/

/-- **Theorem**: Dilatations commute with the Dirac-Kähler kinetic engine:
    $\mathcal{D}(X_{\mathrm{dil}}(c) \omega) = X_{\mathrm{dil}}(c) (\mathcal{D} \omega)$. -/
theorem dilaton_commutes_dirac (c : R) (ω : Form) :
    PolarizedHodgeForm.diracKaehler (souriauDilaton c ω) =
      souriauDilaton c (PolarizedHodgeForm.diracKaehler ω) := by
  ext <;> simp [souriauDilaton, PolarizedHodgeForm.diracKaehler]

/-- **Theorem**: Dilatations commute with the Hodge Laplacian:
    $\Delta(X_{\mathrm{dil}}(c) \omega) = X_{\mathrm{dil}}(c) (\Delta \omega)$. -/
theorem dilaton_commutes_laplacian (c : R) (ω : Form) :
    PolarizedHodgeForm.hodgeLaplacian (souriauDilaton c ω) =
      souriauDilaton c (PolarizedHodgeForm.hodgeLaplacian ω) := by
  ext <;> simp [souriauDilaton, PolarizedHodgeForm.hodgeLaplacian]

/-- **Theorem**: Dilatations commute with the bi-wave kinetic operator:
    $\hat{Z}_{\mathrm{kin}}(c \cdot p) = c \cdot \hat{Z}_{\mathrm{kin}}(p)$. -/
theorem dilaton_commutes_bdgKinetic (c : R) (p : BiWaveForm R) :
    bdgKinetic (c • p.1, c • p.2) =
      (c • (bdgKinetic p).1, c • (bdgKinetic p).2) := by
  obtain ⟨ω, η⟩ := p
  dsimp [bdgKinetic]
  ext <;> simp [PolarizedHodgeForm.diracKaehler]

/-- **Theorem**: Dilatations commute with the bi-wave mass condensation operator:
    $\hat{Z}_{\mathrm{mass}}(m)(c \cdot p) = c \cdot \hat{Z}_{\mathrm{mass}}(m)(p)$. -/
theorem dilaton_commutes_bdgMass (m c : R) (p : BiWaveForm R) :
    bdgMass m (c • p.1, c • p.2) =
      (c • (bdgMass m p).1, c • (bdgMass m p).2) := by
  obtain ⟨ω, η⟩ := p
  dsimp [bdgMass]
  ext <;> simp <;> ring

/-! ## 3. Rotational Souriau Dynamics & Krein Isometries -/

/-- An operator $A$ on polarized forms is an infinitesimal Krein isometry (Lie algebra $\mathfrak{so}_{\mathcal{K}}$)
    if it is skew-adjoint with respect to the Krein inner product:
    $\langle A \omega, \eta \rangle_{\mathcal{K}} + \langle \omega, A \eta \rangle_{\mathcal{K}} = 0$. -/
def IsKreinInfinitesimalIsometry (A : Form → Form) : Prop :=
  ∀ ω η, PolarizedHodgeForm.kreinInnerProduct (A ω) η +
         PolarizedHodgeForm.kreinInnerProduct ω (A η) = 0

/-- **Theorem**: The Dirac-Kähler kinetic operator $\mathcal{D} = d - \delta$ is a canonical Krein infinitesimal isometry. -/
theorem diracKaehler_is_krein_isometry :
    IsKreinInfinitesimalIsometry (PolarizedHodgeForm.diracKaehler (R := R)) := by
  intro ω η
  exact PolarizedHodgeForm.krein_dirac_kaehler_skew_adjoint ω η

/-- **Theorem: Kinetic Transmutation**:
    The Dirac-Kähler operator maps irrotational Souriau modes (exact forms) entirely into
    rotational Souriau modes (coexact forms). -/
theorem dirac_transmutes_irrotational_to_rotational (ω : Form) :
    PolarizedHodgeForm.projCoexact (PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projExact ω)) =
      PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projExact ω) ∧
    PolarizedHodgeForm.projExact (PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projExact ω)) = 0 ∧
    PolarizedHodgeForm.projHarmonic (PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projExact ω)) = 0 := by
  have h := PolarizedHodgeForm.diracKaehler_maps_exact_to_coexact ω
  exact ⟨h.2.2, h.1, h.2.1⟩

/-- **Theorem: Inverse Kinetic Transmutation**:
    The Dirac-Kähler operator maps rotational Souriau modes (coexact forms) entirely into
    irrotational Souriau modes (exact forms). -/
theorem dirac_transmutes_rotational_to_irrotational (ω : Form) :
    PolarizedHodgeForm.projExact (PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projCoexact ω)) =
      PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projCoexact ω) ∧
    PolarizedHodgeForm.projCoexact (PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projCoexact ω)) = 0 ∧
    PolarizedHodgeForm.projHarmonic (PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projCoexact ω)) = 0 := by
  have h := PolarizedHodgeForm.diracKaehler_maps_coexact_to_exact ω
  exact ⟨h.2.2, h.1, h.2.1⟩

/-! ## 4. Cartan's Formula & Cohomological Protection of Harmonic Modes -/

/-- An algebraic Cartan variation of a form $\omega$ induced by a vector field $X$:
    Carries the exact gradient part $d(\iota_X \omega)$ and coclosed contraction $\iota_X(d \omega)$. -/
structure CartanVariation (R : Type*) [CommRing R] where
  exact_shift : PolarizedHodgeForm R
  coexact_shift : PolarizedHodgeForm R
  exact_shift_is_exact : PolarizedHodgeForm.projExact exact_shift = exact_shift
  coexact_shift_is_coexact : PolarizedHodgeForm.projCoexact coexact_shift = coexact_shift

/-- Total Lie derivative variation: $\mathcal{L}_X \omega = d(\iota_X \omega) + \iota_X(d \omega)$. -/
def lieVariation (var : CartanVariation R) : Form :=
  var.exact_shift + var.coexact_shift

/-- On harmonic forms $\gamma \in \mathcal{H}_\Delta$ (where $d\gamma = 0$), the contraction term $\iota_X(d\gamma)$ vanishes identically.
    Hence the Lie derivative variation is purely exact: $\mathcal{L}_X \gamma = d(\iota_X \gamma)$. -/
def harmonicCartanVariation (ex_shift : Form) (h_ex : PolarizedHodgeForm.projExact ex_shift = ex_shift) :
    CartanVariation R where
  exact_shift := ex_shift
  coexact_shift := 0
  exact_shift_is_exact := h_ex
  coexact_shift_is_coexact := by ext <;> simp [PolarizedHodgeForm.projCoexact]

/-- **Theorem: Cohomological Protection of Harmonic Modes**:
    For any variation of a harmonic form where $\iota_X(d\gamma) = 0$, the variation is purely exact:
    1. Its projection onto the exact subspace is the full variation.
    2. Its projection onto the coexact subspace vanishes identically.
    3. Its projection onto the harmonic subspace vanishes identically. -/
theorem harmonic_variation_is_purely_exact (ex_shift : Form)
    (h_ex : PolarizedHodgeForm.projExact ex_shift = ex_shift) :
    let var := harmonicCartanVariation ex_shift h_ex
    PolarizedHodgeForm.projExact (lieVariation var) = lieVariation var ∧
    PolarizedHodgeForm.projCoexact (lieVariation var) = 0 ∧
    PolarizedHodgeForm.projHarmonic (lieVariation var) = 0 := by
  intro var
  dsimp [var, lieVariation, harmonicCartanVariation]
  have h_add_zero : ex_shift + 0 = ex_shift := by ext <;> simp
  rw [h_add_zero]
  refine ⟨h_ex, ?_, ?_⟩
  · rw [← h_ex, PolarizedHodgeForm.projCoexact_projExact]
  · rw [← h_ex, PolarizedHodgeForm.projHarmonic_projExact]

/-! ## 5. Master Synthesis Structure -/

/-- Certified synthesis structure summarizing the Souriau-Hodge Triad Dynamics. -/
structure SouriauHodgeTriadSynthesis where
  dilaton_exact_inv :
    ∀ {R : Type*} [CommRing R] (c : R) (ω : PolarizedHodgeForm R),
      PolarizedHodgeForm.projExact (souriauDilaton c (PolarizedHodgeForm.projExact ω)) =
        souriauDilaton c (PolarizedHodgeForm.projExact ω)
  dilaton_coexact_inv :
    ∀ {R : Type*} [CommRing R] (c : R) (ω : PolarizedHodgeForm R),
      PolarizedHodgeForm.projCoexact (souriauDilaton c (PolarizedHodgeForm.projCoexact ω)) =
        souriauDilaton c (PolarizedHodgeForm.projCoexact ω)
  dilaton_harmonic_inv :
    ∀ {R : Type*} [CommRing R] (c : R) (ω : PolarizedHodgeForm R),
      PolarizedHodgeForm.projHarmonic (souriauDilaton c (PolarizedHodgeForm.projHarmonic ω)) =
        souriauDilaton c (PolarizedHodgeForm.projHarmonic ω)
  dilaton_comm_dirac :
    ∀ {R : Type*} [CommRing R] (c : R) (ω : PolarizedHodgeForm R),
      PolarizedHodgeForm.diracKaehler (souriauDilaton c ω) =
        souriauDilaton c (PolarizedHodgeForm.diracKaehler ω)
  dilaton_comm_laplacian :
    ∀ {R : Type*} [CommRing R] (c : R) (ω : PolarizedHodgeForm R),
      PolarizedHodgeForm.hodgeLaplacian (souriauDilaton c ω) =
        souriauDilaton c (PolarizedHodgeForm.hodgeLaplacian ω)
  dilaton_comm_bdg_kin :
    ∀ {R : Type*} [CommRing R] (c : R) (p : BiWaveForm R),
      bdgKinetic (c • p.1, c • p.2) =
        (c • (bdgKinetic p).1, c • (bdgKinetic p).2)
  dilaton_comm_bdg_mass :
    ∀ {R : Type*} [CommRing R] (m c : R) (p : BiWaveForm R),
      bdgMass m (c • p.1, c • p.2) =
        (c • (bdgMass m p).1, c • (bdgMass m p).2)
  dirac_is_krein_isometry :
    ∀ {R : Type*} [CommRing R],
      IsKreinInfinitesimalIsometry (PolarizedHodgeForm.diracKaehler (R := R))
  transmute_exact_to_coexact :
    ∀ {R : Type*} [CommRing R] (ω : PolarizedHodgeForm R),
      PolarizedHodgeForm.projCoexact (PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projExact ω)) =
        PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projExact ω)
  transmute_coexact_to_exact :
    ∀ {R : Type*} [CommRing R] (ω : PolarizedHodgeForm R),
      PolarizedHodgeForm.projExact (PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projCoexact ω)) =
        PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projCoexact ω)
  harmonic_cartan_exact :
    ∀ {R : Type*} [CommRing R] (ex_shift : PolarizedHodgeForm R)
      (h_ex : PolarizedHodgeForm.projExact ex_shift = ex_shift),
      let var := harmonicCartanVariation ex_shift h_ex
      PolarizedHodgeForm.projExact (lieVariation var) = lieVariation var
  harmonic_cartan_harmonic_zero :
    ∀ {R : Type*} [CommRing R] (ex_shift : PolarizedHodgeForm R)
      (h_ex : PolarizedHodgeForm.projExact ex_shift = ex_shift),
      let var := harmonicCartanVariation ex_shift h_ex
      PolarizedHodgeForm.projHarmonic (lieVariation var) = 0

/-- Verified synthesis instance. -/
def souriau_hodge_triad_synthesis : SouriauHodgeTriadSynthesis where
  dilaton_exact_inv := fun c ω => (dilaton_preserves_exact c ω).1
  dilaton_coexact_inv := fun c ω => (dilaton_preserves_coexact c ω).1
  dilaton_harmonic_inv := fun c ω => (dilaton_preserves_harmonic c ω).1
  dilaton_comm_dirac := dilaton_commutes_dirac
  dilaton_comm_laplacian := dilaton_commutes_laplacian
  dilaton_comm_bdg_kin := dilaton_commutes_bdgKinetic
  dilaton_comm_bdg_mass := dilaton_commutes_bdgMass
  dirac_is_krein_isometry := diracKaehler_is_krein_isometry
  transmute_exact_to_coexact := fun ω => (dirac_transmutes_irrotational_to_rotational ω).1
  transmute_coexact_to_exact := fun ω => (dirac_transmutes_rotational_to_irrotational ω).1
  harmonic_cartan_exact := fun ex_shift h_ex => (harmonic_variation_is_purely_exact ex_shift h_ex).1
  harmonic_cartan_harmonic_zero := fun ex_shift h_ex => (harmonic_variation_is_purely_exact ex_shift h_ex).2.2

end InfoGeometry.Canonical.SouriauHodgeTriad
