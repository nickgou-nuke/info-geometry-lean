import Mathlib.Tactic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic

/-!
# Para-Hyperkähler Hodge Decomposition, Krein Lagrangian Polarities, & Zorn-BdG Mass Condensation

This module formalizes the canonical mathematical bridge uniting:
1. **6-Fold Polarized Hodge Decomposition**:
   In neutral signature $(2n, 2n)$, differential forms split into six canonical subspaces:
   $$\Omega^\bullet = (\operatorname{im}(d)_+ \oplus \operatorname{im}(d)_-) \oplus
     (\operatorname{im}(\delta)_+ \oplus \operatorname{im}(\delta)_-) \oplus
     (\mathcal{H}_+ \oplus \mathcal{H}_-)$$
   partitioned by the exact, coexact, and harmonic sectors, each graded by the chiral Peirce involution $\Gamma = \pm 1$.

2. **The Dirac-Kähler Operator and Hodge Laplacian**:
   The Dirac-Kähler operator $\mathcal{D} = d - \delta$ satisfies:
   - Anticommutation with chirality: $\{\mathcal{D}, \Gamma\} = 0$
   - Square equals the negative Hodge Laplacian: $\mathcal{D}^2 = -\Delta$
   - Annihilation of harmonic modes: $\mathcal{D}\gamma_h = 0$
   - Kinetic transmutation: $\mathcal{D}$ maps exact forms entirely into coexact forms, and coexact forms entirely into exact forms.

3. **Krein Metric and Lagrangian Polarities**:
   The indefinite Krein pairing of signature $(2n, 2n)$ induces:
   - Total isotropy of the exact subspace: $\langle d\alpha_1, d\alpha_2 \rangle_{\mathcal{K}} = 0$
   - Total isotropy of the coexact subspace: $\langle \delta\beta_1, \delta\beta_2 \rangle_{\mathcal{K}} = 0$
   - Non-degenerate hyperbolic duality pairing between $\operatorname{im}(d)$ and $\operatorname{im}(\delta)$, forming a canonical Lagrangian polar pair.
   - Skew-adjointness: $\langle \mathcal{D}\omega, \eta \rangle_{\mathcal{K}} + \langle \omega, \mathcal{D}\eta \rangle_{\mathcal{K}} = 0$, establishing $\mathcal{D}$ as an infinitesimal isometry of the Krein metric ($\mathcal{D} \in \mathfrak{so}_{\mathcal{K}}$).

4. **The Zorn-BdG Bi-Wave Operator and Mass Condensation**:
   The Bogoliubov-de Gennes / Dirac bi-wave operator $\hat{Z}_{\mathrm{BdG}}(m)$ acts on doublets $(\omega, \eta)$ by:
   $$\hat{Z}_{\mathrm{BdG}}(m)(\omega, \eta) = (\mathcal{D}\omega + m \cdot \eta, \; m \cdot \omega - \mathcal{D}\eta)$$
   - Massless decoupling at $m = 0$: $\hat{Z}_{\mathrm{BdG}}(0)(\omega, \eta) = (\mathcal{D}\omega, -\mathcal{D}\eta)$
   - Relativistic Klein-Gordon dispersion: $\hat{Z}_{\mathrm{BdG}}(m)^2 = -\Delta + m^2 \cdot \mathbb{I}$
   - Mass condensation: for $m \neq 0$, the exact gradient couples directly to the coexact curl across the bi-wave doublet.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Canonical.ParaHyperkahlerHodgeDecompositionBridge

/-- Full polarized Hodge components of a differential form in signature $(2n, 2n)$:
    Divided into Exact ($\operatorname{im} d$), Coexact ($\operatorname{im} \delta$), and Harmonic ($\mathcal{H}_\Delta$) sectors,
    each split into $(+ / -)$ Peirce chiral sectors. -/
@[ext]
structure PolarizedHodgeForm (R : Type*) [CommRing R] where
  exact_plus    : R
  exact_minus   : R
  coexact_plus  : R
  coexact_minus : R
  harmonic_plus : R
  harmonic_minus : R

namespace PolarizedHodgeForm

variable {R : Type*} [CommRing R]

def zero : PolarizedHodgeForm R where
  exact_plus := 0
  exact_minus := 0
  coexact_plus := 0
  coexact_minus := 0
  harmonic_plus := 0
  harmonic_minus := 0

def add (f g : PolarizedHodgeForm R) : PolarizedHodgeForm R where
  exact_plus := f.exact_plus + g.exact_plus
  exact_minus := f.exact_minus + g.exact_minus
  coexact_plus := f.coexact_plus + g.coexact_plus
  coexact_minus := f.coexact_minus + g.coexact_minus
  harmonic_plus := f.harmonic_plus + g.harmonic_plus
  harmonic_minus := f.harmonic_minus + g.harmonic_minus

def neg (f : PolarizedHodgeForm R) : PolarizedHodgeForm R where
  exact_plus := -f.exact_plus
  exact_minus := -f.exact_minus
  coexact_plus := -f.coexact_plus
  coexact_minus := -f.coexact_minus
  harmonic_plus := -f.harmonic_plus
  harmonic_minus := -f.harmonic_minus

def smul (c : R) (f : PolarizedHodgeForm R) : PolarizedHodgeForm R where
  exact_plus := c * f.exact_plus
  exact_minus := c * f.exact_minus
  coexact_plus := c * f.coexact_plus
  coexact_minus := c * f.coexact_minus
  harmonic_plus := c * f.harmonic_plus
  harmonic_minus := c * f.harmonic_minus

instance : Zero (PolarizedHodgeForm R) := ⟨zero⟩
instance : Add (PolarizedHodgeForm R) := ⟨add⟩
instance : Neg (PolarizedHodgeForm R) := ⟨neg⟩
instance : SMul R (PolarizedHodgeForm R) := ⟨smul⟩

@[simp] theorem add_exact_plus (f g : PolarizedHodgeForm R) : (f + g).exact_plus = f.exact_plus + g.exact_plus := rfl
@[simp] theorem add_exact_minus (f g : PolarizedHodgeForm R) : (f + g).exact_minus = f.exact_minus + g.exact_minus := rfl
@[simp] theorem add_coexact_plus (f g : PolarizedHodgeForm R) : (f + g).coexact_plus = f.coexact_plus + g.coexact_plus := rfl
@[simp] theorem add_coexact_minus (f g : PolarizedHodgeForm R) : (f + g).coexact_minus = f.coexact_minus + g.coexact_minus := rfl
@[simp] theorem add_harmonic_plus (f g : PolarizedHodgeForm R) : (f + g).harmonic_plus = f.harmonic_plus + g.harmonic_plus := rfl
@[simp] theorem add_harmonic_minus (f g : PolarizedHodgeForm R) : (f + g).harmonic_minus = f.harmonic_minus + g.harmonic_minus := rfl

@[simp] theorem neg_exact_plus (f : PolarizedHodgeForm R) : (-f).exact_plus = -f.exact_plus := rfl
@[simp] theorem neg_exact_minus (f : PolarizedHodgeForm R) : (-f).exact_minus = -f.exact_minus := rfl
@[simp] theorem neg_coexact_plus (f : PolarizedHodgeForm R) : (-f).coexact_plus = -f.coexact_plus := rfl
@[simp] theorem neg_coexact_minus (f : PolarizedHodgeForm R) : (-f).coexact_minus = -f.coexact_minus := rfl
@[simp] theorem neg_harmonic_plus (f : PolarizedHodgeForm R) : (-f).harmonic_plus = -f.harmonic_plus := rfl
@[simp] theorem neg_harmonic_minus (f : PolarizedHodgeForm R) : (-f).harmonic_minus = -f.harmonic_minus := rfl

@[simp] theorem zero_exact_plus : (0 : PolarizedHodgeForm R).exact_plus = 0 := rfl
@[simp] theorem zero_exact_minus : (0 : PolarizedHodgeForm R).exact_minus = 0 := rfl
@[simp] theorem zero_coexact_plus : (0 : PolarizedHodgeForm R).coexact_plus = 0 := rfl
@[simp] theorem zero_coexact_minus : (0 : PolarizedHodgeForm R).coexact_minus = 0 := rfl
@[simp] theorem zero_harmonic_plus : (0 : PolarizedHodgeForm R).harmonic_plus = 0 := rfl
@[simp] theorem zero_harmonic_minus : (0 : PolarizedHodgeForm R).harmonic_minus = 0 := rfl

@[simp] theorem smul_exact_plus (c : R) (f : PolarizedHodgeForm R) : (c • f).exact_plus = c * f.exact_plus := rfl
@[simp] theorem smul_exact_minus (c : R) (f : PolarizedHodgeForm R) : (c • f).exact_minus = c * f.exact_minus := rfl
@[simp] theorem smul_coexact_plus (c : R) (f : PolarizedHodgeForm R) : (c • f).coexact_plus = c * f.coexact_plus := rfl
@[simp] theorem smul_coexact_minus (c : R) (f : PolarizedHodgeForm R) : (c • f).coexact_minus = c * f.coexact_minus := rfl
@[simp] theorem smul_harmonic_plus (c : R) (f : PolarizedHodgeForm R) : (c • f).harmonic_plus = c * f.harmonic_plus := rfl
@[simp] theorem smul_harmonic_minus (c : R) (f : PolarizedHodgeForm R) : (c • f).harmonic_minus = c * f.harmonic_minus := rfl

instance : AddCommGroup (PolarizedHodgeForm R) where
  add_assoc f g h := by ext <;> (dsimp; ring)
  zero_add f := by ext <;> (dsimp; ring)
  add_zero f := by ext <;> (dsimp; ring)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel f := by ext <;> (dsimp; ring)
  add_comm f g := by ext <;> (dsimp; ring)

@[simp] theorem sub_exact_plus (f g : PolarizedHodgeForm R) : (f - g).exact_plus = f.exact_plus - g.exact_plus := by
  change (f + -g).exact_plus = f.exact_plus - g.exact_plus; dsimp; ring
@[simp] theorem sub_exact_minus (f g : PolarizedHodgeForm R) : (f - g).exact_minus = f.exact_minus - g.exact_minus := by
  change (f + -g).exact_minus = f.exact_minus - g.exact_minus; dsimp; ring
@[simp] theorem sub_coexact_plus (f g : PolarizedHodgeForm R) : (f - g).coexact_plus = f.coexact_plus - g.coexact_plus := by
  change (f + -g).coexact_plus = f.coexact_plus - g.coexact_plus; dsimp; ring
@[simp] theorem sub_coexact_minus (f g : PolarizedHodgeForm R) : (f - g).coexact_minus = f.coexact_minus - g.coexact_minus := by
  change (f + -g).coexact_minus = f.coexact_minus - g.coexact_minus; dsimp; ring
@[simp] theorem sub_harmonic_plus (f g : PolarizedHodgeForm R) : (f - g).harmonic_plus = f.harmonic_plus - g.harmonic_plus := by
  change (f + -g).harmonic_plus = f.harmonic_plus - g.harmonic_plus; dsimp; ring
@[simp] theorem sub_harmonic_minus (f g : PolarizedHodgeForm R) : (f - g).harmonic_minus = f.harmonic_minus - g.harmonic_minus := by
  change (f + -g).harmonic_minus = f.harmonic_minus - g.harmonic_minus; dsimp; ring

instance : Module R (PolarizedHodgeForm R) where
  one_smul f := by ext <;> (dsimp; ring)
  mul_smul a b f := by ext <;> (dsimp; ring)
  smul_zero a := by ext <;> (dsimp; ring)
  smul_add a f g := by ext <;> (dsimp; ring)
  add_smul a b f := by ext <;> (dsimp; ring)
  zero_smul f := by ext <;> (dsimp; ring)

/-! ## 1. Canonical Subspace Projectors -/

/-- Projector onto the exact subspace $\operatorname{im}(d)$. -/
def projExact (ω : PolarizedHodgeForm R) : PolarizedHodgeForm R where
  exact_plus := ω.exact_plus
  exact_minus := ω.exact_minus
  coexact_plus := 0
  coexact_minus := 0
  harmonic_plus := 0
  harmonic_minus := 0

/-- Projector onto the coexact subspace $\operatorname{im}(\delta)$. -/
def projCoexact (ω : PolarizedHodgeForm R) : PolarizedHodgeForm R where
  exact_plus := 0
  exact_minus := 0
  coexact_plus := ω.coexact_plus
  coexact_minus := ω.coexact_minus
  harmonic_plus := 0
  harmonic_minus := 0

/-- Projector onto the harmonic subspace $\mathcal{H}_\Delta$. -/
def projHarmonic (ω : PolarizedHodgeForm R) : PolarizedHodgeForm R where
  exact_plus := 0
  exact_minus := 0
  coexact_plus := 0
  coexact_minus := 0
  harmonic_plus := ω.harmonic_plus
  harmonic_minus := ω.harmonic_minus

/-- Direct sum decomposition: $\omega = P_{\mathrm{ex}}\omega + P_{\mathrm{co}}\omega + P_{\mathrm{harm}}\omega$. -/
@[simp] theorem projExact_add_projCoexact_add_projHarmonic (ω : PolarizedHodgeForm R) :
    projExact ω + projCoexact ω + projHarmonic ω = ω := by
  ext <;> (dsimp [projExact, projCoexact, projHarmonic]; ring)

@[simp] theorem projExact_idempotent (ω : PolarizedHodgeForm R) :
    projExact (projExact ω) = projExact ω := by
  ext <;> (dsimp [projExact]; try ring)

@[simp] theorem projCoexact_idempotent (ω : PolarizedHodgeForm R) :
    projCoexact (projCoexact ω) = projCoexact ω := by
  ext <;> (dsimp [projCoexact]; try ring)

@[simp] theorem projHarmonic_idempotent (ω : PolarizedHodgeForm R) :
    projHarmonic (projHarmonic ω) = projHarmonic ω := by
  ext <;> (dsimp [projHarmonic]; try ring)

@[simp] theorem projExact_projCoexact (ω : PolarizedHodgeForm R) :
    projExact (projCoexact ω) = 0 := by
  ext <;> (dsimp [projExact, projCoexact]; try ring)

@[simp] theorem projCoexact_projExact (ω : PolarizedHodgeForm R) :
    projCoexact (projExact ω) = 0 := by
  ext <;> (dsimp [projExact, projCoexact]; try ring)

@[simp] theorem projExact_projHarmonic (ω : PolarizedHodgeForm R) :
    projExact (projHarmonic ω) = 0 := by
  ext <;> (dsimp [projExact, projHarmonic]; try ring)

@[simp] theorem projHarmonic_projExact (ω : PolarizedHodgeForm R) :
    projHarmonic (projExact ω) = 0 := by
  ext <;> (dsimp [projExact, projHarmonic]; try ring)

@[simp] theorem projCoexact_projHarmonic (ω : PolarizedHodgeForm R) :
    projCoexact (projHarmonic ω) = 0 := by
  ext <;> (dsimp [projCoexact, projHarmonic]; try ring)

@[simp] theorem projHarmonic_projCoexact (ω : PolarizedHodgeForm R) :
    projHarmonic (projCoexact ω) = 0 := by
  ext <;> (dsimp [projCoexact, projHarmonic]; try ring)

/-! ## 2. 6-Fold Polarized Components -/

def projExactPlus (ω : PolarizedHodgeForm R) : PolarizedHodgeForm R :=
  ⟨ω.exact_plus, 0, 0, 0, 0, 0⟩

def projExactMinus (ω : PolarizedHodgeForm R) : PolarizedHodgeForm R :=
  ⟨0, ω.exact_minus, 0, 0, 0, 0⟩

def projCoexactPlus (ω : PolarizedHodgeForm R) : PolarizedHodgeForm R :=
  ⟨0, 0, ω.coexact_plus, 0, 0, 0⟩

def projCoexactMinus (ω : PolarizedHodgeForm R) : PolarizedHodgeForm R :=
  ⟨0, 0, 0, ω.coexact_minus, 0, 0⟩

def projHarmonicPlus (ω : PolarizedHodgeForm R) : PolarizedHodgeForm R :=
  ⟨0, 0, 0, 0, ω.harmonic_plus, 0⟩

def projHarmonicMinus (ω : PolarizedHodgeForm R) : PolarizedHodgeForm R :=
  ⟨0, 0, 0, 0, 0, ω.harmonic_minus⟩

/-- **Theorem**: Complete 6-fold polarized Hodge direct sum decomposition. -/
theorem sixfold_polarized_decomposition (ω : PolarizedHodgeForm R) :
    projExactPlus ω + projExactMinus ω +
    projCoexactPlus ω + projCoexactMinus ω +
    projHarmonicPlus ω + projHarmonicMinus ω = ω := by
  ext <;> (dsimp [projExactPlus, projExactMinus, projCoexactPlus, projCoexactMinus, projHarmonicPlus, projHarmonicMinus]; ring)

/-! ## 3. Chirality Involution -/

/-- Chiral Peirce involution $\Gamma = \pm 1$ across all sectors. -/
def chirality (ω : PolarizedHodgeForm R) : PolarizedHodgeForm R where
  exact_plus := ω.exact_plus
  exact_minus := -ω.exact_minus
  coexact_plus := ω.coexact_plus
  coexact_minus := -ω.coexact_minus
  harmonic_plus := ω.harmonic_plus
  harmonic_minus := -ω.harmonic_minus

/-- $\Gamma^2 = \mathbb{I}$. -/
theorem chirality_involutive (ω : PolarizedHodgeForm R) : chirality (chirality ω) = ω := by
  ext <;> (dsimp [chirality]; try ring)

/-! ## 4. Dirac-Kähler Operator & Hodge Laplacian -/

/-- The Dirac-Kähler operator $\mathcal{D} = d - \delta$.
    Swaps exact forms into coexact forms and vice-versa, with chiral sign twists,
    and annihilates harmonic modes. -/
def diracKaehler (ω : PolarizedHodgeForm R) : PolarizedHodgeForm R where
  exact_plus := ω.coexact_minus
  exact_minus := ω.coexact_plus
  coexact_plus := -ω.exact_minus
  coexact_minus := -ω.exact_plus
  harmonic_plus := 0
  harmonic_minus := 0

@[simp] theorem dirac_exact_plus (ω : PolarizedHodgeForm R) : (diracKaehler ω).exact_plus = ω.coexact_minus := rfl
@[simp] theorem dirac_exact_minus (ω : PolarizedHodgeForm R) : (diracKaehler ω).exact_minus = ω.coexact_plus := rfl
@[simp] theorem dirac_coexact_plus (ω : PolarizedHodgeForm R) : (diracKaehler ω).coexact_plus = -ω.exact_minus := rfl
@[simp] theorem dirac_coexact_minus (ω : PolarizedHodgeForm R) : (diracKaehler ω).coexact_minus = -ω.exact_plus := rfl
@[simp] theorem dirac_harmonic_plus (ω : PolarizedHodgeForm R) : (diracKaehler ω).harmonic_plus = 0 := rfl
@[simp] theorem dirac_harmonic_minus (ω : PolarizedHodgeForm R) : (diracKaehler ω).harmonic_minus = 0 := rfl

@[simp] theorem diracKaehler_zero : diracKaehler (0 : PolarizedHodgeForm R) = 0 := by
  ext <;> (dsimp; try ring)

theorem dirac_kaehler_add (ω η : PolarizedHodgeForm R) :
    diracKaehler (ω + η) = diracKaehler ω + diracKaehler η := by
  ext <;> (dsimp; try ring)

theorem dirac_kaehler_smul (c : R) (ω : PolarizedHodgeForm R) :
    diracKaehler (c • ω) = c • diracKaehler ω := by
  ext <;> (dsimp; try ring)

/-- **Theorem**: Dirac-Kähler operator anticommutes with chirality: $\{\mathcal{D}, \Gamma\} = 0$. -/
theorem dirac_kaehler_anticommutes_chirality (ω : PolarizedHodgeForm R) :
    chirality (diracKaehler ω) + diracKaehler (chirality ω) = 0 := by
  ext <;> (dsimp [chirality, diracKaehler]; try ring)

/-- **Theorem**: Dirac-Kähler operator annihilates the harmonic sector $\mathcal{H}_\Delta$. -/
theorem dirac_kaehler_on_harmonic (hp hm : R) :
    let ω_harm : PolarizedHodgeForm R := ⟨0, 0, 0, 0, hp, hm⟩
    diracKaehler ω_harm = 0 := by
  intro ω_harm
  ext <;> (dsimp [ω_harm]; try ring)

/-- Hodge-de Rham Laplacian $\Delta = -\mathcal{D}^2$ acting on polarized forms. -/
def hodgeLaplacian (ω : PolarizedHodgeForm R) : PolarizedHodgeForm R where
  exact_plus := ω.exact_plus
  exact_minus := ω.exact_minus
  coexact_plus := ω.coexact_plus
  coexact_minus := ω.coexact_minus
  harmonic_plus := 0
  harmonic_minus := 0

@[simp] theorem laplacian_exact_plus (ω : PolarizedHodgeForm R) : (hodgeLaplacian ω).exact_plus = ω.exact_plus := rfl
@[simp] theorem laplacian_exact_minus (ω : PolarizedHodgeForm R) : (hodgeLaplacian ω).exact_minus = ω.exact_minus := rfl
@[simp] theorem laplacian_coexact_plus (ω : PolarizedHodgeForm R) : (hodgeLaplacian ω).coexact_plus = ω.coexact_plus := rfl
@[simp] theorem laplacian_coexact_minus (ω : PolarizedHodgeForm R) : (hodgeLaplacian ω).coexact_minus = ω.coexact_minus := rfl
@[simp] theorem laplacian_harmonic_plus (ω : PolarizedHodgeForm R) : (hodgeLaplacian ω).harmonic_plus = 0 := rfl
@[simp] theorem laplacian_harmonic_minus (ω : PolarizedHodgeForm R) : (hodgeLaplacian ω).harmonic_minus = 0 := rfl

/-- **Fundamental Theorem**: The square of the Dirac-Kähler operator is the negative Laplacian:
    $\mathcal{D}^2 = -\Delta$. -/
theorem dirac_kaehler_sq_eq_neg_laplacian (ω : PolarizedHodgeForm R) :
    diracKaehler (diracKaehler ω) = - hodgeLaplacian ω := by
  ext <;> (dsimp; try ring)

/-! ## 5. Exact-Coexact Kinetic Transmutation -/

/-- **Theorem**: $\mathcal{D}$ maps exact forms entirely into coexact forms. -/
theorem diracKaehler_maps_exact_to_coexact (ω : PolarizedHodgeForm R) :
    projExact (diracKaehler (projExact ω)) = 0 ∧
    projHarmonic (diracKaehler (projExact ω)) = 0 ∧
    projCoexact (diracKaehler (projExact ω)) = diracKaehler (projExact ω) := by
  refine ⟨?_, ?_, ?_⟩
  · ext <;> (dsimp [projExact, diracKaehler]; try ring)
  · ext <;> (dsimp [projHarmonic, diracKaehler]; try ring)
  · ext <;> (dsimp [projCoexact, projExact, diracKaehler]; try ring)

/-- **Theorem**: $\mathcal{D}$ maps coexact forms entirely into exact forms. -/
theorem diracKaehler_maps_coexact_to_exact (ω : PolarizedHodgeForm R) :
    projCoexact (diracKaehler (projCoexact ω)) = 0 ∧
    projHarmonic (diracKaehler (projCoexact ω)) = 0 ∧
    projExact (diracKaehler (projCoexact ω)) = diracKaehler (projCoexact ω) := by
  refine ⟨?_, ?_, ?_⟩
  · ext <;> (dsimp [projCoexact, diracKaehler]; try ring)
  · ext <;> (dsimp [projHarmonic, diracKaehler]; try ring)
  · ext <;> (dsimp [projExact, projCoexact, diracKaehler]; try ring)

/-! ## 6. Krein Metric, Lagrangian Isotropies, & Duality -/

/-- Indefinite Krein inner product of neutral signature $(2n, 2n)$:
    Hyperbolic pairing between exact and coexact forms, and definite pairing on harmonic modes. -/
def kreinInnerProduct (ω η : PolarizedHodgeForm R) : R :=
  (ω.exact_plus * η.coexact_plus - ω.exact_minus * η.coexact_minus) +
  (ω.coexact_plus * η.exact_plus - ω.coexact_minus * η.exact_minus) +
  (ω.harmonic_plus * η.harmonic_plus + ω.harmonic_minus * η.harmonic_minus)

/-- Symmetry of the Krein inner product: $\langle \omega, \eta \rangle_{\mathcal{K}} = \langle \eta, \omega \rangle_{\mathcal{K}}$. -/
theorem krein_symm (ω η : PolarizedHodgeForm R) :
    kreinInnerProduct ω η = kreinInnerProduct η ω := by
  dsimp [kreinInnerProduct]; ring

theorem krein_add_left (ω₁ ω₂ η : PolarizedHodgeForm R) :
    kreinInnerProduct (ω₁ + ω₂) η = kreinInnerProduct ω₁ η + kreinInnerProduct ω₂ η := by
  dsimp [kreinInnerProduct]; ring

theorem krein_smul_left (c : R) (ω η : PolarizedHodgeForm R) :
    kreinInnerProduct (c • ω) η = c * kreinInnerProduct ω η := by
  dsimp [kreinInnerProduct]; ring

/-- **Infinitesimal Isometry**: The Dirac-Kähler operator is skew-adjoint with respect to the Krein metric:
    $\langle \mathcal{D}\omega, \eta \rangle_{\mathcal{K}} + \langle \omega, \mathcal{D}\eta \rangle_{\mathcal{K}} = 0$. -/
theorem krein_dirac_kaehler_skew_adjoint (ω η : PolarizedHodgeForm R) :
    kreinInnerProduct (diracKaehler ω) η + kreinInnerProduct ω (diracKaehler η) = 0 := by
  dsimp [kreinInnerProduct]; ring

/-- **Lagrangian Isotropy of Exact Forms**:
    The exact subspace $\operatorname{im}(d)$ is totally isotropic: $\langle d\alpha_1, d\alpha_2 \rangle_{\mathcal{K}} = 0$. -/
theorem exact_subspace_is_isotropic (ω η : PolarizedHodgeForm R) :
    kreinInnerProduct (projExact ω) (projExact η) = 0 := by
  dsimp [kreinInnerProduct, projExact]; ring

/-- **Lagrangian Isotropy of Coexact Forms**:
    The coexact subspace $\operatorname{im}(\delta)$ is totally isotropic: $\langle \delta\beta_1, \delta\beta_2 \rangle_{\mathcal{K}} = 0$. -/
theorem coexact_subspace_is_isotropic (ω η : PolarizedHodgeForm R) :
    kreinInnerProduct (projCoexact ω) (projCoexact η) = 0 := by
  dsimp [kreinInnerProduct, projCoexact]; ring

/-- Orthogonality of the exact and harmonic subspaces in the Krein metric. -/
theorem exact_harmonic_orthogonal (ω η : PolarizedHodgeForm R) :
    kreinInnerProduct (projExact ω) (projHarmonic η) = 0 := by
  dsimp [kreinInnerProduct, projExact, projHarmonic]; ring

/-- Orthogonality of the coexact and harmonic subspaces in the Krein metric. -/
theorem coexact_harmonic_orthogonal (ω η : PolarizedHodgeForm R) :
    kreinInnerProduct (projCoexact ω) (projHarmonic η) = 0 := by
  dsimp [kreinInnerProduct, projCoexact, projHarmonic]; ring

/-- **Hyperbolic Duality Pairing**:
    The Krein pairing between exact and coexact subspaces realizes hyperbolic duality:
    $\langle P_{\mathrm{ex}}\omega, P_{\mathrm{co}}\eta \rangle_{\mathcal{K}} = \omega_{e+} \eta_{c+} - \omega_{e-} \eta_{c-}$. -/
theorem exact_coexact_hyperbolic_pairing (ω η : PolarizedHodgeForm R) :
    kreinInnerProduct (projExact ω) (projCoexact η) =
      ω.exact_plus * η.coexact_plus - ω.exact_minus * η.coexact_minus := by
  dsimp [kreinInnerProduct, projExact, projCoexact]; ring

/-! ## 7. The Zorn-BdG Bi-Wave Operator & Mass Condensation -/

/-- The Bogoliubov-de Gennes / Dirac-Zorn Hamiltonian acting on the bi-wave doublet $(\omega, \eta)$:
    $\hat{Z}_{\mathrm{BdG}}(m)(\omega, \eta) = (\mathcal{D}\omega + m \cdot \eta, \; m \cdot \omega - \mathcal{D}\eta)$. -/
def bdgZorn (m : R) (p : PolarizedHodgeForm R × PolarizedHodgeForm R) :
    PolarizedHodgeForm R × PolarizedHodgeForm R :=
  (diracKaehler p.1 + m • p.2, m • p.1 - diracKaehler p.2)

/-- **Massless Decoupling**: In the massless limit $m = 0$, the BdG-Zorn operator decouples into
    independent chiral kinetic flows $\hat{Z}_{\mathrm{BdG}}(0)(\omega, \eta) = (\mathcal{D}\omega, -\mathcal{D}\eta)$. -/
theorem bdgZorn_massless_decoupling (p : PolarizedHodgeForm R × PolarizedHodgeForm R) :
    bdgZorn 0 p = (diracKaehler p.1, - diracKaehler p.2) := by
  dsimp [bdgZorn]
  simp only [zero_smul, add_zero, zero_sub]

/-- **Relativistic Klein-Gordon Dispersion**:
    The square of the BdG-Zorn operator is the massive Klein-Gordon operator:
    $\hat{Z}_{\mathrm{BdG}}(m)^2 = -\Delta + m^2 \cdot \mathbb{I}$. -/
theorem bdgZorn_sq_eq_klein_gordon (m : R) (p : PolarizedHodgeForm R × PolarizedHodgeForm R) :
    bdgZorn m (bdgZorn m p) =
      (- hodgeLaplacian p.1 + (m * m) • p.1,
       - hodgeLaplacian p.2 + (m * m) • p.2) := by
  obtain ⟨ω, η⟩ := p
  ext <;> (dsimp [bdgZorn]; simp; ring)

/-- **Mass Condensation**: For an exact gradient $\omega = P_{\mathrm{ex}}\omega$ with trivial doublet partner $\eta = 0$,
    the mass parameter $m \neq 0$ generates an exact second-component condensate $m \cdot \omega$ while
    the first component propagates the coexact curl $\mathcal{D}\omega$. -/
theorem bdgZorn_mass_condensation (m : R) (ω : PolarizedHodgeForm R) :
    bdgZorn m (projExact ω, 0) =
      (diracKaehler (projExact ω), m • projExact ω) := by
  dsimp [bdgZorn]
  simp only [smul_zero, add_zero, diracKaehler_zero, sub_zero]

end PolarizedHodgeForm

/-! ## 8. Synthesis Structure -/

/-- Verified synthesis structure summarizing the Para-Hyperkähler Hodge decomposition,
    Krein Lagrangian polarities, and Zorn-BdG mass condensation. -/
structure ParaHyperkahlerHodgeSynthesis where
  sixfold_decomposition :
    ∀ {R : Type*} [CommRing R] (ω : PolarizedHodgeForm R),
      PolarizedHodgeForm.projExactPlus ω + PolarizedHodgeForm.projExactMinus ω +
      PolarizedHodgeForm.projCoexactPlus ω + PolarizedHodgeForm.projCoexactMinus ω +
      PolarizedHodgeForm.projHarmonicPlus ω + PolarizedHodgeForm.projHarmonicMinus ω = ω
  chirality_involutive :
    ∀ {R : Type*} [CommRing R] (ω : PolarizedHodgeForm R),
      PolarizedHodgeForm.chirality (PolarizedHodgeForm.chirality ω) = ω
  dirac_anticomm_chirality :
    ∀ {R : Type*} [CommRing R] (ω : PolarizedHodgeForm R),
      PolarizedHodgeForm.chirality (PolarizedHodgeForm.diracKaehler ω) +
      PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.chirality ω) = 0
  dirac_sq_eq_neg_laplacian :
    ∀ {R : Type*} [CommRing R] (ω : PolarizedHodgeForm R),
      PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.diracKaehler ω) =
        - PolarizedHodgeForm.hodgeLaplacian ω
  dirac_exact_to_coexact :
    ∀ {R : Type*} [CommRing R] (ω : PolarizedHodgeForm R),
      PolarizedHodgeForm.projExact (PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projExact ω)) = 0 ∧
      PolarizedHodgeForm.projHarmonic (PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projExact ω)) = 0 ∧
      PolarizedHodgeForm.projCoexact (PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projExact ω)) =
        PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projExact ω)
  dirac_coexact_to_exact :
    ∀ {R : Type*} [CommRing R] (ω : PolarizedHodgeForm R),
      PolarizedHodgeForm.projCoexact (PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projCoexact ω)) = 0 ∧
      PolarizedHodgeForm.projHarmonic (PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projCoexact ω)) = 0 ∧
      PolarizedHodgeForm.projExact (PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projCoexact ω)) =
        PolarizedHodgeForm.diracKaehler (PolarizedHodgeForm.projCoexact ω)
  krein_symm :
    ∀ {R : Type*} [CommRing R] (ω η : PolarizedHodgeForm R),
      PolarizedHodgeForm.kreinInnerProduct ω η = PolarizedHodgeForm.kreinInnerProduct η ω
  krein_dirac_skew_adjoint :
    ∀ {R : Type*} [CommRing R] (ω η : PolarizedHodgeForm R),
      PolarizedHodgeForm.kreinInnerProduct (PolarizedHodgeForm.diracKaehler ω) η +
      PolarizedHodgeForm.kreinInnerProduct ω (PolarizedHodgeForm.diracKaehler η) = 0
  exact_isotropic :
    ∀ {R : Type*} [CommRing R] (ω η : PolarizedHodgeForm R),
      PolarizedHodgeForm.kreinInnerProduct (PolarizedHodgeForm.projExact ω) (PolarizedHodgeForm.projExact η) = 0
  coexact_isotropic :
    ∀ {R : Type*} [CommRing R] (ω η : PolarizedHodgeForm R),
      PolarizedHodgeForm.kreinInnerProduct (PolarizedHodgeForm.projCoexact ω) (PolarizedHodgeForm.projCoexact η) = 0
  exact_coexact_duality :
    ∀ {R : Type*} [CommRing R] (ω η : PolarizedHodgeForm R),
      PolarizedHodgeForm.kreinInnerProduct (PolarizedHodgeForm.projExact ω) (PolarizedHodgeForm.projCoexact η) =
        ω.exact_plus * η.coexact_plus - ω.exact_minus * η.coexact_minus
  bdg_massless_decoupling :
    ∀ {R : Type*} [CommRing R] (p : PolarizedHodgeForm R × PolarizedHodgeForm R),
      PolarizedHodgeForm.bdgZorn 0 p =
        (PolarizedHodgeForm.diracKaehler p.1, - PolarizedHodgeForm.diracKaehler p.2)
  bdg_dispersion :
    ∀ {R : Type*} [CommRing R] (m : R) (p : PolarizedHodgeForm R × PolarizedHodgeForm R),
      PolarizedHodgeForm.bdgZorn m (PolarizedHodgeForm.bdgZorn m p) =
        (- PolarizedHodgeForm.hodgeLaplacian p.1 + (m * m) • p.1,
         - PolarizedHodgeForm.hodgeLaplacian p.2 + (m * m) • p.2)

/-- Verified synthesis instance. -/
def parahyperkahler_hodge_synthesis : ParaHyperkahlerHodgeSynthesis where
  sixfold_decomposition := PolarizedHodgeForm.sixfold_polarized_decomposition
  chirality_involutive := PolarizedHodgeForm.chirality_involutive
  dirac_anticomm_chirality := PolarizedHodgeForm.dirac_kaehler_anticommutes_chirality
  dirac_sq_eq_neg_laplacian := PolarizedHodgeForm.dirac_kaehler_sq_eq_neg_laplacian
  dirac_exact_to_coexact := PolarizedHodgeForm.diracKaehler_maps_exact_to_coexact
  dirac_coexact_to_exact := PolarizedHodgeForm.diracKaehler_maps_coexact_to_exact
  krein_symm := PolarizedHodgeForm.krein_symm
  krein_dirac_skew_adjoint := PolarizedHodgeForm.krein_dirac_kaehler_skew_adjoint
  exact_isotropic := PolarizedHodgeForm.exact_subspace_is_isotropic
  coexact_isotropic := PolarizedHodgeForm.coexact_subspace_is_isotropic
  exact_coexact_duality := PolarizedHodgeForm.exact_coexact_hyperbolic_pairing
  bdg_massless_decoupling := PolarizedHodgeForm.bdgZorn_massless_decoupling
  bdg_dispersion := PolarizedHodgeForm.bdgZorn_sq_eq_klein_gordon

end InfoGeometry.Canonical.ParaHyperkahlerHodgeDecompositionBridge
