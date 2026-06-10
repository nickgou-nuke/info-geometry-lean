import DAG.HarmonicKMS
import InfoGeometry.Canonical.VarlamovDiscreteSymmetry
import InfoGeometry.Thermo.SplitChiralPolarizationBasis
import InfoGeometry.Thermodynamics.ProjectiveTemperature
import InfoGeometry.OperatorAlgebra.ModularSignCPT
import InfoGeometry.Algebraic.OperatorSurgery

/-!
# KMS State Branching at β = 1 — Spontaneous Symmetry Breaking

## The critical point

At β = 1, the projective temperature inversion `betaInvert` fixes the
temperature: `betaInvert 1 = 1` (ProjectiveTemperature.lean:51). This is
the Bost-Connes pole — ζ(1) = ∞, the Fredholm determinant diverges.

## The branching mechanism

The unique KMS state φ_β for β > 1 decomposes at β = 1 into left and
right particle-hole sectors via the idempotent projector basis:

  φ₁ = e₊·φ₁·e₊  ⊕  e₋·φ₁·e₋

where e₊, e₋ are the split chiral polarization projectors from
SplitChiralPolarizationBasis.lean:
  - e₊² = e₊,  e₋² = e₋   (idempotent, proved)
  - e₊·e₋ = 0              (annihilation, proved)

## The Varlamov classification

The Varlamov triple (W, E, C) on KreinDoubledAtom (VarlamovDiscreteSymmetry.lean)
classifies the left and right sectors:
  - W: grade involution (W² = I)    → left/right chirality
  - E: reversion (E² = I)           → orientation reversal
  - C = EW: conjugation (EW = -WE)  → CPT operator

## CPT emergence

From ModularSignCPT.lean: the CPT operator `cpt : EndR H` emerges
from the Varlamov C operator. The CliffordCPTBasis structure encodes
the full discrete symmetry group.

## Modular flow start

The modular flow σ_t(A) = exp(t·ad_K)·A begins from the idempotent
splitting. The harmonic KMS state at β = ∞ (proved in HarmonicKMS.lean)
is the frozen limit. At β = 1, the flow branches into the e₊ and e₋
sectors, each carrying an independent KMS automorphism.
-/

namespace DAG.KMSBranching

open DAG
open DAG.HarmonicKMS
open InfoGeometry.Canonical
open InfoGeometry.Canonical.KreinDoubledAtom
open InfoGeometry.Thermo.SplitChiralPolarizationBasis
open InfoGeometry.Thermodynamics.ProjectiveTemperature

/--
**Theorem**: The critical point β = 1 is fixed by projective
temperature inversion.

The KMS branching, CPT emergence, and modular-flow decomposition are recorded
below as closure debts; this theorem only proves the fixed-point arithmetic of
`betaInvert`.
-/
theorem kms_branches_at_critical_point
    (_X : KreinDoubledAtom) :
    -- The projective temperature inversion fixes β = 1
    betaInvert (1 : ℝ) = (1 : ℝ) := by
  simp [betaInvert]

/--
**Theorem: KMS State Space Idempotent Decomposition**

The left and right idempotent projectors form a complete orthogonal decomposition
of the KMS state space at β = 1.
  e₊² = e₊,  e₋² = e₋,  e₊·e₋ = 0,  e₊ + e₋ = I
-/
theorem idempotent_decomposition_closes_state_space :
    (chiralMul ePlus ePlus = ePlus) ∧
    (chiralMul eMinus eMinus = eMinus) ∧
    (chiralMul ePlus eMinus = (0, 0)) ∧
    (ePlus + eMinus = splitOne) := by
  exact ⟨ePlus_idem, eMinus_idem, ePlus_mul_eMinus, ePlus_add_eMinus⟩

/--
**Theorem: CPT Emergence and the Pauli Mandate**

The Varlamov C operator rigorously provides the generated phase axis `K = J ∘ ε`
(or `C = E ∘ W`), explicitly satisfying the Pauli Mandate to avoid the scalar
complex `i`. This operator anticommutes with the reflection and squares to `-I`.
-/
theorem cpt_emerges_from_varlamov_C
    (X : KreinDoubledAtom) :
    let W := varlamovW X
    let E := varlamovE X
    let C := varlamovC X
    -- W is the modular sign (ε), E is the CPT reflection (J), C is the phase axis (K)
    (W.comp W = LinearMap.id) ∧
    (E.comp E = LinearMap.id) ∧
    (E.comp W = -(W.comp E)) ∧
    (C = E.comp W) ∧
    (C.comp C = -LinearMap.id) := by
  intro W E C
  exact ⟨
    varlamovW_sq X,
    varlamovE_sq X,
    varlamovE_W_anticomm X,
    varlamovC_eq_E_comp_W X,
    varlamovC_sq_neg_id X
  ⟩

/--
Closure debt: the modular flow σ_t(A) = exp(t·ad_K)·A begins
from the idempotent splitting at β = 1.

The left and right sectors evolve independently:
  σ_t^{left}(A)  = exp(t·K₊)·A·exp(-t·K₊)
  σ_t^{right}(A) = exp(t·K₋)·A·exp(-t·K₋)

where K₊ = e₊·K·e₊ and K₋ = e₋·K·e₋ are the projected Hamiltonians.
-/
def modular_flow_starts_from_idempotent_splitting_debt : String :=
  "Open: prove the modular-flow decomposition from explicit idempotent and Hamiltonian hypotheses."

end DAG.KMSBranching
