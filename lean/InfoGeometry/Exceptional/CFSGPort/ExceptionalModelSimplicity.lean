/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Adapted from the family-model transport step in AxiomMath/CFSG. The
family-specific quasisimplicity results are separate inputs; this module does
not claim to prove them.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.QuasisimpleTransport
public import InfoGeometry.Exceptional.CFSGPort.ExceptionalCatalog
public import InfoGeometry.Exceptional.CFSGPort.CommutatorTorus
public import InfoGeometry.Exceptional.CFSGPort.SuzukiSimplicity

public section

namespace InfoGeometry.Exceptional.CFSGPort

open Chevalley
open Simplicity

/-- In a finite field whose cardinality is a square `q²`, the `q`-power
Frobenius is an involution. This is the field-theoretic input used by the
external twisted-`²E₆` simplicity proof. -/
theorem pow_pow_card_sq {K : Type*} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (c : K) : (c ^ q) ^ q = c := by
  haveI := Fintype.ofFinite K
  rw [← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

/-- An untwisted exceptional model is simple whenever its local adjoint
Chevalley group is quasisimple over every field of the model's cardinality.
This ports the final model-equivalence step of the external family theorem;
the quasisimplicity hypothesis contains the family-specific proof debt. -/
theorem isSimpleGroup_of_untwistedChevalleyModel
    {G : Type} [Group G] {τ : Tag} {q : ℕ}
    (hmodel : UntwistedChevalleyModel G τ q)
    (hquasi : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q →
      IsQuasisimple (↥(adjointGroup τ K))) : IsSimpleGroup G := by
  simp only [Chevalley.UntwistedChevalleyModel] at hmodel
  obtain ⟨K, instField, instFinite, hcard, ⟨e⟩⟩ := hmodel
  letI : Field K := instField
  letI : Finite K := instFinite
  exact isSimpleGroup_of_mulEquiv (hquasi K hcard) e

/-- The generic exceptional adjoint carrier is quasisimple if it is perfect
and every normal subgroup is central or total. This is the local transport
step after the family-specific root-group argument. -/
theorem isQuasisimple_adjointGroup_of_normalDichotomy
    {τ : Tag} (K : Type*) [Field K]
    (hperf : Group.IsPerfect (↥(adjointGroup τ K)))
    (hnormal : ∀ M : Subgroup (↥(adjointGroup τ K)), M.Normal →
      M ≤ Subgroup.center (↥(adjointGroup τ K)) ∨ M = ⊤) :
    IsQuasisimple (↥(adjointGroup τ K)) := by
  letI : Nontrivial (adjointGroup τ K) := Chevalley.nontrivial_adjointGroup τ K
  apply isQuasisimple_of_forall
  · exact hperf
  · exact hnormal

/-- Simplicity of the adjoint central quotient from the local structural
inputs. This matches the quotient-level conclusion of the external F₄/E₈
helpers, while keeping perfectness and the normal-subgroup dichotomy explicit
for the pinned local Chevalley carrier. -/
theorem isSimpleGroup_adjointQuotient_of_normalDichotomy
    {τ : Tag} (K : Type) [Field K]
    (hperf : Group.IsPerfect (↥(adjointGroup τ K)))
    (hnormal : ∀ M : Subgroup (↥(adjointGroup τ K)), M.Normal →
      M ≤ Subgroup.center (↥(adjointGroup τ K)) ∨ M = ⊤) :
    IsSimpleGroup (AdjointQuotient τ K) := by
  letI : Nontrivial (adjointGroup τ K) := Chevalley.nontrivial_adjointGroup τ K
  exact isSimpleGroup_quotient_center_of_forall hperf hnormal

/-- The local finite-field F₄ adjoint quotient is simple once every normal
subgroup of its operator carrier is central or total. The perfectness input
is proved locally from the pinned root operators; only the normal-subgroup
dichotomy remains family-specific. -/
theorem isSimpleGroup_adjointQuotient_F4_of_normalDichotomy
    (K : Type) [Field K] (hK : 3 ≤ Nat.card K)
    (hnormal : ∀ M : Subgroup (↥(adjointGroup .F4 K)), M.Normal →
      M ≤ Subgroup.center (↥(adjointGroup .F4 K)) ∨ M = ⊤) :
    IsSimpleGroup (AdjointQuotient .F4 K) := by
  exact isSimpleGroup_adjointQuotient_of_normalDichotomy (τ := .F4) K
    (Chevalley.isPerfect_adjointGroup_F4_of_three_le_card K hK) hnormal

/-- The local finite-field E₈ adjoint quotient is simple once every normal
subgroup of its operator carrier is central or total. -/
theorem isSimpleGroup_adjointQuotient_E8_of_normalDichotomy
    (K : Type) [Field K] (hK : 3 ≤ Nat.card K)
    (hnormal : ∀ M : Subgroup (↥(adjointGroup .E8 K)), M.Normal →
      M ≤ Subgroup.center (↥(adjointGroup .E8 K)) ∨ M = ⊤) :
    IsSimpleGroup (AdjointQuotient .E8 K) := by
  exact isSimpleGroup_adjointQuotient_of_normalDichotomy (τ := .E8) K
    (Chevalley.isPerfect_adjointGroup_E8_of_three_le_card K hK) hnormal

/-- Uniform untwisted model transport from fieldwise perfectness and the
central-or-total normal-subgroup dichotomy. The fieldwise structural inputs
remain explicit, so this theorem does not claim the family proofs. -/
theorem isSimpleGroup_of_untwistedChevalleyModel_of_normalDichotomy
    {G : Type} [Group G] {τ : Tag} {q : ℕ}
    (hmodel : UntwistedChevalleyModel G τ q)
    (hinputs : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q →
      Group.IsPerfect (↥(adjointGroup τ K)) ∧
        (∀ M : Subgroup (↥(adjointGroup τ K)), M.Normal →
          M ≤ Subgroup.center (↥(adjointGroup τ K)) ∨ M = ⊤)) :
    IsSimpleGroup G := by
  apply isSimpleGroup_of_untwistedChevalleyModel hmodel
  intro K instField instFinite hcard
  letI : Field K := instField
  letI : Finite K := instFinite
  exact isQuasisimple_adjointGroup_of_normalDichotomy (τ := τ) K
    (hinputs K hcard).1 (hinputs K hcard).2

/-- The G₂ family-model adapter, with the external theorem's field-size
condition stated at the local carrier boundary. -/
theorem isSimpleGroup_of_G2Model
    {G : Type} [Group G] {q : ℕ}
    (hmodel : UntwistedChevalleyModel G .G2 q)
    (hquasi : ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K →
      IsQuasisimple (↥(adjointGroup .G2 K)))
    (hq : 3 ≤ q) : IsSimpleGroup G := by
  apply isSimpleGroup_of_untwistedChevalleyModel hmodel
  intro K instField instFinite hcard
  exact hquasi K (hcard ▸ hq)

/-- The G₂ adjoint model is quasisimple once its normal subgroups satisfy
the central-or-total dichotomy. This composes the locally ported G₂
perfectness theorem with the generic quasisimplicity transport. The
normal-subgroup dichotomy is the remaining Curtis--Tits/Bruhat proof input. -/
theorem isQuasisimple_adjointGroup_G2_of_normalDichotomy
    (K : Type*) [Field K] (hK : 3 ≤ Nat.card K)
    (hnormal : ∀ M : Subgroup (↥(adjointGroup .G2 K)), M.Normal →
      M ≤ Subgroup.center (↥(adjointGroup .G2 K)) ∨ M = ⊤) :
    IsQuasisimple (↥(adjointGroup .G2 K)) := by
  exact isQuasisimple_adjointGroup_of_normalDichotomy (τ := .G2) K
    (Chevalley.isPerfect_adjointGroup_G2_of_three_le_card K hK) hnormal

/-- Transport G₂ model simplicity from the explicit local normal-subgroup
dichotomy. This is the root-pinned model-level port boundary for the external
`fam_g2_simplicity` result; it does not hide the missing dichotomy proof. -/
theorem isSimpleGroup_of_G2Model_of_normalDichotomy
    {G : Type} [Group G] {q : ℕ}
    (hmodel : UntwistedChevalleyModel G .G2 q)
    (hnormal : ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K →
      ∀ M : Subgroup (↥(adjointGroup .G2 K)), M.Normal →
        M ≤ Subgroup.center (↥(adjointGroup .G2 K)) ∨ M = ⊤)
    (hq : 3 ≤ q) : IsSimpleGroup G := by
  apply isSimpleGroup_of_G2Model hmodel ?_ hq
  intro K instField instFinite hK
  letI : Field K := instField
  letI : Finite K := instFinite
  exact isQuasisimple_adjointGroup_G2_of_normalDichotomy K hK (hnormal K hK)

/-- The G₂ exceptional-catalog theorem in the same model-family shape as the
external CFSG result. The local adjoint quasisimplicity theorem remains an
explicit input. -/
theorem g2_family_simple_of_adjoint_quasisimple
    {G : Type} [Group G] {p f : ℕ}
    (hmodel : ExceptionalLieModel G .G2 p f)
    (hquasi : ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K →
      IsQuasisimple (↥(adjointGroup .G2 K))) :
    Nontrivial G ∧ IsSimpleGroup G := by
  simp only [Chevalley.ExceptionalLieModel, Chevalley.ChevalleyExceptionalAdmissible,
    Chevalley.ChevalleyExceptionalModel] at hmodel
  rcases hmodel with ⟨hparams, hchev⟩
  change p.Prime ∧ 1 ≤ f ∧ 3 ≤ p ^ f at hparams
  have hs : IsSimpleGroup G := isSimpleGroup_of_G2Model hchev hquasi hparams.2.2
  letI : IsSimpleGroup G := hs
  exact ⟨inferInstance, hs⟩

/-- G₂ catalog-model transport in the external theorem's conjunctive result
shape, with the family-specific normal-subgroup dichotomy left explicit. -/
theorem g2_family_simple_of_normalDichotomy
    {G : Type} [Group G] {p f : ℕ}
    (hmodel : ExceptionalLieModel G .G2 p f)
    (hnormal : ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K →
      ∀ M : Subgroup (↥(adjointGroup .G2 K)), M.Normal →
        M ≤ Subgroup.center (↥(adjointGroup .G2 K)) ∨ M = ⊤) :
    Nontrivial G ∧ IsSimpleGroup G := by
  simp only [Chevalley.ExceptionalLieModel, Chevalley.ChevalleyExceptionalAdmissible,
    Chevalley.ChevalleyExceptionalModel] at hmodel
  rcases hmodel with ⟨hparams, hchev⟩
  change p.Prime ∧ 1 ≤ f ∧ 3 ≤ p ^ f at hparams
  have hs : IsSimpleGroup G := isSimpleGroup_of_G2Model_of_normalDichotomy
    hchev hnormal hparams.2.2
  letI : IsSimpleGroup G := hs
  exact ⟨inferInstance, hs⟩

/-- A diagram/Frobenius-twisted exceptional model is simple when the derived
fixed subgroup is locally quasisimple. This is the local transport interface
for the external ²E₆ and ³D₄ family proofs. -/
theorem isSimpleGroup_of_twistedChevalleyModel
    {G : Type} [Group G] {t : TwistTag} {q : ℕ}
    (hmodel : TwistedChevalleyModel G t q)
    (hquasi : ∀ (K : Type) [Field K] [Finite K] (σ : K →+* K),
      (∀ c, σ c = c ^ q) →
      IsQuasisimple (↥⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆)) :
    IsSimpleGroup G := by
  simp only [Chevalley.TwistedChevalleyModel] at hmodel
  obtain ⟨K, instField, instFinite, hcard, ⟨σ, hσ, ⟨e⟩⟩⟩ := hmodel
  letI : Field K := instField
  letI : Finite K := instFinite
  exact isSimpleGroup_of_mulEquiv (hquasi K σ hσ) e

/-- A Ree/Tits relation model is simple when its derived root-generated
subgroup is locally quasisimple. This covers the transport shape shared by
²G₂, ²F₄, and the Tits group. -/
theorem isSimpleGroup_of_ReeTitsRelationModel
    {G : Type} [Group G] (τ : Tag) (ρ : Equiv.Perm (Fin τ.rank))
    (longRoots : Finset (Fin τ.rank)) {p f a : ℕ}
    (hmodel : ReeTitsRelationModel G τ ρ longRoots p f a)
    (hquasi : ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      IsQuasisimple
        (↥⁅reeFixedGroup τ K ρ
          (fun i => if i ∈ longRoots then p ^ a else p ^ (a + 1)),
          reeFixedGroup τ K ρ
            (fun i => if i ∈ longRoots then p ^ a else p ^ (a + 1))⁆)) :
    IsSimpleGroup G := by
  simp only [Chevalley.ReeTitsRelationModel] at hmodel
  obtain ⟨K, instField, instFinite, hcard, ⟨e⟩⟩ := hmodel
  letI : Field K := instField
  letI : Finite K := instFinite
  exact isSimpleGroup_of_mulEquiv (hquasi K hcard) e

/-- The local Suzuki operator model transports simplicity from the
parameterized operator group to any equivalent carrier. -/
theorem isSimpleGroup_of_SuzukiExceptionalModel
    {G : Type} [Group G] {p f : ℕ}
    (hmodel : SuzukiExceptionalModel G p f) :
    IsSimpleGroup G := by
  simp only [Chevalley.SuzukiExceptionalModel] at hmodel
  rcases hmodel with ⟨rfl, a, ha, K, instField, instFinite, hf, hcard, ⟨e⟩⟩
  letI : Field K := instField
  letI : Finite K := instFinite
  have hfield : Nat.card K = 2 ^ (2 * a + 1) := by
    calc
      Nat.card K = 2 ^ f := hcard
      _ = 2 ^ (2 * a + 1) := by rw [hf]
  haveI : Fintype K := Fintype.ofFinite K
  have hcard' : Fintype.card K = 2 ^ (2 * a + 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact hfield
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CharP K 2 := charP_of_card_eq_prime_pow hcard'
  exact e.isSimpleGroup_congr.mpr
    (Suzuki.suzukiGroup_isSimple_of_field (K := K) a (by omega) hfield)

end InfoGeometry.Exceptional.CFSGPort

end
