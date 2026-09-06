import InfoGeometry.Canonical.BostConnesGalois
import InfoGeometry.Canonical.NormalConeInductive
import InfoGeometry.Canonical.ThermalCompactRecurrence
import DAG.AnalyticBridge

/-!
# Bost--Connes Symmetry-Breaking Readouts

This module contains the source-supported algebraic part of the
Bost--Connes symmetry-breaking story.

It does not prove the analytic classification of KMS states, extremality, or
weak-star zero-temperature limits.  It proves the kernel-checkable readouts
available from the current structural owner files:

* Galois branches act on cyclotomic generators by `e(r) ↦ e(g·r)`.
* Any boundary readout pulls back along each Galois automorphism, producing a
  `G`-indexed branch family.
* Branches separate on a generator when the pulled generator values are
  explicitly separated by the readout.
* The crossed-product and semigroup equivariance relations specialize to
  cyclotomic generators.

#### BUCKET 1: CLOSED FINITE THEOREMS

The Galois generator readouts, pulled-back boundary readouts, crossed-product
generator relation, inductive compactification readout, normal-cone/cocycle
limit packet, and state-separation lemmas below are fully verified.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

`algebraic_cyclotomic_ground_states_faithful` proves the faithful separation
of algebraic cyclotomic ground states from explicit premises:
an injective complex embedding, the evaluation formula
`φ_g(e(r)) = ι(g • χ(r))`, and the statement that `χ(ℚ)` faithfully generates
the abelian Galois action.

#### BUCKET 3: OPEN CLOSURE DEBT

This file does not prove the analytic KMS classification, extremality,
Kronecker--Weber, or the construction of the maximal abelian extension.
Those remain external mathematical inputs until instantiated by dedicated
owner files.
-/

noncomputable section

namespace InfoGeometry.Canonical.BostConnesSymmetryBreaking

open InfoGeometry.Canonical.BostConnesGalois
open InfoGeometry.Canonical.BostConnesKMS
open InfoGeometry.Canonical.ThermalCompactRecurrence
open InfoGeometry.Arithmetic.BostConnesSystem

universe u

variable
    {C_comm : Type u} [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
    (e_rep : GroupElementRepresentation C_comm)
    {G : Type u} [GaloisActionData G]
    (galoisAut : GaloisAlgebraAutomorphism C_comm e_rep (G := G))

/-! ## 1. Galois branches on cyclotomic generators -/

/-- A Galois branch sends the cyclotomic generator `e(r)` to `e(g·r)`. -/
theorem galois_branch_generator_readout
    (g : G) (r : ℚ) :
    galoisAut.galoisAut g (e_rep.e r) =
      e_rep.e (GaloisActionData.actOnQ g r) :=
  galoisAut.galoisAut_on_generator g r

/--
Two Galois branches are separated on `e(r)` whenever their target generator
values are separated.
-/
theorem galois_branches_separate_on_generator
    {g h : G} {r : ℚ}
    (hsep :
      e_rep.e (GaloisActionData.actOnQ g r) ≠
        e_rep.e (GaloisActionData.actOnQ h r)) :
    galoisAut.galoisAut g (e_rep.e r) ≠
      galoisAut.galoisAut h (e_rep.e r) := by
  rw [galois_branch_generator_readout e_rep galoisAut g r]
  rw [galois_branch_generator_readout e_rep galoisAut h r]
  exact hsep

/--
If a Galois branch fixes every boundary observable, then it is the identity
branch.
-/
theorem galois_branch_faithful_of_fixed_boundary
    {g : G} (hfix : ∀ A : C_comm, galoisAut.galoisAut g A = A) :
    g = 1 :=
  galoisAut.galoisAut_faithful g hfix

/-! ## 2. Boundary KMS readout orbits -/

/--
Projection-level boundary readout with an inverse-temperature label.

This is intentionally weaker than a completed C*-KMS state.  The fields record
the scalar boundary evaluation and the normalization parameters already used
by the projection-level KMS corridor.
-/
structure BoundaryKMSReadout
    (C_comm : Type u) [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm] where
  β : ℝ
  ζβ : ℝ
  read : C_comm → ℂ

namespace BoundaryKMSReadout

/--
Pull a boundary readout back along a Galois automorphism.  This is the
state-level algebraic branch indexed by `g : G`.
-/
def galoisTranslate
    (Φ : BoundaryKMSReadout C_comm)
    (galoisAut : GaloisAlgebraAutomorphism C_comm e_rep (G := G))
    (g : G) :
    BoundaryKMSReadout C_comm where
  β := Φ.β
  ζβ := Φ.ζβ
  read := fun A => Φ.read (galoisAut.galoisAut g A)

@[simp]
theorem galoisTranslate_beta
    (Φ : BoundaryKMSReadout C_comm)
    (g : G) :
    (galoisTranslate (e_rep := e_rep) Φ galoisAut g).β = Φ.β :=
  rfl

@[simp]
theorem galoisTranslate_zeta
    (Φ : BoundaryKMSReadout C_comm)
    (g : G) :
    (galoisTranslate (e_rep := e_rep) Φ galoisAut g).ζβ = Φ.ζβ :=
  rfl

@[simp]
theorem galoisTranslate_read
    (Φ : BoundaryKMSReadout C_comm)
    (g : G) (A : C_comm) :
    (galoisTranslate (e_rep := e_rep) Φ galoisAut g).read A =
      Φ.read (galoisAut.galoisAut g A) :=
  rfl

/-- The translated readout evaluates a cyclotomic generator at the translated argument. -/
theorem galoisTranslate_on_generator
    (Φ : BoundaryKMSReadout C_comm)
    (g : G) (r : ℚ) :
    (galoisTranslate (e_rep := e_rep) Φ galoisAut g).read (e_rep.e r) =
      Φ.read (e_rep.e (GaloisActionData.actOnQ g r)) := by
  simp [galoisTranslate, galoisAut.galoisAut_on_generator]

/-- The `G`-indexed family of Galois boundary readouts generated by one base readout. -/
def galoisBranchFamily
    (Φ : BoundaryKMSReadout C_comm)
    (galoisAut : GaloisAlgebraAutomorphism C_comm e_rep (G := G)) :
    G → BoundaryKMSReadout C_comm :=
  fun g => galoisTranslate (e_rep := e_rep) Φ galoisAut g

@[simp]
theorem galoisBranchFamily_apply
    (Φ : BoundaryKMSReadout C_comm)
    (g : G) :
    galoisBranchFamily (e_rep := e_rep) Φ galoisAut g =
      galoisTranslate (e_rep := e_rep) Φ galoisAut g :=
  rfl

/-- Generator readout for the `G`-indexed branch family. -/
theorem galoisBranchFamily_on_generator
    (Φ : BoundaryKMSReadout C_comm)
    (g : G) (r : ℚ) :
    (galoisBranchFamily (e_rep := e_rep) Φ galoisAut g).read (e_rep.e r) =
      Φ.read (e_rep.e (GaloisActionData.actOnQ g r)) :=
  galoisTranslate_on_generator e_rep galoisAut Φ g r

/--
Two pulled-back boundary readouts are separated on `e(r)` whenever the base
readout separates the two Galois-translated generator values.
-/
theorem galoisTranslated_readouts_separate_on_generator
    (Φ : BoundaryKMSReadout C_comm)
    {g h : G} {r : ℚ}
    (hsep :
      Φ.read (e_rep.e (GaloisActionData.actOnQ g r)) ≠
        Φ.read (e_rep.e (GaloisActionData.actOnQ h r))) :
    (galoisTranslate (e_rep := e_rep) Φ galoisAut g).read (e_rep.e r) ≠
      (galoisTranslate (e_rep := e_rep) Φ galoisAut h).read (e_rep.e r) := by
  rw [galoisTranslate_on_generator e_rep galoisAut Φ g r]
  rw [galoisTranslate_on_generator e_rep galoisAut Φ h r]
  exact hsep

end BoundaryKMSReadout

/-! ## 3. Crossed-product and semigroup readouts -/

variable
    {Op : Type u} [Ring Op] [StarRing Op] [Algebra ℂ Op]
    (semigroup : SemigroupEndomorphismAction C_comm e_rep)
    (cuntz : CuntzMultiplicativeIndexing Op)
    (crossed : BostConnesCrossedProduct C_comm Op e_rep semigroup cuntz)

/--
The crossed-product relation on a cyclotomic generator:

`S_n ι(e(r)) S_n* = ι(α_n(e(r)))`.
-/
theorem crossedProduct_relation_on_generator
    (n : ℕ+) (r : ℚ) :
    BostConnesKMS.S cuntz n * crossed.ι (e_rep.e r) *
        star (BostConnesKMS.S cuntz n) =
      crossed.ι (semigroup.α n (e_rep.e r)) :=
  crossed.crossed_product_relation n (e_rep.e r)

/--
Galois-semigroup equivariance on a cyclotomic generator:

`g(α_n(e(r))) = α_n(g(e(r)))`.
-/
theorem galois_semigroup_equivariance_on_generator
    (equivariance :
      GaloisSemigroupEquivariance C_comm e_rep semigroup G galoisAut)
    (g : G) (n : ℕ+) (r : ℚ) :
    galoisAut.galoisAut g (semigroup.α n (e_rep.e r)) =
      semigroup.α n (galoisAut.galoisAut g (e_rep.e r)) :=
  equivariance.equivariance g n (e_rep.e r)

/--
Generator-expanded form of Galois-semigroup equivariance:

`g(α_n(e(r))) = α_n(e(g·r))`.
-/
theorem galois_semigroup_equivariance_generator_readout
    (equivariance :
      GaloisSemigroupEquivariance C_comm e_rep semigroup G galoisAut)
    (g : G) (n : ℕ+) (r : ℚ) :
    galoisAut.galoisAut g (semigroup.α n (e_rep.e r)) =
      semigroup.α n (e_rep.e (GaloisActionData.actOnQ g r)) := by
  calc
    galoisAut.galoisAut g (semigroup.α n (e_rep.e r))
        = semigroup.α n (galoisAut.galoisAut g (e_rep.e r)) :=
          equivariance.equivariance g n (e_rep.e r)
    _ = semigroup.α n (e_rep.e (GaloisActionData.actOnQ g r)) := by
          rw [galoisAut.galoisAut_on_generator g r]

/--
Translated boundary readouts are compatible with the semigroup action on
cyclotomic generators whenever the Galois action and semigroup action commute.
-/
theorem BoundaryKMSReadout.galoisTranslate_semigroup_generator_readout
    (equivariance :
      GaloisSemigroupEquivariance C_comm e_rep semigroup G galoisAut)
    (Φ : BoundaryKMSReadout C_comm)
    (g : G) (n : ℕ+) (r : ℚ) :
    (BoundaryKMSReadout.galoisTranslate (e_rep := e_rep) Φ galoisAut g).read
        (semigroup.α n (e_rep.e r)) =
      Φ.read (semigroup.α n (e_rep.e (GaloisActionData.actOnQ g r))) := by
  simp [BoundaryKMSReadout.galoisTranslate,
    galois_semigroup_equivariance_generator_readout e_rep galoisAut semigroup
      equivariance g n r]

/-! ## 4. Algebraic cyclotomic ground-state separation -/

/--
Algebraic cyclotomic faithful separation of zero-temperature branches.

This is the postulate-free core of the proposed `Q_ab` argument.  It does not
construct `Q_ab`, roots of unity, or the complex embedding.  Instead, it proves
the formal implication needed by the Bost--Connes symmetry-breaking corridor:
if the phase observables evaluate as

`φ_g(e(r)) = ι(g • χ(r))`,

if `ι` is injective, and if the image of `χ` faithfully detects the Galois
action, then distinct Galois parameters give distinct boundary states.
-/
theorem algebraic_cyclotomic_ground_states_faithful
    {G₀ Qab Obs : Type*} [Group G₀] [MulAction G₀ Qab]
    (χ : ℚ → Qab) (ι : Qab → ℂ) (phase : ℚ → Obs)
    (φ₁ φ₂ : Obs → ℂ) (g₁ g₂ : G₀)
    (h_state1 : ∀ r : ℚ, φ₁ (phase r) = ι (g₁ • χ r))
    (h_state2 : ∀ r : ℚ, φ₂ (phase r) = ι (g₂ • χ r))
    (h_embedding_inj : Function.Injective ι)
    (h_chi_generating : ∀ g : G₀, (∀ r : ℚ, g • χ r = χ r) → g = 1)
    (hne : g₁ ≠ g₂) :
    φ₁ ≠ φ₂ := by
  intro hφ
  have hpoint (r : ℚ) : g₁ • χ r = g₂ • χ r := by
    apply h_embedding_inj
    calc
      ι (g₁ • χ r) = φ₁ (phase r) := (h_state1 r).symm
      _ = φ₂ (phase r) := by rw [hφ]
      _ = ι (g₂ • χ r) := h_state2 r
  have hfix : ∀ r : ℚ, (g₂⁻¹ * g₁) • χ r = χ r := by
    intro r
    calc
      (g₂⁻¹ * g₁) • χ r = g₂⁻¹ • (g₁ • χ r) := by
        simp [mul_smul]
      _ = g₂⁻¹ • (g₂ • χ r) := by
        rw [hpoint r]
      _ = χ r := by
        simp [← mul_smul]
  have hid : g₂⁻¹ * g₁ = 1 :=
    h_chi_generating (g₂⁻¹ * g₁) hfix
  have hg : g₁ = g₂ := by
    calc
      g₁ = g₂ * (g₂⁻¹ * g₁) := by group
      _ = g₂ * 1 := by rw [hid]
      _ = g₂ := by group
  exact hne hg

/-! ## 5. Hecke--Cuntz crossed-product ground-state separation -/

/--
Algebraic extreme ground state on the Hecke--Cuntz crossed product.

The phase observables are not abstract here: they are the crossed-product
embedding of the cyclotomic boundary generators, `ι(e(r))`.

The field `eval_shift` records the zero-temperature ground-state condition:
nontrivial positive-integer Cuntz shifts have zero left expectation against
all observables.  This is a proof-carrying assumption, not an analytic
classification of all KMS states.
-/
def HeckeCuntzExtremeGroundState
    {G₀ Qab : Type*} [Group G₀] [MulAction G₀ Qab]
    (χ : ℚ → Qab) (ιab : Qab → ℂ)
    (g : G₀) (φ : Op → ℂ) : Prop :=
  φ 1 = 1 ∧
    (∀ r : ℚ, φ (crossed.ι (e_rep.e r)) = ιab (g • χ r)) ∧
      (∀ (n : ℕ+) (A : Op), n ≠ 1 → φ (BostConnesKMS.S cuntz n * A) = 0)

namespace HeckeCuntzExtremeGroundState

variable
    {G₀ Qab : Type*} [Group G₀] [MulAction G₀ Qab]
    {χ : ℚ → Qab} {ιab : Qab → ℂ}
    {g : G₀} {φ : Op → ℂ}

/-- Readout of the embedded cyclotomic phase observable. -/
theorem phase_readout
    (H : HeckeCuntzExtremeGroundState
      (e_rep := e_rep) (semigroup := semigroup) (cuntz := cuntz) (crossed := crossed)
      χ ιab g φ)
    (r : ℚ) :
    φ (crossed.ι (e_rep.e r)) = ιab (g • χ r) :=
  H.2.1 r

/-- Nontrivial Hecke--Cuntz shifts annihilate embedded phase observables. -/
theorem nontrivial_shift_phase_zero
    (H : HeckeCuntzExtremeGroundState
      (e_rep := e_rep) (semigroup := semigroup) (cuntz := cuntz) (crossed := crossed)
      χ ιab g φ)
    {n : ℕ+} (hn : n ≠ 1) (r : ℚ) :
    φ (BostConnesKMS.S cuntz n * crossed.ι (e_rep.e r)) = 0 :=
  H.2.2 n (crossed.ι (e_rep.e r)) hn

end HeckeCuntzExtremeGroundState

/--
Faithful separation of Hecke--Cuntz crossed-product extreme ground states.

This is the crossed-product specialization of
`algebraic_cyclotomic_ground_states_faithful`: if two ground states evaluate
the embedded phase generators by two distinct algebraic Galois parameters,
and the cyclotomic values generate the action after an injective complex
embedding, then the two state functionals on the crossed product are distinct.
-/
theorem heckeCuntz_extreme_ground_states_faithful
    {G₀ Qab : Type*} [Group G₀] [MulAction G₀ Qab]
    (χ : ℚ → Qab) (ιab : Qab → ℂ)
    (φ₁ φ₂ : Op → ℂ) (g₁ g₂ : G₀)
    (h_state1 : HeckeCuntzExtremeGroundState
      (e_rep := e_rep) (semigroup := semigroup) (cuntz := cuntz) (crossed := crossed)
      χ ιab g₁ φ₁)
    (h_state2 : HeckeCuntzExtremeGroundState
      (e_rep := e_rep) (semigroup := semigroup) (cuntz := cuntz) (crossed := crossed)
      χ ιab g₂ φ₂)
    (h_embedding_inj : Function.Injective ιab)
    (h_chi_generating : ∀ g : G₀, (∀ r : ℚ, g • χ r = χ r) → g = 1)
    (hne : g₁ ≠ g₂) :
    φ₁ ≠ φ₂ :=
  algebraic_cyclotomic_ground_states_faithful
    (χ := χ) (ι := ιab) (phase := fun r : ℚ => crossed.ι (e_rep.e r))
    (φ₁ := φ₁) (φ₂ := φ₂) (g₁ := g₁) (g₂ := g₂)
    h_state1.2.1 h_state2.2.1 h_embedding_inj h_chi_generating hne

/-! ## 6. Inductive compactification, cocycle limit, and rational phase readout -/

/--
Compactified thermal coordinates transport along a finite induction chain and
then into an explicit limit image.

This is a Bost--Connes-facing name for the existing
`ThermalCompactRecurrence.compactifiedRelation_limit_image_chain` owner.  The
result remains purely algebraic: it is a statement about cross-multiplied
Cayley/Mobius relations in rings and ring homomorphisms, not an analytic
completion theorem.
-/
theorem compactified_cyclotomic_induction_limit_image_chain
    {Stage : Nat → Type*} [∀ n : Nat, CommRing (Stage n)]
    {Limit : Type*} [CommRing Limit]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (q T : ∀ n : Nat, Stage n)
    (h0 : CompactifiedRelation (q 0) (T 0))
    (hq : ∀ n : Nat, q (n + 1) = bond n (q n))
    (hT : ∀ n : Nat, T (n + 1) = bond n (T n)) :
    ∀ n : Nat, CompactifiedRelation (toLimit n (q n)) (toLimit n (T n)) :=
  compactifiedRelation_limit_image_chain bond toLimit q T h0 hq hT

/--
Normal-cone compatibility, stationary Connes-cocycle law at the direct-limit
readout, and rational phase periodicity in the crossed product.

This is the finite, repo-owned part of the requested induction/cocycle/normal
cone bridge.  It combines:

* `cone_system_compatible` from the inductive normal-cone tower;
* `DAG.AnalyticBridge.connes_cocycle_at_limit` from the direct-limit cocycle
  readout;
* `e(r + 1) = e(r)` for rational cyclotomic phases; and
* preservation of that rational phase equality after embedding into the
  Hecke--Cuntz crossed product.
-/
theorem normalCone_cocycle_limit_preserves_rational_phase_periodicity
    (n : ℕ)
    (A : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n)
    (s t : ℝ) (r : ℚ) :
    InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n A =
        InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (n + 1)
          (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n A) ∧
      DAG.AnalyticBridge.uhfModularFlow (s + t) =
        DAG.AnalyticBridge.uhfModularFlow s ∘ DAG.AnalyticBridge.uhfModularFlow t ∧
      e_rep.e (r + 1) = e_rep.e r ∧
      crossed.ι (e_rep.e (r + 1)) = crossed.ι (e_rep.e r) := by
  refine ⟨cone_system_compatible n A,
    DAG.AnalyticBridge.connes_cocycle_at_limit s t, e_rep.e_periodic r, ?_⟩
  rw [e_rep.e_periodic r]

end InfoGeometry.Canonical.BostConnesSymmetryBreaking
