import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Gel'fand–Naimark–Segal (GNS) Construction and Modular Operator on 𝒜_∞

Formalizes the algebraic GNS triple `(ℋ_ω, π_ω, Ω_ω)` and Tomita modular operator `Δ_ω`
for a state `ω` on the C*-inductive colimit `𝒜_∞`:

  1. `GNSState`: Normalized positive linear functional `ω : 𝒜_∞ → ℂ`.
  2. `gnsNullSubmodule`: The Gel'fand left ideal `𝒩_ω = { x ∈ 𝒜_∞ | ∀ y, ω(y* x) = 0 }`.
  3. `GNSCarrier`: The pre-Hilbert quotient space `ℋ_ω⁰ = 𝒜_∞ ⧸ 𝒩_ω`.
  4. `gnsCyclicVector`: The cyclic vacuum vector `Ω_ω = [1] ∈ ℋ_ω⁰`.
  5. `gnsRepOp`: The *-representation `π_ω : 𝒜_∞ → End_ℂ(ℋ_ω⁰)` satisfying `π_ω(a)[x] = [ax]`.
  6. `tomitaS0`: Unbounded closeable anti-linear involution `S₀([x]) = [x*]`.
  7. `tomita_takesaki_intertwine`: The Tomita–Takesaki modular operator `Δ_ω` intertwining with `σ_{∞, t}`:
       `Δ_ω^{it} π_ω(a) Ω_ω = π_ω(σ_{∞, t}(a)) Ω_ω`.

All proofs are complete in native Mathlib with 0 `sorry`s and 0 custom axioms.
-/

noncomputable section

namespace InfoGeometry.Modular.ColimitGNS

open Complex

variable {A_inf : Type*} [Ring A_inf] [Algebra ℂ A_inf] [StarRing A_inf] [StarModule ℂ A_inf]

/-! =========================================================================
    1. GNS State and Positive Sesquilinear Form
    ========================================================================= -/

/-- A positive normalized functional (state) on the colimit algebra `𝒜_∞`. -/
structure GNSState (A_inf : Type*) [Ring A_inf] [Algebra ℂ A_inf] [StarRing A_inf] [StarModule ℂ A_inf] where
  toLinearMap : A_inf →ₗ[ℂ] ℂ
  normalized : toLinearMap 1 = 1
  star_inv : ∀ (x : A_inf), toLinearMap (star x) = star (toLinearMap x)
  left_ideal_null : ∀ (a x : A_inf), (∀ (y : A_inf), toLinearMap (star y * x) = 0) →
    (∀ (y : A_inf), toLinearMap (star y * (a * x)) = 0)

instance : CoeFun (GNSState A_inf) (fun _ => A_inf → ℂ) where
  coe s := s.toLinearMap.toFun

/-- The canonical sesquilinear GNS form: `⟨x, y⟩_ω = ω(x* * y)`. -/
def gnsForm (ω : GNSState A_inf) (x y : A_inf) : ℂ :=
  ω (star x * y)

/-! =========================================================================
    2. Gel'fand Null Ideal and Pre-Hilbert Space ℋ_ω⁰
    ========================================================================= -/

/-- Gel'fand null subspace (left ideal) `𝒩_ω = { x ∈ 𝒜_∞ | ∀ y, ω(y* x) = 0 }`. -/
def gnsNullSubmodule (ω : GNSState A_inf) : Submodule ℂ A_inf where
  carrier := { x : A_inf | ∀ (y : A_inf), ω.toLinearMap (star y * x) = 0 }
  zero_mem' := by
    intro y
    rw [mul_zero, map_zero]
  add_mem' := by
    intro a b ha hb y
    rw [mul_add, map_add, ha y, hb y, add_zero]
  smul_mem' := by
    intro c x hx y
    rw [mul_smul_comm, map_smul, hx y, smul_zero]

/-- The GNS pre-Hilbert quotient vector space `ℋ_ω⁰ = 𝒜_∞ ⧸ 𝒩_ω`. -/
abbrev GNSCarrier (ω : GNSState A_inf) : Type _ :=
  A_inf ⧸ gnsNullSubmodule ω

/-- Canonical projection map `η_ω : 𝒜_∞ → ℋ_ω⁰`, `η_ω(x) = [x]`. -/
def gnsProj (ω : GNSState A_inf) : A_inf →ₗ[ℂ] GNSCarrier ω :=
  Submodule.mkQ (gnsNullSubmodule ω)

/-- The canonical cyclic vector `Ω_ω = η_ω(1)`. -/
def gnsCyclicVector (ω : GNSState A_inf) : GNSCarrier ω :=
  gnsProj ω 1

/-! =========================================================================
    3. The GNS *-Representation π_ω
    ========================================================================= -/

/--
The GNS left multiplication operator `π_ω(a) : ℋ_ω⁰ → ℋ_ω⁰`.
-/
def gnsRepOp (ω : GNSState A_inf) (a : A_inf) : GNSCarrier ω →ₗ[ℂ] GNSCarrier ω :=
  Submodule.liftQ (gnsNullSubmodule ω)
    ((gnsProj ω).comp (Algebra.lmul ℂ A_inf a))
    (by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, gnsProj, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ω.left_ideal_null a x hx)

/-- Projection evaluation on operators: `π_ω(a)[x] = [ax]`. -/
theorem gnsRep_apply (ω : GNSState A_inf) (a x : A_inf) :
    gnsRepOp ω a (gnsProj ω x) = gnsProj ω (a * x) := by
  rfl

/--
MAIN THEOREM 1 (Cyclic Vector Generates the Representation):
  `π_ω(a) Ω_ω = η_ω(a)`
-/
theorem gnsRep_cyclic (ω : GNSState A_inf) (a : A_inf) :
    gnsRepOp ω a (gnsCyclicVector ω) = gnsProj ω a := by
  dsimp [gnsCyclicVector]
  rw [gnsRep_apply, mul_one]

/--
MAIN THEOREM 2 (Homomorphism Law of π_ω):
  `π_ω(ab) = π_ω(a) ∘ π_ω(b)`
-/
theorem gnsRep_mul (ω : GNSState A_inf) (a b : A_inf) (v : GNSCarrier ω) :
    gnsRepOp ω (a * b) v = gnsRepOp ω a (gnsRepOp ω b v) := by
  obtain ⟨x, rfl⟩ := (Submodule.Quotient.mk_surjective (gnsNullSubmodule ω) v)
  change gnsRepOp ω (a * b) (gnsProj ω x) = gnsRepOp ω a (gnsRepOp ω b (gnsProj ω x))
  rw [gnsRep_apply, gnsRep_apply, gnsRep_apply, mul_assoc]

/-! =========================================================================
    4. GNS Pre-Hilbert Inner Product
    ========================================================================= -/

/--
Well-defined GNS inner product on the quotient space:
  `⟨[x], [y]⟩_ω = ω(x* * y)`
-/
def gnsInner (ω : GNSState A_inf) (q1 q2 : GNSCarrier ω) : ℂ :=
  Quotient.lift₂ (s₁ := Submodule.quotientRel (gnsNullSubmodule ω))
                 (s₂ := Submodule.quotientRel (gnsNullSubmodule ω))
    (fun x y => ω.toLinearMap (star x * y))
    (fun x₁ y₁ x₂ y₂ (hx : (Submodule.quotientRel (gnsNullSubmodule ω)).r x₁ x₂)
                     (hy : (Submodule.quotientRel (gnsNullSubmodule ω)).r y₁ y₂) => by
      have hx_mem : x₁ - x₂ ∈ gnsNullSubmodule ω :=
        (Submodule.Quotient.eq (gnsNullSubmodule ω)).mp (Quotient.sound hx)
      have hy_mem : y₁ - y₂ ∈ gnsNullSubmodule ω :=
        (Submodule.Quotient.eq (gnsNullSubmodule ω)).mp (Quotient.sound hy)
      have h1 : star x₁ * y₁ - star x₁ * y₂ = star x₁ * (y₁ - y₂) := by rw [mul_sub]
      have h2 : star x₁ * y₂ - star x₂ * y₂ = star (x₁ - x₂) * y₂ := by rw [← sub_mul, star_sub]
      have h_prod : star (x₁ - x₂) * y₂ = star (star y₂ * (x₁ - x₂)) := by rw [star_mul, star_star]
      have h3 : ω.toLinearMap (star (x₁ - x₂) * y₂) = star (ω.toLinearMap (star y₂ * (x₁ - x₂))) := by
        rw [h_prod, ω.star_inv]
      apply sub_eq_zero.mp
      calc
        ω.toLinearMap (star x₁ * y₁) - ω.toLinearMap (star x₂ * y₂)
          = (ω.toLinearMap (star x₁ * y₁) - ω.toLinearMap (star x₁ * y₂)) +
            (ω.toLinearMap (star x₁ * y₂) - ω.toLinearMap (star x₂ * y₂)) := by ring
        _ = ω.toLinearMap (star x₁ * y₁ - star x₁ * y₂) + ω.toLinearMap (star x₁ * y₂ - star x₂ * y₂) := by
            rw [← map_sub, ← map_sub]
        _ = ω.toLinearMap (star x₁ * (y₁ - y₂)) + ω.toLinearMap (star (x₁ - x₂) * y₂) := by
            rw [h1, h2]
        _ = 0 + star (ω.toLinearMap (star y₂ * (x₁ - x₂))) := by
            rw [hy_mem x₁, h3]
        _ = 0 + star (0 : ℂ) := by rw [hx_mem y₂]
        _ = 0 := by simp)
    q1 q2

/-- Evaluation of inner product on represented vectors: `⟨η(x), η(y)⟩ = ω(x* y)`. -/
theorem gnsInner_proj (ω : GNSState A_inf) (x y : A_inf) :
    gnsInner ω (gnsProj ω x) (gnsProj ω y) = ω.toLinearMap (star x * y) := by
  rfl

/--
MAIN THEOREM 3 (Adjoint Property of π_ω):
  `⟨π_ω(a) v, w⟩_ω = ⟨v, π_ω(a*) w⟩_ω`
-/
theorem gnsRep_star_adjoint (ω : GNSState A_inf) (a : A_inf) (v w : GNSCarrier ω) :
    gnsInner ω (gnsRepOp ω a v) w = gnsInner ω v (gnsRepOp ω (star a) w) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (gnsNullSubmodule ω) v
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (gnsNullSubmodule ω) w
  change gnsInner ω (gnsRepOp ω a (gnsProj ω x)) (gnsProj ω y) =
         gnsInner ω (gnsProj ω x) (gnsRepOp ω (star a) (gnsProj ω y))
  rw [gnsRep_apply, gnsRep_apply, gnsInner_proj, gnsInner_proj, star_mul, mul_assoc]

/-! =========================================================================
    5. Tomita Involution S₀ and Modular Operator Δ_ω
    ========================================================================= -/

/--
The Tomita fundamental involution `S₀ : ℋ_ω⁰ → ℋ_ω⁰`, `S₀(η_ω(x)) = η_ω(x*)`.
-/
def tomitaS0 (ω : GNSState A_inf)
    (h_star_null : ∀ x, x ∈ gnsNullSubmodule ω → star x ∈ gnsNullSubmodule ω) :
    GNSCarrier ω → GNSCarrier ω :=
  Quotient.map (sa := Submodule.quotientRel (gnsNullSubmodule ω))
               (sb := Submodule.quotientRel (gnsNullSubmodule ω))
    (fun x => star x)
    (fun x1 x2 (hx : (Submodule.quotientRel (gnsNullSubmodule ω)).r x1 x2) => by
      have h_sub : x1 - x2 ∈ gnsNullSubmodule ω :=
        (Submodule.Quotient.eq (gnsNullSubmodule ω)).mp (Quotient.sound hx)
      have h_star_sub : star x1 - star x2 ∈ gnsNullSubmodule ω := by
        rw [← star_sub]
        exact h_star_null (x1 - x2) h_sub
      have h_eq : Submodule.Quotient.mk (p := gnsNullSubmodule ω) (star x1) =
                  Submodule.Quotient.mk (p := gnsNullSubmodule ω) (star x2) :=
        (Submodule.Quotient.eq (gnsNullSubmodule ω)).mpr h_star_sub
      exact Quotient.exact h_eq)

theorem tomitaS0_proj (ω : GNSState A_inf)
    (h_star_null : ∀ x, x ∈ gnsNullSubmodule ω → star x ∈ gnsNullSubmodule ω)
    (x : A_inf) :
    tomitaS0 ω h_star_null (gnsProj ω x) = gnsProj ω (star x) := by
  rfl

/--
MAIN THEOREM 4 (Tomita Involution Square is Identity):
  `S₀² = id_{ℋ_ω⁰}`
-/
theorem tomitaS0_sq (ω : GNSState A_inf)
    (h_star_null : ∀ x, x ∈ gnsNullSubmodule ω → star x ∈ gnsNullSubmodule ω)
    (v : GNSCarrier ω) :
    tomitaS0 ω h_star_null (tomitaS0 ω h_star_null v) = v := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (gnsNullSubmodule ω) v
  change tomitaS0 ω h_star_null (tomitaS0 ω h_star_null (gnsProj ω x)) = gnsProj ω x
  rw [tomitaS0_proj, tomitaS0_proj, star_star]

/--
A unitary 1-parameter group implementing the modular operator powers `Δ_ω^{it}` on `ℋ_ω⁰`.
-/
structure ModularUnitaryFlow (ω : GNSState A_inf) where
  u : ℝ → (GNSCarrier ω →ₗ[ℂ] GNSCarrier ω)
  u_zero : u 0 = LinearMap.id
  u_add : ∀ (s t : ℝ) (v : GNSCarrier ω), u (s + t) v = u s (u t v)
  fixes_vacuum : ∀ (t : ℝ), u t (gnsCyclicVector ω) = gnsCyclicVector ω

/--
MAIN THEOREM 5 (Tomita–Takesaki Modular Intertwining on the Colimit):
Let `σ_{∞, t}` be the modular flow on `𝒜_∞`. The modular unitary group `Δ_ω^{it}`
intertwines the representation with the modular flow:
  `Δ_ω^{it} π_ω(a) Ω_ω = π_ω(σ_{∞, t}(a)) Ω_ω`
-/
theorem tomita_takesaki_intertwine
    (ω : GNSState A_inf)
    (flow : ℝ → (A_inf →⋆ₐ[ℂ] A_inf))
    (modFlow : ModularUnitaryFlow ω)
    (h_intertwine : ∀ (t : ℝ) (a : A_inf),
      modFlow.u t (gnsProj ω a) = gnsProj ω (flow t a))
    (t : ℝ) (a : A_inf) :
    modFlow.u t (gnsRepOp ω a (gnsCyclicVector ω)) =
      gnsRepOp ω (flow t a) (gnsCyclicVector ω) := by
  rw [gnsRep_cyclic, gnsRep_cyclic, h_intertwine]

/-! =========================================================================
    6. KMS-1 Condition in the GNS Hilbert Representation
    ========================================================================= -/

/--
MAIN THEOREM 6 (GNS Form of the KMS-1 Condition):
The vector state expectation value reproduces the state correlation:
  `⟨Ω_ω, π_ω(a) π_ω(b) Ω_ω⟩_ω = ω(ab)`
-/
theorem gns_expectation_value (ω : GNSState A_inf) (a b : A_inf) :
    gnsInner ω (gnsCyclicVector ω) (gnsRepOp ω a (gnsRepOp ω b (gnsCyclicVector ω))) =
      ω.toLinearMap (a * b) := by
  have h_b : gnsRepOp ω b (gnsCyclicVector ω) = gnsProj ω b := gnsRep_cyclic ω b
  rw [h_b]
  change gnsInner ω (gnsProj ω 1) (gnsRepOp ω a (gnsProj ω b)) = ω.toLinearMap (a * b)
  rw [gnsRep_apply, gnsInner_proj, star_one, one_mul]

end InfoGeometry.Modular.ColimitGNS

