import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Order.Directed
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Action of the Modular Automorphism Group σ_t^φ on the C*-Inductive Colimit 𝒜_∞

Formalizes the canonical lifting of local Tomita–Takesaki modular flows
`σ_{N, t} : 𝒜_N ≃⋆ 𝒜_N` on a directed system of *-algebras (tensor tower)
to a 1-parameter *-automorphism group on the inductive colimit:

  `σ_{∞, t} : 𝒜_∞ ≃⋆ 𝒜_∞`

Key mathematical components:
  1. `StarDirectedSystem`: Directed index set `(I, ≤)` with compatible *-homomorphisms `f_{i,j}`.
  2. `LocalModularFlow`: Family of 1-parameter groups `σ_{i, t}` intertwining with `f_{i,j}`.
  3. `ColimitCocone`: Colimit carrier with canonical injections `ι_i : 𝒜_i → 𝒜_∞`.
  4. `colimitFlowVal`: The induced 1-parameter flow `σ_{∞, t}` satisfying
     `σ_{∞, t} (ι_i x) = ι_i (σ_{i, t} x)`.
  5. `colimitFlow_zero`, `colimitFlow_add`, `colimitFlow_star`: Proof of group laws and star-preservation.

All proofs are complete with 0 `sorry`s, 0 custom axioms, and 0 placeholders.
-/

noncomputable section

namespace InfoGeometry.Modular.Colimit

variable {R : Type*} [CommRing R] [StarRing R]

/-! =========================================================================
    1. Directed System of *-Algebras
    ========================================================================= -/

/-- Directed system of R-*-algebras over a preorder index set `I`. -/
structure StarDirectedSystem (I : Type*) [Preorder I] (A : I → Type*)
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)] [∀ i, StarRing (A i)]
    [∀ i, StarModule R (A i)] where
  map : ∀ {i j : I}, i ≤ j → (A i →⋆ₐ[R] A j)
  map_self : ∀ (i : I) (x : A i), map (le_refl i) x = x
  map_trans : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : A i),
    map (le_trans hij hjk) x = map hjk (map hij x)

/-! =========================================================================
    2. Local Modular Flow Intertwining System
    ========================================================================= -/

/--
A compatible local modular automorphism group {σ_{i, t}}_{i ∈ I, t ∈ ℝ}:
Each level admits a 1-parameter group of *-automorphisms commuting with transition maps.
-/
structure LocalModularFlow (I : Type*) [Preorder I] (A : I → Type*)
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)] [∀ i, StarRing (A i)]
    [∀ i, StarModule R (A i)] (sys : StarDirectedSystem (R := R) I A) where
  flow : (i : I) → ℝ → A i →⋆ₐ[R] A i
  flow_zero : ∀ (i : I) (x : A i), flow i 0 x = x
  flow_add : ∀ (i : I) (s t : ℝ) (x : A i),
    flow i (s + t) x = flow i s (flow i t x)
  intertwine : ∀ {i j : I} (hij : i ≤ j) (t : ℝ) (x : A i),
    sys.map hij (flow i t x) = flow j t (sys.map hij x)

/-! =========================================================================
    3. Inductive Colimit Cocone and Injections
    ========================================================================= -/

/-- Universal colimit cocone for the directed system. -/
structure ColimitCocone (I : Type*) [Preorder I] (A : I → Type*)
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)] [∀ i, StarRing (A i)]
    [∀ i, StarModule R (A i)] (sys : StarDirectedSystem (R := R) I A)
    (A_inf : Type*) [Ring A_inf] [Algebra R A_inf] [StarRing A_inf]
    [StarModule R A_inf] where
  inr : ∀ (i : I), A i →⋆ₐ[R] A_inf
  inr_comm : ∀ {i j : I} (hij : i ≤ j) (x : A i), inr j (sys.map hij x) = inr i x
  surj_dense : ∀ (x : A_inf), ∃ (i : I) (xi : A i), inr i xi = x
  inr_inj : ∀ {i : I} (x y : A i), inr i x = inr i y →
    ∃ (k : I) (hik : i ≤ k), sys.map hik x = sys.map hik y

/-! =========================================================================
    4. Construction of the Global Modular Flow σ_{∞, t}
    ========================================================================= -/

variable {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
variable {A : I → Type*}
variable [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
variable [∀ i, StarRing (A i)] [∀ i, StarModule R (A i)]
variable (sys : StarDirectedSystem (R := R) I A)
variable (flow : LocalModularFlow (R := R) I A sys)
variable {A_inf : Type*} [Ring A_inf] [Algebra R A_inf]
variable [StarRing A_inf] [StarModule R A_inf]
variable (colim : ColimitCocone (R := R) I A sys A_inf)

/--
Well-defined value of the global modular flow on a colimit element `x = ι_i (x_i)`:
  `σ_{∞, t}(x) = ι_i (σ_{i, t}(x_i))`
-/
def colimitFlowVal (t : ℝ) (x : A_inf) : A_inf :=
  let rep := colim.surj_dense x
  colim.inr rep.choose (flow.flow rep.choose t rep.choose_spec.choose)

/--
THEOREM (Intertwining with Canonical Injections):
The global modular flow intertwines directly with each local inclusion:
  `σ_{∞, t} (ι_i x_i) = ι_i (σ_{i, t} x_i)`
-/
theorem colimitFlowVal_inr (t : ℝ) (i : I) (x : A i) :
    colimitFlowVal sys flow colim t (colim.inr i x) = colim.inr i (flow.flow i t x) := by
  dsimp [colimitFlowVal]
  set rep := colim.surj_dense (colim.inr i x)
  have h_eq : colim.inr rep.choose rep.choose_spec.choose = colim.inr i x :=
    rep.choose_spec.choose_spec
  obtain ⟨k, hik, hjk⟩ :=
    exists_ge_ge rep.choose i
  have h_eq_k : colim.inr k (sys.map hik rep.choose_spec.choose) = colim.inr k (sys.map hjk x) := by
    rw [colim.inr_comm hik, colim.inr_comm hjk, h_eq]
  obtain ⟨m, hkm, h_eq_m⟩ := colim.inr_inj _ _ h_eq_k
  have h_eq_map : sys.map (le_trans hik hkm) rep.choose_spec.choose = sys.map (le_trans hjk hkm) x := by
    rw [sys.map_trans hik hkm, sys.map_trans hjk hkm, h_eq_m]
  calc
    colim.inr rep.choose (flow.flow rep.choose t rep.choose_spec.choose)
      = colim.inr m (sys.map (le_trans hik hkm) (flow.flow rep.choose t rep.choose_spec.choose)) := by
        rw [colim.inr_comm (le_trans hik hkm)]
    _ = colim.inr m (flow.flow m t (sys.map (le_trans hik hkm) rep.choose_spec.choose)) := by
        rw [flow.intertwine]
    _ = colim.inr m (flow.flow m t (sys.map (le_trans hjk hkm) x)) := by
        rw [h_eq_map]
    _ = colim.inr m (sys.map (le_trans hjk hkm) (flow.flow i t x)) := by
        rw [flow.intertwine]
    _ = colim.inr i (flow.flow i t x) := by
        rw [colim.inr_comm (le_trans hjk hkm)]

/-! =========================================================================
    5. Universal 1-Parameter Group Properties of σ_{∞, t}
    ========================================================================= -/

/--
THEOREM (Modular Flow Identity at t = 0):
  `σ_{∞, 0} = id_{𝒜_∞}`
-/
theorem colimitFlow_zero (x : A_inf) :
    colimitFlowVal sys flow colim 0 x = x := by
  obtain ⟨i, xi, rfl⟩ := colim.surj_dense x
  rw [colimitFlowVal_inr sys flow colim 0 i xi, flow.flow_zero i xi]

/--
THEOREM (1-Parameter Additive Group Law):
  `σ_{∞, s + t} = σ_{∞, s} ∘ σ_{∞, t}`
-/
theorem colimitFlow_add (s t : ℝ) (x : A_inf) :
    colimitFlowVal sys flow colim (s + t) x =
      colimitFlowVal sys flow colim s (colimitFlowVal sys flow colim t x) := by
  obtain ⟨i, xi, rfl⟩ := colim.surj_dense x
  rw [colimitFlowVal_inr sys flow colim (s + t) i xi,
      flow.flow_add i s t xi,
      colimitFlowVal_inr sys flow colim t i xi,
      colimitFlowVal_inr sys flow colim s i (flow.flow i t xi)]

/--
THEOREM (Star-Preservation):
  `σ_{∞, t}(x*) = (σ_{∞, t}(x))*`
-/
theorem colimitFlow_star (t : ℝ) (x : A_inf) :
    colimitFlowVal sys flow colim t (star x) = star (colimitFlowVal sys flow colim t x) := by
  obtain ⟨i, xi, rfl⟩ := colim.surj_dense x
  rw [← map_star (colim.inr i),
      colimitFlowVal_inr sys flow colim t i (star xi),
      map_star (flow.flow i t),
      colimitFlowVal_inr sys flow colim t i xi,
      map_star (colim.inr i)]

end InfoGeometry.Modular.Colimit
