import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Order.Directed
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Infinitesimal Modular Derivation δ_∞ on the C*-Inductive Colimit 𝒜_∞

Formalizes the construction of the infinitesimal generator
  `δ_∞ = (d/dt σ_{∞, t})|_{t=0}`
as an algebraic derivation on the inductive colimit of algebras `𝒜_∞ = injlim 𝒜_i`.

Mathematical Structure:
  1. `DirectedAlgSystem`: Directed system of R-algebras over `(I, ≤)`.
  2. `LocalDerivationSystem`: Family of local derivations `δ_i : A_i →ₗ[R] A_i`
     satisfying the Leibniz rule `δ_i(xy) = δ_i(x)y + xδ_i(y)` and intertwining
     with transition maps `f_{ij} ∘ δ_i = δ_j ∘ f_{ij}`.
  3. `AlgColimitCocone`: Colimit cocone with canonical inclusions `ι_i : A_i →ₐ[R] A_inf`.
  4. `colimitDerivVal`: The canonically lifted operator `δ_∞ : 𝒜_∞ → 𝒜_∞`
     satisfying `δ_∞ (ι_i x_i) = ι_i (δ_i x_i)`.
  5. `colimitDerivLinearMap`: Bundled `A_inf →ₗ[R] A_inf` with full R-linearity
     and the global Leibniz identity.
  6. `colimitDeriv_comm_flow`: Commutation with the lifted modular flow:
     `σ_{∞, t} ∘ δ_∞ = δ_∞ ∘ σ_{∞, t}`.

All proofs are complete with 0 `sorry`s, 0 custom axioms, and 0 placeholders.
-/

noncomputable section

namespace InfoGeometry.Modular.ColimitDerivation

variable {R : Type*} [CommRing R]

/-! =========================================================================
    1. Directed System of Algebras & Transition Maps
    ========================================================================= -/

/-- Directed system of R-algebras over a preorder index set `I`. -/
structure DirectedAlgSystem (I : Type*) [Preorder I] (A : I → Type*)
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)] where
  map : ∀ {i j : I}, i ≤ j → (A i →ₐ[R] A j)
  map_self : ∀ (i : I) (x : A i), map (le_refl i) x = x
  map_trans : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : A i),
    map (le_trans hij hjk) x = map hjk (map hij x)

/-! =========================================================================
    2. Local Infinitesimal Derivation System
    ========================================================================= -/

/--
A compatible family of local derivations {δ_i}_{i ∈ I}:
Each stage carries an R-linear map `δ_i : A_i →ₗ[R] A_i` satisfying the Leibniz rule
and intertwining with transition maps.
-/
structure LocalDerivationSystem (I : Type*) [Preorder I] (A : I → Type*)
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)] (sys : DirectedAlgSystem (R := R) I A) where
  deriv : ∀ (i : I), A i →ₗ[R] A i
  deriv_leibniz : ∀ (i : I) (x y : A i), deriv i (x * y) = deriv i x * y + x * deriv i y
  intertwine : ∀ {i j : I} (hij : i ≤ j) (x : A i),
    sys.map hij (deriv i x) = deriv j (sys.map hij x)

/-! =========================================================================
    3. Universal Colimit Cocone
    ========================================================================= -/

/-- Universal colimit cocone for the directed algebra system. -/
structure AlgColimitCocone (I : Type*) [Preorder I] (A : I → Type*)
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)] (sys : DirectedAlgSystem (R := R) I A)
    (A_inf : Type*) [Ring A_inf] [Algebra R A_inf] where
  inr : ∀ (i : I), A i →ₐ[R] A_inf
  inr_comm : ∀ {i j : I} (hij : i ≤ j) (x : A i), inr j (sys.map hij x) = inr i x
  surj_dense : ∀ (x : A_inf), ∃ (i : I) (xi : A i), inr i xi = x
  inr_inj : ∀ {i : I} (x y : A i), inr i x = inr i y →
    ∃ (k : I) (hik : i ≤ k), sys.map hik x = sys.map hik y

/-! =========================================================================
    4. Construction of the Colimit Derivation δ_∞
    ========================================================================= -/

variable {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
variable {A : I → Type*}
variable [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
variable (sys : DirectedAlgSystem (R := R) I A)
variable (dsys : LocalDerivationSystem (R := R) I A sys)
variable {A_inf : Type*} [Ring A_inf] [Algebra R A_inf]
variable (colim : AlgColimitCocone (R := R) I A sys A_inf)

/-! Inner derivations are the native operator-surprisal instance of the local
    derivation interface. -/

def innerDerivation
    (K : ∀ i, A i) (i : I) : A i →ₗ[R] A i :=
  LinearMap.mulLeft R (K i) - LinearMap.mulRight R (K i)

theorem innerDerivation_apply
    (K : ∀ i, A i) (i : I) (x : A i) :
    innerDerivation (R := R) K i x = K i * x - x * K i := by
  rfl

theorem innerDerivation_leibniz
    (K : ∀ i, A i) (i : I) (x y : A i) :
    innerDerivation (R := R) K i (x * y) =
      innerDerivation (R := R) K i x * y + x * innerDerivation (R := R) K i y := by
  simp only [innerDerivation_apply, mul_assoc, sub_mul, mul_sub]
  noncomm_ring

def innerDerivationSystem
    (K : ∀ i, A i)
    (hK : ∀ {i j : I} (hij : i ≤ j), sys.map hij (K i) = K j) :
    LocalDerivationSystem (R := R) I A sys where
  deriv := innerDerivation (R := R) K
  deriv_leibniz := innerDerivation_leibniz (R := R) K
  intertwine := by
    intro i j hij x
    rw [innerDerivation_apply (R := R), innerDerivation_apply (R := R)]
    rw [map_sub, map_mul, map_mul, hK hij]

/-- Pointwise evaluation of the global derivation: `δ_∞ (ι_i x_i) = ι_i (δ_i x_i)`. -/
def colimitDerivVal (x : A_inf) : A_inf :=
  let rep := colim.surj_dense x
  colim.inr rep.choose (dsys.deriv rep.choose rep.choose_spec.choose)

/--
LEMMA: Intertwining of the lifted derivation with canonical injections:
  `δ_∞ (ι_i x) = ι_i (δ_i x)`
-/
theorem colimitDerivVal_inr (i : I) (x : A i) :
    colimitDerivVal sys dsys colim (colim.inr i x) = colim.inr i (dsys.deriv i x) := by
  dsimp [colimitDerivVal]
  set rep := colim.surj_dense (colim.inr i x)
  have h_eq : colim.inr rep.choose rep.choose_spec.choose = colim.inr i x :=
    rep.choose_spec.choose_spec
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge rep.choose i
  have h_eq_k : colim.inr k (sys.map hik rep.choose_spec.choose) = colim.inr k (sys.map hjk x) := by
    rw [colim.inr_comm hik, colim.inr_comm hjk, h_eq]
  obtain ⟨m, hkm, h_eq_m⟩ := colim.inr_inj _ _ h_eq_k
  have h_eq_map : sys.map (le_trans hik hkm) rep.choose_spec.choose = sys.map (le_trans hjk hkm) x := by
    rw [sys.map_trans hik hkm, sys.map_trans hjk hkm, h_eq_m]
  calc
    colim.inr rep.choose (dsys.deriv rep.choose rep.choose_spec.choose)
      = colim.inr m (sys.map (le_trans hik hkm) (dsys.deriv rep.choose rep.choose_spec.choose)) := by
        rw [colim.inr_comm (le_trans hik hkm)]
    _ = colim.inr m (dsys.deriv m (sys.map (le_trans hik hkm) rep.choose_spec.choose)) := by
        rw [dsys.intertwine]
    _ = colim.inr m (dsys.deriv m (sys.map (le_trans hjk hkm) x)) := by
        rw [h_eq_map]
    _ = colim.inr m (sys.map (le_trans hjk hkm) (dsys.deriv i x)) := by
        rw [dsys.intertwine]
    _ = colim.inr i (dsys.deriv i x) := by
        rw [colim.inr_comm (le_trans hjk hkm)]

/- Finite-stage readout for the operator-surprisal inner derivation family. -/
theorem colimitInnerDerivation_inr
    (K : ∀ i, A i)
    (hK : ∀ {i j : I} (hij : i ≤ j), sys.map hij (K i) = K j)
    (i : I) (x : A i) :
    colimitDerivVal sys (innerDerivationSystem sys K hK) colim
        (colim.inr i x) =
      colim.inr i (K i * x - x * K i) := by
  rw [colimitDerivVal_inr]
  rfl

/-! =========================================================================
    5. Proof of the Leibniz Rule & Linear Properties
    ========================================================================= -/

/-- Additivity: `δ_∞(x + y) = δ_∞(x) + δ_∞(y)`. -/
theorem colimitDeriv_add (x y : A_inf) :
    colimitDerivVal sys dsys colim (x + y) =
      colimitDerivVal sys dsys colim x + colimitDerivVal sys dsys colim y := by
  obtain ⟨i, xi, rfl⟩ := colim.surj_dense x
  obtain ⟨j, yj, rfl⟩ := colim.surj_dense y
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  rw [← colim.inr_comm hik, ← colim.inr_comm hjk, ← map_add (colim.inr k),
      colimitDerivVal_inr sys dsys colim k (sys.map hik xi + sys.map hjk yj),
      map_add (dsys.deriv k), map_add (colim.inr k),
      ← colimitDerivVal_inr sys dsys colim k (sys.map hik xi),
      ← colimitDerivVal_inr sys dsys colim k (sys.map hjk yj),
      colim.inr_comm hik, colim.inr_comm hjk]

/-- Scalar Multiplication: `δ_∞(r • x) = r • δ_∞(x)`. -/
theorem colimitDeriv_smul (r : R) (x : A_inf) :
    colimitDerivVal sys dsys colim (r • x) = r • colimitDerivVal sys dsys colim x := by
  obtain ⟨i, xi, rfl⟩ := colim.surj_dense x
  rw [← map_smul (colim.inr i),
      colimitDerivVal_inr sys dsys colim i (r • xi),
      map_smul (dsys.deriv i), map_smul (colim.inr i),
      colimitDerivVal_inr sys dsys colim i xi]

/--
MAIN THEOREM (Global Leibniz Rule on 𝒜_∞):
  `δ_∞(xy) = δ_∞(x)y + xδ_∞(y)`
-/
theorem colimitDeriv_leibniz (x y : A_inf) :
    colimitDerivVal sys dsys colim (x * y) =
      colimitDerivVal sys dsys colim x * y + x * colimitDerivVal sys dsys colim y := by
  obtain ⟨i, xi, rfl⟩ := colim.surj_dense x
  obtain ⟨j, yj, rfl⟩ := colim.surj_dense y
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hx : colim.inr i xi = colim.inr k (sys.map hik xi) := (colim.inr_comm hik xi).symm
  have hy : colim.inr j yj = colim.inr k (sys.map hjk yj) := (colim.inr_comm hjk yj).symm
  rw [hx, hy, ← map_mul (colim.inr k),
      colimitDerivVal_inr sys dsys colim k (sys.map hik xi * sys.map hjk yj),
      dsys.deriv_leibniz k,
      map_add (colim.inr k), map_mul (colim.inr k), map_mul (colim.inr k),
      ← colimitDerivVal_inr sys dsys colim k (sys.map hik xi),
      ← colimitDerivVal_inr sys dsys colim k (sys.map hjk yj),
      ← hx, ← hy]

/-! =========================================================================
    6. Bundled Linear Derivation Map on the Inductive Colimit
    ========================================================================= -/

/--
The modular infinitesimal generator `δ_∞` bundled as an R-linear map `A_inf →ₗ[R] A_inf`.
-/
def colimitDerivLinearMap : A_inf →ₗ[R] A_inf where
  toFun := colimitDerivVal sys dsys colim
  map_add' := colimitDeriv_add sys dsys colim
  map_smul' := colimitDeriv_smul sys dsys colim

@[simp]
theorem colimitDerivLinearMap_apply (x : A_inf) :
    colimitDerivLinearMap sys dsys colim x = colimitDerivVal sys dsys colim x :=
  rfl

/--
THEOREM (Global Leibniz Rule for Bundled Linear Map):
  `δ_∞(xy) = δ_∞(x)y + xδ_∞(y)`
-/
theorem colimitDerivLinearMap_leibniz (x y : A_inf) :
    colimitDerivLinearMap sys dsys colim (x * y) =
      colimitDerivLinearMap sys dsys colim x * y + x * colimitDerivLinearMap sys dsys colim y :=
  colimitDeriv_leibniz sys dsys colim x y

/-! =========================================================================
    7. Commutation with the Modular Automorphism Flow
    ========================================================================= -/

variable (flow_inf : ℝ → A_inf →ₐ[R] A_inf)
variable (local_flow : ∀ (i : I), ℝ → A i →ₐ[R] A i)

/--
THEOREM (Infinitesimal-Flow Commutativity):
If local derivations commute with local modular flows `[δ_i, σ_{i, t}] = 0`,
then the global derivation commutes with the global colimit flow:
  `σ_{∞, t} (δ_∞ x) = δ_∞ (σ_{∞, t} x)`
-/
theorem colimitDeriv_comm_flow
    (h_lift : ∀ (t : ℝ) (i : I) (x : A i), flow_inf t (colim.inr i x) = colim.inr i (local_flow i t x))
    (h_local_comm : ∀ (i : I) (t : ℝ) (x : A i), local_flow i t (dsys.deriv i x) = dsys.deriv i (local_flow i t x))
    (t : ℝ) (x : A_inf) :
    flow_inf t (colimitDerivLinearMap sys dsys colim x) =
      colimitDerivLinearMap sys dsys colim (flow_inf t x) := by
  obtain ⟨i, xi, rfl⟩ := colim.surj_dense x
  dsimp [colimitDerivLinearMap]
  rw [colimitDerivVal_inr sys dsys colim i xi,
      h_lift t i (dsys.deriv i xi),
      h_local_comm i t xi,
      ← colimitDerivVal_inr sys dsys colim i (local_flow i t xi),
      ← h_lift t i xi]

end InfoGeometry.Modular.ColimitDerivation
