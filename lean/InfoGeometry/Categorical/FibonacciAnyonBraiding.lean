import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
import InfoGeometry.Clifford.FibonacciCl55Carrier

/-!
# InfoGeometry.Categorical.FibonacciAnyonBraiding

Theorem-safe categorical wrapper for the finite Fibonacci fusion/braiding lane.

This file keeps the scope narrow:

* an explicit two-object Fibonacci fusion type;
* the finite `F`, `R`, and `B = F R F` readouts via the canonical finite
  matrix layer;
* an abstract Artin braid witness structure;
* a leakage-filter/topological-register structure;
* a concrete `Cl(5,5)` carrier alias via the repo-owned split Bott stage.

No analytic continuation.
No universal braid-group representation theorem.
No physical topological-protection claim beyond explicit witnesses.
-/

noncomputable section

namespace InfoGeometry.Categorical.FibonacciAnyonBraiding

open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

/-! ## Fibonacci fusion type -/

/-- Fibonacci anyon charges: vacuum `I` and nontrivial charge `ε`. -/
inductive FibAnyon where
  | I
  | ε
  deriving DecidableEq, Repr

namespace FibAnyon

/-- Finite Fibonacci fusion rule. -/
def fusion : FibAnyon → FibAnyon → List FibAnyon
  | I, a => [a]
  | a, I => [a]
  | ε, ε => [I, ε]

@[simp] theorem fusion_I_left (a : FibAnyon) : fusion I a = [a] := by
  cases a <;> rfl

@[simp] theorem fusion_I_right (a : FibAnyon) : fusion a I = [a] := by
  cases a <;> rfl

@[simp] theorem fusion_eps_eps : fusion ε ε = [I, ε] := rfl

@[simp] theorem I_mem_fusion_eps_eps : I ∈ fusion ε ε := by
  simp [fusion]

@[simp] theorem ε_mem_fusion_eps_eps : ε ∈ fusion ε ε := by
  simp [fusion]

/-- Membership in `ε × ε` is exactly the Fibonacci two-channel split. -/
theorem mem_fusion_eps_eps_iff (a : FibAnyon) :
    a ∈ fusion ε ε ↔ a = I ∨ a = ε := by
  cases a <;> simp [fusion]

end FibAnyon

/-! ## Finite Fibonacci matrix readouts -/

/-- The finite Fibonacci fusion matrix `F`. -/
abbrev FMatrix := InfoGeometry.Canonical.FiniteFibonacciFusionMatrix.fibonacciFusionMatrix

/-- The finite diagonal braid matrix `R`. -/
abbrev RMatrix := InfoGeometry.Canonical.FiniteFibonacciFusionMatrix.fibonacciRMatrix

/-- The finite middle braid readout `B = F R F`. -/
abbrev BMatrix := InfoGeometry.Canonical.FiniteFibonacciFusionMatrix.fibonacciBMatrix

/-- `F² = 1` under the explicit scalar Fibonacci relations. -/
theorem FMatrix_sq {τ s : ℂ} (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    FMatrix τ s * FMatrix τ s = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simpa [FMatrix] using (fibonacciFusionMatrix_sq hs hτ)

/-- `det F = -1` under the explicit scalar Fibonacci relations. -/
theorem det_FMatrix {τ s : ℂ} (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (FMatrix τ s).det = -1 := by
  simpa [FMatrix] using (det_fibonacciFusionMatrix hs hτ)

/-- The middle braid readout is the conjugate `F R F`. -/
theorem BMatrix_eq_FRF (q : Units ℂ) (τ s : ℂ) :
    BMatrix q τ s = FMatrix τ s * RMatrix q * FMatrix τ s := rfl

/-! ## Abstract Artin witness lane -/

/-- Abstract Artin braid witness on a carrier `V`. -/
structure ArtinBraidWitness (V : Type*) where
  b : ℕ → V → V
  far : ℕ → ℕ → Prop
  comm : ∀ i j, far i j → b i ∘ b j = b j ∘ b i
  braid : ∀ i, b i ∘ b (i + 1) ∘ b i = b (i + 1) ∘ b i ∘ b (i + 1)

namespace ArtinBraidWitness

variable {V : Type*} (W : ArtinBraidWitness V)

/-- Readback of the `i`-th braid map. -/
def braidMap (i : ℕ) : V → V := W.b i

/-- Far-commutativity is carried as explicit data. -/
theorem commutes_of_far {i j : ℕ} (h : W.far i j) : W.b i ∘ W.b j = W.b j ∘ W.b i :=
  W.comm i j h

/-- The local Artin relation is carried as explicit data. -/
theorem braid_relation (i : ℕ) :
    W.b i ∘ W.b (i + 1) ∘ W.b i = W.b (i + 1) ∘ W.b i ∘ W.b (i + 1) :=
  W.braid i

end ArtinBraidWitness

/-! ## Leakage-filtered topological register -/

/-- A leakage-filtered register carrying an explicit braid witness and projector. -/
structure TopologicalRegister (V : Type*) (W : ArtinBraidWitness V) where
  computationalSet : Set V
  leakageSet : Set V
  Q_D : V → V
  Q_D_idempotent : ∀ v : V, Q_D (Q_D v) = Q_D v
  Q_D_computational : ∀ v : V, v ∈ computationalSet → Q_D v ∈ computationalSet
  Q_D_leakage : ∀ v : V, v ∈ leakageSet → Q_D v ∈ leakageSet
  computational_leakage_disjoint : ∀ v : V, v ∈ computationalSet → v ∈ leakageSet → False
  braid_protection : ∀ i : ℕ, ∀ v : V, Q_D (W.b i (Q_D v)) = W.b i (Q_D v)

namespace TopologicalRegister

variable {V : Type*} {W : ArtinBraidWitness V}

/-- The projector is idempotent on every carrier element. -/
theorem idempotent (R : TopologicalRegister V W) (v : V) :
    R.Q_D (R.Q_D v) = R.Q_D v :=
  R.Q_D_idempotent v

/-- The projector preserves the computational sector. -/
theorem projector_preserves_computational (R : TopologicalRegister V W) (v : V)
    (hv : v ∈ R.computationalSet) :
    R.Q_D v ∈ R.computationalSet :=
  R.Q_D_computational v hv

/-- The projector preserves the leakage sector. -/
theorem projector_preserves_leakage (R : TopologicalRegister V W) (v : V)
    (hv : v ∈ R.leakageSet) :
    R.Q_D v ∈ R.leakageSet :=
  R.Q_D_leakage v hv

/-- A computational element cannot lie in the leakage set. -/
theorem computational_not_leakage (R : TopologicalRegister V W) (v : V)
    (hv : v ∈ R.computationalSet) :
    ¬ v ∈ R.leakageSet := by
  intro hLeak
  exact R.computational_leakage_disjoint v hv hLeak

end TopologicalRegister

/-! ## Concrete `Cl(5,5)` carrier alias -/

/-- Repo-owned concrete `Cl(5,5)` Fibonacci carrier packet. -/
abbrev Cl55CarrierPacket := InfoGeometry.Clifford.FibonacciCl55Carrier.CarrierPacket

end InfoGeometry.Categorical.FibonacciAnyonBraiding

/-!
## Audit Protocol Map

- Bucket 1: `FibAnyon`, `fusion`, `FMatrix_sq`, `det_FMatrix`, and `BMatrix_eq_FRF`
  are finite theorem-safe readbacks.
- Bucket 2: `ArtinBraidWitness` and `TopologicalRegister` are explicit witness
  carriers; their braid/projection laws are supplied as data.
- Bucket 3: any concrete Artin representation, pentagon/hexagon coherence, or
  physical leakage-proof theorem remains separate debt unless supplied by an
  explicit witness.
-/
