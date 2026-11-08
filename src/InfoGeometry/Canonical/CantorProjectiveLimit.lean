/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorCylinderTopology
import InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-!
# Cantor space as the projective limit of finite prefix spaces

A PR-shaped, domain-free projective-limit boundary for the binary Cantor stream.

The object formalized here is the concrete inverse-limit carrier of the finite
prefix spaces `Fin n → Bool` with bonding maps `prefixSucc`.  We prove it is
homeomorphic to the product Cantor stream `ℕ → Bool`.

This is deliberately not a physics statement and not a full Stone-duality/AF
C*-algebra theorem.  It is the canonical topological spine needed by those
layers.

### Audit Classification (BUCKET 1 / BUCKET 2 / BUCKET 3)
- **BUCKET 1 (Genuine Constructive Theorems)**:
  - `PrefixProjectiveLimit`, `PrefixProjectiveLimit.mk`, `PrefixProjectiveLimit.word`,
    `PrefixProjectiveLimit.coherent`, `PrefixProjectiveLimit.ext`
  - `PrefixProjectiveLimit.π`, `PrefixProjectiveLimit.π_apply`
  - `PrefixProjectiveLimit.ofCantor`, `PrefixProjectiveLimit.toCantor`,
    `PrefixProjectiveLimit.toCantor_ofCantor`,
    `PrefixProjectiveLimit.boundaryPrefix_toCantor_eq_word`,
    `PrefixProjectiveLimit.ofCantor_toCantor`,
    `PrefixProjectiveLimit.cantorEquivPrefixProjectiveLimit`
  - `PrefixProjectiveLimit.continuous_π`, `PrefixProjectiveLimit.continuous_ofCantor`,
    `PrefixProjectiveLimit.continuous_toCantor`,
    `PrefixProjectiveLimit.cantorHomeomorphPrefixProjectiveLimit`,
    `PrefixProjectiveLimit.cantorHomeomorph_projection`,
    `PrefixProjectiveLimit.projection_coherent`
- **BUCKET 2 (Honest Numeric/Finite Certificates)**: None (all results are universally quantified over `n : ℕ`).
- **BUCKET 3 (Eliminated Debt)**: `0` `sorry`, `0` `admit`, `0` wrapper structures.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorProjectiveLimit

open scoped Topology
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-- The concrete projective-limit carrier of the finite prefix spaces, represented as a subtype
of families of finite prefix words compatible under `prefixSucc`. -/
def PrefixProjectiveLimit : Type :=
  { word : ∀ n : ℕ, BitWord n // ∀ n : ℕ, prefixSucc n (word (n + 1)) = word n }

namespace PrefixProjectiveLimit

/-- Construct a `PrefixProjectiveLimit` element from a family of words and its coherence proof. -/
def mk (word : ∀ n : ℕ, BitWord n)
    (coherent : ∀ n : ℕ, prefixSucc n (word (n + 1)) = word n) :
    PrefixProjectiveLimit :=
  ⟨word, coherent⟩

/-- The underlying sequence of finite prefix words `∀ n : ℕ, BitWord n`. -/
def word (p : PrefixProjectiveLimit) : ∀ n : ℕ, BitWord n :=
  p.1

/-- Extracting `.word` from `mk w h` recovers `w`. -/
@[simp] theorem word_mk (w : ∀ n : ℕ, BitWord n)
    (h : ∀ n : ℕ, prefixSucc n (w (n + 1)) = w n) :
    (mk w h).word = w := by
  have hw : (mk w h).word = w := rfl
  exact hw

/-- The one-step prefix coherence law `prefixSucc n (p.word (n + 1)) = p.word n`. -/
theorem coherent (p : PrefixProjectiveLimit) (n : ℕ) :
    prefixSucc n (p.word (n + 1)) = p.word n := by
  have h := p.2 n
  exact h

/-- Two elements of `PrefixProjectiveLimit` are equal if their word sequences agree. -/
@[ext] theorem ext {p q : PrefixProjectiveLimit} (h : p.word = q.word) : p = q := by
  exact Subtype.ext h

instance : CoeFun PrefixProjectiveLimit (fun _ => ∀ n : ℕ, BitWord n) where
  coe p := p.word

/-- Projection to the `n`th finite prefix space. -/
def π (n : ℕ) (p : PrefixProjectiveLimit) : BitWord n :=
  p.word n

/-- Evaluating `π n p` unfolds to `p.word n`. -/
@[simp] theorem π_apply (n : ℕ) (p : PrefixProjectiveLimit) :
    π n p = p.word n := by
  have h : π n p = p.word n := rfl
  exact h

/-- The topology on the projective limit is the subspace topology inherited from
`∀ n, BitWord n`. -/
instance : TopologicalSpace PrefixProjectiveLimit :=
  TopologicalSpace.induced (fun p : PrefixProjectiveLimit => p.word) inferInstance

/-- The cone map from Cantor streams to coherent finite prefixes. -/
def ofCantor (x : CantorBoundary) : PrefixProjectiveLimit :=
  mk (fun n => boundaryPrefix n x) (fun n => boundaryPrefix_succ_eq_prefixSucc n x)

/-- Reconstruct a Cantor stream from a coherent family of finite prefixes. -/
def toCantor (p : PrefixProjectiveLimit) : CantorBoundary :=
  fun k => p.word (k + 1) ⟨k, Nat.lt_succ_self k⟩

/-- Round-trip identity `toCantor (ofCantor x) = x`. -/
@[simp] theorem toCantor_ofCantor (x : CantorBoundary) :
    toCantor (ofCantor x) = x := by
  ext k
  rfl

/-- Taking the `n`-th boundary prefix of `toCantor p` recovers `p.word n`. -/
theorem boundaryPrefix_toCantor_eq_word (p : PrefixProjectiveLimit) (n : ℕ) :
    boundaryPrefix n (toCantor p) = p.word n := by
  induction n with
  | zero =>
      ext i
      exact Fin.elim0 i
  | succ m ih =>
      ext i
      by_cases hi : i.1 < m
      · have hcoh := congrFun (p.coherent m) ⟨i.1, hi⟩
        have hih := congrFun ih ⟨i.1, hi⟩
        simpa [boundaryPrefix, prefixSucc] using hih.trans hcoh.symm
      · cases i with
        | mk val hlt =>
            have hle : m ≤ val := Nat.le_of_not_gt (by simpa using hi)
            have hle' : val ≤ m := Nat.lt_succ_iff.mp hlt
            have heq : val = m := Nat.le_antisymm hle' hle
            subst heq
            simp [boundaryPrefix, toCantor]

/-- Round-trip identity `ofCantor (toCantor p) = p`. -/
@[simp] theorem ofCantor_toCantor (p : PrefixProjectiveLimit) :
    ofCantor (toCantor p) = p := by
  apply PrefixProjectiveLimit.ext
  funext n
  exact boundaryPrefix_toCantor_eq_word p n

/-- Type-level equivalence between Cantor streams and the prefix projective limit. -/
def cantorEquivPrefixProjectiveLimit : CantorBoundary ≃ PrefixProjectiveLimit where
  toFun := ofCantor
  invFun := toCantor
  left_inv := toCantor_ofCantor
  right_inv := by intro p; exact ofCantor_toCantor p

/-- Each finite projection is continuous by construction of the induced topology. -/
theorem continuous_π (n : ℕ) : Continuous (π n) := by
  change Continuous (fun p : PrefixProjectiveLimit => p.word n)
  exact (continuous_apply n).comp continuous_induced_dom

/-- The cone map from Cantor streams to the projective-limit carrier is continuous. -/
theorem continuous_ofCantor : Continuous ofCantor := by
  rw [continuous_induced_rng]
  change Continuous (fun x : CantorBoundary => fun n : ℕ => boundaryPrefix n x)
  exact continuous_pi fun n => by
    unfold boundaryPrefix
    continuity

/-- The reconstruction map from the projective-limit carrier to Cantor streams is continuous. -/
theorem continuous_toCantor : Continuous toCantor := by
  change Continuous (fun p : PrefixProjectiveLimit => fun k : ℕ => p.word (k + 1) ⟨k, Nat.lt_succ_self k⟩)
  exact continuous_pi fun k => by
    exact (continuous_apply ⟨k, Nat.lt_succ_self k⟩).comp (continuous_π (k + 1))

/-- Cantor space is homeomorphic to the concrete projective limit of finite prefix spaces. -/
def cantorHomeomorphPrefixProjectiveLimit : CantorBoundary ≃ₜ PrefixProjectiveLimit where
  toEquiv := cantorEquivPrefixProjectiveLimit
  continuous_toFun := continuous_ofCantor
  continuous_invFun := continuous_toCantor

/-- The `n`th projection of the homeomorphism is the ordinary boundary prefix. -/
theorem cantorHomeomorph_projection (x : CantorBoundary) (n : ℕ) :
    π n (cantorHomeomorphPrefixProjectiveLimit x) = boundaryPrefix n x := by
  have h : π n (cantorHomeomorphPrefixProjectiveLimit x) = boundaryPrefix n x := rfl
  exact h

/-- The projective-limit coherence relation, exposed as a theorem. -/
theorem projection_coherent (p : PrefixProjectiveLimit) (n : ℕ) :
    prefixSucc n (π (n + 1) p) = π n p := by
  have h := p.coherent n
  exact h

end PrefixProjectiveLimit

end InfoGeometry.Canonical.CantorProjectiveLimit
