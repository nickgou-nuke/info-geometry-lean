import Mathlib
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
-/

noncomputable section

namespace CantorProjectiveLimit

open scoped Topology
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-- The concrete projective-limit carrier of the finite prefix spaces. -/
structure PrefixProjectiveLimit where
  word : ∀ n : ℕ, BitWord n
  coherent : ∀ n : ℕ, prefixSucc n (word (n + 1)) = word n

namespace PrefixProjectiveLimit

@[ext] theorem ext {p q : PrefixProjectiveLimit} (h : p.word = q.word) : p = q := by
  cases p
  cases q
  simp_all

instance : CoeFun PrefixProjectiveLimit (fun _ => ∀ n : ℕ, BitWord n) where
  coe p := p.word

/-- Projection to the `n`th finite prefix space. -/
def π (n : ℕ) (p : PrefixProjectiveLimit) : BitWord n :=
  p.word n

@[simp] theorem π_apply (n : ℕ) (p : PrefixProjectiveLimit) :
    π n p = p.word n := rfl

/-- The topology on the projective limit is the subspace topology inherited from
`∀ n, BitWord n`. -/
instance : TopologicalSpace PrefixProjectiveLimit :=
  TopologicalSpace.induced (fun p : PrefixProjectiveLimit => p.word) inferInstance

/-- The cone map from Cantor streams to coherent finite prefixes. -/
def ofCantor (x : CantorBoundary) : PrefixProjectiveLimit where
  word := fun n => boundaryPrefix n x
  coherent := fun n => boundaryPrefix_succ_eq_prefixSucc n x

/-- Reconstruct a Cantor stream from a coherent family of finite prefixes. -/
def toCantor (p : PrefixProjectiveLimit) : CantorBoundary :=
  fun k => p.word (k + 1) ⟨k, Nat.lt_succ_self k⟩

@[simp] theorem toCantor_ofCantor (x : CantorBoundary) :
    toCantor (ofCantor x) = x := by
  ext k
  rfl

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
    π n (cantorHomeomorphPrefixProjectiveLimit x) = boundaryPrefix n x :=
  rfl

/-- The projective-limit coherence relation, exposed as a theorem. -/
theorem projection_coherent (p : PrefixProjectiveLimit) (n : ℕ) :
    prefixSucc n (π (n + 1) p) = π n p :=
  p.coherent n

end PrefixProjectiveLimit

end CantorProjectiveLimit
