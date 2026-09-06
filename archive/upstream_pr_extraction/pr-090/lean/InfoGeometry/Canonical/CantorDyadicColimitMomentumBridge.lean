import Mathlib.Tactic
import Mathlib.Algebra.Colimit.Module
import InfoGeometry.Canonical.CantorDyadicDifferenceScaleBridge

set_option linter.unusedSimpArgs false

/-!
# Cantor Dyadic Colimit Momentum Bridge

This owner module formalizes the continuum four-momentum generator $P_\mu^{\text{colimit}}$
natively via the **Categorical Filtered Direct Inductive Colimit** of dyadic difference operators,
fulfilling the repository's Colimit Continuum Mandate without analytical epsilon approximations:

1. **Filtered Inductive System of Dyadic Scales:**
   $(\text{DyadicScale}(n))_{n \in \mathbb{N}}$ with transition embeddings $f_{m,n}$.

2. **Coherent Difference Family:**
   A family $D_n : \text{DyadicScale}(n) \to+ \text{DyadicScale}(n)$ commuting with the transition maps:
   $$D_n(f_{m,n}(x)) = f_{m,n}(D_m(x))$$

3. **Categorical Colimit Momentum Operator:**
   $$\boxed{P^{\text{colimit}} : \varinjlim \text{Stage}(n) \longrightarrow+ \varinjlim \text{Stage}(n)}$$
   induced uniquely by universal colimit factorization.

4. **Exact Representation Recovery on Every Level:**
   $$\boxed{P^{\text{colimit}}(\operatorname{of}(n, x)) = \operatorname{of}(n, D_n(x))}$$

5. **Universal Abelian Commutativity on the Colimit Space:**
   $$\forall n, [D_{\mu, n}, D_{\nu, n}] = 0 \implies \boxed{[P_\mu^{\text{colimit}}, P_\nu^{\text{colimit}}] = 0}$$
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorDyadicColimitMomentumBridge

open InfoGeometry.Canonical.CantorDyadicDifferenceScaleBridge

/-- The sequence of dyadic stages as additive abelian groups. -/
def Stage (n : ℕ) : Type := DyadicScale n

instance (n : ℕ) : AddCommGroup (Stage n) := by
  dsimp [Stage, DyadicScale]
  infer_instance

variable
    (trans_map : ∀ (m n : ℕ), m ≤ n → Stage m →+ Stage n)
    (htrans_id : ∀ (n : ℕ), trans_map n n (le_refl n) = AddMonoidHom.id (Stage n))
    (htrans_comp : ∀ (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k),
      trans_map i k (le_trans hij hjk) = (trans_map j k hjk).comp (trans_map i j hij))

/-- A family of difference operators on each finite dyadic resolution stage. -/
structure CoherentDifferenceFamily where
  D : ∀ n, Stage n →+ Stage n
  compat : ∀ (m n : ℕ) (h : m ≤ n) (x : Stage m),
    D n (trans_map m n h x) = trans_map m n h (D m x)

/-- Canonical operated injection into the direct limit. -/
def operatedOf (fam : CoherentDifferenceFamily trans_map) (n : ℕ) :
    Stage n →+ AddCommGroup.DirectLimit Stage trans_map :=
  (AddCommGroup.DirectLimit.of Stage trans_map n).comp (fam.D n)

theorem operatedOf_compatible (fam : CoherentDifferenceFamily trans_map)
    (m n : ℕ) (h : m ≤ n) (x : Stage m) :
    operatedOf trans_map fam n (trans_map m n h x) =
      operatedOf trans_map fam m x := by
  dsimp [operatedOf]
  rw [fam.compat m n h x]
  exact AddCommGroup.DirectLimit.of_f (f := trans_map) (i := m) (j := n) (hij := h) (x := fam.D m x)

/-- 🏆 THEOREM 1: The Categorical Direct Colimit Momentum Operator:
    $$P^{\text{colimit}} : \varinjlim \text{Stage}(n) \longrightarrow+ \varinjlim \text{Stage}(n)$$
    induced uniquely by universal colimit factorization. -/
def colimitMomentumOperator (fam : CoherentDifferenceFamily trans_map) :
    AddCommGroup.DirectLimit Stage trans_map →+
      AddCommGroup.DirectLimit Stage trans_map :=
  AddCommGroup.DirectLimit.lift
    Stage trans_map
    (AddCommGroup.DirectLimit Stage trans_map)
    (operatedOf trans_map fam)
    (operatedOf_compatible trans_map fam)

/-- 🏆 THEOREM 2: Exact representation recovery on every finite resolution level:
    $$P^{\text{colimit}}(\operatorname{of}(n, x)) = \operatorname{of}(n, D_n(x))$$ -/
@[simp] theorem colimitMomentumOperator_of
    (fam : CoherentDifferenceFamily trans_map)
    (n : ℕ) (x : Stage n) :
    colimitMomentumOperator trans_map fam
        (AddCommGroup.DirectLimit.of Stage trans_map n x) =
      AddCommGroup.DirectLimit.of Stage trans_map n (fam.D n x) := by
  exact AddCommGroup.DirectLimit.lift_of
    (G := Stage) (f := trans_map)
    (P := AddCommGroup.DirectLimit Stage trans_map)
    (g := operatedOf trans_map fam)
    (Hg := operatedOf_compatible trans_map fam)
    (i := n) (x := x)

/-- 🏆 THEOREM 3: Exact Abelian Commutation of Colimit Momentum Generators:
    If $[D_{\mu, n}, D_{\nu, n}] = 0$ for all $n$, then $[P_\mu^{\text{colimit}}, P_\nu^{\text{colimit}}] = 0$
    on the entire direct limit space $\varinjlim \text{Stage}(n)$. -/
theorem colimitMomentumOperator_comm
    (fam1 fam2 : CoherentDifferenceFamily trans_map)
    (hcomm : ∀ n (x : Stage n), fam1.D n (fam2.D n x) = fam2.D n (fam1.D n x)) :
    ∀ (z : AddCommGroup.DirectLimit Stage trans_map),
      colimitMomentumOperator trans_map fam1 (colimitMomentumOperator trans_map fam2 z) =
      colimitMomentumOperator trans_map fam2 (colimitMomentumOperator trans_map fam1 z) := by
  intro z
  refine AddCommGroup.DirectLimit.induction_on z ?_
  intro n x
  simp only [colimitMomentumOperator_of, hcomm n x]

theorem colimitMomentumOperator_comm_eq
    (fam1 fam2 : CoherentDifferenceFamily trans_map)
    (hcomm : ∀ n (x : Stage n), fam1.D n (fam2.D n x) = fam2.D n (fam1.D n x)) :
    (colimitMomentumOperator trans_map fam1).comp
        (colimitMomentumOperator trans_map fam2) =
      (colimitMomentumOperator trans_map fam2).comp
        (colimitMomentumOperator trans_map fam1) := by
  apply AddMonoidHom.ext
  intro z
  exact colimitMomentumOperator_comm trans_map fam1 fam2 hcomm z

/-! The universal property also gives uniqueness: an additive endomorphism of
the direct limit is determined by its values on the canonical stage maps. -/

theorem colimitMomentumOperator_unique
    (fam : CoherentDifferenceFamily trans_map)
    (g : AddCommGroup.DirectLimit Stage trans_map →+
      AddCommGroup.DirectLimit Stage trans_map)
    (hg : ∀ (n : ℕ) (x : Stage n),
      g (AddCommGroup.DirectLimit.of Stage trans_map n x) =
        AddCommGroup.DirectLimit.of Stage trans_map n (fam.D n x)) :
    g = colimitMomentumOperator trans_map fam := by
  apply AddMonoidHom.ext
  intro z
  refine AddCommGroup.DirectLimit.induction_on z ?_
  intro n x
  rw [hg n x]
  exact (colimitMomentumOperator_of trans_map fam n x).symm

end InfoGeometry.Canonical.CantorDyadicColimitMomentumBridge
