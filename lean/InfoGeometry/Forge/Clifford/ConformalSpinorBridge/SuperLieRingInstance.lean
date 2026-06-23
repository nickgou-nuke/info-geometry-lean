import Mathlib
import InfoGeometry.Algebra.SuperLieRing
import InfoGeometry.Clifford.ConformalLieAlgebra55

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


/-!
# SuperLieRing Instance for ConformalSpinorBridge (FULL VERSION)

**Recovered from Hermes auto-edit backup (2026-06-15).**

This file contains the full `SuperLieRing` instance for `𝔬𝔰𝔭(1|2)` realized
in `Cl(5,5)`, with complete span-induction proofs for the super-Jacobi identity
on arbitrary linear combinations.

**Status:** The span-induction proofs are mathematically correct but may exceed
heartbeat limits during `lake build -R`. The companion file `ConformalSpinorBridge.lean`
exports a lightweight finite-basis version that compiles quickly. This file is
preserved as the authoritative reference implementation.

**Recovery notes:**
- All proofs are real — no `trivial`, `axiom`, or `sorry` placeholders
- The SuperLieRing instance was removed purely for performance reasons
- SymPy witness: `tools/sympy/osp12_spinor_bridge.py`
# InfoGeometry.Clifford.ConformalSpinorBridge

The odd spinor sector of `𝔬𝔰𝔭(1|2)` as a `SuperLieRing` instance, realized
in the `Cl(5,5)` Clifford algebra.

## Generators

Even (3): `H = D5` (dilation), `Ep = u5` (translation P), `Em = v5` (special conformal K)
Odd  (2): `G1`, `G2` — the off-diagonal spinor generators in the (2|1) supermatrix format.

## Brackets

Even-even (𝔰𝔩₂):
  `[H, Ep] = 2·Ep`     `[H, Em] = -2·Em`     `[Ep, Em] = H`

Even-odd (spinor action):
  `[H, G1] = G1`       `[H, G2] = -G2`
  `[Ep, G1] = 0`       `[Ep, G2] = G1`
  `[Em, G1] = G2`      `[Em, G2] = 0`

Odd-odd (symmetric anticommutator):
  `{G1, G1} = 2·Ep`    `{G2, G2} = -2·Em`   `{G1, G2} = {G2, G1} = -H`

Super-Jacobi: verified by SymPy on all 125 homogeneous basis triples.

SymPy witness: `tools/sympy/osp12_spinor_bridge.py`
-/

open InfoGeometry.Algebra

noncomputable section

namespace InfoGeometry.Clifford.ConformalSpinorBridge

set_option linter.unusedSimpArgs false
open InfoGeometry.Clifford.ConformalLieAlgebra55

set_option maxHeartbeats 8000000

/-! ## 1. The 5-dimensional carrier -/

/--
Indices for the 5-element basis {H, Ep, Em, G1, G2}.
-/
inductive B : Type
  | H | Ep | Em | G1 | G2
  deriving DecidableEq, Fintype

open B

/-- The 5-dimensional ℝ-vector space. -/
abbrev OSp12 : Type := B → ℝ

namespace OSp12

instance : AddCommGroup OSp12 := by unfold OSp12; infer_instance
instance : Module ℝ OSp12 := by unfold OSp12; infer_instance

/-! ## 2. Structure constants -/

noncomputable def structConst (i j k : B) : ℚ :=
  match i, j, k with
  | .H,  .Ep, .Ep =>  2    | .Ep, .H,  .Ep => -2
  | .H,  .Em, .Em => -2    | .Em, .H,  .Em =>  2
  | .Ep, .Em, .H  =>  1    | .Em, .Ep, .H  => -1
  | .H,  .G1, .G1 =>  1    | .G1, .H,  .G1 => -1
  | .H,  .G2, .G2 => -1    | .G2, .H,  .G2 =>  1
  | .Ep, .G2, .G1 =>  1    | .G2, .Ep, .G1 => -1
  | .Em, .G1, .G2 =>  1    | .G1, .Em, .G2 => -1
  | .G1, .G2, .H  => -1    | .G2, .G1, .H  => -1
  | .G1, .G1, .Ep =>  2
  | .G2, .G2, .Em => -2
  | _, _, _ => 0

noncomputable def bracket (x y : OSp12) : OSp12 := λ k =>
  ∑ i : B, ∑ j : B, (structConst i j k : ℝ) * (x i) * (y j)

/-! ## 3. SuperLieRing instance -/


private lemma sum_B_eval (f : B → ℝ) : ∑ i : B, f i = f B.H + f B.Ep + f B.Em + f B.G1 + f B.G2 := by
  have : (Finset.univ : Finset B) = {B.H, B.Ep, B.Em, B.G1, B.G2} := rfl
  simp [this, Finset.sum_insert, Finset.sum_singleton]; abel

noncomputable def evenPart : Submodule ℝ OSp12 :=
  Submodule.span ℝ {λ | .H => 1 | _ => 0, λ | .Ep => 1 | _ => 0, λ | .Em => 1 | _ => 0}

noncomputable def oddPart : Submodule ℝ OSp12 :=
  Submodule.span ℝ {λ | .G1 => 1 | _ => 0, λ | .G2 => 1 | _ => 0}

private theorem even_odd_gen_H_G1 :
    bracket (Pi.single B.H (1 : ℝ)) (Pi.single B.G1 (1 : ℝ)) =
      - bracket (Pi.single B.G1 (1 : ℝ)) (Pi.single B.H (1 : ℝ)) := by
  ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]

private theorem even_odd_gen_H_G2 :
    bracket (Pi.single B.H (1 : ℝ)) (Pi.single B.G2 (1 : ℝ)) =
      - bracket (Pi.single B.G2 (1 : ℝ)) (Pi.single B.H (1 : ℝ)) := by
  ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]

private theorem even_odd_gen_Ep_G1 :
    bracket (Pi.single B.Ep (1 : ℝ)) (Pi.single B.G1 (1 : ℝ)) =
      - bracket (Pi.single B.G1 (1 : ℝ)) (Pi.single B.Ep (1 : ℝ)) := by
  ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]

private theorem even_odd_gen_Ep_G2 :
    bracket (Pi.single B.Ep (1 : ℝ)) (Pi.single B.G2 (1 : ℝ)) =
      - bracket (Pi.single B.G2 (1 : ℝ)) (Pi.single B.Ep (1 : ℝ)) := by
  ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]

private theorem even_odd_gen_Em_G1 :
    bracket (Pi.single B.Em (1 : ℝ)) (Pi.single B.G1 (1 : ℝ)) =
      - bracket (Pi.single B.G1 (1 : ℝ)) (Pi.single B.Em (1 : ℝ)) := by
  ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]

private theorem even_odd_gen_Em_G2 :
    bracket (Pi.single B.Em (1 : ℝ)) (Pi.single B.G2 (1 : ℝ)) =
      - bracket (Pi.single B.G2 (1 : ℝ)) (Pi.single B.Em (1 : ℝ)) := by
  ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]

private theorem odd_odd_gen_G1_G2 :
    bracket (Pi.single B.G1 (1 : ℝ)) (Pi.single B.G2 (1 : ℝ)) =
      bracket (Pi.single B.G2 (1 : ℝ)) (Pi.single B.G1 (1 : ℝ)) := by
  ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]


private lemma add_lie_proof (x y z : OSp12) : bracket (x + y) z = bracket x z + bracket y z := by
  ext k; simp [bracket, add_mul, mul_add, Finset.sum_add_distrib]

private lemma lie_add_proof (x y z : OSp12) : bracket x (y + z) = bracket x y + bracket x z := by
  ext k; simp [bracket, add_mul, mul_add, Finset.sum_add_distrib]

private lemma smul_lie_proof (r : ℝ) (x y : OSp12) : bracket (r • x) y = r • bracket x y := by
  ext k; simp [bracket, mul_assoc, Finset.mul_sum]
  congr; ext i; congr; ext j; ring

private lemma lie_smul_proof (r : ℝ) (x y : OSp12) : bracket x (r • y) = r • bracket x y := by
  ext k; simp [bracket, mul_assoc, Finset.mul_sum]
  congr; ext i; congr; ext j; ring

private lemma sup_even_odd_proof : evenPart ⊔ oddPart = ⊤ := by
  have heven : ({fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({(Pi.single B.H (1 : ℝ) : OSp12), (Pi.single B.Ep (1 : ℝ) : OSp12), (Pi.single B.Em (1 : ℝ) : OSp12)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; left; ext x <;> cases x <;> simp
      · right; right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr (Or.inl ?_); ext x <;> cases x <;> simp
      · refine Or.inr (Or.inr ?_); ext x <;> cases x <;> simp
  have hodd : ({fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({(Pi.single B.G1 (1 : ℝ) : OSp12), (Pi.single B.G2 (1 : ℝ) : OSp12)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  rw [eq_top_iff]
  intro x _
  have hsum : x = (x B.H • (Pi.single B.H (1 : ℝ) : OSp12) + x B.Ep • (Pi.single B.Ep (1 : ℝ) : OSp12) + x B.Em • (Pi.single B.Em (1 : ℝ) : OSp12)) +
                  (x B.G1 • (Pi.single B.G1 (1 : ℝ) : OSp12) + x B.G2 • (Pi.single B.G2 (1 : ℝ) : OSp12)) := by
    ext k <;> fin_cases k <;> simp [Pi.single]
  rw [hsum]
  apply Submodule.add_mem (evenPart ⊔ oddPart)
  · apply Submodule.mem_sup_left
    rw [evenPart, heven]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.mem_sup_right
    rw [oddPart, hodd]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private lemma evenPart_zero_on_odd (x : OSp12) (hxeven : x ∈ Submodule.span ℝ ({(Pi.single B.H (1 : ℝ) : OSp12), (Pi.single B.Ep (1 : ℝ) : OSp12), (Pi.single B.Em (1 : ℝ) : OSp12)} : Set OSp12)) : x B.G1 = 0 ∧ x B.G2 = 0 := by
  induction hxeven using Submodule.span_induction with
  | mem v hv => rcases hv with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  | zero => exact ⟨rfl, rfl⟩
  | add u v hu hv ih_u ih_v => exact ⟨by simp [Pi.add_apply, ih_u.1, ih_v.1], by simp [Pi.add_apply, ih_u.2, ih_v.2]⟩
  | smul r u hu ih_u => exact ⟨by simp [Pi.smul_apply, ih_u.1], by simp [Pi.smul_apply, ih_u.2]⟩

private lemma oddPart_zero_on_even (x : OSp12) (hxodd : x ∈ Submodule.span ℝ ({(Pi.single B.G1 (1 : ℝ) : OSp12), (Pi.single B.G2 (1 : ℝ) : OSp12)} : Set OSp12)) : x B.H = 0 ∧ x B.Ep = 0 ∧ x B.Em = 0 := by
  induction hxodd using Submodule.span_induction with
  | mem v hv => rcases hv with rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
  | zero => exact ⟨rfl, rfl, rfl⟩
  | add u v hu hv ih_u ih_v => exact ⟨by simp [Pi.add_apply, ih_u.1, ih_v.1], by simp [Pi.add_apply, ih_u.2.1, ih_v.2.1], by simp [Pi.add_apply, ih_u.2.2, ih_v.2.2]⟩
  | smul r u hu ih_u => exact ⟨by simp [Pi.smul_apply, ih_u.1], by simp [Pi.smul_apply, ih_u.2.1], by simp [Pi.smul_apply, ih_u.2.2]⟩

private lemma even_odd_inter_proof : evenPart ⊓ oddPart = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rcases hx with ⟨hxeven, hxodd⟩
  have heven : ({fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({(Pi.single B.H (1 : ℝ) : OSp12), (Pi.single B.Ep (1 : ℝ) : OSp12), (Pi.single B.Em (1 : ℝ) : OSp12)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; left; ext x <;> cases x <;> simp
      · right; right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr (Or.inl ?_); ext x <;> cases x <;> simp
      · refine Or.inr (Or.inr ?_); ext x <;> cases x <;> simp
  have hodd : ({fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({(Pi.single B.G1 (1 : ℝ) : OSp12), (Pi.single B.G2 (1 : ℝ) : OSp12)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  rw [evenPart, heven] at hxeven
  rw [oddPart, hodd] at hxodd
  have hxeven_zero := evenPart_zero_on_odd x hxeven
  have hxodd_zero := oddPart_zero_on_even x hxodd
  ext k
  fin_cases k
  · exact hxodd_zero.1
  · exact hxodd_zero.2.1
  · exact hxodd_zero.2.2
  · exact hxeven_zero.1
  · exact hxeven_zero.2

private lemma even_even_skew_proof (x y : OSp12) : x ∈ evenPart → y ∈ evenPart → bracket x y = - bracket y x := by
  have heven : ({fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({(Pi.single B.H (1 : ℝ) : OSp12), (Pi.single B.Ep (1 : ℝ) : OSp12), (Pi.single B.Em (1 : ℝ) : OSp12)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; left; ext x <;> cases x <;> simp
      · right; right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr (Or.inl ?_); ext x <;> cases x <;> simp
      · refine Or.inr (Or.inr ?_); ext x <;> cases x <;> simp
  intro hx hy
  rw [evenPart, heven] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hxgen =>
      induction hy using Submodule.span_induction with
      | mem y hygen =>
          rcases hxgen with rfl | rfl | rfl <;>
          rcases hygen with rfl | rfl | rfl <;>
          ext k <;> fin_cases k <;>
          simp [bracket, Pi.single, Function.update, structConst]
      | zero =>
          ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.zero_lie]
      | add a b ha hb haP hbP =>
          simp only [add_lie_proof, lie_add_proof, haP, hbP]<;> try abel
      | smul r a ha haP =>
          simp only [smul_lie_proof, lie_smul_proof, haP, smul_neg, smul_add, smul_sub]<;> try abel
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.zero_lie]
  | add a b ha hb haP hbP =>
      simp only [add_lie_proof, lie_add_proof, haP, hbP]<;> try abel
  | smul r a ha haP =>
      simp only [smul_lie_proof, lie_smul_proof, haP, smul_neg, smul_add, smul_sub]<;> try abel

private lemma even_odd_skew_proof (x y : OSp12) : x ∈ evenPart → y ∈ oddPart → bracket x y = - bracket y x := by
  have heven : ({fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({(Pi.single B.H (1 : ℝ) : OSp12), (Pi.single B.Ep (1 : ℝ) : OSp12), (Pi.single B.Em (1 : ℝ) : OSp12)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; left; ext x <;> cases x <;> simp
      · right; right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr (Or.inl ?_); ext x <;> cases x <;> simp
      · refine Or.inr (Or.inr ?_); ext x <;> cases x <;> simp
  have hodd : ({fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({(Pi.single B.G1 (1 : ℝ) : OSp12), (Pi.single B.G2 (1 : ℝ) : OSp12)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  intro hx hy
  rw [evenPart, heven] at hx
  rw [oddPart, hodd] at hy
  induction hx using Submodule.span_induction with
  | mem x hxgen =>
      induction hy using Submodule.span_induction with
      | mem y hygen =>
          rcases hxgen with rfl | rfl | rfl <;>
          rcases hygen with rfl | rfl <;>
          ext k <;> fin_cases k <;>
          simp [bracket, Pi.single, Function.update, structConst]
      | zero =>
          ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.zero_lie]
      | add a b ha hb haP hbP =>
          simp only [add_lie_proof, lie_add_proof, haP, hbP]<;> try abel
      | smul r a ha haP =>
          simp only [smul_lie_proof, lie_smul_proof, haP, smul_neg, smul_add, smul_sub]<;> try abel
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.zero_lie]
  | add a b ha hb haP hbP =>
      simp only [add_lie_proof, lie_add_proof, haP, hbP]<;> try abel
  | smul r a ha haP =>
      simp only [smul_lie_proof, lie_smul_proof, haP, smul_neg, smul_add, smul_sub]<;> try abel

private lemma odd_odd_symm_proof (x y : OSp12) : x ∈ oddPart → y ∈ oddPart → bracket x y = bracket y x := by
  have hodd : ({fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({(Pi.single B.G1 (1 : ℝ) : OSp12), (Pi.single B.G2 (1 : ℝ) : OSp12)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  intro hx hy
  rw [oddPart, hodd] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hxgen =>
      induction hy using Submodule.span_induction with
      | mem y hygen =>
          rcases hxgen with rfl | rfl <;>
          rcases hygen with rfl | rfl <;>
          ext k <;> fin_cases k <;>
          simp [bracket, Pi.single, Function.update, structConst]
      | zero =>
          ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.zero_lie]
      | add a b ha hb haP hbP =>
          simp only [add_lie_proof, lie_add_proof, haP, hbP]<;> try abel
      | smul r a ha haP =>
          simp only [smul_lie_proof, lie_smul_proof, haP, smul_add]<;> try abel
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.zero_lie]
  | add a b ha hb haP hbP =>
      simp only [add_lie_proof, lie_add_proof, haP, hbP]<;> try abel
  | smul r a ha haP =>
      simp only [smul_lie_proof, lie_smul_proof, haP, smul_add]<;> try abel

private lemma jacobi_basis_even_H (b c : B) :
    bracket (Pi.single B.H (1 : ℝ)) (bracket (Pi.single b (1 : ℝ)) (Pi.single c (1 : ℝ))) =
      bracket (bracket (Pi.single B.H (1 : ℝ)) (Pi.single b (1 : ℝ))) (Pi.single c (1 : ℝ)) +
      bracket (Pi.single b (1 : ℝ)) (bracket (Pi.single B.H (1 : ℝ)) (Pi.single c (1 : ℝ))) := by
  cases b <;> cases c <;> ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst] <;> simp [sum_B_eval] <;> norm_num<;> try abel

private lemma jacobi_basis_even_Ep (b c : B) :
    bracket (Pi.single B.Ep (1 : ℝ)) (bracket (Pi.single b (1 : ℝ)) (Pi.single c (1 : ℝ))) =
      bracket (bracket (Pi.single B.Ep (1 : ℝ)) (Pi.single b (1 : ℝ))) (Pi.single c (1 : ℝ)) +
      bracket (Pi.single b (1 : ℝ)) (bracket (Pi.single B.Ep (1 : ℝ)) (Pi.single c (1 : ℝ))) := by
  cases b <;> cases c <;> ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst] <;> simp [sum_B_eval] <;> norm_num<;> try abel

private lemma jacobi_basis_even_Em (b c : B) :
    bracket (Pi.single B.Em (1 : ℝ)) (bracket (Pi.single b (1 : ℝ)) (Pi.single c (1 : ℝ))) =
      bracket (bracket (Pi.single B.Em (1 : ℝ)) (Pi.single b (1 : ℝ))) (Pi.single c (1 : ℝ)) +
      bracket (Pi.single b (1 : ℝ)) (bracket (Pi.single B.Em (1 : ℝ)) (Pi.single c (1 : ℝ))) := by
  cases b <;> cases c <;> ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst] <;> simp [sum_B_eval] <;> norm_num<;> try abel

private lemma jacobi_even_z (x y z : OSp12)
    (hxgen : ∃ a ∈ (({B.H, B.Ep, B.Em} : Set B) : Set B), x = Pi.single a (1 : ℝ))
    (hygen : ∃ b : B, y = Pi.single b (1 : ℝ)) :
    bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z) := by
  let S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
  have hz_span : z ∈ Submodule.span ℝ S := by
    have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
      ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
    have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
      rw [show S = Set.range (fun a : B => Pi.single a (1 : ℝ)) by rfl, hrange]
      exact (Pi.basisFun ℝ B).span_eq
    rw [hspan]
    exact Submodule.mem_top
  induction hz_span using Submodule.span_induction with
  | mem z hzgen =>
      rcases hxgen with ⟨a, ha, rfl⟩
      rcases hygen with ⟨b, rfl⟩
      rcases hzgen with ⟨c, rfl⟩
      rcases ha with rfl | rfl | rfl
      · exact jacobi_basis_even_H b c
      · exact jacobi_basis_even_Ep b c
      · exact jacobi_basis_even_Em b c
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left]
  | add u v hu hv huP hvP =>
      simp only [add_lie_proof, lie_add_proof, huP, hvP]<;> try abel
  | smul r u hu huP =>
      simp only [smul_lie_proof, lie_smul_proof, huP, smul_neg, smul_add, smul_sub]<;> try abel

private lemma jacobi_even_y (x y z : OSp12)
    (hxgen : ∃ a ∈ (({B.H, B.Ep, B.Em} : Set B) : Set B), x = Pi.single a (1 : ℝ)) :
    bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z) := by
  let S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
  have hy_span : y ∈ Submodule.span ℝ S := by
    have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
      ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
    have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
      rw [show S = Set.range (fun a : B => Pi.single a (1 : ℝ)) by rfl, hrange]
      exact (Pi.basisFun ℝ B).span_eq
    rw [hspan]
    exact Submodule.mem_top
  induction hy_span using Submodule.span_induction with
  | mem y hygen =>
      rcases hygen with ⟨b, rfl⟩
      exact jacobi_even_z x (Pi.single b 1) z hxgen ⟨b, rfl⟩
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left]
  | add u v hu hv huP hvP =>
      simp only [add_lie_proof, lie_add_proof, huP, hvP]<;> try abel
  | smul r u hu huP =>
      simp only [smul_lie_proof, lie_smul_proof, huP, smul_neg, smul_add, smul_sub]<;> try abel

private lemma jacobi_even_proof (x y z : OSp12) (hx : x ∈ evenPart) :
    bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z) := by
  have heven : ({fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({(Pi.single B.H (1 : ℝ) : OSp12), (Pi.single B.Ep (1 : ℝ) : OSp12), (Pi.single B.Em (1 : ℝ) : OSp12)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; left; ext x <;> cases x <;> simp
      · right; right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr (Or.inl ?_); ext x <;> cases x <;> simp
      · refine Or.inr (Or.inr ?_); ext x <;> cases x <;> simp
  have hx2 := hx
  rw [evenPart, heven] at hx2
  clear hx
  induction hx2 using Submodule.span_induction with
  | mem x hxgen =>
      have hxgen_a : ∃ a ∈ (({B.H, B.Ep, B.Em} : Set B) : Set B), x = Pi.single a (1 : ℝ) := by
        rcases hxgen with rfl | rfl | rfl
        · exact ⟨B.H, Or.inl rfl, rfl⟩
        · exact ⟨B.Ep, Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨B.Em, Or.inr (Or.inr rfl), rfl⟩
      exact jacobi_even_y x y z hxgen_a
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left]
  | add u v hu hv huP hvP =>
      simp only [add_lie_proof, lie_add_proof, huP, hvP]<;> try abel
  | smul r u hu huP =>
      simp only [smul_lie_proof, lie_smul_proof, huP, smul_neg, smul_add, smul_sub]<;> try abel

private lemma jacobi_basis_odd_G1 (b c : B) (hb : b ∈ (({B.G1, B.G2} : Set B) : Set B)) :
    bracket (Pi.single B.G1 (1 : ℝ)) (bracket (Pi.single b (1 : ℝ)) (Pi.single c (1 : ℝ))) =
      bracket (bracket (Pi.single B.G1 (1 : ℝ)) (Pi.single b (1 : ℝ))) (Pi.single c (1 : ℝ)) -
      bracket (Pi.single b (1 : ℝ)) (bracket (Pi.single B.G1 (1 : ℝ)) (Pi.single c (1 : ℝ))) := by
  rcases hb with rfl | rfl <;> cases c <;> ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst] <;> simp [sum_B_eval] <;> norm_num<;> try abel

private lemma jacobi_basis_odd_G2 (b c : B) (hb : b ∈ (({B.G1, B.G2} : Set B) : Set B)) :
    bracket (Pi.single B.G2 (1 : ℝ)) (bracket (Pi.single b (1 : ℝ)) (Pi.single c (1 : ℝ))) =
      bracket (bracket (Pi.single B.G2 (1 : ℝ)) (Pi.single b (1 : ℝ))) (Pi.single c (1 : ℝ)) -
      bracket (Pi.single b (1 : ℝ)) (bracket (Pi.single B.G2 (1 : ℝ)) (Pi.single c (1 : ℝ))) := by
  rcases hb with rfl | rfl <;> cases c <;> ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst] <;> simp [sum_B_eval] <;> norm_num<;> try abel

private lemma jacobi_odd_odd_z (x y z : OSp12)
    (hxgen : ∃ a ∈ (({B.G1, B.G2} : Set B) : Set B), x = Pi.single a (1 : ℝ))
    (hygen : ∃ b ∈ (({B.G1, B.G2} : Set B) : Set B), y = Pi.single b (1 : ℝ)) :
    bracket x (bracket y z) = bracket (bracket x y) z - bracket y (bracket x z) := by
  let S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
  have hz_span : z ∈ Submodule.span ℝ S := by
    have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
      ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
    have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
      rw [show S = Set.range (fun a : B => Pi.single a (1 : ℝ)) by rfl, hrange]
      exact (Pi.basisFun ℝ B).span_eq
    rw [hspan]
    exact Submodule.mem_top
  induction hz_span using Submodule.span_induction with
  | mem z hzgen =>
      rcases hxgen with ⟨a, ha, rfl⟩
      rcases hygen with ⟨b, hb, rfl⟩
      rcases hzgen with ⟨c, rfl⟩
      rcases ha with rfl | rfl
      · exact jacobi_basis_odd_G1 b c hb
      · exact jacobi_basis_odd_G2 b c hb
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left]
  | add u v hu hv huP hvP =>
      simp only [add_lie_proof, lie_add_proof, huP, hvP]<;> try abel
  | smul r u hu huP =>
      simp only [smul_lie_proof, lie_smul_proof, huP, smul_neg, smul_add, smul_sub]<;> try abel

private lemma jacobi_odd_odd_y (x y z : OSp12)
    (hxgen : ∃ a ∈ (({B.G1, B.G2} : Set B) : Set B), x = Pi.single a (1 : ℝ)) :
    y ∈ oddPart → bracket x (bracket y z) = bracket (bracket x y) z - bracket y (bracket x z) := by
  have hodd : ({fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({(Pi.single B.G1 (1 : ℝ) : OSp12), (Pi.single B.G2 (1 : ℝ) : OSp12)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  intro hy
  have hy2 := hy
  rw [oddPart, hodd] at hy2
  clear hy
  induction hy2 using Submodule.span_induction with
  | mem y hygen =>
      have hygen_b : ∃ b ∈ (({B.G1, B.G2} : Set B) : Set B), y = Pi.single b (1 : ℝ) := by
        rcases hygen with rfl | rfl
        · exact ⟨B.G1, Or.inl rfl, rfl⟩
        · exact ⟨B.G2, Or.inr rfl, rfl⟩
      exact jacobi_odd_odd_z x y z hxgen hygen_b
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left]
  | add u v hu hv huP hvP =>
      simp only [add_lie_proof, lie_add_proof, huP, hvP]<;> try abel
  | smul r u hu huP =>
      simp only [smul_lie_proof, lie_smul_proof, huP, smul_neg, smul_add, smul_sub]<;> try abel

private lemma jacobi_odd_odd_proof (x y z : OSp12) (hx : x ∈ oddPart) (hy : y ∈ oddPart) :
    bracket x (bracket y z) = bracket (bracket x y) z - bracket y (bracket x z) := by
  have hodd : ({fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({(Pi.single B.G1 (1 : ℝ) : OSp12), (Pi.single B.G2 (1 : ℝ) : OSp12)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  have hx2 := hx
  rw [oddPart, hodd] at hx2
  clear hx
  induction hx2 using Submodule.span_induction with
  | mem x hxgen =>
      have hxgen_a : ∃ a ∈ (({B.G1, B.G2} : Set B) : Set B), x = Pi.single a (1 : ℝ) := by
        rcases hxgen with rfl | rfl
        · exact ⟨B.G1, Or.inl rfl, rfl⟩
        · exact ⟨B.G2, Or.inr rfl, rfl⟩
      exact jacobi_odd_odd_y x y z hxgen_a hy
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left]
  | add u v hu hv huP hvP =>
      simp only [add_lie_proof, lie_add_proof, huP, hvP]<;> try abel
  | smul r u hu huP =>
      simp only [smul_lie_proof, lie_smul_proof, huP, smul_neg, smul_add, smul_sub]<;> try abel


instance : SuperLieRing OSp12 where
  bracket := bracket
  evenPart := evenPart
  oddPart := oddPart
  add_lie := add_lie_proof
  lie_add := lie_add_proof
  lie_smul := lie_smul_proof
  sup_even_odd := sup_even_odd_proof
  even_odd_inter := even_odd_inter_proof
  even_even_skew := even_even_skew_proof
  even_odd_skew := even_odd_skew_proof
  odd_odd_symm := odd_odd_symm_proof
  jacobi_even := jacobi_even_proof
  jacobi_odd_odd := by
    intro x y z hx hy
    exact jacobi_odd_odd_proof x y z hx hy

end OSp12

end InfoGeometry.Clifford.ConformalSpinorBridge
