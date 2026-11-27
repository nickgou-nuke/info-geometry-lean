/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornE7RootSystem
import InfoGeometry.Algebra.H3ZornE7Simplicity
import Mathlib.Algebra.Lie.Basis.Base
import Mathlib.Algebra.Lie.SerreConstruction

/-!
# Serre presentation map for the split `E₇` TKK Lie algebra `H3ZornTKKLie`

The local `E₇` owner `H3ZornTKKLie` has a 133-dimensional Chevalley basis. This file
evaluates Mathlib's free Lie algebra on its seven simple triples, verifies all six
families of Cartan--Serre relations, and descends the evaluation to a Lie homomorphism
`h3zornE7SerreQuotientMap : LieAlgebra.e₇ ℝ →ₗ⁅ℝ⁆ H3ZornTKKLie`.

Surjectivity follows from `LieAlgebra.lieSpan_range_union_eq_top_of_mem_rootSpace`
using the `IsKilling` root-system base constructed in `H3ZornE7Simplicity`.
Injectivity and the upper dimension bound `Module.finrank ℝ (LieAlgebra.e₇ ℝ) ≤ 133`
follow from an explicit 133-dimensional Chevalley spanning decomposition built via
the Chevalley involution and the 63-element positive-root parent tree.
Together these yield `h3zornE7SerreEquiv : LieAlgebra.e₇ ℝ ≃ₗ⁅ℝ⁆ H3ZornTKKLie`,
`finrank_e7_serre : Module.finrank ℝ (LieAlgebra.e₇ ℝ) = 133`, and
`e7Serre_isSimple : LieAlgebra.IsSimple ℝ (LieAlgebra.e₇ ℝ)`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.H3ZornTKKLieAlgebra
open InfoGeometry.Exceptional.CFSGPort.Chevalley

attribute [local instance] Classical.propDecidable

/-- Evaluate the seven Cartan, positive-root, and negative-root generators in
the already constructed 133-dimensional split `E₇` Lie algebra `H3ZornTKKLie`. -/
def h3zornE7SerreGenerator
    (g : CartanMatrix.Generators (Fin 7)) : H3ZornTKKLie :=
  match g with
  | .H i => e7SimpleH i
  | .E i => e7SimpleE i
  | .F i => e7SimpleF i

/-- The universal Lie homomorphism from the free Lie algebra on the `E₇` Serre
generators to `H3ZornTKKLie`. -/
def h3zornE7FreeSerreEval :
    FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 7)) →ₗ⁅ℝ⁆ H3ZornTKKLie :=
  FreeLieAlgebra.lift ℝ h3zornE7SerreGenerator

@[simp] theorem h3zornE7FreeSerreEval_H (i : Fin 7) :
    h3zornE7FreeSerreEval
      (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = e7SimpleH i := by
  simp [h3zornE7FreeSerreEval, h3zornE7SerreGenerator]

@[simp] theorem h3zornE7FreeSerreEval_E (i : Fin 7) :
    h3zornE7FreeSerreEval
      (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i)) = e7SimpleE i := by
  simp [h3zornE7FreeSerreEval, h3zornE7SerreGenerator]

@[simp] theorem h3zornE7FreeSerreEval_F (i : Fin 7) :
    h3zornE7FreeSerreEval
      (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)) = e7SimpleF i := by
  simp [h3zornE7FreeSerreEval, h3zornE7SerreGenerator]

/-- The free-Lie evaluation kills the Cartan-generator commutation relations. -/
theorem h3zornE7FreeSerreEval_HH (i j : Fin 7) :
    h3zornE7FreeSerreEval (CartanMatrix.Relations.HH ℝ (i, j)) = 0 := by
  change h3zornE7FreeSerreEval
    ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i),
      FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H j)⁆ = 0
  rw [LieHom.map_lie, h3zornE7FreeSerreEval_H, h3zornE7FreeSerreEval_H]
  exact e7SimpleH_comm i j

/-- The free-Lie evaluation kills the simple positive/negative root relations. -/
theorem h3zornE7FreeSerreEval_EF (i j : Fin 7) :
    h3zornE7FreeSerreEval (CartanMatrix.Relations.EF ℝ (i, j)) = 0 := by
  by_cases hij : i = j
  · subst j
    simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair]
    change h3zornE7FreeSerreEval
      (⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
        FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)⁆ -
        FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = 0
    rw [map_sub, LieHom.map_lie, h3zornE7FreeSerreEval_E,
      h3zornE7FreeSerreEval_F, h3zornE7FreeSerreEval_H, e7Simple_bracket_EF_same, sub_self]
  · simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, hij, ↓reduceIte]
    change h3zornE7FreeSerreEval
      ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
        FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F j)⁆ = 0
    rw [LieHom.map_lie, h3zornE7FreeSerreEval_E, h3zornE7FreeSerreEval_F]
    exact e7Simple_bracket_EF_ne hij

/-- The free-Lie evaluation kills the `H,E` Cartan relations. -/
theorem h3zornE7FreeSerreEval_HE (i j : Fin 7) :
    h3zornE7FreeSerreEval
      (CartanMatrix.Relations.HE ℝ (CartanMatrix.E 7) (i, j)) = 0 := by
  simp only [CartanMatrix.Relations.HE, Function.uncurry_apply_pair, Function.comp_apply]
  rw [← Int.cast_smul_eq_zsmul ℝ, map_sub, LieHom.map_lie, h3zornE7FreeSerreEval_H,
    h3zornE7FreeSerreEval_E, map_smul, h3zornE7FreeSerreEval_E, e7Simple_bracket_HE]
  have hentry := congrFun (congrFun h3zornE7_cartan_eq_mathlib i) j
  rw [← congrArg (fun z : ℤ => (z : ℝ)) hentry, sub_self]

/-- The free-Lie evaluation kills the `H,F` Cartan relations. -/
theorem h3zornE7FreeSerreEval_HF (i j : Fin 7) :
    h3zornE7FreeSerreEval
      (CartanMatrix.Relations.HF ℝ (CartanMatrix.E 7) (i, j)) = 0 := by
  simp only [CartanMatrix.Relations.HF, Function.uncurry_apply_pair, Function.comp_apply]
  rw [← Int.cast_smul_eq_zsmul ℝ, map_add, LieHom.map_lie, h3zornE7FreeSerreEval_H,
    h3zornE7FreeSerreEval_F, map_smul, h3zornE7FreeSerreEval_F, e7Simple_bracket_HF]
  have hentry := congrFun (congrFun h3zornE7_cartan_eq_mathlib i) j
  rw [← congrArg (fun z : ℤ => (z : ℝ)) hentry]
  simp

private theorem map_iterate_ad {R L L' : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ L') (x y : L) (n : ℕ) :
    f (Nat.iterate (fun z => ⁅x, z⁆) n y) =
      Nat.iterate (fun z => ⁅f x, z⁆) n (f y) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', LieHom.map_lie, ih]

private theorem ad_pow_apply_eq_iterate {R L : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] (x y : L) (n : ℕ) :
    ((LieAlgebra.ad R L x) ^ n) y = Nat.iterate (fun z => ⁅x, z⁆) n y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change (LieAlgebra.ad R L x) (((LieAlgebra.ad R L x) ^ n) y) = _
      rw [ih]
      simp only [LieAlgebra.ad_apply, Function.iterate_succ_apply']

private theorem e7_cartan_offdiag_nonpos {i j : Fin 7} (hij : i ≠ j) :
    Tag.cartan .E7 i j ≤ 0 := by
  have hchk : (List.finRange 7).all (fun a => (List.finRange 7).all (fun b =>
      if a = b then true else decide (Tag.cartan .E7 a b ≤ 0))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have h := hchk i j
  simpa [hij] using h

private theorem e7_serre_exponent {i j : Fin 7} (hij : i ≠ j) :
    (-Tag.cartan .E7 i j).toNat + 1 = (1 - Tag.cartan .E7 i j).toNat := by
  have h0 := e7_cartan_offdiag_nonpos hij
  omega

/-- The free-Lie evaluation kills the positive-root Serre relations. -/
theorem h3zornE7FreeSerreEval_adE (i j : Fin 7) :
    h3zornE7FreeSerreEval
      (CartanMatrix.Relations.adE ℝ (CartanMatrix.E 7) (i, j)) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [CartanMatrix.Relations.adE, Function.uncurry_apply_pair]
  · simp only [CartanMatrix.Relations.adE, Function.uncurry_apply_pair, Function.comp_apply]
    rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie,
      h3zornE7FreeSerreEval_E, h3zornE7FreeSerreEval_E, ← Function.iterate_succ_apply]
    rw [Nat.succ_eq_add_one, ← congrFun (congrFun h3zornE7_cartan_eq_mathlib i) j,
      e7_serre_exponent hij]
    exact e7Simple_serre_E hij

/-- The free-Lie evaluation kills the negative-root Serre relations. -/
theorem h3zornE7FreeSerreEval_adF (i j : Fin 7) :
    h3zornE7FreeSerreEval
      (CartanMatrix.Relations.adF ℝ (CartanMatrix.E 7) (i, j)) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [CartanMatrix.Relations.adF, Function.uncurry_apply_pair]
  · simp only [CartanMatrix.Relations.adF, Function.uncurry_apply_pair, Function.comp_apply]
    rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie,
      h3zornE7FreeSerreEval_F, h3zornE7FreeSerreEval_F, ← Function.iterate_succ_apply]
    rw [Nat.succ_eq_add_one, ← congrFun (congrFun h3zornE7_cartan_eq_mathlib i) j,
      e7_serre_exponent hij]
    exact e7Simple_serre_F hij

/-- The evaluation kernel contains the full Lie ideal generated by all `E₇`
Cartan--Serre relations. -/
theorem h3zornE7FreeSerreEval_serreIdeal :
    CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7) ≤
      h3zornE7FreeSerreEval.ker := by
  rw [CartanMatrix.Relations.toIdeal, LieSubmodule.lieSpan_le]
  intro x hx
  simp only [CartanMatrix.Relations.toSet, Set.mem_union, Set.mem_range] at hx
  rcases hx with (((((⟨⟨i, j⟩, rfl⟩ | ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) |
      ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩)
  · exact h3zornE7FreeSerreEval_HH i j
  · exact h3zornE7FreeSerreEval_EF i j
  · exact h3zornE7FreeSerreEval_HE i j
  · exact h3zornE7FreeSerreEval_HF i j
  · exact h3zornE7FreeSerreEval_adE i j
  · exact h3zornE7FreeSerreEval_adF i j

private theorem h3zornE7FreeSerreEval_serreIdeal_submodule :
    (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7)).toSubmodule ≤
      LinearMap.ker h3zornE7FreeSerreEval.toLinearMap :=
  h3zornE7FreeSerreEval_serreIdeal

/-- The free-Lie evaluation descends to Mathlib's Serre-quotient carrier
`LieAlgebra.e₇ ℝ →ₗ⁅ℝ⁆ H3ZornTKKLie`. -/
noncomputable def h3zornE7SerreQuotientMap :
    LieAlgebra.e₇ ℝ →ₗ⁅ℝ⁆ H3ZornTKKLie := by
  let I := CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7)
  have hI : I.toSubmodule ≤ LinearMap.ker h3zornE7FreeSerreEval.toLinearMap :=
    h3zornE7FreeSerreEval_serreIdeal
  refine { I.toSubmodule.liftQ h3zornE7FreeSerreEval.toLinearMap hI with map_lie' := ?_ }
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
          change h3zornE7FreeSerreEval ⁅x, y⁆ =
            ⁅h3zornE7FreeSerreEval x, h3zornE7FreeSerreEval y⁆
          exact LieHom.map_lie h3zornE7FreeSerreEval x y

@[simp] theorem h3zornE7SerreQuotientMap_H (i : Fin 7) :
    h3zornE7SerreQuotientMap
      (Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i))) =
      e7SimpleH i := by
  change (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7)).toSubmodule.liftQ
    h3zornE7FreeSerreEval.toLinearMap h3zornE7FreeSerreEval_serreIdeal_submodule
    (Submodule.Quotient.mk _) = _
  simp [h3zornE7FreeSerreEval_H]

@[simp] theorem h3zornE7SerreQuotientMap_E (i : Fin 7) :
    h3zornE7SerreQuotientMap
      (Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i))) =
      e7SimpleE i := by
  change (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7)).toSubmodule.liftQ
    h3zornE7FreeSerreEval.toLinearMap h3zornE7FreeSerreEval_serreIdeal_submodule
    (Submodule.Quotient.mk _) = _
  simp [h3zornE7FreeSerreEval_E]

@[simp] theorem h3zornE7SerreQuotientMap_F (i : Fin 7) :
    h3zornE7SerreQuotientMap
      (Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i))) =
      e7SimpleF i := by
  change (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7)).toSubmodule.liftQ
    h3zornE7FreeSerreEval.toLinearMap h3zornE7FreeSerreEval_serreIdeal_submodule
    (Submodule.Quotient.mk _) = _
  simp [h3zornE7FreeSerreEval_F]

/-! ### `IsKilling` surjectivity onto `H3ZornTKKLie` -/

private theorem e7RootCoord_fSimple (i : Fin 7) :
    e7RootCoord (e7FSimpleIdx i) = -e7RootCoord (e7ESimpleIdx i) := by
  have hchk : (List.finRange 7).all (fun i =>
      List.ofFn (e7RootCoord (e7FSimpleIdx i)) ==
        List.ofFn (-e7RootCoord (e7ESimpleIdx i))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
  exact List.ofFn_injective (hchk i)

private theorem e7SimpleE_mem_rootSpace (i : Fin 7) :
    e7SimpleE i ∈ LieAlgebra.rootSpace h3zornE7Cartan (e7SimpleMathlibRoot i).1 := by
  rw [e7SimpleE_eq_rootVec]
  exact e7RootVec_mem_rootSpace (e7ESimpleIdx i)

private theorem e7SimpleF_mem_neg_rootSpace (i : Fin 7) :
    e7SimpleF i ∈ LieAlgebra.rootSpace h3zornE7Cartan (-(e7SimpleMathlibRoot i).1) := by
  rw [LieAlgebra.rootSpace, LieModule.mem_genWeightSpace]
  intro H
  refine ⟨1, ?_⟩
  rw [pow_one]
  change ⁅(H : H3ZornTKKLie), e7SimpleF i⁆ - (-(e7SimpleMathlibRoot i).1) H • e7SimpleF i = 0
  rw [e7SimpleF_eq_rootVec, lie_smul, e7RootVec_bracket_cartan H (e7FSimpleIdx i), smul_smul]
  have hwt : h3zornE7RootWeight (e7FSimpleIdx i) H = -((e7SimpleMathlibRoot i).1 H) := by
    have hrep := e7CartanBasis.sum_repr H
    conv_lhs => rw [← hrep]
    conv_rhs => rw [← hrep]
    simp only [map_sum, map_smul, smul_eq_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : h3zornE7RootWeight (e7FSimpleIdx i) (e7CartanBasis j) =
        -((e7SimpleMathlibRoot i).1 (e7CartanBasis j)) := by
      have he7 : (e7CartanBasis j : h3zornE7Cartan) =
          ⟨e7SimpleH j, e7SimpleH_mem_h3zornE7Cartan j⟩ :=
        Subtype.ext (e7CartanBasis_apply j)
      rw [he7]
      change h3zornE7RootWeight (e7FSimpleIdx i) ⟨e7SimpleH j, e7SimpleH_mem_h3zornE7Cartan j⟩ =
        -h3zornE7RootWeight (e7ESimpleIdx i) ⟨e7SimpleH j, e7SimpleH_mem_h3zornE7Cartan j⟩
      rw [h3zornE7RootWeight_simpleH, h3zornE7RootWeight_simpleH]
      simp only [e7RootEigenvalue, e7RootCoord_fSimple, Pi.neg_apply, mul_neg,
        Finset.sum_neg_distrib, Int.cast_neg]
    rw [hj]
    ring
  have hneg_app : (-(e7SimpleMathlibRoot i).1) H = -((e7SimpleMathlibRoot i).1 H) := rfl
  rw [hwt, hneg_app, smul_smul, mul_comm, sub_self]

/-- The 14 simple positive and negative root vectors `e7SimpleE` and `e7SimpleF`
generate all of `H3ZornTKKLie` as a Lie subalgebra. -/
theorem h3zornE7_lieSpan_EF_eq_top :
    LieSubalgebra.lieSpan ℝ H3ZornTKKLie (Set.range e7SimpleE ∪ Set.range e7SimpleF) = ⊤ := by
  let e : h3zornE7RootSystemBase.support → H3ZornTKKLie :=
    fun α => e7SimpleE (h3zornE7BaseSupportEquiv.symm α)
  let f : h3zornE7RootSystemBase.support → H3ZornTKKLie :=
    fun α => e7SimpleF (h3zornE7BaseSupportEquiv.symm α)
  have hspan := LieAlgebra.lieSpan_range_union_eq_top_of_mem_rootSpace
    (K := ℝ) (L := H3ZornTKKLie) (H := h3zornE7Cartan) h3zornE7RootSystemBase e f
    (fun α => by
      let i := h3zornE7BaseSupportEquiv.symm α
      have hi : (h3zornE7BaseSupportEquiv i : h3zornE7Cartan.root) = α.1 :=
        congrArg Subtype.val (h3zornE7BaseSupportEquiv.apply_symm_apply α)
      have hwt : (e7SimpleMathlibRoot i).1 = α.1.1 := congrArg Subtype.val hi
      have hcor : ((LieAlgebra.IsKilling.rootSystem h3zornE7Cartan).coroot α : H3ZornTKKLie) =
          e7SimpleH i := by
        rw [LieAlgebra.IsKilling.rootSystem_coroot_apply, ← hwt, e7Simple_coroot_eq]
      rw [hcor]
      exact e7Simple_isSl2Triple i)
    (fun α => by
      let i := h3zornE7BaseSupportEquiv.symm α
      have hi : (h3zornE7BaseSupportEquiv i : h3zornE7Cartan.root) = α.1 :=
        congrArg Subtype.val (h3zornE7BaseSupportEquiv.apply_symm_apply α)
      have hwt : (e7SimpleMathlibRoot i).1 = α.1.1 := congrArg Subtype.val hi
      change e7SimpleE i ∈ LieAlgebra.rootSpace h3zornE7Cartan (α.1.1 : h3zornE7Cartan → ℝ)
      rw [← hwt]
      exact e7SimpleE_mem_rootSpace i)
    (fun α => by
      let i := h3zornE7BaseSupportEquiv.symm α
      have hi : (h3zornE7BaseSupportEquiv i : h3zornE7Cartan.root) = α.1 :=
        congrArg Subtype.val (h3zornE7BaseSupportEquiv.apply_symm_apply α)
      have hwt : (e7SimpleMathlibRoot i).1 = α.1.1 := congrArg Subtype.val hi
      change e7SimpleF i ∈ LieAlgebra.rootSpace h3zornE7Cartan (-(α.1.1 : h3zornE7Cartan → ℝ))
      rw [← hwt]
      exact e7SimpleF_mem_neg_rootSpace i)
  have he : Set.range e = Set.range e7SimpleE := by
    ext x
    constructor
    · rintro ⟨α, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨h3zornE7BaseSupportEquiv i, by simp [e]⟩
  have hf : Set.range f = Set.range e7SimpleF := by
    ext x
    constructor
    · rintro ⟨α, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨h3zornE7BaseSupportEquiv i, by simp [f]⟩
  rwa [he, hf] at hspan

/-- The 21 simple Cartan and root generators generate all of `H3ZornTKKLie`. -/
theorem h3zornE7_lieSpan_HEF_eq_top :
    LieSubalgebra.lieSpan ℝ H3ZornTKKLie
      (Set.range e7SimpleH ∪ Set.range e7SimpleE ∪ Set.range e7SimpleF) = ⊤ := by
  rw [eq_top_iff, ← h3zornE7_lieSpan_EF_eq_top]
  exact LieSubalgebra.lieSpan_mono (by
    rintro x (hx | hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx)

/-- Any Lie subalgebra of `H3ZornTKKLie` containing `e7SimpleE` and `e7SimpleF`
equals `⊤`. -/
theorem h3zornE7_simple_generators_generate
    (S : LieSubalgebra ℝ H3ZornTKKLie)
    (hE : ∀ i : Fin 7, e7SimpleE i ∈ S)
    (hF : ∀ i : Fin 7, e7SimpleF i ∈ S) : S = ⊤ := by
  rw [eq_top_iff, ← h3zornE7_lieSpan_EF_eq_top, LieSubalgebra.lieSpan_le]
  rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact hE i
  · exact hF i

/-- The descended Serre map is surjective onto `H3ZornTKKLie`. -/
theorem h3zornE7SerreQuotientMap_surjective :
    Function.Surjective h3zornE7SerreQuotientMap := by
  apply (LieHom.range_eq_top h3zornE7SerreQuotientMap).mp
  apply h3zornE7_simple_generators_generate h3zornE7SerreQuotientMap.range
  · intro i
    rw [LieHom.mem_range]
    exact ⟨Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i)),
      h3zornE7SerreQuotientMap_E i⟩
  · intro i
    rw [LieHom.mem_range]
    exact ⟨Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)),
      h3zornE7SerreQuotientMap_F i⟩

/-- A linear section obtained by lifting the 133 Chevalley basis vectors through
the surjective Serre map. -/
noncomputable def h3zornE7SerreQuotientSection :
    H3ZornTKKLie →ₗ[ℝ] LieAlgebra.e₇ ℝ :=
  e7ChevalleyBasis.constr ℝ fun i =>
    Classical.choose (h3zornE7SerreQuotientMap_surjective (e7ChevalleyBasis i))

theorem h3zornE7SerreQuotientMap_section_basis (i : Fin 7 ⊕ Fin 126) :
    h3zornE7SerreQuotientMap
      (h3zornE7SerreQuotientSection (e7ChevalleyBasis i)) = e7ChevalleyBasis i := by
  rw [h3zornE7SerreQuotientSection, e7ChevalleyBasis.constr_basis]
  exact Classical.choose_spec
    (h3zornE7SerreQuotientMap_surjective (e7ChevalleyBasis i))

theorem h3zornE7SerreQuotientMap_section_leftInverse :
    h3zornE7SerreQuotientMap.toLinearMap.comp h3zornE7SerreQuotientSection = LinearMap.id := by
  apply e7ChevalleyBasis.ext
  intro i
  simp [LinearMap.comp_apply, h3zornE7SerreQuotientMap_section_basis]

theorem h3zornE7SerreQuotientSection_injective :
    Function.Injective h3zornE7SerreQuotientSection := by
  intro x y hxy
  have h := congrArg h3zornE7SerreQuotientMap.toLinearMap hxy
  change (h3zornE7SerreQuotientMap.toLinearMap.comp h3zornE7SerreQuotientSection) x =
      (h3zornE7SerreQuotientMap.toLinearMap.comp h3zornE7SerreQuotientSection) y at h
  rw [h3zornE7SerreQuotientMap_section_leftInverse, LinearMap.id_apply, LinearMap.id_apply] at h
  exact h

theorem h3zornE7SerreQuotient_finrank_lower_bound
    [FiniteDimensional ℝ (LieAlgebra.e₇ ℝ)] :
    133 ≤ Module.finrank ℝ (LieAlgebra.e₇ ℝ) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := h3zornE7SerreQuotientSection) h3zornE7SerreQuotientSection_injective
  rw [finrank_H3ZornTKKLie] at h
  exact h

noncomputable def h3zornE7SerreQuotientEquivOfFinrank
    [FiniteDimensional ℝ (LieAlgebra.e₇ ℝ)]
    (hdim : Module.finrank ℝ (LieAlgebra.e₇ ℝ) = 133) :
    LieAlgebra.e₇ ℝ ≃ₗ⁅ℝ⁆ H3ZornTKKLie := by
  have hdim' : Module.finrank ℝ (LieAlgebra.e₇ ℝ) = Module.finrank ℝ H3ZornTKKLie := by
    rw [hdim, finrank_H3ZornTKKLie]
  have hsurj : Function.Surjective h3zornE7SerreQuotientMap.toLinearMap :=
    h3zornE7SerreQuotientMap_surjective
  have hinj : Function.Injective h3zornE7SerreQuotientMap.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').2 hsurj
  exact LieEquiv.ofBijective h3zornE7SerreQuotientMap ⟨hinj, hsurj⟩

/-! ### Serre quotient finite-dimensionality (133D Chevalley span) and isomorphism closure -/

private def e7SerreMk :
    FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 7)) →ₗ⁅ℝ⁆ LieAlgebra.e₇ ℝ where
  toLinearMap := (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7)).toSubmodule.mkQ
  map_lie' := fun {_ _} => rfl

/-- The simple Cartan generators inside Mathlib's `LieAlgebra.e₇ ℝ`. -/
def e7SerreH (i : Fin 7) : LieAlgebra.e₇ ℝ :=
  e7SerreMk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i))

/-- The simple positive root generators inside Mathlib's `LieAlgebra.e₇ ℝ`. -/
def e7SerreE (i : Fin 7) : LieAlgebra.e₇ ℝ :=
  e7SerreMk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i))

/-- The simple negative root generators inside Mathlib's `LieAlgebra.e₇ ℝ`. -/
def e7SerreF (i : Fin 7) : LieAlgebra.e₇ ℝ :=
  e7SerreMk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i))

/-- Any Lie subalgebra of `LieAlgebra.e₇ ℝ` containing the 21 Chevalley generators
equals the whole Lie algebra. -/
theorem e7Serre_generators_generate (S : LieSubalgebra ℝ (LieAlgebra.e₇ ℝ))
    (hH : ∀ i, e7SerreH i ∈ S)
    (hE : ∀ i, e7SerreE i ∈ S)
    (hF : ∀ i, e7SerreF i ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let g : CartanMatrix.Generators (Fin 7) → S := fun gen =>
    match gen with
    | .H i => ⟨e7SerreH i, hH i⟩
    | .E i => ⟨e7SerreE i, hE i⟩
    | .F i => ⟨e7SerreF i, hF i⟩
  have hcomp : S.incl.comp (FreeLieAlgebra.lift ℝ g) = e7SerreMk := by
    apply FreeLieAlgebra.hom_ext
    intro gen
    cases gen with
    | H i => simp [g, e7SerreH]
    | E i => simp [g, e7SerreE]
    | F i => simp [g, e7SerreF]
  have hy : e7SerreMk y = S.incl (FreeLieAlgebra.lift ℝ g y) := by
    rw [← hcomp]
    rfl
  change e7SerreMk y ∈ S
  rw [hy]
  exact (FreeLieAlgebra.lift ℝ g y).2

private theorem e7SerreMk_mem_ideal_zero
    {x : FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 7))}
    (hx : x ∈ CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 7)) :
    e7SerreMk x = 0 := by
  change LieSubmodule.Quotient.mk x = 0
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan hx

private theorem e7SerreH_comm (i j : Fin 7) : ⁅e7SerreH i, e7SerreH j⁆ = 0 := by
  have hx : CartanMatrix.Relations.HH ℝ (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 7) :=
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(i, j), rfl⟩))))
  have h := e7SerreMk_mem_ideal_zero hx
  change e7SerreMk
    ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i),
      FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H j)⁆ = 0 at h
  simpa [LieHom.map_lie, e7SerreH] using h

private theorem e7Serre_bracket_EF_same (i : Fin 7) :
    ⁅e7SerreE i, e7SerreF i⁆ = e7SerreH i := by
  have hx : CartanMatrix.Relations.EF ℝ (i, i) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 7) :=
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, i), rfl⟩))))
  have h := e7SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, ↓reduceIte] at h
  change e7SerreMk
    (⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
      FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)⁆ -
      FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = 0 at h
  rw [map_sub, LieHom.map_lie] at h
  exact sub_eq_zero.mp h

private theorem e7Serre_bracket_EF_ne {i j : Fin 7} (hij : i ≠ j) :
    ⁅e7SerreE i, e7SerreF j⁆ = 0 := by
  have hx : CartanMatrix.Relations.EF ℝ (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 7) :=
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩))))
  have h := e7SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, hij, ↓reduceIte] at h
  change e7SerreMk
    ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
      FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F j)⁆ = 0 at h
  simpa [LieHom.map_lie, e7SerreE, e7SerreF] using h

private theorem e7Serre_bracket_HE (i j : Fin 7) :
    ⁅e7SerreH i, e7SerreE j⁆ = ((Tag.cartan .E7 i j : ℤ) : ℝ) • e7SerreE j := by
  have hx : CartanMatrix.Relations.HE ℝ (CartanMatrix.E 7) (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 7) :=
    Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩)))
  have h := e7SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.HE, Function.uncurry_apply_pair, Function.comp_apply] at h
  rw [← Int.cast_smul_eq_zsmul ℝ, map_sub, LieHom.map_lie, map_smul] at h
  have hentry := congrFun (congrFun h3zornE7_cartan_eq_mathlib i) j
  rw [← hentry] at h
  exact sub_eq_zero.mp h

private theorem e7Serre_bracket_HF (i j : Fin 7) :
    ⁅e7SerreH i, e7SerreF j⁆ = (-(Tag.cartan .E7 i j : ℤ) : ℝ) • e7SerreF j := by
  have hx : CartanMatrix.Relations.HF ℝ (CartanMatrix.E 7) (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 7) :=
    Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩))
  have h := e7SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.HF, Function.uncurry_apply_pair, Function.comp_apply] at h
  rw [← Int.cast_smul_eq_zsmul ℝ, map_add, LieHom.map_lie, map_smul] at h
  have hentry := congrFun (congrFun h3zornE7_cartan_eq_mathlib i) j
  rw [← hentry] at h
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h

private theorem e7Serre_adE_iter {i j : Fin 7} (hij : i ≠ j) :
    Nat.iterate (fun x => ⁅e7SerreE i, x⁆)
      (1 - Tag.cartan .E7 i j).toNat (e7SerreE j) = 0 := by
  have hx : CartanMatrix.Relations.adE ℝ (CartanMatrix.E 7) (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 7) :=
    Or.inl (Or.inr ⟨(i, j), rfl⟩)
  have h := e7SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.adE, Function.uncurry_apply_pair, Function.comp_apply] at h
  rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie,
    ← Function.iterate_succ_apply] at h
  have hentry := congrFun (congrFun h3zornE7_cartan_eq_mathlib i) j
  rw [Nat.succ_eq_add_one, ← hentry, e7_serre_exponent hij] at h
  exact h

private theorem e7Serre_adF_iter {i j : Fin 7} (hij : i ≠ j) :
    Nat.iterate (fun x => ⁅e7SerreF i, x⁆)
      (1 - Tag.cartan .E7 i j).toNat (e7SerreF j) = 0 := by
  have hx : CartanMatrix.Relations.adF ℝ (CartanMatrix.E 7) (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 7) :=
    Or.inr ⟨(i, j), rfl⟩
  have h := e7SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.adF, Function.uncurry_apply_pair, Function.comp_apply] at h
  rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie,
    ← Function.iterate_succ_apply] at h
  have hentry := congrFun (congrFun h3zornE7_cartan_eq_mathlib i) j
  rw [Nat.succ_eq_add_one, ← hentry, e7_serre_exponent hij] at h
  exact h

private theorem e7_cartan_diag (i : Fin 7) : Tag.cartan .E7 i i = 2 := by
  fin_cases i <;> decide

private theorem e7Serre_adE_zero {i j : Fin 7} (hc : Tag.cartan .E7 i j = 0) :
    ⁅e7SerreE i, e7SerreE j⁆ = 0 := by
  have hij : i ≠ j := by
    intro heq
    subst heq
    have hd := e7_cartan_diag i
    omega
  have h := e7Serre_adE_iter hij
  rw [hc] at h
  simpa using h

private theorem e7Serre_adE_negOne {i j : Fin 7} (hc : Tag.cartan .E7 i j = -1) :
    ⁅e7SerreE i, ⁅e7SerreE i, e7SerreE j⁆⁆ = 0 := by
  have hij : i ≠ j := by
    intro heq
    subst heq
    have hd := e7_cartan_diag i
    omega
  have h := e7Serre_adE_iter hij
  rw [hc] at h
  simpa using h

private theorem e7_cartan_offdiag_cases {i j : Fin 7} (hij : i ≠ j) :
    Tag.cartan .E7 i j = 0 ∨ Tag.cartan .E7 i j = -1 := by
  have hchk : (List.finRange 7).all (fun a => (List.finRange 7).all (fun b =>
      if a = b then true else decide (Tag.cartan .E7 a b = 0 ∨ Tag.cartan .E7 a b = -1))) =
      true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have h := hchk i j
  simpa [hij] using h

private theorem e7Serre_adE_sq_gen (i j : Fin 7) :
    ⁅e7SerreE i, ⁅e7SerreE i, e7SerreE j⁆⁆ = 0 := by
  by_cases hij : i = j
  · subst hij
    simp [lie_self]
  · rcases e7_cartan_offdiag_cases hij with h0 | h1
    · rw [e7Serre_adE_zero h0, lie_zero]
    · exact e7Serre_adE_negOne h1

/-! #### Chevalley involution on `LieAlgebra.e₇ ℝ` -/

private def e7SerreChevalleyGen
    (g : CartanMatrix.Generators (Fin 7)) : LieAlgebra.e₇ ℝ :=
  match g with
  | .H i => -e7SerreH i
  | .E i => e7SerreF i
  | .F i => e7SerreE i

private noncomputable def e7SerreChevalleyFree :
    FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 7)) →ₗ⁅ℝ⁆ LieAlgebra.e₇ ℝ :=
  FreeLieAlgebra.lift ℝ e7SerreChevalleyGen

private theorem e7SerreChevalleyFree_serreIdeal :
    CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7) ≤
      e7SerreChevalleyFree.ker := by
  rw [CartanMatrix.Relations.toIdeal, LieSubmodule.lieSpan_le]
  intro x hx
  simp only [CartanMatrix.Relations.toSet, Set.mem_union, Set.mem_range] at hx
  rcases hx with (((((⟨⟨i, j⟩, rfl⟩ | ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) |
      ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩)
  · change e7SerreChevalleyFree
      ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i),
        FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H j)⁆ = 0
    simp [e7SerreChevalleyFree, e7SerreChevalleyGen, e7SerreH_comm]
  · change e7SerreChevalleyFree (CartanMatrix.Relations.EF ℝ (i, j)) = 0
    by_cases hij : i = j
    · subst hij
      simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, ↓reduceIte]
      change e7SerreChevalleyFree
        (⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
          FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)⁆ -
          FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = 0
      simp only [map_sub, LieHom.map_lie, e7SerreChevalleyFree,
        FreeLieAlgebra.lift_of_apply, e7SerreChevalleyGen]
      rw [← lie_skew (e7SerreF i) (e7SerreE i), e7Serre_bracket_EF_same, sub_neg_eq_add,
        neg_add_cancel]
    · simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, hij, ↓reduceIte]
      change e7SerreChevalleyFree
        ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
          FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F j)⁆ = 0
      simp only [LieHom.map_lie, e7SerreChevalleyFree, FreeLieAlgebra.lift_of_apply,
        e7SerreChevalleyGen]
      rw [← lie_skew (e7SerreF i) (e7SerreE j), e7Serre_bracket_EF_ne (Ne.symm hij), neg_zero]
  · change e7SerreChevalleyFree
      (CartanMatrix.Relations.HE ℝ (CartanMatrix.E 7) (i, j)) = 0
    simp only [CartanMatrix.Relations.HE, Function.uncurry_apply_pair, Function.comp_apply]
    rw [← Int.cast_smul_eq_zsmul ℝ, map_sub, LieHom.map_lie, map_smul]
    simp only [e7SerreChevalleyFree, FreeLieAlgebra.lift_of_apply, e7SerreChevalleyGen,
      neg_lie, e7Serre_bracket_HF]
    have hentry := congrFun (congrFun h3zornE7_cartan_eq_mathlib i) j
    rw [← hentry, neg_smul, neg_neg, sub_self]
  · change e7SerreChevalleyFree
      (CartanMatrix.Relations.HF ℝ (CartanMatrix.E 7) (i, j)) = 0
    simp only [CartanMatrix.Relations.HF, Function.uncurry_apply_pair, Function.comp_apply]
    rw [← Int.cast_smul_eq_zsmul ℝ, map_add, LieHom.map_lie, map_smul]
    simp only [e7SerreChevalleyFree, FreeLieAlgebra.lift_of_apply, e7SerreChevalleyGen,
      neg_lie, e7Serre_bracket_HE]
    have hentry := congrFun (congrFun h3zornE7_cartan_eq_mathlib i) j
    rw [← hentry, neg_add_cancel]
  · change e7SerreChevalleyFree
      (CartanMatrix.Relations.adE ℝ (CartanMatrix.E 7) (i, j)) = 0
    by_cases hij : i = j
    · subst hij
      simp [CartanMatrix.Relations.adE, Function.uncurry_apply_pair]
    · simp only [CartanMatrix.Relations.adE, Function.uncurry_apply_pair, Function.comp_apply]
      rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie,
        ← Function.iterate_succ_apply]
      simp only [e7SerreChevalleyFree, FreeLieAlgebra.lift_of_apply, e7SerreChevalleyGen]
      have hentry := congrFun (congrFun h3zornE7_cartan_eq_mathlib i) j
      rw [Nat.succ_eq_add_one, ← hentry, e7_serre_exponent hij]
      exact e7Serre_adF_iter hij
  · change e7SerreChevalleyFree
      (CartanMatrix.Relations.adF ℝ (CartanMatrix.E 7) (i, j)) = 0
    by_cases hij : i = j
    · subst hij
      simp [CartanMatrix.Relations.adF, Function.uncurry_apply_pair]
    · simp only [CartanMatrix.Relations.adF, Function.uncurry_apply_pair, Function.comp_apply]
      rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie,
        ← Function.iterate_succ_apply]
      simp only [e7SerreChevalleyFree, FreeLieAlgebra.lift_of_apply, e7SerreChevalleyGen]
      have hentry := congrFun (congrFun h3zornE7_cartan_eq_mathlib i) j
      rw [Nat.succ_eq_add_one, ← hentry, e7_serre_exponent hij]
      exact e7Serre_adE_iter hij

private noncomputable def e7SerreChevalleyHom :
    LieAlgebra.e₇ ℝ →ₗ⁅ℝ⁆ LieAlgebra.e₇ ℝ :=
  { (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7)).toSubmodule.liftQ
      e7SerreChevalleyFree.toLinearMap e7SerreChevalleyFree_serreIdeal with
    map_lie' := by
      intro x y
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
          induction y using Submodule.Quotient.induction_on with
          | _ y =>
              change e7SerreChevalleyFree ⁅x, y⁆ =
                ⁅e7SerreChevalleyFree x, e7SerreChevalleyFree y⁆
              exact LieHom.map_lie e7SerreChevalleyFree x y }

@[simp] private theorem e7SerreChevalleyHom_H (i : Fin 7) :
    e7SerreChevalleyHom (e7SerreH i) = -e7SerreH i := by
  change e7SerreChevalleyFree (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = _
  simp [e7SerreChevalleyFree, e7SerreChevalleyGen]

@[simp] private theorem e7SerreChevalleyHom_E (i : Fin 7) :
    e7SerreChevalleyHom (e7SerreE i) = e7SerreF i := by
  change e7SerreChevalleyFree (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i)) = _
  simp [e7SerreChevalleyFree, e7SerreChevalleyGen]

@[simp] private theorem e7SerreChevalleyHom_F (i : Fin 7) :
    e7SerreChevalleyHom (e7SerreF i) = e7SerreE i := by
  change e7SerreChevalleyFree (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)) = _
  simp [e7SerreChevalleyFree, e7SerreChevalleyGen]

private theorem e7SerreChevalleyHom_involutive (x : LieAlgebra.e₇ ℝ) :
    e7SerreChevalleyHom (e7SerreChevalleyHom x) = x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hcomp : (e7SerreChevalleyHom.comp e7SerreChevalleyHom).comp e7SerreMk = e7SerreMk := by
    apply FreeLieAlgebra.hom_ext
    intro gen
    cases gen with
    | H i =>
        change e7SerreChevalleyHom (e7SerreChevalleyHom (e7SerreH i)) = e7SerreH i
        simp
    | E i =>
        change e7SerreChevalleyHom (e7SerreChevalleyHom (e7SerreE i)) = e7SerreE i
        simp
    | F i =>
        change e7SerreChevalleyHom (e7SerreChevalleyHom (e7SerreF i)) = e7SerreF i
        simp
  exact congrArg (fun f => f y) hcomp

/-- The Chevalley involution on `LieAlgebra.e₇ ℝ`, swapping `E_i ↔ F_i` and negating `H_i`. -/
noncomputable def e7SerreChevalleyInv :
    LieAlgebra.e₇ ℝ ≃ₗ⁅ℝ⁆ LieAlgebra.e₇ ℝ :=
  LieEquiv.ofBijective e7SerreChevalleyHom
    ⟨Function.LeftInverse.injective e7SerreChevalleyHom_involutive,
      Function.RightInverse.surjective e7SerreChevalleyHom_involutive⟩

@[simp] theorem e7SerreChevalleyInv_H (i : Fin 7) :
    e7SerreChevalleyInv (e7SerreH i) = -e7SerreH i :=
  e7SerreChevalleyHom_H i

@[simp] theorem e7SerreChevalleyInv_E (i : Fin 7) :
    e7SerreChevalleyInv (e7SerreE i) = e7SerreF i :=
  e7SerreChevalleyHom_E i

@[simp] theorem e7SerreChevalleyInv_F (i : Fin 7) :
    e7SerreChevalleyInv (e7SerreF i) = e7SerreE i :=
  e7SerreChevalleyHom_F i

@[simp] theorem e7SerreChevalleyInv_involutive (x : LieAlgebra.e₇ ℝ) :
    e7SerreChevalleyInv (e7SerreChevalleyInv x) = x :=
  e7SerreChevalleyHom_involutive x

/-! #### 63 positive root vectors in `LieAlgebra.e₇ ℝ` -/

private def e7SimplePosIdx (i : Fin 7) : Fin 63 :=
  ⟨i.val, by omega⟩

private def e7SimpleOfPos (p : Fin 63) : Fin 7 :=
  if h : p.val < 7 then ⟨p.val, h⟩ else 0

def e7PosHeight (p : Fin 63) : ℕ :=
  match p.val with
  | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1
  | 7 => 2 | 8 => 2 | 9 => 2 | 10 => 2 | 11 => 2 | 12 => 2 | 13 => 3
  | 14 => 3 | 15 => 3 | 16 => 3 | 17 => 3 | 18 => 3 | 19 => 4 | 20 => 4
  | 21 => 4 | 22 => 4 | 23 => 4 | 24 => 4 | 25 => 5 | 26 => 5 | 27 => 5
  | 28 => 5 | 29 => 5 | 30 => 5 | 31 => 6 | 32 => 6 | 33 => 6 | 34 => 6
  | 35 => 6 | 36 => 7 | 37 => 7 | 38 => 7 | 39 => 7 | 40 => 7 | 41 => 8
  | 42 => 8 | 43 => 8 | 44 => 8 | 45 => 9 | 46 => 9 | 47 => 9 | 48 => 9
  | 49 => 10 | 50 => 10 | 51 => 10 | 52 => 11 | 53 => 11 | 54 => 11 | 55 => 12
  | 56 => 12 | 57 => 13 | 58 => 13 | 59 => 14 | 60 => 15 | 61 => 16 | 62 => 17
  | _ => 1

def e7PosParent (p : Fin 63) : Option (Fin 7 × Fin 63) :=
  match p.val with
  | 7 => some (5, 6) | 8 => some (4, 5) | 9 => some (3, 4) | 10 => some (2, 3)
  | 11 => some (1, 3) | 12 => some (0, 2) | 13 => some (4, 7) | 14 => some (3, 8)
  | 15 => some (2, 9) | 16 => some (1, 9) | 17 => some (1, 10) | 18 => some (0, 10)
  | 19 => some (3, 13) | 20 => some (2, 14) | 21 => some (1, 14) | 22 => some (1, 15)
  | 23 => some (0, 15) | 24 => some (0, 17) | 25 => some (2, 19) | 26 => some (1, 19)
  | 27 => some (1, 20) | 28 => some (3, 22) | 29 => some (0, 20) | 30 => some (0, 22)
  | 31 => some (1, 25) | 32 => some (3, 27) | 33 => some (0, 25) | 34 => some (0, 27)
  | 35 => some (0, 28) | 36 => some (3, 31) | 37 => some (4, 32) | 38 => some (0, 31)
  | 39 => some (0, 32) | 40 => some (2, 35) | 41 => some (4, 36) | 42 => some (0, 36)
  | 43 => some (0, 37) | 44 => some (2, 39) | 45 => some (5, 41) | 46 => some (0, 41)
  | 47 => some (2, 42) | 48 => some (2, 43) | 49 => some (0, 45) | 50 => some (2, 46)
  | 51 => some (3, 48) | 52 => some (2, 49) | 53 => some (3, 50) | 54 => some (1, 51)
  | 55 => some (3, 52) | 56 => some (1, 53) | 57 => some (4, 55) | 58 => some (1, 55)
  | 59 => some (1, 57) | 60 => some (3, 59) | 61 => some (2, 60) | 62 => some (0, 61)
  | _ => none

private theorem e7PosParent_lt_bool :
    (List.finRange 63).all (fun p => match e7PosParent p with
      | some (_, p₀) => decide (p₀.val < p.val)
      | none => true) = true := by
  decide

private theorem e7PosParent_lt {p : Fin 63} {k : Fin 7} {p₀ : Fin 63}
    (hp : e7PosParent p = some (k, p₀)) : p₀.val < p.val := by
  have h := e7PosParent_lt_bool
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have hp' := h p
  rw [hp] at hp'
  exact of_decide_eq_true hp'

/-- The 63 positive root vectors inside `LieAlgebra.e₇ ℝ`, built inductively
by height from the seven simple positive generators `e7SerreE i`. -/
noncomputable def e7SerrePosVec (p : Fin 63) : LieAlgebra.e₇ ℝ :=
  match hp : e7PosParent p with
  | none => e7SerreE (e7SimpleOfPos p)
  | some (k, p₀) =>
      have _ : p₀.val < p.val := e7PosParent_lt hp
      ⁅e7SerreE k, e7SerrePosVec p₀⁆
termination_by p.val

private theorem e7_ht_le_one_simple {p : Fin 63} (hp : e7PosParent p = none) :
    e7SerrePosVec p = e7SerreE (e7SimpleOfPos p) := by
  rw [e7SerrePosVec]
  split
  · rfl
  · next h => exact absurd (hp.symm.trans h) (by simp)

private theorem e7SerrePosVec_simple (i : Fin 7) :
    e7SerrePosVec (e7SimplePosIdx i) = e7SerreE i := by
  fin_cases i <;>
    · rw [e7_ht_le_one_simple rfl]
      rfl

private theorem e7SerrePosVec_parent {p : Fin 63} {k : Fin 7} {p₀ : Fin 63}
    (hp : e7PosParent p = some (k, p₀)) :
    e7SerrePosVec p = ⁅e7SerreE k, e7SerrePosVec p₀⁆ := by
  rw [e7SerrePosVec]
  split
  · next h => exact absurd (hp.symm.trans h) (by simp)
  · next k' p₀' h =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hp.symm.trans h))
      rfl

private def e7Cartan (i j : Fin 7) : ℤ :=
  if i = j then 2
  else if (i.val = 0 ∧ j.val = 2) ∨ (j.val = 0 ∧ i.val = 2) ∨
      (i.val = 1 ∧ j.val = 3) ∨ (j.val = 1 ∧ i.val = 3) ∨
      (2 ≤ i.val ∧ i.val + 1 = j.val) ∨ (2 ≤ j.val ∧ j.val + 1 = i.val)
    then -1 else 0

private lemma e7Cartan_eq (i j : Fin 7) : Tag.cartan .E7 i j = e7Cartan i j := by
  have hchk : (List.finRange 7).all (fun a => (List.finRange 7).all (fun b =>
      Tag.cartan .E7 a b == e7Cartan a b)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
  exact hchk i j

/-- Next positive root entry `(positiveSign, target)` for `⁅e7SerreE i, e7SerrePosVec p⁆`. -/
def e7PosUp (i : Fin 7) (p : Fin 63) : Option (Bool × Fin 63) :=
  match i.val, p.val with
  | 0, 2 => some (true, 12) | 0, 10 => some (true, 18) | 0, 15 => some (true, 23) | 0, 17 => some (true, 24)
  | 0, 20 => some (true, 29) | 0, 22 => some (true, 30) | 0, 25 => some (true, 33) | 0, 27 => some (true, 34)
  | 0, 28 => some (true, 35) | 0, 31 => some (true, 38) | 0, 32 => some (true, 39) | 0, 36 => some (true, 42)
  | 0, 37 => some (true, 43) | 0, 41 => some (true, 46) | 0, 45 => some (true, 49) | 0, 61 => some (true, 62)
  | 1, 3 => some (true, 11) | 1, 9 => some (true, 16) | 1, 10 => some (true, 17) | 1, 14 => some (true, 21)
  | 1, 15 => some (true, 22) | 1, 18 => some (true, 24) | 1, 19 => some (true, 26) | 1, 20 => some (true, 27)
  | 1, 23 => some (true, 30) | 1, 25 => some (true, 31) | 1, 29 => some (true, 34) | 1, 33 => some (true, 38)
  | 1, 51 => some (true, 54) | 1, 53 => some (true, 56) | 1, 55 => some (true, 58) | 1, 57 => some (true, 59)
  | 2, 0 => some (false, 12) | 2, 3 => some (true, 10) | 2, 9 => some (true, 15) | 2, 11 => some (true, 17)
  | 2, 14 => some (true, 20) | 2, 16 => some (true, 22) | 2, 19 => some (true, 25) | 2, 21 => some (true, 27)
  | 2, 26 => some (true, 31) | 2, 35 => some (true, 40) | 2, 39 => some (true, 44) | 2, 42 => some (true, 47)
  | 2, 43 => some (true, 48) | 2, 46 => some (true, 50) | 2, 49 => some (true, 52) | 2, 60 => some (true, 61)
  | 3, 1 => some (false, 11) | 3, 2 => some (false, 10) | 3, 4 => some (true, 9) | 3, 8 => some (true, 14)
  | 3, 12 => some (false, 18) | 3, 13 => some (true, 19) | 3, 22 => some (true, 28) | 3, 27 => some (true, 32)
  | 3, 30 => some (true, 35) | 3, 31 => some (true, 36) | 3, 34 => some (true, 39) | 3, 38 => some (true, 42)
  | 3, 48 => some (true, 51) | 3, 50 => some (true, 53) | 3, 52 => some (true, 55) | 3, 59 => some (true, 60)
  | 4, 3 => some (false, 9) | 4, 5 => some (true, 8) | 4, 7 => some (true, 13) | 4, 10 => some (false, 15)
  | 4, 11 => some (false, 16) | 4, 17 => some (false, 22) | 4, 18 => some (false, 23) | 4, 24 => some (false, 30)
  | 4, 32 => some (true, 37) | 4, 36 => some (true, 41) | 4, 39 => some (true, 43) | 4, 42 => some (true, 46)
  | 4, 44 => some (true, 48) | 4, 47 => some (true, 50) | 4, 55 => some (true, 57) | 4, 58 => some (true, 59)
  | 5, 4 => some (false, 8) | 5, 6 => some (true, 7) | 5, 9 => some (false, 14) | 5, 15 => some (false, 20)
  | 5, 16 => some (false, 21) | 5, 22 => some (false, 27) | 5, 23 => some (false, 29) | 5, 28 => some (false, 32)
  | 5, 30 => some (false, 34) | 5, 35 => some (false, 39) | 5, 40 => some (false, 44) | 5, 41 => some (true, 45)
  | 5, 46 => some (true, 49) | 5, 50 => some (true, 52) | 5, 53 => some (true, 55) | 5, 56 => some (true, 58)
  | 6, 5 => some (false, 7) | 6, 8 => some (false, 13) | 6, 14 => some (false, 19) | 6, 20 => some (false, 25)
  | 6, 21 => some (false, 26) | 6, 27 => some (false, 31) | 6, 29 => some (false, 33) | 6, 32 => some (false, 36)
  | 6, 34 => some (false, 38) | 6, 37 => some (false, 41) | 6, 39 => some (false, 42) | 6, 43 => some (false, 46)
  | 6, 44 => some (false, 47) | 6, 48 => some (false, 50) | 6, 51 => some (false, 53) | 6, 54 => some (false, 56)
  | _, _ => none

private def e7IsSelfParent (i : Fin 7) (p : Fin 63) : Bool :=
  match e7PosUp i p with
  | some (true, q) => e7PosParent q == some (i, p)
  | _ => false

noncomputable def e7EvalPosUp : Option (Bool × Fin 63) → LieAlgebra.e₇ ℝ
  | none => 0
  | some (true, q) => e7SerrePosVec q
  | some (false, q) => -e7SerrePosVec q

private def e7AdjRemWitness (i : Fin 7) (p : Fin 63) : Option (Bool × Fin 63) :=
  match i.val, p.val with
  | 2, 28 => some (true, 16)  | 2, 32 => some (true, 21)  | 2, 36 => some (true, 26)
  | 3, 17 => some (false, 2)  | 3, 40 => some (true, 30)  | 3, 44 => some (true, 34)
  | 3, 47 => some (true, 38)  | 4, 28 => some (false, 17) | 4, 51 => some (true, 44)
  | 4, 53 => some (true, 47)  | 4, 60 => some (true, 58)  | 5, 37 => some (false, 28)
  | 5, 57 => some (true, 53)  | 6, 45 => some (false, 37) | _, _ => none

private lemma e7_two_smul_bracket_eq_ad_sq {x z y : LieAlgebra.e₇ ℝ}
    (hxz : ⁅x, ⁅x, z⁆⁆ = 0) (hxy : ⁅x, ⁅x, y⁆⁆ = 0) :
    (2 : ℝ) • ⁅x, ⁅z, ⁅x, y⁆⁆⁆ = ⁅x, ⁅x, ⁅z, y⁆⁆⁆ := by
  have h1 : ⁅x, ⁅x, ⁅z, y⁆⁆⁆ =
      ⁅x, ⁅⁅x, z⁆, y⁆⁆ + ⁅x, ⁅z, ⁅x, y⁆⁆⁆ := by
    rw [leibniz_lie x z y, lie_add]
  have h2 : ⁅x, ⁅⁅x, z⁆, y⁆⁆ = ⁅⁅x, z⁆, ⁅x, y⁆⁆ := by
    rw [leibniz_lie x ⁅x, z⁆ y, hxz, zero_lie, zero_add]
  have h3 : ⁅⁅x, z⁆, ⁅x, y⁆⁆ = ⁅x, ⁅z, ⁅x, y⁆⁆⁆ := by
    rw [lie_lie x z ⁅x, y⁆, hxy, lie_zero, sub_zero]
  rw [h1, h2, h3, two_smul]

private lemma e7PosParent_ht_lt_bool :
    (List.finRange 63).all (fun p => match e7PosParent p with
      | some (_, p₀) => decide (e7PosHeight p₀ < e7PosHeight p)
      | none => true) = true := by
  decide

private lemma e7PosParent_ht_lt {p : Fin 63} {k : Fin 7} {p₀ : Fin 63}
    (hp : e7PosParent p = some (k, p₀)) : e7PosHeight p₀ < e7PosHeight p := by
  have h := e7PosParent_ht_lt_bool
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have hp' := h p
  rw [hp] at hp'
  exact of_decide_eq_true hp'

private lemma e7PosParent_ht_succ_bool :
    (List.finRange 63).all (fun p => match e7PosParent p with
      | some (_, p₀) => decide (e7PosHeight p = e7PosHeight p₀ + 1)
      | none => true) = true := by
  decide

private lemma e7PosParent_ht_succ {p : Fin 63} {k : Fin 7} {p₀ : Fin 63}
    (hp : e7PosParent p = some (k, p₀)) : e7PosHeight p = e7PosHeight p₀ + 1 := by
  have h := e7PosParent_ht_succ_bool
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have hp' := h p
  rw [hp] at hp'
  exact of_decide_eq_true hp'

private lemma e7PosUp_ht_le_bool :
    (List.finRange 7).all (fun i => (List.finRange 63).all (fun p => match e7PosUp i p with
      | some (_, q) => decide (e7PosHeight q ≤ e7PosHeight p + 1)
      | none => true)) = true := by
  decide

private lemma e7PosUp_ht_le {i : Fin 7} {p : Fin 63} {s : Bool} {q : Fin 63}
    (hu : e7PosUp i p = some (s, q)) : e7PosHeight q ≤ e7PosHeight p + 1 := by
  have h := e7PosUp_ht_le_bool
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have hp' := h i p
  rw [hu] at hp'
  exact of_decide_eq_true hp'

private lemma e7PosHeight_pos (p : Fin 63) : 1 ≤ e7PosHeight p := by
  have h : (List.finRange 63).all (fun x => decide (1 ≤ e7PosHeight x)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at h
  exact h p

private lemma e7PosHeight_le_17 (p : Fin 63) : e7PosHeight p ≤ 17 := by
  have h : (List.finRange 63).all (fun x => decide (e7PosHeight x ≤ 17)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at h
  exact h p

private lemma e7_adSq_mid_up_none_bool :
    (List.finRange 63).all (fun p => match e7PosParent p with
      | some (k, p₀) => match e7PosParent p₀ with
        | some (m, p₁) =>
            if decide (e7Cartan k m ≠ 0 ∧ k ≠ m) then e7PosUp k p₁ == none else true
        | none => true
      | none => true) = true := by
  decide

private lemma e7_adSq_mid_up_none {p : Fin 63} {k : Fin 7} {p₀ : Fin 63}
    {m : Fin 7} {p₁ : Fin 63}
    (hp : e7PosParent p = some (k, p₀)) (hp₀ : e7PosParent p₀ = some (m, p₁))
    (hkm : e7Cartan k m ≠ 0) (hkmeq : k ≠ m) :
    e7PosUp k p₁ = none := by
  have h := e7_adSq_mid_up_none_bool
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have hp' := h p
  rw [hp] at hp'
  dsimp only at hp'
  rw [hp₀] at hp'
  simpa [hkm, hkmeq] using hp'

private lemma e7_adSq_end_up_none_bool :
    (List.finRange 63).all (fun p => match e7PosParent p with
      | some (k, p₀) => match e7PosParent p₀ with
        | some (_, p₁) => match e7PosUp k p₁ with
          | some (_, q) => e7PosUp k q == none
          | none => true
        | none => true
      | none => true) = true := by
  decide

private lemma e7_adSq_end_up_none {p : Fin 63} {k : Fin 7} {p₀ : Fin 63}
    {m : Fin 7} {p₁ : Fin 63} {s : Bool} {q : Fin 63}
    (hp : e7PosParent p = some (k, p₀)) (hp₀ : e7PosParent p₀ = some (m, p₁))
    (hup : e7PosUp k p₁ = some (s, q)) :
    e7PosUp k q = none := by
  have h := e7_adSq_end_up_none_bool
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have hp' := h p
  rw [hp] at hp'
  dsimp only at hp'
  rw [hp₀] at hp'
  dsimp only at hp'
  rw [hup] at hp'
  exact eq_of_beq hp'

private lemma e7_diag_up_none_bool :
    (List.finRange 63).all (fun p => match e7PosParent p with
      | some (k, _) => e7PosUp k p == none
      | none => true) = true := by
  decide

private lemma e7_diag_up_none {p : Fin 63} {k : Fin 7} {p₀ : Fin 63}
    (hp : e7PosParent p = some (k, p₀)) : e7PosUp k p = none := by
  have h := e7_diag_up_none_bool
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have hp' := h p
  rw [hp] at hp'
  exact eq_of_beq hp'

private lemma e7_comm_up_none_bool :
    (List.finRange 7).all (fun i => (List.finRange 63).all (fun p =>
      match e7PosParent p with
      | some (k, p₀) =>
          if decide (i ≠ k ∧ e7Cartan i k = 0) && (e7PosUp i p₀ == none)
          then e7PosUp i p == none else true
      | none => true)) = true := by
  decide

private lemma e7_comm_up_none {p : Fin 63} {i k : Fin 7} {p₀ : Fin 63}
    (hp : e7PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : e7Cartan i k = 0) (hup0 : e7PosUp i p₀ = none) :
    e7PosUp i p = none := by
  have h := e7_comm_up_none_bool
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have hp' := h i p
  rw [hp] at hp'
  simpa [hik, hcart, hup0] using hp'

private lemma e7_comm_up_self_parent_bool :
    (List.finRange 7).all (fun i => (List.finRange 63).all (fun p =>
      match e7PosParent p with
      | some (k, p₀) =>
          if decide (i ≠ k ∧ e7Cartan i k = 0) && e7IsSelfParent i p then
            match e7PosUp i p₀ with
            | some (s₀, _) => s₀ == true
            | none => true
          else true
      | none => true)) = true := by
  decide

private lemma e7_comm_up_self_parent {p : Fin 63} {i k : Fin 7} {p₀ q₁ : Fin 63}
    {s₀ : Bool}
    (hp : e7PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : e7Cartan i k = 0) (hup0 : e7PosUp i p₀ = some (s₀, q₁))
    (hself : e7IsSelfParent i p = true) :
    s₀ = true := by
  have h := e7_comm_up_self_parent_bool
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have hp' := h i p
  rw [hp] at hp'
  simpa [hik, hcart, hself, hup0] using hp'

private lemma e7_comm_up_other_parent_bool :
    (List.finRange 7).all (fun i => (List.finRange 63).all (fun p =>
      match e7PosParent p with
      | some (k, p₀) =>
          if decide (i ≠ k ∧ e7Cartan i k = 0) && !(e7IsSelfParent i p) then
            match e7PosUp i p₀ with
            | some (s₀, q₁) => match e7PosUp i p with
              | some (s, q) => (s == s₀) && (e7PosParent q == some (k, q₁))
              | none => false
            | none => true
          else true
      | none => true)) = true := by
  decide

private lemma e7_comm_up_other_parent {p : Fin 63} {i k : Fin 7} {p₀ q₁ : Fin 63}
    {s₀ : Bool}
    (hp : e7PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : e7Cartan i k = 0) (hup0 : e7PosUp i p₀ = some (s₀, q₁))
    (hnot : e7IsSelfParent i p = false) :
    ∃ q, e7PosUp i p = some (s₀, q) ∧ e7PosParent q = some (k, q₁) := by
  have h := e7_comm_up_other_parent_bool
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have hp' := h i p
  rw [hp] at hp'
  dsimp only at hp'
  rw [decide_eq_true ⟨hik, hcart⟩, hnot] at hp'
  simp only [Bool.true_and, Bool.not_false, ↓reduceIte] at hp'
  rw [hup0] at hp'
  dsimp only at hp'
  cases hup : e7PosUp i p with
  | none => rw [hup] at hp'; dsimp only at hp'; contradiction
  | some sq =>
      rcases sq with ⟨s, q⟩
      rw [hup] at hp'
      simp only [Bool.and_eq_true, beq_iff_eq] at hp'
      exact ⟨q, by rw [hp'.1], hp'.2⟩

private lemma e7_cartan_symm_zero {i k : Fin 7}
    (h : e7Cartan i k = 0) : e7Cartan k i = 0 := by
  have hbool : (List.finRange 7).all (fun a => (List.finRange 7).all (fun b =>
      if e7Cartan a b == 0 then e7Cartan b a == 0 else true)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hbool
  have ha := hbool i k
  simpa [h] using ha

private lemma e7_adj_up_none_bool :
    (List.finRange 7).all (fun i => (List.finRange 63).all (fun p =>
      match e7PosParent p with
      | some (k, _) =>
          if decide (i ≠ k ∧ e7Cartan i k ≠ 0) && !(e7IsSelfParent i p)
          then e7PosUp i p == none else true
      | none => true)) = true := by
  decide

private lemma e7_adj_up_none {p : Fin 63} {i k : Fin 7} {p₀ : Fin 63}
    (hp : e7PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : e7Cartan i k ≠ 0) (hnot : e7IsSelfParent i p = false) :
    e7PosUp i p = none := by
  have h := e7_adj_up_none_bool
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have hp' := h i p
  rw [hp] at hp'
  simpa [hik, hcart, hnot] using hp'

private lemma e7_adj_ht2_simple_bool :
    (List.finRange 7).all (fun i => (List.finRange 63).all (fun p =>
      match e7PosParent p with
      | some (k, p₀) =>
          if decide (i ≠ k ∧ e7Cartan i k ≠ 0) && !(e7IsSelfParent i p) then
            match e7PosParent p₀ with
            | none => e7SimpleOfPos p₀ == i
            | some _ => true
          else true
      | none => true)) = true := by
  decide

private lemma e7_adj_ht2_simple {p : Fin 63} {i k : Fin 7} {p₀ : Fin 63}
    (hp : e7PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : e7Cartan i k ≠ 0) (hnot : e7IsSelfParent i p = false)
    (hp₀ : e7PosParent p₀ = none) :
    e7SimpleOfPos p₀ = i := by
  have h := e7_adj_ht2_simple_bool
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have hp' := h i p
  rw [hp] at hp'
  dsimp only at hp'
  rw [decide_eq_true ⟨hik, hcart⟩, hnot] at hp'
  rw [hp₀] at hp'
  exact eq_of_beq hp'

private lemma e7_adj_mi_up_none_bool :
    (List.finRange 7).all (fun m => (List.finRange 63).all (fun p =>
      match e7PosParent p with
      | some (k, p₀) =>
          if decide (m ≠ k ∧ e7Cartan m k ≠ 0) && !(e7IsSelfParent m p) then
            match e7PosParent p₀ with
            | some (m', p₁) =>
                if m' == m then (e7PosUp k p₁ == none) && (e7PosUp m p₀ == none) else true
            | none => true
          else true
      | none => true)) = true := by
  decide

private lemma e7_adj_mi_up_none {p : Fin 63} {m k : Fin 7} {p₀ p₁ : Fin 63}
    (hp : e7PosParent p = some (k, p₀)) (hmk : m ≠ k)
    (hcart : e7Cartan m k ≠ 0) (hnot : e7IsSelfParent m p = false)
    (hp₀ : e7PosParent p₀ = some (m, p₁)) :
    e7PosUp k p₁ = none ∧ e7PosUp m p₀ = none := by
  have h := e7_adj_mi_up_none_bool
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have hp' := h m p
  rw [hp] at hp'
  dsimp only at hp'
  rw [decide_eq_true ⟨hmk, hcart⟩, hnot] at hp'
  rw [hp₀] at hp'
  simpa using hp'

private lemma e7_adj_comm_m_witness_bool :
    (List.finRange 7).all (fun i => (List.finRange 63).all (fun p =>
      match e7PosParent p with
      | some (k, p₀) =>
          if decide (i ≠ k ∧ e7Cartan i k ≠ 0) && !(e7IsSelfParent i p) then
            match e7PosParent p₀ with
            | some (m, p₁) =>
                if decide (m ≠ i ∧ e7Cartan k m = 0 ∧ e7Cartan i m = 0) then
                  match e7PosUp k p₁ with
                  | some (_, q) => e7PosUp i q == none
                  | none => false
                else true
            | none => true
          else true
      | none => true)) = true := by
  decide

private lemma e7_adj_comm_m_witness {p : Fin 63} {i k m : Fin 7} {p₀ p₁ : Fin 63}
    (hp : e7PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : e7Cartan i k ≠ 0) (hnot : e7IsSelfParent i p = false)
    (hp₀ : e7PosParent p₀ = some (m, p₁)) (hmi : m ≠ i)
    (hcomm : e7Cartan k m = 0 ∧ e7Cartan i m = 0) :
    ∃ s q, e7PosUp k p₁ = some (s, q) ∧ e7PosUp i q = none := by
  have h := e7_adj_comm_m_witness_bool
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have hp' := h i p
  rw [hp] at hp'
  dsimp only at hp'
  rw [decide_eq_true ⟨hik, hcart⟩, hnot] at hp'
  simp only [Bool.true_and, Bool.not_false, ↓reduceIte] at hp'
  rw [hp₀] at hp'
  dsimp only at hp'
  rw [decide_eq_true ⟨hmi, hcomm⟩] at hp'
  simp only [↓reduceIte] at hp'
  cases hupk : e7PosUp k p₁ with
  | none => rw [hupk] at hp'; dsimp only at hp'; contradiction
  | some sq =>
      rcases sq with ⟨s, q⟩
      rw [hupk] at hp'
      dsimp only at hp'
      exact ⟨s, q, rfl, eq_of_beq hp'⟩

private lemma e7_adj_rem_witness_bool :
    (List.finRange 7).all (fun i => (List.finRange 63).all (fun p =>
      match e7PosParent p with
      | some (k, p₀) =>
          if decide (i ≠ k ∧ e7Cartan i k ≠ 0) && !(e7IsSelfParent i p) then
            match e7PosParent p₀ with
            | some (m, _) =>
                if decide (m ≠ i ∧ ¬(e7Cartan k m = 0 ∧ e7Cartan i m = 0)) then
                  match e7AdjRemWitness i p with
                  | some (s₂, q₂) =>
                      decide (e7PosHeight q₂ + 1 = e7PosHeight p₀) &&
                        (e7PosUp i q₂ == some (s₂, p₀)) &&
                        (e7PosUp i p₀ == none) &&
                        (e7PosUp k q₂ == none)
                  | none => false
                else true
            | none => true
          else true
      | none => true)) = true := by
  decide

private lemma e7_adj_rem_witness {p : Fin 63} {i k m : Fin 7} {p₀ p₁ : Fin 63}
    (hp : e7PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : e7Cartan i k ≠ 0) (hnot : e7IsSelfParent i p = false)
    (hp₀ : e7PosParent p₀ = some (m, p₁)) (hmi : m ≠ i)
    (hnc : ¬(e7Cartan k m = 0 ∧ e7Cartan i m = 0)) :
    ∃ s₂ q₂, e7PosHeight q₂ + 1 = e7PosHeight p₀ ∧
      e7PosUp i q₂ = some (s₂, p₀) ∧ e7PosUp i p₀ = none ∧ e7PosUp k q₂ = none := by
  have h := e7_adj_rem_witness_bool
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have hp' := h i p
  rw [hp] at hp'
  dsimp only at hp'
  rw [decide_eq_true ⟨hik, hcart⟩, hnot] at hp'
  simp only [Bool.true_and, Bool.not_false, ↓reduceIte] at hp'
  rw [hp₀] at hp'
  dsimp only at hp'
  rw [decide_eq_true (p := m ≠ i ∧ ¬(e7Cartan k m = 0 ∧ e7Cartan i m = 0)) ⟨hmi, hnc⟩] at hp'
  simp only [↓reduceIte] at hp'
  cases hw : e7AdjRemWitness i p with
  | none => rw [hw] at hp'; dsimp only at hp'; contradiction
  | some sq =>
      rcases sq with ⟨s₂, q₂⟩
      rw [hw] at hp'
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp'
      exact ⟨s₂, q₂, hp'.1.1.1, hp'.1.1.2, hp'.1.2, hp'.2⟩

private lemma e7_pos_base_ht1_simple (i j : Fin 7) :
    ⁅e7SerreE i, e7SerrePosVec (e7SimplePosIdx j)⁆ =
      e7EvalPosUp (e7PosUp i (e7SimplePosIdx j)) := by
  by_cases hij : i = j
  · subst hij
    have hdiag : (List.finRange 7).all
        (fun a => e7PosUp a (e7SimplePosIdx a) == none) = true := by
      decide
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hdiag
    rw [e7SerrePosVec_simple, hdiag i, e7EvalPosUp, lie_self]
  · by_cases h0 : e7Cartan i j = 0
    · have hzero : e7PosUp i (e7SimplePosIdx j) = none := by
        have hb : (List.finRange 7).all (fun a => (List.finRange 7).all (fun b =>
            if decide (e7Cartan a b = 0) then e7PosUp a (e7SimplePosIdx b) == none else true)) =
            true := by
          decide
        simp only [List.all_eq_true, List.mem_finRange, true_implies] at hb
        have h' := hb i j
        simpa [h0] using h'
      rw [e7SerrePosVec_simple, hzero, e7EvalPosUp]
      exact e7Serre_adE_zero (by rw [e7Cartan_eq]; exact h0)
    · have htrich : (List.finRange 7).all (fun a => (List.finRange 7).all (fun b =>
          if decide (a ≠ b ∧ e7Cartan a b ≠ 0) then
            (match e7PosUp a (e7SimplePosIdx b) with
              | some (true, q) => e7PosParent q == some (a, e7SimplePosIdx b)
              | some (false, q) => e7PosParent q == some (b, e7SimplePosIdx a)
              | none => false) else true)) = true := by
        decide
      simp only [List.all_eq_true, List.mem_finRange, true_implies] at htrich
      have ht := htrich i j
      rw [decide_eq_true ⟨hij, h0⟩] at ht
      simp only [↓reduceIte] at ht
      cases hup : e7PosUp i (e7SimplePosIdx j) with
      | none => rw [hup] at ht; contradiction
      | some sq =>
          rcases sq with ⟨s, q⟩
          cases s
          · rw [hup] at ht
            rw [e7SerrePosVec_simple j, ← lie_skew, ← e7SerrePosVec_simple i]
            dsimp only [e7EvalPosUp]
            exact congrArg Neg.neg (e7SerrePosVec_parent (eq_of_beq ht)).symm
          · rw [hup] at ht
            dsimp only [e7EvalPosUp]
            exact (e7SerrePosVec_parent (eq_of_beq ht)).symm

private lemma e7_pos_base_ht1 (i : Fin 7) (p : Fin 63) (hp : e7PosParent p = none) :
    ⁅e7SerreE i, e7SerrePosVec p⁆ = e7EvalPosUp (e7PosUp i p) := by
  have hbool : (List.finRange 63).all (fun x => match e7PosParent x with
      | none => x == e7SimplePosIdx (e7SimpleOfPos x)
      | some _ => true) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hbool
  have hsp : p = e7SimplePosIdx (e7SimpleOfPos p) := by
    have h := hbool p
    rw [hp] at h
    exact eq_of_beq h
  conv_lhs => rw [hsp]
  conv_rhs => rw [hsp]
  exact e7_pos_base_ht1_simple i (e7SimpleOfPos p)

private lemma e7_ad_sq_posVec_eq_zero (n : ℕ)
    (ih : ∀ q : Fin 63, e7PosHeight q ≤ n → ∀ j : Fin 7,
      ⁅e7SerreE j, e7SerrePosVec q⁆ = e7EvalPosUp (e7PosUp j q))
    (p : Fin 63) (hn : e7PosHeight p ≤ n + 1) (k : Fin 7) (p₀ : Fin 63)
    (hp : e7PosParent p = some (k, p₀)) :
    ⁅e7SerreE k, e7SerrePosVec p⁆ = 0 := by
  rw [e7SerrePosVec_parent hp]
  have hlt0 : e7PosHeight p₀ ≤ n :=
    Nat.le_of_lt_succ (lt_of_lt_of_le (e7PosParent_ht_lt hp) hn)
  cases hp₀ : e7PosParent p₀ with
  | none =>
      rw [e7_ht_le_one_simple hp₀]
      exact e7Serre_adE_sq_gen k (e7SimpleOfPos p₀)
  | some kp1 =>
      rcases kp1 with ⟨m, p₁⟩
      have hlt1 : e7PosHeight p₁ < e7PosHeight p₀ := e7PosParent_ht_lt hp₀
      have hlt1n : e7PosHeight p₁ ≤ n := by omega
      rw [e7SerrePosVec_parent hp₀]
      have had : ⁅e7SerreE k, ⁅e7SerreE k, ⁅e7SerreE m, e7SerrePosVec p₁⁆⁆⁆ =
          ⁅⁅e7SerreE k, ⁅e7SerreE k, e7SerreE m⁆⁆, e7SerrePosVec p₁⁆ +
          (2 : ℝ) • ⁅⁅e7SerreE k, e7SerreE m⁆, ⁅e7SerreE k, e7SerrePosVec p₁⁆⁆ +
          ⁅e7SerreE m, ⁅e7SerreE k, ⁅e7SerreE k, e7SerrePosVec p₁⁆⁆⁆ := by
        rw [leibniz_lie (e7SerreE k) (e7SerreE m) (e7SerrePosVec p₁), lie_add]
        rw [leibniz_lie (e7SerreE k) ⁅e7SerreE k, e7SerreE m⁆ (e7SerrePosVec p₁)]
        rw [leibniz_lie (e7SerreE k) (e7SerreE m) ⁅e7SerreE k, e7SerrePosVec p₁⁆]
        rw [two_smul]
        abel
      rw [had, e7Serre_adE_sq_gen k m, zero_lie, zero_add]
      have hmid : ⁅⁅e7SerreE k, e7SerreE m⁆, ⁅e7SerreE k, e7SerrePosVec p₁⁆⁆ = 0 := by
        by_cases hkm : e7Cartan k m = 0
        · rw [e7Serre_adE_zero (by rw [e7Cartan_eq]; exact hkm), zero_lie]
        · by_cases hkm_eq : k = m
          · subst hkm_eq; simp [lie_self]
          · have hup := e7_adSq_mid_up_none hp hp₀ hkm hkm_eq
            rw [ih p₁ hlt1n k, hup, e7EvalPosUp, lie_zero]
      have hend : ⁅e7SerreE k, ⁅e7SerreE k, e7SerrePosVec p₁⁆⁆ = 0 := by
        rw [ih p₁ hlt1n k]
        cases hup : e7PosUp k p₁ with
        | none => simp [e7EvalPosUp]
        | some sq =>
            rcases sq with ⟨s, q⟩
            have hq_ht : e7PosHeight q ≤ e7PosHeight p₁ + 1 := e7PosUp_ht_le hup
            have hq_le : e7PosHeight q ≤ n := by
              have := e7PosParent_ht_succ hp₀
              omega
            have hup2 := e7_adSq_end_up_none hp hp₀ hup
            cases s <;> simp [e7EvalPosUp, ih q hq_le k, hup2]
      rw [hmid, smul_zero, zero_add, hend, lie_zero]

/-- Explicit action of `ad (e7SerreE i)` on the 63 positive root vectors `e7SerrePosVec p`. -/
theorem e7Serre_adE_posVec :
    ∀ (n : ℕ) (p : Fin 63), e7PosHeight p ≤ n → ∀ i : Fin 7,
      ⁅e7SerreE i, e7SerrePosVec p⁆ = e7EvalPosUp (e7PosUp i p) := by
  intro n
  induction n with
  | zero =>
      intro p hp
      have := e7PosHeight_pos p
      omega
  | succ n ih =>
      intro p hn i
      cases hp : e7PosParent p with
      | none => exact e7_pos_base_ht1 i p hp
      | some kp₀ =>
          rcases kp₀ with ⟨k, p₀⟩
          have hlt0 : e7PosHeight p₀ ≤ n := by
            have := e7PosParent_ht_succ hp
            omega
          by_cases hik : i = k
          · subst hik
            rw [e7_diag_up_none hp, e7EvalPosUp]
            exact e7_ad_sq_posVec_eq_zero n ih p hn i p₀ hp
          · by_cases hcart : e7Cartan i k = 0
            · rw [e7SerrePosVec_parent hp]
              rw [leibniz_lie (e7SerreE i) (e7SerreE k) (e7SerrePosVec p₀)]
              rw [e7Serre_adE_zero (by rw [e7Cartan_eq]; exact hcart), zero_lie, zero_add]
              rw [ih p₀ hlt0 i]
              cases hup0 : e7PosUp i p₀ with
              | none =>
                  rw [e7_comm_up_none hp hik hcart hup0, e7EvalPosUp, lie_zero]
              | some sq1 =>
                  rcases sq1 with ⟨s₀, q₁⟩
                  cases hself : e7IsSelfParent i p
                  · rcases e7_comm_up_other_parent hp hik hcart hup0 hself with ⟨q, hup, hparq⟩
                    rw [hup]
                    cases s₀ <;> simp [e7EvalPosUp, lie_neg, e7SerrePosVec_parent hparq]
                  · have hself' := hself
                    unfold e7IsSelfParent at hself'
                    cases hup : e7PosUp i p with
                    | none => rw [hup] at hself'; contradiction
                    | some sq =>
                        rcases sq with ⟨s, q⟩
                        rw [hup] at hself'
                        cases s
                        · contradiction
                        · have hparq : e7PosParent q = some (i, p) := by
                            simpa using hself'
                          have hs1 := e7_comm_up_self_parent hp hik hcart hup0 hself
                          subst hs1
                          rw [e7EvalPosUp, e7EvalPosUp]
                          calc ⁅e7SerreE k, e7SerrePosVec q₁⁆
                              = ⁅e7SerreE k, ⁅e7SerreE i, e7SerrePosVec p₀⁆⁆ := by
                                  have := ih p₀ hlt0 i
                                  rw [hup0, e7EvalPosUp] at this
                                  rw [this]
                            _ = ⁅e7SerreE i, ⁅e7SerreE k, e7SerrePosVec p₀⁆⁆ := by
                                  rw [leibniz_lie (e7SerreE k) (e7SerreE i) (e7SerrePosVec p₀)]
                                  rw [e7Serre_adE_zero
                                      (by rw [e7Cartan_eq]; exact e7_cartan_symm_zero hcart),
                                    zero_lie, zero_add]
                            _ = ⁅e7SerreE i, e7SerrePosVec p⁆ := by rw [e7SerrePosVec_parent hp]
                            _ = e7SerrePosVec q := (e7SerrePosVec_parent hparq).symm
            · have hcartTag : Tag.cartan .E7 i k ≠ 0 := by
                intro hzero
                apply hcart
                rw [← e7Cartan_eq]
                exact hzero
              have hcart1 : Tag.cartan .E7 i k = -1 :=
                (e7_cartan_offdiag_cases hik).resolve_left hcartTag
              cases hself : e7IsSelfParent i p
              · have hup := e7_adj_up_none hp hik hcart hself
                rw [hup, e7EvalPosUp]
                cases hp₀ : e7PosParent p₀ with
                | none =>
                    have hsi := e7_adj_ht2_simple hp hik hcart hself hp₀
                    rw [e7SerrePosVec_parent hp, e7_ht_le_one_simple hp₀, hsi]
                    rw [← lie_skew (e7SerreE k) (e7SerreE i), lie_neg,
                      e7Serre_adE_negOne hcart1, neg_zero]
                | some mp₁ =>
                    rcases mp₁ with ⟨m, p₁⟩
                    have hlt1n : e7PosHeight p₁ ≤ n := by
                      have := e7PosParent_ht_lt hp₀
                      omega
                    by_cases hmi : m = i
                    · subst hmi
                      obtain ⟨hup_kp1, hup_mp0⟩ :=
                        e7_adj_mi_up_none hp hik hcart hself hp₀
                      rw [e7SerrePosVec_parent hp, e7SerrePosVec_parent hp₀]
                      have h1 : ⁅e7SerreE m, ⁅e7SerreE m, e7SerrePosVec p₁⁆⁆ = 0 := by
                        rw [← e7SerrePosVec_parent hp₀, ih p₀ hlt0 m, hup_mp0, e7EvalPosUp]
                      have h2 : ⁅e7SerreE m, ⁅e7SerreE m, ⁅e7SerreE k, e7SerrePosVec p₁⁆⁆⁆ = 0 := by
                        rw [ih p₁ hlt1n k, hup_kp1, e7EvalPosUp, lie_zero, lie_zero]
                      have h2sm := e7_two_smul_bracket_eq_ad_sq (e7Serre_adE_negOne hcart1) h1
                      rw [h2] at h2sm
                      exact (smul_eq_zero.mp h2sm).resolve_left (by norm_num)
                    · by_cases hcomm_km : e7Cartan k m = 0 ∧ e7Cartan i m = 0
                      · rw [e7SerrePosVec_parent hp, e7SerrePosVec_parent hp₀]
                        rw [leibniz_lie (e7SerreE k) (e7SerreE m) (e7SerrePosVec p₁),
                          e7Serre_adE_zero (by rw [e7Cartan_eq]; exact hcomm_km.1),
                          zero_lie, zero_add]
                        rw [leibniz_lie (e7SerreE i) (e7SerreE m) ⁅e7SerreE k, e7SerrePosVec p₁⁆,
                          e7Serre_adE_zero (by rw [e7Cartan_eq]; exact hcomm_km.2),
                          zero_lie, zero_add]
                        obtain ⟨s, q, hupk, hupi⟩ :=
                          e7_adj_comm_m_witness hp hik hcart hself hp₀ hmi hcomm_km
                        have hq_le : e7PosHeight q ≤ n := by
                          have hq_ht := e7PosUp_ht_le hupk
                          have hp0_ht := e7PosParent_ht_succ hp₀
                          omega
                        have hres : ⁅e7SerreE i, ⁅e7SerreE k, e7SerrePosVec p₁⁆⁆ = 0 := by
                          rw [ih p₁ hlt1n k, hupk]
                          cases s <;> simp [e7EvalPosUp, lie_neg, ih q hq_le i, hupi]
                        rw [hres, lie_zero]
                      · obtain ⟨s₂, q₂, hq₂_ht, hup_iq₂, hup_ip₀, hup_kq₂⟩ :=
                          e7_adj_rem_witness hp hik hcart hself hp₀ hmi hcomm_km
                        have hq₂n : e7PosHeight q₂ ≤ n := by omega
                        have hk_q₂ : ⁅e7SerreE k, e7SerrePosVec q₂⁆ = 0 := by
                          rw [ih q₂ hq₂n k, hup_kq₂, e7EvalPosUp]
                        have hi_p₀ : ⁅e7SerreE i, e7SerrePosVec p₀⁆ = 0 := by
                          rw [ih p₀ hlt0 i, hup_ip₀, e7EvalPosUp]
                        have hi_q₂ : ⁅e7SerreE i, e7SerrePosVec q₂⁆ =
                            e7EvalPosUp (some (s₂, p₀)) := by
                          rw [ih q₂ hq₂n i, hup_iq₂]
                        have hi_sq_q₂ : ⁅e7SerreE i, ⁅e7SerreE i, e7SerrePosVec q₂⁆⁆ = 0 := by
                          rw [hi_q₂]
                          cases s₂ <;> simp [e7EvalPosUp, lie_neg, hi_p₀]
                        have h2sm :=
                          e7_two_smul_bracket_eq_ad_sq (e7Serre_adE_negOne hcart1) hi_sq_q₂
                        rw [hk_q₂, lie_zero, lie_zero, hi_q₂] at h2sm
                        rw [e7SerrePosVec_parent hp]
                        cases s₂
                        · dsimp only [e7EvalPosUp] at h2sm
                          rw [lie_neg, lie_neg] at h2sm
                          have hneg := (smul_eq_zero.mp h2sm).resolve_left (by norm_num)
                          exact neg_eq_zero.mp hneg
                        · dsimp only [e7EvalPosUp] at h2sm
                          exact (smul_eq_zero.mp h2sm).resolve_left (by norm_num)
              · unfold e7IsSelfParent at hself
                cases hup : e7PosUp i p with
                | none => rw [hup] at hself; contradiction
                | some sq =>
                    rcases sq with ⟨s, q⟩
                    rw [hup] at hself
                    cases s
                    · contradiction
                    · have hparq : e7PosParent q = some (i, p) := by simpa using hself
                      rw [e7EvalPosUp, e7SerrePosVec_parent hparq]

/-! #### 133-dimensional spanning submodule and triangular decomposition -/

def e7SerrePosSpan : Submodule ℝ (LieAlgebra.e₇ ℝ) :=
  Submodule.span ℝ (Set.range e7SerrePosVec)

def e7SerreCartan : Submodule ℝ (LieAlgebra.e₇ ℝ) :=
  Submodule.span ℝ (Set.range e7SerreH)

noncomputable def e7SerreNegVec (p : Fin 63) : LieAlgebra.e₇ ℝ :=
  e7SerreChevalleyInv (e7SerrePosVec p)

def e7SerreNegSpan : Submodule ℝ (LieAlgebra.e₇ ℝ) :=
  Submodule.span ℝ (Set.range e7SerreNegVec)

def e7SerreSpan133 : Submodule ℝ (LieAlgebra.e₇ ℝ) :=
  e7SerreNegSpan ⊔ e7SerreCartan ⊔ e7SerrePosSpan

private theorem e7SerrePosVec_mem_posSpan (p : Fin 63) :
    e7SerrePosVec p ∈ e7SerrePosSpan :=
  Submodule.subset_span ⟨p, rfl⟩

private theorem e7SerreE_mem_posSpan (i : Fin 7) :
    e7SerreE i ∈ e7SerrePosSpan := by
  rw [← e7SerrePosVec_simple i]
  exact e7SerrePosVec_mem_posSpan _

private theorem e7SerreH_mem_cartan (i : Fin 7) :
    e7SerreH i ∈ e7SerreCartan :=
  Submodule.subset_span ⟨i, rfl⟩

private theorem e7SerreF_mem_negSpan (i : Fin 7) :
    e7SerreF i ∈ e7SerreNegSpan := by
  have h : e7SerreF i = e7SerreNegVec (e7SimplePosIdx i) := by
    simp [e7SerreNegVec, e7SerrePosVec_simple]
  rw [h]
  exact Submodule.subset_span ⟨e7SimplePosIdx i, rfl⟩

private theorem e7EvalPosUp_mem_posSpan (o : Option (Bool × Fin 63)) :
    e7EvalPosUp o ∈ e7SerrePosSpan := by
  cases o with
  | none => exact e7SerrePosSpan.zero_mem
  | some bq =>
      rcases bq with ⟨b, q⟩
      cases b with
      | true => exact e7SerrePosVec_mem_posSpan q
      | false => exact e7SerrePosSpan.neg_mem (e7SerrePosVec_mem_posSpan q)

private theorem e7Serre_adE_posVec_mem (i : Fin 7) (p : Fin 63) :
    ⁅e7SerreE i, e7SerrePosVec p⁆ ∈ e7SerrePosSpan := by
  rw [e7Serre_adE_posVec 17 p (e7PosHeight_le_17 p) i]
  exact e7EvalPosUp_mem_posSpan _

private theorem e7Serre_adE_posSpan_mem (i : Fin 7) {y : LieAlgebra.e₇ ℝ}
    (hy : y ∈ e7SerrePosSpan) : ⁅e7SerreE i, y⁆ ∈ e7SerrePosSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e7SerrePosSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e7SerrePosSpan.smul_mem c ha
  | mem _ hp =>
      rcases hp with ⟨p, rfl⟩
      exact e7Serre_adE_posVec_mem i p

private theorem e7Serre_adE_cartan_mem (i : Fin 7) {y : LieAlgebra.e₇ ℝ}
    (hy : y ∈ e7SerreCartan) : ⁅e7SerreE i, y⁆ ∈ e7SerrePosSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e7SerrePosSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e7SerrePosSpan.smul_mem c ha
  | mem _ hj =>
      rcases hj with ⟨j, rfl⟩
      rw [← lie_skew (e7SerreE i) (e7SerreH j), e7Serre_bracket_HE, ← neg_smul]
      exact e7SerrePosSpan.smul_mem _ (e7SerreE_mem_posSpan i)

/-- Adjoint action of Cartan generators `e7SerreH i` preserves `e7SerrePosSpan`. -/
theorem e7Serre_adH_posVec_mem (i : Fin 7) :
    ∀ p : Fin 63, ⁅e7SerreH i, e7SerrePosVec p⁆ ∈ e7SerrePosSpan := by
  intro p
  induction hp_val : p.val using Nat.strong_induction_on generalizing p with
  | h n ih =>
      subst hp_val
      cases hp : e7PosParent p with
      | none =>
          rw [e7_ht_le_one_simple hp, e7Serre_bracket_HE]
          exact e7SerrePosSpan.smul_mem _ (e7SerreE_mem_posSpan _)
      | some kp₀ =>
          rcases kp₀ with ⟨k, p₀⟩
          have hlt : p₀.val < p.val := e7PosParent_lt hp
          rw [e7SerrePosVec_parent hp,
            leibniz_lie (e7SerreH i) (e7SerreE k) (e7SerrePosVec p₀),
            e7Serre_bracket_HE, smul_lie]
          refine e7SerrePosSpan.add_mem ?_ ?_
          · exact e7SerrePosSpan.smul_mem _ (e7Serre_adE_posVec_mem k p₀)
          · exact e7Serre_adE_posSpan_mem k (ih p₀.val hlt p₀ rfl)

/-- Adjoint action of negative simple generators `e7SerreF i` maps `e7SerrePosVec p`
into `e7SerrePosSpan ⊔ e7SerreCartan`. -/
theorem e7Serre_adF_posVec_mem (i : Fin 7) :
    ∀ (n : ℕ) (p : Fin 63), e7PosHeight p ≤ n →
      ⁅e7SerreF i, e7SerrePosVec p⁆ ∈ e7SerrePosSpan ⊔ e7SerreCartan := by
  intro n
  induction n with
  | zero =>
      intro p hp
      have := e7PosHeight_pos p
      omega
  | succ n ih =>
      intro p hp
      cases hpar : e7PosParent p with
      | none =>
          rw [e7_ht_le_one_simple hpar, ← lie_skew (e7SerreF i) (e7SerreE (e7SimpleOfPos p))]
          by_cases hij : e7SimpleOfPos p = i
          · rw [hij, e7Serre_bracket_EF_same]
            exact Submodule.mem_sup_right (e7SerreCartan.neg_mem (e7SerreH_mem_cartan i))
          · rw [e7Serre_bracket_EF_ne hij, neg_zero]
            exact (e7SerrePosSpan ⊔ e7SerreCartan).zero_mem
      | some kp₀ =>
          rcases kp₀ with ⟨k, p₀⟩
          have hlt : e7PosHeight p₀ ≤ n := by
            have := e7PosParent_ht_succ hpar
            omega
          rw [e7SerrePosVec_parent hpar,
            leibniz_lie (e7SerreF i) (e7SerreE k) (e7SerrePosVec p₀)]
          refine (e7SerrePosSpan ⊔ e7SerreCartan).add_mem ?_ ?_
          · rw [← lie_skew (e7SerreF i) (e7SerreE k)]
            by_cases hik : k = i
            · rw [hik, e7Serre_bracket_EF_same, neg_lie]
              exact Submodule.mem_sup_left
                (e7SerrePosSpan.neg_mem (e7Serre_adH_posVec_mem i p₀))
            · rw [e7Serre_bracket_EF_ne hik, neg_zero, zero_lie]
              exact (e7SerrePosSpan ⊔ e7SerreCartan).zero_mem
          · have hih := ih p₀ hlt
            rw [Submodule.mem_sup] at hih
            rcases hih with ⟨u, hu, v, hv, huv⟩
            rw [← huv, lie_add]
            exact Submodule.mem_sup_left
              (e7SerrePosSpan.add_mem (e7Serre_adE_posSpan_mem k hu)
                (e7Serre_adE_cartan_mem k hv))

private def e7SubmoduleLieNormalizer (S : Submodule ℝ (LieAlgebra.e₇ ℝ)) :
    LieSubalgebra ℝ (LieAlgebra.e₇ ℝ) where
  carrier := { x | ∀ y ∈ S, ⁅x, y⁆ ∈ S }
  zero_mem' y _ := by simp
  add_mem' hx hy y hyS := by rw [add_lie]; exact S.add_mem (hx y hyS) (hy y hyS)
  smul_mem' c x hx y hyS := by rw [smul_lie]; exact S.smul_mem c (hx y hyS)
  lie_mem' hx₁ hx₂ y hyS := by
    rw [lie_lie]
    exact S.sub_mem (hx₁ _ (hx₂ y hyS)) (hx₂ _ (hx₁ y hyS))

private theorem e7_chevalley_posSpan_mem_negSpan {x : LieAlgebra.e₇ ℝ}
    (hx : x ∈ e7SerrePosSpan) : e7SerreChevalleyInv x ∈ e7SerreNegSpan := by
  induction hx using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [map_add]; exact e7SerreNegSpan.add_mem ha hb
  | smul c _ _ ha => rw [map_smul]; exact e7SerreNegSpan.smul_mem c ha
  | mem _ hq =>
      rcases hq with ⟨q, rfl⟩
      exact Submodule.subset_span ⟨q, rfl⟩

private theorem e7_chevalley_mem_span133_of_pos_cartan {x : LieAlgebra.e₇ ℝ}
    (hx : x ∈ e7SerrePosSpan ⊔ e7SerreCartan) :
    e7SerreChevalleyInv x ∈ e7SerreSpan133 := by
  rw [Submodule.mem_sup] at hx
  rcases hx with ⟨u, hu, v, hv, rfl⟩
  rw [map_add]
  refine Submodule.mem_sup_left (Submodule.add_mem _ ?_ ?_)
  · exact Submodule.mem_sup_left (e7_chevalley_posSpan_mem_negSpan hu)
  · apply Submodule.mem_sup_right
    induction hv using Submodule.span_induction with
    | zero => simp
    | add _ _ _ _ ha hb => rw [map_add]; exact e7SerreCartan.add_mem ha hb
    | smul c _ _ ha => rw [map_smul]; exact e7SerreCartan.smul_mem c ha
    | mem _ hj =>
        rcases hj with ⟨j, rfl⟩
        rw [e7SerreChevalleyInv_H]
        exact e7SerreCartan.neg_mem (e7SerreH_mem_cartan j)

private theorem e7Serre_adH_negSpan_mem (i : Fin 7) {y : LieAlgebra.e₇ ℝ}
    (hy : y ∈ e7SerreNegSpan) : ⁅e7SerreH i, y⁆ ∈ e7SerreNegSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e7SerreNegSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e7SerreNegSpan.smul_mem c ha
  | mem _ hp =>
      rcases hp with ⟨p, rfl⟩
      have heq : ⁅e7SerreH i, e7SerreNegVec p⁆ =
          -e7SerreChevalleyInv ⁅e7SerreH i, e7SerrePosVec p⁆ := by
        rw [LieEquiv.map_lie, e7SerreChevalleyInv_H, neg_lie, neg_neg]
        rfl
      rw [heq]
      exact e7SerreNegSpan.neg_mem
        (e7_chevalley_posSpan_mem_negSpan (e7Serre_adH_posVec_mem i p))

private theorem e7Serre_adH_cartan_mem (i : Fin 7) {y : LieAlgebra.e₇ ℝ}
    (hy : y ∈ e7SerreCartan) : ⁅e7SerreH i, y⁆ ∈ e7SerreCartan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e7SerreCartan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e7SerreCartan.smul_mem c ha
  | mem _ hj =>
      rcases hj with ⟨j, rfl⟩
      rw [e7SerreH_comm]
      exact e7SerreCartan.zero_mem

private theorem e7Serre_adH_posSpan_mem (i : Fin 7) {y : LieAlgebra.e₇ ℝ}
    (hy : y ∈ e7SerrePosSpan) : ⁅e7SerreH i, y⁆ ∈ e7SerrePosSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e7SerrePosSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e7SerrePosSpan.smul_mem c ha
  | mem _ hp =>
      rcases hp with ⟨p, rfl⟩
      exact e7Serre_adH_posVec_mem i p

private theorem e7Serre_adE_negSpan_mem (i : Fin 7) {y : LieAlgebra.e₇ ℝ}
    (hy : y ∈ e7SerreNegSpan) : ⁅e7SerreE i, y⁆ ∈ e7SerreSpan133 := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e7SerreSpan133.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e7SerreSpan133.smul_mem c ha
  | mem _ hp =>
      rcases hp with ⟨p, rfl⟩
      have heq : ⁅e7SerreE i, e7SerreNegVec p⁆ =
          e7SerreChevalleyInv ⁅e7SerreF i, e7SerrePosVec p⁆ := by
        rw [LieEquiv.map_lie, e7SerreChevalleyInv_F]
        rfl
      rw [heq]
      exact e7_chevalley_mem_span133_of_pos_cartan
        (e7Serre_adF_posVec_mem i 17 p (e7PosHeight_le_17 p))

private theorem e7Serre_adF_negSpan_mem (i : Fin 7) {y : LieAlgebra.e₇ ℝ}
    (hy : y ∈ e7SerreNegSpan) : ⁅e7SerreF i, y⁆ ∈ e7SerreNegSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e7SerreNegSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e7SerreNegSpan.smul_mem c ha
  | mem _ hp =>
      rcases hp with ⟨p, rfl⟩
      have heq : ⁅e7SerreF i, e7SerreNegVec p⁆ =
          e7SerreChevalleyInv ⁅e7SerreE i, e7SerrePosVec p⁆ := by
        rw [LieEquiv.map_lie, e7SerreChevalleyInv_E]
        rfl
      rw [heq]
      exact e7_chevalley_posSpan_mem_negSpan (e7Serre_adE_posVec_mem i p)

private theorem e7Serre_adF_cartan_mem (i : Fin 7) {y : LieAlgebra.e₇ ℝ}
    (hy : y ∈ e7SerreCartan) : ⁅e7SerreF i, y⁆ ∈ e7SerreNegSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e7SerreNegSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e7SerreNegSpan.smul_mem c ha
  | mem _ hj =>
      rcases hj with ⟨j, rfl⟩
      rw [← lie_skew (e7SerreF i) (e7SerreH j), e7Serre_bracket_HF, ← neg_smul]
      exact e7SerreNegSpan.smul_mem _ (e7SerreF_mem_negSpan i)

private theorem e7Serre_adF_posSpan_mem (i : Fin 7) {y : LieAlgebra.e₇ ℝ}
    (hy : y ∈ e7SerrePosSpan) : ⁅e7SerreF i, y⁆ ∈ e7SerreSpan133 := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e7SerreSpan133.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e7SerreSpan133.smul_mem c ha
  | mem _ hp =>
      rcases hp with ⟨p, rfl⟩
      have hmem := e7Serre_adF_posVec_mem i 17 p (e7PosHeight_le_17 p)
      rw [Submodule.mem_sup] at hmem
      rcases hmem with ⟨u, hu, v, hv, huv⟩
      rw [← huv]
      exact e7SerreSpan133.add_mem (Submodule.mem_sup_right hu)
        (Submodule.mem_sup_left (Submodule.mem_sup_right hv))

private theorem e7Serre_span133_ad_invariant (x : LieAlgebra.e₇ ℝ)
    (hx : x ∈ (Set.range e7SerreH ∪ Set.range e7SerreE ∪ Set.range e7SerreF)) :
    x ∈ e7SubmoduleLieNormalizer e7SerreSpan133 := by
  intro y hy
  have hy' : y ∈ e7SerreNegSpan ⊔ e7SerreCartan ⊔ e7SerrePosSpan := hy
  rcases Submodule.mem_sup.mp hy' with ⟨y₁, hy₁, y₃, hy₃, rfl⟩
  rcases Submodule.mem_sup.mp hy₁ with ⟨y_neg, hy_neg, y_car, hy_car, rfl⟩
  rw [lie_add, lie_add]
  rcases hx with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
  · exact e7SerreSpan133.add_mem
      (e7SerreSpan133.add_mem
        (Submodule.mem_sup_left (Submodule.mem_sup_left (e7Serre_adH_negSpan_mem i hy_neg)))
        (Submodule.mem_sup_left (Submodule.mem_sup_right (e7Serre_adH_cartan_mem i hy_car))))
      (Submodule.mem_sup_right (e7Serre_adH_posSpan_mem i hy₃))
  · exact e7SerreSpan133.add_mem
      (e7SerreSpan133.add_mem
        (e7Serre_adE_negSpan_mem i hy_neg)
        (Submodule.mem_sup_right (e7Serre_adE_cartan_mem i hy_car)))
      (Submodule.mem_sup_right (e7Serre_adE_posSpan_mem i hy₃))
  · exact e7SerreSpan133.add_mem
      (e7SerreSpan133.add_mem
        (Submodule.mem_sup_left (Submodule.mem_sup_left (e7Serre_adF_negSpan_mem i hy_neg)))
        (Submodule.mem_sup_left (Submodule.mem_sup_left (e7Serre_adF_cartan_mem i hy_car))))
      (e7Serre_adF_posSpan_mem i hy₃)

private theorem e7Serre_span133_eq_top : e7SerreSpan133 = ⊤ := by
  have hnorm : e7SubmoduleLieNormalizer e7SerreSpan133 = ⊤ := by
    apply e7Serre_generators_generate
    · intro i
      exact e7Serre_span133_ad_invariant _ (Or.inl (Or.inl ⟨i, rfl⟩))
    · intro i
      exact e7Serre_span133_ad_invariant _ (Or.inl (Or.inr ⟨i, rfl⟩))
    · intro i
      exact e7Serre_span133_ad_invariant _ (Or.inr ⟨i, rfl⟩)
  let S_lie : LieSubalgebra ℝ (LieAlgebra.e₇ ℝ) :=
    { e7SerreSpan133 with
      lie_mem' := fun {x y} _ hy => by
        have hx_norm : x ∈ e7SubmoduleLieNormalizer e7SerreSpan133 := by rw [hnorm]; trivial
        exact hx_norm y hy }
  have htop : S_lie = ⊤ := by
    apply e7Serre_generators_generate
    · intro i
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (e7SerreH_mem_cartan i))
    · intro i
      exact Submodule.mem_sup_right (e7SerreE_mem_posSpan i)
    · intro i
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (e7SerreF_mem_negSpan i))
  exact congrArg LieSubalgebra.toSubmodule htop

private noncomputable def e7SerreSpanVec :
    Fin 7 ⊕ Fin 63 ⊕ Fin 63 → LieAlgebra.e₇ ℝ :=
  Sum.elim e7SerreH (Sum.elim e7SerrePosVec e7SerreNegVec)

private theorem e7SerreSpanVec_span_eq_top :
    Submodule.span ℝ (Set.range e7SerreSpanVec) = ⊤ := by
  rw [← e7Serre_span133_eq_top]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨idx, rfl⟩
    rcases idx with i | p | p
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (e7SerreH_mem_cartan i))
    · exact Submodule.mem_sup_right (e7SerrePosVec_mem_posSpan p)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨p, rfl⟩))
  · refine sup_le (sup_le ?_ ?_) ?_
    · dsimp only [e7SerreNegSpan]
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact Submodule.subset_span ⟨Sum.inr (Sum.inr p), rfl⟩
    · dsimp only [e7SerreCartan]
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    · dsimp only [e7SerrePosSpan]
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact Submodule.subset_span ⟨Sum.inr (Sum.inl p), rfl⟩

/-- `LieAlgebra.e₇ ℝ` is finite-dimensional, spanned by the 133 Chevalley elements. -/
instance e7Serre_finiteDimensional : FiniteDimensional ℝ (LieAlgebra.e₇ ℝ) := by
  have : Module.Finite ℝ (Submodule.span ℝ (Set.range e7SerreSpanVec)) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range e7SerreSpanVec)
  exact Module.Finite.equiv
    ((LinearEquiv.ofEq _ ⊤ e7SerreSpanVec_span_eq_top).trans Submodule.topEquiv)

/-- The Serre presentation of `E₇` over `ℝ` has dimension at most `133`. -/
theorem finrank_e7_serre_le : Module.finrank ℝ (LieAlgebra.e₇ ℝ) ≤ 133 := by
  have h := finrank_le_of_span_eq_top e7SerreSpanVec_span_eq_top
  simpa using h

/-- The descended Serre quotient homomorphism `LieAlgebra.e₇ ℝ →ₗ⁅ℝ⁆ H3ZornTKKLie`
is injective. -/
theorem h3zornE7SerreQuotientMap_injective :
    Function.Injective h3zornE7SerreQuotientMap := by
  let f := h3zornE7SerreQuotientMap.toLinearMap
  have hrange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr h3zornE7SerreQuotientMap_surjective
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, finrank_H3ZornTKKLie] at hrank
  have hle : Module.finrank ℝ (LieAlgebra.e₇ ℝ) ≤ 133 := finrank_e7_serre_le
  have hker0 : Module.finrank ℝ (LinearMap.ker f) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker0)

/-- **E₇ Serre Isomorphism**: Mathlib's Serre quotient `LieAlgebra.e₇ ℝ` is isomorphic
as a real Lie algebra to the 133-dimensional split `E₇` TKK Lie algebra `H3ZornTKKLie`. -/
noncomputable def h3zornE7SerreEquiv :
    LieAlgebra.e₇ ℝ ≃ₗ⁅ℝ⁆ H3ZornTKKLie :=
  LieEquiv.ofBijective h3zornE7SerreQuotientMap
    ⟨h3zornE7SerreQuotientMap_injective, h3zornE7SerreQuotientMap_surjective⟩

/-- Mathlib's Serre presentation `LieAlgebra.e₇ ℝ` has exact dimension `133`. -/
theorem finrank_e7_serre : Module.finrank ℝ (LieAlgebra.e₇ ℝ) = 133 := by
  rw [LinearEquiv.finrank_eq h3zornE7SerreEquiv.toLinearEquiv, finrank_H3ZornTKKLie]

/-- Mathlib's Serre presentation `LieAlgebra.e₇ ℝ` is a simple real Lie algebra. -/
instance e7Serre_isSimple : LieAlgebra.IsSimple ℝ (LieAlgebra.e₇ ℝ) where
  eq_bot_or_eq_top I := by
    rcases LieAlgebra.IsSimple.eq_bot_or_eq_top
        (I.map (h3zornE7SerreEquiv : LieAlgebra.e₇ ℝ →ₗ⁅ℝ⁆ H3ZornTKKLie)) with
      hbot | htop
    · exact Or.inl (LieIdeal.bot_of_map_eq_bot h3zornE7SerreEquiv.injective hbot)
    · right
      rw [eq_top_iff]
      intro x _
      have hx : (h3zornE7SerreEquiv : LieAlgebra.e₇ ℝ →ₗ⁅ℝ⁆ H3ZornTKKLie) x ∈
          I.map (h3zornE7SerreEquiv : LieAlgebra.e₇ ℝ →ₗ⁅ℝ⁆ H3ZornTKKLie) := by
        rw [htop]
        trivial
      obtain ⟨y, hy⟩ := LieIdeal.mem_map_of_surjective h3zornE7SerreEquiv.surjective hx
      have hyx : (y : LieAlgebra.e₇ ℝ) = x := h3zornE7SerreEquiv.injective hy
      rw [← hyx]
      exact y.2
  non_abelian := by
    rw [lie_abelian_iff_equiv_lie_abelian h3zornE7SerreEquiv]
    exact LieAlgebra.IsSimple.non_abelian ℝ

end InfoGeometry.Algebra
