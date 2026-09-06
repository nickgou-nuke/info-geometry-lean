import InfoGeometry.Lie.CanonicalZornMathlibRootSpace
import InfoGeometry.Lie.CanonicalZornIdealWeightDecomposition
import InfoGeometry.Lie.CanonicalZornAbelianIdeal
import InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy
import Mathlib.Algebra.Lie.Abelian

/-!
# Root-space obstruction for abelian ideals

This is the root-component part of the semisimplicity argument.  It is stated
elementwise so that the later Mathlib ideal decomposition can consume it
without introducing a second decomposition API.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornSemisimple

open InfoGeometry.Lie.CanonicalZornMathlibRootSpace
open InfoGeometry.Lie.CanonicalZornAbelianIdeal
open InfoGeometry.Lie.CanonicalZornMathlibBridge
open InfoGeometry.Lie.CanonicalZornIdealWeightDecomposition
open InfoGeometry.Lie.CanonicalZornCartanRootSystem
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornCartanAdjointAction
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

abbrev Der := CanonicalZornCartanAdjointAction.Der

theorem abelianIdeal_cartan_inf_eq_bot
    (I : LieIdeal ℝ Der) [hI : IsLieAbelian I] :
    idealRestrict I axialCartanLieSubalgebra ⊓
        axialCartanLieSubalgebra.toLieSubmodule = ⊥ := by
  rw [eq_bot_iff]
  intro H hH
  by_cases hHz : H = 0
  · exact hHz
  have hHleft := hH.1
  change H ∈ I at hHleft
  let HC : axialCartanLieSubalgebra := ⟨H, hH.2⟩
  have hHC : HC ≠ 0 := by
    intro hzero
    exact hHz (congrArg Subtype.val hzero)
  have hsep := nativeRootWeights_separate (H := HC) hHC
  obtain ⟨i, hi⟩ := hsep
  let X : Der := rootDerivation i.1
  have hbr' : ⁅(H : Der), X⁆ = nativeRootWeight i HC • X := by
    change ⁅(HC : Der), rootDerivation i.1⁆ =
      (rootWeight i.1 (axialCartanLieEquiv.symm HC) : ℝ) •
        rootDerivation i.1
    rw [← adCartan_rootDerivation (axialCartanLieEquiv.symm HC) i.1]
    simp [adCartan_apply, nativeRootWeight, HC]
  have hXI : X ∈ I := by
    have hbr : ⁅(H : Der), X⁆ ∈ I := by
      exact lie_mem_left ℝ Der I H X hHleft
    have hnonzero : nativeRootWeight i HC ≠ 0 := hi
    have := I.smul_mem (nativeRootWeight i HC)⁻¹ hbr
    simpa [hbr', smul_smul, hnonzero] using this
  have hbr : ⁅(H : Der), X⁆ ∈ I := by
    exact lie_mem_left ℝ Der I H X hHleft
  have hab : ⁅(H : Der), ⁅(H : Der), X⁆⁆ = 0 := by
    exact congrArg Subtype.val (hI.trivial ⟨H, hHleft⟩ ⟨⁅(H : Der), X⁆, hbr⟩)
  have hcalc : ⁅(H : Der), ⁅(H : Der), X⁆⁆ =
      (nativeRootWeight i HC) ^ 2 • X := by
    calc
      ⁅(H : Der), ⁅(H : Der), X⁆⁆ =
          ⁅(H : Der), nativeRootWeight i HC • X⁆ :=
        congrArg (fun Y : Der => ⁅(H : Der), Y⁆) hbr'
      _ = nativeRootWeight i HC • ⁅(H : Der), X⁆ := by
        rw [lie_smul]
      _ = nativeRootWeight i HC • (nativeRootWeight i HC • X) :=
        congrArg (fun Y : Der => nativeRootWeight i HC • Y) hbr'
      _ = (nativeRootWeight i HC) ^ 2 • X := by
        rw [smul_smul]
        ring_nf
  rw [hcalc] at hab
  have hXzero : X = 0 :=
    (smul_eq_zero.mp hab).resolve_left (pow_ne_zero 2 hi)
  exact False.elim (rootDerivation_ne_zero i.1 hXzero)

theorem abelianIdeal_rootSpace_mem_eq_zero
    (I : LieIdeal ℝ Der) [hI : IsLieAbelian I]
    (i j : nonzeroIndex)
    (hdouble :
      ⁅⁅rootDerivation j.1, rootDerivation i.1⁆, rootDerivation i.1⁆ ≠ 0)
    {X : Der} (hXI : X ∈ I)
    (hXroot : X ∈
      LieAlgebra.rootSpace axialCartanLieSubalgebra (nativeRootWeight i)) :
    X = 0 := by
  have hXroot' : X ∈ ℝ ∙ rootDerivation i.1 := by
    rw [← mathlib_rootSpace_eq_span_rootDerivation i]
    exact hXroot
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hXroot'
  by_cases hc : c = 0
  · simp [hc]
  have hrootI : rootDerivation i.1 ∈ I := by
    have hs := I.smul_mem c⁻¹ hXI
    simpa [smul_smul, hc] using hs
  have hbrI : ⁅rootDerivation j.1, rootDerivation i.1⁆ ∈ I :=
    lie_mem_right ℝ Der I (rootDerivation j.1) (rootDerivation i.1) hrootI
  have hzero :
      ⁅⁅rootDerivation j.1, rootDerivation i.1⁆, rootDerivation i.1⁆ = 0 := by
    exact abelianIdeal_bracket_eq_zero I
      ⟨⁅rootDerivation j.1, rootDerivation i.1⁆, hbrI⟩
      ⟨rootDerivation i.1, hrootI⟩
  exact False.elim (hdouble hzero)

private theorem opposite_double_bracket_reverse
    (i j : nonzeroIndex)
    (hij : ∀ k : TracelessWeight,
      rootWeight j.1 k = -rootWeight i.1 k)
    (hforward :
      ⁅⁅rootDerivation i.1, rootDerivation j.1⁆,
        rootDerivation i.1⁆ ≠ 0) :
    ⁅⁅rootDerivation i.1, rootDerivation j.1⁆,
      rootDerivation j.1⁆ ≠ 0 := by
  intro hreverse
  have hcartan :
      ⁅rootDerivation i.1, rootDerivation j.1⁆ ∈
        axialCartanLieSubalgebra := by
    change ⁅rootDerivation i.1, rootDerivation j.1⁆ ∈
      axialCartanLieSubalgebra.toLieSubmodule
    apply rootDerivation_bracket_mem_nativeCartan_of_opposite
    funext k
    change rootWeight i.1 (axialCartanLieEquiv.symm k) +
      rootWeight j.1 (axialCartanLieEquiv.symm k) = 0
    rw [hij]
    simp
  let k : TracelessWeight :=
    axialCartanLieEquiv.symm
      ⟨⁅rootDerivation i.1, rootDerivation j.1⁆, hcartan⟩
  have hcartan_eq :
      (axialCartanLieEquiv k : Der) =
        ⁅rootDerivation i.1, rootDerivation j.1⁆ := by
    simp [k]
  have hi_action :
      ⁅⁅rootDerivation i.1, rootDerivation j.1⁆,
        rootDerivation i.1⁆ =
        (rootWeight i.1 k : ℝ) • rootDerivation i.1 := by
    rw [← hcartan_eq]
    simpa [CanonicalZornCartanAdjointAction.adCartan_apply] using
      adCartan_rootDerivation k i.1
  have hj_action :
      ⁅⁅rootDerivation i.1, rootDerivation j.1⁆,
        rootDerivation j.1⁆ =
        (rootWeight j.1 k : ℝ) • rootDerivation j.1 := by
    rw [← hcartan_eq]
    simpa [CanonicalZornCartanAdjointAction.adCartan_apply] using
      adCartan_rootDerivation k j.1
  have hi_ne : rootWeight i.1 k ≠ 0 := by
    intro hzero
    apply hforward
    rw [hi_action, hzero, zero_smul]
  have hreverse' : (-(rootWeight i.1 k)) • rootDerivation j.1 = 0 := by
    simpa [hj_action, hij k, neg_smul] using hreverse
  rcases smul_eq_zero.mp hreverse' with hscalar | hvector
  · exact hi_ne (neg_eq_zero.mp hscalar)
  · exact rootDerivation_ne_zero j.1 hvector

private theorem lie_bracket_reverse_inner_ne_zero
    {x y : Der}
    (hforward : ⁅⁅x, y⁆, x⁆ ≠ 0) :
    ⁅⁅y, x⁆, x⁆ ≠ 0 := by
  intro hreverse
  apply hforward
  calc
      ⁅⁅x, y⁆, x⁆ = -⁅⁅y, x⁆, x⁆ := by
        rw [show ⁅x, y⁆ = -⁅y, x⁆ by rw [lie_skew]]
        rw [neg_lie]
    _ = 0 := by rw [hreverse, neg_zero]

private theorem reverse_double_bracket_0_10 :
    ⁅⁅rootDerivation 10, rootDerivation 0⁆, rootDerivation 0⁆ ≠ 0 :=
  lie_bracket_reverse_inner_ne_zero
    (x := rootDerivation 0) (y := rootDerivation 10)
    InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy.opposite_root_double_bracket_0_10

private theorem reverse_double_bracket_1_5 :
    ⁅⁅rootDerivation 5, rootDerivation 1⁆, rootDerivation 1⁆ ≠ 0 :=
  lie_bracket_reverse_inner_ne_zero
    (x := rootDerivation 1) (y := rootDerivation 5)
    InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy.opposite_root_double_bracket_1_5

private theorem reverse_double_bracket_2_11 :
    ⁅⁅rootDerivation 11, rootDerivation 2⁆, rootDerivation 2⁆ ≠ 0 :=
  lie_bracket_reverse_inner_ne_zero
    (x := rootDerivation 2) (y := rootDerivation 11)
    InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy.opposite_root_double_bracket_2_11

private theorem reverse_double_bracket_3_9 :
    ⁅⁅rootDerivation 9, rootDerivation 3⁆, rootDerivation 3⁆ ≠ 0 :=
  lie_bracket_reverse_inner_ne_zero
    (x := rootDerivation 3) (y := rootDerivation 9)
    InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy.opposite_root_double_bracket_3_9

private theorem reverse_double_bracket_4_8 :
    ⁅⁅rootDerivation 8, rootDerivation 4⁆, rootDerivation 4⁆ ≠ 0 :=
  lie_bracket_reverse_inner_ne_zero
    (x := rootDerivation 4) (y := rootDerivation 8)
    InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy.opposite_root_double_bracket_4_8

private theorem double_bracket_3_9 :
    ⁅⁅rootDerivation 3, rootDerivation 9⁆, rootDerivation 9⁆ ≠ 0 :=
  opposite_double_bracket_reverse
    ⟨3, by decide, by decide⟩ ⟨9, by decide, by decide⟩
    (fun k => by
      change rootWeight (9 : Fin 14) k = -rootWeight (3 : Fin 14) k
      exact rootWeight_neg_pair_3_9 k)
    InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy.opposite_root_double_bracket_3_9

private theorem double_bracket_2_11 :
    ⁅⁅rootDerivation 2, rootDerivation 11⁆, rootDerivation 11⁆ ≠ 0 :=
  opposite_double_bracket_reverse
    ⟨2, by decide, by decide⟩ ⟨11, by decide, by decide⟩
    (fun k => by
      change rootWeight (11 : Fin 14) k = -rootWeight (2 : Fin 14) k
      exact rootWeight_neg_pair_2_11 k)
    InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy.opposite_root_double_bracket_2_11

private theorem double_bracket_1_5 :
    ⁅⁅rootDerivation 1, rootDerivation 5⁆, rootDerivation 5⁆ ≠ 0 :=
  opposite_double_bracket_reverse
    ⟨1, by decide, by decide⟩ ⟨5, by decide, by decide⟩
    (fun k => by
      change rootWeight (5 : Fin 14) k = -rootWeight (1 : Fin 14) k
      exact rootWeight_neg_pair_1_5 k)
    InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy.opposite_root_double_bracket_1_5

private theorem double_bracket_0_10 :
    ⁅⁅rootDerivation 0, rootDerivation 10⁆, rootDerivation 10⁆ ≠ 0 :=
  opposite_double_bracket_reverse
    ⟨0, by decide, by decide⟩ ⟨10, by decide, by decide⟩
    (fun k => rootWeight_neg_pair_0_10 k)
    InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy.opposite_root_double_bracket_0_10

private theorem double_bracket_7_12 :
    ⁅⁅rootDerivation 7, rootDerivation 12⁆, rootDerivation 12⁆ ≠ 0 :=
  opposite_double_bracket_reverse
    ⟨7, by decide, by decide⟩ ⟨12, by decide, by decide⟩
    (fun k => rootWeight_neg_pair_7_12 k)
    InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy.opposite_root_double_bracket_7_12

private theorem reverse_double_bracket_7_12 :
    ⁅⁅rootDerivation 12, rootDerivation 7⁆, rootDerivation 7⁆ ≠ 0 :=
  lie_bracket_reverse_inner_ne_zero
    (x := rootDerivation 7) (y := rootDerivation 12)
    InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy.opposite_root_double_bracket_7_12

private theorem double_bracket_4_8 :
    ⁅⁅rootDerivation 4, rootDerivation 8⁆, rootDerivation 8⁆ ≠ 0 :=
  opposite_double_bracket_reverse
    ⟨4, by decide, by decide⟩ ⟨8, by decide, by decide⟩
    (fun k => by
      have h := congrArg Neg.neg (rootWeight_neg_pair_4_8 k)
      simpa only [neg_neg] using h.symm)
    InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy.opposite_root_double_bracket_4_8

private theorem opposite_double_bracket_for_index
    (i : nonzeroIndex) :
    ∃ j : nonzeroIndex,
      ⁅⁅rootDerivation j.1, rootDerivation i.1⁆, rootDerivation i.1⁆ ≠ 0 := by
  rcases i with ⟨i, hi6, hi13⟩
  have hi_cases :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 := by
    omega
  rcases hi_cases with h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst i
  · exact ⟨⟨10, by decide, by decide⟩, by simpa only using reverse_double_bracket_0_10⟩
  · exact ⟨⟨5, by decide, by decide⟩, by simpa only using reverse_double_bracket_1_5⟩
  · exact ⟨⟨11, by decide, by decide⟩, by simpa only using reverse_double_bracket_2_11⟩
  · exact ⟨⟨9, by decide, by decide⟩, by simpa only using reverse_double_bracket_3_9⟩
  · exact ⟨⟨8, by decide, by decide⟩, by simpa only using reverse_double_bracket_4_8⟩
  · exact ⟨⟨1, by decide, by decide⟩, by simpa only using double_bracket_1_5⟩
  · exact ⟨⟨12, by decide, by decide⟩, by simpa only using reverse_double_bracket_7_12⟩
  · exact ⟨⟨4, by decide, by decide⟩, by simpa only using double_bracket_4_8⟩
  · exact ⟨⟨3, by decide, by decide⟩, by simpa only using double_bracket_3_9⟩
  · exact ⟨⟨0, by decide, by decide⟩, by simpa only using double_bracket_0_10⟩
  · exact ⟨⟨2, by decide, by decide⟩, by simpa only using double_bracket_2_11⟩
  · exact ⟨⟨7, by decide, by decide⟩, by simpa only using double_bracket_7_12⟩

theorem no_nonzero_abelian_ideal
    (I : LieIdeal ℝ Der) [hI : IsLieAbelian I] : I = ⊥ := by
  have hroot : ∀ (i : nonzeroIndex) {X : Der}, X ∈ I →
      X ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra (nativeRootWeight i) → X = 0 := by
    intro i X hXI hXroot
    obtain ⟨j, hdouble⟩ := opposite_double_bracket_for_index i
    exact abelianIdeal_rootSpace_mem_eq_zero I i j hdouble hXI hXroot
  have hcartan :
      idealRestrict I axialCartanLieSubalgebra ⊓
          axialCartanLieSubalgebra.toLieSubmodule = ⊥ :=
    abelianIdeal_cartan_inf_eq_bot I
  have hroot' : ∀ (α : LieModule.Weight ℝ axialCartanLieSubalgebra Der),
      α.IsNonZero →
        idealRestrict I axialCartanLieSubalgebra ⊓
            LieAlgebra.rootSpace axialCartanLieSubalgebra α = ⊥ := by
    intro α hα
    obtain ⟨i, hi⟩ := mathlib_nonzero_weight_eq_nativeRootWeight α hα
    rw [← hi]
    apply le_antisymm
    · intro X hX
      exact hroot i hX.1 hX.2
    · exact bot_le
  have hdecomp :=
    lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace
      (H := axialCartanLieSubalgebra) I
  have hrestr : idealRestrict I axialCartanLieSubalgebra = ⊥ := by
    rw [hdecomp, hcartan]
    simp only [bot_sup_eq, iSup_bot]
    apply iSup₂_eq_bot.mpr
    intro α hα
    exact hroot' α hα
  apply le_antisymm
  · intro X hX
    have hX' : X ∈ idealRestrict I axialCartanLieSubalgebra := hX
    rw [hrestr] at hX'
    exact hX'
  · exact bot_le

end InfoGeometry.Lie.CanonicalZornSemisimple
