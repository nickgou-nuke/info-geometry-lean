import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
import InfoGeometry.Lie.SplitOctonionCrossTensor

/-!
# Levi--Civita completion of the native circular Zorn table

The Cartesian/circular owner already owns the Peirce actions, the general
opposite-root Kronecker packet, and the raw same-root cross-product readout.
This focused completion only records their `diagEll` commutator consequences
and rewrites the same-root cross channel using the existing native
Levi--Civita tensor. It does not identify diagonal `diagEll` with the separate
off-diagonal `lUnit` carrier.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable

open InfoGeometry.Canonical
open InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita
open InfoGeometry.Lie.SplitOctonionEllFlowOperator
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

/-! The opposite-root packet in scalar Kronecker-delta form.  The underlying
`if`-form identities are owned by the circular-basis file; these readouts
make the tensorial coefficient explicit without introducing a new carrier. -/

theorem cartesianZorn_rootPlus_mul_rootMinus_delta (i j : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootMinus j) =
      (if i = j then (1 : ℝ) else 0) •
        InfoGeometry.Canonical.ZornMatrix.zornPlus := by
  rw [cartesianZorn_rootPlus_mul_rootMinus_if]
  by_cases h : i = j <;> simp [h]

theorem cartesianZorn_rootMinus_mul_rootPlus_delta (i j : Fin 3) :
    cartesianZornLinearEquiv (rootMinus i) *
        cartesianZornLinearEquiv (rootPlus j) =
      (if i = j then (1 : ℝ) else 0) •
        InfoGeometry.Canonical.ZornMatrix.zornMinus := by
  rw [cartesianZorn_rootMinus_mul_rootPlus_if]
  by_cases h : i = j <;> simp [h]

theorem cartesianZorn_rootPlus_rootMinus_commutator_delta (i j : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootMinus j) -
      cartesianZornLinearEquiv (rootMinus j) *
        cartesianZornLinearEquiv (rootPlus i) =
      (if i = j then (1 : ℝ) else 0) • diagEll := by
  rw [cartesianZorn_root_commutator_if]
  by_cases h : i = j <;> simp [h]

theorem cartesianZorn_rootPlus_rootMinus_anticommutator_delta (i j : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootMinus j) +
      cartesianZornLinearEquiv (rootMinus j) *
        cartesianZornLinearEquiv (rootPlus i) =
      (if i = j then (1 : ℝ) else 0) •
        (1 : InfoGeometry.Canonical.ZornMatrix ℝ) := by
  rw [cartesianZorn_root_anticommutator_if]
  by_cases h : i = j <;> simp [h]

theorem diagEll_rootPlus_commutator (i : Fin 3) :
    diagEll * cartesianZornLinearEquiv (rootPlus i) -
        cartesianZornLinearEquiv (rootPlus i) * diagEll =
      2 • cartesianZornLinearEquiv (rootPlus i) := by
  rw [diagEll_mul_cartesianZorn_rootPlus,
    cartesianZorn_rootPlus_mul_diagEll]
  module

theorem diagEll_rootMinus_commutator (i : Fin 3) :
    diagEll * cartesianZornLinearEquiv (rootMinus i) -
        cartesianZornLinearEquiv (rootMinus i) * diagEll =
      (-2 : ℝ) • cartesianZornLinearEquiv (rootMinus i) := by
  rw [diagEll_mul_cartesianZorn_rootMinus,
    cartesianZorn_rootMinus_mul_diagEll]
  module

theorem diagEll_rootPlus_anticommutator (i : Fin 3) :
    diagEll * cartesianZornLinearEquiv (rootPlus i) +
        cartesianZornLinearEquiv (rootPlus i) * diagEll = 0 := by
  rw [diagEll_mul_cartesianZorn_rootPlus,
    cartesianZorn_rootPlus_mul_diagEll, add_neg_cancel]

theorem diagEll_rootMinus_anticommutator (i : Fin 3) :
    diagEll * cartesianZornLinearEquiv (rootMinus i) +
        cartesianZornLinearEquiv (rootMinus i) * diagEll = 0 := by
  rw [diagEll_mul_cartesianZorn_rootMinus,
    cartesianZorn_rootMinus_mul_diagEll, neg_add_cancel]

@[simp] theorem cross_axis_apply (i j k : Fin 3) :
    ZornMatrix.cross (axis i) (axis j) k =
      (leviCivita3 k i j : ℝ) := by
  rw [InfoGeometry.Lie.SplitOctonionCrossTensor.nativeCross_eq_leviCivita3]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [axis, leviCivita3, Fin.sum_univ_three, Pi.single_apply]

theorem cross_axis_expansion (i j : Fin 3) :
    ZornMatrix.cross (axis i) (axis j) =
      ∑ k : Fin 3, (leviCivita3 k i j : ℝ) • axis k := by
  funext k
  rw [cross_axis_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [axis, leviCivita3, Fin.sum_univ_three, Pi.single_apply]

theorem leviCivita3_swap_last (k i j : Fin 3) :
    (leviCivita3 k j i : ℝ) = -(leviCivita3 k i j : ℝ) := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [leviCivita3]
  all_goals apply Fin.ext <;> rfl

theorem cartesianZorn_rootPlus_mul_rootPlus_leviCivita (i j : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootPlus j) =
      ∑ k : Fin 3, (leviCivita3 k i j : ℝ) •
        cartesianZornLinearEquiv (rootMinus k) := by
  rw [cartesianZorn_rootPlus_mul_rootPlus_cross]
  simp_rw [cartesianZorn_rootMinus]
  have hsum :
      (∑ k : Fin 3, (leviCivita3 k i j : ℝ) •
          InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis k) =
        (let Z : InfoGeometry.Canonical.ZornMatrix ℝ :=
          { a := 0, b := 0, x := 0,
            y := InfoGeometry.Canonical.ZornMatrix.cross (axis i) (axis j) }
         Z) := by
    let Z : InfoGeometry.Canonical.ZornMatrix ℝ :=
      { a := 0, b := 0, x := 0,
        y := InfoGeometry.Canonical.ZornMatrix.cross (axis i) (axis j) }
    have h := InfoGeometry.Canonical.ZornMatrix.anticolorProject_eq_chiralLower_sum Z
    rw [InfoGeometry.Canonical.ZornMatrix.anticolorProject_apply] at h
    calc
      (∑ k : Fin 3, (leviCivita3 k i j : ℝ) •
          InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis k) =
          ∑ k : Fin 3, (InfoGeometry.Canonical.ZornMatrix.cross
            (axis i) (axis j) k) •
            InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [cross_axis_apply]
      _ = Z := by
        simpa [Z] using h.symm
  rw [hsum]

theorem cartesianZorn_rootMinus_mul_rootMinus_leviCivita (i j : Fin 3) :
    cartesianZornLinearEquiv (rootMinus i) *
        cartesianZornLinearEquiv (rootMinus j) =
      -∑ k : Fin 3, (leviCivita3 k i j : ℝ) •
        cartesianZornLinearEquiv (rootPlus k) := by
  rw [cartesianZorn_rootMinus_mul_rootMinus_cross]
  simp_rw [cartesianZorn_rootPlus]
  have hsum :
      (∑ k : Fin 3, (leviCivita3 k i j : ℝ) •
          InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis k) =
        (let Z : InfoGeometry.Canonical.ZornMatrix ℝ :=
          { a := 0, b := 0,
            x := InfoGeometry.Canonical.ZornMatrix.cross (axis i) (axis j),
            y := 0 }
         Z) := by
    let Z : InfoGeometry.Canonical.ZornMatrix ℝ :=
      { a := 0, b := 0,
        x := InfoGeometry.Canonical.ZornMatrix.cross (axis i) (axis j),
        y := 0 }
    have h := InfoGeometry.Canonical.ZornMatrix.colorProject_eq_chiralUpper_sum Z
    rw [InfoGeometry.Canonical.ZornMatrix.colorProject_apply] at h
    calc
      (∑ k : Fin 3, (leviCivita3 k i j : ℝ) •
          InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis k) =
          ∑ k : Fin 3, (InfoGeometry.Canonical.ZornMatrix.cross
            (axis i) (axis j) k) •
            InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [cross_axis_apply]
      _ = Z := by
        simpa [Z] using h.symm
  rw [hsum]
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    simp

theorem cartesianZorn_rootPlus_commutator_leviCivita (i j : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootPlus j) -
      cartesianZornLinearEquiv (rootPlus j) *
        cartesianZornLinearEquiv (rootPlus i) =
      2 • ∑ k : Fin 3, (leviCivita3 k i j : ℝ) •
        cartesianZornLinearEquiv (rootMinus k) := by
  rw [cartesianZorn_rootPlus_mul_rootPlus_leviCivita,
    cartesianZorn_rootPlus_mul_rootPlus_leviCivita]
  have hswap :
      (∑ k : Fin 3, (leviCivita3 k j i : ℝ) •
          cartesianZornLinearEquiv (rootMinus k)) =
        -(∑ k : Fin 3, (leviCivita3 k i j : ℝ) •
          cartesianZornLinearEquiv (rootMinus k)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [leviCivita3_swap_last]
    module
  rw [hswap]
  module

theorem cartesianZorn_rootMinus_commutator_leviCivita (i j : Fin 3) :
    cartesianZornLinearEquiv (rootMinus i) *
        cartesianZornLinearEquiv (rootMinus j) -
      cartesianZornLinearEquiv (rootMinus j) *
        cartesianZornLinearEquiv (rootMinus i) =
      -2 • ∑ k : Fin 3, (leviCivita3 k i j : ℝ) •
        cartesianZornLinearEquiv (rootPlus k) := by
  rw [cartesianZorn_rootMinus_mul_rootMinus_leviCivita,
    cartesianZorn_rootMinus_mul_rootMinus_leviCivita]
  have hswap :
      (∑ k : Fin 3, (leviCivita3 k j i : ℝ) •
          cartesianZornLinearEquiv (rootPlus k)) =
        -(∑ k : Fin 3, (leviCivita3 k i j : ℝ) •
          cartesianZornLinearEquiv (rootPlus k)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [leviCivita3_swap_last]
    module
  rw [hswap]
  module

theorem cartesianZorn_rootPlus_same_channel_anticommutator (i j : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootPlus j) +
      cartesianZornLinearEquiv (rootPlus j) *
        cartesianZornLinearEquiv (rootPlus i) = 0 := by
  rw [cartesianZorn_rootPlus_mul_rootPlus_leviCivita,
    cartesianZorn_rootPlus_mul_rootPlus_leviCivita]
  have hswap :
      (∑ k : Fin 3, (leviCivita3 k j i : ℝ) •
          cartesianZornLinearEquiv (rootMinus k)) =
        -(∑ k : Fin 3, (leviCivita3 k i j : ℝ) •
          cartesianZornLinearEquiv (rootMinus k)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [leviCivita3_swap_last]
    module
  rw [hswap]
  module

theorem cartesianZorn_rootMinus_same_channel_anticommutator (i j : Fin 3) :
    cartesianZornLinearEquiv (rootMinus i) *
        cartesianZornLinearEquiv (rootMinus j) +
      cartesianZornLinearEquiv (rootMinus j) *
        cartesianZornLinearEquiv (rootMinus i) = 0 := by
  rw [cartesianZorn_rootMinus_mul_rootMinus_leviCivita,
    cartesianZorn_rootMinus_mul_rootMinus_leviCivita]
  have hswap :
      (∑ k : Fin 3, (leviCivita3 k j i : ℝ) •
          cartesianZornLinearEquiv (rootPlus k)) =
        -(∑ k : Fin 3, (leviCivita3 k i j : ℝ) •
          cartesianZornLinearEquiv (rootPlus k)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [leviCivita3_swap_last]
    module
  rw [hswap]
  module

end InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable
