import InfoGeometry.HodgeCohomology.KreinHodgeDiracBounded
import InfoGeometry.Krein.DoubledSpace
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

namespace InfoGeometry.HodgeCohomology.KreinHodgeObstruction

open InfoGeometry.Krein
open KreinSpace KreinHodgeDiracBounded
open CategoryTheory

noncomputable section

abbrev Plane := DoubledSpace ℝ

def nullDirac : Plane →L[ℝ] Plane :=
  (fst_L + snd_L : Plane →L[ℝ] ℝ).smulRight (to_doubled 1 (-1))

theorem nullDirac_apply (state : Plane) :
    nullDirac state =
      to_doubled (WithLp.fst state + WithLp.snd state)
        (-(WithLp.fst state + WithLp.snd state)) := by
  apply DoubledSpace.ext <;> simp [nullDirac, fst_L, snd_L]

theorem nullDirac_pairing :
    LinearMap.IsAdjointPair kreinBilin kreinBilin nullDirac nullDirac := by
  intro left right
  change kreinInner (nullDirac left) right = kreinInner left (nullDirac right)
  rw [nullDirac_apply, nullDirac_apply, krein_inner_prod_l2, krein_inner_prod_l2]
  simp only [WithLp.fst, WithLp.snd]
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right]
  ring

theorem nullDirac_krein_adjoint : kreinAdjoint nullDirac = nullDirac :=
  kreinAdjoint_eq_of_pairing nullDirac nullDirac nullDirac_pairing

theorem nullDirac_square : nullDirac * nullDirac = 0 := by
  apply ContinuousLinearMap.ext
  intro state
  change nullDirac (nullDirac state) = 0
  simp only [nullDirac_apply, fst_to_doubled, snd_to_doubled, add_neg_cancel, neg_zero]
  rfl

theorem nullDirac_kernel_counterexample :
    LinearMap.ker (nullDirac * nullDirac).toLinearMap ≠
      LinearMap.ker nullDirac.toLinearMap := by
  intro equal_kernels
  have in_square : (to_doubled 1 0 : Plane) ∈
      LinearMap.ker (nullDirac * nullDirac).toLinearMap := by
    rw [nullDirac_square]
    simp
  rw [equal_kernels] at in_square
  have first_component := congrArg WithLp.fst in_square
  norm_num [nullDirac_apply] at first_component

theorem nullDirac_range_eq_kernel :
    LinearMap.range nullDirac.toLinearMap = LinearMap.ker nullDirac.toLinearMap := by
  ext state
  constructor
  · rintro ⟨primitive, rfl⟩
    exact congrArg (fun operator : Plane →L[ℝ] Plane => operator primitive) nullDirac_square
  · intro closed
    have coordinate_sum := congrArg WithLp.fst closed
    change WithLp.fst (nullDirac state) = 0 at coordinate_sum
    simp only [nullDirac_apply, fst_to_doubled] at coordinate_sum
    refine ⟨to_doubled (WithLp.fst state) 0, ?_⟩
    change nullDirac (to_doubled (WithLp.fst state) 0) = state
    rw [nullDirac_apply]
    apply DoubledSpace.ext
    · simp
    · simp only [fst_to_doubled, snd_to_doubled, add_zero]
      linarith

def nullComplex : ShortComplex (ModuleCat ℝ) :=
  ShortComplex.moduleCatMkOfKerLERange
    (ModuleCat.ofHom nullDirac.toLinearMap) (ModuleCat.ofHom nullDirac.toLinearMap)
    nullDirac_range_eq_kernel.le

theorem nullComplex_exact : nullComplex.Exact := by
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker nullComplex).mpr
  exact nullDirac_range_eq_kernel

theorem nullComplex_homology_zero : Limits.IsZero nullComplex.homology :=
  (ShortComplex.exact_iff_isZero_homology nullComplex).mp nullComplex_exact

theorem nonzero_exact_closed_coclosed_harmonic :
    ∃ state : Plane, state ≠ 0 ∧
      state ∈ LinearMap.range nullDirac.toLinearMap ∧
      nullDirac state = 0 ∧ kreinAdjoint nullDirac state = 0 ∧
      (nullDirac * kreinAdjoint nullDirac + kreinAdjoint nullDirac * nullDirac) state = 0 := by
  refine ⟨to_doubled 1 (-1), ?_, ?_, ?_, ?_, ?_⟩
  · intro zero_state
    have first := congrArg WithLp.fst zero_state
    norm_num at first
  · refine ⟨to_doubled 1 0, ?_⟩
    change nullDirac (to_doubled 1 0) = to_doubled 1 (-1)
    simp [nullDirac_apply]
  · simp [nullDirac_apply]
  · rw [nullDirac_krein_adjoint]
    simp [nullDirac_apply]
  · rw [nullDirac_krein_adjoint, nullDirac_square]
    simp

end

end InfoGeometry.HodgeCohomology.KreinHodgeObstruction
