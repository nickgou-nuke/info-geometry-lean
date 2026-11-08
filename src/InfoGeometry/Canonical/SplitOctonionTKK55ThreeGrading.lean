import InfoGeometry.OperatorAlgebra.TKKConformalClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionTKK55LieEquivalence

/-!
# Concrete three-grading of the hyperbolic TKK carrier

The carrier is written as `(a, (K, (x, y)))`.  The `x` and `y` components are
the two outer grades and `(a, K)` is the structure grade.  This owner turns
that concrete decomposition into Mathlib submodules and proves the grading
rules from the already verified component bracket.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionTKK55ThreeGrading

open InfoGeometry.Canonical.SplitOctonionTKK55
open InfoGeometry.Canonical.SplitOctonionTKK55LieEquivalence
open InfoGeometry.Canonical.SplitOctonionTKK55Blocks
open InfoGeometry.Canonical.SplitOctonionSkew28
open InfoGeometry.Canonical.SplitOctonionJordanForm
open InfoGeometry.OperatorAlgebra.TKKConformalClosure

abbrev Carrier := AbstractTKKCarrier

def gradeMinus : Submodule ℝ Carrier where
  carrier := {d | d.1 = 0 ∧ d.2.1 = 0 ∧ d.2.2.1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Prod.add_def] at hx hy ⊢
    rcases hx with ⟨hxa, hxK, hxx⟩
    rcases hy with ⟨hya, hyK, hxy⟩
    exact ⟨by simp [hxa, hya], by simp [hxK, hyK], by simp [hxx, hxy]⟩
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rcases hx with ⟨hxa, hxK, hxx⟩
    exact ⟨by simp [hxa], by simp [hxK], by simp [hxx]⟩

def gradeZero : Submodule ℝ Carrier where
  carrier := {d | d.2.2.1 = 0 ∧ d.2.2.2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Prod.add_def] at hx hy ⊢
    rcases hx with ⟨hxx, hxy⟩
    rcases hy with ⟨hyx, hyy⟩
    exact ⟨by simp [hxx, hyx], by simp [hxy, hyy]⟩
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rcases hx with ⟨hxx, hxy⟩
    exact ⟨by simp [hxx], by simp [hxy]⟩

def gradePlus : Submodule ℝ Carrier where
  carrier := {d | d.1 = 0 ∧ d.2.1 = 0 ∧ d.2.2.2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Prod.add_def] at hx hy ⊢
    rcases hx with ⟨hxa, hxK, hxy⟩
    rcases hy with ⟨hya, hyK, hyy⟩
    exact ⟨by simp [hxa, hya], by simp [hxK, hyK], by simp [hxy, hyy]⟩
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rcases hx with ⟨hxa, hxK, hxy⟩
    exact ⟨by simp [hxa], by simp [hxK], by simp [hxy]⟩

noncomputable def gradeMinusMap : SplitOctonionTKK55.Middle →ₗ[ℝ] gradeMinus where
  toFun x := ⟨(0, (0, (0, x))), by simp [gradeMinus]⟩
  map_add' x y := by
    apply Subtype.ext
    simp [Prod.add_def]
  map_smul' c x := by
    apply Subtype.ext
    simp [Prod.smul_mk]

noncomputable def gradePlusMap : SplitOctonionTKK55.Middle →ₗ[ℝ] gradePlus where
  toFun x := ⟨(0, (0, (x, 0))), by simp [gradePlus]⟩
  map_add' x y := by
    apply Subtype.ext
    simp [Prod.add_def]
  map_smul' c x := by
    apply Subtype.ext
    simp [Prod.smul_mk]

noncomputable def gradeZeroMap : (ℝ × OrthogonalMiddle) →ₗ[ℝ] gradeZero where
  toFun d := ⟨(d.1, (d.2, (0, 0))), by simp [gradeZero]⟩
  map_add' x y := by
    apply Subtype.ext
    simp [Prod.add_def]
  map_smul' c x := by
    apply Subtype.ext
    simp [Prod.smul_mk]

noncomputable def gradeMinusEquiv : SplitOctonionTKK55.Middle ≃ₗ[ℝ] gradeMinus :=
  LinearEquiv.ofBijective gradeMinusMap
    ⟨(fun x y h => by
        exact congrArg (fun d : gradeMinus => (d : Carrier).2.2.2) h),
      (fun d => by
        refine ⟨(d : Carrier).2.2.2, ?_⟩
        apply Subtype.ext
        rcases d with ⟨⟨a, K, x, y⟩, hd⟩
        change a = 0 ∧ K = 0 ∧ x = 0 at hd
        rcases hd with ⟨rfl, rfl, rfl⟩
        rfl)⟩

noncomputable def gradePlusEquiv : SplitOctonionTKK55.Middle ≃ₗ[ℝ] gradePlus :=
  LinearEquiv.ofBijective gradePlusMap
    ⟨(fun x y h => by
        exact congrArg (fun d : gradePlus => (d : Carrier).2.2.1) h),
      (fun d => by
        refine ⟨(d : Carrier).2.2.1, ?_⟩
        apply Subtype.ext
        rcases d with ⟨⟨a, K, x, y⟩, hd⟩
        change a = 0 ∧ K = 0 ∧ y = 0 at hd
        rcases hd with ⟨rfl, rfl, rfl⟩
        rfl)⟩

noncomputable def gradeZeroEquiv : (ℝ × OrthogonalMiddle) ≃ₗ[ℝ] gradeZero :=
  LinearEquiv.ofBijective gradeZeroMap
    ⟨(fun x y h => by
        exact congrArg (fun d : gradeZero =>
          ((d : Carrier).1, (d : Carrier).2.1)) h),
      (fun d => by
        refine ⟨((d : Carrier).1, (d : Carrier).2.1), ?_⟩
        apply Subtype.ext
        rcases d with ⟨⟨a, K, x, y⟩, hd⟩
        change x = 0 ∧ y = 0 at hd
        rcases hd with ⟨rfl, rfl⟩
        rfl)⟩

theorem finrank_gradeMinus : Module.finrank ℝ gradeMinus = 8 := by
  rw [← LinearEquiv.finrank_eq gradeMinusEquiv]
  simp [SplitOctonionTKK55.Middle]

theorem finrank_gradePlus : Module.finrank ℝ gradePlus = 8 := by
  rw [← LinearEquiv.finrank_eq gradePlusEquiv]
  simp [SplitOctonionTKK55.Middle]

theorem finrank_gradeZero : Module.finrank ℝ gradeZero = 29 := by
  rw [← LinearEquiv.finrank_eq gradeZeroEquiv]
  simp [SplitOctonionSkew28.finrank_orthogonal44]

noncomputable def tkkToMinus : SplitOctonionTKK55.Middle →ₗ[ℝ] Carrier where
  toFun y := (0, (0, (0, y)))
  map_add' x y := by
    simp [Prod.add_def]
  map_smul' c x := by
    simp [Prod.smul_mk]

noncomputable def tkkToPlus : SplitOctonionTKK55.Middle →ₗ[ℝ] Carrier where
  toFun x := (0, (0, (x, 0)))
  map_add' x y := by
    simp [Prod.add_def]
  map_smul' c x := by
    simp [Prod.smul_mk]

theorem tkkToMinus_mem_grade (x : SplitOctonionTKK55.Middle) :
    tkkToMinus x ∈ gradeMinus := by
  simp [tkkToMinus, gradeMinus]

theorem tkkToPlus_mem_grade (x : SplitOctonionTKK55.Middle) :
    tkkToPlus x ∈ gradePlus := by
  simp [tkkToPlus, gradePlus]

theorem grade_decomposition_eq_top :
    (⊤ : Submodule ℝ Carrier) = gradeMinus ⊔ gradeZero ⊔ gradePlus := by
  apply le_antisymm
  · intro d hd
    let dm : Carrier := (0, (0, (0, d.2.2.2)))
    let dz : Carrier := (d.1, (d.2.1, (0, 0)))
    let dp : Carrier := (0, (0, (d.2.2.1, 0)))
    have hdm : dm ∈ gradeMinus := by
      simp [dm, gradeMinus]
    have hdz : dz ∈ gradeZero := by
      simp [dz, gradeZero]
    have hdp : dp ∈ gradePlus := by
      simp [dp, gradePlus]
    have hsum : d = (dm + dz) + dp := by
      ext <;> simp [dm, dz, dp]
    rw [hsum]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup hdm hdz) hdp
  · exact le_top

private theorem bracket_eq_concrete (d e : Carrier) :
    ⁅d, e⁆ = tkkBracket d e := by
  exact (tkkBracket_eq_abstractTKKBracket d e).symm

private theorem orthogonal44Bracket_zero_left (K : OrthogonalMiddle) :
    orthogonal44Bracket 0 K = 0 := by
  apply Subtype.ext
  simp [orthogonal44Bracket]

private theorem orthogonal44Bracket_zero_right (K : OrthogonalMiddle) :
    orthogonal44Bracket K 0 = 0 := by
  apply Subtype.ext
  simp [orthogonal44Bracket]

private theorem rankTwoOrthogonal_zero_left (y : TKKMiddle) :
    rankTwoOrthogonal 0 y = 0 := by
  apply Subtype.ext
  ext i j
  simp [rankTwoOrthogonal, rankTwoMatrix, eta44Matrix, eta44,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem rankTwoOrthogonal_zero_right (x : TKKMiddle) :
    rankTwoOrthogonal x 0 = 0 := by
  apply Subtype.ext
  ext i j
  simp [rankTwoOrthogonal, rankTwoMatrix, eta44Matrix, eta44,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem tkk_triple_identity
    (x y z : SplitOctonionTKK55.Middle) :
    ⁅⁅tkkToMinus x, tkkToPlus y⁆, tkkToMinus z⁆ =
      ⁅⁅tkkToMinus z, tkkToPlus y⁆, tkkToMinus x⁆ := by
  rw [bracket_eq_concrete, bracket_eq_concrete, bracket_eq_concrete,
    bracket_eq_concrete]
  simp [tkkToMinus, tkkToPlus, tkkBracket,
    rankTwoOrthogonal_zero_left, rankTwoOrthogonal_zero_right,
    orthogonal44Bracket_zero_right]
  ext i
  simp [rankTwoOrthogonal, rankTwoMatrix, eta44Matrix, eta44,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem bracket_gradeMinus_gradeMinus
    {d e : Carrier} (hd : d ∈ gradeMinus) (he : e ∈ gradeMinus) :
    ⁅d, e⁆ = 0 := by
  rw [bracket_eq_concrete]
  rcases d with ⟨a, K, x, y⟩
  rcases e with ⟨b, L, u, v⟩
  change a = 0 ∧ K = 0 ∧ x = 0 at hd
  change b = 0 ∧ L = 0 ∧ u = 0 at he
  rcases hd with ⟨rfl, rfl, rfl⟩
  rcases he with ⟨rfl, rfl, rfl⟩
  simp [tkkBracket, orthogonal44Bracket_zero_right,
    rankTwoOrthogonal_zero_left]

theorem bracket_gradePlus_gradePlus
    {d e : Carrier} (hd : d ∈ gradePlus) (he : e ∈ gradePlus) :
    ⁅d, e⁆ = 0 := by
  rw [bracket_eq_concrete]
  rcases d with ⟨a, K, x, y⟩
  rcases e with ⟨b, L, u, v⟩
  change a = 0 ∧ K = 0 ∧ y = 0 at hd
  change b = 0 ∧ L = 0 ∧ v = 0 at he
  rcases hd with ⟨rfl, rfl, rfl⟩
  rcases he with ⟨rfl, rfl, rfl⟩
  simp [tkkBracket, orthogonal44Bracket_zero_right,
    rankTwoOrthogonal_zero_right]

theorem bracket_gradeZero_gradeMinus
    {d e : Carrier} (hd : d ∈ gradeZero) (he : e ∈ gradeMinus) :
    ⁅d, e⁆ ∈ gradeMinus := by
  rw [bracket_eq_concrete]
  rcases d with ⟨a, K, x, y⟩
  rcases e with ⟨b, L, u, v⟩
  change x = 0 ∧ y = 0 at hd
  change b = 0 ∧ L = 0 ∧ u = 0 at he
  rcases hd with ⟨rfl, rfl⟩
  rcases he with ⟨rfl, rfl, rfl⟩
  simp [tkkBracket, gradeMinus, orthogonal44Bracket_zero_right,
    rankTwoOrthogonal_zero_left, rankTwoOrthogonal_zero_right]

theorem bracket_gradeZero_gradePlus
    {d e : Carrier} (hd : d ∈ gradeZero) (he : e ∈ gradePlus) :
    ⁅d, e⁆ ∈ gradePlus := by
  rw [bracket_eq_concrete]
  rcases d with ⟨a, K, x, y⟩
  rcases e with ⟨b, L, u, v⟩
  change x = 0 ∧ y = 0 at hd
  change b = 0 ∧ L = 0 ∧ v = 0 at he
  rcases hd with ⟨rfl, rfl⟩
  rcases he with ⟨rfl, rfl, rfl⟩
  simp [tkkBracket, gradePlus, orthogonal44Bracket_zero_right,
    rankTwoOrthogonal_zero_right]

theorem bracket_gradeZero_gradeZero
    {d e : Carrier} (hd : d ∈ gradeZero) (he : e ∈ gradeZero) :
    ⁅d, e⁆ ∈ gradeZero := by
  rw [bracket_eq_concrete]
  rcases d with ⟨a, K, x, y⟩
  rcases e with ⟨b, L, u, v⟩
  change x = 0 ∧ y = 0 at hd
  change u = 0 ∧ v = 0 at he
  rcases hd with ⟨rfl, rfl⟩
  rcases he with ⟨rfl, rfl⟩
  simp [tkkBracket, gradeZero, rankTwoOrthogonal_zero_right]

theorem bracket_gradeMinus_gradePlus
    {d e : Carrier} (hd : d ∈ gradeMinus) (he : e ∈ gradePlus) :
    ⁅d, e⁆ ∈ gradeZero := by
  rw [bracket_eq_concrete]
  rcases d with ⟨a, K, x, y⟩
  rcases e with ⟨b, L, u, v⟩
  change a = 0 ∧ K = 0 ∧ x = 0 at hd
  change b = 0 ∧ L = 0 ∧ v = 0 at he
  rcases hd with ⟨rfl, rfl, rfl⟩
  rcases he with ⟨rfl, rfl, rfl⟩
  simp [tkkBracket, gradeZero, orthogonal44Bracket_zero_right,
    rankTwoOrthogonal_zero_right]

noncomputable def concreteTKKThreeGrading :
    TKKThreeGrading Carrier where
  gMinus := gradeMinus
  gZero := gradeZero
  gPlus := gradePlus
  decomposition_eq_top := grade_decomposition_eq_top
  bracket_minus_minus := by
    intro X Y hX hY
    exact bracket_gradeMinus_gradeMinus hX hY
  bracket_plus_plus := by
    intro X Y hX hY
    exact bracket_gradePlus_gradePlus hX hY
  bracket_zero_minus := by
    intro X Y hX hY
    exact bracket_gradeZero_gradeMinus hX hY
  bracket_zero_plus := by
    intro X Y hX hY
    exact bracket_gradeZero_gradePlus hX hY
  bracket_zero_zero := by
    intro X Y hX hY
    exact bracket_gradeZero_gradeZero hX hY
  bracket_minus_plus := by
    intro X Y hX hY
    exact bracket_gradeMinus_gradePlus hX hY

theorem concrete_tkk_three_grading_packet :
    concreteTKKThreeGrading.gMinus = gradeMinus ∧
      concreteTKKThreeGrading.gZero = gradeZero ∧
      concreteTKKThreeGrading.gPlus = gradePlus := by
  exact ⟨rfl, rfl, rfl⟩

end InfoGeometry.Canonical.SplitOctonionTKK55ThreeGrading

end noncomputable section
