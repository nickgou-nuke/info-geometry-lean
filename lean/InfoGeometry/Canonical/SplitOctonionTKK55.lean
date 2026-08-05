import InfoGeometry.Canonical.SplitOctonionJordanCore
import InfoGeometry.Canonical.SplitOctonionSkew28
import InfoGeometry.Canonical.SplitOctonionSpinJordanTriple
import InfoGeometry.OperatorAlgebra.TKKClosure

/-!
# Hyperbolic TKK55 carrier and grade maps

This owner constructs the independently typed hyperbolic carrier
`ℝ ⊕ MiddleCarrier ⊕ ℝ` and its signature-compatible `P`/`N` grade maps.
It does not identify the resulting operator algebra with `so(5,5)` yet.
-/

namespace InfoGeometry.Canonical.SplitOctonionTKK55

open SplitOctonionJordanForm

abbrev Middle := MiddleCarrier
abbrev Carrier := ℝ × (Middle × ℝ)

theorem carrier_finrank :
    Module.finrank ℝ Carrier = 10 := by
  simp [Middle, Carrier, Module.finrank_fin_fun]

def hyperbolicBeta (x y : Carrier) : ℝ :=
  x.1 * y.2.2 + beta44 x.2.1 y.2.1 + x.2.2 * y.1

theorem hyperbolicBeta_symmetric (x y : Carrier) :
    hyperbolicBeta x y = hyperbolicBeta y x := by
  simp [hyperbolicBeta, beta44_symmetric, mul_comm, add_comm, add_left_comm]

theorem hyperbolicBeta_add_left (x y z : Carrier) :
    hyperbolicBeta (x + y) z = hyperbolicBeta x z + hyperbolicBeta y z := by
  simp [hyperbolicBeta, beta44_add_left]
  ring

theorem hyperbolicBeta_add_right (x y z : Carrier) :
    hyperbolicBeta x (y + z) = hyperbolicBeta x y + hyperbolicBeta x z := by
  simp [hyperbolicBeta, beta44_add_right]
  ring

theorem hyperbolicBeta_smul_left (r : ℝ) (x y : Carrier) :
    hyperbolicBeta (r • x) y = r * hyperbolicBeta x y := by
  simp [hyperbolicBeta, beta44_smul_left, smul_eq_mul]
  ring

theorem hyperbolicBeta_smul_right (r : ℝ) (x y : Carrier) :
    hyperbolicBeta x (r • y) = r * hyperbolicBeta x y := by
  simp [hyperbolicBeta, beta44_smul_right, smul_eq_mul]
  ring

def P (x : Middle) (z : Carrier) : Carrier :=
  (0, (z.1 • x, -beta44 x z.2.1))

def N (y : Middle) (z : Carrier) : Carrier :=
  (-beta44 y z.2.1, (z.2.2 • y, 0))

def pMap : Middle →ₗ[ℝ] Module.End ℝ Carrier where
  toFun x := {
    toFun := P x
    map_add' u v := by
      rcases u with ⟨a, u, c⟩
      rcases v with ⟨b, v, d⟩
      change ((0 : ℝ), ((a + b) • x, -beta44 x (u + v))) =
        ((0 : ℝ), (a • x, -beta44 x u)) + ((0 : ℝ), (b • x, -beta44 x v))
      congr 1
      · simp
      · apply Prod.ext
        · change (a + b) • x = a • x + b • x
          module
        · change -beta44 x (u + v) = -beta44 x u + -beta44 x v
          rw [beta44_add_right]
          ring

    map_smul' r u := by
      rcases u with ⟨a, u, c⟩
      change ((0 : ℝ), ((r * a) • x, -beta44 x (r • u))) =
        r • ((0 : ℝ), (a • x, -beta44 x u))
      congr 1
      · simp
      · apply Prod.ext
        · change (r * a) • x = r • (a • x)
          simp [smul_smul, smul_eq_mul]
        · change -beta44 x (r • u) = r • (-beta44 x u)
          rw [beta44_smul_right]
          simp [smul_eq_mul]
          ring
  }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    rcases z with ⟨a, u, c⟩
    change ((0 : ℝ), (a • (x + y), -beta44 (x + y) u)) =
      ((0 : ℝ), (a • x, -beta44 x u)) + ((0 : ℝ), (a • y, -beta44 y u))
    congr 1
    · simp
    · apply Prod.ext
      · change a • (x + y) = a • x + a • y
        module
      · change -beta44 (x + y) u = -beta44 x u + -beta44 y u
        rw [beta44_add_left]
        ring
  map_smul' r x := by
    apply LinearMap.ext
    intro z
    rcases z with ⟨a, u, c⟩
    change ((0 : ℝ), (a • (r • x), -beta44 (r • x) u)) =
      r • ((0 : ℝ), (a • x, -beta44 x u))
    congr 1
    · simp
    · apply Prod.ext
      · change a • (r • x) = r • (a • x)
        simp [smul_smul, smul_eq_mul, mul_comm]
      · change -beta44 (r • x) u = r • (-beta44 x u)
        rw [beta44_smul_left]
        simp [smul_eq_mul]
        ring

def nMap : Middle →ₗ[ℝ] Module.End ℝ Carrier where
  toFun y := {
    toFun := N y
    map_add' u v := by
      rcases u with ⟨a, u, c⟩
      rcases v with ⟨b, v, d⟩
      change (-beta44 y (u + v), (((c + d) • y), 0)) =
        (-beta44 y u, (c • y, 0)) + (-beta44 y v, (d • y, 0))
      congr 1
      · change -beta44 y (u + v) = -beta44 y u + -beta44 y v
        rw [beta44_add_right]
        ring
      · apply Prod.ext
        · change (c + d) • y = c • y + d • y
          module
        · norm_num
    map_smul' r u := by
      rcases u with ⟨a, u, c⟩
      change (-beta44 y (r • u), ((r * c) • y, 0)) =
        r • (-beta44 y u, (c • y, 0))
      congr 1
      · change -beta44 y (r • u) = r • (-beta44 y u)
        rw [beta44_smul_right]
        simp [smul_eq_mul]
        ring
      · apply Prod.ext
        · change (r * c) • y = r • (c • y)
          simp [smul_smul, smul_eq_mul]
        · norm_num
  }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    rcases z with ⟨a, u, c⟩
    change N (x + y) (a, (u, c)) =
      N x (a, (u, c)) + N y (a, (u, c))
    change (-beta44 (x + y) u, (c • (x + y), (0 : ℝ))) =
      (-beta44 x u, (c • x, (0 : ℝ))) + (-beta44 y u, (c • y, (0 : ℝ)))
    congr 1
    · change -beta44 (x + y) u = -beta44 x u + -beta44 y u
      rw [beta44_add_left]
      ring
    · apply Prod.ext
      · change c • (x + y) = c • x + c • y
        module
      · norm_num
  map_smul' r y := by
    apply LinearMap.ext
    intro z
    rcases z with ⟨a, u, c⟩
    change N (r • y) (a, (u, c)) = r • N y (a, (u, c))
    change (-beta44 (r • y) u, (c • (r • y), (0 : ℝ))) =
      r • (-beta44 y u, (c • y, (0 : ℝ)))
    congr 1
    · change -beta44 (r • y) u = r • (-beta44 y u)
      rw [beta44_smul_left]
      simp [smul_eq_mul]
      ring
    · apply Prod.ext
      · change c • (r • y) = r • (c • y)
        simp [smul_smul, smul_eq_mul, mul_comm]
      · norm_num

@[simp] theorem pMap_apply (x : Middle) (z : Carrier) : pMap x z = P x z := rfl

@[simp] theorem nMap_apply (y : Middle) (z : Carrier) : nMap y z = N y z := rfl

theorem P_hyperbolic_skew (x : Middle) (u v : Carrier) :
    hyperbolicBeta (P x u) v + hyperbolicBeta u (P x v) = 0 := by
  rcases u with ⟨a, u, c⟩
  rcases v with ⟨b, v, d⟩
  simp [P, hyperbolicBeta, beta44_symmetric]
  ring

theorem N_hyperbolic_skew (y : Middle) (u v : Carrier) :
    hyperbolicBeta (N y u) v + hyperbolicBeta u (N y v) = 0 := by
  rcases u with ⟨a, u, c⟩
  rcases v with ⟨b, v, d⟩
  simp [N, hyperbolicBeta, beta44_symmetric]
  ring

theorem hyperbolicBeta_P_zero (x : Middle) :
    hyperbolicBeta (P x (0, (0, 0))) (0, (0, 0)) = 0 := by
  simp [P, hyperbolicBeta]

theorem hyperbolicBeta_N_zero (y : Middle) :
    hyperbolicBeta (N y (0, (0, 0))) (0, (0, 0)) = 0 := by
  simp [N, hyperbolicBeta]

/-! ## Nilpotent grade readbacks -/

theorem P_commutator_zero (x y : Middle) (z : Carrier) :
    P x (P y z) - P y (P x z) = 0 := by
  rcases z with ⟨a, u, c⟩
  simp [P, beta44_symmetric]
  ring

theorem N_commutator_zero (x y : Middle) (z : Carrier) :
    N x (N y z) - N y (N x z) = 0 := by
  rcases z with ⟨a, u, c⟩
  simp [N, beta44_symmetric]
  ring

theorem pMap_lie_commute (x y : Middle) :
    pMap x * pMap y - pMap y * pMap x = 0 := by
  apply LinearMap.ext
  intro z
  simpa [Module.End.mul_apply, pMap_apply] using P_commutator_zero x y z

theorem nMap_lie_commute (x y : Middle) :
    nMap x * nMap y - nMap y * nMap x = 0 := by
  apply LinearMap.ext
  intro z
  simpa [Module.End.mul_apply, nMap_apply] using N_commutator_zero x y z

theorem P_comp_N_apply (x y : Middle) (z : Carrier) :
    P x (N y z) =
      (0, ((-beta44 y z.2.1) • x, -beta44 x (z.2.2 • y))) := by
  rcases z with ⟨a, u, c⟩
  rfl

theorem N_comp_P_apply (x y : Middle) (z : Carrier) :
    N y (P x z) =
      (-beta44 y (z.1 • x), ((-beta44 x z.2.1) • y, 0)) := by
  rcases z with ⟨a, u, c⟩
  rfl

theorem P_N_commutator_apply (x y : Middle) (z : Carrier) :
    P x (N y z) - N y (P x z) =
      (beta44 y (z.1 • x),
        ((-beta44 y z.2.1) • x - (-beta44 x z.2.1) • y,
          -beta44 x (z.2.2 • y))) := by
  rcases z with ⟨a, u, c⟩
  simp [P, N]

/-! ## Explicit exhaustive block-data carrier -/

abbrev OrthogonalMiddle := SplitOctonionSkew28.Orthogonal44
abbrev BlockData := ℝ × (OrthogonalMiddle × (Middle × Middle))

theorem blockData_finrank : Module.finrank ℝ BlockData = 45 := by
  simp [BlockData, SplitOctonionSkew28.finrank_orthogonal44]

def blockOperator (d : BlockData) : Module.End ℝ Carrier where
  toFun z :=
    (d.1 * z.1 - beta44 d.2.2.2 z.2.1,
      (z.1 • d.2.2.1 + d.2.1.1.mulVec z.2.1 + z.2.2 • d.2.2.2,
        -beta44 d.2.2.1 z.2.1 - d.1 * z.2.2))
  map_add' z w := by
    rcases z with ⟨a, u, c⟩
    rcases w with ⟨b, v, q⟩
    apply Prod.ext
    · change d.1 * (a + b) - beta44 d.2.2.2 (u + v) =
        (d.1 * a - beta44 d.2.2.2 u) + (d.1 * b - beta44 d.2.2.2 v)
      rw [beta44_add_right]
      ring
    · apply Prod.ext
      · change (a + b) • d.2.2.1 + d.2.1.1.mulVec (u + v) +
          (c + q) • d.2.2.2 =
          (a • d.2.2.1 + d.2.1.1.mulVec u + c • d.2.2.2) +
            (b • d.2.2.1 + d.2.1.1.mulVec v + q • d.2.2.2)
        rw [Matrix.mulVec_add]
        module
      · change -beta44 d.2.2.1 (u + v) - d.1 * (c + q) =
          (-beta44 d.2.2.1 u - d.1 * c) +
            (-beta44 d.2.2.1 v - d.1 * q)
        rw [beta44_add_right]
        ring
  map_smul' r z := by
    rcases z with ⟨a, u, c⟩
    apply Prod.ext
    · change d.1 * (r * a) - beta44 d.2.2.2 (r • u) =
        r • (d.1 * a - beta44 d.2.2.2 u)
      rw [beta44_smul_right]
      simp [smul_eq_mul]
      ring
    · apply Prod.ext
      · change (r * a) • d.2.2.1 + d.2.1.1.mulVec (r • u) +
          (r * c) • d.2.2.2 =
          r • (a • d.2.2.1 + d.2.1.1.mulVec u + c • d.2.2.2)
        rw [Matrix.mulVec_smul]
        module
      · change -beta44 d.2.2.1 (r • u) - d.1 * (r * c) =
          r • (-beta44 d.2.2.1 u - d.1 * c)
        rw [beta44_smul_right]
        simp [smul_eq_mul]
        ring

@[simp] theorem blockOperator_apply (d : BlockData) (z : Carrier) :
    blockOperator d z =
      (d.1 * z.1 - beta44 d.2.2.2 z.2.1,
        (z.1 • d.2.2.1 + d.2.1.1.mulVec z.2.1 + z.2.2 • d.2.2.2,
          -beta44 d.2.2.1 z.2.1 - d.1 * z.2.2)) := rfl

def blockOperatorLinear : BlockData →ₗ[ℝ] Module.End ℝ Carrier where
  toFun d := blockOperator d
  map_add' d e := by
    apply LinearMap.ext
    intro z
    rcases d with ⟨a, D, x, y⟩
    rcases e with ⟨b, E, u, v⟩
    rcases z with ⟨s, w, t⟩
    change ((a + b) * s - beta44 (y + v) w,
      (s • (x + u) + (D.1 + E.1).mulVec w + t • (y + v),
        -beta44 (x + u) w - (a + b) * t)) =
      (a * s - beta44 y w, (s • x + D.1.mulVec w + t • y,
        -beta44 x w - a * t)) +
        (b * s - beta44 v w, (s • u + E.1.mulVec w + t • v,
          -beta44 u w - b * t))
    apply Prod.ext
    · change (a + b) * s - beta44 (y + v) w =
        (a * s - beta44 y w) + (b * s - beta44 v w)
      rw [beta44_add_left]
      ring
    · apply Prod.ext
      · change s • (x + u) + (D.1 + E.1).mulVec w + t • (y + v) =
          (s • x + D.1.mulVec w + t • y) +
            (s • u + E.1.mulVec w + t • v)
        rw [Matrix.add_mulVec]
        module
      · change -beta44 (x + u) w - (a + b) * t =
          (-beta44 x w - a * t) + (-beta44 u w - b * t)
        rw [beta44_add_left]
        ring
  map_smul' r d := by
    apply LinearMap.ext
    intro z
    rcases d with ⟨a, D, x, y⟩
    rcases z with ⟨s, w, t⟩
    change ((r • a) * s - beta44 (r • y) w,
      (s • (r • x) + (r • D.1).mulVec w + t • (r • y),
        -beta44 (r • x) w - (r • a) * t)) =
      r • (a * s - beta44 y w,
        (s • x + D.1.mulVec w + t • y, -beta44 x w - a * t))
    apply Prod.ext
    · change (r • a) * s - beta44 (r • y) w =
        r • (a * s - beta44 y w)
      rw [beta44_smul_left]
      simp [smul_eq_mul]
      ring
    · apply Prod.ext
      · change s • (r • x) + (r • D.1).mulVec w + t • (r • y) =
          r • (s • x + D.1.mulVec w + t • y)
        rw [Matrix.smul_mulVec]
        module
      · change -beta44 (r • x) w - (r • a) * t =
          r • (-beta44 x w - a * t)
        rw [beta44_smul_left]
        simp [smul_eq_mul]
        ring

theorem blockOperatorLinear_injective :
    Function.Injective blockOperatorLinear := by
  intro d e h
  rcases d with ⟨a, D, x, y⟩
  rcases e with ⟨b, E, u, v⟩
  have h₀ := congrArg (fun T : Module.End ℝ Carrier => T (1, (0, 0))) h
  have h₁ := congrArg (fun T : Module.End ℝ Carrier => T (0, (0, 1))) h
  have hab : a = b := by
    simpa [blockOperatorLinear, blockOperator] using congrArg Prod.fst h₀
  have hxy : x = u := by
    simpa [blockOperatorLinear, blockOperator] using
      congrArg (fun z : Carrier => z.2.1) h₀
  have hyv : y = v := by
    simpa [blockOperatorLinear, blockOperator] using
      congrArg (fun z : Carrier => z.2.1) h₁
  subst hab
  subst hxy
  subst hyv
  have hDE : D.1 = E.1 := by
    apply Matrix.mulVec_injective
    funext w
    have hw := congrArg
      (fun T : Module.End ℝ Carrier => T (0, (w, 0))) h
    have hm := congrArg (fun z : Carrier => z.2.1) hw
    simp [blockOperatorLinear, blockOperator] at hm
    exact hm
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Subtype.ext
      exact hDE
    · rfl

theorem blockOperator_hyperbolic_skew (d : BlockData) (z w : Carrier) :
    hyperbolicBeta (blockOperator d z) w +
      hyperbolicBeta z (blockOperator d w) = 0 := by
  rcases d with ⟨a, ⟨D, ⟨x, y⟩⟩⟩
  rcases z with ⟨s, ⟨u, t⟩⟩
  rcases w with ⟨r, ⟨v, q⟩⟩
  have hD : beta44 (D.1.mulVec u) v + beta44 u (D.1.mulVec v) = 0 := by
    exact SplitOctonionSkew28.orthogonal44_beta_skew D u v
  change hyperbolicBeta
      (a * s - beta44 y u,
        (s • x + D.1.mulVec u + t • y, -beta44 x u - a * t))
      (r, (v, q)) +
      hyperbolicBeta (s, (u, t))
        (a * r - beta44 y v,
        (r • x + D.1.mulVec v + q • y, -beta44 x v - a * q)) = 0
  simp only [hyperbolicBeta, Prod.fst, Prod.snd,
    beta44_add_left, beta44_add_right, beta44_smul_left,
    beta44_smul_right, smul_eq_mul]
  rw [beta44_symmetric u y, beta44_symmetric u x]
  linear_combination hD

def hyperbolicSkewPredicate (T : Module.End ℝ Carrier) : Prop :=
  ∀ z w, hyperbolicBeta (T z) w + hyperbolicBeta z (T w) = 0

def hyperbolicSkewSubmodule :
    Submodule ℝ (Module.End ℝ Carrier) where
  carrier := {T | hyperbolicSkewPredicate T}
  zero_mem' := by
    intro z w
    simp [hyperbolicSkewPredicate, hyperbolicBeta]
  add_mem' := by
    intro T S hT hS z w
    change hyperbolicBeta ((T + S) z) w + hyperbolicBeta z ((T + S) w) = 0
    rw [LinearMap.add_apply, LinearMap.add_apply]
    rw [hyperbolicBeta_add_left, hyperbolicBeta_add_right]
    have h₁ := hT z w
    have h₂ := hS z w
    linarith
  smul_mem' := by
    intro r T hT z w
    change hyperbolicBeta ((r • T) z) w + hyperbolicBeta z ((r • T) w) = 0
    rw [LinearMap.smul_apply, LinearMap.smul_apply]
    rw [hyperbolicBeta_smul_left, hyperbolicBeta_smul_right]
    have h := hT z w
    linear_combination r * h

def blockOperatorLinearSubmodule :
    BlockData →ₗ[ℝ] hyperbolicSkewSubmodule where
  toFun d := ⟨blockOperator d, blockOperator_hyperbolic_skew d⟩
  map_add' d e := by
    apply Subtype.ext
    exact blockOperatorLinear.map_add d e
  map_smul' r d := by
    apply Subtype.ext
    exact blockOperatorLinear.map_smul r d

theorem blockOperatorLinearSubmodule_injective :
    Function.Injective blockOperatorLinearSubmodule := by
  intro d e h
  apply blockOperatorLinear_injective
  simpa [blockOperatorLinearSubmodule] using congrArg Subtype.val h

/-! ## Exhaustive block decomposition -/

def middleBlockMap (T : hyperbolicSkewSubmodule) : Middle →ₗ[ℝ] Middle where
  toFun u := (T.1 (0, (u, 0))).2.1
  map_add' u v := by
    simpa using congrArg (fun z : Carrier => z.2.1)
      (T.1.map_add (0, (u, 0)) (0, (v, 0)))
  map_smul' r u := by
    simpa using congrArg (fun z : Carrier => z.2.1)
      (T.1.map_smul r (0, (u, 0)))

set_option maxHeartbeats 1000000 in
noncomputable def blockDataOf (T : hyperbolicSkewSubmodule) : BlockData :=
    let eMinus : Carrier := (1, (0, 0))
    let ePlus : Carrier := (0, (0, 1))
    let teMinus := T.1 eMinus
    let tePlus := T.1 ePlus
    (teMinus.1,
    (⟨LinearMap.toMatrix' (middleBlockMap T), by
        rw [mem_skewAdjointMatricesSubmodule]
        simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
        ext i j
        have h := T.2 (0, (Pi.single i 1, 0))
          (0, (Pi.single j 1, 0))
        fin_cases i <;> fin_cases j <;>
          simp [hyperbolicBeta, Matrix.mul_apply,
            LinearMap.toMatrix'_apply, middleBlockMap, beta44,
            SplitOctonionSkew28.eta44, Matrix.transpose_apply,
            Fin.sum_univ_succ, Matrix.diagonal_apply,
            Pi.single_apply, Finset.sum_ite_irrel] at h ⊢ <;>
          linarith⟩,
      (teMinus.2.1, tePlus.2.1)))

theorem blockDataOf_components (T : hyperbolicSkewSubmodule) :
    let d := blockDataOf T
    let eMinus : Carrier := (1, (0, 0))
    let ePlus : Carrier := (0, (0, 1))
    T.1 eMinus = (d.1, (d.2.2.1, 0)) ∧
      T.1 ePlus = (0, (d.2.2.2, -d.1)) := by
  dsimp [blockDataOf]
  have hMinus := T.2 (1, (0, 0)) (1, (0, 0))
  have hPlus := T.2 (0, (0, 1)) (0, (0, 1))
  have hMinusPlus := T.2 (1, (0, 0)) (0, (0, 1))
  constructor
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · simp [hyperbolicBeta] at hMinus
        linarith
  · apply Prod.ext
    · simp [hyperbolicBeta] at hPlus
      linarith
    · apply Prod.ext
      · rfl
      · simp [hyperbolicBeta] at hMinusPlus
        linarith

theorem middleBlockMap_apply (T : hyperbolicSkewSubmodule) (u : Middle) :
    middleBlockMap T u =
      (LinearMap.toMatrix' (middleBlockMap T)).mulVec u := by
  rw [← Matrix.toLin'_apply]
  rw [Matrix.toLin'_toMatrix']

theorem blockDataOf_middle_components (T : hyperbolicSkewSubmodule) (u : Middle) :
    let d := blockDataOf T
    let m := T.1 (0, (u, 0))
    m.1 = -beta44 d.2.2.2 u ∧
      m.2.2 = -beta44 d.2.2.1 u ∧
      m.2.1 = d.2.1.1.mulVec u := by
  dsimp [blockDataOf]
  let eMinus : Carrier := (1, (0, 0))
  let ePlus : Carrier := (0, (0, 1))
  have hMinus := T.2 eMinus (0, (u, 0))
  have hPlus := T.2 ePlus (0, (u, 0))
  have hm := T.2 (0, (u, 0)) (0, (u, 0))
  have hMinus' : (T.1 (0, (u, 0))).2.2 =
      -beta44 (T.1 eMinus).2.1 u := by
    dsimp [eMinus] at hMinus
    simp [hyperbolicBeta, beta44] at hMinus ⊢
    linarith
  have hPlus' : (T.1 (0, (u, 0))).1 =
      -beta44 (T.1 ePlus).2.1 u := by
    dsimp [ePlus] at hPlus
    simp [hyperbolicBeta, beta44] at hPlus ⊢
    linarith
  refine ⟨?_, ?_, ?_⟩
  · dsimp [ePlus] at hPlus' ⊢
    exact hPlus'
  · dsimp [eMinus] at hMinus' ⊢
    exact hMinus'
  · change (T.1 (0, (u, 0))).2.1 = _
    change middleBlockMap T u = _
    exact (LinearMap.toMatrix'_mulVec (middleBlockMap T) u).symm

theorem blockOperatorLinearSubmodule_surjective :
    Function.Surjective blockOperatorLinearSubmodule := by
  intro T
  let d := blockDataOf T
  refine ⟨d, ?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  rcases z with ⟨s, u, t⟩
  have hc := blockDataOf_components T
  have hm := blockDataOf_middle_components T u
  have hz : (s, (u, t)) =
      s • (1, (0, 0)) + (0, (u, 0)) + t • (0, (0, 1)) := by
    ext <;> simp
  rcases hc with ⟨hcMinus, hcPlus⟩
  rcases hm with ⟨hm₁, hm₂, hm₃⟩
  have hMinus : blockOperator d (1, (0, 0)) = T.1 (1, (0, 0)) := by
    simpa [blockOperator, d] using hcMinus.symm
  have hPlus : blockOperator d (0, (0, 1)) = T.1 (0, (0, 1)) := by
    simpa [blockOperator, d] using hcPlus.symm
  have hMiddle : blockOperator d (0, (u, 0)) = T.1 (0, (u, 0)) := by
    apply Prod.ext
    · simpa [blockOperator, d] using hm₁.symm
    · apply Prod.ext
      · simpa [blockOperator, d] using hm₃.symm
      · simpa [blockOperator, d] using hm₂.symm
  change blockOperator d (s, (u, t)) = T.1 (s, (u, t))
  calc
    blockOperator d (s, (u, t)) =
        blockOperator d (s • (1, (0, 0)) + (0, (u, 0)) +
          t • (0, (0, 1))) := by rw [hz]
    _ = s • blockOperator d (1, (0, 0)) +
          blockOperator d (0, (u, 0)) +
          t • blockOperator d (0, (0, 1)) := by
      simp only [map_add, map_smul]
    _ = s • T.1 (1, (0, 0)) + T.1 (0, (u, 0)) +
          t • T.1 (0, (0, 1)) := by rw [hMinus, hMiddle, hPlus]
    _ = T.1 (s, (u, t)) := by
      simpa only [map_add, map_smul] using (congrArg T.1 hz).symm

noncomputable def blockOperatorLinearSubmoduleEquiv :
    BlockData ≃ₗ[ℝ] hyperbolicSkewSubmodule :=
  LinearEquiv.ofBijective blockOperatorLinearSubmodule
    ⟨blockOperatorLinearSubmodule_injective,
      blockOperatorLinearSubmodule_surjective⟩

theorem hyperbolicSkewSubmodule_finrank :
    Module.finrank ℝ hyperbolicSkewSubmodule = 45 := by
  calc
    Module.finrank ℝ hyperbolicSkewSubmodule = Module.finrank ℝ BlockData :=
      (LinearEquiv.finrank_eq blockOperatorLinearSubmoduleEquiv).symm
    _ = 45 := blockData_finrank

/-! ## Independent abstract TKK bracket and its concrete orthogonal realization -/

theorem hyperbolicSkew_bracket_mem
    (A B : hyperbolicSkewSubmodule) :
    hyperbolicSkewPredicate ⁅A.1, B.1⁆ := by
  intro z w
  have hA z w := A.2 z w
  have hB z w := B.2 z w
  have hAz := A.2 (B.1 z) w
  have hAw := A.2 z (B.1 w)
  have hBz := B.2 (A.1 z) w
  have hBw := B.2 z (A.1 w)
  change hyperbolicBeta ((A.1 * B.1 - B.1 * A.1) z) w +
      hyperbolicBeta z ((A.1 * B.1 - B.1 * A.1) w) = 0
  change hyperbolicBeta (A.1 (B.1 z) - B.1 (A.1 z)) w +
      hyperbolicBeta z (A.1 (B.1 w) - B.1 (A.1 w)) = 0
  have hneg_left (x y : Carrier) :
      hyperbolicBeta (-x) y = -hyperbolicBeta x y := by
    simpa using hyperbolicBeta_smul_left (-1) x y
  have hneg_right (x y : Carrier) :
      hyperbolicBeta x (-y) = -hyperbolicBeta x y := by
    simpa using hyperbolicBeta_smul_right (-1) x y
  rw [sub_eq_add_neg, sub_eq_add_neg,
    hyperbolicBeta_add_left, hyperbolicBeta_add_right,
    hneg_left, hneg_right]
  linear_combination hAz - hBw + hAw - hBz

noncomputable def hyperbolicSkewLieSubalgebra :
    LieSubalgebra ℝ (Module.End ℝ Carrier) :=
  { hyperbolicSkewSubmodule with
    lie_mem' := by
      intro A B hA hB
      exact hyperbolicSkew_bracket_mem ⟨A, hA⟩ ⟨B, hB⟩ }

noncomputable def hyperbolicSkewSubalgebraEquiv :
    hyperbolicSkewSubmodule ≃ₗ[ℝ]
      hyperbolicSkewLieSubalgebra :=
  { toFun := fun A => ⟨A.1, A.2⟩
    invFun := fun A => ⟨A.1, A.2⟩
    left_inv := by intro A; rfl
    right_inv := by intro A; rfl
    map_add' := by intro A B; rfl
    map_smul' := by intro r A; rfl }

def hyperbolicSkewBracket
    (A B : hyperbolicSkewSubmodule) : hyperbolicSkewSubmodule :=
  ⟨⁅A.1, B.1⁆, hyperbolicSkew_bracket_mem A B⟩

theorem hyperbolicSkew_smul_mem
    (r : ℝ) (A : hyperbolicSkewSubmodule) :
    hyperbolicSkewPredicate (r • A.1) := by
  intro z w
  change hyperbolicBeta ((r • A.1) z) w +
      hyperbolicBeta z ((r • A.1) w) = 0
  rw [LinearMap.smul_apply, LinearMap.smul_apply,
    hyperbolicBeta_smul_left, hyperbolicBeta_smul_right]
  linear_combination r * A.2 z w

noncomputable instance : LieRing hyperbolicSkewSubmodule where
  bracket := hyperbolicSkewBracket
  add_lie := by
    intro A B C
    apply Subtype.ext
    change ⁅A.1 + B.1, C.1⁆ = ⁅A.1, C.1⁆ + ⁅B.1, C.1⁆
    exact add_lie A.1 B.1 C.1
  lie_add := by
    intro A B C
    apply Subtype.ext
    change ⁅A.1, B.1 + C.1⁆ = ⁅A.1, B.1⁆ + ⁅A.1, C.1⁆
    exact lie_add A.1 B.1 C.1
  lie_self := by
    intro A
    apply Subtype.ext
    exact lie_self A.1
  leibniz_lie := by
    intro A B C
    apply Subtype.ext
    change ⁅A.1, ⁅B.1, C.1⁆⁆ =
      ⁅⁅A.1, B.1⁆, C.1⁆ + ⁅B.1, ⁅A.1, C.1⁆⁆
    exact leibniz_lie A.1 B.1 C.1

noncomputable instance : LieAlgebra ℝ hyperbolicSkewSubmodule where
  lie_smul := by
    intro r A B
    apply Subtype.ext
    change ⁅A.1, r • B.1⁆ = r • ⁅A.1, B.1⁆
    change A.1 * (r • B.1) - (r • B.1) * A.1 =
      r • (A.1 * B.1 - B.1 * A.1)
    simp [sub_eq_add_neg, mul_smul, smul_mul_assoc]

noncomputable def hyperbolicSkewSubalgebraLieEquiv :
    hyperbolicSkewSubmodule ≃ₗ⁅ℝ⁆ hyperbolicSkewLieSubalgebra := by
  refine LieEquiv.mk
    (LieHom.mk hyperbolicSkewSubalgebraEquiv ?_)
    hyperbolicSkewSubalgebraEquiv.symm ?_ ?_
  · intro A B
    apply Subtype.ext
    rfl
  · intro A
    exact hyperbolicSkewSubalgebraEquiv.left_inv A
  · intro A
    exact hyperbolicSkewSubalgebraEquiv.right_inv A

abbrev AbstractTKKCarrier := BlockData

noncomputable def abstractTKKBracket (d e : AbstractTKKCarrier) : AbstractTKKCarrier :=
  (blockOperatorLinearSubmoduleEquiv.symm
    (hyperbolicSkewBracket
      (blockOperatorLinearSubmoduleEquiv d)
      (blockOperatorLinearSubmoduleEquiv e)))

theorem abstractTKKBracket_equiv (d e : AbstractTKKCarrier) :
    blockOperatorLinearSubmoduleEquiv (abstractTKKBracket d e) =
      hyperbolicSkewBracket
        (blockOperatorLinearSubmoduleEquiv d)
        (blockOperatorLinearSubmoduleEquiv e) := by
  simp [abstractTKKBracket]

theorem abstractTKKBracket_skew (d e : AbstractTKKCarrier) :
    abstractTKKBracket d e = -abstractTKKBracket e d := by
  apply blockOperatorLinearSubmoduleEquiv.injective
  rw [abstractTKKBracket_equiv, map_neg, abstractTKKBracket_equiv]
  apply Subtype.ext
  simp only [hyperbolicSkewBracket, Subtype.coe_mk]
  exact (lie_skew _ _).symm

theorem abstractTKKBracket_add_left
    (d e f : AbstractTKKCarrier) :
    abstractTKKBracket (d + e) f =
      abstractTKKBracket d f + abstractTKKBracket e f := by
  apply blockOperatorLinearSubmoduleEquiv.injective
  simp only [abstractTKKBracket_equiv, map_add]
  apply Subtype.ext
  simp only [hyperbolicSkewBracket, Subtype.coe_mk]
  change ⁅(blockOperatorLinearSubmoduleEquiv d).1 +
      (blockOperatorLinearSubmoduleEquiv e).1,
      (blockOperatorLinearSubmoduleEquiv f).1⁆ =
    ⁅(blockOperatorLinearSubmoduleEquiv d).1,
      (blockOperatorLinearSubmoduleEquiv f).1⁆ +
    ⁅(blockOperatorLinearSubmoduleEquiv e).1,
      (blockOperatorLinearSubmoduleEquiv f).1⁆
  simpa only using
    (add_lie (blockOperatorLinearSubmoduleEquiv d).1
      (blockOperatorLinearSubmoduleEquiv e).1
      (blockOperatorLinearSubmoduleEquiv f).1)

theorem abstractTKKBracket_add_right
    (d e f : AbstractTKKCarrier) :
    abstractTKKBracket d (e + f) =
      abstractTKKBracket d e + abstractTKKBracket d f := by
  apply blockOperatorLinearSubmoduleEquiv.injective
  simp only [abstractTKKBracket_equiv, map_add]
  apply Subtype.ext
  simp only [hyperbolicSkewBracket, Subtype.coe_mk]
  change ⁅(blockOperatorLinearSubmoduleEquiv d).1,
      (blockOperatorLinearSubmoduleEquiv e).1 +
        (blockOperatorLinearSubmoduleEquiv f).1⁆ =
    ⁅(blockOperatorLinearSubmoduleEquiv d).1,
      (blockOperatorLinearSubmoduleEquiv e).1⁆ +
      ⁅(blockOperatorLinearSubmoduleEquiv d).1,
        (blockOperatorLinearSubmoduleEquiv f).1⁆
  simpa only using
    (lie_add (blockOperatorLinearSubmoduleEquiv d).1
      (blockOperatorLinearSubmoduleEquiv e).1
      (blockOperatorLinearSubmoduleEquiv f).1)

theorem abstractTKKBracket_smul_left
    (r : ℝ) (d e : AbstractTKKCarrier) :
    abstractTKKBracket (r • d) e = r • abstractTKKBracket d e := by
  apply blockOperatorLinearSubmoduleEquiv.injective
  simp only [abstractTKKBracket_equiv, map_smul]
  apply Subtype.ext
  simp only [hyperbolicSkewBracket, Subtype.coe_mk]
  change ⁅r • (blockOperatorLinearSubmoduleEquiv d).1,
      (blockOperatorLinearSubmoduleEquiv e).1⁆ =
    r • ⁅(blockOperatorLinearSubmoduleEquiv d).1,
      (blockOperatorLinearSubmoduleEquiv e).1⁆
  simpa only using
    (smul_lie r (blockOperatorLinearSubmoduleEquiv d).1
      (blockOperatorLinearSubmoduleEquiv e).1)

theorem abstractTKKBracket_smul_right
    (r : ℝ) (d e : AbstractTKKCarrier) :
    abstractTKKBracket d (r • e) = r • abstractTKKBracket d e := by
  apply blockOperatorLinearSubmoduleEquiv.injective
  simp only [abstractTKKBracket_equiv, map_smul]
  apply Subtype.ext
  simp only [hyperbolicSkewBracket, Subtype.coe_mk]
  change ⁅(blockOperatorLinearSubmoduleEquiv d).1,
      r • (blockOperatorLinearSubmoduleEquiv e).1⁆ =
    r • ⁅(blockOperatorLinearSubmoduleEquiv d).1,
      (blockOperatorLinearSubmoduleEquiv e).1⁆
  exact congrArg Subtype.val
    (LieAlgebra.lie_smul r
      (blockOperatorLinearSubmoduleEquiv d)
      (blockOperatorLinearSubmoduleEquiv e))

theorem abstractTKKBracket_jacobi
    (d e f : AbstractTKKCarrier) :
    abstractTKKBracket d (abstractTKKBracket e f) +
        abstractTKKBracket e (abstractTKKBracket f d) +
        abstractTKKBracket f (abstractTKKBracket d e) = 0 := by
  apply blockOperatorLinearSubmoduleEquiv.injective
  simp only [abstractTKKBracket_equiv, map_add, map_zero]
  apply Subtype.ext
  simp only [hyperbolicSkewBracket, Subtype.coe_mk]
  exact lie_jacobi _ _ _

noncomputable instance : LieRing AbstractTKKCarrier where
  bracket := abstractTKKBracket
  add_lie := abstractTKKBracket_add_left
  lie_add := by
    intro d e f
    exact abstractTKKBracket_add_right d e f
  lie_self := by
    intro d
    apply blockOperatorLinearSubmoduleEquiv.injective
    rw [abstractTKKBracket_equiv]
    apply Subtype.ext
    simpa [hyperbolicSkewBracket] using
      (lie_self (blockOperatorLinearSubmoduleEquiv d))
  leibniz_lie := by
    intro d e f
    apply blockOperatorLinearSubmoduleEquiv.injective
    simp only [abstractTKKBracket_equiv, map_add, map_zero]
    apply Subtype.ext
    simp only [hyperbolicSkewBracket, Subtype.coe_mk]
    exact leibniz_lie _ _ _

noncomputable instance : LieAlgebra ℝ AbstractTKKCarrier where
  lie_smul := abstractTKKBracket_smul_right

noncomputable def abstractTKKLieEquiv :
    AbstractTKKCarrier ≃ₗ⁅ℝ⁆ hyperbolicSkewSubmodule := by
  refine LieEquiv.mk
    (LieHom.mk blockOperatorLinearSubmodule ?_)
    blockOperatorLinearSubmoduleEquiv.symm ?_ ?_
  · intro d e
    exact abstractTKKBracket_equiv d e
  · intro d
    exact blockOperatorLinearSubmoduleEquiv.left_inv d
  · intro d
    exact blockOperatorLinearSubmoduleEquiv.right_inv d

theorem abstractTKKLieEquiv_map_lie (d e : AbstractTKKCarrier) :
    abstractTKKLieEquiv ⁅d, e⁆ =
      ⁅abstractTKKLieEquiv d, abstractTKKLieEquiv e⁆ := by
  exact abstractTKKLieEquiv.map_lie d e

theorem abstractTKKLieEquiv_finrank :
    Module.finrank ℝ AbstractTKKCarrier =
      Module.finrank ℝ hyperbolicSkewSubmodule := by
  exact abstractTKKLieEquiv.toLinearEquiv.finrank_eq

noncomputable def abstractTKKToNativeOrthogonal :
    AbstractTKKCarrier ≃ₗ⁅ℝ⁆ hyperbolicSkewLieSubalgebra :=
  abstractTKKLieEquiv.trans hyperbolicSkewSubalgebraLieEquiv

theorem abstractTKKToNativeOrthogonal_map_lie
    (d e : AbstractTKKCarrier) :
    abstractTKKToNativeOrthogonal ⁅d, e⁆ =
      ⁅abstractTKKToNativeOrthogonal d,
        abstractTKKToNativeOrthogonal e⁆ := by
  exact abstractTKKToNativeOrthogonal.map_lie d e

noncomputable def abstractTKKLieSocket :
    InfoGeometry.OperatorAlgebra.LieSocket AbstractTKKCarrier where
  bracket := abstractTKKBracket
  bracket_skew := abstractTKKBracket_skew
  bracket_add_left := abstractTKKBracket_add_left
  bracket_smul_left := abstractTKKBracket_smul_left
  jacobi := abstractTKKBracket_jacobi

theorem abstractTKK_to_hyperbolic_bracket
    (d e : AbstractTKKCarrier) :
    blockOperatorLinearSubmoduleEquiv
        (abstractTKKBracket d e) =
      hyperbolicSkewBracket
        (blockOperatorLinearSubmoduleEquiv d)
        (blockOperatorLinearSubmoduleEquiv e) := by
  exact abstractTKKBracket_equiv d e

theorem abstractTKK_to_hyperbolic_bijective :
    Function.Bijective blockOperatorLinearSubmoduleEquiv :=
  blockOperatorLinearSubmoduleEquiv.bijective

theorem abstractTKK_eq_of_block_val_eq {d e : AbstractTKKCarrier}
    (h : ((blockOperatorLinearSubmoduleEquiv d : hyperbolicSkewSubmodule) :
      Module.End ℝ Carrier) =
      ((blockOperatorLinearSubmoduleEquiv e : hyperbolicSkewSubmodule) :
        Module.End ℝ Carrier)) :
    d = e := by
  apply blockOperatorLinearSubmoduleEquiv.injective
  exact Subtype.ext h

theorem abstractTKK_finrank :
    Module.finrank ℝ AbstractTKKCarrier = 45 :=
  blockData_finrank

end InfoGeometry.Canonical.SplitOctonionTKK55
