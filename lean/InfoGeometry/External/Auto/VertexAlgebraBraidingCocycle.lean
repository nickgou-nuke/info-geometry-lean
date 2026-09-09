import Mathlib.Tactic

/-!
# Vertex-algebra / braiding cocycle skeleton

This file gives a compact, theorem-honest combinatorial framework for the user's
picture:

- directed edges as cocycle data,
- Wilson/holonomy as a closed-cycle log-sum,
- `a_ij` ratios as entropies,
- detailed balance as potential-exactness,
- broken detailed balance as a nonzero closed-cycle affinity.

Analytic/physical refinements are intentionally left out unless represented by
explicit finite hypotheses.
-/

open scoped BigOperators

noncomputable section

namespace VertexAlgebraBraidingCocycle

/-- Directed edge system with positive transition weights `aij`. -/
structure EdgeSystem (V : Type*) where
  weight : V → V → ℝ
  weight_pos : ∀ i j, 0 < weight i j

namespace EdgeSystem

def logWeight (S : EdgeSystem V) (i j : V) : ℝ :=
  Real.log (S.weight i j)

def logRatio (S : EdgeSystem V) (i j : V) : ℝ :=
  Real.log (S.weight i j / S.weight j i)

variable {V : Type*}

/-- Skew-symmetry of the log-ratio cocycle (`log(a_ij/a_ji) = -log(a_ji/a_ij)`). -/
theorem logRatio_skew (S : EdgeSystem V) (i j : V) :
    logRatio S i j = - logRatio S j i := by
  have hij : S.weight i j ≠ 0 := ne_of_gt (S.weight_pos i j)
  have hji : S.weight j i ≠ 0 := ne_of_gt (S.weight_pos j i)
  dsimp [logRatio]
  rw [Real.log_div hij hji, Real.log_div hji hij]
  ring

/-- Closed walk on vertices: start plus intermediate vertices, implicitly
`start → v1 → ⋯ → vn → start`.
-/
structure SpinNetCycle (V : Type*) where
  start : V
  interior : List V

/-- Walk contribution from current vertex to finish a fixed start. -/
def cycleWalk (S : EdgeSystem V) (start cur : V) : List V → ℝ
  | [] => logRatio S cur start
  | v :: vs => logRatio S cur v + cycleWalk S start v vs

/-- Loop entropy/cocycle on a closed spin-net loop. -/
def cycleAffinity (S : EdgeSystem V) (C : SpinNetCycle V) : ℝ :=
  match C.interior with
  | [] => 0
  | v :: vs => logRatio S C.start v + cycleWalk S C.start v vs

/-- Cycle alias with the same content in a later-facing name. -/
def cycleEntropyProduction (S : EdgeSystem V) (C : SpinNetCycle V) : ℝ :=
  cycleAffinity S C

/-- Exactness notion for a given edge cocycle and vertex potential. -/
def IsExact (S : EdgeSystem V) (potential : V → ℝ) : Prop :=
  ∀ i j, logRatio S i j = potential j - potential i

/-- Recursive lemma: a walk with fixed start evaluates to a telescoping potential
    difference.
-/
theorem cycleWalk_eq_potential_diff
    (S : EdgeSystem V)
    (hpot : V → ℝ)
    (hratio : ∀ i j, logRatio S i j = hpot j - hpot i)
    (start cur : V) :
    ∀ rest : List V, cycleWalk S start cur rest = hpot start - hpot cur := by
  intro rest
  induction rest generalizing cur with
  | nil =>
      simp [cycleWalk, hratio]
  | cons v vs ih =>
      calc
        cycleWalk S start cur (v :: vs)
            = logRatio S cur v + cycleWalk S start v vs := by
                rfl
        _ = (hpot v - hpot cur) + (hpot start - hpot v) := by
              rw [hratio, ih]
        _ = hpot start - hpot cur := by ring

/-- Under detailed balance, all loops have zero Wilson/cocycle sum.

This is the finite, algebraic content: exactness (`hpot`) kills all cycle
affinities.
-/
theorem detailed_balance_implies_zero_cycle
    (S : EdgeSystem V)
    (potential : V → ℝ)
    (hratio : IsExact S potential)
    (C : SpinNetCycle V) : cycleEntropyProduction S C = 0 := by
  rcases C with ⟨start, interior⟩
  cases interior with
  | nil =>
      rfl
  | cons v vs =>
      simp [cycleEntropyProduction, cycleAffinity]
      have htel :=
        cycleWalk_eq_potential_diff S potential hratio start v vs
      have hfirst : logRatio S start v = potential v - potential start :=
        hratio start v
      rw [hfirst, htel]
      ring

/-- Zero loop affinity on all closed cycles yields exactness via a chosen basepoint.

Choosing a base vertex `b`, define `h x := logRatio S b x`; cycle
`b → i → j → b` gives
`logRatio b i + logRatio i j + logRatio j b = 0` and therefore
`logRatio i j = h j - h i`.
-/

theorem zero_cycle_affinity_implies_detailed_balance
    (S : EdgeSystem V) (b : V)
    (hzero : ∀ C : SpinNetCycle V, cycleAffinity S C = 0) :
    ∃ h : V → ℝ, IsExact S h := by
  refine ⟨fun x => logRatio S b x, ?_⟩
  intro i j
  have hbij : logRatio S b i + (logRatio S i j + logRatio S j b) = 0 := by
    simpa [cycleAffinity, cycleWalk] using hzero ⟨b, [i, j]⟩
  have hskew : logRatio S j b = -logRatio S b j := logRatio_skew S j b
  have hdiff : logRatio S i j = logRatio S b j - logRatio S b i := by
    linarith [hbij, hskew]
  simpa using hdiff

/-- If detailed balance holds for the same edge system, no nonzero broken
    closed-cycle affinity exists.
-/
theorem no_broken_from_detailed_balance
    (S : EdgeSystem V)
    (potential : V → ℝ)
    (hratio : IsExact S potential)
    (C : SpinNetCycle V)
    (hC_nonzero : cycleEntropyProduction S C ≠ 0) : False := by
  apply hC_nonzero
  exact detailed_balance_implies_zero_cycle S potential hratio C

/-- Exact edge cocycles have zero entropy production on every closed cycle. -/
theorem exact_implies_zero_cycle
    (S : EdgeSystem V)
    (potential : V → ℝ)
    (hratio : IsExact S potential)
    (C : SpinNetCycle V) : cycleEntropyProduction S C = 0 := by
  rcases C with ⟨start, interior⟩
  cases interior with
  | nil =>
      rfl
  | cons v vs =>
      simp [cycleEntropyProduction, cycleAffinity]
      have htel :=
        cycleWalk_eq_potential_diff S potential hratio start v vs
      have hfirst : logRatio S start v = potential v - potential start :=
        hratio start v
      rw [hfirst, htel]
      ring

end EdgeSystem

end VertexAlgebraBraidingCocycle

end noncomputable section
