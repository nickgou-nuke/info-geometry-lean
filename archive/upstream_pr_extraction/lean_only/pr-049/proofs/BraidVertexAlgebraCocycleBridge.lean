import Mathlib
import proofs.VertexAlgebraBraidingCocycle
import proofs.BraidInductiveColimitCategory

noncomputable section

namespace BraidVertexAlgebraCocycleBridge

open VertexAlgebraBraidingCocycle
open VertexAlgebraBraidingCocycle.EdgeSystem
open BraidInductiveColimitComplement

-- Braid-oriented finite/infinite dictionary for the cocycle/entropy model.
-- `finiteToInfinite` is the stage-by-stage embedding `Fin n ↪ ℕ`.

/-- Pull back an infinite cocycle to a finite generator stage. -/
def inducedFiniteSystem (n : ℕ) (S : EdgeSystem ℕ) : EdgeSystem (FiniteBraidGenerators n) :=
  { weight := fun i j => S.weight (finiteToInfinite i) (finiteToInfinite j)
    weight_pos := by
      intro i j
      exact S.weight_pos (finiteToInfinite i) (finiteToInfinite j) }

/-- Transport a finite cycle to the infinite-generator boundary. -/
def transportCycle (n : ℕ) (C : SpinNetCycle (FiniteBraidGenerators n)) :
    SpinNetCycle ℕ :=
  { start := finiteToInfinite C.start
    interior := C.interior.map finiteToInfinite }

/-- Transport of open walk sums along `finiteToInfinite`. -/
theorem cycleWalk_transport (n : ℕ) (S : EdgeSystem ℕ)
    (start : FiniteBraidGenerators n) :
    ∀ (cur : FiniteBraidGenerators n), ∀ rest : List (FiniteBraidGenerators n),
      (inducedFiniteSystem n S).cycleWalk start cur rest =
        S.cycleWalk (finiteToInfinite start) (finiteToInfinite cur)
          (rest.map finiteToInfinite) := by
  intro cur rest
  induction rest generalizing cur with
  | nil =>
      simp [EdgeSystem.cycleWalk, inducedFiniteSystem, logRatio]
  | cons b rest ih =>
      have hlog :
          (inducedFiniteSystem n S).logRatio cur b =
            S.logRatio (finiteToInfinite cur) (finiteToInfinite b) := by
        simp [inducedFiniteSystem, logRatio]
      calc
        (inducedFiniteSystem n S).cycleWalk start cur (b :: rest)
            = (inducedFiniteSystem n S).logRatio cur b +
                (inducedFiniteSystem n S).cycleWalk start b rest := by
                simp [EdgeSystem.cycleWalk]
        _ = S.logRatio (finiteToInfinite cur) (finiteToInfinite b) +
              S.cycleWalk (finiteToInfinite start) (finiteToInfinite b)
                (List.map finiteToInfinite rest) := by
              rw [hlog, ih (cur := b)]
        _ = S.cycleWalk (finiteToInfinite start) (finiteToInfinite cur)
                (List.map finiteToInfinite (b :: rest)) := by
              simp [EdgeSystem.cycleWalk]

/-- Compatibility of finite-to-infinite map with closed-cycle affinity. -/
theorem cycleAffinity_transport (n : ℕ) (S : EdgeSystem ℕ)
    (C : SpinNetCycle (FiniteBraidGenerators n)) :
    cycleAffinity (inducedFiniteSystem n S) C =
      cycleAffinity S (transportCycle n C) := by
  rcases C with ⟨start, interior⟩
  cases interior with
  | nil =>
      simp [cycleAffinity, transportCycle]
  | cons a as =>
      have hlog :
          (inducedFiniteSystem n S).logRatio start a =
            S.logRatio (finiteToInfinite start) (finiteToInfinite a) := by
        simp [inducedFiniteSystem, logRatio]
      have hwalk :
          (inducedFiniteSystem n S).cycleWalk start a as =
            S.cycleWalk (finiteToInfinite start) (finiteToInfinite a) (as.map finiteToInfinite) := by
        simpa using (cycleWalk_transport (n := n) (S := S) (start := start) (cur := a) as)
      simp [cycleAffinity, transportCycle]
      rw [hlog, hwalk]

/-- A three-step local braid-index cycle on `ℕ` (triangle on consecutive indices). -/
def braidLocalCycle (i : ℕ) : SpinNetCycle ℕ :=
  { start := i
    interior := [i + 1, i + 2] }

/-- Finite-stage version of the local braid-index cycle (requires room). -/
def finiteBraidLocalCycle
    (n : ℕ) (i : Fin n) (h : i.1 + 2 < n) : SpinNetCycle (FiniteBraidGenerators n) := by
  have h1 : i.1 + 1 < n := by omega
  exact { start := i
          interior := [
            ⟨i.1 + 1, h1⟩,
            ⟨i.1 + 2, h⟩
          ] }

/-- If all local braid-index cycles vanish in the infinite system,
corresponding pulled-back finite cycles also vanish. -/
theorem finite_local_cycle_zero_from_infinite_zero
    (S : EdgeSystem ℕ) (hlocal : ∀ i : ℕ, cycleAffinity S (braidLocalCycle i) = 0)
    (n : ℕ) (i : Fin n) (h : i.1 + 2 < n) :
    cycleAffinity (inducedFiniteSystem n S) (finiteBraidLocalCycle n i h) = 0 := by
  rw [cycleAffinity_transport (n := n) (S := S) (C := finiteBraidLocalCycle n i h)]
  have htr :
      transportCycle n (finiteBraidLocalCycle n i h) =
        braidLocalCycle (finiteToInfinite i) := by
    rfl
  simpa [htr] using hlocal (i := finiteToInfinite i)

/-- Exactness restricts to each finite braid-generator stage along
`finiteToInfinite`. -/
theorem induced_finite_exact
    (n : ℕ) (S : EdgeSystem ℕ) (potential : ℕ → ℝ)
    (hExact : IsExact S potential) :
    IsExact (inducedFiniteSystem n S) (fun i => potential (finiteToInfinite i)) := by
  intro i j
  simpa [IsExact, inducedFiniteSystem, logRatio] using
    hExact (finiteToInfinite i) (finiteToInfinite j)

/-- A finite-stage nonzero closed cycle is blocked by induced exactness. -/
theorem finite_no_broken_from_global_detailed_balance
    (n : ℕ)
    (S : EdgeSystem ℕ)
    (potential : ℕ → ℝ)
    (hExact : IsExact S potential)
    (C : SpinNetCycle (FiniteBraidGenerators n))
    (hC_nonzero :
      cycleEntropyProduction (inducedFiniteSystem n S) C ≠ 0) : False := by
  apply no_broken_from_detailed_balance
    (inducedFiniteSystem n S)
    (fun i => potential (finiteToInfinite i))
    (induced_finite_exact n S potential hExact)
    C
    hC_nonzero

end BraidVertexAlgebraCocycleBridge

end noncomputable section
