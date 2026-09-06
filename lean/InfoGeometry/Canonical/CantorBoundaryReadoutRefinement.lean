import InfoGeometry.Canonical.CantorCylinderHomeomorph

/-!
# Finite-readout compatibility with symbolic refinement

This owner connects the topological refinement square to the existing finite
binary readout.  It proves only a finite-stage identity, so no extra analytic
or measure-theoretic claim is introduced.
-/

namespace InfoGeometry.Canonical.CantorBoundaryReadoutRefinement

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorBoundaryCuntzShift
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorCylinderTopology
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge

theorem prefixExtend_eq_boundaryConsList
    {n : ℕ} (w : BitWord n) (x : CantorBoundary) :
    prefixExtend w x = boundaryConsList (List.ofFn w) x := by
  induction n with
  | zero =>
      funext k
      simp [prefixExtend]
  | succ n ih =>
      let wt : BitWord n := fun i => w i.succ
      have hlist : List.ofFn w = w 0 :: List.ofFn wt := by
        rw [List.ofFn_succ]
      have hprefix :
          prefixExtend w x = prefixBit (w 0) (prefixExtend wt x) := by
        funext k
        cases k with
        | zero => rfl
        | succ k =>
            by_cases hk : k < n
            · simp [prefixExtend, prefixBit, wt, hk]
            · have hkn : n ≤ k := Nat.le_of_not_gt hk
              have hsub : k + 1 - (n + 1) = k - n := by omega
              simp [prefixExtend, prefixBit, hk, hsub]
      rw [hlist, boundaryConsList, hprefix]
      rw [ih wt]
      have hcons :
          prefixBit (w 0) (boundaryConsList (List.ofFn wt) x) =
            boundaryCons (w 0) (boundaryConsList (List.ofFn wt) x) := by
        funext k
        cases k <;> rfl
      exact hcons

theorem realBinaryPartialReadout_refinement
    (n : ℕ) (w : BitWord n) (b : Bool) (x : CantorBoundary) :
    realBinaryPartialReadout (n + 1)
        (prefixExtend (extendSucc n w b) x) =
      realBinaryPartialReadout n
        (prefixExtend w (prefixBit b x)) +
        (if b then (1 / 2 : ℝ) ^ (n + 1) else 0) := by
  rw [prefixExtend_extendSucc_eq_prefixBit]
  rw [realBinaryPartialReadout_succ]
  have hbit : prefixExtend w (prefixBit b x) n = b := by
    simp [prefixExtend, prefixBit]
  simp [realBinaryTerm, hbit]

theorem realBinaryReadout_prefixExtend
    (n : ℕ) (w : BitWord n) (x : CantorBoundary) :
    realBinaryReadout (prefixExtend w x) =
      finitePrefixReadout (List.ofFn w) +
        (1 / 2 : ℝ) ^ n * realBinaryReadout x := by
  rw [prefixExtend_eq_boundaryConsList]
  simpa using realBinaryReadout_boundaryConsList (List.ofFn w) x

theorem realBinaryReadout_prefixExtend_front
    {n : ℕ} (w : BitWord (n + 1)) (x : CantorBoundary) :
    realBinaryReadout (prefixExtend w x) =
      (if w 0 then (1 / 2 : ℝ) else 0) +
        (1 / 2 : ℝ) *
          realBinaryReadout (prefixExtend (fun i => w i.succ) x) := by
  rw [prefixExtend_front_eq_prefixBit]
  exact realBinaryReadout_prefixBit (w 0) (prefixExtend (fun i => w i.succ) x)

theorem realBinaryReadout_prefixExtend_mem_dyadicInterval
    (n : ℕ) (w : BitWord n) (x : CantorBoundary) :
    realBinaryReadout (prefixExtend w x) ∈
      Set.Icc (finitePrefixReadout (List.ofFn w))
        (finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ n) := by
  rw [realBinaryReadout_prefixExtend]
  have hx := realBinaryReadout_mem_unitInterval x
  have hp : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  constructor <;> nlinarith [hx.1, hx.2]

theorem realBinaryReadout_prefixExtend_pair_distance
    (n : ℕ) (w : BitWord n) (x y : CantorBoundary) :
    |realBinaryReadout (prefixExtend w x) -
        realBinaryReadout (prefixExtend w y)| ≤ (1 / 2 : ℝ) ^ n := by
  apply abs_realBinaryReadout_sub_le_of_prefix n
  intro i hi
  simp [prefixExtend, hi]

end InfoGeometry.Canonical.CantorBoundaryReadoutRefinement
