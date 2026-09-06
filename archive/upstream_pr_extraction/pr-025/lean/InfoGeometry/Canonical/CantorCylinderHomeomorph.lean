import InfoGeometry.Canonical.CantorCylinderClopen
import InfoGeometry.Canonical.CantorBoundaryCuntzShiftTopology

/-!
# Homeomorphisms from finite-prefix cylinders to the Cantor boundary

Every finite prefix cylinder is a copy of the whole symbolic boundary.  The
forward map writes a finite word and then appends an arbitrary tail; the
inverse removes the first `n` coordinates.  This is a purely product-topology
statement and uses the existing `BitWord`/`prefixCylinder` owners.
-/

open Set TopologicalSpace

namespace InfoGeometry.Canonical.CantorCylinderTopology

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.StoneCantorMathlib
open InfoGeometry.Canonical.CantorBoundaryCuntzShift

def prefixExtend {n : ℕ} (w : BitWord n) (x : CantorStream) : CantorStream :=
  fun k => if h : k < n then w ⟨k, h⟩ else x (k - n)

def prefixTailN (n : ℕ) (y : CantorStream) : CantorStream :=
  fun k => y (k + n)

theorem prefixExtend_mem_prefixCylinder
    {n : ℕ} (w : BitWord n) (x : CantorStream) :
    prefixExtend w x ∈ prefixCylinder n w := by
  change boundaryPrefix n (prefixExtend w x) = w
  funext i
  simp [boundaryPrefix, prefixExtend, i.2]

theorem continuous_prefixExtend {n : ℕ} (w : BitWord n) :
    Continuous (prefixExtend w) := by
  apply continuous_pi
  intro k
  by_cases hk : k < n
  · simpa [prefixExtend, hk] using
      (continuous_const : Continuous (fun _ : CantorStream => w ⟨k, hk⟩))
  · simp [prefixExtend, hk]
    exact continuous_apply (k - n)

theorem continuous_prefixTailN (n : ℕ) :
    Continuous (prefixTailN n) := by
  apply continuous_pi
  intro k
  exact continuous_apply (k + n)

theorem prefixTailN_prefixExtend {n : ℕ} (w : BitWord n) (x : CantorStream) :
    prefixTailN n (prefixExtend w x) = x := by
  funext k
  simp [prefixTailN, prefixExtend, Nat.not_lt_of_ge (Nat.le_add_left n k)]

theorem prefixExtend_prefixTailN
    {n : ℕ} (w : BitWord n) {y : CantorStream}
    (hy : y ∈ prefixCylinder n w) :
    prefixExtend w (prefixTailN n y) = y := by
  change boundaryPrefix n y = w at hy
  funext k
  by_cases hk : k < n
  · have hkw := congrFun hy ⟨k, hk⟩
    simpa [prefixExtend, boundaryPrefix, hk] using hkw.symm
  · have hnk : n ≤ k := Nat.le_of_not_gt hk
    have hsub : k - n + n = k := Nat.sub_add_cancel hnk
    simp [prefixExtend, hk, prefixTailN, hsub]

theorem prefixExtend_extendSucc_eq_prefixBit
    (n : ℕ) (w : BitWord n) (b : Bool) (x : CantorStream) :
    prefixExtend (extendSucc n w b) x =
      prefixExtend w (prefixBit b x) := by
  funext k
  by_cases hk : k < n
  · simp [prefixExtend, extendSucc, hk, Nat.le_of_lt hk]
  · by_cases hkn : k = n
    · subst hkn
      simp [prefixExtend, extendSucc, prefixBit]
    · have hnk : n < k := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hk) (Ne.symm hkn)
      have hsucc : k - n = (k - (n + 1)) + 1 := by omega
      have hnk1 : ¬ k < n + 1 :=
        Nat.not_lt_of_ge (Nat.succ_le_iff.mpr hnk)
      simp [prefixExtend, hk, hnk1, hsucc, prefixBit]

theorem prefixExtend_front_eq_prefixBit
    {n : ℕ} (w : BitWord (n + 1)) (x : CantorStream) :
    prefixExtend w x =
      prefixBit (w 0) (prefixExtend (fun i => w i.succ) x) := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
      by_cases hk : k < n
      · simp [prefixExtend, prefixBit, hk]
      · have hkn : n ≤ k := Nat.le_of_not_gt hk
        have hsub : k + 1 - (n + 1) = k - n := by omega
        simp [prefixExtend, prefixBit, hk, hsub]

theorem range_prefixExtend_eq_prefixCylinder
    (n : ℕ) (w : BitWord n) :
    Set.range (prefixExtend w) = prefixCylinder n w := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact prefixExtend_mem_prefixCylinder w x
  · intro hy
    exact ⟨prefixTailN n y, prefixExtend_prefixTailN w hy⟩

theorem range_prefixExtend_refinement
    (n : ℕ) (w : BitWord n) :
    Set.range (prefixExtend w) =
      Set.range (prefixExtend (extendSucc n w false)) ∪
        Set.range (prefixExtend (extendSucc n w true)) := by
  rw [range_prefixExtend_eq_prefixCylinder,
    prefixCylinder_successor_union]
  rw [← range_prefixExtend_eq_prefixCylinder,
    ← range_prefixExtend_eq_prefixCylinder]

noncomputable def prefixCylinderHomeomorph (n : ℕ) (w : BitWord n) :
    CantorStream ≃ₜ prefixCylinder n w :=
  { toEquiv :=
      { toFun := fun x => ⟨prefixExtend w x, prefixExtend_mem_prefixCylinder w x⟩
        invFun := fun y => prefixTailN n y.1
        left_inv := prefixTailN_prefixExtend w
        right_inv := by
          intro y
          apply Subtype.ext
          exact prefixExtend_prefixTailN w y.2 }
    continuous_toFun :=
      (continuous_prefixExtend w).subtype_mk (fun x => prefixExtend_mem_prefixCylinder w x)
    continuous_invFun := continuous_prefixTailN n |>.comp continuous_subtype_val }

theorem prefixCylinderHomeomorph_apply
    (n : ℕ) (w : BitWord n) (x : CantorStream) :
    prefixCylinderHomeomorph n w x =
      ⟨prefixExtend w x, prefixExtend_mem_prefixCylinder w x⟩ :=
  rfl

end InfoGeometry.Canonical.CantorCylinderTopology
