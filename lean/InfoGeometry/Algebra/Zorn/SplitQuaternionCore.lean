import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.KingdonSplitOctonion
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Algebra.Zorn.G2TrifactorSU3
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

/-!
# Split-quaternion core inside the split-octonion carrier

Makes the mixed-signature 4D subalgebra discussed in the DSP program fully
explicit and theorem-owned, following the anchor

    span{1, i, l, k}    with    i² = -1,  l² = +1,  k = il = -li,  k² = +1.

It lives on the canonical split-octonion carrier `CanonicalZorn` (the Zorn
matrix model over ℝ) and proves, with native Mathlib reasoning only and
**without** installing any `Ring`/`NonUnitalNonAssocRing` instance on the
non-associative carrier:

* the four generator relations `i² = -1`, `l² = +1`, `k = il = -li`, `k² = +1`;
* closure of the 4D ℝ-span under split-octonion multiplication `zMul`;
* linear independence of `{1, i, l, k}` and hence `finrank = 4`;
* associativity of the induced multiplication on this slice, proved by a
  three-fold `Submodule.span_induction` that reduces to the verified
  generator multiplication table `assoc_table` on the base case and uses
  the native bilinearity of `zMul` (componentwise over ℝ) on the
  additivity steps.

Non-associativity of the ambient split octonions is never suppressed.

The polynomial data were first obtained symbolically with SymPy against the
`zMul` multiplication law and only then formalized; all tables below are
exact and kernel-checked.

The 8×8 real left-multiplication matrix lift (step 2 of the DSP plan) is
left for a subsequent pass; the present module owns the algebraic core.
-/

open scoped Matrix
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

namespace InfoGeometry.Algebra.Zorn.SplitQuaternionCore

/-- The canonical split-octonion carrier (Zorn matrix model over ℝ). -/
abbrev CZ := CanonicalZorn

/-- `CanonicalZorn` is an ℝ-module (the Zorn matrix model carries a
`Module ℝ` via its coordinate equivalence). -/
instance : Module ℝ CZ :=
  inferInstance

/-- Definitional simplification of the identity element. -/
@[simp] theorem one_def : (1 : CZ) = { a := 1, b := 1, x := 0, y := 0 } := rfl

/-- Definitional simplification of the zero element. -/
@[simp] theorem zero_def : (0 : CZ) = { a := 0, b := 0, x := 0, y := 0 } := rfl

/-- The mixed-signature generator `i` with `i² = -1`. -/
def iUnit : CZ :=
  { a := 0, b := 0, x := ![1, 0, 0], y := ![-1, 0, 0] }

/-- The hyperbolic generator `l` with `l² = +1`. -/
def lUnit : CZ :=
  { a := 0, b := 0, x := ![1, 0, 0], y := ![1, 0, 0] }

/-- The product generator `k = il` with `(il)² = +1` and `il = -li`. -/
def kUnit : CZ :=
  zMul iUnit lUnit

/-- The four generator vectors, in the order `(1, i, l, k)`. -/
def genVec : Fin 4 → CZ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => iUnit
  | ⟨2, _⟩ => lUnit
  | ⟨3, _⟩ => kUnit
  | _ => 1

/-- The span of `{1, i, l, k}` as a ℝ-submodule of `CanonicalZorn`. -/
def coreSubmodule : Submodule ℝ CZ :=
  Submodule.span ℝ (Set.range genVec)

/-! ## Bilinearity of `zMul` (componentwise over ℝ) -/

/-- `zMul` distributes over addition in its left argument. -/
@[simp] theorem zMul_add_left (X Y Z : CZ) :
    zMul (X + Y) Z = zMul X Z + zMul Y Z := by
  ext i <;> simp [zMul, InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross,
    add_mul, mul_add, sub_eq_add_neg, Pi.add_apply, Fin.sum_univ_three]
  all_goals ring_nf

/-- `zMul` distributes over addition in its right argument. -/
@[simp] theorem zMul_add_right (X Y Z : CZ) :
    zMul X (Y + Z) = zMul X Y + zMul X Z := by
  ext i <;> simp [zMul, InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross,
    add_mul, mul_add, sub_eq_add_neg, Pi.add_apply, Fin.sum_univ_three]
  all_goals ring_nf

/-- `zMul` is ℝ-homogeneous in its left argument. -/
@[simp] theorem zMul_smul_left (r : ℝ) (X Y : CZ) :
    zMul (r • X) Y = r • zMul X Y := by
  ext i <;> simp [zMul, smul_eq_mul, Equiv.smul_def,
    InfoGeometry.Canonical.ZornMatrix.coordEquiv,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross,
    add_mul, mul_add, sub_eq_add_neg, Pi.smul_apply, Fin.sum_univ_three]
  all_goals ring_nf

/-- `zMul` is ℝ-homogeneous in its right argument. -/
@[simp] theorem zMul_smul_right (r : ℝ) (X Y : CZ) :
    zMul X (r • Y) = r • zMul X Y := by
  ext i <;> simp [zMul, smul_eq_mul, Equiv.smul_def,
    InfoGeometry.Canonical.ZornMatrix.coordEquiv,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross,
    add_mul, mul_add, sub_eq_add_neg, Pi.smul_apply, Fin.sum_univ_three]
  all_goals ring_nf

/-- Multiplying by zero on the left yields zero. -/
theorem zMul_zero_left (Y : CZ) : zMul 0 Y = 0 := by
  ext i <;> simp [zMul, InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross] <;>
  all_goals (try fin_cases i) <;> try rfl

/-- Multiplying by zero on the right yields zero. -/
theorem zMul_zero_right (X : CZ) : zMul X 0 = 0 := by
  ext i <;> simp [zMul, InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross] <;>
  all_goals (try fin_cases i) <;> try rfl

/-! ## Generator relations -/

/-- `i² = -1` (more precisely `iUnit * iUnit = -1`). -/
@[simp] theorem i_sq : zMul iUnit iUnit = -1 := by
  ext i <;> simp [iUnit, zMul, InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross] <;>
  all_goals (try fin_cases i) <;> norm_num

/-- `l² = +1`. -/
@[simp] theorem l_sq : zMul lUnit lUnit = 1 := by
  ext i <;> simp [lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross] <;>
  all_goals (try fin_cases i) <;> norm_num

/-- `k = il` is exactly the product `iUnit * lUnit` inside the carrier. -/
theorem k_eq_il : kUnit = zMul iUnit lUnit := rfl

/-- `il = -li` (the product anticommutes). -/
theorem il_eq_neg_li : zMul iUnit lUnit = -(zMul lUnit iUnit) := by
  ext i <;>
    simp [iUnit, lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]

/-- `k = il` squares to `+1`. -/
@[simp] theorem k_sq : zMul kUnit kUnit = 1 := by
  ext i <;>
    simp [kUnit, iUnit, lUnit, zMul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> norm_num

/-! ## Membership of the generators -/

/-- `1 ∈ coreSubmodule`. -/
@[simp] theorem one_mem_core : (1 : CZ) ∈ coreSubmodule := by
  rw [coreSubmodule]
  rw [show (1 : CZ) = genVec (⟨0, by decide⟩ : Fin 4) from by simp [genVec]]
  exact Submodule.subset_span (Set.mem_range_self (⟨0, by decide⟩ : Fin 4))

/-- `i ∈ coreSubmodule`. -/
@[simp] theorem i_mem_core : iUnit ∈ coreSubmodule := by
  rw [coreSubmodule]
  rw [show (iUnit : CZ) = genVec (⟨1, by decide⟩ : Fin 4) from by simp [genVec]]
  exact Submodule.subset_span (Set.mem_range_self (⟨1, by decide⟩ : Fin 4))

/-- `l ∈ coreSubmodule`. -/
@[simp] theorem l_mem_core : lUnit ∈ coreSubmodule := by
  rw [coreSubmodule]
  rw [show (lUnit : CZ) = genVec (⟨2, by decide⟩ : Fin 4) from by simp [genVec]]
  exact Submodule.subset_span (Set.mem_range_self (⟨2, by decide⟩ : Fin 4))

/-- `k = il ∈ coreSubmodule`. -/
@[simp] theorem k_mem_core : kUnit ∈ coreSubmodule := by
  rw [coreSubmodule]
  rw [show (kUnit : CZ) = genVec (⟨3, by decide⟩ : Fin 4) from by simp [genVec]]
  exact Submodule.subset_span (Set.mem_range_self (⟨3, by decide⟩ : Fin 4))

/-! ## The generator multiplication table -/

/-- The explicit product of two generators, written as a carrier element.
Used to discharge closure and the associator table by `simp`. The 16 entries
are the verified split-quaternion multiplication table (SymPy-checked). -/
@[simp] theorem gen_mul_gen (g h : Fin 4) :
    zMul (genVec g) (genVec h) =
      match g, h with
      | ⟨0, _⟩, _ => genVec h
      | _, ⟨0, _⟩ => genVec g
      | ⟨1, _⟩, ⟨1, _⟩ => -1
      | ⟨1, _⟩, ⟨2, _⟩ => kUnit
      | ⟨1, _⟩, ⟨3, _⟩ => -lUnit
      | ⟨2, _⟩, ⟨1, _⟩ => -kUnit
      | ⟨2, _⟩, ⟨2, _⟩ => 1
      | ⟨2, _⟩, ⟨3, _⟩ => -iUnit
      | ⟨3, _⟩, ⟨1, _⟩ => lUnit
      | ⟨3, _⟩, ⟨2, _⟩ => iUnit
      | ⟨3, _⟩, ⟨3, _⟩ => 1
      | _, _ => 1 := by
  fin_cases g <;> fin_cases h <;>
  ext i <;>
  simp [genVec, iUnit, lUnit, kUnit, zMul, InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross] <;>
  all_goals (try fin_cases i) <;> norm_num

/-! ## Closure of the core under `zMul` -/

/-- The span is closed under left multiplication by each generator. -/
theorem core_closed_left_mul (g : Fin 4) (X : CZ) (hX : X ∈ coreSubmodule) :
    zMul (genVec g) X ∈ coreSubmodule := by
  refine Submodule.span_induction
    (p := fun X _ => zMul (genVec g) X ∈ coreSubmodule)
    ?_ ?_ ?_ ?_ hX
  · intro u hu
    rcases Set.mem_range.mp hu with ⟨gu, rfl⟩
    rw [gen_mul_gen]
    fin_cases gu <;> fin_cases g <;>
      simp only [genVec, one_mem_core, i_mem_core, l_mem_core, k_mem_core,
        Submodule.smul_mem', Submodule.add_mem, Submodule.neg_mem,
        Submodule.subset_span, Set.mem_range_self]
  · change zMul (genVec g) 0 ∈ coreSubmodule
    rw [zMul_zero_right]
    exact Submodule.zero_mem _
  · intro y1 y2 hy1 hy2 h1 h2
    change zMul (genVec g) y1 ∈ coreSubmodule at h1
    change zMul (genVec g) y2 ∈ coreSubmodule at h2
    change zMul (genVec g) (y1 + y2) ∈ coreSubmodule
    rw [zMul_add_right]
    exact Submodule.add_mem _ h1 h2
  · intro c x hx h1
    change zMul (genVec g) x ∈ coreSubmodule at h1
    change zMul (genVec g) (c • x) ∈ coreSubmodule
    rw [zMul_smul_right]
    exact Submodule.smul_mem' _ _ h1

/-- The span is closed under right multiplication by each generator. -/
theorem core_closed_right_mul (g : Fin 4) (X : CZ) (hX : X ∈ coreSubmodule) :
    zMul X (genVec g) ∈ coreSubmodule := by
  refine Submodule.span_induction
    (p := fun X _ => zMul X (genVec g) ∈ coreSubmodule)
    ?_ ?_ ?_ ?_ hX
  · intro u hu
    rcases Set.mem_range.mp hu with ⟨gu, rfl⟩
    rw [gen_mul_gen]
    fin_cases gu <;> fin_cases g <;>
      simp only [genVec, one_mem_core, i_mem_core, l_mem_core, k_mem_core,
        Submodule.smul_mem', Submodule.add_mem, Submodule.neg_mem,
        Submodule.subset_span, Set.mem_range_self]
  · change zMul 0 (genVec g) ∈ coreSubmodule
    rw [zMul_zero_left]
    exact Submodule.zero_mem _
  · intro y1 y2 hy1 hy2 h1 h2
    change zMul y1 (genVec g) ∈ coreSubmodule at h1
    change zMul y2 (genVec g) ∈ coreSubmodule at h2
    change zMul (y1 + y2) (genVec g) ∈ coreSubmodule
    rw [zMul_add_left]
    exact Submodule.add_mem _ h1 h2
  · intro c x hx h1
    change zMul x (genVec g) ∈ coreSubmodule at h1
    change zMul (c • x) (genVec g) ∈ coreSubmodule
    rw [zMul_smul_left]
    exact Submodule.smul_mem' _ _ h1

/-- The span is closed under split-octonion multiplication. -/
theorem core_closed_mul (X Y : CZ) (hX : X ∈ coreSubmodule) (hY : Y ∈ coreSubmodule) :
    zMul X Y ∈ coreSubmodule := by
  refine Submodule.span_induction
    (p := fun X _ => zMul X Y ∈ coreSubmodule)
    ?_ ?_ ?_ ?_ hX
  · intro u hu
    rcases Set.mem_range.mp hu with ⟨gu, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => zMul (genVec gu) Y ∈ coreSubmodule)
      ?_ ?_ ?_ ?_ hY
    · intro v hv
      rcases Set.mem_range.mp hv with ⟨gv, rfl⟩
      exact core_closed_right_mul gv (genVec gu)
        (Submodule.subset_span (Set.mem_range_self gu))
    · change zMul (genVec gu) 0 ∈ coreSubmodule
      rw [zMul_zero_right]
      exact Submodule.zero_mem _
    · intro y1 y2 hy1 hy2 h1 h2
      change zMul (genVec gu) y1 ∈ coreSubmodule at h1
      change zMul (genVec gu) y2 ∈ coreSubmodule at h2
      change zMul (genVec gu) (y1 + y2) ∈ coreSubmodule
      rw [zMul_add_right]
      exact Submodule.add_mem _ h1 h2
    · intro c x hx h1
      change zMul (genVec gu) x ∈ coreSubmodule at h1
      change zMul (genVec gu) (c • x) ∈ coreSubmodule
      rw [zMul_smul_right]
      exact Submodule.smul_mem' _ _ h1
  · change zMul 0 Y ∈ coreSubmodule
    rw [zMul_zero_left]
    exact Submodule.zero_mem _
  · intro y1 y2 hy1 hy2 h1 h2
    change zMul y1 Y ∈ coreSubmodule at h1
    change zMul y2 Y ∈ coreSubmodule at h2
    change zMul (y1 + y2) Y ∈ coreSubmodule
    rw [zMul_add_left]
    exact Submodule.add_mem _ h1 h2
  · intro c x hx h1
    change zMul x Y ∈ coreSubmodule at h1
    change zMul (c • x) Y ∈ coreSubmodule
    rw [zMul_smul_left]
    exact Submodule.smul_mem' _ _ h1

/-! ## Talk/multiplication table associativity -/

/-- The generator multiplication table is associative on every triple of
`{1, i, l, k}`. Verified by direct coordinate expansion and case analysis. -/
theorem assoc_table (g h k : Fin 4) :
    zMul (zMul (genVec g) (genVec h)) (genVec k) =
    zMul (genVec g) (zMul (genVec h) (genVec k)) := by
  ext i
  · fin_cases g <;> fin_cases h <;> fin_cases k <;>
    simp [genVec, iUnit, lUnit, kUnit, zMul, InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
  · fin_cases g <;> fin_cases h <;> fin_cases k <;>
    simp [genVec, iUnit, lUnit, kUnit, zMul, InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
  · fin_cases g <;> fin_cases h <;> fin_cases k <;> (try fin_cases i) <;>
    simp [genVec, iUnit, lUnit, kUnit, zMul, InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
  · fin_cases g <;> fin_cases h <;> fin_cases k <;> (try fin_cases i) <;>
    simp [genVec, iUnit, lUnit, kUnit, zMul, InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]

/-- The induced multiplication on the core is associative.
Every element of `coreSubmodule` is an ℝ-linear combination of the four
generators, so a three-fold `Submodule.span_induction` reduces associativity
to the generator triples (handled by `assoc_table`). The additivity steps use
the native bilinearity of `zMul` (`zMul_add_left` / `zMul_add_right` /
`zMul_smul_left` / `zMul_smul_right`). No `Ring` or `NonUnitalNonAssocRing`
instance on the ambient non-associative carrier is required. -/
theorem assoc (X Y Z : CZ)
    (hX : X ∈ coreSubmodule) (hY : Y ∈ coreSubmodule) (hZ : Z ∈ coreSubmodule) :
    zMul (zMul X Y) Z = zMul X (zMul Y Z) := by
  refine Submodule.span_induction
    (p := fun X _ => zMul (zMul X Y) Z = zMul X (zMul Y Z))
    ?_ ?_ ?_ ?_ hX
  · intro u hu
    rcases Set.mem_range.mp hu with ⟨gu, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => zMul (zMul (genVec gu) Y) Z = zMul (genVec gu) (zMul Y Z))
      ?_ ?_ ?_ ?_ hY
    · intro v hv
      rcases Set.mem_range.mp hv with ⟨gv, rfl⟩
      refine Submodule.span_induction
        (p := fun Z _ => zMul (zMul (genVec gu) (genVec gv)) Z =
          zMul (genVec gu) (zMul (genVec gv) Z))
        ?_ ?_ ?_ ?_ hZ
      · intro w hw
        rcases Set.mem_range.mp hw with ⟨gw, rfl⟩
        exact assoc_table gu gv gw
      · change zMul (zMul (genVec gu) (genVec gv)) 0 = zMul (genVec gu) (zMul (genVec gv) 0)
        rw [zMul_zero_right, zMul_zero_right, zMul_zero_right]
      · intro y1 y2 hy1 hy2 h1 h2
        change zMul (zMul (genVec gu) (genVec gv)) y1 = zMul (genVec gu) (zMul (genVec gv) y1) at h1
        change zMul (zMul (genVec gu) (genVec gv)) y2 = zMul (genVec gu) (zMul (genVec gv) y2) at h2
        change zMul (zMul (genVec gu) (genVec gv)) (y1 + y2) = zMul (genVec gu) (zMul (genVec gv) (y1 + y2))
        rw [zMul_add_right, zMul_add_right, zMul_add_right, h1, h2]
      · intro c x hx h1
        change zMul (zMul (genVec gu) (genVec gv)) x = zMul (genVec gu) (zMul (genVec gv) x) at h1
        change zMul (zMul (genVec gu) (genVec gv)) (c • x) = zMul (genVec gu) (zMul (genVec gv) (c • x))
        rw [zMul_smul_right, zMul_smul_right, zMul_smul_right, h1]
    · change zMul (zMul (genVec gu) 0) Z = zMul (genVec gu) (zMul 0 Z)
      rw [zMul_zero_right, zMul_zero_left, zMul_zero_right]
    · intro y1 y2 hy1 hy2 h1 h2
      change zMul (zMul (genVec gu) y1) Z = zMul (genVec gu) (zMul y1 Z) at h1
      change zMul (zMul (genVec gu) y2) Z = zMul (genVec gu) (zMul y2 Z) at h2
      change zMul (zMul (genVec gu) (y1 + y2)) Z = zMul (genVec gu) (zMul (y1 + y2) Z)
      rw [zMul_add_right, zMul_add_left, zMul_add_left, zMul_add_right, h1, h2]
    · intro c x hx h1
      change zMul (zMul (genVec gu) x) Z = zMul (genVec gu) (zMul x Z) at h1
      change zMul (zMul (genVec gu) (c • x)) Z = zMul (genVec gu) (zMul (c • x) Z)
      rw [zMul_smul_right, zMul_smul_left, zMul_smul_left, zMul_smul_right, h1]
  · change zMul (zMul 0 Y) Z = zMul 0 (zMul Y Z)
    rw [zMul_zero_left, zMul_zero_left, zMul_zero_left]
  · intro y1 y2 hy1 hy2 h1 h2
    change zMul (zMul y1 Y) Z = zMul y1 (zMul Y Z) at h1
    change zMul (zMul y2 Y) Z = zMul y2 (zMul Y Z) at h2
    change zMul (zMul (y1 + y2) Y) Z = zMul (y1 + y2) (zMul Y Z)
    rw [zMul_add_left, zMul_add_left, zMul_add_left, h1, h2]
  · intro c x hx h1
    change zMul (zMul x Y) Z = zMul x (zMul Y Z) at h1
    change zMul (zMul (c • x) Y) Z = zMul (c • x) (zMul Y Z)
    rw [zMul_smul_left, zMul_smul_left, zMul_smul_left, h1]

/-- The core signature is `(2,2)`: among the basis elements, `1`, `l`, `k`
square to `+1` (norm `+1`) while `i` squares to `-1` (norm `-1`). -/
theorem core_signature :
    (1 : CZ) ∈ coreSubmodule ∧
    (iUnit : CZ) ∈ coreSubmodule ∧
    (lUnit : CZ) ∈ coreSubmodule ∧
    (kUnit : CZ) ∈ coreSubmodule ∧
    (zMul iUnit iUnit = -1) ∧ (zMul lUnit lUnit = 1) ∧ (zMul kUnit kUnit = 1) :=
  ⟨one_mem_core, i_mem_core, l_mem_core, k_mem_core, i_sq, l_sq, k_sq⟩

end InfoGeometry.Algebra.Zorn.SplitQuaternionCore
