import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Colimit.Module
import Mathlib.Tactic
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-!
# Primon Colimit Algebra

The finite, algebraic full-matrix tower used for the Primon/UHF colimit.

The stage indexed by `n` is the matrix algebra on `BitWord n`.  The bonding
map is the block-diagonal inclusion `M ↦ M ⊗ I₂`, written in the canonical
`BitWord (n + 1)` coordinates.  This file proves the ring-hom, injectivity,
and normalized-trace compatibility facts, then reuses the repository's
existing algebraic direct-limit owner.

This is an algebraic direct limit only.  No C*-completion, topology, or
uniqueness theorem for a completed tracial state is asserted here.
-/

noncomputable section

namespace InfoGeometry.Algebra.PrimonColimitAlgebra

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open Matrix

abbrev MatrixStage (n : ℕ) := Matrix (BitWord n) (BitWord n) ℝ

def matrixBondFun (n : ℕ) (M : MatrixStage n) : MatrixStage (n + 1) :=
  fun v w =>
    if v ⟨n, Nat.lt_succ_self n⟩ = w ⟨n, Nat.lt_succ_self n⟩ then
      M (prefixSucc n v) (prefixSucc n w)
    else
      0

/-- The UHF bond is block diagonal in the two Cantor branch coordinates. -/
theorem matrixBondFun_extendSucc (n : ℕ) (M : MatrixStage n)
    (u v : BitWord n) (b c : Bool) :
    matrixBondFun n M (extendSucc n u b) (extendSucc n v c) =
      if b = c then M u v else 0 := by
  cases b <;> cases c <;>
    simp [matrixBondFun, extendSucc, prefixSucc_extendSucc]

theorem matrixBondFun_add (n : ℕ) (M N : MatrixStage n) :
    matrixBondFun n (M + N) = matrixBondFun n M + matrixBondFun n N := by
  ext v w
  dsimp [matrixBondFun]
  split_ifs with h
  · rfl
  · simp

theorem matrixBondFun_one (n : ℕ) :
    matrixBondFun n (1 : MatrixStage n) = (1 : MatrixStage (n + 1)) := by
  ext v w
  dsimp [matrixBondFun, Matrix.one_apply]
  by_cases hlast : v ⟨n, Nat.lt_succ_self n⟩ = w ⟨n, Nat.lt_succ_self n⟩
  · by_cases hvw : v = w
    · subst w
      simp
    · have hpref : prefixSucc n v ≠ prefixSucc n w := by
        intro h
        apply hvw
        funext i
        by_cases hi : i.1 < n
        · exact congrFun h ⟨i.1, hi⟩
        · have hi' : i.1 = n := by omega
          have hi_eq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi'
          rw [hi_eq]
          exact hlast
      simp [hvw, hpref]
  · have hvw : v ≠ w := by
      intro h
      subst w
      exact hlast rfl
    simp [hvw, hlast]

theorem bitword_sum_last_split (n : ℕ) (f : BitWord (n + 1) → ℝ) :
    ∑ u : BitWord (n + 1), f u =
      ∑ u_pref : BitWord n,
        (f (extendSucc n u_pref true) + f (extendSucc n u_pref false)) := by
  let hequiv : BitWord (n + 1) ≃ BitWord n × Bool := {
      toFun := fun w => (prefixSucc n w, w ⟨n, Nat.lt_succ_self n⟩)
      invFun := fun p => extendSucc n p.1 p.2
      left_inv := by
        intro w
        funext i
        by_cases hi : i.1 < n
        · simp [prefixSucc, extendSucc, hi]
        · have hi' : i.1 = n := by omega
          have hi_eq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi'
          rw [hi_eq]
          dsimp [extendSucc]
          rw [dif_neg (lt_irrefl n)]
      right_inv := by
        rintro ⟨w, b⟩
        apply Prod.ext
        · funext i
          change prefixSucc n (extendSucc n w b) i = w i
          exact congrFun (prefixSucc_extendSucc n w b) i
        · change (extendSucc n w b) ⟨n, Nat.lt_succ_self n⟩ = b
          dsimp [extendSucc]
          rw [dif_neg (lt_irrefl n)]
  }
  rw [← Equiv.sum_comp hequiv.symm]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have hequiv_symm (x : BitWord n) (b : Bool) :
      hequiv.symm (x, b) = extendSucc n x b := by
    simp [hequiv]
  simp_rw [hequiv_symm]

theorem matrixBondFun_mul (n : ℕ) (M N : MatrixStage n) :
    matrixBondFun n (M * N) = matrixBondFun n M * matrixBondFun n N := by
  ext v w
  change
    (if v ⟨n, Nat.lt_succ_self n⟩ = w ⟨n, Nat.lt_succ_self n⟩ then
        (M * N) (prefixSucc n v) (prefixSucc n w)
      else 0) =
      ∑ u : BitWord (n + 1),
        (if v ⟨n, Nat.lt_succ_self n⟩ = u ⟨n, Nat.lt_succ_self n⟩ then
            M (prefixSucc n v) (prefixSucc n u)
          else 0) *
        (if u ⟨n, Nat.lt_succ_self n⟩ = w ⟨n, Nat.lt_succ_self n⟩ then
            N (prefixSucc n u) (prefixSucc n w)
          else 0)
  rw [bitword_sum_last_split]
  cases hv : v ⟨n, Nat.lt_succ_self n⟩ <;>
    cases hw : w ⟨n, Nat.lt_succ_self n⟩ <;>
      simp [hv, hw, extendSucc, Matrix.mul_apply, prefixSucc_extendSucc]

def matrixBond (n : ℕ) : MatrixStage n →+* MatrixStage (n + 1) where
  toFun := matrixBondFun n
  map_one' := matrixBondFun_one n
  map_mul' := matrixBondFun_mul n
  map_zero' := by
    ext v w
    dsimp [matrixBondFun]
    split_ifs <;> rfl
  map_add' := matrixBondFun_add n

theorem matrixBond_injective (n : ℕ) :
    Function.Injective (matrixBond n) := by
  intro M N hMN
  ext v w
  have h_inj := congrFun (congrFun hMN
    (extendSucc n v true)) (extendSucc n w true)
  dsimp [matrixBond, matrixBondFun] at h_inj
  have hb :
      (extendSucc n v true) ⟨n, Nat.lt_succ_self n⟩ =
        (extendSucc n w true) ⟨n, Nat.lt_succ_self n⟩ := by
        dsimp [extendSucc]
        rw [dif_neg (lt_irrefl n), dif_neg (lt_irrefl n)]
  rw [if_pos hb, if_pos hb, prefixSucc_extendSucc,
    prefixSucc_extendSucc] at h_inj
  exact h_inj

theorem matrixBond_smul (n : ℕ) (c : ℝ) (M : MatrixStage n) :
    matrixBond n (c • M) = c • matrixBond n M := by
  ext v w
  simp [matrixBond, matrixBondFun, smul_eq_mul]

def rawTrace (n : ℕ) (M : MatrixStage n) : ℝ :=
  Matrix.trace M

theorem rawTrace_bond (n : ℕ) (M : MatrixStage n) :
    rawTrace (n + 1) (matrixBond n M) = 2 * rawTrace n M := by
  dsimp [rawTrace, Matrix.trace]
  rw [bitword_sum_last_split]
  have h_diag : ∀ u_pref : BitWord n,
      (matrixBond n M (extendSucc n u_pref true) (extendSucc n u_pref true) +
        matrixBond n M (extendSucc n u_pref false) (extendSucc n u_pref false)) =
        2 * M u_pref u_pref := by
    intro u_pref
    dsimp [matrixBond, matrixBondFun]
    rw [if_pos rfl, if_pos rfl, prefixSucc_extendSucc,
      prefixSucc_extendSucc]
    ring
  simp_rw [h_diag]
  rw [← Finset.mul_sum]

def normalizedTrace (n : ℕ) (M : MatrixStage n) : ℝ :=
  (1 / (2 ^ n : ℝ)) * rawTrace n M

@[simp] theorem normalizedTrace_one (n : ℕ) :
    normalizedTrace n (1 : MatrixStage n) = 1 := by
  dsimp [normalizedTrace, rawTrace, Matrix.trace]
  have h_card : (Finset.univ : Finset (BitWord n)).card = 2 ^ n := by
    simp [BitWord]
  simp only [Matrix.one_apply_eq, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [h_card]
  norm_num [Nat.cast_pow]

@[simp] theorem normalizedTrace_compatible (n : ℕ) (M : MatrixStage n) :
    normalizedTrace (n + 1) (matrixBond n M) = normalizedTrace n M := by
  dsimp [normalizedTrace]
  rw [rawTrace_bond n M]
  have h_pow : (2 ^ (n + 1) : ℝ) = 2 ^ n * 2 := by ring
  rw [h_pow]
  have h_ne : (2 ^ n : ℝ) ≠ 0 := by positivity
  field_simp [h_ne]

theorem bondMap_smul
    (m n : ℕ) (h : m ≤ n) (c : ℝ) (M : MatrixStage m) :
    bondMap matrixBond m n h (c • M) =
      c • bondMap matrixBond m n h M := by
  refine Nat.le_induction
    (m := m)
    (P := fun k hk =>
      bondMap matrixBond m k hk (c • M) =
        c • bondMap matrixBond m k hk M)
    ?base ?succ n h
  · simp [bondMap_refl]
  · intro k hmk ih
    rw [bondMap_succ matrixBond m k hmk]
    change matrixBond k (bondMap matrixBond m k hmk (c • M)) =
      c • matrixBond k (bondMap matrixBond m k hmk M)
    rw [ih, matrixBond_smul]

abbrev PrimonUHFAlgebra :=
  DirectLimitSuperClosure (Stage := MatrixStage) matrixBond

def primonUHFScalar (c : ℝ) (x : PrimonUHFAlgebra) : PrimonUHFAlgebra :=
  DirectLimit.map
    (fun _ _ hij => bondMap matrixBond _ _ hij)
    (fun _ _ hij => bondMap matrixBond _ _ hij)
    (fun _ M => c • M)
    (by
      intro m n h M
      exact bondMap_smul m n h c M)
    x

@[simp] theorem primonUHFScalar_stage (c : ℝ) (n : ℕ) (M : MatrixStage n) :
    primonUHFScalar c (⟦⟨n, M⟩⟧ : PrimonUHFAlgebra) =
      ⟦⟨n, c • M⟩⟧ := by
  rfl

noncomputable instance primonUHFModule : Module ℝ PrimonUHFAlgebra where
  smul := primonUHFScalar
  one_smul := by
    intro x
    induction x using DirectLimit.induction with
    | _ n M =>
        change primonUHFScalar 1 (⟦⟨n, M⟩⟧ : PrimonUHFAlgebra) = ⟦⟨n, M⟩⟧
        rw [primonUHFScalar_stage]
        simp
  mul_smul := by
    intro c d x
    induction x using DirectLimit.induction with
    | _ n M =>
        change primonUHFScalar (c * d) (⟦⟨n, M⟩⟧ : PrimonUHFAlgebra) =
          primonUHFScalar c (primonUHFScalar d ⟦⟨n, M⟩⟧)
        rw [primonUHFScalar_stage, primonUHFScalar_stage]
        simp [smul_smul]
  smul_zero := by
    intro c
    rw [DirectLimit.zero_def 0]
    change primonUHFScalar c (⟦⟨0, 0⟩⟧ : PrimonUHFAlgebra) = ⟦⟨0, 0⟩⟧
    simpa using (primonUHFScalar_stage c 0 (0 : MatrixStage 0))
  smul_add := by
    intro c x y
    induction x, y using DirectLimit.induction₂ with
    | _ n M N =>
        rw [DirectLimit.add_def]
        change primonUHFScalar c (⟦⟨n, M + N⟩⟧ : PrimonUHFAlgebra) =
          primonUHFScalar c ⟦⟨n, M⟩⟧ + primonUHFScalar c ⟦⟨n, N⟩⟧
        rw [primonUHFScalar_stage, primonUHFScalar_stage,
          primonUHFScalar_stage]
        rw [smul_add]
        exact (DirectLimit.add_def n (c • M) (c • N)).symm
  add_smul := by
    intro c d x
    induction x using DirectLimit.induction with
    | _ n M =>
        change primonUHFScalar (c + d) (⟦⟨n, M⟩⟧ : PrimonUHFAlgebra) =
          primonUHFScalar c ⟦⟨n, M⟩⟧ + primonUHFScalar d ⟦⟨n, M⟩⟧
        rw [primonUHFScalar_stage, primonUHFScalar_stage,
          primonUHFScalar_stage]
        rw [add_smul]
        exact (DirectLimit.add_def n (c • M) (d • M)).symm
  zero_smul := by
    intro x
    induction x using DirectLimit.induction with
    | _ n M =>
        change primonUHFScalar 0 (⟦⟨n, M⟩⟧ : PrimonUHFAlgebra) = 0
        rw [primonUHFScalar_stage]
        rw [DirectLimit.zero_def n]
        simp

def toColimit (n : ℕ) : MatrixStage n →+* PrimonUHFAlgebra :=
  directLimitOf matrixBond n

def toColimitLinear (n : ℕ) : MatrixStage n →ₗ[ℝ] PrimonUHFAlgebra where
  toFun := toColimit n
  map_add' := (toColimit n).map_add
  map_smul' := by
    intro c M
    change toColimit n (c • M) = primonUHFScalar c (toColimit n M)
    rfl

@[simp] theorem toColimit_bond (n : ℕ) (M : MatrixStage n) :
    toColimit (n + 1) (matrixBond n M) = toColimit n M :=
  directLimitOf_bond matrixBond n M

/-- The full matrix-stage cone is compatible with the successor bonding map
    at the linear-map level. -/
def matrixBondLinear (n : ℕ) : MatrixStage n →ₗ[ℝ] MatrixStage (n + 1) where
  toFun := matrixBond n
  map_add' := (matrixBond n).map_add
  map_smul' := matrixBond_smul n

theorem toColimitLinear_comp_matrixBond (n : ℕ) :
    (toColimitLinear (n + 1)).comp (matrixBondLinear n) =
      toColimitLinear n := by
  apply LinearMap.ext
  intro M
  exact toColimit_bond n M

theorem toColimit_injective (n : ℕ) :
    Function.Injective (toColimit n) :=
  directLimitOf_injective matrixBond matrixBond_injective n

def TraceCompatibleCone : Prop :=
  ∀ (n : ℕ) (M : MatrixStage n),
    normalizedTrace (n + 1) (matrixBond n M) = normalizedTrace n M

theorem traceCompatibleCone : TraceCompatibleCone := by
  intro n M
  exact normalizedTrace_compatible n M

/-! ## 4. Linear Trace Descent on the Algebraic Colimit -/

/-- The normalized trace at one finite stage, packaged as a native linear map. -/
def normalizedTraceLinear (n : ℕ) : MatrixStage n →ₗ[ℝ] ℝ where
  toFun := normalizedTrace n
  map_add' := by
    intro M N
    simp [normalizedTrace, rawTrace, Matrix.trace_add, add_mul]
    ring
  map_smul' := by
    intro c M
    simp [normalizedTrace, rawTrace, Matrix.trace_smul, smul_eq_mul,
      mul_assoc]
    ring

/-! The finite trace already supplies the cyclic identity needed by the
colimit readout.  Keeping this at the stage owner avoids rebuilding it in
each modular or chiral application. -/

theorem normalizedTrace_commutator_zero (n : ℕ) (M N : MatrixStage n) :
    normalizedTrace n (M * N - N * M) = 0 := by
  unfold normalizedTrace rawTrace
  rw [Matrix.trace_sub, Matrix.trace_mul_comm M N]
  ring

/-- Compatibility of the normalized traces with every iterated bonding map. -/
theorem normalizedTrace_compatible_bondMap
    (m n : ℕ) (h : m ≤ n) (M : MatrixStage m) :
    normalizedTrace n (bondMap matrixBond m n h M) = normalizedTrace m M := by
  refine Nat.le_induction
    (m := m)
    (P := fun k hk =>
      normalizedTrace k (bondMap matrixBond m k hk M) = normalizedTrace m M)
    ?base ?succ n h
  · simp [bondMap_refl]
  · intro k hmk ih
    rw [bondMap_succ matrixBond m k hmk]
    change normalizedTrace (k + 1)
      (matrixBond k (bondMap matrixBond m k hmk M)) = normalizedTrace m M
    rw [normalizedTrace_compatible]
    exact ih

def colimitTrace : PrimonUHFAlgebra →ₗ[ℝ] ℝ where
  toFun := DirectLimit.lift
    (fun _ _ hij => bondMap matrixBond _ _ hij)
    (fun n M => normalizedTrace n M)
    (by
      intro m n h M
      exact (normalizedTrace_compatible_bondMap m n h M).symm)
  map_add' := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ n M N =>
        simp only [DirectLimit.add_def, DirectLimit.lift_def]
        exact (normalizedTraceLinear n).map_add M N
  map_smul' := by
    intro c x
    induction x using DirectLimit.induction with
    | _ n M =>
        rw [show c • (⟦⟨n, M⟩⟧ : PrimonUHFAlgebra) =
          primonUHFScalar c (⟦⟨n, M⟩⟧ : PrimonUHFAlgebra) by rfl]
        rw [primonUHFScalar_stage]
        simp only [DirectLimit.lift_def]
        exact (normalizedTraceLinear n).map_smul c M

@[simp] theorem colimitTrace_stage (n : ℕ) (M : MatrixStage n) :
    colimitTrace (toColimit n M) = normalizedTrace n M := by
  rfl

theorem colimitTrace_one : colimitTrace (1 : PrimonUHFAlgebra) = 1 := by
  rw [DirectLimit.one_def 0]
  exact normalizedTrace_one 0

def tauInfinity : PrimonUHFAlgebra →ₗ[ℝ] ℝ := colimitTrace

@[simp] theorem tauInfinity_stage (n : ℕ) (M : MatrixStage n) :
    tauInfinity (toColimit n M) = normalizedTrace n M := by
  rfl

theorem tauInfinity_commutator_zero (X Y : PrimonUHFAlgebra) :
    tauInfinity (X * Y - Y * X) = 0 := by
  induction X, Y using DirectLimit.induction₂ with
  | _ n M N =>
      rw [DirectLimit.mul_def, DirectLimit.mul_def, DirectLimit.sub_def]
      change normalizedTrace n (M * N - N * M) = 0
      exact normalizedTrace_commutator_zero n M N

theorem tauInfinity_toColimitLinear (n : ℕ) (M : MatrixStage n) :
    tauInfinity (toColimitLinear n M) = normalizedTraceLinear n M := by
  rfl

theorem tauInfinity_one : tauInfinity (1 : PrimonUHFAlgebra) = 1 := by
  exact colimitTrace_one

end InfoGeometry.Algebra.PrimonColimitAlgebra
