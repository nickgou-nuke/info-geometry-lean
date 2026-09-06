import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Tactic
import InfoGeometry.Algebra.PrimonColimitAlgebra
import InfoGeometry.OperatorAlgebra.FiniteParitySupertrace

/-!
# Finite fermionic parity on the Primon/UHF colimit

This owner formalizes the algebraic `Z₂` parity carried by the Boolean-word
matrix tower.  The parity is defined on finite occupation words, transported
to matrix stages by diagonal conjugation, and descended through the native
direct limit.

No analytic zeta interpretation, Hilbert-transform theorem, or automorphic
identification is asserted here.
-/

noncomputable section

namespace InfoGeometry.Algebra.PrimonSuperalgebra

open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.OperatorAlgebra.FiniteParitySupertrace
open Matrix

abbrev Carrier := PrimonUHFAlgebra

/-- The local parity sign of one Boolean occupation bit. -/
def bitParity (b : Bool) : ℝ :=
  if b then -1 else 1

@[simp] theorem bitParity_sq (b : Bool) :
    bitParity b * bitParity b = 1 := by
  cases b <;> norm_num [bitParity]

/-- Recursive parity sign of a finite Boolean occupation word. -/
def paritySign : (n : ℕ) → BitWord n → ℝ
  | 0, _ => 1
  | n + 1, w =>
      paritySign n (prefixSucc n w) *
        bitParity (w ⟨n, Nat.lt_succ_self n⟩)

@[simp] theorem paritySign_sq (n : ℕ) (w : BitWord n) :
    paritySign n w * paritySign n w = 1 := by
  induction n with
  | zero => norm_num [paritySign]
  | succ n ih =>
      dsimp [paritySign]
      calc
        (paritySign n (prefixSucc n w) * bitParity (w _)) *
            (paritySign n (prefixSucc n w) * bitParity (w _)) =
          (paritySign n (prefixSucc n w) * paritySign n (prefixSucc n w)) *
            (bitParity (w _) * bitParity (w _)) := by ring
        _ = 1 * 1 := by rw [ih, bitParity_sq]
        _ = 1 := by norm_num

/-- Stage parity acts on a matrix entry by the two endpoint signs. -/
def stageParityFun (n : ℕ) (M : MatrixStage n) : MatrixStage n :=
  fun v w => paritySign n v * paritySign n w * M v w

theorem stageParity_mul (n : ℕ) (M N : MatrixStage n) :
    stageParityFun n (M * N) = stageParityFun n M * stageParityFun n N := by
  ext v w
  simp only [stageParityFun, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  calc
    paritySign n v * paritySign n w * (M v u * N u w) =
        (paritySign n v * paritySign n u * M v u) *
          (paritySign n u * paritySign n w * N u w) := by
      calc
        paritySign n v * paritySign n w * (M v u * N u w) =
            (paritySign n v * paritySign n w * (M v u * N u w)) *
              (paritySign n u * paritySign n u) := by
                rw [paritySign_sq]
                ring
        _ = (paritySign n v * paritySign n u * M v u) *
              (paritySign n u * paritySign n w * N u w) := by ring

theorem stageParity_one (n : ℕ) :
    stageParityFun n (1 : MatrixStage n) = 1 := by
  ext v w
  simp only [stageParityFun, Matrix.one_apply]
  by_cases h : v = w
  · subst w
    simp [paritySign_sq]
  · simp [h]

/-- The finite-stage parity ring endomorphism. -/
def stageParityHom (n : ℕ) : MatrixStage n →+* MatrixStage n where
  toFun := stageParityFun n
  map_one' := stageParity_one n
  map_mul' := stageParity_mul n
  map_zero' := by
    ext v w
    simp [stageParityFun]
  map_add' := by
    intro M N
    ext v w
    simp [stageParityFun, mul_add]

@[simp] theorem stageParityHom_apply (n : ℕ) (M : MatrixStage n) :
    stageParityHom n M = stageParityFun n M :=
  rfl

/-- Stage parity commutes with the native block-diagonal bonding map. -/
theorem stageParity_bond (n : ℕ) (M : MatrixStage n) :
    stageParityHom (n + 1) (matrixBond n M) =
      matrixBond n (stageParityHom n M) := by
  ext v w
  dsimp [stageParityHom, stageParityFun, matrixBond, matrixBondFun]
  by_cases hlast : v ⟨n, Nat.lt_succ_self n⟩ =
      w ⟨n, Nat.lt_succ_self n⟩
  · simp only [hlast]
    dsimp [paritySign]
    rw [hlast]
    calc
      paritySign n (prefixSucc n v) * bitParity (w _) *
          (paritySign n (prefixSucc n w) * bitParity (w _)) *
          M (prefixSucc n v) (prefixSucc n w) =
        paritySign n (prefixSucc n v) * paritySign n (prefixSucc n w) *
          (bitParity (w _) * bitParity (w _)) *
          M (prefixSucc n v) (prefixSucc n w) := by ring
      _ = paritySign n (prefixSucc n v) * paritySign n (prefixSucc n w) *
          M (prefixSucc n v) (prefixSucc n w) := by
            rw [bitParity_sq]
            ring
  · simp [hlast]

theorem stageParity_involutive (n : ℕ) (M : MatrixStage n) :
    stageParityHom n (stageParityHom n M) = M := by
  ext v w
  change paritySign n v * paritySign n w *
      (paritySign n v * paritySign n w * M v w) = M v w
  calc
    paritySign n v * paritySign n w *
        (paritySign n v * paritySign n w * M v w) =
      (paritySign n v * paritySign n v) *
        (paritySign n w * paritySign n w) * M v w := by ring
    _ = M v w := by rw [paritySign_sq, paritySign_sq]; ring

/-! At a finite stage, the parity automorphism is implemented by the
diagonal sign operator, so the canonical finite supertrace owner applies
directly to its odd eigenspace. -/

theorem finiteParitySupertrace_zero_of_stageParity_neg
    (n : ℕ) (M : MatrixStage n)
    (hodd : stageParityHom n M = -M) :
    supertrace (paritySign n) M = 0 := by
  have hdiag : ∀ v : BitWord n, M v v = 0 := by
    intro v
    have h := congrArg (fun A : MatrixStage n => A v v) hodd
    change paritySign n v * paritySign n v * M v v = -M v v at h
    rw [paritySign_sq] at h
    linarith
  rw [supertrace_eq_sum_sign_mul_diagonal]
  simp_rw [hdiag]
  simp

def stageParityToColimit (n : ℕ) : MatrixStage n →+* Carrier :=
  (toColimit n).comp (stageParityHom n)

theorem stageParityToColimit_compatible (n : ℕ) (M : MatrixStage n) :
    stageParityToColimit (n + 1) (matrixBond n M) =
      stageParityToColimit n M := by
  change toColimit (n + 1)
      (stageParityHom (n + 1) (matrixBond n M)) =
    toColimit n (stageParityHom n M)
  rw [stageParity_bond, toColimit_bond]

/-- The parity endomorphism descended to the algebraic direct limit. -/
def globalParity : Carrier →+* Carrier :=
  directLimitLift matrixBond
    (fun n => stageParityToColimit n)
    (by
      intro n M
      exact stageParityToColimit_compatible n M)

@[simp] theorem globalParity_stage (n : ℕ) (M : MatrixStage n) :
    globalParity (toColimit n M) = toColimit n (stageParityHom n M) :=
  directLimitLift_of matrixBond
    (fun n => stageParityToColimit n)
    (by
      intro n M
      exact stageParityToColimit_compatible n M)
    n M

theorem globalParity_one :
    globalParity (1 : Carrier) = 1 := by
  rw [DirectLimit.one_def 0]
  change globalParity (toColimit 0 (1 : MatrixStage 0)) = _
  rw [globalParity_stage]
  change toColimit 0 (stageParityFun 0 (1 : MatrixStage 0)) = _
  exact congrArg (toColimit 0) (stageParity_one 0)

theorem globalParity_mul (X Y : Carrier) :
    globalParity (X * Y) = globalParity X * globalParity Y := by
  exact (globalParity).map_mul X Y

theorem globalParity_involutive (X : Carrier) :
    globalParity (globalParity X) = X := by
  induction X using DirectLimit.induction with
  | _ n M =>
      calc
        globalParity (globalParity (toColimit n M)) =
            globalParity (toColimit n (stageParityHom n M)) := by
              rw [globalParity_stage]
        _ = toColimit n (stageParityHom n (stageParityHom n M)) := by
              rw [globalParity_stage]
        _ = toColimit n M := by rw [stageParity_involutive]

/-! The normalized trace is invariant under the parity automorphism.  This is
the scalar trace consequence of the finite diagonal conjugations; it is not
an internal implementation of parity by a distinguished colimit element. -/

theorem normalizedTrace_stageParity (n : ℕ) (M : MatrixStage n) :
    normalizedTrace n (stageParityHom n M) = normalizedTrace n M := by
  dsimp [normalizedTrace, rawTrace, stageParityHom, stageParityFun, Matrix.trace]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  rw [paritySign_sq]
  ring

theorem tauInfinity_globalParity (X : Carrier) :
    tauInfinity (globalParity X) = tauInfinity X := by
  induction X using DirectLimit.induction with
  | _ n M =>
      change tauInfinity (globalParity (toColimit n M)) =
        tauInfinity (toColimit n M)
      rw [globalParity_stage, tauInfinity_stage, tauInfinity_stage,
        normalizedTrace_stageParity]

/-- The descended parity is an actual automorphism of the direct-limit ring. -/
def globalParityEquiv : Carrier ≃+* Carrier where
  toFun := globalParity
  invFun := globalParity
  left_inv := globalParity_involutive
  right_inv := globalParity_involutive
  map_mul' := globalParity.map_mul
  map_add' := globalParity.map_add

@[simp] theorem globalParityEquiv_apply (X : Carrier) :
    globalParityEquiv X = globalParity X :=
  rfl

@[simp] theorem globalParityEquiv_symm_apply (X : Carrier) :
    globalParityEquiv.symm X = globalParity X :=
  rfl

def isBosonic (X : Carrier) : Prop := globalParity X = X

def isFermionic (X : Carrier) : Prop := globalParity X = -X

theorem tauInfinity_zero_of_isFermionic {X : Carrier}
    (hX : isFermionic X) :
    tauInfinity X = 0 := by
  have htrace := tauInfinity_globalParity X
  rw [hX, map_neg] at htrace
  linarith

theorem isBosonic_zero : isBosonic (0 : Carrier) := by
  simp [isBosonic]

theorem isBosonic_one : isBosonic (1 : Carrier) := by
  rw [isBosonic]
  exact globalParity_one

theorem isBosonic_add {X Y : Carrier}
    (hX : isBosonic X) (hY : isBosonic Y) :
    isBosonic (X + Y) := by
  rw [isBosonic, globalParity.map_add, hX, hY]

theorem isBosonic_neg {X : Carrier}
    (hX : isBosonic X) : isBosonic (-X) := by
  rw [isBosonic, globalParity.map_neg, hX]

theorem isBosonic_mul {X Y : Carrier}
    (hX : isBosonic X) (hY : isBosonic Y) :
    isBosonic (X * Y) := by
  rw [isBosonic, globalParity.map_mul, hX, hY]

theorem isFermionic_add {X Y : Carrier}
    (hX : isFermionic X) (hY : isFermionic Y) :
    isFermionic (X + Y) := by
  rw [isFermionic, globalParity.map_add, hX, hY]
  exact (neg_add X Y).symm

theorem isFermionic_neg {X : Carrier}
    (hX : isFermionic X) : isFermionic (-X) := by
  rw [isFermionic, globalParity.map_neg, hX]

theorem isFermionic_mul_isFermionic_isBosonic
    {X Y : Carrier} (hX : isFermionic X) (hY : isFermionic Y) :
    isBosonic (X * Y) := by
  rw [isBosonic, globalParity.map_mul, hX, hY]
  simp

theorem isBosonic_mul_isFermionic_isFermionic
    {X Y : Carrier} (hX : isBosonic X) (hY : isFermionic Y) :
    isFermionic (X * Y) := by
  rw [isFermionic, globalParity.map_mul, hX, hY]
  simp

theorem isFermionic_mul_isBosonic_isFermionic
    {X Y : Carrier} (hX : isFermionic X) (hY : isBosonic Y) :
    isFermionic (X * Y) := by
  rw [isFermionic, globalParity.map_mul, hX, hY]
  simp

end InfoGeometry.Algebra.PrimonSuperalgebra

end noncomputable section
