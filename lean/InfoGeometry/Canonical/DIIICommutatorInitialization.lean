/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealBdG
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture
import InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Complex.Basic

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.DIIICommutatorInitialization

Symbol-first initialization surface for DIII operator constraints on the doubled
real carrier.

This file is intentionally thin:

- it defines commutator/anticommutator operators on endomorphisms,
- it packages the DIII algebra as a typeclass,
- and it provides a constructor theorem from the two core constraints
  `[T, H] = 0` and `{P, H} = 0`.

No physical narrative is used as proof evidence; only operator identities.
-/

namespace InfoGeometry.Canonical.DIIICommutatorInitialization

open RealBdG
open InfoGeometry.Krein

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Endomorphism commutator `[A,B] = AB - BA` on the doubled carrier. -/
noncomputable def endCommutator (A B : EndH) : EndH :=
  A.comp B - B.comp A

/-- Endomorphism anticommutator `{A,B} = AB + BA` on the doubled carrier. -/
noncomputable def endAnticommutator (A B : EndH) : EndH :=
  A.comp B + B.comp A

/--
Operator-level DIII initialization package.

`T` and `P` satisfy the Clifford signatures, while `H` is constrained by
the commutator/anticommutator laws and induced chiral product `C = T ∘ P`.
-/
class TopologicalClassDIII (H T P : EndH) : Prop where
  T_squared : T.comp T = -(ContinuousLinearMap.id ℝ H₂)
  P_squared : P.comp P = ContinuousLinearMap.id ℝ H₂
  T_commutes : T.comp H = H.comp T
  P_anticommutes : P.comp H = -(H.comp P)
  C_definition : ∃ C : EndH, C = T.comp P ∧ C.comp H = -(H.comp C)

/-- Class law `[T,H]=0` in explicit commutator form. -/
@[rep_depth transport]
theorem commutator_T_H_eq_zero
    {H T P : EndH}
    [hDIII : TopologicalClassDIII (E := E) H T P] :
    endCommutator T H = 0 := by
  simpa [endCommutator] using (sub_eq_zero.mpr hDIII.T_commutes)

/-- Class law `{P,H}=0` in explicit anticommutator form. -/
@[rep_depth transport]
theorem anticommutator_P_H_eq_zero
    {H T P : EndH}
    [hDIII : TopologicalClassDIII (E := E) H T P] :
    endAnticommutator P H = 0 := by
  unfold endAnticommutator
  calc
    P.comp H + H.comp P = -(H.comp P) + H.comp P := by
      rw [hDIII.P_anticommutes]
    _ = 0 := by
      abel

/-- The induced chiral witness is available as an explicit existential theorem. -/
@[rep_depth transport]
theorem chiral_witness_exists
    {H T P : EndH}
    [hDIII : TopologicalClassDIII (E := E) H T P] :
    ∃ C : EndH, C = T.comp P ∧ C.comp H = -(H.comp C) :=
  hDIII.C_definition

/--
Constructor theorem: if `T²=-1`, `P²=1`, `[T,H]=0`, and `{P,H}=0`, then the
full DIII package is forced.
-/
@[rep_depth transport]
theorem topologicalClassDIII_of_commutation_data
    (H T P : EndH)
    (hTsq : T.comp T = -(ContinuousLinearMap.id ℝ H₂))
    (hPsq : P.comp P = ContinuousLinearMap.id ℝ H₂)
    (hTH : T.comp H = H.comp T)
    (hPH : P.comp H = -(H.comp P)) :
    TopologicalClassDIII (E := E) H T P := by
  refine ⟨hTsq, hPsq, hTH, hPH, ?_⟩
  refine ⟨T.comp P, rfl, ?_⟩
  calc
    (T.comp P).comp H = T.comp (P.comp H) := by
      simp [ContinuousLinearMap.comp_assoc]
    _ = T.comp (-(H.comp P)) := by
      rw [hPH]
    _ = -(T.comp (H.comp P)) := by
      simp
    _ = -((T.comp H).comp P) := by
      simp [ContinuousLinearMap.comp_assoc]
    _ = -((H.comp T).comp P) := by
      rw [hTH]
    _ = -(H.comp (T.comp P)) := by
      simp [ContinuousLinearMap.comp_assoc]

section Bridge

variable [CompleteSpace E]

/--
Bridge constructor from the real BdG datum to DIII constraints with
`T := K = J ∘ ε` and `P := J`, assuming the datum's chiral lane is `J`.
-/
@[rep_depth transport]
theorem topologicalClassDIII_of_realBdGDatum
    (X : RealBdGDatum (E := E))
    (hChiral : X.chiral = modular_j (E := E)) :
    TopologicalClassDIII (E := E) X.H (modularK (E := E)) (modular_j (E := E)) := by
  have hTH : (modularK (E := E)).comp X.H = X.H.comp (modularK (E := E)) := by
    simpa [KLinear] using X.H_KLinear.symm
  have hPH : (modular_j (E := E)).comp X.H = -(X.H.comp (modular_j (E := E))) := by
    calc
      (modular_j (E := E)).comp X.H = X.chiral.comp X.H := by
        simp [hChiral]
      _ = -(X.H.comp X.chiral) := X.H_chiral
      _ = -(X.H.comp (modular_j (E := E))) := by
        simp [hChiral]
  exact topologicalClassDIII_of_commutation_data
    (E := E) X.H (modularK (E := E)) (modular_j (E := E))
    (modularK_sq (E := E))
    (modular_j_involution (E := E))
    hTH hPH

end Bridge

end Core

section RingAZ

open InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge

/-- Integer square-sign encoding (`0` for absent, `1` for `+1`, `-1` for `-1`). -/
def symSquareToInt : SymSquareSign → ℤ
  | .absent => 0
  | .plus => 1
  | .minus => -1

section RingAlgebra

variable {A : Type*} [Ring A]

/-- Associative-ring commutator `[x, y] = x * y - y * x`. -/
def ringComm (x y : A) : A :=
  x * y - y * x

/-- Associative-ring anticommutator `{x, y} = x * y + y * x`. -/
def ringAnticomm (x y : A) : A :=
  x * y + y * x

@[simp]
theorem ringComm_eq_zero_iff (x y : A) : ringComm x y = 0 ↔ x * y = y * x :=
  sub_eq_zero

@[simp]
theorem ringAnticomm_eq_zero_iff (x y : A) : ringAnticomm x y = 0 ↔ x * y = -(y * x) := by
  rw [ringAnticomm, add_eq_zero_iff_eq_neg]

/-- Algebraic forcing: if `[T, H] = 0` and `{C, H} = 0`, then `{T * C, H} = 0`. -/
theorem chiral_of_TR_PH {H T C : A}
    (hTH : ringComm T H = 0) (hCH : ringAnticomm C H = 0) :
    ringAnticomm (T * C) H = 0 := by
  have hTH' : T * H = H * T := (ringComm_eq_zero_iff T H).mp hTH
  have hCH' : C * H = -(H * C) := (ringAnticomm_eq_zero_iff C H).mp hCH
  rw [ringAnticomm_eq_zero_iff]
  calc
    (T * C) * H = T * (C * H) := mul_assoc T C H
    _ = T * (-(H * C)) := by rw [hCH']
    _ = -((T * H) * C) := by rw [mul_neg, mul_assoc]
    _ = -((H * T) * C) := by rw [hTH']
    _ = -(H * (T * C)) := by rw [mul_assoc]

/-- Algebraic forcing: if `{C, H} = 0` and `{S, H} = 0`, then `[C * S, H] = 0`. -/
theorem tr_of_PH_chiral {H C S : A}
    (hCH : ringAnticomm C H = 0) (hSH : ringAnticomm S H = 0) :
    ringComm (C * S) H = 0 := by
  have hCH' : C * H = -(H * C) := (ringAnticomm_eq_zero_iff C H).mp hCH
  have hSH' : S * H = -(H * S) := (ringAnticomm_eq_zero_iff S H).mp hSH
  rw [ringComm_eq_zero_iff]
  calc
    (C * S) * H = C * (S * H) := mul_assoc C S H
    _ = C * (-(H * S)) := by rw [hSH']
    _ = -((C * H) * S) := by rw [mul_neg, mul_assoc]
    _ = -((-(H * C)) * S) := by rw [hCH']
    _ = (H * C) * S := by rw [neg_mul, neg_neg]
    _ = H * (C * S) := mul_assoc H C S

/-- Exact square sign of `T * C` given `T² = εT • 1`, `C² = εC • 1`, and
`T * C = η • (C * T)` with `η² = 1`: `(T * C)² = (εT * εC * η) • 1`. -/
theorem chiral_sq_of_comm_or_anticomm {T C : A} {εT εC η : ℤ}
    (hη : η * η = 1)
    (hTsq : T * T = εT • (1 : A))
    (hCsq : C * C = εC • (1 : A))
    (hTC : T * C = η • (C * T)) :
    (T * C) * (T * C) = (εT * εC * η) • (1 : A) := by
  have hCT : C * T = η • (T * C) := by
    calc
      C * T = (1 : ℤ) • (C * T) := (one_zsmul _).symm
      _ = (η * η) • (C * T) := by rw [hη]
      _ = η • (η • (C * T)) := mul_smul η η (C * T)
      _ = η • (T * C) := by rw [← hTC]
  calc
    (T * C) * (T * C) = T * (C * T) * C := by simp only [mul_assoc]
    _ = T * (η • (T * C)) * C := by rw [hCT]
    _ = η • ((T * T) * (C * C)) := by
        rw [mul_smul_comm, smul_mul_assoc]
        simp only [mul_assoc]
    _ = η • ((εT • (1 : A)) * (εC • (1 : A))) := by rw [hTsq, hCsq]
    _ = (η * (εT * εC)) • (1 : A) := by
        rw [smul_mul_assoc, one_mul, ← mul_smul, ← mul_smul]
        congr 1
        ring
    _ = (εT * εC * η) • (1 : A) := by
        congr 1
        ring

/-- Specialized DIII chiral involution identity: `T² = -1`, `C² = +1`, and `{T, C} = 0`
force `(T * C)² = 1`. -/
theorem diii_chiral_sq_one_of_anticomm {T C : A}
    (hTsq : T * T = (-1 : ℤ) • (1 : A))
    (hCsq : C * C = (1 : ℤ) • (1 : A))
    (hTC : T * C = -(C * T)) :
    (T * C) * (T * C) = (1 : A) := by
  have h := chiral_sq_of_comm_or_anticomm (A := A) (T := T) (C := C)
    (εT := -1) (εC := 1) (η := -1) (by norm_num) hTsq hCsq (by simpa using hTC)
  simpa using h

/-- Ring-level signed-operator packet over an associative ring `A`.
Its fields enforce the encoded presence, square, Hamiltonian, and (when present)
`T`/`C`/`S` coherence laws. It does not represent anti-linear symmetries or
require a self-adjoint or gapped Hamiltonian. -/
structure RingAZSymmetrySystem (A : Type*) [Ring A] (H : A) where
  sig : AZSignature
  isValid : sig.IsValid
  T : Option A
  C : Option A
  S : Option A
  T_some_iff : T.isSome ↔ sig.T_sq ≠ .absent
  C_some_iff : C.isSome ↔ sig.C_sq ≠ .absent
  S_some_iff : S.isSome ↔ sig.hasS = true
  T_law : ∀ t, T = some t → ringComm t H = 0 ∧ t * t = symSquareToInt sig.T_sq • (1 : A)
  C_law : ∀ c, C = some c → ringAnticomm c H = 0 ∧ c * c = symSquareToInt sig.C_sq • (1 : A)
  S_law : ∀ s, S = some s → ringAnticomm s H = 0 ∧ s * s = (1 : A)
  TC_commutation : ∀ t c, T = some t → C = some c →
    t * c = (symSquareToInt sig.T_sq * symSquareToInt sig.C_sq) • (c * t)
  S_eq_TC : ∀ t c s, T = some t → C = some c → S = some s → s = t * c

/-- Recover the AZ label encoded by a ring-level packet's validated signature. -/
def RingAZSymmetrySystem.azClass {H : A} (sys : RingAZSymmetrySystem A H) : AZClass :=
  azClassEquivValidSignature.symm ⟨sys.sig, sys.isValid⟩

theorem RingAZSymmetrySystem.azSignature_azClass {H : A} (sys : RingAZSymmetrySystem A H) :
    azSignature sys.azClass = sys.sig :=
  congrArg Subtype.val (azClassEquivValidSignature.apply_symm_apply ⟨sys.sig, sys.isValid⟩)

/-- Construct a `RingAZSymmetrySystem` from `[T, H] = 0` and `{C, H} = 0` whenever
`T` and `C` satisfy `T² = εT • 1`, `C² = εC • 1`, `T * C = η • (C * T)`, and
`εT * εC * η = 1` (covering BDI, DIII, CII, CI). -/
def ringAZSymmetrySystem_of_TR_PH
    (H T C : A) (tSign cSign : SymSquareSign)
    (ht : tSign ≠ .absent) (hc : cSign ≠ .absent)
    {η : ℤ} (hη : η * η = 1)
    (hTH : ringComm T H = 0)
    (hCH : ringAnticomm C H = 0)
    (hTsq : T * T = symSquareToInt tSign • (1 : A))
    (hCsq : C * C = symSquareToInt cSign • (1 : A))
    (hTC : T * C = η • (C * T))
    (hSign : symSquareToInt tSign * symSquareToInt cSign * η = 1) :
    RingAZSymmetrySystem A H where
  sig := ⟨tSign, cSign, true⟩
  isValid := ⟨fun _ _ => rfl, fun _ h => absurd h hc, fun h _ => absurd h ht⟩
  T := some T
  C := some C
  S := some (T * C)
  T_some_iff := by simp [ht]
  C_some_iff := by simp [hc]
  S_some_iff := by simp
  T_law := by
    intro t ht_eq
    cases ht_eq
    exact ⟨hTH, hTsq⟩
  C_law := by
    intro c hc_eq
    cases hc_eq
    exact ⟨hCH, hCsq⟩
  S_law := by
    intro s hs_eq
    cases hs_eq
    refine ⟨chiral_of_TR_PH hTH hCH, ?_⟩
    have hsq := chiral_sq_of_comm_or_anticomm hη hTsq hCsq hTC
    rw [hSign, one_zsmul] at hsq
    exact hsq
  TC_commutation := by
    intro t c ht_eq hc_eq
    cases ht_eq
    cases hc_eq
    have hEta : η = symSquareToInt tSign * symSquareToInt cSign := by
      cases tSign <;> cases cSign <;> simp_all [symSquareToInt] <;> omega
    rw [← hEta]
    exact hTC
  S_eq_TC := by
    intro t c s ht_eq hc_eq hs_eq
    cases ht_eq
    cases hc_eq
    cases hs_eq
    rfl

end RingAlgebra

section ComplexRingAlgebra

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- In a `ℂ`-algebra, multiplying an anti-involution `X² = -1` by `Complex.I` yields a
chiral involution `(I • X)² = 1` preserving `{·, H} = 0`. -/
theorem complex_chiral_of_neg_sq {H X : A}
    (hXH : ringAnticomm X H = 0) (hXsq : X * X = -(1 : A)) :
    ringAnticomm (Complex.I • X) H = 0 ∧ (Complex.I • X) * (Complex.I • X) = (1 : A) := by
  refine ⟨?_, ?_⟩
  · have hXH' : X * H = -(H * X) := (ringAnticomm_eq_zero_iff X H).mp hXH
    rw [ringAnticomm_eq_zero_iff, smul_mul_assoc, hXH', smul_neg, mul_smul_comm]
  · rw [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, hXsq, neg_smul,
      one_smul, neg_neg]

end ComplexRingAlgebra

section BridgeToRingAZ

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Lift a `TopologicalClassDIII` package together with the explicit relation
`T P = -P T` to a ring-level signed-operator packet with DIII signature. -/
noncomputable def ringAZSymmetrySystem_of_topologicalClassDIII
    (H T P : EndH)
    [hDIII : TopologicalClassDIII (E := E) H T P]
    (hTP : T.comp P = -(P.comp T)) :
    RingAZSymmetrySystem EndH H :=
  ringAZSymmetrySystem_of_TR_PH
    (A := EndH) H T P .minus .plus (by decide) (by decide)
    (η := -1) (by norm_num)
    (by
      rw [ringComm_eq_zero_iff]
      exact hDIII.T_commutes)
    (by
      rw [ringAnticomm_eq_zero_iff]
      exact hDIII.P_anticommutes)
    (by
      change T.comp T = (-1 : ℤ) • ContinuousLinearMap.id ℝ H₂
      rw [hDIII.T_squared, neg_one_zsmul])
    (by
      change P.comp P = (1 : ℤ) • ContinuousLinearMap.id ℝ H₂
      rw [hDIII.P_squared, one_zsmul])
    (by
      change T.comp P = (-1 : ℤ) • (P.comp T)
      rw [hTP, neg_one_zsmul])
    (by decide)

theorem ringAZSymmetrySystem_of_topologicalClassDIII_azClass
    (H T P : EndH)
    [TopologicalClassDIII (E := E) H T P]
    (hTP : T.comp P = -(P.comp T)) :
    (ringAZSymmetrySystem_of_topologicalClassDIII H T P hTP).azClass = .DIII := by
  rfl

section RealBdGRingAZ

variable [CompleteSpace E]

/-- Lift a `RealBdGDatum` satisfying `X.chiral = modular_j` to a ring-level
signed-operator packet with DIII signature, using `T := modularK` and
`C := modular_j`. -/
noncomputable def ringAZSymmetrySystem_of_realBdGDatum
    (X : RealBdGDatum (E := E))
    (hChiral : X.chiral = modular_j (E := E)) :
    RingAZSymmetrySystem EndH X.H :=
  letI : TopologicalClassDIII (E := E) X.H (modularK (E := E)) (modular_j (E := E)) :=
    topologicalClassDIII_of_realBdGDatum (E := E) X hChiral
  ringAZSymmetrySystem_of_topologicalClassDIII
    X.H (modularK (E := E)) (modular_j (E := E))
    (by
      rw [modularK_eq_complex_i (E := E), complex_i_comp_modular_j (E := E),
        modular_j_comp_complex_i (E := E)])

theorem ringAZSymmetrySystem_of_realBdGDatum_azClass
    (X : RealBdGDatum (E := E))
    (hChiral : X.chiral = modular_j (E := E)) :
    (ringAZSymmetrySystem_of_realBdGDatum X hChiral).azClass = .DIII := by
  dsimp [RingAZSymmetrySystem.azClass, ringAZSymmetrySystem_of_realBdGDatum,
    ringAZSymmetrySystem_of_topologicalClassDIII, ringAZSymmetrySystem_of_TR_PH,
    azClassEquivValidSignature, ofValidSignature]

end RealBdGRingAZ

end BridgeToRingAZ

section TenfoldMatrixWitnesses

open Matrix

private abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
private abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

private def sigI_C : M2C := 1
private def sigX_C : M2C := !![0, 1; 1, 0]
private def sigY_C : M2C := !![0, -Complex.I; Complex.I, 0]
private def sigZ_C : M2C := !![1, 0; 0, -1]
private def iSigY_C : M2C := !![0, 1; -1, 0]

private def sigX_R : M2R := !![0, 1; 1, 0]
private def sigZ_R : M2R := !![1, 0; 0, -1]
private def iSigY_R : M2R := !![0, 1; -1, 0]

private theorem sigX_C_sq : sigX_C * sigX_C = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigX_C, Matrix.mul_apply, Fin.sum_univ_two]

private theorem sigY_C_sq : sigY_C * sigY_C = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigY_C, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

private theorem sigZ_C_sq : sigZ_C * sigZ_C = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigZ_C, Matrix.mul_apply, Fin.sum_univ_two]

private theorem iSigY_C_sq : iSigY_C * iSigY_C = -(1 : M2C) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [iSigY_C, Matrix.mul_apply, Fin.sum_univ_two]

/-- Matrix parameter used by the finite ring-level AZ symmetry packets.
The `CII` packet uses the zero matrix; these data do not encode a spectral gap. -/
def azWitnessH : AZClass → M2C
  | .A    => sigZ_C
  | .AIII => sigX_C
  | .AI   => sigX_C
  | .BDI  => sigX_C
  | .D    => sigX_C
  | .DIII => sigY_C
  | .AII  => sigY_C
  | .CII  => 0
  | .C    => sigZ_C
  | .CI   => sigX_C

theorem azWitnessH_ne_zero (c : AZClass) (hc : c ≠ .CII) : azWitnessH c ≠ 0 := by
  cases c <;> intro h
  · simpa [azWitnessH, sigZ_C] using congrArg (fun M : M2C => M 0 0) h
  · simpa [azWitnessH, sigX_C] using congrArg (fun M : M2C => M 0 1) h
  · simpa [azWitnessH, sigX_C] using congrArg (fun M : M2C => M 0 1) h
  · simpa [azWitnessH, sigX_C] using congrArg (fun M : M2C => M 0 1) h
  · simpa [azWitnessH, sigX_C] using congrArg (fun M : M2C => M 0 1) h
  · simpa [azWitnessH, sigY_C] using congrArg (fun M : M2C => M 1 0) h
  · simpa [azWitnessH, sigY_C] using congrArg (fun M : M2C => M 1 0) h
  · exact (hc rfl).elim
  · simpa [azWitnessH, sigZ_C] using congrArg (fun M : M2C => M 0 0) h
  · simpa [azWitnessH, sigX_C] using congrArg (fun M : M2C => M 0 1) h

/-- Constructive ring-level signed-operator packet on `Matrix (Fin 2) (Fin 2) ℂ`
for each AZ signature. This is finite algebraic data, not an antiunitary or
stable-phase classification. -/
def azWitnessSystem (c : AZClass) : RingAZSymmetrySystem M2C (azWitnessH c) :=
  match c with
  | .A =>
    { sig := azSignature .A
      isValid := azSignature_isValid .A
      T := none
      C := none
      S := none
      T_some_iff := by simp [azSignature]
      C_some_iff := by simp [azSignature]
      S_some_iff := by simp [azSignature]
      T_law := by intro t ht; cases ht
      C_law := by intro x hx; cases hx
      S_law := by intro s hs; cases hs
      TC_commutation := by intro t c ht hc; cases ht
      S_eq_TC := by intro t c s ht hc hs; cases ht }
  | .AIII =>
    { sig := azSignature .AIII
      isValid := azSignature_isValid .AIII
      T := none
      C := none
      S := some sigZ_C
      T_some_iff := by simp [azSignature]
      C_some_iff := by simp [azSignature]
      S_some_iff := by simp [azSignature]
      T_law := by intro t ht; cases ht
      C_law := by intro x hx; cases hx
      S_law := by
        intro s hs; cases hs
        refine ⟨?_, sigZ_C_sq⟩
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [ringAnticomm, azWitnessH, sigZ_C, sigX_C]
      TC_commutation := by intro t c ht hc; cases ht
      S_eq_TC := by intro t c s ht hc hs; cases ht }
  | .AI =>
    { sig := azSignature .AI
      isValid := azSignature_isValid .AI
      T := some sigX_C
      C := none
      S := none
      T_some_iff := by simp [azSignature]
      C_some_iff := by simp [azSignature]
      S_some_iff := by simp [azSignature]
      T_law := by
        intro t ht; cases ht
        refine ⟨?_, by simpa [symSquareToInt, azSignature] using sigX_C_sq⟩
        simp [ringComm, azWitnessH]
      C_law := by intro x hx; cases hx
      S_law := by intro s hs; cases hs
      TC_commutation := by intro t c ht hc; cases hc
      S_eq_TC := by intro t c s ht hc hs; cases hc }
  | .BDI =>
    ringAZSymmetrySystem_of_TR_PH
      (A := M2C) sigX_C sigI_C sigZ_C .plus .plus (by decide) (by decide)
      (η := 1) (by norm_num)
      (by simp [ringComm_eq_zero_iff, sigI_C])
      (by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [ringAnticomm, sigX_C, sigZ_C])
      (by simp [symSquareToInt, sigI_C])
      (by simpa [symSquareToInt] using sigZ_C_sq)
      (by simp [sigI_C, sigZ_C])
      (by decide)
  | .D =>
    { sig := azSignature .D
      isValid := azSignature_isValid .D
      T := none
      C := some sigZ_C
      S := none
      T_some_iff := by simp [azSignature]
      C_some_iff := by simp [azSignature]
      S_some_iff := by simp [azSignature]
      T_law := by intro t ht; cases ht
      C_law := by
        intro x hx; cases hx
        refine ⟨?_, by simpa [symSquareToInt, azSignature] using sigZ_C_sq⟩
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [ringAnticomm, azWitnessH, sigZ_C, sigX_C]
      S_law := by intro s hs; cases hs
      TC_commutation := by intro t c ht hc; cases ht
      S_eq_TC := by intro t c s ht hc hs; cases ht }
  | .DIII =>
    ringAZSymmetrySystem_of_TR_PH
      (A := M2C) sigY_C iSigY_C sigZ_C .minus .plus (by decide) (by decide)
      (η := -1) (by norm_num)
      (by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [ringComm, iSigY_C, sigY_C])
      (by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [ringAnticomm, sigZ_C, sigY_C])
      (by simpa [symSquareToInt] using iSigY_C_sq)
      (by simpa [symSquareToInt] using sigZ_C_sq)
      (by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [iSigY_C, sigZ_C, Matrix.mul_apply, Fin.sum_univ_two])
      (by decide)
  | .AII =>
    { sig := azSignature .AII
      isValid := azSignature_isValid .AII
      T := some iSigY_C
      C := none
      S := none
      T_some_iff := by simp [azSignature]
      C_some_iff := by simp [azSignature]
      S_some_iff := by simp [azSignature]
      T_law := by
        intro t ht; cases ht
        refine ⟨?_, by simpa [symSquareToInt, azSignature] using iSigY_C_sq⟩
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [ringComm, azWitnessH, iSigY_C, sigY_C]
      C_law := by intro x hx; cases hx
      S_law := by intro s hs; cases hs
      TC_commutation := by intro t c ht hc; cases hc
      S_eq_TC := by intro t c s ht hc hs; cases hc }
  | .CII =>
    ringAZSymmetrySystem_of_TR_PH
      (A := M2C) 0 iSigY_C iSigY_C .minus .minus (by decide) (by decide)
      (η := 1) (by norm_num)
      (by simp [ringComm])
      (by simp [ringAnticomm])
      (by simpa [symSquareToInt] using iSigY_C_sq)
      (by simpa [symSquareToInt] using iSigY_C_sq)
      (by simp)
      (by decide)
  | .C =>
    { sig := azSignature .C
      isValid := azSignature_isValid .C
      T := none
      C := some iSigY_C
      S := none
      T_some_iff := by simp [azSignature]
      C_some_iff := by simp [azSignature]
      S_some_iff := by simp [azSignature]
      T_law := by intro t ht; cases ht
      C_law := by
        intro x hx; cases hx
        refine ⟨?_, by simpa [symSquareToInt, azSignature] using iSigY_C_sq⟩
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [ringAnticomm, azWitnessH, iSigY_C, sigZ_C]
      S_law := by intro s hs; cases hs
      TC_commutation := by intro t c ht hc; cases ht
      S_eq_TC := by intro t c s ht hc hs; cases ht }
  | .CI =>
    ringAZSymmetrySystem_of_TR_PH
      (A := M2C) sigX_C sigX_C iSigY_C .plus .minus (by decide) (by decide)
      (η := -1) (by norm_num)
      (by simp [ringComm])
      (by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [ringAnticomm, iSigY_C, sigX_C])
      (by simpa [symSquareToInt] using sigX_C_sq)
      (by simpa [symSquareToInt] using iSigY_C_sq)
      (by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [sigX_C, iSigY_C, Matrix.mul_apply, Fin.sum_univ_two])
      (by decide)

theorem azWitnessSystem_azClass (c : AZClass) :
    (azWitnessSystem c).azClass = c := by
  cases c <;> rfl

/-- Real `2×2` matrix-ring witness for the DIII signed relations. Its `H` is
skew-symmetric, so this algebraic witness is not a self-adjoint Hamiltonian. -/
def realDIIIRingWitness : RingAZSymmetrySystem M2R iSigY_R :=
  ringAZSymmetrySystem_of_TR_PH
    (A := M2R) iSigY_R iSigY_R sigZ_R .minus .plus (by decide) (by decide)
    (η := -1) (by norm_num)
    (by simp [ringComm])
    (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [ringAnticomm, sigZ_R, iSigY_R])
    (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [iSigY_R, symSquareToInt, Matrix.mul_apply, Fin.sum_univ_two])
    (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [sigZ_R, symSquareToInt, Matrix.mul_apply, Fin.sum_univ_two])
    (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [iSigY_R, sigZ_R, Matrix.mul_apply, Fin.sum_univ_two])
    (by decide)

theorem realDIIIRingWitness_azClass : realDIIIRingWitness.azClass = .DIII := by
  rfl

/-- Real `2×2` matrix witness for class CI (`T = σ_x`, `C = iσ_y`, `H = σ_x`). -/
def realCIWitness : RingAZSymmetrySystem M2R sigX_R :=
  ringAZSymmetrySystem_of_TR_PH
    (A := M2R) sigX_R sigX_R iSigY_R .plus .minus (by decide) (by decide)
    (η := -1) (by norm_num)
    (by simp [ringComm])
    (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [ringAnticomm, iSigY_R, sigX_R])
    (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [sigX_R, symSquareToInt, Matrix.mul_apply, Fin.sum_univ_two])
    (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [iSigY_R, symSquareToInt, Matrix.mul_apply, Fin.sum_univ_two])
    (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [sigX_R, iSigY_R, Matrix.mul_apply, Fin.sum_univ_two])
    (by decide)

theorem realCIWitness_azClass : realCIWitness.azClass = .CI := by
  dsimp [RingAZSymmetrySystem.azClass, realCIWitness, ringAZSymmetrySystem_of_TR_PH,
    azClassEquivValidSignature, ofValidSignature]

end TenfoldMatrixWitnesses

end RingAZ

end InfoGeometry.Canonical.DIIICommutatorInitialization
