import Mathlib
import InfoGeometry.Algebra.HypercomplexTriad

/-!
# InfoGeometry.Canonical.HypercomplexTriadVirasoroBridge

Finite algebraic bridge between:

* a hypercomplex triad Lie lane (`J, K, N` with `N^2 = 0`), and
* a Virasoro cocycle/Casimir readout lane.

This file is theorem-safe and algebraic only. It does **not** claim analytic
completion, Type III factor classification, or a global CFT construction.
-/

namespace HypercomplexTriadVirasoroBridge

/-- Noncommutative commutator. -/
def commutator {A : Type*} [Ring A] (X Y : A) : A :=
  X * Y - Y * X

section ConcreteTriad

open InfoGeometry.Algebra.HypercomplexTriad

/-- In the concrete `2×2` real triad, `[E, N] = 2N`. -/
theorem commutator_E_N :
    commutator E N = (2 : ℝ) • N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commutator, E, N, Matrix.mul_apply, Fin.sum_univ_two]

/-- In the concrete `2×2` real triad, `[I, N] = -E`. -/
theorem commutator_I_N :
    commutator I N = -E := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commutator, I, E, N, Matrix.mul_apply, Fin.sum_univ_two]

end ConcreteTriad

section AbstractBridge

/--
Minimal Lie-triad packet for the modular nilpotent lane.

`[K, N] = λN` records the scaling of the nilpotent direction under the modular
flow generator.
-/
structure TriadLieDatum (A : Type*) [Ring A] [Module ℝ A] where
  J : A
  K : A
  N : A
  lam : ℝ
  N_sq : N * N = 0
  bracket_KN : commutator K N = lam • N
  bracket_JN_in_span : ∃ a b : ℝ, commutator J N = a • N + b • K

namespace TriadLieDatum

variable {A : Type*} [Ring A] [Module ℝ A]

/-- A nilpotent generator annihilates twice on any vacuum vector in the same algebra module. -/
theorem highestWeight_of_vacuum
    (D : TriadLieDatum A) (Ω : A)
    (hvac : D.N * Ω = 0) :
    D.N * (D.N * Ω) = 0 := by
  simpa [mul_assoc, hvac] using congrArg (fun X => X * Ω) D.N_sq

/-- Readback of the scaling law `[K, N] = λN`. -/
theorem bracket_KN_readback (D : TriadLieDatum A) :
    commutator D.K D.N = D.lam • D.N :=
  D.bracket_KN

end TriadLieDatum

/--
Finite Virasoro cocycle/Casimir packet.

The cocycle is explicit and the central charge is read back as a scalar from a
Casimir-defect datum; no analytic completion is asserted.
-/
structure VirasoroCocycleCasimirDatum (A : Type*) [Ring A] [Module ℝ A] where
  L : ℤ → A
  cocycle : ℤ → ℤ → ℝ
  centralCharge : ℝ
  virasoro_bracket :
    ∀ m n : ℤ,
      commutator (L m) (L n) =
        ((m - n : ℤ) : ℝ) • L (m + n) + (cocycle m n) • (1 : A)
  cocycle_center :
    ∀ m n : ℤ,
      cocycle m n =
        if m + n = 0 then
          (centralCharge / 12) * (m : ℝ) * ((m : ℝ) ^ 2 - 1)
        else 0
  casimirReadout : A → ℝ
  casimirDefect : ℝ
  centralCharge_eq_casimirDefect : centralCharge = casimirDefect

namespace VirasoroCocycleCasimirDatum

variable {A : Type*} [Ring A] [Module ℝ A]

/-- Central charge as Casimir-defect readback. -/
theorem centralCharge_readback
    (V : VirasoroCocycleCasimirDatum A) :
    V.centralCharge = V.casimirDefect :=
  V.centralCharge_eq_casimirDefect

/-- Exact cocycle value on opposite modes. -/
theorem cocycle_on_opposite_modes
    (V : VirasoroCocycleCasimirDatum A) (m : ℤ) :
    V.cocycle m (-m) =
      (V.centralCharge / 12) * (m : ℝ) * ((m : ℝ) ^ 2 - 1) := by
  simpa using V.cocycle_center m (-m)

/-- Virasoro bracket law at arbitrary mode pair. -/
theorem virasoro_bracket_readback
    (V : VirasoroCocycleCasimirDatum A) (m n : ℤ) :
    commutator (V.L m) (V.L n) =
      ((m - n : ℤ) : ℝ) • V.L (m + n) + (V.cocycle m n) • (1 : A) :=
  V.virasoro_bracket m n

end VirasoroCocycleCasimirDatum

/--
Bridge datum identifying the nilpotent triad generator with Virasoro `L_{-1}`.
-/
structure TriadToVirasoroBridge (A : Type*) [Ring A] [Module ℝ A] where
  triad : TriadLieDatum A
  vir : VirasoroCocycleCasimirDatum A
  N_eq_LminusOne : triad.N = vir.L (-1)

namespace TriadToVirasoroBridge

variable {A : Type*} [Ring A] [Module ℝ A]

/-- If the triad nilpotent generator annihilates a vacuum, then `L_{-1}` also annihilates it. -/
theorem LminusOne_vacuum_of_N_vacuum
    (B : TriadToVirasoroBridge A) (Ω : A)
    (hNvac : B.triad.N * Ω = 0) :
    B.vir.L (-1) * Ω = 0 := by
  simpa [B.N_eq_LminusOne] using hNvac

/-- Casimir-defect readback transported through the bridge. -/
theorem centralCharge_readback
    (B : TriadToVirasoroBridge A) :
    B.vir.centralCharge = B.vir.casimirDefect :=
  B.vir.centralCharge_eq_casimirDefect

end TriadToVirasoroBridge

end AbstractBridge

end HypercomplexTriadVirasoroBridge
