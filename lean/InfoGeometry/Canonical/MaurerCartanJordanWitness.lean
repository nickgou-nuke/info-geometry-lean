import InfoGeometry.Quantum.Monodromy
import InfoGeometry.Clifford.LogCftMonodromy
import InfoGeometry.OperatorAlgebra.LogExchangeMonodromy

/-!
# InfoGeometry.Canonical.MaurerCartanJordanWitness

Finite witness-alias packet for the nilpotent/Jordan truncation corridor.

This file does not introduce new closure theory. It exposes the already-owned
finite theorems that witness the same truncation pattern:

- square-zero nilpotent correction;
- Jordan-cell power collapse;
- Hadjiivanov phase-times-nilpotent readout.

The corresponding SymPy witness is `tools/sympy/maurer_cartan_jordan_truncation.py`.
-/

noncomputable section

namespace InfoGeometry.Canonical.MaurerCartanJordanWitness

open InfoGeometry.OperatorAlgebra.LogExchangeMonodromy

/-- SymPy witness alias: square-zero nilpotent Jordan power. -/
theorem nilpotent_jordan_power
    {A : Type*} [Ring A]
    (u N : A) (h_comm : Commute u N) (h_nil : N * N = 0) (n : ℕ) :
    (u + N) ^ (n + 1) = u ^ (n + 1) + (n + 1) • (u ^ n * N) := by
  exact InfoGeometry.QuantumMonodromy.nilpotent_jordan_power u N h_comm h_nil n

/-- SymPy witness alias: Hadjiivanov monodromy power law. -/
theorem hadjiivanovMonodromy_pow_winding (h : ℂ) (n : ℕ) :
    InfoGeometry.Clifford.LogCftMonodromy.hadjiivanovMonodromy h ^ n =
      InfoGeometry.Clifford.LogCftMonodromy.lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          ((n : ℂ) * InfoGeometry.Clifford.LogCftMonodromy.logShearBase) •
            InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent) := by
  exact InfoGeometry.Clifford.LogCftMonodromy.hadjiivanovMonodromy_pow_winding h n

/-- SymPy witness alias: lower Hadjiivanov exchange block factors through the conjugated nilpotent corridor. -/
theorem lowerHadjiivanovMonodromy_pow_eq_phase_conj_componentN_bridge (h : ℂ) (n : ℕ) :
    InfoGeometry.Clifford.LogCftMonodromy.lowerHadjiivanovMonodromy h ^ n =
      InfoGeometry.Clifford.LogCftMonodromy.lcftPhase h ^ n •
        (InfoGeometry.Clifford.ModularCftBridge.modularS *
          InfoGeometry.Dynamics.KanDecomposition.componentN
            (-((n : ℂ) * InfoGeometry.Clifford.LogCftMonodromy.logShearBase)) *
          InfoGeometry.Clifford.ModularCftBridge.modularSInverse) := by
  exact lowerHadjiivanovMonodromy_pow_eq_phase_conj_componentN h n

end InfoGeometry.Canonical.MaurerCartanJordanWitness
