import Mathlib.LinearAlgebra.Projectivization.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.KreinSpace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Krein State Space (Projectivization)

This module defines the **Krein state space**, which is the projectivization of a Krein space.
It represents physical states modulo Weyl gauge symmetry (scaling by units `ℝˣ`).

It provides:
1. `KreinStateSpace`: The projectivization `ℙ ℝ H`.
2. Cones: `PositiveCone`, `NegativeCone`, `NullCone` as subsets of the state space.
3. `kreinSign`: Well-defined sign of the indefinite form on the state space.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [InfoGeometry.Krein.KreinSpace H]

namespace InfoGeometry.Krein

/-- The **Krein state space** is the projectivization of a Krein space.
This construction takes nonzero vectors modulo the action of the gauge group `ℝˣ`. -/
abbrev KreinStateSpace (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H] :=
  Projectivization ℝ H

namespace KreinStateSpace

/-- The sign of the Krein form is well-defined on the projectivization. -/
noncomputable def kreinSign (s : KreinStateSpace H) : ℝ :=
  Projectivization.lift (fun (x : {v // v ≠ 0}) => if 0 < KreinSpace.kreinQuad (x : H) then (1 : ℝ) else if KreinSpace.kreinQuad (x : H) < 0 then -1 else 0)
    (fun x y (c : ℝ) h => by
      simp only [h, KreinSpace.kreinQuad_smul]
      have hnonzero : c ≠ 0 := by
        intro hc; rw [hc, zero_smul] at h; exact x.2 h
      have hsq : 0 < c^2 := sq_pos_of_ne_zero hnonzero
      set q := KreinSpace.kreinQuad (y : H)
      split_ifs with h1 h2 h3 h4 h5 h6 <;> try rfl
      · exfalso; nlinarith
      · exfalso; nlinarith
      · exfalso; nlinarith
      · exfalso; nlinarith
      · exfalso; nlinarith
      · exfalso; nlinarith
    ) s

/-- The **positive cone** in the Krein state space. -/
def PositiveCone (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H] :
    Set (KreinStateSpace H) :=
  {s | kreinSign s = 1}

/-- The **negative cone** in the Krein state space. -/
def NegativeCone (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H] :
    Set (KreinStateSpace H) :=
  {s | kreinSign s = -1}

/-- The **null cone** (light cone) in the Krein state space. -/
def NullCone (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H] :
    Set (KreinStateSpace H) :=
  {s | kreinSign s = 0}

end KreinStateSpace

end InfoGeometry.Krein
