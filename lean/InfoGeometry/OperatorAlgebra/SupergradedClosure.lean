import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation

namespace InfoGeometry.OperatorAlgebra.SupergradedClosure

/--
Nilpotent supercharges generate a Dirac operator whose square is the
super-Laplacian.

`D = Q + Q♯`, `Δ = Q Q♯ + Q♯ Q`, and `D² = Δ`.
-/
@[rep_depth thermo]
theorem superDirac_sq_eq_superLaplacian
    {R : Type*} [Ring R]
    {Q Qsharp : R}
    (hQ : Q * Q = 0)
    (hQsharp : Qsharp * Qsharp = 0) :
    (Q + Qsharp) * (Q + Qsharp) =
      Q * Qsharp + Qsharp * Q := by
  calc
    (Q + Qsharp) * (Q + Qsharp)
        = Q * Q + (Q * Qsharp + Qsharp * Q) + Qsharp * Qsharp := by
          noncomm_ring
    _ = 0 + (Q * Qsharp + Qsharp * Q) + 0 := by
          rw [hQ, hQsharp]
    _ = Q * Qsharp + Qsharp * Q := by
          simp

/--
The left supercharge commutes with the super-Laplacian: `[Q, Δ] = 0`.
-/
@[rep_depth thermo]
theorem supercharge_commutes_superLaplacian
    {R : Type*} [Ring R]
    {Q Qsharp : R}
    (hQ : Q * Q = 0) :
    Q * (Q * Qsharp + Qsharp * Q) =
      (Q * Qsharp + Qsharp * Q) * Q := by
  calc
    Q * (Q * Qsharp + Qsharp * Q)
        = (Q * Q) * Qsharp + Q * Qsharp * Q := by
          noncomm_ring
    _ = 0 * Qsharp + Q * Qsharp * Q := by
          rw [hQ]
    _ = Q * Qsharp * Q := by
          simp
    _ = Q * Qsharp * Q + Qsharp * (Q * Q) := by
          rw [hQ]
          simp
    _ = (Q * Qsharp + Qsharp * Q) * Q := by
          noncomm_ring

/--
The dual supercharge commutes with the super-Laplacian: `[Q♯, Δ] = 0`.
-/
@[rep_depth thermo]
theorem dualSupercharge_commutes_superLaplacian
    {R : Type*} [Ring R]
    {Q Qsharp : R}
    (hQsharp : Qsharp * Qsharp = 0) :
    Qsharp * (Q * Qsharp + Qsharp * Q) =
      (Q * Qsharp + Qsharp * Q) * Qsharp := by
  calc
    Qsharp * (Q * Qsharp + Qsharp * Q)
        = Qsharp * Q * Qsharp + (Qsharp * Qsharp) * Q := by
          noncomm_ring
    _ = Qsharp * Q * Qsharp + 0 * Q := by
          rw [hQsharp]
    _ = Qsharp * Q * Qsharp := by
          simp
    _ = Q * (Qsharp * Qsharp) + Qsharp * Q * Qsharp := by
          rw [hQsharp]
          simp
    _ = (Q * Qsharp + Qsharp * Q) * Qsharp := by
          noncomm_ring

/--
The Dirac operator commutes with its super-Laplacian: `[D, Δ] = 0`.
-/
@[rep_depth thermo]
theorem superDirac_commutes_superLaplacian
    {R : Type*} [Ring R]
    {Q Qsharp : R}
    (hQ : Q * Q = 0)
    (hQsharp : Qsharp * Qsharp = 0) :
    (Q + Qsharp) * (Q * Qsharp + Qsharp * Q) =
      (Q * Qsharp + Qsharp * Q) * (Q + Qsharp) := by
  calc
    (Q + Qsharp) * (Q * Qsharp + Qsharp * Q)
        =
      Q * (Q * Qsharp + Qsharp * Q) +
        Qsharp * (Q * Qsharp + Qsharp * Q) := by
          noncomm_ring
    _ =
      (Q * Qsharp + Qsharp * Q) * Q +
        (Q * Qsharp + Qsharp * Q) * Qsharp := by
          rw [
            supercharge_commutes_superLaplacian (Q := Q) (Qsharp := Qsharp) hQ,
            dualSupercharge_commutes_superLaplacian (Q := Q) (Qsharp := Qsharp) hQsharp
          ]
    _ =
      (Q * Qsharp + Qsharp * Q) * (Q + Qsharp) := by
          noncomm_ring

/--
Supergraded Dirac/Laplacian closure package at one degree:

* `D = Q + Q♯`
* `Δ = Q Q♯ + Q♯ Q`
* `D² = Δ`
* `[Q,Δ]=0`, `[Q♯,Δ]=0`, `[D,Δ]=0`.
-/
@[rep_depth thermo]
def SupergradedClosureAt {R : Type*} [Ring R] (Q Qsharp : R) : Prop :=
  (Q + Qsharp) * (Q + Qsharp) = (Q * Qsharp + Qsharp * Q) ∧
  Q * (Q * Qsharp + Qsharp * Q) = (Q * Qsharp + Qsharp * Q) * Q ∧
  Qsharp * (Q * Qsharp + Qsharp * Q) = (Q * Qsharp + Qsharp * Q) * Qsharp ∧
  (Q + Qsharp) * (Q * Qsharp + Qsharp * Q) =
    (Q * Qsharp + Qsharp * Q) * (Q + Qsharp)

/--
Nilpotent supercharges imply full supergraded Dirac/Laplacian closure.
-/
@[rep_depth thermo]
theorem supergradedClosureAt_of_nilpotent
    {R : Type*} [Ring R]
    {Q Qsharp : R}
    (hQ : Q * Q = 0)
    (hQsharp : Qsharp * Qsharp = 0) :
    SupergradedClosureAt (R := R) Q Qsharp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact superDirac_sq_eq_superLaplacian (Q := Q) (Qsharp := Qsharp) hQ hQsharp
  · exact supercharge_commutes_superLaplacian (Q := Q) (Qsharp := Qsharp) hQ
  · exact dualSupercharge_commutes_superLaplacian (Q := Q) (Qsharp := Qsharp) hQsharp
  · exact superDirac_commutes_superLaplacian (Q := Q) (Qsharp := Qsharp) hQ hQsharp


end InfoGeometry.OperatorAlgebra.SupergradedClosure
