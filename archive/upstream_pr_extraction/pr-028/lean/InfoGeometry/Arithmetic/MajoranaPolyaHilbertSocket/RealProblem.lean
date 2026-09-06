noncomputable section

namespace InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket

/-! ## 2. Real Majorana--Berry--Keating operator problem -/

/--
Finite-cutoff real Majorana--Berry--Keating operator problem.

This names the combined operator

`D_Λ = H_BK ⊗ 1 + ρ ⊗ Q_Λ`

without pretending to construct its analytic closure.  The square law is
separate witness data; it depends on the anticommutation of `ρ` with the real
Berry--Keating block and on the Dirac-square law for `Q_Λ`.
-/
structure RealMajoranaBerryKeatingProblem
    (Carrier Operator Mode Cutoff : Type) where
  carrier : Carrier
  cutoff : Cutoff
  realBerryKeatingBlock : Operator
  chiralityRho : Operator
  majoranaDiracCutoff : Operator
  combinedDirac : Operator
  modeEnergyCoefficient : Mode → ℝ

namespace RealMajoranaBerryKeatingProblem

end RealMajoranaBerryKeatingProblem

end InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket
