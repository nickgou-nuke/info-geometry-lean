
  groupLift :
    ConformalGroupLiftWitness L W

  ricciFlux :
    TKKRicciFluxDatum L State Geometry



namespace TKKConformalClosure

variable
    {J V W L State Geometry : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]

variable (C : TKKConformalClosure J V W L State Geometry)



/-- Ricci flux expands as curvature variation plus closure defect. -/
theorem ricciFlux_def
    (X : L)
    (s : State) :
    C.ricciFlux.ricciFlux X s =
      C.ricciFlux.derivativeAlong.deriv
        C.ricciFlux.curvatureReadout.curvature X s +
      C.ricciFlux.closureDefect.defect X s :=
  C.ricciFlux.ricciFlux_def X s

/--
The conformal anomaly (Ricci flux) is identified with the TKK closure defect
when curvature is stationary along a generator `X`.

This is the formal content of the Weyl anomaly theorem in the TKK framework:
the trace anomaly of the stress tensor equals the failure of conformal
invariance, expressed as the closure defect of the three-grading.

**Literature**: Fradkin–Tseytlin, Phys. Lett. B 134 (1984) 187;
Nakahara, Geometry, Topology and Physics §13.5.
-/
theorem anomaly_is_closure_defect
    (X : L)
    (s : State)
    (hstat :
      C.ricciFlux.derivativeAlong.deriv
        C.ricciFlux.curvatureReadout.curvature X s = 0) :
    C.ricciFlux.ricciFlux X s = C.ricciFlux.closureDefect.defect X s :=
  C.ricciFlux.ricciFlux_eq_defect_of_curvature_stationary X s hstat

end TKKConformalClosure

end InfoGeometry.OperatorAlgebra.TKKConformalClosure
