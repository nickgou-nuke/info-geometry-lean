import InfoGeometry.Canonical.ProjectiveCCR

set_option trace.Meta.Tactic.axiom true

theorem check_vacuum :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] 
    (Q : (E →L[ℝ] E)) (B : InfoGeometry.Canonical.ProjectiveCCR.ProjectiveBoundaryPacket Q),
    B.split.zeroMode.vacuumMode = 1 :=
  fun _ _ _ _ _ B => B.split.zeroMode.vacuum_eq_one
