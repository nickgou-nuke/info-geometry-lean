    ∃ y : Obs,
      flow.flow t x * y = 1 ∧ y * flow.flow t x = 1 := by
  rcases hInv with ⟨y, hxy, hyx⟩
  refine ⟨flow.flow t y, ?_, ?_⟩
  · calc
      flow.flow t x * flow.flow t y = flow.flow t (x * y) := by
        exact ((flow.flow t).map_mul x y).symm
      _ = flow.flow t 1 := by rw [hxy]
      _ = 1 := by
        exact (flow.flow t).map_one
  · calc
      flow.flow t y * flow.flow t x = flow.flow t (y * x) := by
        exact ((flow.flow t).map_mul y x).symm
      _ = flow.flow t 1 := by rw [hyx]
      _ = 1 := by
        exact (flow.flow t).map_one

/--
Drazin inverse covariance under modular transport, as an explicit certificate.

The repo `ModularFlow` is a ring-equivalence flow, but it is not a star-flow in
this socket.  Therefore this packet records the transported Drazin law without
claiming transported self-adjointness of the support.
-/
@[rep_depth operator]
structure DrazinTransportCertificate
    (Obs : Type*) [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (t : ℝ) where
  transported_True :
    IsDrazinInverse (flow.flow t D.A) (flow.flow t D.AD) D.index

/--
The transported Drazin support is the modular image of the original support.

This is the formal version of `p_{σₜ(A)} = σₜ(p_A)` at the support level.
-/
@[rep_depth operator]
theorem transported_support_eq_moving_boundary
    {Obs : Type*} [Ring Obs] [Star Obs]
    (flow : ModularFlow Obs)
    (D : DrazinSupportData Obs)
    (t : ℝ) :
    flow.flow t D.A * flow.flow t D.AD =
      movingDrazinBoundary flow D t := by
  unfold movingDrazinBoundary
  rw [D.p_def]
  exact ((flow.flow t).map_mul D.A D.AD).symm

/--