import InfoGeometry.Physics.AmariSurprisalIwasawaSynthesis

namespace InfoGeometry.Physics.AmariSurprisalIwasawa

/-! The square-root embedding is faithful on the finite positive simplex. -/

theorem amplitude_map_injective
    {D : ℕ} (P Q : PositiveDist D)
    (h : ∀ i, amplitude P i = amplitude Q i) : P.p = Q.p := by
  funext i
  have hs := congrArg (fun x : ℝ => x ^ 2) (h i)
  simpa [amplitude,
    Real.sq_sqrt (le_of_lt (P.h_pos i)),
    Real.sq_sqrt (le_of_lt (Q.h_pos i))] using hs

end InfoGeometry.Physics.AmariSurprisalIwasawa
