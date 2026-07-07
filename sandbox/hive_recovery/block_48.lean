/-- 
The Capstone theorem which resolves the RankDecisionSocket 
once the certificate is supplied.
-/
theorem discharge_rank_decision 
    (cert : BettiCertificate)
    (h_ambient : cert.dim_ambient = 8)
    (h_verified : cert.is_verified = true)
    (h_rank : cert.total_rank = 8) : 
    cert.total_rank * InfoGeometry.Projective.PenroseSpinTiling.spinTilingMultiplicity = 32 := by
  -- If the external Macaulay2 run certifies that the total local rank is indeed 8,
  -- this theorem formally discharges the target socket of the de Rham spine (32).
  rw [h_rank]
  rfl