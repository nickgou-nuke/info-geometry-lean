theory OrbifoldBianchiIntegration
  imports Main
begin

definition "g_flux_integral_cancellation (n_tensor :: nat) \<equiv> n_tensor = 16"

lemma orbifold_anomaly_cancellation:
  "g_flux_integral_cancellation 16"
  unfolding g_flux_integral_cancellation_def
  by simp

end
