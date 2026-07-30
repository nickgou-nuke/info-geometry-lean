import InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

namespace InfoGeometry.Canonical.ColimitRigidityProofChainBridge

open InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

theorem tower_stage_injectivity_survival
    {V : ℕ → Type*} [∀ n, AddCommGroup (V n)] [∀ n, Module ℝ (V n)]
    (f : ∀ n, V n →ₗ[ℝ] V (n + 1)) (h_inj : ∀ n, Function.Injective (f n))
    {n : ℕ} (v : V n) (hv : v ≠ 0) :
    f n v ≠ 0 :=
  stage_injectivity_survival f h_inj v hv

end InfoGeometry.Canonical.ColimitRigidityProofChainBridge
