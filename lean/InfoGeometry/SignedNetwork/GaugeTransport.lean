import Mathlib
namespace InfoGeometry.SignedNetwork.GaugeTransport
variable {V G : Type*} [Group G]
def endpoint (start : V) : List V → V | [] => start | v :: xs => endpoint v xs
def transport (U : V → V → G) (start : V) : List V → G
  | [] => 1
  | v :: xs => transport U v xs * U v start
def gaugeKernel (g : V → G) (U : V → V → G) (v u : V) : G :=
  g v * U v u * (g u)⁻¹
theorem transport_gauge (g : V → G) (U : V → V → G) (start : V) (p : List V) :
    transport (gaugeKernel g U) start p =
      g (endpoint start p) * transport U start p * (g start)⁻¹ := by
  induction p generalizing start with
  | nil => simp [transport, endpoint]
  | cons v p ih =>
      simp only [transport, endpoint]
      rw [ih]
      simp only [gaugeKernel]
      group
end InfoGeometry.SignedNetwork.GaugeTransport
