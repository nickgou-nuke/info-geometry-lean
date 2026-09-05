import Mathlib

/-!
# Ordered transport and endpoint gauge covariance

Transport is an ordered product in a group of frame transformations. It is
not a product in a nonassociative field algebra. For a Zorn-valued payload the
chosen group must act by the appropriate structure-preserving maps.

A vertex list here is a composable chain with an explicit initial vertex.
Graph adjacency can restrict which lists are admissible; the covariance law
is valid for every list and therefore for every such restriction. No directed
cycle in a DAG is introduced by the closed-chain theorem.
-/

namespace InfoGeometry.SignedNetwork.GaugeTransport

variable {V G : Type*} [Group G]

/-- Last vertex of a chain, with a specified initial vertex for the empty chain. -/
def endpoint (start : V) : List V → V
  | [] => start
  | v :: rest => endpoint v rest

/-- Rows are destinations; the earliest transport factor acts first. -/
def transport (U : V → V → G) (start : V) : List V → G
  | [] => 1
  | v :: rest => transport U v rest * U v start

/-- Independent change of frame at every vertex. -/
def gaugeKernel (g : V → G) (U : V → V → G) (target source : V) : G :=
  g target * U target source * (g source)⁻¹

/-- All internal frame changes cancel, leaving only the endpoint frames. -/
theorem transport_gauge (g : V → G) (U : V → V → G) (start : V) (p : List V) :
    transport (gaugeKernel g U) start p =
      g (endpoint start p) * transport U start p * (g start)⁻¹ := by
  induction p generalizing start with
  | nil => simp [transport, endpoint]
  | cons v rest ih =>
      change transport (gaugeKernel g U) v rest * gaugeKernel g U v start =
        g (endpoint v rest) * (transport U v rest * U v start) * (g start)⁻¹
      rw [ih]
      simp [gaugeKernel, mul_assoc]

/-- A genuinely closed chain transforms by conjugation at its base point.
On a DAG a nontrivial such chain requires reversed edges or additional cells. -/
theorem closed_transport_gauge (g : V → G) (U : V → V → G)
    (start : V) (p : List V) (hclosed : endpoint start p = start) :
    transport (gaugeKernel g U) start p =
      g start * transport U start p * (g start)⁻¹ := by
  rw [transport_gauge, hclosed]

/-- Coherent return requires the inverse group transformation. -/
theorem transport_then_reverse (h : G) : h⁻¹ * h = 1 := inv_mul_cancel h

end InfoGeometry.SignedNetwork.GaugeTransport
