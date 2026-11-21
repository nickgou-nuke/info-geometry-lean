/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
