import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.BostConnesCrossedProduct

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {R : Type*} [CommRing R]

def crossedProductRelation (Sp : R) (A alphaA : R) : Prop :=
  Sp * A = alphaA * Sp

def cyclotomicPhase (r : ℚ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((r : ℝ) : ℂ))

theorem cyclotomic_phase_add (r1 r2 : ℚ) :
    cyclotomicPhase (r1 + r2) = cyclotomicPhase r1 * cyclotomicPhase r2 := by
  unfold cyclotomicPhase
  rw [← Complex.exp_add]
  have : 2 * Real.pi * Complex.I * (((r1 + r2 : ℚ) : ℝ) : ℂ) =
         2 * Real.pi * Complex.I * ((r1 : ℝ) : ℂ) +
         2 * Real.pi * Complex.I * ((r2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this]

theorem galois_crossed_product_equivariance
    (g : R →+* R) (alpha : R →+* R) (Sp A : R)
    (h_comm : ∀ x, g (alpha x) = alpha (g x))
    (h_rel : crossedProductRelation Sp A (alpha A)) :
    crossedProductRelation (g Sp) (g A) (alpha (g A)) := by
  unfold crossedProductRelation at *
  calc
    g Sp * g A = g (Sp * A) := (map_mul g Sp A).symm
    _ = g (alpha A * Sp) := by rw [h_rel]
    _ = g (alpha A) * g Sp := map_mul g (alpha A) Sp
    _ = alpha (g A) * g Sp := by rw [h_comm]

theorem grand_bost_connes_crossed_product_synthesis
    (g alpha : R →+* R) (Sp A : R) (r1 r2 : ℚ)
    (h_comm : ∀ x, g (alpha x) = alpha (g x))
    (h_rel : crossedProductRelation Sp A (alpha A)) :
    (cyclotomicPhase (r1 + r2) = cyclotomicPhase r1 * cyclotomicPhase r2) ∧
    (crossedProductRelation (g Sp) (g A) (alpha (g A))) :=
  ⟨cyclotomic_phase_add r1 r2,
   galois_crossed_product_equivariance g alpha Sp A h_comm h_rel⟩
