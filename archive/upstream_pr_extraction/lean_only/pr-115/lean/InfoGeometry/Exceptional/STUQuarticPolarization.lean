import InfoGeometry.Exceptional.STUFreudenthalQuarticScaling

/-!
# Explicit STU quartic polarization readout

This file records the native finite multilinear expression only.  The full
finite-difference polarization theorem is intentionally not asserted here
until its combinatorial normalization has a kernel-checked proof.
-/

noncomputable section
namespace InfoGeometry.Exceptional.STUDatum

open scoped BigOperators
open InfoGeometry.Exceptional.Freudenthal

def fin4PolarizedProduct (a b c d : Fin 4 → ℝ) : ℝ :=
  (1 / 24 : ℝ) * ∑ σ : Equiv.Perm (Fin 4),
    a (σ 0) * b (σ 1) * c (σ 2) * d (σ 3)

def stuQuarticPolarizationExplicit
    (Q : Fin 4 → FreudenthalCharge STUCarrier) : ℝ :=
  let α := fun i => (Q i).alpha
  let β := fun i => (Q i).beta
  let X := fun j i => (Q i).x j
  let Y := fun j i => (Q i).y j
  fin4PolarizedProduct α α β β -
    2 * ∑ j : Fin 3, fin4PolarizedProduct α β (X j) (Y j) +
    ∑ j : Fin 3, ∑ k : Fin 3,
      fin4PolarizedProduct (X j) (Y j) (X k) (Y k) -
    4 * fin4PolarizedProduct α (X 0) (X 1) (X 2) -
    4 * fin4PolarizedProduct β (Y 0) (Y 1) (Y 2) +
    4 * (fin4PolarizedProduct (X 1) (X 2) (Y 1) (Y 2) +
      fin4PolarizedProduct (X 0) (X 2) (Y 0) (Y 2) +
      fin4PolarizedProduct (X 0) (X 1) (Y 0) (Y 1))

def stuQuarticPolarization
    (Q : Fin 4 → FreudenthalCharge STUCarrier) : ℝ :=
  stuQuarticPolarizationExplicit Q

end InfoGeometry.Exceptional.STUDatum
