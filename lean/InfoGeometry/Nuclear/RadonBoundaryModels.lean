/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Nuclear.DiffusionParameters

/-!
# Two-reservoir and Robin boundary profiles

This module constructs a two-parameter family of actual twice differentiable
solutions; it does not assert completeness or uniqueness of all ODE solutions.
Concentration uses the pore-gas convention and flux is `-B * C'`, with `B`
the bulk flux coefficient, rather than the storage-divided diffusivity.

The normalized Robin profile uses `cosh + beta * sinh`, where a physical
zero-exterior-concentration boundary has `h = B * k * beta`. This covers
nonnegative `beta`, including Neumann at zero and exponential decay at one.
A positive shifted sinh gives only `beta > 1`; it is not a representation
of every passive Robin boundary. No dual-porosity mechanism or large-shift
limit is inferred. A fixed-amplitude shift does not have a finite limit;
the fixed-inlet large-shift limit is not claimed as a theorem here.
-/

noncomputable section

namespace InfoGeometry.Nuclear.RadonBoundaryModels

open InfoGeometry.Nuclear.RadonDiffusionProfiles
open InfoGeometry.Nuclear.DiffusionParameters

/-- The two hyperbolic basis coefficients are independent real parameters. -/
def combinedProfile (a b k L x : ℝ) : ℝ :=
  sinhProfile a k L x + coshProfile b k L x

theorem hasDerivAt_combinedProfile (a b k L x : ℝ) :
    HasDerivAt (combinedProfile a b k L) (-k * combinedProfile b a k L x) x := by
  apply ((hasDerivAt_sinhProfile a k L x).add
    (hasDerivAt_coshProfile b k L x)).congr_deriv
  unfold combinedProfile
  ring

theorem deriv_combinedProfile (a b k L : ℝ) :
    deriv (combinedProfile a b k L) = fun x => -k * combinedProfile b a k L x := by
  funext x
  exact (hasDerivAt_combinedProfile a b k L x).deriv

theorem deriv2_combinedProfile (a b k L x : ℝ) :
    deriv (deriv (combinedProfile a b k L)) x = k ^ 2 * combinedProfile a b k L x := by
  rw [deriv_combinedProfile]
  convert ((hasDerivAt_combinedProfile b a k L x).const_mul (-k)).deriv using 1
  ring

theorem combinedProfile_solves (a b k L D lambda : ℝ) (hrel : D * k ^ 2 = lambda) :
    SolvesDiffusionDecay D lambda (combinedProfile a b k L) := by
  refine ⟨fun x => (hasDerivAt_combinedProfile a b k L x).differentiableAt, ?_, ?_⟩
  · rw [deriv_combinedProfile]
    exact fun x => ((hasDerivAt_combinedProfile b a k L x).const_mul (-k)).differentiableAt
  · intro x
    rw [deriv2_combinedProfile, ← mul_assoc, hrel, sub_self]

@[simp] theorem combinedProfile_outlet (a b k L : ℝ) :
    combinedProfile a b k L L = b := by
  simp [combinedProfile, sinhProfile, coshProfile]

/-- Outward diffusive flux at the right endpoint, in the pore-gas convention. -/
def outletFlux (B : ℝ) (C : ℝ → ℝ) (L : ℝ) : ℝ := -B * deriv C L

theorem combinedProfile_outletFlux (B a b k L : ℝ) :
    outletFlux B (combinedProfile a b k L) L = B * k * a := by
  simp [outletFlux, deriv_combinedProfile, combinedProfile_outlet] <;> ring

/-- A Robin endpoint is exactly a relation between the two basis coefficients. -/
theorem robin_coefficient_iff (B h a b k L : ℝ) :
    outletFlux B (combinedProfile a b k L) L = h * combinedProfile a b k L L ↔
      B * k * a = h * b := by
  rw [combinedProfile_outletFlux, combinedProfile_outlet]

/-- With a specified ambient reservoir, the driving concentration difference
enters the boundary condition; it is not an additive interior source. -/
theorem robin_ambient_coefficient_iff (B h ambient a b k L : ℝ) :
    outletFlux B (combinedProfile a b k L) L =
        h * (combinedProfile a b k L L - ambient) ↔
      B * k * a = h * (b - ambient) := by
  rw [combinedProfile_outletFlux, combinedProfile_outlet]

/-- A perfect sink has zero endpoint concentration and strictly positive outgoing
flux. The Robin constitutive law is an additional assumption about the boundary. -/
theorem dirichlet_zero_value_positive_flux (C0 B k L : ℝ)
    (hC0 : 0 < C0) (hB : 0 < B) (hk : 0 < k) (hL : 0 < L) :
    dirichletProfile C0 k L L = 0 ∧
      0 < outletFlux B (dirichletProfile C0 k L) L := by
  refine ⟨dirichlet_outlet C0 k L, ?_⟩
  have hf : dirichletProfile C0 k L =
      combinedProfile (C0 / Real.sinh (k * L)) 0 k L := by
    funext x
    simp [dirichletProfile, combinedProfile, coshProfile]
  rw [hf, combinedProfile_outletFlux]
  exact mul_pos (mul_pos hB hk)
    (div_pos hC0 (Real.sinh_pos_iff.mpr (mul_pos hk hL)))

/-- Outlet flux of the normalized fixed-inlet, zero-outlet profile. -/
theorem dirichlet_outletFlux (B C0 k L : ℝ) :
    outletFlux B (dirichletProfile C0 k L) L =
      B * k * (C0 / Real.sinh (k * L)) := by
  unfold outletFlux dirichletProfile
  rw [deriv_sinhProfile]
  simp [coshProfile] <;> ring

theorem linearDirichlet_outletFlux (B C0 L : ℝ) :
    outletFlux B (linearDirichlet C0 L) L = B * C0 / L := by
  simp [outletFlux, deriv_linearDirichlet] <;> ring

/-- The transmission factor compares actual outlet fluxes for the same inlet,
bulk flux coefficient, length, and perfect-sink outlet. It is not an endpoint
evaluation of the concentration quotient, which is zero divided by zero. -/
theorem dirichlet_linear_outletFlux_ratio (B C0 k L : ℝ)
    (hB : B ≠ 0) (hC0 : C0 ≠ 0) (hL : L ≠ 0)
    (hs : Real.sinh (k * L) ≠ 0) :
    outletFlux B (dirichletProfile C0 k L) L /
      outletFlux B (linearDirichlet C0 L) L = k * L / Real.sinh (k * L) := by
  rw [dirichlet_outletFlux, linearDirichlet_outletFlux]
  field_simp [hB, hC0, hL, hs] <;> ring

/-- Two prescribed reservoir concentrations, represented in the outlet basis. -/
def twoReservoir (Cin Cout k L : ℝ) : ℝ → ℝ :=
  combinedProfile ((Cin - Cout * Real.cosh (k * L)) / Real.sinh (k * L)) Cout k L

theorem twoReservoir_inlet (Cin Cout k L : ℝ) (hs : Real.sinh (k * L) ≠ 0) :
    twoReservoir Cin Cout k L 0 = Cin := by
  simp only [twoReservoir, combinedProfile, sinhProfile, coshProfile, sub_zero]
  field_simp [hs] <;> ring

@[simp] theorem twoReservoir_outlet (Cin Cout k L : ℝ) :
    twoReservoir Cin Cout k L L = Cout := by
  simp [twoReservoir]

theorem twoReservoir_solves (Cin Cout k L D lambda : ℝ)
    (hrel : D * k ^ 2 = lambda) :
    SolvesDiffusionDecay D lambda (twoReservoir Cin Cout k L) :=
  combinedProfile_solves _ _ _ _ _ _ hrel

/-- The outlet-basis construction equals the standard two-reservoir formula. -/
theorem twoReservoir_formula (Cin Cout k L x : ℝ) (hs : Real.sinh (k * L) ≠ 0) :
    twoReservoir Cin Cout k L x =
      Cin * Real.sinh (k * (L - x)) / Real.sinh (k * L) +
        Cout * Real.sinh (k * x) / Real.sinh (k * L) := by
  have hx : Real.sinh (k * x) =
      Real.sinh (k * L) * Real.cosh (k * (L - x)) -
        Real.cosh (k * L) * Real.sinh (k * (L - x)) := by
    rw [show k * x = k * L - k * (L - x) by ring, Real.sinh_sub]
  unfold twoReservoir combinedProfile sinhProfile coshProfile
  rw [hx]
  field_simp [hs] <;> ring

def robinDenominator (beta k L : ℝ) : ℝ :=
  Real.cosh (k * L) + beta * Real.sinh (k * L)

/-- Same-inlet normalized Robin family, with `beta = h / (B * k)` physically. -/
def robinProfile (C0 beta k L : ℝ) : ℝ → ℝ :=
  combinedProfile (C0 * beta / robinDenominator beta k L)
    (C0 / robinDenominator beta k L) k L

theorem robinProfile_formula (C0 beta k L x : ℝ) :
    robinProfile C0 beta k L x =
      C0 * (Real.cosh (k * (L - x)) + beta * Real.sinh (k * (L - x))) /
        robinDenominator beta k L := by
  unfold robinProfile combinedProfile sinhProfile coshProfile
  ring

theorem robinDenominator_pos (beta k L : ℝ)
    (hbeta : 0 ≤ beta) (hk : 0 ≤ k) (hL : 0 ≤ L) :
    0 < robinDenominator beta k L := by
  unfold robinDenominator
  exact add_pos_of_pos_of_nonneg (Real.cosh_pos _)
    (mul_nonneg hbeta (Real.sinh_nonneg_iff.mpr (mul_nonneg hk hL)))

theorem robinProfile_inlet (C0 beta k L : ℝ)
    (hden : robinDenominator beta k L ≠ 0) :
    robinProfile C0 beta k L 0 = C0 := by
  rw [robinProfile_formula]
  simp only [sub_zero]
  change C0 * robinDenominator beta k L / robinDenominator beta k L = C0
  field_simp [hden]

theorem robinProfile_solves (C0 beta k L D lambda : ℝ) (hrel : D * k ^ 2 = lambda) :
    SolvesDiffusionDecay D lambda (robinProfile C0 beta k L) :=
  combinedProfile_solves _ _ _ _ _ _ hrel

/-- The actual endpoint flux has mass-transfer coefficient `B * k * beta`. -/
theorem robinProfile_boundary (C0 beta k L B : ℝ) :
    outletFlux B (robinProfile C0 beta k L) L =
      (B * k * beta) * robinProfile C0 beta k L L := by
  unfold robinProfile
  rw [combinedProfile_outletFlux, combinedProfile_outlet]
  ring

@[simp] theorem robinProfile_zero (C0 k L : ℝ) :
    robinProfile C0 0 k L = neumannProfile C0 k L := by
  funext x
  simp [robinProfile, robinDenominator, combinedProfile, sinhProfile,
    coshProfile, neumannProfile]

/-- Unit dimensionless outlet conductance gives the exact exponential profile. -/
theorem robinProfile_one (C0 k L : ℝ) :
    robinProfile C0 1 k L = expProfile C0 k := by
  funext x
  rw [robinProfile_formula]
  simp only [robinDenominator, one_mul, Real.cosh_add_sinh]
  unfold expProfile
  rw [show k * (L - x) = k * L + -k * x by ring, Real.exp_add]
  field_simp [Real.exp_ne_zero (k * L)] <;> ring

/-- A real positive spatial shift moves the sinh zero beyond the endpoint. -/
def shiftedSinh (A k L delta : ℝ) : ℝ → ℝ := sinhProfile A k (L + delta)

theorem shiftedSinh_expansion (A k L delta : ℝ) :
    shiftedSinh A k L delta =
      combinedProfile (A * Real.cosh (k * delta)) (A * Real.sinh (k * delta)) k L := by
  funext x
  unfold shiftedSinh combinedProfile sinhProfile coshProfile
  rw [show k * (L + delta - x) = k * (L - x) + k * delta by ring, Real.sinh_add]
  ring

/-- Cancel the nonzero amplitude in the exact shifted-sinh Robin condition. -/
theorem shiftedSinh_robin_iff (A B k L delta h : ℝ) (hA : A ≠ 0) :
    outletFlux B (shiftedSinh A k L delta) L = h * shiftedSinh A k L delta L ↔
      B * k * Real.cosh (k * delta) = h * Real.sinh (k * delta) := by
  rw [shiftedSinh_expansion, robin_coefficient_iff]
  constructor
  · intro hc
    apply mul_left_cancel₀ hA
    calc
      A * (B * k * Real.cosh (k * delta)) =
          B * k * (A * Real.cosh (k * delta)) := by ring
      _ = h * (A * Real.sinh (k * delta)) := hc
      _ = A * (h * Real.sinh (k * delta)) := by ring
  · intro hc
    calc
      B * k * (A * Real.cosh (k * delta)) =
          A * (B * k * Real.cosh (k * delta)) := by ring
      _ = A * (h * Real.sinh (k * delta)) := by rw [hc]
      _ = h * (A * Real.sinh (k * delta)) := by ring

/-- The shift parameter satisfies the tanh relation, when the stated Robin condition holds. -/
theorem shiftedSinh_tanh_relation (A B k L delta h : ℝ)
    (hA : A ≠ 0) (hh : h ≠ 0)
    (hrobin : outletFlux B (shiftedSinh A k L delta) L =
      h * shiftedSinh A k L delta L) :
    Real.tanh (k * delta) = B * k / h := by
  have hc := (shiftedSinh_robin_iff A B k L delta h hA).mp hrobin
  rw [Real.tanh_eq_sinh_div_cosh]
  apply (div_eq_div_iff (ne_of_gt (Real.cosh_pos _)) hh).mpr
  calc
    Real.sinh (k * delta) * h = h * Real.sinh (k * delta) := mul_comm _ _
    _ = B * k * Real.cosh (k * delta) := hc.symm

/-- Positive shifts represent only outlet conductances above the critical value `B*k`. -/
theorem shiftedSinh_robin_gt (A B k L delta h : ℝ)
    (hA : A ≠ 0) (hB : 0 < B) (hk : 0 < k) (hdelta : 0 < delta)
    (hrobin : outletFlux B (shiftedSinh A k L delta) L =
      h * shiftedSinh A k L delta L) : B * k < h := by
  have hc := (shiftedSinh_robin_iff A B k L delta h hA).mp hrobin
  have hs : 0 < Real.sinh (k * delta) := Real.sinh_pos_iff.mpr (mul_pos hk hdelta)
  apply (mul_lt_mul_iff_left₀ hs).mp
  calc
    (B * k) * Real.sinh (k * delta) < (B * k) * Real.cosh (k * delta) :=
      mul_lt_mul_of_pos_left (Real.sinh_lt_cosh (x := k * delta)) (mul_pos hB hk)
    _ = h * Real.sinh (k * delta) := hc

/-- A decomposition that separates the exponential ratio from its positive correction. -/
theorem sinh_add_exponential_decomposition (u v : ℝ) :
    Real.sinh (u + v) =
      Real.exp v * Real.sinh u + Real.exp (-u) * Real.sinh v := by
  rw [Real.sinh_add, ← Real.cosh_add_sinh v, ← Real.cosh_sub_sinh u]
  ring

/-- A positive shifted-sinh adjacent ratio strictly exceeds the equal-step
exponential ratio. Increasing the positive shift cannot turn this into a
ratio below `exp v`. -/
theorem exp_lt_sinh_step_ratio (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    Real.exp v < Real.sinh (u + v) / Real.sinh u := by
  apply (lt_div_iff₀ (Real.sinh_pos_iff.mpr hu)).mpr
  rw [sinh_add_exponential_decomposition]
  have hpos : 0 < Real.exp (-u) * Real.sinh v :=
    mul_pos (Real.exp_pos _) (Real.sinh_pos_iff.mpr hv)
  linarith

end InfoGeometry.Nuclear.RadonBoundaryModels
