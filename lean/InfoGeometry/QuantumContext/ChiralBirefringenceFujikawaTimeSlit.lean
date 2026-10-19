/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Section 117a: Fujikawa Chiral Anomaly Jacobian, Eikonal Birefringence, and Temporal Double-Slit

This module formalizes the algebraic synthesis connecting:
1. **3D Electromagnetic Vector Carrier (`Vec3 R`)**: Three-component spatial vectors supporting
   the Poynting radiation vector $\mathbf{E} \times \mathbf{B}$ and the topological Pontryagin
   density $\mathbf{E} \cdot \mathbf{B}$.
2. **Fujikawa Path-Integral Anomaly Doubling (`fujikawa_anomaly_factor_two`)**: Because
   $\{\gamma_0, \gamma_5\} = 0$, both $\psi$ and $\bar{\psi}$ transform with the same chiral
   phase $+i \alpha \gamma_5$, so their Berezinian exponents add constructively to
   $-2 \alpha (n_R - n_L) = -2 \alpha \operatorname{Ind}(D)$.
3. **Poynting–Fujikawa Electromagnetic Energy Partition (`poynting_fujikawa_energy_partition`)**:
   The 3D Lagrange identity decomposes the field norm product $\|\mathbf{E}\|^2 \|\mathbf{B}\|^2$
   into the transverse Poynting radiation flux $\|\mathbf{E} \times \mathbf{B}\|^2$ plus the square
   of the topological Fujikawa anomaly source $(\mathbf{E} \cdot \mathbf{B})^2$.
4. **Chiral Eikonal Birefringence & Sapienza Temporal Double-Slit**: In a chirally twisted medium
   with torsion/chemical potential shift $b_0$, the eikonal frequencies $\Omega_\pm = k \pm b_0$
   split by $\Omega_+ - \Omega_- = 2b_0$ with product $\Omega_+ \Omega_- = k^2 - b_0^2$, and
   destructive two-state interference produces a strictly negative Steinberg–Aharonov weak dwell
   time even when both individual channel delays are strictly positive.
-/

namespace InfoGeometry.QuantumContext.FujikawaBirefringence

variable {R : Type*} [CommRing R]

/-! ## Section 1: 3D Vector Carrier (`Vec3 R`) -/

/-- Three-component spatial field vector $(x, y, z)$. -/
@[ext]
structure Vec3 (R : Type*) where
  x : R
  y : R
  z : R
  deriving DecidableEq, Repr, Inhabited

namespace Vec3

variable {R : Type*} [CommRing R]

/-- Zero 3-vector. -/
def zero : Vec3 R := ⟨0, 0, 0⟩

/-- Canonical non-zero integer 3-vector along the $x$-axis. -/
def unitX : Vec3 ℤ := ⟨1, 0, 0⟩

/-- The canonical 3-vector `unitX` over $\mathbb{Z}$ is distinct from `zero`. -/
theorem unitX_ne_zero : unitX ≠ (zero : Vec3 ℤ) := by
  intro h
  have h1 : unitX.x = (zero : Vec3 ℤ).x := congrArg Vec3.x h
  revert h1
  decide

/-- Euclidean dot product $\mathbf{u} \cdot \mathbf{v}$. -/
def dot (u v : Vec3 R) : R :=
  u.x * v.x + u.y * v.y + u.z * v.z

/-- Euclidean exterior cross product $\mathbf{u} \times \mathbf{v}$. -/
def cross (u v : Vec3 R) : Vec3 R where
  x := u.y * v.z - u.z * v.y
  y := u.z * v.x - u.x * v.z
  z := u.x * v.y - u.y * v.x

/-- Squared Euclidean norm $\|\mathbf{u}\|^2 = \mathbf{u} \cdot \mathbf{u}$. -/
def sq (u : Vec3 R) : R :=
  dot u u

/-- Non-commutativity of the 3D cross product over $\mathbb{Z}$. -/
theorem cross_noncommutative_int :
    let u : Vec3 ℤ := ⟨1, 0, 0⟩
    let v : Vec3 ℤ := ⟨0, 1, 0⟩
    cross u v ≠ cross v u := by
  decide

end Vec3

/-! ## Section 2: Fujikawa Path-Integral Jacobian & Atiyah–Singer Chiral Index -/

/-- Chiral zero-mode multiplicities $(n_R, n_L)$ of the Dirac operator. -/
@[ext]
structure ChiralZeroModes (R : Type*) where
  n_R : R
  n_L : R
  deriving DecidableEq, Repr, Inhabited

namespace ChiralZeroModes

variable {R : Type*} [CommRing R]

/-- Zero chiral zero-mode configuration. -/
def zero : ChiralZeroModes R := ⟨0, 0⟩

/-- Canonical chiral zero-mode configuration with unit right-handed excess over $\mathbb{Z}$. -/
def unitRightMode : ChiralZeroModes ℤ := ⟨1, 0⟩

/-- The canonical configuration `unitRightMode` over $\mathbb{Z}$ is distinct from `zero`. -/
theorem unitRightMode_ne_zero : unitRightMode ≠ (zero : ChiralZeroModes ℤ) := by
  intro h
  have h1 : unitRightMode.n_R = (zero : ChiralZeroModes ℤ).n_R :=
    congrArg ChiralZeroModes.n_R h
  revert h1
  decide

end ChiralZeroModes

/-- Atiyah–Singer analytical chiral index $\operatorname{Ind}(D) = n_R - n_L$. -/
def atiyahSingerIndex (M : ChiralZeroModes R) : R :=
  M.n_R - M.n_L

/-- Fujikawa path-integral measure exponent summing the equal-sign Berezinian shifts of
    $\psi \mapsto e^{i\alpha\gamma_5}\psi$ and $\bar{\psi} \mapsto \bar{\psi} e^{i\alpha\gamma_5}$. -/
def fujikawaMeasureExponent (α : R) (M : ChiralZeroModes R) : R :=
  (- α * (M.n_R - M.n_L)) + (- α * (M.n_R - M.n_L))

/-- **Fujikawa Chiral Anomaly Doubling Identity (1979)**:
    The path-integral measure exponent equals $-2 \alpha \operatorname{Ind}(D)$. -/
theorem fujikawa_anomaly_factor_two (α : R) (M : ChiralZeroModes R) :
    fujikawaMeasureExponent α M = - 2 * α * atiyahSingerIndex M := by
  dsimp [fujikawaMeasureExponent, atiyahSingerIndex]
  ring

/-! ## Section 3: Poynting–Fujikawa Electromagnetic Energy Partition -/

/-- Topological Pontryagin chiral source density $\mathbf{E} \cdot \mathbf{B}$. -/
def pontryaginSource (E B : Vec3 R) : R :=
  Vec3.dot E B

/-- Squared norm of the Poynting radiation vector $\|\mathbf{E} \times \mathbf{B}\|^2$. -/
def poyntingSq (E B : Vec3 R) : R :=
  Vec3.sq (Vec3.cross E B)

/-- **Poynting–Fujikawa Electromagnetic Energy Partition**:
    The product of the squared electric and magnetic field norms decomposes into the transverse
    Poynting radiation flux $\|\mathbf{E} \times \mathbf{B}\|^2$ plus the square of the topological
    Fujikawa anomaly source $(\mathbf{E} \cdot \mathbf{B})^2$. -/
theorem poynting_fujikawa_energy_partition (E B : Vec3 R) :
    poyntingSq E B + (pontryaginSource E B) ^ 2 = Vec3.sq E * Vec3.sq B := by
  dsimp [poyntingSq, pontryaginSource, Vec3.sq, Vec3.dot, Vec3.cross]
  ring

/-! ## Section 4: Chiral Eikonal Birefringence & Steinberg–Aharonov Negative Dwell Time -/

/-- Right-circular eikonal frequency $\Omega_+ = k + b_0$ in a chirally twisted medium. -/
def eikonalOmegaPlus (k b₀ : R) : R := k + b₀

/-- Left-circular eikonal frequency $\Omega_- = k - b_0$ in a chirally twisted medium. -/
def eikonalOmegaMinus (k b₀ : R) : R := k - b₀

/-- **Sapienza Temporal Double-Slit Frequency Splitting**:
    The frequency splitting between the right- and left-circular eikonal branches equals twice
    the chiral torsion parameter $2b_0$. -/
theorem chiral_birefringence_frequency_split (k b₀ : R) :
    eikonalOmegaPlus k b₀ - eikonalOmegaMinus k b₀ = 2 * b₀ := by
  dsimp [eikonalOmegaPlus, eikonalOmegaMinus]
  ring

/-- **Chiral Eikonal Dispersion Product**:
    The product of the two birefringent eikonal frequencies yields the relativistic dispersion
    relation $\Omega_+ \Omega_- = k^2 - b_0^2$ with tachyonic mass-squared shift $-b_0^2$. -/
theorem chiral_eikonal_dispersion_product (k b₀ : R) :
    eikonalOmegaPlus k b₀ * eikonalOmegaMinus k b₀ = k ^ 2 - b₀ ^ 2 := by
  dsimp [eikonalOmegaPlus, eikonalOmegaMinus]
  ring

/-- Two-state weak dwell-time numerator $A_+ \tau_+ + A_- \tau_-$ across the two birefringent channels. -/
def weakDwellTimeNumerator (A_plus A_minus τ_plus τ_minus : R) : R :=
  A_plus * τ_plus + A_minus * τ_minus

/-- **Steinberg–Aharonov Negative Dwell Time from Strictly Positive Channel Delays**:
    Even when both birefringent transit delays are strictly positive ($\tau_+ = 1 > 0$ and
    $\tau_- = 2 > 0$), destructive two-state interference ($A_+ = 3, A_- = -2$ with $A_+ + A_- = 1$)
    yields a strictly negative net weak dwell time $\tau_{\mathrm{weak}} = -1 < 0$. -/
theorem steinberg_negative_dwell_time_from_positive_delays :
    let A_plus  : ℤ := 3
    let A_minus : ℤ := -2
    let τ_plus  : ℤ := 1
    let τ_minus : ℤ := 2
    τ_plus > 0 ∧
    τ_minus > 0 ∧
    A_plus + A_minus = 1 ∧
    weakDwellTimeNumerator A_plus A_minus τ_plus τ_minus = -1 ∧
    weakDwellTimeNumerator A_plus A_minus τ_plus τ_minus < 0 := by
  dsimp [weakDwellTimeNumerator]
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

end InfoGeometry.QuantumContext.FujikawaBirefringence
