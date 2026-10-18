/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Section 118: Axion Gauge Term, Weyl Semimetals, and Chiral Birefringence

This module formalizes Carroll–Field–Jackiw axion electrodynamics in Weyl semimetals and
chirally twisted media:
1. **3D Electromagnetic & Axion Field Carrier (`Vec3 R`)**: Three-component spatial vectors
   for the electric field $\mathbf{E}$, magnetic field $\mathbf{B}$, and Weyl node separation $\mathbf{b}$.
2. **Lagrange–Poynting–Fujikawa Decomposition (`poynting_fujikawa_lagrange_identity`)**:
   $\|\mathbf{E} \times \mathbf{B}\|^2 + (\mathbf{E} \cdot \mathbf{B})^2 = \|\mathbf{E}\|^2 \|\mathbf{B}\|^2$.
3. **Topological Axion Current & Joule Power Law**: The total axion current
   $\mathbf{J}_{\mathrm{axion}} = b_0 \mathbf{B} + \mathbf{b} \times \mathbf{E}$ combines the
   Chiral Magnetic Effect (CME) and the Anomalous Hall Effect (AHE). The AHE current is
   strictly dissipationless ($\mathbf{E} \cdot (\mathbf{b} \times \mathbf{E}) = 0$), so the entire
   Joule power injection equals the Fujikawa–Pontryagin source
   $\mathbf{E} \cdot \mathbf{J}_{\mathrm{axion}} = b_0 (\mathbf{E} \cdot \mathbf{B})$.
4. **Phase-Velocity Birefringence Splitting & Tachyonic Zitterbewegung Threshold**:
   For $k v_\pm = \Omega_\pm = k \pm b_0$, the phase velocities satisfy $k(v_+ - v_-) = 2b_0$,
   and in the subcritical momentum regime $k^2 < b_0^2$, the dispersion product is strictly
   negative ($\Omega_+ \Omega_- = k^2 - b_0^2 < 0$).
-/

namespace InfoGeometry.QuantumContext.AxionBirefringence

variable {R : Type*} [CommRing R]

/-! ## Section 1: 3D Vector Carrier for Electromagnetic and Axion Fields (`Vec3 R`) -/

/-- Three-component spatial vector $(x, y, z)$. -/
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

/-- Canonical non-zero integer 3-vector along the $y$-axis. -/
def unitY : Vec3 ℤ := ⟨0, 1, 0⟩

/-- The canonical 3-vector `unitY` over $\mathbb{Z}$ is distinct from `zero`. -/
theorem unitY_ne_zero : unitY ≠ (zero : Vec3 ℤ) := by
  intro h
  have h1 : unitY.y = (zero : Vec3 ℤ).y := congrArg Vec3.y h
  revert h1
  decide

/-- Componentwise addition of 3-vectors. -/
def add (u v : Vec3 R) : Vec3 R :=
  ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

/-- Scalar multiplication on a 3-vector. -/
def smul (c : R) (u : Vec3 R) : Vec3 R :=
  ⟨c * u.x, c * u.y, c * u.z⟩

/-- Euclidean dot product $\mathbf{u} \cdot \mathbf{v}$. -/
def dot (u v : Vec3 R) : R :=
  u.x * v.x + u.y * v.y + u.z * v.z

/-- Euclidean cross product $\mathbf{u} \times \mathbf{v}$. -/
def cross (u v : Vec3 R) : Vec3 R where
  x := u.y * v.z - u.z * v.y
  y := u.z * v.x - u.x * v.z
  z := u.x * v.y - u.y * v.x

/-- Squared Euclidean norm $\|\mathbf{u}\|^2 = \mathbf{u} \cdot \mathbf{u}$. -/
def sq (u : Vec3 R) : R :=
  dot u u

/-- Orthogonality of a cross product with its second factor: $\mathbf{v} \cdot (\mathbf{u} \times \mathbf{v}) = 0$. -/
@[simp]
theorem dot_cross_self_right (u v : Vec3 R) : dot v (cross u v) = 0 := by
  dsimp [dot, cross]
  ring

/-- Non-commutativity of the 3D cross product over $\mathbb{Z}$. -/
theorem cross_noncommutative_int :
    let u : Vec3 ℤ := ⟨1, 0, 0⟩
    let v : Vec3 ℤ := ⟨0, 1, 0⟩
    cross u v ≠ cross v u := by
  decide

end Vec3

/-! ## Section 2: Axion Gauge Term and Poynting–Fujikawa Decomposition -/

/-- Topological Fujikawa–Pontryagin invariant $\mathbf{E} \cdot \mathbf{B}$. -/
def pontryaginInvariant (E B : Vec3 R) : R :=
  Vec3.dot E B

/-- Axion gauge density $\mathcal{L}_{\mathrm{axion}} = \theta (\mathbf{E} \cdot \mathbf{B})$ in the effective Lagrangian. -/
def axionGaugeTerm (θ : R) (E B : Vec3 R) : R :=
  θ * pontryaginInvariant E B

/-- Poynting radiation vector $\mathbf{S} = \mathbf{E} \times \mathbf{B}$. -/
def poyntingVector (E B : Vec3 R) : Vec3 R :=
  Vec3.cross E B

/-- **Lagrange–Poynting–Fujikawa Decomposition**:
    $\|\mathbf{E} \times \mathbf{B}\|^2 + (\mathbf{E} \cdot \mathbf{B})^2 = \|\mathbf{E}\|^2 \|\mathbf{B}\|^2$. -/
theorem poynting_fujikawa_lagrange_identity (E B : Vec3 R) :
    Vec3.sq (poyntingVector E B) + (pontryaginInvariant E B) ^ 2 =
      Vec3.sq E * Vec3.sq B := by
  dsimp [poyntingVector, pontryaginInvariant, Vec3.sq, Vec3.dot, Vec3.cross]
  ring

/-! ## Section 3: Topological Axion Current in Weyl Semimetals (CME + AHE) -/

/-- Chiral Magnetic Effect (CME) current $\mathbf{J}_{\mathrm{CME}} = b_0 \mathbf{B}$. -/
def chiralMagneticCurrent (b₀ : R) (B : Vec3 R) : Vec3 R :=
  Vec3.smul b₀ B

/-- Anomalous Hall Effect (AHE) current $\mathbf{J}_{\mathrm{AHE}} = \mathbf{b} \times \mathbf{E}$. -/
def anomalousHallCurrent (b_vec E : Vec3 R) : Vec3 R :=
  Vec3.cross b_vec E

/-- Total topological Carroll–Field–Jackiw axion current
    $\mathbf{J}_{\mathrm{axion}} = b_0 \mathbf{B} + \mathbf{b} \times \mathbf{E}$. -/
def totalAxionCurrent (b₀ : R) (b_vec E B : Vec3 R) : Vec3 R :=
  Vec3.add (chiralMagneticCurrent b₀ B) (anomalousHallCurrent b_vec E)

/-- **Zero Joule Heating of the Anomalous Hall Current**:
    The anomalous Hall current $\mathbf{b} \times \mathbf{E}$ is perpendicular to $\mathbf{E}$,
    doing zero dissipative Joule work ($\mathbf{E} \cdot (\mathbf{b} \times \mathbf{E}) = 0$). -/
theorem anomalous_hall_zero_joule_heating (b_vec E : Vec3 R) :
    Vec3.dot E (anomalousHallCurrent b_vec E) = 0 := by
  dsimp [anomalousHallCurrent]
  exact Vec3.dot_cross_self_right b_vec E

/-- **Axion Current Joule Power Law**:
    The electromagnetic power injected into the total axion current comes purely from the
    Fujikawa–Pontryagin chiral anomaly:
    $\mathbf{E} \cdot \mathbf{J}_{\mathrm{axion}} = b_0 (\mathbf{E} \cdot \mathbf{B}) = \mathcal{L}_{\mathrm{axion}}(b_0, \mathbf{E}, \mathbf{B})$. -/
theorem axion_current_power_is_pontryagin (b₀ : R) (b_vec E B : Vec3 R) :
    Vec3.dot E (totalAxionCurrent b₀ b_vec E B) = b₀ * pontryaginInvariant E B ∧
    Vec3.dot E (totalAxionCurrent b₀ b_vec E B) = axionGaugeTerm b₀ E B := by
  dsimp [totalAxionCurrent, chiralMagneticCurrent, anomalousHallCurrent,
    pontryaginInvariant, axionGaugeTerm, Vec3.add, Vec3.smul, Vec3.dot, Vec3.cross]
  exact ⟨by ring, by ring⟩

/-! ## Section 4: Phase-Velocity Birefringence Splitting & Tachyonic Zitterbewegung Instability -/

/-- Right-polarity eikonal frequency $\Omega_+ = k + b_0$. -/
def omegaRight (k b₀ : R) : R := k + b₀

/-- Left-polarity eikonal frequency $\Omega_- = k - b_0$. -/
def omegaLeft (k b₀ : R) : R := k - b₀

/-- **Chiral Birefringence Phase-Velocity Splitting**:
    When the phase velocities $v_+, v_-$ satisfy $k v_+ = \Omega_+$ and $k v_- = \Omega_-$,
    their difference obeys $k (v_+ - v_-) = 2 b_0$. -/
theorem phase_velocity_birefringence_splitting (k b₀ v_plus v_minus : R)
    (h_right : k * v_plus = omegaRight k b₀)
    (h_left  : k * v_minus = omegaLeft k b₀) :
    k * (v_plus - v_minus) = 2 * b₀ := by
  dsimp [omegaRight, omegaLeft] at h_right h_left
  linear_combination h_right - h_left

/-- **Subcritical Tachyonic Zitterbewegung Instability ($k^2 < b_0^2 \implies \Omega_+ \Omega_- < 0$)**:
    When the squared wavenumber $k^2$ falls below the squared chiral torsion $b_0^2$, the
    dispersion product $\Omega_+ \Omega_- = k^2 - b_0^2$ is strictly negative. -/
theorem chiral_tachyonic_zitterbewegung_instability [LinearOrder R] [IsStrictOrderedRing R]
    (k b₀ : R) (h_subcritical : k ^ 2 < b₀ ^ 2) :
    omegaRight k b₀ * omegaLeft k b₀ < 0 := by
  dsimp [omegaRight, omegaLeft]
  have h_prod : (k + b₀) * (k - b₀) = k ^ 2 - b₀ ^ 2 := by ring
  rw [h_prod]
  exact sub_neg.mpr h_subcritical

/-- **Destructive Birefringence Negative Dwell Time**:
    For strictly positive channel transit times ($\tau_+ = 1, \tau_- = 2$) and Aharonov
    two-state weights ($A_+ = 3, A_- = -2$ with $A_+ + A_- = 1$), the net weak dwell time is
    $\tau_{\mathrm{weak}} = -1 < 0$. -/
theorem destructive_birefringence_negative_dwell_time :
    let τ_plus  : ℤ := 1
    let τ_minus : ℤ := 2
    let A_plus  : ℤ := 3
    let A_minus : ℤ := -2
    let τ_weak  : ℤ := A_plus * τ_plus + A_minus * τ_minus
    τ_plus > 0 ∧ τ_minus > 0 ∧ A_plus + A_minus = 1 ∧ τ_weak = -1 ∧ τ_weak < 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **Section 118 Master Synthesis**:
    Combines the Lagrange–Poynting–Fujikawa identity, dissipationless anomalous Hall current,
    axion current Pontryagin power law, phase-velocity birefringence splitting, and subcritical
    tachyonic instability. -/
theorem axion_weyl_birefringence_master_synthesis [LinearOrder R] [IsStrictOrderedRing R] :
    (∀ E B : Vec3 R,
      Vec3.sq (poyntingVector E B) + (pontryaginInvariant E B) ^ 2 = Vec3.sq E * Vec3.sq B) ∧
    (∀ b_vec E : Vec3 R, Vec3.dot E (anomalousHallCurrent b_vec E) = 0) ∧
    (∀ (b₀ : R) (b_vec E B : Vec3 R),
      Vec3.dot E (totalAxionCurrent b₀ b_vec E B) = b₀ * pontryaginInvariant E B) ∧
    (∀ (k b₀ v_p v_m : R),
      k * v_p = omegaRight k b₀ → k * v_m = omegaLeft k b₀ → k * (v_p - v_m) = 2 * b₀) ∧
    (∀ k b₀ : R, k ^ 2 < b₀ ^ 2 → omegaRight k b₀ * omegaLeft k b₀ < 0) := by
  exact ⟨poynting_fujikawa_lagrange_identity, anomalous_hall_zero_joule_heating,
    fun b₀ b_vec E B => (axion_current_power_is_pontryagin b₀ b_vec E B).1,
    phase_velocity_birefringence_splitting,
    chiral_tachyonic_zitterbewegung_instability⟩

end InfoGeometry.QuantumContext.AxionBirefringence
