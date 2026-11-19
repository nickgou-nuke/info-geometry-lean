/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Star
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
import InfoGeometry.Clifford.GradedGraceContraction
import InfoGeometry.Clifford.CoordinateLessCliffordInvariance
import InfoGeometry.Clifford.Cl11GradedMorita
import InfoGeometry.Algebraic.CliffordSymmetryLift
import InfoGeometry.OperatorAlgebra.MaurerCartanTower

/-!
# Cartan–Hestenes Rotor Darboux Spin Connection, Einstein–Cartan Contortion–Spin Locking, and 5-Graded Maurer–Cartan Unification

This module formalizes the mathematical unification of **spin** (as an odd/rotor algebraic carrier)
and the **spin connection** (as its even logarithmic Darboux derivative and Grade-$0$ Maurer–Cartan
projection), resolving the artificial fiber-bundle separation between matter spinors and gauge
connections across five sections:

1. **Section 1 — The Clifford–Hestenes Darboux Identity ($\Omega = (dR)\widetilde{R}$ and $\nabla(R \gamma_a \widetilde{R}) = [\Omega, e_a]$)**:
   - Defines the rotated tetrad frame vector $e_a = R \gamma_a \widetilde{R}$ (`rotorFrameVector`),
     its Leibniz variation $de_a = (dR)\gamma_a \widetilde{R} + R \gamma_a (d\widetilde{R})$
     (`rotorFrameDerivative`), and the bivector Darboux spin connection
     $\Omega = (dR)\widetilde{R}$ (`rotorDarbouxConnection`).
   - Proves `cartan_hestenes_rotor_darboux_spin_connection_identity`: for any normalized spin
     rotor ($R \widetilde{R} = I$, $\widetilde{R} R = I$) satisfying the differentiated
     normalization constraint $(dR)\widetilde{R} + R(d\widetilde{R}) = 0$, the frame variation
     is governed identically by the bivector commutator with the rotor's logarithmic derivative:
     $$d(R \gamma_a \widetilde{R}) = [\Omega, R \gamma_a \widetilde{R}] = [\Omega, e_a].$$
   - Certifies the explicit hyperbolic rotor witness $R(\theta) = \cosh\theta \, I_2 + \sinh\theta \, e_{01}$
     in $\mathrm{Cl}(1,1) \cong M_2(\mathbb{R})$, proving $R(\theta)\widetilde{R}(\theta) = I_2$
     and $(R'(\theta))\widetilde{R}(\theta) = e_{01}$ (constant boost bivector spin connection).

2. **Section 2 — Einstein–Cartan–Sciama–Kibble Contortion–Spin Equivalence ($\omega = \mathring{\omega} + K(S)$)**:
   - Formalizes the affine decomposition of the full spin connection
     $\omega = \mathring{\omega} + K$ (`fullSpinConnection`) into the torsion-free Levi-Civita
     connection $\mathring{\omega}$ and the contortion tensor $K$.
   - Proves `einstein_cartan_sciama_kibble_contortion_spin_locking`: whenever $\mathring{\omega}$
     is torsion-free ($de + [\mathring{\omega}, e] = 0$), the torsion of the full connection reduces
     strictly to the algebraic commutator $[K, e]$, vanishes if and only if $[K, e] = 0$, and
     decomposes the full curvature into $F(\mathring{\omega}) + (dK + \{\mathring{\omega}, K\} + K^2)$.

3. **Section 3 — 5-Graded Maurer–Cartan Unification of Spin ($\Omega_{\pm 1}$) and Spin Connection ($\Omega_0$)**:
   - Proves `maurer_cartan_spin_and_spin_connection_unification`: in any flat 5-graded Maurer–Cartan
     super-connection $\Omega = \Omega_{-2} + \Omega_{-1} + \Omega_0 + \Omega_{+1} + \Omega_{+2}$,
     the Grade-$0$ spin-connection curvature $F(\Omega_0) = d\Omega_0 + \frac{1}{2}[\Omega_0 \wedge \Omega_0]$
     is sourced directly by the trans-sheet spinor-current bracket $-[\Omega_{-1} \wedge \Omega_{+1}]$
     (when contact torsion $[\Omega_{-2} \wedge \Omega_{+2}] = 0$), while the nilpotent odd
     generators $\Omega_{-1} = e_+$, $\Omega_{+1} = e_-$ satisfy $e_+^2 = 0$, $e_-^2 = 0$, and
     $[e_+, e_-] = e_{01}$ (the exact Cartan–Hestenes boost bivector connection).

4. **Section 4 — Abstract `CliffordAlgebra Q` Rotor Lifting & R1 `MaurerCartanTower` Coupling**:
   - Lifts the Darboux spin-connection calculus to genuine noncommutative `CliffordAlgebra Q`
     over arbitrary `[CommRing R]`, using `CliffordAlgebra.reverse` directly (`R⁻¹ = reverse R`),
     proving frame `Q`-preservation, `reverse Ω = -Ω` skew-reversion closure, `equivExterior_reverse`
     and grade-2 bivector characterization under `[Invertible (2 : R)]`, full R1 `MaurerCartanTower`
     coupling (`Ω = actionThetaR = thetaR = -thetaL u⁻¹`, covariant frame derivative, and
     $d\Omega - \Omega \wedge \Omega = 0$), the `reverseCommutingLane Q` subalgebra, and the
     `spinGroup Q →* Q.IsometryEquiv Q` M2.1 equivariance bridge.

5. **Section 5 — Concrete `CliffordAlgebra q11` Hyperbolic Rotor Specialization to `M₂(ℝ)`**:
   - Realizes `cl11HyperbolicRotor θ ∈ spinGroup q11` and specializes via both `cl11EquivMat`
     and `cl11StandardEquiv = walshConjugation ∘ cl11EquivMat` to recover `hyperbolicRotor θ`,
     `hyperbolicRotorReverse θ`, and `cl11BoostBivector`.

## Honest `BUCKET 1 / 2 / 3` Scope Note
- **`BUCKET 1` (Sections 1–3)**: Concrete `Matrix (Fin m) (Fin m) ℝ` (`M₂(ℝ)`) realization and
  5-graded `FiveGradedMaurerCartanJet` identities (where `R_rev` is supplied as a matrix hypothesis).
- **`BUCKET 1` (Sections 4–5)**: Algebraic `CliffordAlgebra Q` rotor calculus, `reverse`-commuting
  R1 `MaurerCartanTower` coupling, and `CliffordAlgebra q11` specialization; **`BUCKET 2`**:
  grade-2 `equivExterior_reverse` / `spinGroupToIsometryHom` results parameterized by
  `[Invertible (2 : R)]` (and `dim ≤ 3` bivector closure over finite-dim `ℝ`).
- **`BUCKET 3`**: General smooth manifold rotor fields $R : U \to \mathrm{Spin}(Q)$ (beyond 1D
  real curves `θ ↦ cl11HyperbolicRotor θ` and algebraic derivation lanes `K`) remain outside
  this module's algebraic scope.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis

open scoped Matrix BigOperators
open Matrix
open InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis

/-!
## Section 1: The Clifford–Hestenes Darboux Identity ($\Omega = (dR)\widetilde{R}$ and $d(R \gamma_a \widetilde{R}) = [\Omega, e_a]$)
-/

/-- First $2 \times 2$ real Clifford generator $e_{01} = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$
representing the hyperbolic boost bivector in $\mathrm{Cl}(1,1) \cong M_2(\mathbb{R})$. -/
def cl11BoostBivector : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![1, 0], ![0, -1]]

/-- Second $2 \times 2$ real Clifford generator $\gamma_0 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$
representing the reflections/frame vector in $\mathrm{Cl}(1,1) \cong M_2(\mathbb{R})$. -/
def cl11FrameGamma0 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![0, 1], ![1, 0]]

/-- Explicit non-commutativity witness on the $2 \times 2$ real Clifford matrix carrier (`T16`). -/
theorem cl11BoostBivector_mul_cl11FrameGamma0_ne_comm :
    cl11BoostBivector * cl11FrameGamma0 ≠ cl11FrameGamma0 * cl11BoostBivector := by
  intro h_comm
  have h01 : (cl11BoostBivector * cl11FrameGamma0) 0 1 =
      (cl11FrameGamma0 * cl11BoostBivector) 0 1 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h_comm
  revert h01
  simp [cl11BoostBivector, cl11FrameGamma0, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

/-- Rotated orthonormal frame vector $e_a = R \gamma_a \widetilde{R}$ generated by double-sided
Clifford rotor sandwiching of a reference vector $\gamma_a$. -/
def rotorFrameVector {m : ℕ} (R R_rev gamma_a : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  R * gamma_a * R_rev

/-- Leibniz directional derivative $d(R \gamma_a \widetilde{R}) = (dR)\gamma_a \widetilde{R} + R \gamma_a (d\widetilde{R})$
of the rotor-dressed frame vector along a tangent variation $(dR, d\widetilde{R})$. -/
def rotorFrameDerivative {m : ℕ} (R R_rev dR dR_rev gamma_a : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  dR * gamma_a * R_rev + R * gamma_a * dR_rev

/-- Cartan–Hestenes Darboux bivector spin connection $\Omega = (dR)\widetilde{R}$, defined as the
right-logarithmic derivative of the spin rotor $R$. -/
def rotorDarbouxConnection {m : ℕ} (dR R_rev : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  dR * R_rev

/-- Matrix Lie commutator $[A, B] = A B - B A$. -/
def matCommutator {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  A * B - B * A

/-- Explicit hyperbolic spin rotor $R(\theta) = \cosh\theta \, I_2 + \sinh\theta \, e_{01}$
in $\mathrm{Cl}(1,1) \cong M_2(\mathbb{R})$. -/
def hyperbolicRotor (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![Real.cosh θ + Real.sinh θ, 0], ![0, Real.cosh θ - Real.sinh θ]]

/-- Clifford reverse $\widetilde{R}(\theta) = \cosh\theta \, I_2 - \sinh\theta \, e_{01}$
of the hyperbolic spin rotor in $\mathrm{Cl}(1,1) \cong M_2(\mathbb{R})$. -/
def hyperbolicRotorReverse (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![Real.cosh θ - Real.sinh θ, 0], ![0, Real.cosh θ + Real.sinh θ]]

/-- Rapidities derivative $R'(\theta) = \sinh\theta \, I_2 + \cosh\theta \, e_{01}$
of the hyperbolic spin rotor with respect to the boost parameter $\theta$. -/
def hyperbolicRotorDeriv (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![Real.sinh θ + Real.cosh θ, 0], ![0, Real.sinh θ - Real.cosh θ]]

/-- The explicit matrix `hyperbolicRotorDeriv θ` is the derivative of the
hyperbolic rotor map at `θ`. The proof reduces the matrix-valued derivative to
its finitely many entries. -/
theorem hyperbolicRotor_hasDerivAt (θ : ℝ) :
    HasDerivAt hyperbolicRotor (hyperbolicRotorDeriv θ) θ := by
  change HasDerivAt
    (fun t : ℝ => fun i : Fin 2 => fun j : Fin 2 => hyperbolicRotor t i j)
    (fun i : Fin 2 => fun j : Fin 2 => hyperbolicRotorDeriv θ i j) θ
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  fin_cases i <;> fin_cases j
  · convert (Real.hasDerivAt_cosh θ).add (Real.hasDerivAt_sinh θ) using 1
    all_goals
      first
      | (funext x; simp [hyperbolicRotor, Pi.add_apply])
      | rfl
  · convert (hasDerivAt_const θ (0 : ℝ)) using 1
    all_goals
      first
      | (funext x; simp [hyperbolicRotor])
      | rfl
  · convert (hasDerivAt_const θ (0 : ℝ)) using 1
    all_goals
      first
      | (funext x; simp [hyperbolicRotor])
      | rfl
  · convert (Real.hasDerivAt_cosh θ).sub (Real.hasDerivAt_sinh θ) using 1
    all_goals
      first
      | (funext x; simp [hyperbolicRotor, Pi.sub_apply])
      | rfl

/-- Scalar helper identity $(\cosh\theta + \sinh\theta)(\cosh\theta - \sinh\theta) = 1$. -/
lemma cosh_add_sinh_mul_cosh_sub_sinh (θ : ℝ) :
    (Real.cosh θ + Real.sinh θ) * (Real.cosh θ - Real.sinh θ) = 1 := by
  calc
    (Real.cosh θ + Real.sinh θ) * (Real.cosh θ - Real.sinh θ)
        = Real.cosh θ ^ 2 - Real.sinh θ ^ 2 := by ring
    _ = 1 := Real.cosh_sq_sub_sinh_sq θ

/-- Scalar helper identity $(\cosh\theta - \sinh\theta)(\cosh\theta + \sinh\theta) = 1$. -/
lemma cosh_sub_sinh_mul_cosh_add_sinh (θ : ℝ) :
    (Real.cosh θ - Real.sinh θ) * (Real.cosh θ + Real.sinh θ) = 1 := by
  rw [mul_comm, cosh_add_sinh_mul_cosh_sub_sinh]

/-- Scalar helper identity $(\sinh\theta - \cosh\theta)(\cosh\theta + \sinh\theta) = -1$. -/
lemma sinh_sub_cosh_mul_cosh_add_sinh (θ : ℝ) :
    (Real.sinh θ - Real.cosh θ) * (Real.cosh θ + Real.sinh θ) = -1 := by
  calc
    (Real.sinh θ - Real.cosh θ) * (Real.cosh θ + Real.sinh θ)
        = -((Real.cosh θ + Real.sinh θ) * (Real.cosh θ - Real.sinh θ)) := by ring
    _ = -1 := by rw [cosh_add_sinh_mul_cosh_sub_sinh]

/-- **Theorem 1.1 (`cartan_hestenes_rotor_darboux_spin_connection_identity`)**:
1. **Reversed Darboux Skewness**:
   From the differentiated normalization constraint $(dR)\widetilde{R} + R(d\widetilde{R}) = 0$,
   the right variation satisfies $R(d\widetilde{R}) = -\Omega$.
2. **Exact Darboux Frame Transport Identity**:
   For any rotor $R$ with $\widetilde{R} R = I$ (`h_rev_norm`) and differentiated normalization
   $(dR)\widetilde{R} + R(d\widetilde{R}) = 0$ (`h_dnorm`), the directional derivative of the
   rotated tetrad frame $e_a = R \gamma_a \widetilde{R}$ is given identically by the commutator
   with the rotor's logarithmic derivative $\Omega = (dR)\widetilde{R}$:
   `rotorFrameDerivative R R_rev dR dR_rev gamma_a = matCommutator (rotorDarbouxConnection dR R_rev) (rotorFrameVector R R_rev gamma_a)`.
3. **Hyperbolic Rotor Normalization & Constant Bivector Connection Witness**:
   For every boost parameter $\theta \in \mathbb{R}$, `hyperbolicRotor θ * hyperbolicRotorReverse θ = 1`
   and its Darboux connection `rotorDarbouxConnection (hyperbolicRotorDeriv θ) (hyperbolicRotorReverse θ)`
   equals the constant boost bivector `cl11BoostBivector`. -/
theorem cartan_hestenes_rotor_darboux_spin_connection_identity
    {m : ℕ} (R R_rev dR dR_rev gamma_a : Matrix (Fin m) (Fin m) ℝ)
    (h_rev_norm : R_rev * R = 1)
    (h_dnorm : dR * R_rev + R * dR_rev = 0)
    (θ : ℝ) :
    R * dR_rev = -rotorDarbouxConnection dR R_rev ∧
    rotorFrameDerivative R R_rev dR dR_rev gamma_a =
      matCommutator (rotorDarbouxConnection dR R_rev) (rotorFrameVector R R_rev gamma_a) ∧
    (hyperbolicRotor θ * hyperbolicRotorReverse θ = 1 ∧
     rotorDarbouxConnection (hyperbolicRotorDeriv θ) (hyperbolicRotorReverse θ) =
       cl11BoostBivector) := by
  have h_skew : R * dR_rev = -(dR * R_rev) := eq_neg_of_add_eq_zero_right h_dnorm
  refine ⟨h_skew, ?_, ⟨?_, ?_⟩⟩
  · dsimp [rotorFrameDerivative, matCommutator, rotorDarbouxConnection, rotorFrameVector]
    have h_left : dR * gamma_a * R_rev = (dR * R_rev) * (R * gamma_a * R_rev) := by
      calc
        dR * gamma_a * R_rev = dR * (1 * gamma_a) * R_rev := by rw [Matrix.one_mul]
        _ = dR * ((R_rev * R) * gamma_a) * R_rev := by rw [h_rev_norm]
        _ = (dR * R_rev) * (R * gamma_a * R_rev) := by simp only [Matrix.mul_assoc]
    have h_right : R * gamma_a * dR_rev = -((R * gamma_a * R_rev) * (dR * R_rev)) := by
      calc
        R * gamma_a * dR_rev = R * (gamma_a * 1) * dR_rev := by rw [Matrix.mul_one]
        _ = R * (gamma_a * (R_rev * R)) * dR_rev := by rw [h_rev_norm]
        _ = (R * gamma_a * R_rev) * (R * dR_rev) := by simp only [Matrix.mul_assoc]
        _ = (R * gamma_a * R_rev) * -(dR * R_rev) := by rw [h_skew]
        _ = -((R * gamma_a * R_rev) * (dR * R_rev)) := by rw [Matrix.mul_neg]
    rw [h_left, h_right, ← sub_eq_add_neg]
  · ext i j
    fin_cases i <;> fin_cases j
    · dsimp [hyperbolicRotor, hyperbolicRotorReverse, Matrix.mul_apply]
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero, Matrix.one_apply_eq]
      exact cosh_add_sinh_mul_cosh_sub_sinh θ
    · simp [hyperbolicRotor, hyperbolicRotorReverse, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [hyperbolicRotor, hyperbolicRotorReverse, Matrix.mul_apply, Fin.sum_univ_two]
    · dsimp [hyperbolicRotor, hyperbolicRotorReverse, Matrix.mul_apply]
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_add, Matrix.one_apply_eq]
      exact cosh_sub_sinh_mul_cosh_add_sinh θ
  · ext i j
    fin_cases i <;> fin_cases j
    · dsimp [rotorDarbouxConnection, hyperbolicRotorDeriv, hyperbolicRotorReverse,
        cl11BoostBivector, Matrix.mul_apply]
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero]
      rw [add_comm (Real.sinh θ) (Real.cosh θ)]
      exact cosh_add_sinh_mul_cosh_sub_sinh θ
    · simp [rotorDarbouxConnection, hyperbolicRotorDeriv, hyperbolicRotorReverse,
        cl11BoostBivector, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [rotorDarbouxConnection, hyperbolicRotorDeriv, hyperbolicRotorReverse,
        cl11BoostBivector, Matrix.mul_apply, Fin.sum_univ_two]
    · dsimp [rotorDarbouxConnection, hyperbolicRotorDeriv, hyperbolicRotorReverse,
        cl11BoostBivector, Matrix.mul_apply]
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_add]
      exact sinh_sub_cosh_mul_cosh_add_sinh θ

/-!
## Section 2: Einstein–Cartan–Sciama–Kibble Contortion–Spin Equivalence ($\omega = \mathring{\omega} + K(S)$)
-/

/-- Full Einstein–Cartan spin connection $\omega = \mathring{\omega} + K$, decomposing into the
torsion-free Levi-Civita connection $\mathring{\omega}$ (`omega_LC`) and the contortion tensor
$K = \kappa S$ (`K`). -/
def fullSpinConnection {m : ℕ} (omega_LC K : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  omega_LC + K

/-- Soldered Cartan torsion $T(\omega, e) = de + [\omega, e]$ of a spin connection $\omega$
with respect to a soldered frame $e$ and its exterior variation $de$. -/
def solderedTorsion {m : ℕ} (omega e_frame de_frame : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  de_frame + matCommutator omega e_frame

/-- Non-abelian Cartan curvature $F(d\omega, \omega) = d\omega + \omega^2$. -/
def connectionCurvature {m : ℕ} (d_omega omega : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  d_omega + omega * omega

/-- **Theorem 2.1 (`einstein_cartan_sciama_kibble_contortion_spin_locking`)**:
For any Levi-Civita connection $\mathring{\omega}$ whose soldered torsion vanishes
(`h_tf : solderedTorsion omega_LC e_frame de_frame = 0`) and any contortion tensor $K$:
1. **Pure Algebraic Torsion–Spin Locking**:
   The torsion of the full connection $\omega = \mathring{\omega} + K$ reduces strictly to the
   algebraic commutator of the contortion tensor $K$ with the soldered frame $e$:
   `solderedTorsion (fullSpinConnection omega_LC K) e_frame de_frame = matCommutator K e_frame`.
2. **Torsion-Free Reduction Criterion**:
   The full connection $\omega = \mathring{\omega} + K$ is torsion-free if and only if the
   contortion action on the soldered frame vanishes (`matCommutator K e_frame = 0`).
3. **Einstein–Cartan Curvature Expansion**:
   The curvature of $\omega = \mathring{\omega} + K$ expands into the Riemannian curvature
   $F(\mathring{\omega})$ plus the covariant contortion differential and quadratic spin-spin
   self-interaction $K^2$:
   `connectionCurvature (d_omega_LC + dK) (fullSpinConnection omega_LC K) = connectionCurvature d_omega_LC omega_LC + (dK + (omega_LC * K + K * omega_LC) + K * K)`. -/
theorem einstein_cartan_sciama_kibble_contortion_spin_locking
    {m : ℕ} (omega_LC K e_frame de_frame d_omega_LC dK : Matrix (Fin m) (Fin m) ℝ)
    (h_tf : solderedTorsion omega_LC e_frame de_frame = 0) :
    solderedTorsion (fullSpinConnection omega_LC K) e_frame de_frame =
      matCommutator K e_frame ∧
    (solderedTorsion (fullSpinConnection omega_LC K) e_frame de_frame = 0 ↔
      matCommutator K e_frame = 0) ∧
    connectionCurvature (d_omega_LC + dK) (fullSpinConnection omega_LC K) =
      connectionCurvature d_omega_LC omega_LC +
        (dK + (omega_LC * K + K * omega_LC) + K * K) := by
  have h_torsion :
      solderedTorsion (fullSpinConnection omega_LC K) e_frame de_frame =
        matCommutator K e_frame := by
    calc
      solderedTorsion (fullSpinConnection omega_LC K) e_frame de_frame
          = solderedTorsion omega_LC e_frame de_frame + matCommutator K e_frame := by
            ext i j
            dsimp [solderedTorsion, fullSpinConnection, matCommutator]
            rw [Matrix.add_mul, Matrix.mul_add]
            simp only [Matrix.add_apply]
            abel
      _ = 0 + matCommutator K e_frame := by rw [h_tf]
      _ = matCommutator K e_frame := zero_add _
  refine ⟨h_torsion, ?_, ?_⟩
  · rw [h_torsion]
  · ext i j
    dsimp [connectionCurvature, fullSpinConnection]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
    simp only [Matrix.add_apply]
    abel

/-!
## Section 3: 5-Graded Maurer–Cartan Unification of Spin ($\Omega_{\pm 1}$) and Spin Connection ($\Omega_0$)
-/

/-- Grade-$0$ internal gauge/Riemannian curvature component
$F(\Omega_0) = d\Omega_0 + \frac{1}{2}[\Omega_0 \wedge \Omega_0]$ of a 5-graded Maurer–Cartan jet. -/
def grade0SpinConnectionCurvature {R : Type*} [Ring R]
    (J : FiveGradedMaurerCartanJet R) : R :=
  J.dOmega_0 + J.br_0_0_half

/-- Grade-$-1$ covariant spin-frame exterior derivative
$\mathcal{D}_{\Omega_0}\Omega_{-1} = d\Omega_{-1} + [\Omega_0 \wedge \Omega_{-1}]$. -/
def gradeM1CovariantSpinDerivative {R : Type*} [Ring R]
    (J : FiveGradedMaurerCartanJet R) : R :=
  J.dOmega_m1 + J.br_0_m1

/-- Grade-$+1$ covariant dual-spin exterior derivative
$\mathcal{D}_{\Omega_0}\Omega_{+1} = d\Omega_{+1} + [\Omega_0 \wedge \Omega_{+1}]$. -/
def gradeP1CovariantSpinDerivative {R : Type*} [Ring R]
    (J : FiveGradedMaurerCartanJet R) : R :=
  J.dOmega_p1 + J.br_0_p1

/-- Positive-sheet nilpotent spinor generator $\Omega_{-1} = e_+ = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$. -/
def spinCurrentPlus2 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![0, 1], ![0, 0]]

/-- Negative-sheet nilpotent dual-spinor generator $\Omega_{+1} = e_- = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$. -/
def spinCurrentMinus2 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![0, 0], ![1, 0]]

/-- **Theorem 3.1 (`maurer_cartan_spin_and_spin_connection_unification`)**:
In any flat 5-graded Maurer–Cartan super-connection (`h_flat : mcCurvatureTower J = (0, 0, 0, 0, 0)`):
1. **Grade-$0$ Curvature Sourced by Odd Spin Currents**:
   `grade0SpinConnectionCurvature J = -(J.br_m1_p1 + J.br_m2_p2)`, and when the contact
   Grade-$\pm 2$ bracket vanishes (`h_contact : J.br_m2_p2 = 0`), the Grade-$0$ spin-connection
   curvature is generated purely by the odd trans-sheet spinor bracket:
   $$F(\Omega_0) = d\Omega_0 + \frac{1}{2}[\Omega_0 \wedge \Omega_0] = -[\Omega_{-1} \wedge \Omega_{+1}].$$
2. **Grade-$\pm 1$ Covariant Spin Transport**:
   $\mathcal{D}_{\Omega_0}\Omega_{-1} = -[\Omega_{+1} \wedge \Omega_{-2}]$ and
   $\mathcal{D}_{\Omega_0}\Omega_{+1} = -[\Omega_{-1} \wedge \Omega_{+2}]$.
3. **Explicit Clifford Matrix Realization of $[\Omega_{-1}, \Omega_{+1}] = \Omega_0$**:
   The odd spinor currents `spinCurrentPlus2` ($e_+$) and `spinCurrentMinus2` ($e_-$) are both
   nilpotent ($e_+^2 = 0$, $e_-^2 = 0$), while their Lie commutator $[e_+, e_-]$ equals the
   exact Grade-$0$ Cartan–Hestenes boost bivector spin connection `cl11BoostBivector` ($e_{01}$). -/
theorem maurer_cartan_spin_and_spin_connection_unification
    {R : Type*} [Ring R] (J : FiveGradedMaurerCartanJet R)
    (h_flat : mcCurvatureTower J = (0, 0, 0, 0, 0))
    (h_contact : J.br_m2_p2 = 0) :
    (grade0SpinConnectionCurvature J = -(J.br_m1_p1 + J.br_m2_p2) ∧
     grade0SpinConnectionCurvature J = -J.br_m1_p1) ∧
    (gradeM1CovariantSpinDerivative J = -J.br_p1_m2 ∧
     gradeP1CovariantSpinDerivative J = -J.br_m1_p2) ∧
    (spinCurrentPlus2 * spinCurrentPlus2 = 0 ∧
     spinCurrentMinus2 * spinCurrentMinus2 = 0 ∧
     matCommutator spinCurrentPlus2 spinCurrentMinus2 = cl11BoostBivector) := by
  have h_laws := (mcCurvatureTower_flat_iff_source_laws J).mp h_flat
  rcases h_laws with ⟨_, h_m1, h_0, h_p1, _⟩
  refine ⟨⟨h_0, ?_⟩, ⟨h_m1, h_p1⟩, ⟨?_, ?_, ?_⟩⟩
  · dsimp [grade0SpinConnectionCurvature]
    rw [h_0, h_contact, add_zero]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spinCurrentPlus2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spinCurrentMinus2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matCommutator, spinCurrentPlus2, spinCurrentMinus2, cl11BoostBivector]

/-!
## Section 4: Abstract `CliffordAlgebra Q` Rotor Calculus & R1 `MaurerCartanTower` Coupling
-/

section AbstractCliffordRotorCalculus

open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.MaurerCartanTower
open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Clifford.CoordinateLessCliffordInvariance
open InfoGeometry.Riemannian

section Part4A_And_4B

variable {R_coeff : Type*} [CommRing R_coeff]
variable {M : Type*} [AddCommGroup M] [Module R_coeff M]
variable {Q : QuadraticForm R_coeff M}

/-- Package a normalized `CliffordAlgebra Q` rotor `R` (with `R⁻¹ = CliffordAlgebra.reverse R`)
as a unit in `(CliffordAlgebra Q)ˣ`. -/
def clRotorUnit (R : CliffordAlgebra Q)
    (h_mul_rev : R * CliffordAlgebra.reverse R = 1)
    (h_rev_mul : CliffordAlgebra.reverse R * R = 1) :
    (CliffordAlgebra Q)ˣ :=
  ⟨R, CliffordAlgebra.reverse R, h_mul_rev, h_rev_mul⟩

@[simp] theorem clRotorUnit_val (R : CliffordAlgebra Q)
    (h_mul_rev : R * CliffordAlgebra.reverse R = 1)
    (h_rev_mul : CliffordAlgebra.reverse R * R = 1) :
    (clRotorUnit R h_mul_rev h_rev_mul : CliffordAlgebra Q) = R :=
  rfl

@[simp] theorem clRotorUnit_inv_val (R : CliffordAlgebra Q)
    (h_mul_rev : R * CliffordAlgebra.reverse R = 1)
    (h_rev_mul : CliffordAlgebra.reverse R * R = 1) :
    ((clRotorUnit R h_mul_rev h_rev_mul)⁻¹ : (CliffordAlgebra Q)ˣ).val =
      CliffordAlgebra.reverse R :=
  rfl

/-- Rotated Clifford element `R * γ * reverse R` in `CliffordAlgebra Q`. -/
def clRotorFrameVector (R γ : CliffordAlgebra Q) : CliffordAlgebra Q :=
  R * γ * CliffordAlgebra.reverse R

/-- Rotor conjugation as an `R_coeff`-algebra automorphism of `CliffordAlgebra Q`. -/
def clRotorConjugateAlgEquiv (R : CliffordAlgebra Q)
    (h_mul_rev : R * CliffordAlgebra.reverse R = 1)
    (h_rev_mul : CliffordAlgebra.reverse R * R = 1) :
    CliffordAlgebra Q ≃ₐ[R_coeff] CliffordAlgebra Q :=
  conjugateAlgEquiv R_coeff (clRotorUnit R h_mul_rev h_rev_mul)

@[simp] theorem clRotorConjugateAlgEquiv_apply (R : CliffordAlgebra Q)
    (h_mul_rev : R * CliffordAlgebra.reverse R = 1)
    (h_rev_mul : CliffordAlgebra.reverse R * R = 1)
    (γ : CliffordAlgebra Q) :
    clRotorConjugateAlgEquiv R h_mul_rev h_rev_mul γ = clRotorFrameVector R γ :=
  rfl

theorem clRotorFrameVector_reverse (R γ : CliffordAlgebra Q) :
    CliffordAlgebra.reverse (clRotorFrameVector R γ) =
      clRotorFrameVector R (CliffordAlgebra.reverse γ) := by
  dsimp [clRotorFrameVector]
  rw [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse.map_mul,
    CliffordAlgebra.reverse_reverse, mul_assoc]

theorem clRotorFrameVector_ι_reverse (R : CliffordAlgebra Q) (v : M) :
    CliffordAlgebra.reverse (clRotorFrameVector R (CliffordAlgebra.ι Q v)) =
      clRotorFrameVector R (CliffordAlgebra.ι Q v) := by
  rw [clRotorFrameVector_reverse, CliffordAlgebra.reverse_ι]

theorem clRotorFrameVector_sq (R γ : CliffordAlgebra Q)
    (h_rev_mul : CliffordAlgebra.reverse R * R = 1) :
    clRotorFrameVector R γ * clRotorFrameVector R γ = clRotorFrameVector R (γ * γ) := by
  dsimp [clRotorFrameVector]
  calc
    R * γ * CliffordAlgebra.reverse R * (R * γ * CliffordAlgebra.reverse R)
        = R * γ * (CliffordAlgebra.reverse R * R) * γ * CliffordAlgebra.reverse R := by
          simp only [mul_assoc]
    _ = R * γ * 1 * γ * CliffordAlgebra.reverse R := by rw [h_rev_mul]
    _ = R * (γ * γ) * CliffordAlgebra.reverse R := by simp only [mul_one, mul_assoc]

theorem clRotorFrameVector_ι_sq (R : CliffordAlgebra Q)
    (h_mul_rev : R * CliffordAlgebra.reverse R = 1)
    (h_rev_mul : CliffordAlgebra.reverse R * R = 1) (v : M) :
    clRotorFrameVector R (CliffordAlgebra.ι Q v) *
        clRotorFrameVector R (CliffordAlgebra.ι Q v) =
      algebraMap R_coeff (CliffordAlgebra Q) (Q v) := by
  rw [clRotorFrameVector_sq R (CliffordAlgebra.ι Q v) h_rev_mul,
    CliffordAlgebra.ι_sq_scalar]
  dsimp [clRotorFrameVector]
  rw [← Algebra.commutes (Q v) R, mul_assoc, h_mul_rev, mul_one]

/-- Leibniz variation of the rotor-dressed frame `R * γ * reverse R`. -/
def clRotorFrameDerivative (R dR dR_rev γ dγ : CliffordAlgebra Q) : CliffordAlgebra Q :=
  dR * γ * CliffordAlgebra.reverse R +
    R * dγ * CliffordAlgebra.reverse R +
    R * γ * dR_rev

/-- Abstract Cartan–Hestenes Darboux spin connection `Ω = (dR) * CliffordAlgebra.reverse R`. -/
def clRotorDarbouxConnection (R dR : CliffordAlgebra Q) : CliffordAlgebra Q :=
  dR * CliffordAlgebra.reverse R

/-- Noncommutative Clifford Lie commutator `[A, B] = A * B - B * A`. -/
def clCommutator (A B : CliffordAlgebra Q) : CliffordAlgebra Q :=
  A * B - B * A

/-- Abstract `CliffordAlgebra Q` Darboux spin-connection identity:
`d(R γ R̃) = [Ω, R γ R̃] + R (dγ) R̃` for `Ω = (dR) * reverse R`. -/
theorem clRotor_darboux_spin_connection_identity
    (R dR dR_rev γ dγ : CliffordAlgebra Q)
    (h_rev_norm : CliffordAlgebra.reverse R * R = 1)
    (h_dnorm : dR * CliffordAlgebra.reverse R + R * dR_rev = 0) :
    R * dR_rev = -clRotorDarbouxConnection R dR ∧
    clRotorFrameDerivative R dR dR_rev γ dγ =
      clCommutator (clRotorDarbouxConnection R dR) (clRotorFrameVector R γ) +
        clRotorFrameVector R dγ := by
  have h_skew : R * dR_rev = -clRotorDarbouxConnection R dR :=
    eq_neg_of_add_eq_zero_right h_dnorm
  refine ⟨h_skew, ?_⟩
  dsimp [clRotorFrameDerivative, clCommutator, clRotorDarbouxConnection, clRotorFrameVector]
  have h_left :
      dR * γ * CliffordAlgebra.reverse R =
        (dR * CliffordAlgebra.reverse R) * (R * γ * CliffordAlgebra.reverse R) := by
    calc
      dR * γ * CliffordAlgebra.reverse R
          = dR * (1 * γ) * CliffordAlgebra.reverse R := by rw [one_mul]
      _ = dR * ((CliffordAlgebra.reverse R * R) * γ) * CliffordAlgebra.reverse R := by
            rw [h_rev_norm]
      _ = (dR * CliffordAlgebra.reverse R) * (R * γ * CliffordAlgebra.reverse R) := by
            simp only [mul_assoc]
  have h_right :
      R * γ * dR_rev =
        -((R * γ * CliffordAlgebra.reverse R) * (dR * CliffordAlgebra.reverse R)) := by
    calc
      R * γ * dR_rev = R * (γ * 1) * dR_rev := by rw [mul_one]
      _ = R * (γ * (CliffordAlgebra.reverse R * R)) * dR_rev := by rw [h_rev_norm]
      _ = (R * γ * CliffordAlgebra.reverse R) * (R * dR_rev) := by simp only [mul_assoc]
      _ = (R * γ * CliffordAlgebra.reverse R) * -(dR * CliffordAlgebra.reverse R) := by
            rw [h_skew]; rfl
      _ = -((R * γ * CliffordAlgebra.reverse R) * (dR * CliffordAlgebra.reverse R)) := by
            rw [mul_neg]
  rw [h_left, h_right]
  abel

theorem clRotor_darboux_spin_connection_identity_const
    (R dR dR_rev γ : CliffordAlgebra Q)
    (h_rev_norm : CliffordAlgebra.reverse R * R = 1)
    (h_dnorm : dR * CliffordAlgebra.reverse R + R * dR_rev = 0) :
    clRotorFrameDerivative R dR dR_rev γ 0 =
      clCommutator (clRotorDarbouxConnection R dR) (clRotorFrameVector R γ) := by
  have h := (clRotor_darboux_spin_connection_identity R dR dR_rev γ 0 h_rev_norm h_dnorm).2
  simpa [clRotorFrameVector] using h

/-- Skew-reversion closure (`reverse Ω = -Ω`) for `Ω = (dR) * reverse R` whenever
`d(R * reverse R) = dR * reverse R + R * reverse dR = 0`. -/
theorem clRotorDarbouxConnection_reverse_eq_neg
    (R dR : CliffordAlgebra Q)
    (h_dnorm : dR * CliffordAlgebra.reverse R + R * CliffordAlgebra.reverse dR = 0) :
    CliffordAlgebra.reverse (clRotorDarbouxConnection R dR) =
      -(clRotorDarbouxConnection R dR) := by
  rw [clRotorDarbouxConnection, CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_reverse]
  exact eq_neg_of_add_eq_zero_right h_dnorm

end Part4A_And_4B

section Part4C_ReverseGradeTwo

variable {R_coeff : Type*} [CommRing R_coeff]
variable {M : Type*} [AddCommGroup M] [Module R_coeff M]

private theorem contractLeft_mul_ι {Q : QuadraticForm R_coeff M}
    (d : Module.Dual R_coeff M) (x : CliffordAlgebra Q) (a : M) :
    CliffordAlgebra.contractLeft d (x * CliffordAlgebra.ι Q a) =
      d a • CliffordAlgebra.involute x +
        CliffordAlgebra.contractLeft d x * CliffordAlgebra.ι Q a := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [← Algebra.smul_def, map_smul, CliffordAlgebra.contractLeft_ι, AlgHom.commutes,
      CliffordAlgebra.contractLeft_algebraMap, zero_mul, add_zero,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      smul_smul, smul_smul, mul_comm]
  | add x₁ x₂ hx₁ hx₂ =>
    rw [add_mul, map_add, map_add, map_add, add_mul, hx₁, hx₂, smul_add]
    abel
  | ι_mul x_cl m hx =>
    rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul, hx, mul_add, mul_smul_comm,
      ← mul_assoc, map_mul, CliffordAlgebra.involute_ι, neg_mul, smul_neg,
      CliffordAlgebra.contractLeft_ι_mul, sub_mul, smul_mul_assoc]
    abel

private theorem contractRight_ι_mul {Q : QuadraticForm R_coeff M}
    (d : Module.Dual R_coeff M) (a : M) (x : CliffordAlgebra Q) :
    CliffordAlgebra.contractRight (CliffordAlgebra.ι Q a * x) d =
      d a • CliffordAlgebra.involute x +
        CliffordAlgebra.ι Q a * CliffordAlgebra.contractRight x d := by
  rw [CliffordAlgebra.contractRight_eq, CliffordAlgebra.reverse.map_mul,
    CliffordAlgebra.reverse_ι, contractLeft_mul_ι, map_add, map_smul,
    CliffordAlgebra.reverse_involute, CliffordAlgebra.reverse.map_mul,
    CliffordAlgebra.reverse_ι, CliffordAlgebra.reverse_reverse, CliffordAlgebra.contractRight_eq]

private theorem contractRight_contractLeft {Q : QuadraticForm R_coeff M}
    (d d' : Module.Dual R_coeff M) (x : CliffordAlgebra Q) :
    CliffordAlgebra.contractLeft d (CliffordAlgebra.contractRight x d') =
      CliffordAlgebra.contractRight (CliffordAlgebra.contractLeft d x) d' := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp [CliffordAlgebra.contractRight_eq, CliffordAlgebra.reverse.commutes]
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
  | ι_mul x_cl m hx =>
    rw [contractRight_ι_mul, map_add, map_smul, CliffordAlgebra.contractLeft_ι_mul,
      CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, contractRight_ι_mul, hx]
    have hinvol :
        CliffordAlgebra.contractLeft d (CliffordAlgebra.involute x_cl) =
          -(CliffordAlgebra.involute (CliffordAlgebra.contractLeft d x_cl)) := by
      have h := involute_contractLeft Q d x_cl
      calc
        CliffordAlgebra.contractLeft d (CliffordAlgebra.involute x_cl)
            = - -CliffordAlgebra.contractLeft d (CliffordAlgebra.involute x_cl) := (neg_neg _).symm
        _ = -CliffordAlgebra.involute (CliffordAlgebra.contractLeft d x_cl) := by rw [h]
    rw [hinvol, smul_neg]
    abel

private theorem changeForm_mul_ι {Q Q' : QuadraticForm R_coeff M} {B : LinearMap.BilinForm R_coeff M}
    (hB : ∀ x y, B x y = B y x) (h : B.toQuadraticMap = Q' - Q)
    (x : CliffordAlgebra Q) (m : M) :
    CliffordAlgebra.changeForm h (x * CliffordAlgebra.ι Q m) =
      CliffordAlgebra.changeForm h x * CliffordAlgebra.ι Q' m -
        CliffordAlgebra.contractRight (CliffordAlgebra.changeForm h x) (B m) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [← Algebra.smul_def, map_smul, CliffordAlgebra.changeForm_ι,
      CliffordAlgebra.changeForm_algebraMap, ← Algebra.smul_def,
      CliffordAlgebra.contractRight_algebraMap, sub_zero]
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [add_mul, map_add, LinearMap.add_apply, hx₁, hx₂]
    abel
  | ι_mul x_cl a hx =>
    rw [mul_assoc, CliffordAlgebra.changeForm_ι_mul, CliffordAlgebra.changeForm_ι_mul, hx,
      mul_sub, map_sub, contractLeft_mul_ι, sub_mul, map_sub, LinearMap.sub_apply,
      contractRight_ι_mul, contractRight_contractLeft, hB a m, mul_assoc]
    abel

theorem changeForm_reverse {Q Q' : QuadraticForm R_coeff M} {B : LinearMap.BilinForm R_coeff M}
    (hB : ∀ x y, B x y = B y x) (h : B.toQuadraticMap = Q' - Q) (x : CliffordAlgebra Q) :
    CliffordAlgebra.changeForm h (CliffordAlgebra.reverse x) =
      CliffordAlgebra.reverse (CliffordAlgebra.changeForm h x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [CliffordAlgebra.reverse.commutes, CliffordAlgebra.changeForm_algebraMap,
      CliffordAlgebra.reverse.commutes]
  | add x₁ x₂ hx₁ hx₂ =>
    rw [map_add, map_add, map_add, map_add, hx₁, hx₂]
  | ι_mul x_cl m hx =>
    rw [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι,
      changeForm_mul_ι hB h, CliffordAlgebra.changeForm_ι_mul, map_sub,
      CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι, hx]
    congr 1
    rw [CliffordAlgebra.contractRight_eq, CliffordAlgebra.reverse_reverse]

variable [Invertible (2 : R_coeff)]

private theorem associated_symm (Q : QuadraticForm R_coeff M) (x y : M) :
    QuadraticMap.associated (R := R_coeff) Q x y =
      QuadraticMap.associated (R := R_coeff) Q y x := by
  simp only [QuadraticMap.associated_apply]
  rw [add_comm y x, sub_sub, add_comm (Q x) (Q y), ← sub_sub]

/-- `CliffordAlgebra.equivExterior Q` commutes with `CliffordAlgebra.reverse`. -/
theorem equivExterior_reverse (Q : QuadraticForm R_coeff M) (x : CliffordAlgebra Q) :
    CliffordAlgebra.equivExterior Q (CliffordAlgebra.reverse x) =
      CliffordAlgebra.reverse (CliffordAlgebra.equivExterior Q x) := by
  change CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof
      (CliffordAlgebra.reverse x) =
    CliffordAlgebra.reverse
      (CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof x)
  exact changeForm_reverse (associated_symm (-Q)) _ x

omit [Invertible (2 : R_coeff)] in
theorem exteriorPower_two_reverse {y : ExteriorAlgebra R_coeff M} (hy : y ∈ ⋀[R_coeff]^2 M) :
    CliffordAlgebra.reverse y = -y := by
  rw [ExteriorAlgebra.exteriorPower, pow_two] at hy
  refine Submodule.mul_induction_on hy ?_ ?_
  · intro a ha b hb
    rcases LinearMap.mem_range.mp ha with ⟨u, rfl⟩
    rcases LinearMap.mem_range.mp hb with ⟨v, rfl⟩
    have hanti : ExteriorAlgebra.ι R_coeff u * ExteriorAlgebra.ι R_coeff v +
        ExteriorAlgebra.ι R_coeff v * ExteriorAlgebra.ι R_coeff u = 0 := by
      have hsq := ExteriorAlgebra.ι_sq_zero (R := R_coeff) (u + v)
      rw [map_add, add_mul, mul_add, mul_add, ExteriorAlgebra.ι_sq_zero,
        ExteriorAlgebra.ι_sq_zero, zero_add, add_zero] at hsq
      exact hsq
    rw [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι,
      CliffordAlgebra.reverse_ι]
    exact eq_neg_of_add_eq_zero_right hanti
  · intro a b ha hb
    rw [map_add, ha, hb, neg_add]

/-- Every grade-2 projection in `CliffordAlgebra Q` is skew under `CliffordAlgebra.reverse`. -/
theorem cliffordGradeProj_two_reverse (Q : QuadraticForm R_coeff M) (x : CliffordAlgebra Q) :
    CliffordAlgebra.reverse (cliffordGradeProj Q 2 x) = -cliffordGradeProj Q 2 x := by
  apply (CliffordAlgebra.equivExterior Q).injective
  rw [equivExterior_reverse, map_neg]
  change CliffordAlgebra.reverse
      (CliffordAlgebra.equivExterior Q
        ((CliffordAlgebra.equivExterior Q).symm
          (exteriorGradeProj R_coeff M 2 (CliffordAlgebra.equivExterior Q x)))) =
    -(CliffordAlgebra.equivExterior Q
      ((CliffordAlgebra.equivExterior Q).symm
        (exteriorGradeProj R_coeff M 2 (CliffordAlgebra.equivExterior Q x))))
  rw [LinearEquiv.apply_symm_apply]
  exact exteriorPower_two_reverse (exteriorGradeProj_mem R_coeff M 2 _)

theorem cliffordGradeSubmodule_two_reverse {Q : QuadraticForm R_coeff M} {B : CliffordAlgebra Q}
    (hB : B ∈ cliffordGradeSubmodule Q 2) :
    CliffordAlgebra.reverse B = -B := by
  rw [mem_cliffordGradeSubmodule_iff] at hB
  rw [← hB]
  exact cliffordGradeProj_two_reverse Q B

theorem hTrace_cl_reverse (Q : QuadraticForm R_coeff M) (x : CliffordAlgebra Q) :
    hTrace_cl Q (CliffordAlgebra.reverse x) = hTrace_cl Q x := by
  change ExteriorAlgebra.algebraMapInv
      (CliffordAlgebra.equivExterior Q (CliffordAlgebra.reverse x)) =
    ExteriorAlgebra.algebraMapInv (CliffordAlgebra.equivExterior Q x)
  rw [equivExterior_reverse]
  have hmem : ∀ y : ExteriorAlgebra R_coeff M,
      ExteriorAlgebra.algebraMapInv (CliffordAlgebra.reverse y) =
        ExteriorAlgebra.algebraMapInv y := by
    intro y
    induction y using CliffordAlgebra.induction with
    | algebraMap r => simp [CliffordAlgebra.reverse.commutes]
    | ι m => simp [CliffordAlgebra.reverse_ι]
    | mul a b ha hb => simp [CliffordAlgebra.reverse.map_mul, ha, hb, mul_comm]
    | add a b ha hb => simp [map_add, ha, hb]
  exact hmem _

theorem hTrace_cl_eq_zero_of_reverse_eq_neg {Q : QuadraticForm R_coeff M}
    {x : CliffordAlgebra Q} (hx : CliffordAlgebra.reverse x = -x) :
    hTrace_cl Q x = 0 := by
  have h := hTrace_cl_reverse Q x
  rw [hx, map_neg] at h
  have h2 : (2 : R_coeff) * hTrace_cl Q x = 0 := by
    calc
      (2 : R_coeff) * hTrace_cl Q x = hTrace_cl Q x + hTrace_cl Q x := two_mul _
      _ = -(hTrace_cl Q x) + hTrace_cl Q x := by conv_lhs => lhs; rw [← h]
      _ = 0 := neg_add_cancel _
  have hinv := congrArg (fun r => ⅟(2 : R_coeff) * r) h2
  simpa [← mul_assoc] using hinv

section RealDimLeThreeBivector

variable {M_real : Type*} [AddCommGroup M_real] [Module ℝ M_real] [Module.Finite ℝ M_real]

/-- In dimension `≤ 3`, every even Clifford element `x` with `reverse x = -x` is a pure
grade-2 bivector (`x ∈ cliffordGradeSubmodule Q 2`). -/
theorem mem_cliffordGradeSubmodule_two_of_even_reverse_neg_finrank_le_three
    (Q : QuadraticForm ℝ M_real) (hdim : Module.finrank ℝ M_real ≤ 3)
    {x : CliffordAlgebra Q} (hx_even : x ∈ CliffordAlgebra.evenOdd Q 0)
    (hx_rev : CliffordAlgebra.reverse x = -x) :
    x ∈ cliffordGradeSubmodule Q 2 := by
  rw [mem_cliffordGradeSubmodule_iff]
  have hinvol : CliffordAlgebra.involute x = x :=
    CliffordAlgebra.involute_eq_of_mem_even hx_even
  have h0 : cliffordGradeProj Q 0 x = 0 := by
    rw [cliffordGradeProj_zero_eq_algebraMap_hTrace,
      hTrace_cl_eq_zero_of_reverse_eq_neg hx_rev, map_zero]
  have hodd : ∀ k : ℕ, Odd k → cliffordGradeProj Q k x = 0 := by
    intro k hk
    have hinv := cliffordGradeProj_involute Q k x
    rw [hinvol, hk.neg_one_pow, neg_one_smul] at hinv
    have h2 : (2 : ℝ) • cliffordGradeProj Q k x = 0 := by
      calc
        (2 : ℝ) • cliffordGradeProj Q k x
            = cliffordGradeProj Q k x + cliffordGradeProj Q k x := two_smul ℝ _
        _ = cliffordGradeProj Q k x + -cliffordGradeProj Q k x := by
              conv_rhs => rw [← hinv]
        _ = 0 := add_neg_cancel _
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  have h1 : cliffordGradeProj Q 1 x = 0 := hodd 1 odd_one
  have h3 : cliffordGradeProj Q 3 x = 0 := hodd 3 (by decide)
  have hsum := (cliffordGradeProj_sum_range_apply Q x).symm
  have hrange : ∀ k ∈ Finset.range (Module.finrank ℝ M_real + 1),
      k ≠ 2 → cliffordGradeProj Q k x = 0 := by
    intro k hk hne
    have hklt : k < 4 :=
      Nat.lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.succ_le_succ hdim)
    interval_cases k
    · exact h0
    · exact h1
    · exact (hne rfl).elim
    · exact h3
  by_cases h2mem : 2 ∈ Finset.range (Module.finrank ℝ M_real + 1)
  · rw [Finset.sum_eq_single 2] at hsum
    · exact hsum.symm
    · intro k hk hne
      exact hrange k hk hne
    · intro hnot
      exact (hnot h2mem).elim
  · have hzero : x = 0 := by
      calc
        x = ∑ k ∈ Finset.range (Module.finrank ℝ M_real + 1), cliffordGradeProj Q k x := hsum
        _ = 0 := Finset.sum_eq_zero fun k hk => hrange k hk (fun h => h2mem (h ▸ hk))
    subst hzero
    simp

end RealDimLeThreeBivector

end Part4C_ReverseGradeTwo

section Part4D_MaurerCartanCoupling

variable {R_coeff : Type*} [CommRing R_coeff]
variable {M : Type*} [AddCommGroup M] [Module R_coeff M]
variable {Q : QuadraticForm R_coeff M}

/-- Darboux spin connection equals R1 right-logarithmic form `actionThetaR K u ![x]`. -/
theorem clRotorDarbouxConnection_eq_actionThetaR
    (K : LieActionLane R_coeff (CliffordAlgebra Q))
    (R_cl : CliffordAlgebra Q)
    (h_mul_rev : R_cl * CliffordAlgebra.reverse R_cl = 1)
    (h_rev_mul : CliffordAlgebra.reverse R_cl * R_cl = 1)
    (x : K.L) :
    clRotorDarbouxConnection R_cl (K.operatorAction x R_cl) =
      actionThetaR K (clRotorUnit R_cl h_mul_rev h_rev_mul) ![x] :=
  rfl

/-- Sign dictionary connecting Cartan–Hestenes Darboux connection to R1 `thetaR`, `-thetaL u⁻¹`,
and `-pureGaugeForm`. -/
theorem clRotorDarbouxConnection_eq_thetaR
    (K : DerivationLieLane R_coeff (CliffordAlgebra Q))
    (R_cl : CliffordAlgebra Q)
    (h_mul_rev : R_cl * CliffordAlgebra.reverse R_cl = 1)
    (h_rev_mul : CliffordAlgebra.reverse R_cl * R_cl = 1)
    (x : K.L) :
    clRotorDarbouxConnection R_cl (K.operatorAction x R_cl) =
        thetaR K (clRotorUnit R_cl h_mul_rev h_rev_mul) ![x] ∧
      clRotorDarbouxConnection R_cl (K.operatorAction x R_cl) =
        -(thetaL K (clRotorUnit R_cl h_mul_rev h_rev_mul)⁻¹ ![x]) ∧
      clRotorDarbouxConnection R_cl (K.operatorAction x R_cl) =
        -(InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm (algDerivOfLane K x)
          (clRotorUnit R_cl h_mul_rev h_rev_mul)) := by
  let u := clRotorUnit R_cl h_mul_rev h_rev_mul
  refine ⟨rfl, ?_, ?_⟩
  · exact AlternatingMap.congr_fun (thetaR_eq_neg_thetaL_inv K u) ![x]
  · have h1 := AlternatingMap.congr_fun (thetaR_eq_neg_thetaL_inv K u) ![x]
    have h2 := pureGaugeForm_lane_eq_thetaL_inv K x u
    dsimp [clRotorDarbouxConnection]
    rw [h2]
    exact h1

/-- Frame derivative via R1 `actionExteriorDerivative_actionConjugateForm`:
`D_x(R γ R̃) = [θ_R(u)(x), R γ R̃] + R (D_x γ) R̃`. -/
theorem clRotor_actionExteriorDerivative_frame
    (K : LieActionLane R_coeff (CliffordAlgebra Q))
    (hK : IsLeibnizAction K)
    (R_cl : CliffordAlgebra Q)
    (h_mul_rev : R_cl * CliffordAlgebra.reverse R_cl = 1)
    (h_rev_mul : CliffordAlgebra.reverse R_cl * R_cl = 1)
    (γ : CliffordAlgebra Q) (x : K.L) :
    K.operatorAction x (clRotorFrameVector R_cl γ) =
      clCommutator (actionThetaR K (clRotorUnit R_cl h_mul_rev h_rev_mul) ![x])
          (clRotorFrameVector R_cl γ) +
        clRotorFrameVector R_cl (K.operatorAction x γ) := by
  let u := clRotorUnit R_cl h_mul_rev h_rev_mul
  let γ₀ : ActionOperatorForm K 0 := actionZeroFormEquiv K γ
  have hconj := actionExteriorDerivative_actionConjugateForm K hK u γ₀
  have heval := AlternatingMap.congr_fun hconj ![x]
  simp only [actionExteriorDerivative_zero_apply, actionConjugateForm_apply,
    Matrix.cons_val_zero, AlternatingMap.sub_apply, AlternatingMap.add_apply,
    pow_zero, one_smul, reindexForm_apply] at heval
  have hlhs : InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate u (γ₀ Fin.elim0) =
      clRotorFrameVector R_cl γ := by
    simp [InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate, γ₀, u,
      clRotorFrameVector]
  have hrhs0 : InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate u
        (K.operatorAction x (γ₀ Fin.elim0)) =
      clRotorFrameVector R_cl (K.operatorAction x γ) := by
    simp [InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate, γ₀, u,
      clRotorFrameVector]
  have hwL :
      actionWedge K (actionThetaR K u) (actionConjugateForm K u γ₀)
          (![x] ∘ finCongr (Nat.add_comm 1 0)) =
        actionThetaR K u ![x] * clRotorFrameVector R_cl γ := by
    rw [actionWedge_succ_zero]
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.flip_apply, LinearMap.mul_apply',
      actionConjugateForm_apply]
    rw [hlhs]
    rfl
  have hwR :
      actionWedge K (actionConjugateForm K u γ₀) (actionThetaR K u) ![x] =
        clRotorFrameVector R_cl γ * actionThetaR K u ![x] := by
    rw [actionWedge_zero_left]
    simp only [reindexForm_apply, LinearMap.compAlternatingMap_apply, LinearMap.mul_apply',
      actionConjugateForm_apply]
    rw [hlhs]
    rfl
  rw [hlhs, hrhs0, hwL, hwR] at heval
  rw [heval]
  dsimp [clCommutator]
  abel

theorem clRotor_actionExteriorDerivative_frame_const
    (K : LieActionLane R_coeff (CliffordAlgebra Q))
    (hK : IsLeibnizAction K)
    (R_cl : CliffordAlgebra Q)
    (h_mul_rev : R_cl * CliffordAlgebra.reverse R_cl = 1)
    (h_rev_mul : CliffordAlgebra.reverse R_cl * R_cl = 1)
    (γ : CliffordAlgebra Q) (x : K.L) (hconst : K.operatorAction x γ = 0) :
    K.operatorAction x (clRotorFrameVector R_cl γ) =
      clCommutator (actionThetaR K (clRotorUnit R_cl h_mul_rev h_rev_mul) ![x])
        (clRotorFrameVector R_cl γ) := by
  rw [clRotor_actionExteriorDerivative_frame K hK R_cl h_mul_rev h_rev_mul γ x, hconst]
  dsimp [clRotorFrameVector]
  simp only [mul_zero, zero_mul, add_zero]

/-- Spin-connection Maurer–Cartan equation `dΩ - Ω ∧ Ω = 0` on `LieActionLane` and
canonical `thetaL` flatness `ceCurvature K (thetaL K u⁻¹) = 0` on `DerivationLieLane`. -/
theorem clRotorDarboux_maurerCartan
    (K : LieActionLane R_coeff (CliffordAlgebra Q))
    (hK : IsLeibnizAction K)
    (R_cl : CliffordAlgebra Q)
    (h_mul_rev : R_cl * CliffordAlgebra.reverse R_cl = 1)
    (h_rev_mul : CliffordAlgebra.reverse R_cl * R_cl = 1) :
    actionExteriorDerivative K 1 (actionThetaR K (clRotorUnit R_cl h_mul_rev h_rev_mul)) -
      actionWedge K (actionThetaR K (clRotorUnit R_cl h_mul_rev h_rev_mul))
        (actionThetaR K (clRotorUnit R_cl h_mul_rev h_rev_mul)) = 0 := by
  rw [actionThetaR_maurerCartan K hK (clRotorUnit R_cl h_mul_rev h_rev_mul), sub_self]

theorem clRotorDarboux_derivation_maurerCartan
    (K : DerivationLieLane R_coeff (CliffordAlgebra Q))
    (R_cl : CliffordAlgebra Q)
    (h_mul_rev : R_cl * CliffordAlgebra.reverse R_cl = 1)
    (h_rev_mul : CliffordAlgebra.reverse R_cl * R_cl = 1) :
    ceExteriorDerivative K 1 (thetaR K (clRotorUnit R_cl h_mul_rev h_rev_mul)) =
        ceWedge K (thetaR K (clRotorUnit R_cl h_mul_rev h_rev_mul))
          (thetaR K (clRotorUnit R_cl h_mul_rev h_rev_mul)) ∧
      ceCurvature K (thetaL K (clRotorUnit R_cl h_mul_rev h_rev_mul)⁻¹) = 0 :=
  ⟨thetaR_maurerCartan K (clRotorUnit R_cl h_mul_rev h_rev_mul),
    thetaL_flat K (clRotorUnit R_cl h_mul_rev h_rev_mul)⁻¹⟩

/-- Lie subalgebra of `CliffordAlgebra.reverse`-commuting derivations on `CliffordAlgebra Q`. -/
def reverseCommutingDerivations (Q : QuadraticForm R_coeff M) :
    LieSubalgebra R_coeff (NonAssocDerivation.derivations R_coeff (CliffordAlgebra Q)) where
  carrier := {D | ∀ x : CliffordAlgebra Q,
    CliffordAlgebra.reverse (D.1 x) = D.1 (CliffordAlgebra.reverse x)}
  zero_mem' x := by simp
  add_mem' {D₁ D₂} h₁ h₂ x := by
    change CliffordAlgebra.reverse (D₁.1 x + D₂.1 x) =
      D₁.1 (CliffordAlgebra.reverse x) + D₂.1 (CliffordAlgebra.reverse x)
    rw [map_add, h₁ x, h₂ x]
  smul_mem' c {D} h x := by
    change CliffordAlgebra.reverse (c • D.1 x) = c • D.1 (CliffordAlgebra.reverse x)
    rw [map_smul, h x]
  lie_mem' {D₁ D₂} h₁ h₂ x := by
    change CliffordAlgebra.reverse (D₁.1 (D₂.1 x) - D₂.1 (D₁.1 x)) =
      D₁.1 (D₂.1 (CliffordAlgebra.reverse x)) - D₂.1 (D₁.1 (CliffordAlgebra.reverse x))
    rw [map_sub, h₁, h₂, h₂, h₁]

/-- Canonical `DerivationLieLane` of `CliffordAlgebra.reverse`-commuting derivations. -/
def reverseCommutingLane (Q : QuadraticForm R_coeff M) :
    DerivationLieLane R_coeff (CliffordAlgebra Q) :=
  lieSubalgebraLane (reverseCommutingDerivations Q)

/-- Inner derivation `ad B : x ↦ B * x - x * B` commutes with `reverse` whenever
`CliffordAlgebra.reverse B = -B` (in particular, for every grade-2 bivector). -/
def innerBivectorDerivation (B : CliffordAlgebra Q)
    (hB : CliffordAlgebra.reverse B = -B) :
    reverseCommutingDerivations Q := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact
      { toFun := fun x => B * x - x * B
        map_add' := fun x y => by noncomm_ring
        map_smul' := fun c x => by
          simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc, smul_sub] }
  · intro x y
    change B * (x * y) - (x * y) * B = (B * x - x * B) * y + x * (B * y - y * B)
    noncomm_ring
  · intro x
    change CliffordAlgebra.reverse (B * x - x * B) =
      B * CliffordAlgebra.reverse x - CliffordAlgebra.reverse x * B
    rw [map_sub, CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse.map_mul, hB]
    noncomm_ring

/-- Every rotor Darboux connection along `reverseCommutingLane Q` is skew under `reverse`:
`CliffordAlgebra.reverse Ω = -Ω`. -/
theorem reverseCommutingLane_thetaR_reverse_eq_neg
    (R_cl : CliffordAlgebra Q)
    (h_mul_rev : R_cl * CliffordAlgebra.reverse R_cl = 1)
    (h_rev_mul : CliffordAlgebra.reverse R_cl * R_cl = 1)
    (x : (reverseCommutingLane Q).L) :
    CliffordAlgebra.reverse
        (thetaR (reverseCommutingLane Q) (clRotorUnit R_cl h_mul_rev h_rev_mul) ![x]) =
      -(thetaR (reverseCommutingLane Q) (clRotorUnit R_cl h_mul_rev h_rev_mul) ![x]) := by
  have hder := congrArg (fun d => (reverseCommutingLane Q).operatorAction x d)
    h_mul_rev
  have hleib := (reverseCommutingLane Q).operatorAction_leibniz x R_cl
    (CliffordAlgebra.reverse R_cl)
  have hzero : (reverseCommutingLane Q).operatorAction x (1 : CliffordAlgebra Q) = 0 := by
    have h1 := (reverseCommutingLane Q).operatorAction_leibniz x 1 1
    rw [mul_one, one_mul, mul_one] at h1
    have h2 : (reverseCommutingLane Q).operatorAction x (1 : CliffordAlgebra Q) + 0 =
        (reverseCommutingLane Q).operatorAction x (1 : CliffordAlgebra Q) +
          (reverseCommutingLane Q).operatorAction x (1 : CliffordAlgebra Q) := by
      rw [add_zero]
      exact h1
    exact (add_left_cancel h2).symm
  rw [hleib, hzero] at hder
  have hcomm : (reverseCommutingLane Q).operatorAction x (CliffordAlgebra.reverse R_cl) =
      CliffordAlgebra.reverse ((reverseCommutingLane Q).operatorAction x R_cl) :=
    (x.prop R_cl).symm
  rw [hcomm] at hder
  have heq :
      clRotorDarbouxConnection R_cl ((reverseCommutingLane Q).operatorAction x R_cl) =
        thetaR (reverseCommutingLane Q) (clRotorUnit R_cl h_mul_rev h_rev_mul) ![x] :=
    rfl
  rw [← heq]
  exact clRotorDarbouxConnection_reverse_eq_neg R_cl
    ((reverseCommutingLane Q).operatorAction x R_cl) hder

end Part4D_MaurerCartanCoupling

section Part4E_SpinGroupEquivOfIsometry

variable {R_coeff : Type*} [CommRing R_coeff] [Invertible (2 : R_coeff)]
variable {M : Type*} [AddCommGroup M] [Module R_coeff M]
variable (Q : QuadraticForm R_coeff M)

omit [Invertible (2 : R_coeff)] in
private theorem spinGroup_reverse_eq_star (g : spinGroup Q) :
    CliffordAlgebra.reverse (g : CliffordAlgebra Q) = star (g : CliffordAlgebra Q) := by
  rw [CliffordAlgebra.star_def, spinGroup.involute_eq g.prop]

omit [Invertible (2 : R_coeff)] in
private theorem spinGroup_mul_reverse (g : spinGroup Q) :
    (g : CliffordAlgebra Q) * CliffordAlgebra.reverse (g : CliffordAlgebra Q) = 1 := by
  rw [spinGroup_reverse_eq_star]
  exact spinGroup.coe_mul_star_self g

omit [Invertible (2 : R_coeff)] in
private theorem spinGroup_reverse_mul (g : spinGroup Q) :
    CliffordAlgebra.reverse (g : CliffordAlgebra Q) * (g : CliffordAlgebra Q) = 1 := by
  rw [spinGroup_reverse_eq_star]
  exact spinGroup.coe_star_mul_self g

private def spinGroupUnit (g : spinGroup Q) : (CliffordAlgebra Q)ˣ :=
  clRotorUnit (g : CliffordAlgebra Q) (spinGroup_mul_reverse Q g) (spinGroup_reverse_mul Q g)

private theorem spinGroup_conj_ι_mem_range (g : spinGroup Q) (v : M) :
    (g : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        CliffordAlgebra.reverse (g : CliffordAlgebra Q) ∈
      LinearMap.range (CliffordAlgebra.ι Q) := by
  have hmem := spinGroup.conjAct_smul_ι_mem_range_ι (x := spinGroupUnit Q g) g.prop v
  simpa [spinGroupUnit, ConjAct.units_smul_def, mul_assoc] using hmem

private def ιRangeEquiv : M ≃ₗ[R_coeff] LinearMap.range (CliffordAlgebra.ι Q) :=
  LinearEquiv.ofInjective (CliffordAlgebra.ι Q) (clifford_ι_injective Q)

private theorem hTrace_cl_algebraMap (r : R_coeff) :
    hTrace_cl Q (algebraMap R_coeff (CliffordAlgebra Q) r) = r := by
  change ExteriorAlgebra.algebraMapInv
      (CliffordAlgebra.equivExterior Q (algebraMap R_coeff (CliffordAlgebra Q) r)) = r
  rw [equivExterior_algebraMap]
  exact AlgHom.commutes (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra R_coeff M →ₐ[R_coeff] R_coeff) r

/-- Every `g : spinGroup Q` induces an isometry in `Q.IsometryEquiv Q` via `v ↦ ι⁻¹(g ι(v) reverse g)`. -/
def spinGroupIsometryEquiv (g : spinGroup Q) : Q.IsometryEquiv Q := by
  let f : M →ₗ[R_coeff] M :=
    { toFun := fun v => (ιRangeEquiv Q).symm
        ⟨(g : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
          CliffordAlgebra.reverse (g : CliffordAlgebra Q),
          spinGroup_conj_ι_mem_range Q g v⟩
      map_add' := fun v w => by
        apply (ιRangeEquiv Q).injective
        apply Subtype.ext
        simp only [ιRangeEquiv, LinearEquiv.apply_symm_apply, map_add, mul_add, add_mul,
          Submodule.coe_add]
      map_smul' := fun c v => by
        apply (ιRangeEquiv Q).injective
        apply Subtype.ext
        simp only [ιRangeEquiv, LinearEquiv.apply_symm_apply, map_smul, mul_smul_comm,
          smul_mul_assoc, RingHom.id_apply, SetLike.val_smul] }
  let finv : M →ₗ[R_coeff] M :=
    { toFun := fun v => (ιRangeEquiv Q).symm
        ⟨CliffordAlgebra.reverse (g : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
          (g : CliffordAlgebra Q),
          by
            have h := spinGroup_conj_ι_mem_range Q (star g) v
            simpa [spinGroup.coe_star, ← spinGroup_reverse_eq_star Q g,
              CliffordAlgebra.reverse_reverse] using h⟩
      map_add' := fun v w => by
        apply (ιRangeEquiv Q).injective
        apply Subtype.ext
        simp only [ιRangeEquiv, LinearEquiv.apply_symm_apply, map_add, mul_add, add_mul,
          Submodule.coe_add]
      map_smul' := fun c v => by
        apply (ιRangeEquiv Q).injective
        apply Subtype.ext
        simp only [ιRangeEquiv, LinearEquiv.apply_symm_apply, map_smul, mul_smul_comm,
          smul_mul_assoc, RingHom.id_apply, SetLike.val_smul] }
  refine
    { toLinearEquiv :=
        { toLinearMap := f
          invFun := finv
          left_inv := fun v => by
            apply (ιRangeEquiv Q).injective
            apply Subtype.ext
            change CliffordAlgebra.ι Q (finv (f v)) = CliffordAlgebra.ι Q v
            have hf : CliffordAlgebra.ι Q (f v) =
                (g : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
                  CliffordAlgebra.reverse (g : CliffordAlgebra Q) :=
              congrArg Subtype.val ((ιRangeEquiv Q).apply_symm_apply _)
            have hfinv : CliffordAlgebra.ι Q (finv (f v)) =
                CliffordAlgebra.reverse (g : CliffordAlgebra Q) * CliffordAlgebra.ι Q (f v) *
                  (g : CliffordAlgebra Q) :=
              congrArg Subtype.val ((ιRangeEquiv Q).apply_symm_apply _)
            rw [hfinv, hf]
            calc
              CliffordAlgebra.reverse (g : CliffordAlgebra Q) *
                  ((g : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
                    CliffordAlgebra.reverse (g : CliffordAlgebra Q)) *
                  (g : CliffordAlgebra Q)
                  = (CliffordAlgebra.reverse (g : CliffordAlgebra Q) * (g : CliffordAlgebra Q)) *
                      CliffordAlgebra.ι Q v *
                      (CliffordAlgebra.reverse (g : CliffordAlgebra Q) * (g : CliffordAlgebra Q)) := by
                    simp only [mul_assoc]
              _ = 1 * CliffordAlgebra.ι Q v * 1 := by rw [spinGroup_reverse_mul]
              _ = CliffordAlgebra.ι Q v := by simp
          right_inv := fun v => by
            apply (ιRangeEquiv Q).injective
            apply Subtype.ext
            change CliffordAlgebra.ι Q (f (finv v)) = CliffordAlgebra.ι Q v
            have hfinv : CliffordAlgebra.ι Q (finv v) =
                CliffordAlgebra.reverse (g : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
                  (g : CliffordAlgebra Q) :=
              congrArg Subtype.val ((ιRangeEquiv Q).apply_symm_apply _)
            have hf : CliffordAlgebra.ι Q (f (finv v)) =
                (g : CliffordAlgebra Q) * CliffordAlgebra.ι Q (finv v) *
                  CliffordAlgebra.reverse (g : CliffordAlgebra Q) :=
              congrArg Subtype.val ((ιRangeEquiv Q).apply_symm_apply _)
            rw [hf, hfinv]
            calc
              (g : CliffordAlgebra Q) *
                  (CliffordAlgebra.reverse (g : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
                    (g : CliffordAlgebra Q)) *
                  CliffordAlgebra.reverse (g : CliffordAlgebra Q)
                  = ((g : CliffordAlgebra Q) * CliffordAlgebra.reverse (g : CliffordAlgebra Q)) *
                      CliffordAlgebra.ι Q v *
                      ((g : CliffordAlgebra Q) * CliffordAlgebra.reverse (g : CliffordAlgebra Q)) := by
                    simp only [mul_assoc]
              _ = 1 * CliffordAlgebra.ι Q v * 1 := by rw [spinGroup_mul_reverse]
              _ = CliffordAlgebra.ι Q v := by simp }
      map_app' := fun v => by
        have hf : CliffordAlgebra.ι Q (f v) =
            (g : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
              CliffordAlgebra.reverse (g : CliffordAlgebra Q) :=
          congrArg Subtype.val ((ιRangeEquiv Q).apply_symm_apply _)
        have hsq : algebraMap R_coeff (CliffordAlgebra Q) (Q (f v)) =
            algebraMap R_coeff (CliffordAlgebra Q) (Q v) := by
          rw [← CliffordAlgebra.ι_sq_scalar, hf]
          calc
            ((g : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
                CliffordAlgebra.reverse (g : CliffordAlgebra Q)) *
                ((g : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
                  CliffordAlgebra.reverse (g : CliffordAlgebra Q))
                = (g : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
                    (CliffordAlgebra.reverse (g : CliffordAlgebra Q) * (g : CliffordAlgebra Q)) *
                    CliffordAlgebra.ι Q v * CliffordAlgebra.reverse (g : CliffordAlgebra Q) := by
                  simp only [mul_assoc]
            _ = (g : CliffordAlgebra Q) * (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v) *
                  CliffordAlgebra.reverse (g : CliffordAlgebra Q) := by
                  rw [spinGroup_reverse_mul, mul_one]; simp only [mul_assoc]
            _ = (g : CliffordAlgebra Q) * algebraMap R_coeff (CliffordAlgebra Q) (Q v) *
                  CliffordAlgebra.reverse (g : CliffordAlgebra Q) := by
                  rw [CliffordAlgebra.ι_sq_scalar]
            _ = algebraMap R_coeff (CliffordAlgebra Q) (Q v) *
                  ((g : CliffordAlgebra Q) * CliffordAlgebra.reverse (g : CliffordAlgebra Q)) := by
                  rw [← Algebra.commutes (Q v) (g : CliffordAlgebra Q), mul_assoc]
            _ = algebraMap R_coeff (CliffordAlgebra Q) (Q v) := by
                  rw [spinGroup_mul_reverse, mul_one]
        have htr := congrArg (hTrace_cl Q) hsq
        rwa [hTrace_cl_algebraMap, hTrace_cl_algebraMap] at htr }

@[simp] theorem ι_spinGroupIsometryEquiv (g : spinGroup Q) (v : M) :
    CliffordAlgebra.ι Q (spinGroupIsometryEquiv Q g v) =
      (g : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        CliffordAlgebra.reverse (g : CliffordAlgebra Q) :=
  congrArg Subtype.val ((ιRangeEquiv Q).apply_symm_apply _)

/-- Group homomorphism `spinGroup Q →* Q.IsometryEquiv Q` (reusing M2.1's `quadraticIsometryEquivGroup`). -/
def spinGroupToIsometryHom : spinGroup Q →* Q.IsometryEquiv Q where
  toFun := spinGroupIsometryEquiv Q
  map_one' := by
    apply DFunLike.ext
    intro v
    apply clifford_ι_injective Q
    change CliffordAlgebra.ι Q (spinGroupIsometryEquiv Q 1 v) = CliffordAlgebra.ι Q v
    rw [ι_spinGroupIsometryEquiv]
    simp
  map_mul' g₁ g₂ := by
    apply DFunLike.ext
    intro v
    apply clifford_ι_injective Q
    change CliffordAlgebra.ι Q (spinGroupIsometryEquiv Q (g₁ * g₂) v) =
      CliffordAlgebra.ι Q (spinGroupIsometryEquiv Q g₁ (spinGroupIsometryEquiv Q g₂ v))
    rw [ι_spinGroupIsometryEquiv, ι_spinGroupIsometryEquiv, ι_spinGroupIsometryEquiv]
    simp only [Submonoid.coe_mul, CliffordAlgebra.reverse.map_mul, mul_assoc]

/-- Lifting `spinGroupToIsometryHom Q g` via `CliffordAlgebra.equivOfIsometry` agrees on every
`x : CliffordAlgebra Q` with rotor sandwiching `g * x * reverse g`. -/
theorem equivOfIsometry_spinGroupToIsometryHom (g : spinGroup Q) (x : CliffordAlgebra Q) :
    CliffordAlgebra.equivOfIsometry (spinGroupToIsometryHom Q g) x =
      (g : CliffordAlgebra Q) * x * CliffordAlgebra.reverse (g : CliffordAlgebra Q) := by
  have h :
      (CliffordAlgebra.equivOfIsometry (spinGroupToIsometryHom Q g)).toAlgHom =
        (clRotorConjugateAlgEquiv (g : CliffordAlgebra Q)
          (spinGroup_mul_reverse Q g) (spinGroup_reverse_mul Q g)).toAlgHom := by
    apply CliffordAlgebra.hom_ext
    ext v
    change CliffordAlgebra.equivOfIsometry (spinGroupToIsometryHom Q g) (CliffordAlgebra.ι Q v) =
      clRotorFrameVector (g : CliffordAlgebra Q) (CliffordAlgebra.ι Q v)
    rw [CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
    exact ι_spinGroupIsometryEquiv Q g v
  exact AlgHom.congr_fun h x

/-- M2.1 invariance corollaries for `spinGroup Q` rotor conjugation. -/
theorem spinGroup_conj_cliffordGradeProj (g : spinGroup Q) (k : ℕ) (x : CliffordAlgebra Q) :
    (g : CliffordAlgebra Q) * cliffordGradeProj Q k x *
        CliffordAlgebra.reverse (g : CliffordAlgebra Q) =
      cliffordGradeProj Q k
        ((g : CliffordAlgebra Q) * x * CliffordAlgebra.reverse (g : CliffordAlgebra Q)) := by
  rw [← equivOfIsometry_spinGroupToIsometryHom, ← equivOfIsometry_spinGroupToIsometryHom,
    cliffordGradeProj_equivOfIsometry]

theorem spinGroup_conj_hTrace_cl (g : spinGroup Q) (x : CliffordAlgebra Q) :
    hTrace_cl Q ((g : CliffordAlgebra Q) * x * CliffordAlgebra.reverse (g : CliffordAlgebra Q)) =
      hTrace_cl Q x := by
  rw [← equivOfIsometry_spinGroupToIsometryHom, hTrace_cl_equivOfIsometry]

theorem spinGroup_conj_cliffordKreinPairing (g : spinGroup Q) (u v : CliffordAlgebra Q) :
    cliffordKreinPairing Q
        ((g : CliffordAlgebra Q) * u * CliffordAlgebra.reverse (g : CliffordAlgebra Q))
        ((g : CliffordAlgebra Q) * v * CliffordAlgebra.reverse (g : CliffordAlgebra Q)) =
      cliffordKreinPairing Q u v := by
  rw [← equivOfIsometry_spinGroupToIsometryHom, ← equivOfIsometry_spinGroupToIsometryHom,
    cliffordKreinPairing_equivOfIsometry]

/-- Specialization to `SplitSpinGroup n →* SplitQuadraticSymmetry n` over `ℝ`. -/
def splitSpinToQuadraticSymmetryHom (n : ℕ) :
    InfoGeometry.Algebraic.SplitSignature.SplitSpinGroup n →*
      InfoGeometry.Algebraic.SplitSignature.SplitQuadraticSymmetry n :=
  (InfoGeometry.Algebraic.SplitSignature.splitQuadraticSymmetryMulEquiv n).symm.toMonoidHom.comp
    (spinGroupToIsometryHom (InfoGeometry.Algebraic.SplitSignature.splitQuadraticForm n))

theorem splitCliffordLift_splitSpinToQuadraticSymmetryHom (n : ℕ)
    (g : InfoGeometry.Algebraic.SplitSignature.SplitSpinGroup n)
    (x : InfoGeometry.Algebraic.SplitSignature.Cl_nn n) :
    InfoGeometry.Algebraic.SplitSignature.splitCliffordLift n
        (splitSpinToQuadraticSymmetryHom n g) x =
      (g : InfoGeometry.Algebraic.SplitSignature.Cl_nn n) * x *
        CliffordAlgebra.reverse (g : InfoGeometry.Algebraic.SplitSignature.Cl_nn n) :=
  equivOfIsometry_spinGroupToIsometryHom
    (InfoGeometry.Algebraic.SplitSignature.splitQuadraticForm n) g x

end Part4E_SpinGroupEquivOfIsometry

end AbstractCliffordRotorCalculus

/-!
## Section 5: Concrete `Cl(1,1)` Specialization to `M₂(ℝ)` (`cl11EquivMat` and `cl11StandardEquiv`)
-/

section Cl11HyperbolicRotorSpecialization

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Clifford.GradedGraceContraction

private local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

/-- Abstract `Cl(1,1)` hyperbolic rotor `cosh θ • 1 + sinh θ • J1_cl`. -/
def cl11HyperbolicRotor (θ : ℝ) : CliffordAlgebra q11 :=
  Real.cosh θ • (1 : CliffordAlgebra q11) + Real.sinh θ • J1_cl

/-- Abstract `Cl(1,1)` rapidity derivative `sinh θ • 1 + cosh θ • J1_cl`. -/
def cl11HyperbolicRotorDeriv (θ : ℝ) : CliffordAlgebra q11 :=
  Real.sinh θ • (1 : CliffordAlgebra q11) + Real.cosh θ • J1_cl

theorem reverse_J1_cl : CliffordAlgebra.reverse J1_cl = -J1_cl := by
  apply cl11EquivMat.injective
  have h1 : J1_cl = CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (0, 1) := rfl
  rw [h1, CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι,
    CliffordAlgebra.reverse_ι, map_neg, map_mul, map_mul,
    cl11EquivMat_iota_pos, cl11EquivMat_iota_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Eplus, Eminus]

theorem J1_cl_mem_cliffordGradeSubmodule_two :
    J1_cl ∈ cliffordGradeSubmodule q11 2 := by
  rw [mem_cliffordGradeSubmodule_iff]
  apply (CliffordAlgebra.equivExterior q11).injective
  change (CliffordAlgebra.equivExterior q11)
      ((CliffordAlgebra.equivExterior q11).symm
        (exteriorGradeProj ℝ Vec11 2 (CliffordAlgebra.equivExterior q11 J1_cl))) =
    CliffordAlgebra.equivExterior q11 J1_cl
  rw [LinearEquiv.apply_symm_apply]
  have hmem : CliffordAlgebra.equivExterior q11 J1_cl ∈ ⋀[ℝ]^2 Vec11 := by
    have heq : CliffordAlgebra.equivExterior q11 J1_cl =
        ExteriorAlgebra.ι ℝ (1, 0) * ExteriorAlgebra.ι ℝ (0, 1) := by
      change CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof
          (CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (0, 1)) = _
      rw [CliffordAlgebra.changeForm_ι_mul_ι]
      have hassoc : QuadraticMap.associated (R := ℝ) (-q11) (1, 0) (0, 1) = 0 := by
        simp [QuadraticMap.associated_apply, q11]
      rw [hassoc, map_zero, sub_zero]
    rw [heq, ExteriorAlgebra.exteriorPower, pow_two]
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
  exact exteriorGradeProj_of_mem hmem

theorem cl11HyperbolicRotor_reverse (θ : ℝ) :
    CliffordAlgebra.reverse (cl11HyperbolicRotor θ) =
      Real.cosh θ • (1 : CliffordAlgebra q11) - Real.sinh θ • J1_cl := by
  dsimp [cl11HyperbolicRotor]
  rw [map_add, map_smul, map_smul, CliffordAlgebra.reverse.map_one, reverse_J1_cl,
    smul_neg, sub_eq_add_neg]

theorem cl11HyperbolicRotor_mul_reverse (θ : ℝ) :
    cl11HyperbolicRotor θ * CliffordAlgebra.reverse (cl11HyperbolicRotor θ) = 1 := by
  rw [cl11HyperbolicRotor_reverse, cl11HyperbolicRotor]
  have hsq : J1_cl * J1_cl = 1 := J1_cl_sq
  calc
    (Real.cosh θ • (1 : CliffordAlgebra q11) + Real.sinh θ • J1_cl) *
        (Real.cosh θ • (1 : CliffordAlgebra q11) - Real.sinh θ • J1_cl)
        = (Real.cosh θ * Real.cosh θ) • (1 : CliffordAlgebra q11) -
            (Real.sinh θ * Real.sinh θ) • (J1_cl * J1_cl) := by
          simp only [mul_sub, add_mul, smul_mul_smul, mul_one, one_mul,
            mul_comm (Real.cosh θ) (Real.sinh θ)]
          abel
    _ = (Real.cosh θ ^ 2 - Real.sinh θ ^ 2) • (1 : CliffordAlgebra q11) := by
          rw [hsq, ← sq, ← sq, sub_smul]
    _ = 1 := by rw [Real.cosh_sq_sub_sinh_sq, one_smul]

theorem cl11HyperbolicRotor_reverse_mul (θ : ℝ) :
    CliffordAlgebra.reverse (cl11HyperbolicRotor θ) * cl11HyperbolicRotor θ = 1 := by
  rw [cl11HyperbolicRotor_reverse, cl11HyperbolicRotor]
  calc
    (Real.cosh θ • (1 : CliffordAlgebra q11) - Real.sinh θ • J1_cl) *
        (Real.cosh θ • (1 : CliffordAlgebra q11) + Real.sinh θ • J1_cl)
        = (Real.cosh θ * Real.cosh θ) • (1 : CliffordAlgebra q11) -
            (Real.sinh θ * Real.sinh θ) • (J1_cl * J1_cl) := by
          simp only [sub_mul, mul_add, smul_mul_smul, mul_one, one_mul,
            mul_comm (Real.cosh θ) (Real.sinh θ)]
          abel
    _ = (Real.cosh θ ^ 2 - Real.sinh θ ^ 2) • (1 : CliffordAlgebra q11) := by
          rw [J1_cl_sq, ← sq, ← sq, sub_smul]
    _ = 1 := by rw [Real.cosh_sq_sub_sinh_sq, one_smul]

theorem cl11HyperbolicRotor_dnorm (θ : ℝ) :
    cl11HyperbolicRotorDeriv θ * CliffordAlgebra.reverse (cl11HyperbolicRotor θ) +
      cl11HyperbolicRotor θ * CliffordAlgebra.reverse (cl11HyperbolicRotorDeriv θ) = 0 := by
  have hrevD : CliffordAlgebra.reverse (cl11HyperbolicRotorDeriv θ) =
      Real.sinh θ • (1 : CliffordAlgebra q11) - Real.cosh θ • J1_cl := by
    dsimp [cl11HyperbolicRotorDeriv]
    rw [map_add, map_smul, map_smul, CliffordAlgebra.reverse.map_one, reverse_J1_cl,
      smul_neg, sub_eq_add_neg]
  rw [cl11HyperbolicRotor_reverse, hrevD, cl11HyperbolicRotor, cl11HyperbolicRotorDeriv]
  simp only [sub_eq_add_neg, mul_add, add_mul, mul_neg, smul_mul_smul,
    mul_one, one_mul, J1_cl_sq, mul_comm (Real.cosh θ) (Real.sinh θ)]
  abel

/-- Abstract `Cl(1,1)` Darboux connection of `cl11HyperbolicRotor θ` equals `J1_cl`,
whose `reverse` is `-J1_cl`. -/
theorem cl11HyperbolicRotor_darboux (θ : ℝ) :
    clRotorDarbouxConnection (cl11HyperbolicRotor θ) (cl11HyperbolicRotorDeriv θ) = J1_cl := by
  rw [clRotorDarbouxConnection, cl11HyperbolicRotorDeriv, cl11HyperbolicRotor_reverse]
  calc
    (Real.sinh θ • (1 : CliffordAlgebra q11) + Real.cosh θ • J1_cl) *
        (Real.cosh θ • (1 : CliffordAlgebra q11) - Real.sinh θ • J1_cl)
        = (Real.cosh θ * Real.cosh θ - Real.sinh θ * Real.sinh θ) • J1_cl := by
          simp only [mul_sub, add_mul, smul_mul_smul, mul_one, one_mul,
            J1_cl_sq, mul_comm (Real.sinh θ) (Real.cosh θ)]
          rw [sub_smul]
          abel
    _ = J1_cl := by
          rw [← sq, ← sq, Real.cosh_sq_sub_sinh_sq, one_smul]

theorem cl11HyperbolicRotor_darboux_reverse (θ : ℝ) :
    CliffordAlgebra.reverse
        (clRotorDarbouxConnection (cl11HyperbolicRotor θ) (cl11HyperbolicRotorDeriv θ)) =
      -(clRotorDarbouxConnection (cl11HyperbolicRotor θ) (cl11HyperbolicRotorDeriv θ)) :=
  clRotorDarbouxConnection_reverse_eq_neg (cl11HyperbolicRotor θ)
    (cl11HyperbolicRotorDeriv θ) (cl11HyperbolicRotor_dnorm θ)

private theorem iota_mem_pinGroup_of_sq_eq_neg_one (v : Vec11) (hq : q11 v = -1) :
    CliffordAlgebra.ι q11 v ∈ pinGroup q11 := by
  let u : (CliffordAlgebra q11)ˣ :=
    { val := CliffordAlgebra.ι q11 v
      inv := -CliffordAlgebra.ι q11 v
      val_inv := by
        rw [mul_neg, CliffordAlgebra.ι_sq_scalar, hq, map_neg, map_one, neg_neg]
      inv_val := by
        rw [neg_mul, CliffordAlgebra.ι_sq_scalar, hq, map_neg, map_one, neg_neg] }
  refine ⟨⟨u, Subgroup.subset_closure ⟨v, rfl⟩, rfl⟩, ?_⟩
  rw [SetLike.mem_coe, Unitary.mem_iff]
  constructor
  · rw [CliffordAlgebra.star_ι, neg_mul, CliffordAlgebra.ι_sq_scalar, hq, map_neg, map_one,
      neg_neg]
  · rw [CliffordAlgebra.star_ι, mul_neg, CliffordAlgebra.ι_sq_scalar, hq, map_neg, map_one,
      neg_neg]

/-- `cl11HyperbolicRotor θ` belongs to `spinGroup q11` (factoring as two timelike vectors). -/
theorem cl11HyperbolicRotor_mem_spinGroup (θ : ℝ) :
    cl11HyperbolicRotor θ ∈ spinGroup q11 := by
  have hfac : cl11HyperbolicRotor θ =
      CliffordAlgebra.ι q11 (0, -1) *
        CliffordAlgebra.ι q11 (Real.sinh θ, Real.cosh θ) := by
    have hv1 : (0, (-1 : ℝ)) = -((0 : ℝ), 1) := by ext <;> simp
    have hv2 : (Real.sinh θ, Real.cosh θ) =
        Real.sinh θ • (1, (0 : ℝ)) + Real.cosh θ • ((0 : ℝ), 1) := by
      ext <;> simp
    rw [hv1, hv2, map_neg, map_add, map_smul, map_smul, neg_mul, mul_add,
      mul_smul_comm, mul_smul_comm, neg_add]
    have h10 : -((CliffordAlgebra.ι q11 (0, 1)) * (CliffordAlgebra.ι q11 (1, 0))) = J1_cl := by
      apply cl11EquivMat.injective
      have h1 : J1_cl = CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (0, 1) := rfl
      rw [h1, map_neg, map_mul, map_mul, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Eplus, Eminus]
    have h01 : -((CliffordAlgebra.ι q11 (0, 1)) * (CliffordAlgebra.ι q11 (0, 1))) = 1 := by
      rw [CliffordAlgebra.ι_sq_scalar]
      have hq : q11 (0, 1) = -1 := by simp [q11]
      rw [hq, map_neg, map_one, neg_neg]
    rw [← smul_neg, h10, ← smul_neg, h01, add_comm]
    rfl
  rw [hfac]
  change CliffordAlgebra.ι q11 (0, -1) * CliffordAlgebra.ι q11 (Real.sinh θ, Real.cosh θ) ∈
      pinGroup q11 ⊓ (CliffordAlgebra.even q11).toSubring.toSubmonoid
  refine ⟨?_, ?_⟩
  · apply Submonoid.mul_mem
    · exact iota_mem_pinGroup_of_sq_eq_neg_one (0, -1) (by simp [q11])
    · refine iota_mem_pinGroup_of_sq_eq_neg_one (Real.sinh θ, Real.cosh θ) ?_
      simp [q11]
      have h := Real.cosh_sq_sub_sinh_sq θ
      linarith
  · exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero q11 (0, -1) (Real.sinh θ, Real.cosh θ)

/-- Direct `cl11EquivMat` images of `cl11HyperbolicRotor θ` and its Darboux connection. -/
theorem cl11EquivMat_cl11HyperbolicRotor (θ : ℝ) :
    cl11EquivMat (cl11HyperbolicRotor θ) =
      Real.cosh θ • (1 : Mat2) + Real.sinh θ • J1 := by
  have hJ : cl11EquivMat J1_cl = J1 := by
    have h1 : J1_cl = CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (0, 1) := rfl
    rw [h1, map_mul, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg, Eplus_mul_Eminus]
  rw [cl11HyperbolicRotor, map_add, map_smul, map_smul, map_one, hJ]

theorem cl11EquivMat_cl11HyperbolicRotor_darboux (θ : ℝ) :
    cl11EquivMat
        (clRotorDarbouxConnection (cl11HyperbolicRotor θ) (cl11HyperbolicRotorDeriv θ)) =
      J1 := by
  rw [cl11HyperbolicRotor_darboux]
  have h1 : J1_cl = CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (0, 1) := rfl
  rw [h1, map_mul, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg, Eplus_mul_Eminus]

/-- Under `cl11StandardEquiv = walshConjugation ∘ cl11EquivMat`, `cl11HyperbolicRotor θ`
specializes identically to `hyperbolicRotor θ`, its reverse to `hyperbolicRotorReverse θ`,
and its Darboux connection to `cl11BoostBivector`. -/
theorem walshConjugation_cl11EquivMat_hyperbolicRotor (θ : ℝ) :
    walshConjugation (cl11EquivMat (cl11HyperbolicRotor θ)) = hyperbolicRotor θ := by
  change cl11StandardEquiv (cl11HyperbolicRotor θ) = hyperbolicRotor θ
  rw [cl11HyperbolicRotor, map_add, map_smul, map_smul, map_one, cl11StandardEquiv_J1_cl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eplus, hyperbolicRotor, -Real.cosh_sub_sinh, sub_eq_add_neg]

theorem walshConjugation_cl11EquivMat_hyperbolicRotorReverse (θ : ℝ) :
    walshConjugation (cl11EquivMat (CliffordAlgebra.reverse (cl11HyperbolicRotor θ))) =
      hyperbolicRotorReverse θ := by
  change cl11StandardEquiv (CliffordAlgebra.reverse (cl11HyperbolicRotor θ)) =
    hyperbolicRotorReverse θ
  rw [cl11HyperbolicRotor_reverse, map_sub, map_smul, map_smul, map_one,
    cl11StandardEquiv_J1_cl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eplus, hyperbolicRotorReverse, -Real.cosh_sub_sinh, sub_eq_add_neg]

theorem walshConjugation_cl11EquivMat_darboux (θ : ℝ) :
    walshConjugation
        (cl11EquivMat
          (clRotorDarbouxConnection (cl11HyperbolicRotor θ) (cl11HyperbolicRotorDeriv θ))) =
      cl11BoostBivector := by
  change cl11StandardEquiv
      (clRotorDarbouxConnection (cl11HyperbolicRotor θ) (cl11HyperbolicRotorDeriv θ)) =
    cl11BoostBivector
  rw [cl11HyperbolicRotor_darboux, cl11StandardEquiv_J1_cl]
  rfl

theorem cl11StandardEquiv_frameVector (θ : ℝ) :
    cl11StandardEquiv
        (clRotorFrameVector (cl11HyperbolicRotor θ) (CliffordAlgebra.ι q11 (1, 0))) =
      hyperbolicRotor θ * cl11FrameGamma0 * hyperbolicRotorReverse θ := by
  dsimp [clRotorFrameVector]
  rw [map_mul, map_mul, cl11StandardEquiv_iota_pos]
  change walshConjugation (cl11EquivMat (cl11HyperbolicRotor θ)) * J1 *
      walshConjugation (cl11EquivMat (CliffordAlgebra.reverse (cl11HyperbolicRotor θ))) =
    hyperbolicRotor θ * cl11FrameGamma0 * hyperbolicRotorReverse θ
  rw [walshConjugation_cl11EquivMat_hyperbolicRotor,
    walshConjugation_cl11EquivMat_hyperbolicRotorReverse]
  rfl

end Cl11HyperbolicRotorSpecialization

end InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis
