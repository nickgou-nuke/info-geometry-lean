import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import InfoGeometry.Clifford.SplitQuaternion

set_option autoImplicit false

namespace RealPauliCausalCone

open InfoGeometry.Clifford

/-- Base structure representing the 4-vector spacetime / M₂(ℝ) operator space 
    using the real Pauli matrices basis: I, σx, ε=iσy, σz. -/
structure RealPauliOp where
  t : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

/-- Trace isolates the time coordinate. -/
def trace (X : RealPauliOp) : ℝ := 2 * X.t

/-- Determinant generates the exact Split/Minkowski signature (2,2) mapping. -/
def det (X : RealPauliOp) : ℝ := X.t^2 - X.x^2 + X.y^2 - X.z^2

/-- Scalar multiplication representing the continuous scaling group. -/
def smul (c : ℝ) (X : RealPauliOp) : RealPauliOp :=
  ⟨c * X.t, c * X.x, c * X.y, c * X.z⟩

/- #### BUCKET 1: CLOSED FINITE THEOREMS -/
-- [Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]

/-- CLOSED THEOREM 1: The metric scales quadratically with scalar multiplication. -/
lemma det_smul (c : ℝ) (X : RealPauliOp) :
  det (smul c X) = c^2 * det X := by
  unfold det smul
  dsimp
  ring

/-- CLOSED THEOREM 2: The trace scales linearly with scalar multiplication. -/
lemma trace_smul (c : ℝ) (X : RealPauliOp) :
  trace (smul c X) = c * trace X := by
  unfold trace smul
  dsimp
  ring

/-- CLOSED THEOREM 3: Trace is affine on convex combinations. -/
lemma trace_affine_combo (A B : RealPauliOp) (p : ℝ) :
    trace ⟨p * A.t + (1 - p) * B.t,
           p * A.x + (1 - p) * B.x,
           p * A.y + (1 - p) * B.y,
           p * A.z + (1 - p) * B.z⟩
      = p * trace A + (1 - p) * trace B := by
  unfold trace
  ring


/- #### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES -/
-- [Theorems that compile conditionally based on explicitly named, valid premises or external verified witnesses. No hidden assumptions.]

/-- Mapping operators into the bounded affine space (Poincaré/Bloch geometry). -/
def to_density (X : RealPauliOp) (c : ℝ) : RealPauliOp := smul c X

/-- Explicit witness guaranteeing projection to Trace = 1. -/
class NormalizedTrace (X : RealPauliOp) (c : ℝ) where
  is_normalized : c * trace X = 1

/-- CONDITIONAL THEOREM 1: Density matrix trace maps strictly to the observer's conformal boundary. -/
theorem density_trace_one (X : RealPauliOp) (c : ℝ) [nt : NormalizedTrace X c] :
  trace (to_density X c) = 1 := by
  unfold to_density
  rw [trace_smul]
  exact nt.is_normalized

/-- Purity metric mapping the determinant of the normalized state. -/
def purity (X : RealPauliOp) (c : ℝ) : ℝ := det (to_density X c)

/-- CONDITIONAL THEOREM 2: Operators with det=0 map perfectly to pure states (purity=0) on the Celestial Sphere. -/
theorem pure_state_lightcone (X : RealPauliOp) (c : ℝ) (h_det : det X = 0) :
  purity X c = 0 := by
  unfold purity to_density
  rw [det_smul]
  rw [h_det]
  ring


/- #### BUCKET 3: OPEN CLOSURE DEBT -/
-- [Identified gaps, missing structural steps, or unverified steps. This defines the exact remaining debt line. No overclaims permitted.]

/-- Transport `RealPauliOp` to the split-quaternion algebra used elsewhere in the repo. -/
def toSplitQuaternion (X : RealPauliOp) : SplitQuaternion :=
  ⟨X.t, X.y, X.x, X.z⟩

/-- Transport split quaternions back to `RealPauliOp`. -/
def fromSplitQuaternion (q : SplitQuaternion) : RealPauliOp :=
  ⟨q.w, q.y, q.x, q.z⟩

/-- Non-commutative multiplication via the split-quaternion model. -/
def RealPauliOp_mul (A B : RealPauliOp) : RealPauliOp :=
  fromSplitQuaternion (toSplitQuaternion A * toSplitQuaternion B)

lemma det_eq_norm (X : RealPauliOp) : det X = InfoGeometry.Clifford.norm (toSplitQuaternion X) := by
  change X.t ^ 2 - X.x ^ 2 + X.y ^ 2 - X.z ^ 2 =
    InfoGeometry.Clifford.norm (⟨X.t, X.y, X.x, X.z⟩ : SplitQuaternion)
  simp [InfoGeometry.Clifford.norm]
  ring

/-- DEBT 2: Prove that if X^2 = 0 (Nilpotent Operator Flux), then det(X) = 0 (Locks precisely to the Celestial Sphere lightcone boundary). -/
theorem nilpotent_is_lightlike (X : RealPauliOp) :
  RealPauliOp_mul X X = ⟨0, 0, 0, 0⟩ → det X = 0 := by
  intro h
  have hsq : toSplitQuaternion X * toSplitQuaternion X = 0 := by
    apply SplitQuaternion.ext
    · simpa [RealPauliOp_mul, toSplitQuaternion, fromSplitQuaternion] using congrArg RealPauliOp.t h
    · simpa [RealPauliOp_mul, toSplitQuaternion, fromSplitQuaternion] using congrArg RealPauliOp.y h
    · simpa [RealPauliOp_mul, toSplitQuaternion, fromSplitQuaternion] using congrArg RealPauliOp.x h
    · simpa [RealPauliOp_mul, toSplitQuaternion, fromSplitQuaternion] using congrArg RealPauliOp.z h
  have hmul := InfoGeometry.Clifford.norm_mul (toSplitQuaternion X) (toSplitQuaternion X)
  rw [hsq] at hmul
  have hzero : InfoGeometry.Clifford.norm (0 : SplitQuaternion) = 0 := by
    change (0 : ℝ) * (0 : ℝ) + (0 : ℝ) * (0 : ℝ) - (0 : ℝ) * (0 : ℝ) - (0 : ℝ) * (0 : ℝ) = 0
    ring
  rw [hzero] at hmul
  have hsq2 : InfoGeometry.Clifford.norm (toSplitQuaternion X) * InfoGeometry.Clifford.norm (toSplitQuaternion X) = 0 := by
    simpa using hmul
  have hnorm : InfoGeometry.Clifford.norm (toSplitQuaternion X) = 0 := by
    nlinarith [hsq2]
  rw [det_eq_norm, hnorm]

/-- Determinant in the standard Minkowski signature (1,3): t^2 - x^2 - y^2 - z^2. -/
def detMinkowski (X : RealPauliOp) : ℝ := X.t^2 - X.x^2 - X.y^2 - X.z^2

/-- DEBT 3: Convex Affine Geometry Mapping (The Hessian Interior).
    Prove that the interior space of mixed states (trace=1 and detMinkowski > 0) is strictly convex. -/
theorem density_interior_convex (A B : RealPauliOp) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
  (hAt : trace A = 1) (hBt : trace B = 1) (hAd : detMinkowski A > 0) (hBd : detMinkowski B > 0) :
  detMinkowski (⟨p * A.t + (1 - p) * B.t, 
                 p * A.x + (1 - p) * B.x, 
                 p * A.y + (1 - p) * B.y, 
                 p * A.z + (1 - p) * B.z⟩) > 0 := by
  have hAt2 : A.t = 1/2 := by
    unfold trace at hAt
    linarith
  have hBt2 : B.t = 1/2 := by
    unfold trace at hBt
    linarith
  unfold detMinkowski at hAd hBd ⊢
  dsimp
  rw [hAt2] at hAd
  rw [hBt2] at hBd
  rw [hAt2, hBt2]
  have htime : p * (1 / 2) + (1 - p) * (1 / 2) = 1 / 2 := by ring
  rw [htime]
  have h_sq_conv (u v : ℝ) : (p * u + (1 - p) * v)^2 ≤ p * u^2 + (1 - p) * v^2 := by
    have hdiff : p * u^2 + (1 - p) * v^2 - (p * u + (1 - p) * v)^2 = p * (1 - p) * (u - v)^2 := by ring
    have hp_nonneg : 0 ≤ p * (1 - p) := by
      nlinarith
    have h_diff_nonneg : 0 ≤ p * (1 - p) * (u - v)^2 := by
      have h_sq : 0 ≤ (u - v)^2 := sq_nonneg (u - v)
      exact mul_nonneg hp_nonneg h_sq
    linarith
  have hx := h_sq_conv A.x B.x
  have hy := h_sq_conv A.y B.y
  have hz := h_sq_conv A.z B.z
  rcases eq_or_lt_of_le hp0 with hp_zero | hp_pos
  · subst hp_zero
    simp only [zero_mul, sub_zero, zero_add] at hx hy hz ⊢
    linarith
  · have h1p : 0 ≤ 1 - p := by linarith
    nlinarith [hx, hy, hz, hAd, hBd]

end RealPauliCausalCone

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
- `det_smul` : Proves quadratic scaling of determinant metric under scalar multiplication.
- `trace_smul` : Proves linear scaling of trace under scalar multiplication.
- `trace_affine_combo` : Trace is affine on convex combinations.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[Theorems that compile conditionally based on explicitly named, valid premises or external verified witnesses. No hidden assumptions.]
- `density_trace_one` : Shows trace normalization conditioned on `NormalizedTrace`.
- `pure_state_lightcone` : Shows purity is exactly zero on the lightcone.

#### BUCKET 3: OPEN CLOSURE DEBT
[Identified gaps, missing structural steps, or unverified steps. This defines the exact remaining debt line. No overclaims permitted.]
- `nilpotent_is_lightlike` : Nilpotent operator locks to the lightcone.
- `density_interior_convex` : Convexity of the state interior (Minkowski domain). Fully proved.
-/
