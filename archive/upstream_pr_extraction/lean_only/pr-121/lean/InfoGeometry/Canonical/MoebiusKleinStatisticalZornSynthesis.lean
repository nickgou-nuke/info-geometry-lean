import Mathlib
import InfoGeometry.Canonical.ThreePointMoebiusCrossRatioBridge
import InfoGeometry.Topology.MobiusCrossRatio
import InfoGeometry.Topology.ThermodynamicSL2MobiusFlow
import InfoGeometry.Topology.WallpaperKleinBottlePresentation
import InfoGeometry.Thermodynamics.UnruhTemperature
import InfoGeometry.Canonical.UnruhTemperatureAccelerationBridge
import InfoGeometry.Physics.MD011StatisticalInfoGeometry
import InfoGeometry.Algebra.Zorn.InverseAdjugate

noncomputable section

namespace InfoGeometry.Canonical.MoebiusKleinStatisticalZornSynthesis

open BigOperators
open Matrix
open InfoGeometry.Physics.MD011StatisticalInfoGeometry

/-! ## Projective `2 × 2` matrices -/

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Affine fractional-linear action of a raw complex `2 × 2` matrix. -/
def matrixMobiusAction (A : Mat2C) (z : ℂ) : ℂ :=
  (A 0 0 * z + A 0 1) / (A 1 0 * z + A 1 1)

/-- Entrywise scalar multiplication, exposed explicitly to avoid conflating it with composition. -/
def matrixScale (c : ℂ) (A : Mat2C) : Mat2C :=
  fun i j => c * A i j

/-- A nonzero projective rescaling does not change the Möbius action. -/
theorem matrixMobiusAction_matrixScale
    (c : ℂ) (hc : c ≠ 0) (A : Mat2C) (z : ℂ) :
    matrixMobiusAction (matrixScale c A) z = matrixMobiusAction A z := by
  unfold matrixMobiusAction matrixScale
  rw [show
    c * A 0 0 * z + c * A 0 1 = c * (A 0 0 * z + A 0 1) by ring]
  rw [show
    c * A 1 0 * z + c * A 1 1 = c * (A 1 0 * z + A 1 1) by ring]
  exact mul_div_mul_left _ _ hc

/-- For `2 × 2` matrices, scalar rescaling multiplies the determinant by `c²`. -/
theorem det_matrixScale (c : ℂ) (A : Mat2C) :
    Matrix.det (matrixScale c A) = c ^ 2 * Matrix.det A := by
  simp [Matrix.det_fin_two, matrixScale, pow_two]
  ring

/-- Explicit trace of a `2 × 2` matrix. -/
def trace2 (A : Mat2C) : ℂ :=
  A 0 0 + A 1 1

/-- The projectively meaningful trace-determinant ratio. -/
def projectiveTraceInvariant (A : Mat2C) : ℂ :=
  trace2 A ^ 2 / Matrix.det A

/-- Scalar multiplication scales the trace linearly. -/
theorem trace2_matrixScale (c : ℂ) (A : Mat2C) :
    trace2 (matrixScale c A) = c * trace2 A := by
  unfold trace2 matrixScale
  ring

/-- The trace-determinant ratio is invariant under nonzero projective rescaling. -/
theorem projectiveTraceInvariant_matrixScale
    (c : ℂ) (hc : c ≠ 0) (A : Mat2C) :
    projectiveTraceInvariant (matrixScale c A) = projectiveTraceInvariant A := by
  unfold projectiveTraceInvariant
  rw [trace2_matrixScale, det_matrixScale]
  rw [show (c * trace2 A) ^ 2 = c ^ 2 * trace2 A ^ 2 by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hc)

/--
Riemann-sphere cross-ratio invariance and raw matrix projective rescaling hold
in the same theorem packet without identifying their respective carriers.
-/
theorem riemannSphere_crossRatio_and_matrixScale_packet
    (g : GL (Fin 2) ℂ)
    (z₁ z₂ z₃ z₄ : OnePoint ℂ)
    (c : ℂ) (hc : c ≠ 0) (A : Mat2C) (z : ℂ) :
    InfoGeometry.crossRatio (g • z₁) (g • z₂) (g • z₃) (g • z₄) =
        InfoGeometry.crossRatio z₁ z₂ z₃ z₄ ∧
      matrixMobiusAction (matrixScale c A) z = matrixMobiusAction A z := by
  exact ⟨InfoGeometry.crossRatio_smul g z₁ z₂ z₃ z₄,
    matrixMobiusAction_matrixScale c hc A z⟩

/-- Multiplication by `i` preserves the projective action. -/
theorem matrixMobiusAction_I_scale (A : Mat2C) (z : ℂ) :
    matrixMobiusAction (matrixScale Complex.I A) z = matrixMobiusAction A z := by
  exact matrixMobiusAction_matrixScale Complex.I Complex.I_ne_zero A z

/-- Multiplication by `i` reverses the ordinary complex determinant. -/
theorem det_I_scale (A : Mat2C) :
    Matrix.det (matrixScale Complex.I A) = -Matrix.det A := by
  rw [det_matrixScale]
  simp [pow_two]

/--
Consequently, the sign of an ordinary determinant cannot be a projective
invariant over `ℂ`: the same Möbius action has representatives with opposite
determinants.
-/
theorem determinant_sign_not_projective_invariant (A : Mat2C) (z : ℂ) :
    matrixMobiusAction (matrixScale Complex.I A) z = matrixMobiusAction A z ∧
      Matrix.det (matrixScale Complex.I A) = -Matrix.det A := by
  exact ⟨matrixMobiusAction_I_scale A z, det_I_scale A⟩

/-- Diagonal reciprocal matrix representing a dilation/rotation multiplier. -/
def diagonalMode (q : ℂ) : Mat2C :=
  !![q, 0; 0, q⁻¹]

/-- The reciprocal diagonal matrix has determinant one away from `q = 0`. -/
theorem diagonalMode_det
    (q : ℂ) (hq : q ≠ 0) :
    Matrix.det (diagonalMode q) = 1 := by
  simp [diagonalMode, Matrix.det_fin_two, hq]

/-- The corresponding projective action has multiplier `q²`. -/
theorem diagonalMode_action (q z : ℂ) :
    matrixMobiusAction (diagonalMode q) z = q ^ 2 * z := by
  simp [matrixMobiusAction, diagonalMode, div_eq_mul_inv, pow_two]
  ring

/-- A multiplier is elliptic when its modulus is one. -/
def IsEllipticMultiplier (ρ : ℂ) : Prop :=
  ‖ρ‖ = 1

/-- A multiplier is loxodromic when its modulus is not one. -/
def IsLoxodromicMultiplier (ρ : ℂ) : Prop :=
  ‖ρ‖ ≠ 1

/-- Every complex multiplier satisfies the exact elliptic/loxodromic modulus dichotomy. -/
theorem multiplier_elliptic_or_loxodromic (ρ : ℂ) :
    IsEllipticMultiplier ρ ∨ IsLoxodromicMultiplier ρ := by
  simpa [IsEllipticMultiplier, IsLoxodromicMultiplier] using
    (eq_or_ne ‖ρ‖ 1)

/--
The reciprocal diagonal representative has determinant one, acts by `q²`, and
its multiplier is classified by the modulus dichotomy.
-/
theorem diagonalMode_packet (q z : ℂ) (hq : q ≠ 0) :
    Matrix.det (diagonalMode q) = 1 ∧
      matrixMobiusAction (diagonalMode q) z = q ^ 2 * z ∧
      (IsEllipticMultiplier (q ^ 2) ∨ IsLoxodromicMultiplier (q ^ 2)) := by
  exact ⟨diagonalMode_det q hq, diagonalMode_action q z,
    multiplier_elliptic_or_loxodromic (q ^ 2)⟩

/-! ## Two sheets, involution, and the Klein relation -/

abbrev SheetPair (α : Type*) := α × α

/-- Exchange the two sheets. -/
def sheetSwap {α : Type*} : SheetPair α ≃ SheetPair α where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv := by
    intro p
    rcases p with ⟨x, y⟩
    rfl
  right_inv := by
    intro p
    rcases p with ⟨x, y⟩
    rfl

@[simp]
theorem sheetSwap_apply {α : Type*} (p : SheetPair α) :
    sheetSwap p = (p.2, p.1) := rfl

@[simp]
theorem sheetSwap_involutive {α : Type*} (p : SheetPair α) :
    sheetSwap (sheetSwap p) = p := by
  rcases p with ⟨x, y⟩
  rfl

/-- The fixed locus of sheet exchange is exactly the diagonal equilibrium locus. -/
theorem sheetSwap_fixed_iff {α : Type*} (p : SheetPair α) :
    sheetSwap p = p ↔ p.1 = p.2 := by
  rcases p with ⟨x, y⟩
  constructor
  · intro h
    exact congrArg Prod.snd h
  · intro h
    cases h
    rfl

/-- Symmetric/equilibrium projector on two real sheets. -/
def evenSheetProjector (p : SheetPair ℝ) : SheetPair ℝ :=
  ((p.1 + p.2) / 2, (p.1 + p.2) / 2)

/-- Antisymmetric/off-equilibrium projector on two real sheets. -/
def oddSheetProjector (p : SheetPair ℝ) : SheetPair ℝ :=
  ((p.1 - p.2) / 2, (p.2 - p.1) / 2)

/-- Every two-sheet state is the sum of its even and odd parts. -/
theorem even_add_odd_eq (p : SheetPair ℝ) :
    evenSheetProjector p + oddSheetProjector p = p := by
  rcases p with ⟨x, y⟩
  ext <;> simp [evenSheetProjector, oddSheetProjector] <;> ring

/-- The even projector is idempotent. -/
theorem evenSheetProjector_idempotent (p : SheetPair ℝ) :
    evenSheetProjector (evenSheetProjector p) = evenSheetProjector p := by
  rcases p with ⟨x, y⟩
  dsimp [evenSheetProjector]
  ext <;> ring

/-- The odd projector is idempotent. -/
theorem oddSheetProjector_idempotent (p : SheetPair ℝ) :
    oddSheetProjector (oddSheetProjector p) = oddSheetProjector p := by
  rcases p with ⟨x, y⟩
  dsimp [oddSheetProjector]
  ext <;> ring

/-- The even and odd projectors are mutually annihilating. -/
theorem evenSheetProjector_oddSheetProjector (p : SheetPair ℝ) :
    evenSheetProjector (oddSheetProjector p) = 0 := by
  rcases p with ⟨x, y⟩
  ext <;> dsimp [evenSheetProjector, oddSheetProjector] <;> ring

/-- The odd and even projectors are mutually annihilating. -/
theorem oddSheetProjector_evenSheetProjector (p : SheetPair ℝ) :
    oddSheetProjector (evenSheetProjector p) = 0 := by
  rcases p with ⟨x, y⟩
  ext <;> dsimp [evenSheetProjector, oddSheetProjector] <;> ring

/-- Sheet exchange acts by eigenvalue `+1` on the even sector. -/
theorem sheetSwap_even (p : SheetPair ℝ) :
    sheetSwap (evenSheetProjector p) = evenSheetProjector p := by
  rcases p with ⟨x, y⟩
  rfl

/-- Sheet exchange acts by eigenvalue `-1` on the odd sector. -/
theorem sheetSwap_odd (p : SheetPair ℝ) :
    sheetSwap (oddSheetProjector p) = -oddSheetProjector p := by
  rcases p with ⟨x, y⟩
  ext <;> simp [sheetSwap, oddSheetProjector] <;> ring

/-- Reciprocal right/left mode on a doubled carrier. -/
def sheetMode {K : Type*} [Field K] (q : K) (p : SheetPair K) : SheetPair K :=
  (q * p.1, q⁻¹ * p.2)

/-- Unit multiplier acts trivially. -/
@[simp]
theorem sheetMode_one {K : Type*} [Field K] (p : SheetPair K) :
    sheetMode (1 : K) p = p := by
  rcases p with ⟨x, y⟩
  simp [sheetMode]

/-- Multipliers compose multiplicatively. -/
theorem sheetMode_mul
    {K : Type*} [Field K]
    (q r : K) (p : SheetPair K) :
    sheetMode (q * r) p = sheetMode q (sheetMode r p) := by
  rcases p with ⟨x, y⟩
  ext <;> simp [sheetMode, mul_comm, mul_left_comm]

/--
Exact Klein presentation relation on the two-sheet carrier:
`swap · mode(q) · swap = mode(q⁻¹)`.
-/
theorem sheetSwap_conjugates_mode_to_inverse
    {K : Type*} [Field K]
    (q : K) (p : SheetPair K) :
    sheetSwap (sheetMode q (sheetSwap p)) = sheetMode q⁻¹ p := by
  rcases p with ⟨x, y⟩
  ext <;> simp [sheetSwap, sheetMode]

/--
The existing thermodynamic `sl₂` matrix flow and the doubled reciprocal mode
satisfy, simultaneously, determinant one and the Klein conjugation relation.
-/
theorem thermodynamicSL2_klein_packet
    (translation dilation specialConformal : ℝ)
    (t q : ℂ) (p : SheetPair ℂ) :
    Matrix.det
        (InfoGeometry.Topology.ThermodynamicSL2MobiusFlow.thermodynamicSL2MatrixFlow
          translation dilation specialConformal t) = 1 ∧
      sheetSwap (sheetMode q (sheetSwap p)) = sheetMode q⁻¹ p := by
  constructor
  · exact
      InfoGeometry.Topology.ThermodynamicSL2MobiusFlow.thermodynamicSL2MatrixFlow_det
        translation dilation specialConformal t
  · exact sheetSwap_conjugates_mode_to_inverse q p

/-- The Unruh temperature defines a diagonal fixed point of sheet exchange. -/
theorem unruh_temperature_sheet_equilibrium
    (obs : InfoGeometry.Thermodynamics.UnruhTemperature.RindlerObserver) :
    InfoGeometry.Thermodynamics.UnruhTemperature.unruhTemperature obs =
        obs.a / (2 * Real.pi) ∧
      sheetSwap
          (InfoGeometry.Thermodynamics.UnruhTemperature.unruhTemperature obs,
           InfoGeometry.Thermodynamics.UnruhTemperature.unruhTemperature obs) =
        (InfoGeometry.Thermodynamics.UnruhTemperature.unruhTemperature obs,
         InfoGeometry.Thermodynamics.UnruhTemperature.unruhTemperature obs) := by
  constructor
  · exact InfoGeometry.Thermodynamics.UnruhTemperature.unruhTemperature_eq obs
  · rfl

/-- The physical-constants Unruh law is nonnegative and sheet-symmetric. -/
theorem unruh_temperature_with_constants_sheet_nonneg
    (acc hbar c kB n : ℝ)
    (ha : 0 ≤ acc) (hh : 0 < hbar) (hc : 0 < c) (hk : 0 < kB) :
    0 ≤ InfoGeometry.Canonical.UnruhTemperatureAccelerationBridge.unruhTemperature
        acc hbar c kB ∧
      sheetSwap (n, n) = (n, n) := by
  constructor
  · exact
      InfoGeometry.Canonical.UnruhTemperatureAccelerationBridge.unruh_temperature_nonneg
        acc hbar c kB ha hh hc hk
  · rfl

/-! ## Statistical moment matrices -/

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev Tangent2 := Fin 2 → ℝ

/-- Over `ℝ`, a nonzero determinant has a genuine sign dichotomy. -/
theorem realDeterminant_sign_dichotomy
    (A : Mat2R) (hA : Matrix.det A ≠ 0) :
    Matrix.det A < 0 ∨ 0 < Matrix.det A := by
  exact lt_or_gt_of_ne hA

/-- Second-moment matrix of a scalar law with mean `μ` and variance `v`. -/
def momentMatrix (μ v : ℝ) : Mat2R :=
  !![1, μ; μ, μ ^ 2 + v]

/-- Its determinant is exactly the variance. -/
theorem momentMatrix_det (μ v : ℝ) :
    Matrix.det (momentMatrix μ v) = v := by
  simp [momentMatrix, Matrix.det_fin_two]
  ring

/-- The moment matrix is symmetric. -/
theorem momentMatrix_transpose (μ v : ℝ) :
    (momentMatrix μ v).transpose = momentMatrix μ v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [momentMatrix]

/-- Explicit quadratic form for a real `2 × 2` matrix. -/
def quadraticForm2 (A : Mat2R) (x : Tangent2) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, x i * A i j * x j

/--
Bridge to the existing finite Fisher/covariance owner: its Gram quadratic form
is exactly the variance of the corresponding linear statistic.
-/
theorem quadraticForm2_finiteFisherCov2Atom_eq_variance
    (w : Fin 2 → ℝ) (u : RVec2) (T : Fin 2 → Fin 2 → ℝ) :
    quadraticForm2 (finiteFisherCov2Atom w T) u =
      finiteVarianceReal w (linStat2Atom u T) := by
  simpa [quadraticForm2] using
    (finiteFisherCov2Atom_quadratic_eq_variance w u T)

/-- Nonnegative finite weights produce a positive-semidefinite Fisher Gram form. -/
theorem quadraticForm2_finiteFisherCov2Atom_nonneg
    (w : Fin 2 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (u : RVec2) (T : Fin 2 → Fin 2 → ℝ) :
    0 ≤ quadraticForm2 (finiteFisherCov2Atom w T) u := by
  simpa [quadraticForm2] using
    (finiteFisherCov2Atom_quadratic_nonneg w hw u T)

/-- Completion-of-the-square identity for the moment matrix. -/
theorem momentMatrix_quadraticForm
    (μ v : ℝ) (x : Tangent2) :
    quadraticForm2 (momentMatrix μ v) x =
      (x 0 + μ * x 1) ^ 2 + v * (x 1) ^ 2 := by
  simp [quadraticForm2, momentMatrix, Fin.sum_univ_two]
  ring

/-- Nonnegative variance gives a positive-semidefinite moment matrix. -/
theorem momentMatrix_quadraticForm_nonneg
    (μ v : ℝ) (hv : 0 ≤ v) (x : Tangent2) :
    0 ≤ quadraticForm2 (momentMatrix μ v) x := by
  rw [momentMatrix_quadraticForm]
  exact add_nonneg (sq_nonneg _) (mul_nonneg hv (sq_nonneg _))

/-- Strictly positive variance gives a positive-definite moment matrix. -/
theorem momentMatrix_quadraticForm_pos
    (μ v : ℝ) (hv : 0 < v) (x : Tangent2) (hx : x ≠ 0) :
    0 < quadraticForm2 (momentMatrix μ v) x := by
  rw [momentMatrix_quadraticForm]
  by_cases hx1 : x 1 = 0
  · have hx0 : x 0 ≠ 0 := by
      intro hx0
      apply hx
      funext i
      fin_cases i
      · simpa using hx0
      · simpa using hx1
    have hsq : 0 < (x 0) ^ 2 := sq_pos_of_ne_zero hx0
    simpa [hx1] using hsq
  · have hsq : 0 < (x 1) ^ 2 := sq_pos_of_ne_zero hx1
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hv hsq)

/-- Gaussian second-moment matrix. -/
def gaussianMomentMatrix (μ σ : ℝ) : Mat2R :=
  momentMatrix μ (σ ^ 2)

/-- Gaussian determinant equals the variance `σ²`. -/
theorem gaussianMomentMatrix_det (μ σ : ℝ) :
    Matrix.det (gaussianMomentMatrix μ σ) = σ ^ 2 := by
  simp [gaussianMomentMatrix, momentMatrix_det]

/-- Poisson second-moment matrix. -/
def poissonMomentMatrix (lam : ℝ) : Mat2R :=
  momentMatrix lam lam

/-- Poisson determinant equals its mean/variance parameter. -/
theorem poissonMomentMatrix_det (lam : ℝ) :
    Matrix.det (poissonMomentMatrix lam) = lam := by
  simp [poissonMomentMatrix, momentMatrix_det]

/-- Congruence transforms scale a `2 × 2` moment determinant by `det(A)²`. -/
theorem determinant_congruence
    (A H : Mat2R) :
    Matrix.det (A * H * A.transpose) =
      Matrix.det A ^ 2 * Matrix.det H := by
  calc
    Matrix.det (A * H * A.transpose) =
        Matrix.det (A * H) * Matrix.det A.transpose := by
          rw [Matrix.det_mul]
    _ = (Matrix.det A * Matrix.det H) * Matrix.det A := by
          rw [Matrix.det_mul, Matrix.det_transpose]
    _ = Matrix.det A ^ 2 * Matrix.det H := by ring

/-! ## Fisher, Wasserstein, and the independent skew form -/

/-- Fisher metric of the univariate Gaussian family in `(μ,σ)` coordinates. -/
def gaussianFisher (σ : ℝ) (u v : Tangent2) : ℝ :=
  (u 0 * v 0 + 2 * u 1 * v 1) / σ ^ 2

/-- Wasserstein metric of the univariate Gaussian family in `(μ,σ)` coordinates. -/
def gaussianWasserstein (u v : Tangent2) : ℝ :=
  u 0 * v 0 + u 1 * v 1

/-- Canonical skew form on the same two-coordinate carrier. -/
def canonicalSymplectic (u v : Tangent2) : ℝ :=
  u 0 * v 1 - u 1 * v 0

/-- The Fisher tensor is symmetric. -/
theorem gaussianFisher_symmetric (σ : ℝ) (u v : Tangent2) :
    gaussianFisher σ u v = gaussianFisher σ v u := by
  unfold gaussianFisher
  ring

/-- The Wasserstein tensor is symmetric. -/
theorem gaussianWasserstein_symmetric (u v : Tangent2) :
    gaussianWasserstein u v = gaussianWasserstein v u := by
  unfold gaussianWasserstein
  ring

/-- The symplectic tensor is antisymmetric. -/
theorem canonicalSymplectic_antisymmetric (u v : Tangent2) :
    canonicalSymplectic u v = -canonicalSymplectic v u := by
  unfold canonicalSymplectic
  ring

/-- A skew form vanishes on the diagonal. -/
@[simp]
theorem canonicalSymplectic_self (u : Tangent2) :
    canonicalSymplectic u u = 0 := by
  unfold canonicalSymplectic
  ring

/-- Symmetric part of an arbitrary real response kernel. -/
def responseSymPart {α : Type*} (H : α → α → ℝ) (x y : α) : ℝ :=
  (H x y + H y x) / 2

/-- Unnormalized alternating part of an arbitrary real response kernel. -/
def responseAltPart {α : Type*} (H : α → α → ℝ) (x y : α) : ℝ :=
  H x y - H y x

/-- The symmetric part is symmetric. -/
theorem responseSymPart_symmetric
    {α : Type*} (H : α → α → ℝ) (x y : α) :
    responseSymPart H x y = responseSymPart H y x := by
  unfold responseSymPart
  ring

/-- The alternating part changes sign under exchange. -/
theorem responseAltPart_antisymmetric
    {α : Type*} (H : α → α → ℝ) (x y : α) :
    responseAltPart H x y = -responseAltPart H y x := by
  unfold responseAltPart
  ring

/-- Exact reconstruction coefficient: `H = Sym(H) + 1/2 Alt(H)`. -/
theorem response_reconstruction
    {α : Type*} (H : α → α → ℝ) (x y : α) :
    H x y = responseSymPart H x y + (1 / 2 : ℝ) * responseAltPart H x y := by
  unfold responseSymPart responseAltPart
  ring

/-- Mean of two real connection-coefficient kernels. -/
def connectionMean {α : Type*}
    (e m : α → α → α → ℝ) (x y z : α) : ℝ :=
  (e x y z + m x y z) / 2

/-- Difference of the dual connection-coefficient kernels. -/
def connectionDifference {α : Type*}
    (e m : α → α → α → ℝ) (x y z : α) : ℝ :=
  m x y z - e x y z

/-- Recover the exponential connection from mean and difference. -/
theorem exponential_connection_reconstruction
    {α : Type*} (e m : α → α → α → ℝ) (x y z : α) :
    e x y z = connectionMean e m x y z -
      (1 / 2 : ℝ) * connectionDifference e m x y z := by
  unfold connectionMean connectionDifference
  ring

/-- Recover the mixture connection from mean and difference. -/
theorem mixture_connection_reconstruction
    {α : Type*} (e m : α → α → α → ℝ) (x y z : α) :
    m x y z = connectionMean e m x y z +
      (1 / 2 : ℝ) * connectionDifference e m x y z := by
  unfold connectionMean connectionDifference
  ring

/-! ## Complex versus para-complex doubling -/

abbrev DoubledTangent := Tangent2 × Tangent2

/-- Ordinary tangent-bundle complex structure. -/
def tangentComplexStructure (p : DoubledTangent) : DoubledTangent :=
  (-p.2, p.1)

/-- It squares to minus the identity. -/
theorem tangentComplexStructure_sq (p : DoubledTangent) :
    tangentComplexStructure (tangentComplexStructure p) = -p := by
  rcases p with ⟨u, v⟩
  rfl

/-- Sheet-grading para-complex structure. -/
def tangentParaStructure (p : DoubledTangent) : DoubledTangent :=
  (p.1, -p.2)

/-- It squares to the identity. -/
theorem tangentParaStructure_sq (p : DoubledTangent) :
    tangentParaStructure (tangentParaStructure p) = p := by
  rcases p with ⟨u, v⟩
  simp [tangentParaStructure]

/-! ## Exact Zorn/Moufang associator packet -/

namespace ZornAssociator

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

abbrev ZornInt := ZornCell ℤ

@[ext]
theorem ZornCell_ext {R : Type*} {a b : ZornCell R}
    (hr : a.r = b.r) (hs : a.s = b.s)
    (hx1 : a.x1 = b.x1) (hx2 : a.x2 = b.x2) (hx3 : a.x3 = b.x3)
    (hy1 : a.y1 = b.y1) (hy2 : a.y2 = b.y2) (hy3 : a.y3 = b.y3) :
    a = b := by
  cases a; cases b
  congr

/-- The first unipotent Zorn generator. -/
def S1 : ZornInt :=
  ⟨1, 1, 1, 0, 0, 0, 0, 0⟩

/-- The second unipotent Zorn generator. -/
def S2 : ZornInt :=
  ⟨1, 1, 0, 1, 0, 0, 0, 0⟩

/-- The third twisted generator. -/
def U3 : ZornInt :=
  ⟨0, 1, 0, 0, 1, 0, 0, -1⟩

/-- All three generators have Zorn determinant one. -/
theorem generators_det_one :
    detZ S1 = 1 ∧ detZ S2 = 1 ∧ detZ U3 = 1 := by
  constructor
  · norm_num [S1, detZ]
  constructor
  · norm_num [S2, detZ]
  · norm_num [U3, detZ]

/-- First intermediate product. -/
theorem S1_mul_S2 :
    S1 * S2 = ⟨1, 1, 1, 1, 0, 0, 0, 1⟩ := by
  change mulZ S1 S2 = _
  ext <;> norm_num [S1, S2, mulZ]

/-- Second intermediate product. -/
theorem S2_mul_U3 :
    S2 * U3 = ⟨0, 1, 0, 1, 1, 1, 0, -1⟩ := by
  change mulZ S2 U3 = _
  ext <;> norm_num [S2, U3, mulZ]

/-- Left-associated product. -/
theorem leftAssociated_value :
    (S1 * S2) * U3 = ⟨0, 2, 1, 1, 1, 1, -1, -1⟩ := by
  change mulZ (mulZ S1 S2) U3 = _
  ext <;> norm_num [S1, S2, U3, mulZ]

/-- Right-associated product. -/
theorem rightAssociated_value :
    S1 * (S2 * U3) = ⟨1, 1, 1, 1, 1, 1, -1, 0⟩ := by
  change mulZ S1 (mulZ S2 U3) = _
  ext <;> norm_num [S1, S2, U3, mulZ]

/-- The displayed generators are genuinely nonassociative. -/
theorem concrete_nonassociative :
    (S1 * S2) * U3 ≠ S1 * (S2 * U3) := by
  intro h
  have hr := congrArg ZornCell.r h
  rw [leftAssociated_value, rightAssociated_value] at hr
  norm_num at hr

/-- Additive coordinate subtraction on the existing Zorn carrier. -/
def subZ (X Y : ZornInt) : ZornInt :=
  ⟨X.r - Y.r, X.s - Y.s,
    X.x1 - Y.x1, X.x2 - Y.x2, X.x3 - Y.x3,
    X.y1 - Y.y1, X.y2 - Y.y2, X.y3 - Y.y3⟩

/-- Additive associator. -/
def additiveAssociator (X Y Z : ZornInt) : ZornInt :=
  subZ ((X * Y) * Z) (X * (Y * Z))

/-- Exact additive associator of `(S₁,S₂,U₃)`. -/
theorem additiveAssociator_value :
    additiveAssociator S1 S2 U3 = ⟨-1, 1, 0, 0, 0, 0, 0, -1⟩ := by
  unfold additiveAssociator
  rw [leftAssociated_value, rightAssociated_value]
  ext <;> norm_num [subZ]

/-- Multiplicative loop associator using the determinant-one adjugate inverse. -/
def loopAssociator (X Y Z : ZornInt) : ZornInt :=
  ((X * Y) * Z) * conjZ (X * (Y * Z))

/-- Exact multiplicative associator of `(S₁,S₂,U₃)`. -/
theorem loopAssociator_value :
    loopAssociator S1 S2 U3 = ⟨0, 3, 0, 0, 1, -1, 1, -1⟩ := by
  unfold loopAssociator
  rw [leftAssociated_value, rightAssociated_value]
  change
    mulZ
      (⟨0, 2, 1, 1, 1, 1, -1, -1⟩ : ZornInt)
      (conjZ (⟨1, 1, 1, 1, 1, 1, -1, 0⟩ : ZornInt)) = _
  ext <;> norm_num [conjZ, mulZ]

/-- The multiplicative associator remains on the determinant-one Zorn locus. -/
theorem loopAssociator_det_one :
    detZ (loopAssociator S1 S2 U3) = 1 := by
  rw [loopAssociator_value]
  norm_num [detZ]

/-- The multiplicative associator is nontrivial. -/
theorem loopAssociator_ne_one :
    loopAssociator S1 S2 U3 ≠ oneZ := by
  intro h
  have hs := congrArg ZornCell.s h
  rw [loopAssociator_value] at hs
  norm_num [oneZ] at hs

end ZornAssociator

/-! ## Consolidated theorem packet -/

/--
Finite theorem-safe core of the consolidation.  It deliberately states only
claims proved in the imported native owners or in this module; no quotient
manifold, orbifold, supermanifold, Kähler, or topological-classification claim is
silently postulated.
-/
theorem consolidated_finite_core
    (p : SheetPair ℝ)
    (μ v : ℝ)
    (hv : 0 ≤ v)
    (x : Tangent2) :
    sheetSwap (sheetSwap p) = p ∧
      Matrix.det (momentMatrix μ v) = v ∧
      0 ≤ quadraticForm2 (momentMatrix μ v) x ∧
      InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.detZ
        (ZornAssociator.loopAssociator
          ZornAssociator.S1 ZornAssociator.S2 ZornAssociator.U3) = 1 := by
  refine ⟨sheetSwap_involutive p, momentMatrix_det μ v, ?_, ?_⟩
  · exact momentMatrix_quadraticForm_nonneg μ v hv x
  · exact ZornAssociator.loopAssociator_det_one

end InfoGeometry.Canonical.MoebiusKleinStatisticalZornSynthesis

end noncomputable section
