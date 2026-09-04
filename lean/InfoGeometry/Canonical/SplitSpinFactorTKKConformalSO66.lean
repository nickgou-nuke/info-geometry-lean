import Mathlib
import InfoGeometry.Canonical.SplitSpinFactorHomothetySO55

noncomputable section

namespace InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66

open InfoGeometry.Algebra
open InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation
open InfoGeometry.Canonical.SplitSpinFactorHomothetySO55
open InfoGeometry.Canonical.SplitOctonionTKKFiniteDimensionalBridges

abbrev V10 := SplitSpacetime10
abbrev Zorn := InfoGeometry.Algebra.ZornVectorMatrix ℝ

/-- Polarized bilinear form of the split determinant on the native
`H2(O_s)` Peirce-zero carrier. -/
def B10 (u v : V10) : ℝ :=
  (1 / 2 : ℝ) *
    (u.1.1 * v.1.2 + u.1.2 * v.1.1 - zornPolar u.2 v.2)

@[simp] theorem B10_symm (u v : V10) : B10 u v = B10 v u := by
  simp only [B10, zornPolar_symm]
  ring

@[simp] theorem B10_self (u : V10) : B10 u u = splitInterval10 u := by
  simp [B10, splitInterval10, h2SplitDet, zornPolar_self]
  ring

@[simp] theorem B10_smul_left (a : ℝ) (u v : V10) :
    B10 (a • u) v = a * B10 u v := by
  rcases u with ⟨⟨u2, u3⟩, ux⟩
  rcases v with ⟨⟨v2, v3⟩, vx⟩
  simp [B10, zornPolar, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
    ZornVectorMatrix.conj, ZornVectorMatrix.smul, ZornVec3.dot,
    Fin.sum_univ_three]
  ring

@[simp] theorem B10_smul_right (a : ℝ) (u v : V10) :
    B10 u (a • v) = a * B10 u v := by
  rw [B10_symm, B10_smul_left, B10_symm v u]

@[simp] theorem B10_zero_left (v : V10) : B10 0 v = 0 := by
  simpa using B10_smul_left 0 (0 : V10) v

@[simp] theorem B10_zero_right (u : V10) : B10 u 0 = 0 := by
  rw [B10_symm, B10_zero_left]

/-- Twelve-dimensional conformal carrier `R ⊕ V10 ⊕ R`.
The two scalar rails form one additional hyperbolic plane. -/
abbrev V12 := ℝ × (V10 × ℝ)

/-- Neutral conformal bilinear form extending the native `(5,5)` form. -/
def B66 (x y : V12) : ℝ :=
  x.1 * y.2.2 + x.2.2 * y.1 + B10 x.2.1 y.2.1

@[simp] theorem B66_symm (x y : V12) : B66 x y = B66 y x := by
  simp only [B66, B10_symm]
  ring

/-- Infinitesimal orthogonal condition on the 12-dimensional conformal
carrier.  This is the coordinate-free defining equation for `so(6,6)`. -/
def InSO66 (T : V12 → V12) : Prop :=
  ∀ x y, B66 (T x) y + B66 x (T y) = 0

/-- Grade `-1`: translation generator attached to `u : V10`. -/
def pGen (u : V10) (x : V12) : V12 :=
  (-B10 u x.2.1, (x.2.2 • u, 0))

/-- Grade `+1`: special-conformal generator attached to `v : V10`. -/
def kGen (v : V10) (x : V12) : V12 :=
  (0, (x.1 • v, -B10 v x.2.1))

/-- Zero-grade split dilatation. -/
def dGen (a : ℝ) (x : V12) : V12 :=
  (a * x.1, (0, -a * x.2.2))

/-- Zero-grade lift of a metric-skew endomorphism of the ten-dimensional
split spin factor. -/
def rotGen (M : V10 → V10) (x : V12) : V12 :=
  (0, (M x.2.1, 0))

/-- Every translation generator is infinitesimally `(6,6)`-orthogonal. -/
theorem pGen_in_so66 (u : V10) : InSO66 (pGen u) := by
  intro x y
  simp [InSO66, B66, pGen, B10_smul_left, B10_smul_right, B10_symm]
  ring

/-- Every special-conformal generator is infinitesimally `(6,6)`-orthogonal. -/
theorem kGen_in_so66 (v : V10) : InSO66 (kGen v) := by
  intro x y
  simp [InSO66, B66, kGen, B10_smul_left, B10_smul_right, B10_symm]
  ring

/-- Dilatations are infinitesimally `(6,6)`-orthogonal. -/
theorem dGen_in_so66 (a : ℝ) : InSO66 (dGen a) := by
  intro x y
  simp [InSO66, B66, dGen]
  ring

/-- A native `(5,5)` metric-skew operator lifts to an infinitesimal
`(6,6)`-orthogonal operator. -/
theorem rotGen_in_so66 (M : V10 → V10)
    (hM : ∀ u v, B10 (M u) v + B10 u (M v) = 0) :
    InSO66 (rotGen M) := by
  intro x y
  simp [InSO66, B66, rotGen]
  exact hM x.2.1 y.2.1

/-- Pointwise commutator of endomorphism-valued generators. -/
def bracket (A B : V12 → V12) (x : V12) : V12 :=
  A (B x) - B (A x)

/-- The negative grade is abelian. -/
theorem bracket_p_p (u v : V10) (x : V12) :
    bracket (pGen u) (pGen v) x = 0 := by
  simp [bracket, pGen, B10_smul_right, B10_symm]

/-- The positive grade is abelian. -/
theorem bracket_k_k (u v : V10) (x : V12) :
    bracket (kGen u) (kGen v) x = 0 := by
  simp [bracket, kGen, B10_smul_right, B10_symm]

/-- Dilatation grades translations with weight `+1` in these conventions. -/
theorem bracket_d_p (a : ℝ) (u : V10) (x : V12) :
    bracket (dGen a) (pGen u) x = pGen (a • u) x := by
  simp [bracket, dGen, pGen, B10_smul_left]
  module

/-- Dilatation grades special-conformal transformations with weight `-1`. -/
theorem bracket_d_k (a : ℝ) (v : V10) (x : V12) :
    bracket (dGen a) (kGen v) x = -kGen (a • v) x := by
  simp [bracket, dGen, kGen, B10_smul_left]
  module

/-- Metric bivector in the ten-dimensional spin factor. -/
def metricBivector (u v z : V10) : V10 :=
  B10 u z • v - B10 v z • u

/-- The cross bracket lands in the zero grade: a dilatation plus the
metric bivector rotation. -/
theorem bracket_p_k (u v : V10) (x : V12) :
    bracket (pGen u) (kGen v) x =
      dGen (-B10 u v) x + rotGen (metricBivector u v) x := by
  simp [bracket, pGen, kGen, dGen, rotGen, metricBivector,
    B10_smul_left, B10_smul_right, B10_symm]
  module

/-- The metric bivector is infinitesimally skew for `B10`. -/
theorem metricBivector_skew (u v : V10) :
    ∀ x y,
      B10 (metricBivector u v x) y +
        B10 x (metricBivector u v y) = 0 := by
  intro x y
  simp [metricBivector, B10_smul_left, B10_smul_right, B10_symm]
  ring

/-- Hence the zero-grade bivector term in `[P(u),K(v)]` is a genuine
infinitesimal `(6,6)` isometry. -/
theorem metricBivector_rot_in_so66 (u v : V10) :
    InSO66 (rotGen (metricBivector u v)) :=
  rotGen_in_so66 _ (metricBivector_skew u v)

/-- Native ten-dimensional Peirce-zero carrier has finrank ten. -/
theorem V10_finrank : Module.finrank ℝ V10 = 10 := by
  exact peirce_coordinate_finranks.2.2

/-- Structure/reduced conformal zero grade `so(5,5) ⊕ R D`. -/
abbrev Structure55 := So55 × ℝ

theorem structure55_finrank : Module.finrank ℝ Structure55 = 46 := by
  rw [Module.finrank_prod, native_so55_finrank, Module.finrank_self]
  norm_num

/-- The theorem-safe TKK carrier corresponding to the decomposition
`g_{-1} ⊕ g_0 ⊕ g_{+1}`. -/
abbrev ConformalTKKCarrier := V10 × (Structure55 × V10)

/-- Exact `10 + 46 + 10 = 66` dimension certificate. -/
theorem conformalTKKCarrier_finrank :
    Module.finrank ℝ ConformalTKKCarrier = 66 := by
  rw [Module.finrank_prod, Module.finrank_prod, V10_finrank,
    structure55_finrank, V10_finrank]
  norm_num

/-- Mathlib's split type-D6 orthogonal Lie algebra is the canonical target
for a future bijective TKK realization.  This file deliberately does not
claim the equivalence before the generator map is proved bijective. -/
abbrev SplitConformalTypeD6 := LieAlgebra.Orthogonal.typeD (Fin 6) ℝ

/-- Numerical orthogonal dimension in twelve variables. -/
theorem orthogonal_dimension_12_eq_66 : 12 * (12 - 1) / 2 = 66 := by
  norm_num

/-- The TKK carrier dimension agrees with the expected dimension of
`so(6,6)`.  Equality of dimensions is recorded separately from the missing
Lie-equivalence theorem. -/
theorem conformalTKK_dimension_matches_so66 :
    Module.finrank ℝ ConformalTKKCarrier = 12 * (12 - 1) / 2 := by
  rw [conformalTKKCarrier_finrank]
  norm_num

end InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66
