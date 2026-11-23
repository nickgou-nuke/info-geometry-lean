/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.RindlerSpinTorsion
import InfoGeometry.Canonical.SpinorBundleKosmannDerivative
import InfoGeometry.Canonical.SouriauKillingLipschitzBridge
import InfoGeometry.Canonical.RealChiralCARTranslationSynthesis
import InfoGeometry.Clifford.LipschitzWittRieszPrimary
import InfoGeometry.Clifford.Cl11Matrix
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# A curved real Lorentzian Cartan frame and its `Cl(1,1)` spin lift

This owner gives an explicit two-dimensional Lorentzian model with lapse
`N(x) = 1 + x^2`.  The time-translation flow is an isometry, the orthonormal
frame connection is Lorentz-skew and torsion-free, and its curvature is
nonzero.  Its spin connection is computed in the existing real `Cl(1,1)`
matrix representation and its curvature acts on Clifford vectors as the
vector curvature.  The Mathlib real spinor-bundle connection is also evaluated
on both coordinate fields: its curvature commutator on constant sections is
proved and its curvature coefficient is transported through the existing
real graded-CAR representation.

This is an explicit local-frame model, not a global spin-structure theorem or
a claim about Kerr, KMS analyticity, or horizon commutants.
-/

noncomputable section

namespace InfoGeometry.Geometry.CurvedLorentzianKosmannFrame

open InfoGeometry.Geometry.RindlerCartanFrame
open InfoGeometry.Geometry.RindlerSpinTorsion
open InfoGeometry.Clifford.Cl11Matrix

abbrev Tangent := ℝ × ℝ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Vec := Fin 2 → ℝ

def e01 : Mat2 := Matrix.single 0 1 1
def e10 : Mat2 := Matrix.single 1 0 1

/-- Opposite matrix units witness noncommutativity in this exact `Fin 2`
operator carrier. -/
theorem mat2_noncommutative_witness : e01 * e10 ≠ e10 * e01 := by
  intro h
  simp only [e01, e10] at h
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h
  have h00 := congrArg (fun M : Mat2 => M 0 0) h
  norm_num [Matrix.single] at h00

/-- The strictly positive lapse of the curved static Lorentzian chart. -/
def lapse (x : ℝ) : ℝ := x ^ 2 + 1

theorem lapse_pos (x : ℝ) : 0 < lapse x := by
  dsimp [lapse]
  positivity

/-- Orthonormal coframe components: `θ⁰=N(x) dt`, `θ¹=dx`. -/
def coframe (x : ℝ) (v : Tangent) : Vec := ![lapse x * v.1, v.2]

/-- The Lorentz metric written in the coordinate frame, obtained from the
orthonormal coframe and signature `(-,+)`. -/
def metric (x : ℝ) (v w : Tangent) : ℝ :=
  -(lapse x * v.1) * (lapse x * w.1) + v.2 * w.2

/-- The Lorentz pairing on orthonormal-frame components. -/
def lorentzPair (u w : Vec) : ℝ := -(u 0) * (w 0) + (u 1) * (w 1)

theorem metric_eq_orthonormal_coframe (x : ℝ) (v w : Tangent) :
    metric x v w = -(coframe x v 0) * (coframe x w 0) +
      (coframe x v 1) * (coframe x w 1) := by
  simp [metric, coframe]

/-- At the origin the metric agrees with the standard real Minkowski pairing
on the coordinate tangent plane. -/
theorem metric_at_origin (v w : Tangent) :
    metric 0 v w = -v.1 * w.1 + v.2 * w.2 := by
  simp [metric, lapse]

/-- The squared Lorentz norm of the coordinate time-translation Killing
field is the negative square of the chart lapse. -/
theorem timeTranslation_metric_norm_sq (x : ℝ) :
    metric x (1, 0) (1, 0) = -(lapse x) ^ 2 := by
  simp [metric, pow_two]

/-- In the static curved chart, a positive Souriau normalization `β₀` of
the time-translation Killing field has inverse-temperature norm
`β₀ N(x)`. This is the local Tolman redshift identity derived from the
metric, rather than a supplied temperature-field compatibility assumption. -/
theorem timeTranslation_inverseTemperature_norm
    (β₀ x : ℝ) (hβ₀ : 0 < β₀) :
    Real.sqrt (-metric x (β₀, 0) (β₀, 0)) = β₀ * lapse x := by
  have hmetric : metric x (β₀, 0) (β₀, 0) = -((β₀ * lapse x) ^ 2) := by
    simp [metric]
    ring
  rw [hmetric]
  simp [Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hβ₀ (lapse_pos x))]

/-- Nondegeneracy of the Lorentz metric: its only vector orthogonal to every
coordinate tangent vector is zero. -/
theorem metric_nondegenerate (x : ℝ) (v : Tangent)
    (hv : ∀ w, metric x v w = 0) : v = (0, 0) := by
  have ht := hv (1, 0)
  have hs := hv (0, 1)
  have hN : lapse x ≠ 0 := ne_of_gt (lapse_pos x)
  have hv₁ : v.1 = 0 := by
    have h := ht
    simp [metric] at h
    rcases h with (hN0 | hv0) | hN0
    · exact (hN hN0).elim
    · exact hv0
    · exact (hN hN0).elim
  have hv₂ : v.2 = 0 := by
    simpa [metric] using hs
  exact Prod.ext hv₁ hv₂

/-- Time translation on the chart. -/
def timeFlow (s : ℝ) (p : Tangent) : Tangent := (p.1 + s, p.2)

/-- The flow preserves the Lorentz metric, since the metric coefficients
depend only on the spatial coordinate. -/
theorem timeFlow_isometry (s : ℝ) (p : Tangent) (v w : Tangent) :
    metric (timeFlow s p).2 v w = metric p.2 v w := by
  rfl

/-- Frame derivative of the lapse. -/
theorem hasDerivAt_lapse (x : ℝ) : HasDerivAt lapse (2 * x) x := by
  change HasDerivAt (fun y : ℝ => y ^ 2 + 1) (2 * x) x
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
  convert ((hasDerivAt_id x).pow 2).add hconst using 1
  · funext y
    simp
  · simp

theorem deriv_lapse (x : ℝ) : deriv lapse x = 2 * x :=
  (hasDerivAt_lapse x).deriv

/-- The exterior derivative of the time coframe, represented as an alternating
bilinear form on the coordinate tangent space. -/
def dTimeCoframe (x : ℝ) : LinearMap.BilinForm ℝ Tangent :=
  -(deriv lapse x) • area

/-- The connection contribution `ω⁰₁ ∧ θ¹` in Cartan's first structure
equation. -/
def timeConnectionTerm (x : ℝ) : LinearMap.BilinForm ℝ Tangent :=
  (deriv lapse x) • area

/-- The first Cartan structure equation is torsion-free for this coframe and
connection. -/
theorem timeCoframe_torsion_zero (x : ℝ) :
    dTimeCoframe x + timeConnectionTerm x = 0 := by
  rw [dTimeCoframe, timeConnectionTerm]
  module

/-- The Lorentz-valued Cartan connection in the orthonormal frame. -/
def vectorConnection (x : ℝ) (v : Tangent) : Mat2 :=
  (deriv lapse x * v.1) • J1

theorem vectorConnection_at_origin (v : Tangent) : vectorConnection 0 v = 0 := by
  simp [vectorConnection, deriv_lapse]

/-- The frame connection is compatible with the Lorentz metric. -/
theorem vectorConnection_lorentz_skew (x : ℝ) (v : Tangent) :
    (vectorConnection x v).transpose * metricMatrix +
      metricMatrix * vectorConnection x v = 0 := by
  simpa [vectorConnection, connectionForm, deriv_lapse] using
    connection_lorentz_skew (2 * x * v.1) (1, 0)

/-- The local curved-frame connection is the existing finite Kosmann owner's
Rindler connection with its acceleration parameter set to the local lapse
derivative `N'(x) = 2x`. This is an equality of connection matrices on the
same real tangent and `Cl(1,1)` carriers. -/
theorem vectorConnection_eq_finiteRindlerConnection (x : ℝ) (v : Tangent) :
    vectorConnection x v =
      (InfoGeometry.Canonical.SouriauKillingLipschitzBridge.rindlerFiniteKosmannDatum
        (2 * x)).vectorConnection v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vectorConnection,
      InfoGeometry.Canonical.SouriauKillingLipschitzBridge.rindlerFiniteKosmannDatum,
      lorentzConnection, deriv_lapse, J1]

/-- The spin connection is the trace-free real Kosmann lift of the frame
connection; its coefficient is `-N'(x)/2`. -/
def spinConnection (x : ℝ) (v : Tangent) : Mat2 :=
  spinLift (deriv lapse x) 0 0 (0 : Tangent →ₗ[ℝ] ℝ) v

theorem spinConnection_eq_lapseDerivative (x : ℝ) (v : Tangent) :
    spinConnection x v = (-((deriv lapse x * v.1) / 2)) • J1 := by
  simp [spinConnection, spinLift]

/-- Away from the flat origin, the curved time-spin connection acts
noncommutatively with the existing negative Clifford generator. The proof
uses the matrix witness owned by the real `Cl(1,1)` representation. -/
theorem spinConnection_time_noncommutes_Eminus {x : ℝ} (hx : x ≠ 0) :
    spinConnection x (1, 0) * Eminus ≠ Eminus * spinConnection x (1, 0) := by
  intro h
  have hconn : spinConnection x (1, 0) = (-x) • J1 := by
    rw [spinConnection_eq_lapseDerivative, deriv_lapse]
    simp
  have h' : (-x) • (J1 * Eminus) = (-x) • (Eminus * J1) := by
    simpa only [hconn, Matrix.smul_mul, Matrix.mul_smul] using h
  have hs : (-x) ≠ 0 := neg_ne_zero.mpr hx
  have hcomm : J1 * Eminus = Eminus * J1 := by
    ext i j
    have hij := congrArg (fun A : Mat2 => A i j) h'
    exact mul_left_cancel₀ hs (by simpa [Matrix.smul_apply] using hij)
  exact J1_mul_Eminus_ne hcomm

/-- The spin lift computed in the curved bundle owner agrees with the
connection-derived spin lift in the finite Souriau/Kosmann owner. -/
theorem spinConnection_eq_finiteKosmannSpinConnection (x : ℝ) (v : Tangent) :
    spinConnection x v =
      (InfoGeometry.Canonical.SouriauKillingLipschitzBridge.rindlerFiniteKosmannDatum
        (2 * x)).spinConnection v := by
  rw [spinConnection_eq_lapseDerivative]
  simp [InfoGeometry.Canonical.SouriauKillingLipschitzBridge.FiniteKosmannDatum.spinConnection,
    InfoGeometry.Canonical.SouriauKillingLipschitzBridge.rindlerFiniteKosmannDatum,
    InfoGeometry.Canonical.SouriauKillingLipschitzBridge.kosmannSpinLiftOfLorentzConnection,
    lorentzConnection, deriv_lapse, J1]

/-- Transport the existing finite-owner Kosmann correction identity to the
connection induced by this curved frame. The datum parameter is the local
lapse derivative `2x`; both sides act on the finite owner's real matrix
spinor carrier. -/
theorem curvedFrame_kosmannCorrection_eq_finiteSpinAction
    (x : ℝ) (v : Tangent)
    (ψ : InfoGeometry.Canonical.SouriauKillingLipschitzBridge.Mat2) :
    InfoGeometry.Canonical.SouriauKillingLipschitzBridge.kosmannCorrection
        ((InfoGeometry.Canonical.SouriauKillingLipschitzBridge.rindlerFiniteKosmannDatum
          (2 * x)).contractedBivector v) ψ =
      spinConnection x v * ψ := by
  calc
    InfoGeometry.Canonical.SouriauKillingLipschitzBridge.kosmannCorrection
        ((InfoGeometry.Canonical.SouriauKillingLipschitzBridge.rindlerFiniteKosmannDatum
          (2 * x)).contractedBivector v) ψ =
      (InfoGeometry.Canonical.SouriauKillingLipschitzBridge.rindlerFiniteKosmannDatum
        (2 * x)).covariantDerivative v ψ :=
      InfoGeometry.Canonical.SouriauKillingLipschitzBridge.rindlerFiniteKosmannDatum_correction_eq_covariantDerivative
        (2 * x) v ψ
    _ = spinConnection x v * ψ := by
      simp only [InfoGeometry.Canonical.SouriauKillingLipschitzBridge.FiniteKosmannDatum.covariantDerivative]
      rw [← spinConnection_eq_finiteKosmannSpinConnection]

/-- The real matrix `Cl(1,1)` generator agrees with the existing Clifford
algebra bivector under the repository's fixed representation equivalence. -/
theorem cl11EquivMat_symm_J1 :
    InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm J1 =
      InfoGeometry.Clifford.Cl11Matrix.J1_cl := by
  apply InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.injective
  have hJmap : InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat
      InfoGeometry.Clifford.Cl11Matrix.J1_cl = J1 := by
    rw [show InfoGeometry.Clifford.Cl11Matrix.J1_cl =
        CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0) *
          CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (0, 1) from rfl,
      map_mul,
      InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat_iota_pos,
      InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat_iota_neg,
      InfoGeometry.Clifford.Cl11Matrix.Eplus_mul_Eminus]
  simpa using hJmap.symm

/-- Primitive split-Clifford idempotent defining the real two-component
spinor left ideal in the existing Riesz realization. -/
def spinorIdempotent : CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11 :=
  (1 / 2 : ℝ) • (1 + CliffordAlgebra.ι
    InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0))

theorem spinorIdempotent_matrix :
    InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat spinorIdempotent =
      !![(1 : ℝ), 0; 0, 0] := by
  dsimp [spinorIdempotent]
  rw [map_smul, map_add, map_one,
    InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat_iota_pos]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Eplus]

theorem spinorIdempotent_idempotent : IsIdempotentElem spinorIdempotent := by
  change spinorIdempotent * spinorIdempotent = spinorIdempotent
  apply InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.injective
  rw [map_mul, spinorIdempotent_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- A real spinor column, regarded as the first-column matrix in the existing
`Cl(1,1) ≃ M₂(ℝ)` representation and then as an element of the Riesz left
ideal generated by the primitive idempotent. -/
def spinorColumnElement (ψ : Vec) :
    InfoGeometry.Clifford.LipschitzWittRieszPrimary.RieszLeftIdeal
      (CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) spinorIdempotent := by
  let A : Mat2 := !![ψ 0, 0; ψ 1, 0]
  let a := InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm A
  refine ⟨a, ?_⟩
  apply (InfoGeometry.Clifford.LipschitzWittRieszPrimary.mem_rieszLeftIdeal_iff_mul_eq
    spinorIdempotent_idempotent a).2
  apply InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.injective
  rw [map_mul, AlgEquiv.apply_symm_apply]
  rw [spinorIdempotent_matrix]
  dsimp [a, A]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Distinct real spinor columns define distinct elements of the primitive
left ideal. -/
theorem spinorColumnElement_injective : Function.Injective spinorColumnElement := by
  intro ψ χ h
  have hm := congrArg InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat
    (congrArg Subtype.val h)
  dsimp [spinorColumnElement] at hm
  simp only [AlgEquiv.apply_symm_apply] at hm
  have h00 := congrArg (fun A : Mat2 => A 0 0) hm
  have h10 := congrArg (fun A : Mat2 => A 1 0) hm
  ext i
  fin_cases i
  · simpa using h00
  · simpa using h10

/-- Every element of the existing primitive left ideal is represented by a
unique real spinor column in the fixed `Cl(1,1) ≃ M₂(ℝ)` representation. -/
theorem spinorColumnElement_surjective : Function.Surjective spinorColumnElement := by
  intro z
  let M : Mat2 := InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat z.1
  have hzf := (InfoGeometry.Clifford.LipschitzWittRieszPrimary.mem_rieszLeftIdeal_iff_mul_eq
    spinorIdempotent_idempotent z.1).mp z.2
  have hMf : M * !![(1 : ℝ), 0; 0, 0] = M := by
    dsimp [M]
    rw [← spinorIdempotent_matrix, ← map_mul, hzf]
  have h01 : M 0 1 = 0 := by
    have h := congrArg (fun A : Mat2 => A 0 1) hMf
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    linarith
  have h11 : M 1 1 = 0 := by
    have h := congrArg (fun A : Mat2 => A 1 1) hMf
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    linarith
  refine ⟨![M 0 0, M 1 0], ?_⟩
  apply Subtype.ext
  apply InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.injective
  dsimp [spinorColumnElement]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, h01, h11]

/-- Every real `2 × 2` matrix acting on a spinor column is represented by left
multiplication in the existing `Cl(1,1)` Riesz ideal. This extends the
already-used Kosmann-generator action to the complete real matrix carrier. -/
theorem spinorColumnElement_matrix_left_action (A : Mat2) (ψ : Vec) :
    (spinorColumnElement (A.mulVec ψ) :
      CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) =
      InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm A *
        (spinorColumnElement ψ :
          CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) := by
  apply InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.injective
  rw [map_mul, AlgEquiv.apply_symm_apply]
  dsimp [spinorColumnElement]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

/-- The column realization is a linear equivalence from the real two-spinor
carrier onto the existing primitive Riesz ideal. This equips the already
proved bijection with its actual linear structure for transport through the
Hestenes tower. -/
noncomputable def spinorColumnLinearEquiv :
    Vec ≃ₗ[ℝ]
      InfoGeometry.Clifford.LipschitzWittRieszPrimary.RieszLeftIdeal
        (CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) spinorIdempotent :=
  LinearEquiv.ofBijective
    { toFun := spinorColumnElement
      map_add' := by
        intro ψ χ
        apply Subtype.ext
        apply InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.injective
        dsimp [spinorColumnElement]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.add_apply]
      map_smul' := by
        intro c ψ
        apply Subtype.ext
        apply InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.injective
        dsimp [spinorColumnElement]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.smul_apply] }
    ⟨spinorColumnElement_injective, spinorColumnElement_surjective⟩

@[simp] theorem spinorColumnLinearEquiv_apply (ψ : Vec) :
    spinorColumnLinearEquiv ψ = spinorColumnElement ψ := rfl

/-- Left multiplication by a curved Kosmann coefficient on the Riesz spinor
ideal is exactly the real matrix action on its two-component column. The
column realization is bijective by the preceding carrier theorems. -/
theorem cl11_spinConnection_leftIdeal_action (x : ℝ) (v : Tangent) (ψ : Vec) :
    (spinorColumnElement ((spinConnection x v).mulVec ψ) :
      CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) =
      InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm (spinConnection x v) *
        (spinorColumnElement ψ : CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) := by
  exact spinorColumnElement_matrix_left_action (spinConnection x v) ψ

/-- The curved chart's pointwise time-direction spin connection transports
through the existing real `Cl(1,1)`-to-Koszul-graded-CAR representation. Its
coefficient is `2x` times the established unit Rindler Majorana generator.
This identifies the local connection coefficient, not a CAR bundle
connection or its global holonomy. -/
theorem curvedTimeSpinConnection_eq_realCARGenerator (p : Vec) :
    InfoGeometry.Canonical.RealChiralCARTranslationSynthesis.rindlerPlaneCliffordToCAR
        (InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm
          (spinConnection (p 1) (1, 0))) =
      (2 * p 1) •
        InfoGeometry.Canonical.RealChiralCARTranslationSynthesis.rindlerMajoranaSpinGenerator := by
  rw [spinConnection_eq_lapseDerivative, deriv_lapse]
  simp only [map_smul]
  rw [cl11EquivMat_symm_J1,
    InfoGeometry.Canonical.RealChiralCARTranslationSynthesis.rindlerMajoranaSpinGenerator_eq_embeddedKosmannGenerator]
  simp [smul_smul]
  congr 1
  ring

theorem spinConnection_at_origin (v : Tangent) : spinConnection 0 v = 0 := by
  rw [spinConnection_eq_lapseDerivative, deriv_lapse]
  simp

/-- The derived spin connection implements the Lorentz connection by the
Clifford commutator on real vectors. -/
theorem spinConnection_adjoint (x : ℝ) (v : Tangent) (u : Vec) :
    spinConnection x v * cliffordVector u -
        cliffordVector u * spinConnection x v =
      cliffordVector ((vectorConnection x v).mulVec u) := by
  have hconn : vectorConnection x v = lorentzConnection (deriv lapse x) 0 0 v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [vectorConnection, lorentzConnection, J1]
  rw [spinConnection, hconn]
  exact spinLift_adjoint (deriv lapse x) 0 0 (0 : Tangent →ₗ[ℝ] ℝ) v u

/-- The time-translation Killing field in the orthonormal frame. -/
def timeKillingFieldFrame (x : ℝ) : Vec := ![lapse x, 0]

/-- Covariant derivative of the time-translation Killing field, expressed in
the orthonormal frame. The ordinary derivative term differentiates its frame
components in the spatial direction; the connection term is the previously
constructed Lorentz connection. -/
def covariantDerivativeTimeKilling (x : ℝ) (v : Tangent) : Vec :=
  ![deriv lapse x * v.2, 0] +
    (vectorConnection x v).mulVec (timeKillingFieldFrame x)

theorem covariantDerivativeTimeKilling_components (x : ℝ) (v : Tangent) :
    covariantDerivativeTimeKilling x v =
      ![deriv lapse x * v.2, lapse x * deriv lapse x * v.1] := by
  ext i
  fin_cases i
  all_goals
    simp [covariantDerivativeTimeKilling, vectorConnection,
      timeKillingFieldFrame, J1] <;> ring

/-- The covariant derivative of the time-translation field is skew with
respect to the curved Lorentz metric: this is the Killing equation in the
coordinate tangent frame, with tangent vectors converted by the coframe. -/
theorem timeKillingField_killing (x : ℝ) (v w : Tangent) :
    lorentzPair (covariantDerivativeTimeKilling x v) (coframe x w) +
      lorentzPair (coframe x v) (covariantDerivativeTimeKilling x w) = 0 := by
  rw [covariantDerivativeTimeKilling_components x v,
    covariantDerivativeTimeKilling_components x w]
  simp [deriv_lapse, lorentzPair, coframe, lapse]
  ring

/-- The Kosmann bivector coefficient extracted from the Killing derivative.
The two frame components are `∇ₓβ_t = N'` and `∇ₜβₓ = N'`; lowering the
time index gives the required skew pair. -/
def kosmannTimeGenerator (x : ℝ) : Mat2 :=
  (-(deriv lapse x / 2)) • J1

theorem kosmannTimeGenerator_eq_spinConnection (x : ℝ) :
    kosmannTimeGenerator x = spinConnection x (1, 0) := by
  simp [kosmannTimeGenerator, spinConnection, spinLift]

theorem kosmannTimeGenerator_eq_killing_derivative (x : ℝ) :
    kosmannTimeGenerator x =
      (-(covariantDerivativeTimeKilling x (0, 1) 0 / 2)) • J1 := by
  rw [covariantDerivativeTimeKilling_components]
  simp [kosmannTimeGenerator, deriv_lapse]

/-- Coordinate curvature of the vector frame connection in the oriented
`(t,x)` plane. -/
def vectorCurvature (x : ℝ) : Mat2 :=
  -((deriv (fun y : ℝ => deriv lapse y) x)) • J1

/-- Coordinate curvature of the spin connection in the oriented `(t,x)`
plane. -/
def spinCurvature (x : ℝ) : Mat2 :=
  -((deriv (fun y : ℝ => -(deriv lapse y / 2)) x)) • J1

theorem vectorCurvature_eq (x : ℝ) : vectorCurvature x = (-2 : ℝ) • J1 := by
  have h : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    convert (hasDerivAt_id x).const_mul 2 using 1 <;> norm_num
  have hfun : (fun y : ℝ => deriv lapse y) = fun y => 2 * y := by
    funext y
    exact deriv_lapse y
  rw [vectorCurvature, hfun, h.deriv]


theorem spinCurvature_eq (x : ℝ) : spinCurvature x = (1 : ℝ) • J1 := by
  have h : HasDerivAt (fun y : ℝ => -y) (-1) x := by
    convert (hasDerivAt_id x).const_mul (-1) using 1 <;> norm_num
  have hfun : (fun y : ℝ => -(deriv lapse y / 2)) = fun y => -y := by
    funext y
    rw [deriv_lapse]
    ring
  rw [spinCurvature, hfun, h.deriv]
  norm_num

/-- The actual spin curvature coefficient of the curved frame maps to the
real graded-CAR curvature bivector under the existing `Cl(1,1)` embedding.
The factor `-2` is fixed by the repository's established normalization of the
Rindler Majorana generator. -/
theorem spinCurvature_eq_realCARBivector (x : ℝ) :
    InfoGeometry.Canonical.RealChiralCARTranslationSynthesis.rindlerPlaneCliffordToCAR
        (InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm (spinCurvature x)) =
      (-2 : ℝ) •
        InfoGeometry.Canonical.RealChiralCARTranslationSynthesis.rindlerMajoranaSpinGenerator := by
  rw [spinCurvature_eq, map_smul, one_smul, cl11EquivMat_symm_J1,
    InfoGeometry.Canonical.RealChiralCARTranslationSynthesis.rindlerPlaneCliffordToCAR_bivector,
    InfoGeometry.Canonical.RealChiralCARTranslationSynthesis.rindlerMajoranaSpinGenerator_eq_embeddedKosmannGenerator]
  simp [smul_smul]

/-- The curved frame has nonzero curvature at every spatial point. -/
theorem vectorCurvature_ne_zero (x : ℝ) : vectorCurvature x ≠ 0 := by
  rw [vectorCurvature_eq]
  intro h
  have h' := congrArg (fun A : Mat2 => A 0 1) h
  simp [J1] at h'

/-- The model agrees with the flat Minkowski metric and vanishing connection
at the origin, but has nonzero curvature there. -/
theorem curved_frame_matches_flat_jet_but_not_flat :
    (∀ v w, metric 0 v w = -v.1 * w.1 + v.2 * w.2) ∧
    (∀ v, vectorConnection 0 v = 0) ∧ vectorCurvature 0 ≠ 0 := by
  exact ⟨metric_at_origin, vectorConnection_at_origin,
    vectorCurvature_ne_zero 0⟩

/-- The curvature of the spin lift acts on Clifford vectors by the vector
curvature, with the established normalization of the real `Cl(1,1)` spin
representation. -/
theorem spinCurvature_adjoint (x : ℝ) (u : Vec) :
    spinCurvature x * cliffordVector u -
        cliffordVector u * spinCurvature x =
      cliffordVector ((vectorCurvature x).mulVec u) := by
  rw [spinCurvature_eq, vectorCurvature_eq]
  have hspin : (1 : ℝ) • J1 =
      spinLift (-2) 0 0 (0 : Tangent →ₗ[ℝ] ℝ) (1, 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spinLift, J1]
  have hvec : (-2 : ℝ) • J1 = lorentzConnection (-2) 0 0 (1, 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lorentzConnection, J1]
  rw [hspin, hvec]
  exact spinLift_adjoint (-2) 0 0 (0 : Tangent →ₗ[ℝ] ℝ) (1, 0) u

/-! ## The corresponding real spinor bundle connection on the curved chart

The preceding frame formulas now act on sections of the trivial real rank-two
spinor bundle over the actual two-coordinate manifold.  The bundle connection
is constructed with Mathlib's `CovariantDerivative.addOneForm`; its one-form
is the real `Cl(1,1)` spin lift already derived above. -/

open Bundle ContinuousLinearMap
open scoped Manifold ContDiff
open scoped _root_.Topology

abbrev Base := Vec
abbrev SpinorBundle := Bundle.Trivial Base Vec
abbrev BaseModel := modelWithCornersSelf ℝ Base

/-- Transfer the chart model's real norm to each tangent fiber of this
coordinate manifold.  This is the model-space norm used by the continuous
one-form in the Kosmann connection. -/
local instance tangentNormedAddCommGroup (p : Base) :
    NormedAddCommGroup (TangentSpace BaseModel p) :=
  Pi.normedAddCommGroup

local instance tangentNormedSpace (p : Base) :
    NormedSpace ℝ (TangentSpace BaseModel p) :=
  Pi.normedSpace

/-- The flat covariant derivative on the trivial real spinor bundle over the
two-coordinate chart. -/
def flatSpinorBundleConnection :
    CovariantDerivative BaseModel Vec (SpinorBundle) where
  toFun σ x := mvfderiv BaseModel σ x
  isCovariantDerivativeOnUniv :=
    { add := fun {σ σ' x} hσ hσ' _ => by
        let σ₁ : Base → Vec := σ
        let σ₂ : Base → Vec := σ'
        have h1 : MDifferentiableAt BaseModel 𝓘(ℝ, Vec) σ₁ x := by
          simpa [σ₁, Bundle.Trivial.fiberBundle_trivializationAt'] using
            (mdifferentiableAt_section (IB := BaseModel) (F := Vec)
              (E := SpinorBundle) σ).mp hσ
        have h2 : MDifferentiableAt BaseModel 𝓘(ℝ, Vec) σ₂ x := by
          simpa [σ₂, Bundle.Trivial.fiberBundle_trivializationAt'] using
            (mdifferentiableAt_section (IB := BaseModel) (F := Vec)
              (E := SpinorBundle) σ').mp hσ'
        exact mvfderiv_add h1 h2
      leibniz := fun {σ g x} hσ hg _ => by
        let σ₁ : Base → Vec := σ
        have h1 : MDifferentiableAt BaseModel 𝓘(ℝ, Vec) σ₁ x := by
          simpa [σ₁, Bundle.Trivial.fiberBundle_trivializationAt'] using
            (mdifferentiableAt_section (IB := BaseModel) (F := Vec)
              (E := SpinorBundle) σ).mp hσ
        exact mvfderiv_smul hg h1 }

/-- Real linear action of a `Cl(1,1)` frame matrix on real spinor columns. -/
def frameMatrixOnSpinors : Mat2 →L[ℝ] (Vec →L[ℝ] Vec) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A.mulVecLin.toContinuousLinearMap
      map_add' := fun A B => by
        ext ψ i
        simp
      map_smul' := fun c A => by
        ext ψ i
        change ((c • A).mulVec ψ) i = c • (A.mulVec ψ) i
        rw [Matrix.smul_mulVec]
        rfl }

@[simp] theorem frameMatrixOnSpinors_apply (A : Mat2) (ψ : Vec) :
    frameMatrixOnSpinors A ψ = A.mulVec ψ := rfl

/-- The real Clifford-vector action on the rank-two spinor column, as a
continuous-linear family of spinor endomorphisms. This is the existing
`cliffordVector` matrix followed by the established real matrix action. -/
def cliffordVectorAction : Vec →L[ℝ] (Vec →L[ℝ] Vec) :=
  frameMatrixOnSpinors.comp
    (LinearMap.toContinuousLinearMap
      { toFun := cliffordVector
        map_add' := by
          intro u w
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [cliffordVector, Eminus, Eplus, add_smul]
        map_smul' := by
          intro c u
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [cliffordVector, Eminus, Eplus, smul_eq_mul] })

@[simp] theorem cliffordVectorAction_apply (u ψ : Vec) :
    cliffordVectorAction u ψ = Matrix.mulVec (cliffordVector u) ψ := rfl

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000
/-- Differentiating the real Clifford action on two varying sections obeys
the bilinear product rule. The proof uses Mathlib's continuous-linear-map
derivative rule and the existing real Clifford frame action. -/
theorem fderiv_cliffordVectorAction_apply
    (u ψ : Base → Vec) (p : Base)
    (hu : DifferentiableAt ℝ u p) (hψ : DifferentiableAt ℝ ψ p)
    (v : Base) :
    fderiv ℝ (fun q => cliffordVectorAction (u q) (ψ q)) p v =
      cliffordVectorAction (fderiv ℝ u p v) (ψ p) +
        cliffordVectorAction (u p) (fderiv ℝ ψ p v) := by
  let A : Base → Vec →L[ℝ] Vec := fun q => cliffordVectorAction (u q)
  have hA : DifferentiableAt ℝ A p :=
    (differentiableAt_const cliffordVectorAction).clm_apply hu
  have hAderiv : fderiv ℝ A p = cliffordVectorAction.comp (fderiv ℝ u p) := by
    rw [fderiv_clm_apply (differentiableAt_const cliffordVectorAction) hu]
    simp [fderiv_const_apply]
  rw [show (fun q => cliffordVectorAction (u q) (ψ q)) = fun q => A q (ψ q) by
    funext q
    rfl, fderiv_clm_apply hA hψ]
  rw [hAderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

set_option synthInstance.maxHeartbeats 1000000 in
/-- The spin-connection one-form, as a continuous linear map from chart
directions to real spinor endomorphisms. Its coefficient is extracted from
the curved frame connection, not supplied as independent bundle data. -/
def spinConnectionOneForm (p : Base) : Vec →L[ℝ] (Vec →L[ℝ] Vec) :=
  (frameMatrixOnSpinors.comp
    (((-(deriv lapse (p 1) / 2)) • (ContinuousLinearMap.proj 0 :
      Vec →L[ℝ] ℝ)).smulRight J1))

set_option synthInstance.maxHeartbeats 1000000 in
/-- The endomorphism-valued one-form in the argument order expected by
Mathlib's `CovariantDerivative.addOneForm`. The sign is chosen so that the
corrected derivative `∇ - C` acts by adding the derived spin connection. -/
def spinConnectionEndomorphismOneForm (p : Base) :
    SpinorBundle p →L[ℝ]
      TangentSpace BaseModel p →L[ℝ] SpinorBundle p := by
  change Vec →L[ℝ] TangentSpace BaseModel p →L[ℝ] Vec
  exact ((ContinuousLinearMap.compL ℝ (TangentSpace BaseModel p) Vec Vec).flip
      (tangentSpaceCastModel BaseModel p).toContinuousLinearMap).comp
    (-(spinConnectionOneForm p).flip)

/-- Evaluation of the endomorphism-valued one-form is the negative of the
derived real spin-frame action. -/
theorem spinConnectionEndomorphismOneForm_apply (p : Base) (ψ : Vec)
    (v : TangentSpace BaseModel p) :
    spinConnectionEndomorphismOneForm p ψ v =
      -(spinConnectionOneForm p (tangentSpaceCastModel BaseModel p v) ψ) := by
  rfl

set_option synthInstance.maxHeartbeats 1000000 in
/-- Real spinor-bundle covariant derivative on the curved chart, constructed
from the flat derivative and the previously derived `Cl(1,1)` spin lift. -/
def curvedSpinorBundleConnection :
    CovariantDerivative BaseModel Vec SpinorBundle :=
  InfoGeometry.Canonical.SpinorBundleKosmannDerivative.connectionCorrectedCovariantDerivative
    BaseModel flatSpinorBundleConnection spinConnectionEndomorphismOneForm

/-- Evaluation of the bundle connection is the directional derivative plus
the actual real spin-frame action on the spinor section. -/
theorem curvedSpinorBundleConnection_apply
    (σ : Base → Vec) (p : Base) (v : TangentSpace BaseModel p) :
    curvedSpinorBundleConnection σ p v =
      mvfderiv BaseModel σ p v +
        Matrix.mulVec
          (spinConnection (p 1)
            ((tangentSpaceCastModel BaseModel p v) 0,
              (tangentSpaceCastModel BaseModel p v) 1)) (σ p) := by
  let X : ∀ x : Base, TangentSpace BaseModel x := fun x =>
    (tangentSpaceCastModel BaseModel x).symm
      ((tangentSpaceCastModel BaseModel p) v)
  have hXp : X p = v := by simp [X]
  rw [curvedSpinorBundleConnection, ← hXp,
    InfoGeometry.Canonical.SpinorBundleKosmannDerivative.connectionCorrectedCovariantDerivative_apply
      BaseModel flatSpinorBundleConnection spinConnectionEndomorphismOneForm X σ p]
  rw [InfoGeometry.Canonical.SpinorBundleKosmannDerivative.connectionCorrectedDerivative,
    spinConnectionEndomorphismOneForm_apply]
  simp [flatSpinorBundleConnection, spinConnectionOneForm,
    frameMatrixOnSpinors, spinConnection, spinLift, Vec, deriv_lapse, hXp]
  simp [J1]
  have hhalf (c : ℝ) : 2 * p 1 * c / 2 = p 1 * c := by
    calc
      (2 * p 1 * c) / 2 = (2 * (p 1 * c)) / 2 := by rw [mul_assoc]
      _ = p 1 * c := mul_div_cancel_left₀ _ (by norm_num)
  constructor
  · rw [sub_eq_add_neg, hhalf]
  · rw [sub_eq_add_neg, hhalf]

/-- The spinor-bundle connection's endomorphism coefficient implements the
curved Lorentz frame connection on Clifford vectors, by the concrete adjoint
identity of the real `Cl(1,1)` lift. -/
theorem curvedSpinorBundleConnection_adjoint
    (p v : Base) (u : Vec) :
    spinConnection (p 1) (v 0, v 1) * cliffordVector u -
        cliffordVector u * spinConnection (p 1) (v 0, v 1) =
      cliffordVector ((vectorConnection (p 1) (v 0, v 1)).mulVec u) := by
  exact spinConnection_adjoint (p 1) (v 0, v 1) u

/-- The curved real Clifford action is parallel for the vector connection and
its spin lift. This is the local section-level Kosmann compatibility law:
the derivative of `c(u) ψ` is the sum of the Clifford actions of `∇u` and
`∇ψ`. The algebraic correction is exactly the previously proved adjoint
identity, not an independently supplied compatibility hypothesis. -/
theorem curvedCliffordAction_covariantDerivative
    (u ψ : Base → Vec) (p v : Base)
    (hu : DifferentiableAt ℝ u p) (hψ : DifferentiableAt ℝ ψ p) :
    fderiv ℝ (fun q => cliffordVectorAction (u q) (ψ q)) p v +
        (spinConnection (p 1) (v 0, v 1)).mulVec
          (cliffordVectorAction (u p) (ψ p)) =
      cliffordVectorAction
          ((fderiv ℝ u p v) +
            (vectorConnection (p 1) (v 0, v 1)).mulVec (u p)) (ψ p) +
        cliffordVectorAction (u p)
          ((fderiv ℝ ψ p v) +
            (spinConnection (p 1) (v 0, v 1)).mulVec (ψ p)) := by
  rw [fderiv_cliffordVectorAction_apply u ψ p hu hψ]
  have hadj := spinConnection_adjoint (p 1) (v 0, v 1) (u p)
  have hmat :
      spinConnection (p 1) (v 0, v 1) * cliffordVector (u p) -
          cliffordVector (u p) * spinConnection (p 1) (v 0, v 1) =
        cliffordVector ((vectorConnection (p 1) (v 0, v 1)).mulVec (u p)) :=
    hadj
  have hvec := congrArg (fun A : Mat2 => A.mulVec (ψ p)) hmat
  simp only [Matrix.sub_mulVec] at hvec
  have hAction :
      (spinConnection (p 1) (v 0, v 1)).mulVec
          (cliffordVectorAction (u p) (ψ p)) =
        cliffordVectorAction ((vectorConnection (p 1) (v 0, v 1)).mulVec (u p))
            (ψ p) +
          cliffordVectorAction (u p)
            ((spinConnection (p 1) (v 0, v 1)).mulVec (ψ p)) := by
    have hvec' := hvec
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hvec'
    have h' := (sub_eq_iff_eq_add).mp hvec'
    simpa using h'
  rw [map_add, add_apply, hAction]
  rw [map_add]
  abel_nf

/-- In this self-model chart, the manifold derivative along the tangent
obtained from the coordinate vector `v` is exactly the Fréchet derivative
evaluated on `v`. -/
theorem mvfderiv_tangentCastModel (σ : Base → Vec) (p v : Base) :
    mvfderiv BaseModel σ p
        ((tangentSpaceCastModel BaseModel p).symm v) =
      fderiv ℝ σ p v := by
  rw [mvfderiv_eq_fderiv]
  rfl

/-- Bundle-level curved Kosmann compatibility in the existing real
`CovariantDerivative` carrier. The left side differentiates the actual
Clifford product section; the spinor derivative on the right is the existing
curvature-carrying bundle connection, while the vector term uses the already
proved Lorentz frame connection. -/
theorem curvedCliffordAction_bundleCovariantDerivative
    (u ψ : Base → Vec) (p v : Base)
    (hu : DifferentiableAt ℝ u p) (hψ : DifferentiableAt ℝ ψ p) :
    curvedSpinorBundleConnection
        (fun q => cliffordVectorAction (u q) (ψ q)) p
          ((tangentSpaceCastModel BaseModel p).symm v) =
      cliffordVectorAction
          ((fderiv ℝ u p v) +
            (vectorConnection (p 1) (v 0, v 1)).mulVec (u p)) (ψ p) +
        cliffordVectorAction (u p)
          (curvedSpinorBundleConnection ψ p
            ((tangentSpaceCastModel BaseModel p).symm v)) := by
  rw [curvedSpinorBundleConnection_apply, curvedSpinorBundleConnection_apply]
  rw [mvfderiv_tangentCastModel, mvfderiv_tangentCastModel]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  exact curvedCliffordAction_covariantDerivative u ψ p v hu hψ

/-- The coordinate tangent of the time-translation isometry, viewed in the
tangent fiber of the curved chart. -/
def timeTranslationTangent (p : Base) : TangentSpace BaseModel p :=
  (tangentSpaceCastModel BaseModel p).symm (![1, 0] : Vec)

/-- The coordinate spatial vector field, viewed in the tangent fiber of the
curved chart. -/
def spaceTranslationTangent (p : Base) : TangentSpace BaseModel p :=
  (tangentSpaceCastModel BaseModel p).symm (![0, 1] : Vec)

/-- The manifold derivative of a spinor section linear in the spatial
coordinate, evaluated on the coordinate spatial vector. -/
theorem mvfderiv_spatialCoordinate_smul (C : Vec) (p : Base) :
    mvfderiv BaseModel (fun q : Base => -(q 1) • C) p
      (spaceTranslationTangent p) = -C := by
  rw [mvfderiv_eq_fderiv]
  have hderiv : HasFDerivAt (fun q : Base => -(q 1) • C)
      (((ContinuousLinearMap.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).smulRight (-C))) p := by
    convert (((ContinuousLinearMap.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).smulRight (-C))).hasFDerivAt using 1
    ext q i
    simp [smul_eq_mul]
  change fderiv ℝ (fun q : Vec => -(q 1) • C) p (![0, 1] : Vec) = -C
  rw [hderiv.fderiv]
  simp [ContinuousLinearMap.smulRight_apply]

/-- The spinor field obtained by applying the time-frame connection to a
constant real spinor. -/
def timeConnectionOnConstant (ψ : Vec) (p : Base) : Vec :=
  -(p 1) • (J1.mulVec ψ)

/-- Along the spatial coordinate vector, the induced spinor-bundle
connection kills constant sections. -/
theorem curvedSpinorBundleConnection_spaceOnConstant (ψ : Vec) (p : Base) :
    curvedSpinorBundleConnection (fun _ : Base => ψ) p
      (spaceTranslationTangent p) = 0 := by
  rw [curvedSpinorBundleConnection_apply]
  have hframe : ((![0, 1] : Vec) 0, (![0, 1] : Vec) 1) = (0, 1) := by
    simp
  simp only [spaceTranslationTangent, ContinuousLinearEquiv.apply_symm_apply]
  rw [hframe]
  simp [mvfderiv_const, zero_apply, spinConnection_eq_lapseDerivative,
    deriv_lapse, J1]

/-- Applying the curved spin connection to a constant spinor along the time
coordinate gives the local coefficient section `-x J₁ ψ`. -/
theorem curvedSpinorBundleConnection_timeOnConstant (ψ : Vec) (p : Base) :
    curvedSpinorBundleConnection (fun _ : Base => ψ) p
      (timeTranslationTangent p) = timeConnectionOnConstant ψ p := by
  rw [curvedSpinorBundleConnection_apply]
  simp only [timeTranslationTangent, ContinuousLinearEquiv.apply_symm_apply]
  simp [timeConnectionOnConstant, mvfderiv_const, zero_apply,
    spinConnection_eq_lapseDerivative, deriv_lapse, J1]

/-- The curvature commutator of the constructed real spinor-bundle
connection, evaluated on constant sections and the commuting coordinate
fields, is the already computed spin-frame curvature. This is an actual
bundle-connection computation on the local curved chart, with convention
`R(∂t, ∂x) = ∇t∇x - ∇x∇t`. -/
theorem curvedSpinorBundleConnection_curvatureOnConstant
    (ψ : Vec) (p : Base) :
    curvedSpinorBundleConnection
        (fun q => curvedSpinorBundleConnection (fun _ : Base => ψ) q
          (spaceTranslationTangent q)) p (timeTranslationTangent p) -
      curvedSpinorBundleConnection
        (fun q => curvedSpinorBundleConnection (fun _ : Base => ψ) q
          (timeTranslationTangent q)) p (spaceTranslationTangent p) =
      (spinCurvature (p 1)).mulVec ψ := by
  have hspace : ∀ q : Base,
      curvedSpinorBundleConnection (fun _ : Base => ψ) q
        (spaceTranslationTangent q) = 0 :=
    curvedSpinorBundleConnection_spaceOnConstant ψ
  have htime : ∀ q : Base,
      curvedSpinorBundleConnection (fun _ : Base => ψ) q
        (timeTranslationTangent q) = timeConnectionOnConstant ψ q :=
    curvedSpinorBundleConnection_timeOnConstant ψ
  have hspaceSection :
      (fun q => curvedSpinorBundleConnection (fun _ : Base => ψ) q
        (spaceTranslationTangent q)) = fun _ : Base => (0 : Vec) := by
    funext q
    exact hspace q
  have htimeSection :
      (fun q => curvedSpinorBundleConnection (fun _ : Base => ψ) q
        (timeTranslationTangent q)) = timeConnectionOnConstant ψ := by
    funext q
    exact htime q
  rw [hspaceSection, htimeSection]
  have hzero : curvedSpinorBundleConnection (fun _ : Base => (0 : Vec)) p
      (timeTranslationTangent p) = 0 := by
    rw [curvedSpinorBundleConnection_apply]
    simp [mvfderiv_const, zero_apply]
  have hspatial : curvedSpinorBundleConnection (timeConnectionOnConstant ψ) p
      (spaceTranslationTangent p) = -(J1.mulVec ψ) := by
    rw [curvedSpinorBundleConnection_apply]
    have hframe : ((tangentSpaceCastModel BaseModel p
        (spaceTranslationTangent p)) 0,
        (tangentSpaceCastModel BaseModel p (spaceTranslationTangent p)) 1) =
        (0, 1) := by
      simp [spaceTranslationTangent]
    rw [hframe]
    change mvfderiv BaseModel
        (fun q : Base => -(q 1) • J1.mulVec ψ) p (spaceTranslationTangent p) +
          (spinConnection (p 1) (0, 1)).mulVec (-(p 1) • J1.mulVec ψ) = _
    have hspConn : spinConnection (p 1) (0, 1) = 0 := by
      simp [spinConnection_eq_lapseDerivative, deriv_lapse, J1]
    rw [mvfderiv_spatialCoordinate_smul, hspConn]
    simp
  rw [hzero, hspatial]
  rw [spinCurvature_eq]
  simp [J1]

/-- The spatial component of the curved spinor connection is the ordinary
coordinate derivative.  In this chart the spin connection has no spatial
component; this holds for every differentiable section, not only constant
spinors. -/
theorem curvedSpinorBundleConnection_space_component
    (σ : Base → Vec) (p : Base) :
    curvedSpinorBundleConnection σ p (spaceTranslationTangent p) =
      mvfderiv BaseModel σ p (spaceTranslationTangent p) := by
  rw [curvedSpinorBundleConnection_apply]
  have hframe :
      ((tangentSpaceCastModel BaseModel p (spaceTranslationTangent p)) 0,
        (tangentSpaceCastModel BaseModel p (spaceTranslationTangent p)) 1) =
        (0, 1) := by
    simp [spaceTranslationTangent]
  rw [hframe]
  simp [spinConnection_eq_lapseDerivative, deriv_lapse, J1]

/-- Along the time-translation Killing field, the curved spin connection has
the ordinary directional derivative plus the bivector generator extracted
from the Killing equation. -/
theorem curvedSpinorBundleConnection_time_component (σ : Base → Vec) (p : Base) :
    curvedSpinorBundleConnection σ p (timeTranslationTangent p) =
      mvfderiv BaseModel σ p (timeTranslationTangent p) +
        (kosmannTimeGenerator (p 1)).mulVec (σ p) := by
  rw [curvedSpinorBundleConnection_apply]
  simp only [timeTranslationTangent, ContinuousLinearEquiv.apply_symm_apply]
  have hframe : ((![1, 0] : Vec) 0, (![1, 0] : Vec) 1) = (1, 0) := by
    simp
  rw [hframe, ← kosmannTimeGenerator_eq_spinConnection]

/-- The local spinor connection has the expected curvature on every real
spinor section that is `C²` at the point, not only on constant columns. The proof uses
symmetry of the section's second Fréchet derivative; all connection and
curvature signs are those of `R(∂t,∂x) = ∇t∇x - ∇x∇t`. -/
theorem curvedSpinorBundleConnection_curvature
    (σ : Base → Vec) (p : Base) (hσ : ContDiffAt ℝ 2 σ p) :
    curvedSpinorBundleConnection
        (fun q => curvedSpinorBundleConnection σ q (spaceTranslationTangent q)) p
        (timeTranslationTangent p) -
      curvedSpinorBundleConnection
        (fun q => curvedSpinorBundleConnection σ q (timeTranslationTangent q)) p
        (spaceTranslationTangent p) =
      (spinCurvature (p 1)).mulVec (σ p) := by
  let eT : Vec := ![1, 0]
  let eX : Vec := ![0, 1]
  let J : Vec →L[ℝ] Vec := J1.mulVecLin.toContinuousLinearMap
  have hσAt : ContDiffAt ℝ 2 σ p := hσ
  have hσDiff : DifferentiableAt ℝ σ p :=
    hσAt.differentiableAt (by norm_num)
  have hDσ : ContDiffAt ℝ 1 (fderiv ℝ σ) p :=
    hσAt.fderiv_right (by norm_num)
  have hDσDiff : DifferentiableAt ℝ (fderiv ℝ σ) p :=
    hDσ.differentiableAt (by norm_num)
  have hSymm : IsSymmSndFDerivAt ℝ σ p := by
    apply ContDiffAt.isSymmSndFDerivAt (n := 2) hσAt
    simp
  let dX : Base → Vec := fun q => fderiv ℝ σ q eX
  let dT : Base → Vec := fun q => fderiv ℝ σ q eT
  have hdX : (fun q => curvedSpinorBundleConnection σ q
      (spaceTranslationTangent q)) = dX := by
    funext q
    rw [curvedSpinorBundleConnection_space_component, mvfderiv_eq_fderiv]
    change fderiv ℝ σ q (![0, 1] : Vec) = fderiv ℝ σ q eX
    simp [eX]
  have hdT : (fun q => curvedSpinorBundleConnection σ q
      (timeTranslationTangent q)) = fun q =>
        dT q - q 1 • J (σ q) := by
    funext q
    rw [curvedSpinorBundleConnection_time_component, mvfderiv_eq_fderiv]
    change fderiv ℝ σ q (![1, 0] : Vec) +
      (kosmannTimeGenerator (q 1)).mulVec (σ q) = _
    simp [dT, eT, J, kosmannTimeGenerator, deriv_lapse, J1, sub_eq_add_neg,
      smul_eq_mul]
  rw [show (fun q => curvedSpinorBundleConnection σ q
      (spaceTranslationTangent q)) = dX from hdX,
    show (fun q => curvedSpinorBundleConnection σ q
      (timeTranslationTangent q)) = (fun q => dT q - q 1 • J (σ q)) from hdT]
  rw [curvedSpinorBundleConnection_time_component,
    curvedSpinorBundleConnection_space_component]
  rw [mvfderiv_eq_fderiv, mvfderiv_eq_fderiv]
  have hsecondX :
      fderiv ℝ dX p eT = fderiv ℝ (fderiv ℝ σ) p eT eX := by
    dsimp [dX, eX]
    rw [fderiv_clm_apply hDσDiff (differentiableAt_const _)]
    simp
  have hsecondT :
      fderiv ℝ dT p eX = fderiv ℝ (fderiv ℝ σ) p eX eT := by
    dsimp [dT, eT]
    rw [fderiv_clm_apply hDσDiff (differentiableAt_const _)]
    simp
  have hJDiff : DifferentiableAt ℝ (fun q => J (σ q)) p := by
    exact (differentiableAt_const J).clm_apply hσDiff
  have hJderiv : fderiv ℝ (fun q => J (σ q)) p =
      J.comp (fderiv ℝ σ p) := by
    rw [fderiv_clm_apply (differentiableAt_const J) hσDiff]
    simp
  let coordProj : Base →L[ℝ] ℝ := ContinuousLinearMap.proj (1 : Fin 2)
  have hcoordDiff : DifferentiableAt ℝ (fun q : Base => q 1) p := by
    change DifferentiableAt ℝ (fun q => coordProj q) p
    exact coordProj.differentiableAt
  have hcoordDeriv : fderiv ℝ (fun q : Base => q 1) p eX = 1 := by
    change fderiv ℝ (fun q => coordProj q) p eX = 1
    rw [coordProj.hasFDerivAt.fderiv]
    simp [coordProj, eX, ContinuousLinearMap.proj]
  have hdTDiff : DifferentiableAt ℝ dT p := by
    exact hDσDiff.clm_apply (differentiableAt_const eT)
  have hprodDiff : DifferentiableAt ℝ
      (fun q : Base => q 1 • J (σ q)) p := hcoordDiff.smul hJDiff
  have hproduct :
      fderiv ℝ (fun q : Base => q 1 • J (σ q)) p eX =
        p 1 • J (fderiv ℝ σ p eX) + J (σ p) := by
    rw [fderiv_fun_smul hcoordDiff hJDiff]
    rw [hJderiv]
    change p 1 • J ((fderiv ℝ σ p) eX) +
      (fderiv ℝ (fun q : Base => q 1) p eX) • J (σ p) = _
    rw [hcoordDeriv]
    simp
  have htimeDerivative :
      fderiv ℝ (fun q : Base => dT q - q 1 • J (σ q)) p eX =
        fderiv ℝ dT p eX -
          fderiv ℝ (fun q : Base => q 1 • J (σ q)) p eX := by
    rw [fderiv_fun_sub hdTDiff hprodDiff]
    simp only [sub_apply]
  have hcurv := hSymm.eq eT eX
  change fderiv ℝ dX p (![1, 0] : Vec) +
      (kosmannTimeGenerator (p 1)).mulVec (dX p) -
      fderiv ℝ (fun q => dT q - q 1 • J (σ q)) p (![0, 1] : Vec) =
    (spinCurvature (p 1)).mulVec (σ p)
  rw [hsecondX, htimeDerivative, hsecondT, hproduct, hcurv]
  simp [J, eX, eT, dX, kosmannTimeGenerator, spinCurvature_eq,
    deriv_lapse, J1, smul_eq_mul]

/-- The local spinor-bundle connection has nonzero curvature action, witnessed
on the constant real spinor column `(1, 0)`.  Thus the nonzero matrix
coefficient in `spinCurvature_eq` is detected on the actual rank-two fiber;
it is not merely a nonzero coefficient acting trivially on the chosen spinor
representation. -/
theorem curvedSpinorBundleConnection_curvature_nonzero (p : Base) :
    curvedSpinorBundleConnection
        (fun q => curvedSpinorBundleConnection (fun _ : Base => (![1, 0] : Vec) : Base → Vec) q
          (spaceTranslationTangent q)) p (timeTranslationTangent p) -
      curvedSpinorBundleConnection
        (fun q => curvedSpinorBundleConnection (fun _ : Base => (![1, 0] : Vec) : Base → Vec) q
          (timeTranslationTangent q)) p (spaceTranslationTangent p) ≠ 0 := by
  rw [curvedSpinorBundleConnection_curvature
    (fun _ : Base => (![1, 0] : Vec)) p (by fun_prop)]
  intro h
  have h₁ := congrArg (fun v : Vec => v 1) h
  norm_num [spinCurvature_eq, J1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] at h₁

/-- The spinorial Lie derivative for the time-translation Killing field in
this curved real chart.  The Kosmann correction cancels the spin-frame
connection coefficient, leaving the directional derivative along the static
time-coordinate vector field. -/
def timeKillingKosmannDerivative (σ : Base → Vec) (p : Base) : Vec :=
  curvedSpinorBundleConnection σ p (timeTranslationTangent p) -
    (kosmannTimeGenerator (p 1)).mulVec (σ p)

/-- The coordinate curve generated by the chart's time-translation isometry.
Its tangent at zero is the same real tangent vector used by the bundle
connection and the Kosmann correction. -/
def timeTranslationCurve (p : Base) (s : ℝ) : Base :=
  p + s • (![1, 0] : Vec)

/-- On this static curved chart, the Kosmann lift of the time-translation
Killing field is exactly the directional derivative on the real spinor
bundle; the cancellation is proved using the curved spin connection and the
generator derived from the Killing equation. -/
theorem timeKillingKosmannDerivative_eq_mvfderiv (σ : Base → Vec) (p : Base) :
    timeKillingKosmannDerivative σ p =
      mvfderiv BaseModel σ p (timeTranslationTangent p) := by
  rw [timeKillingKosmannDerivative, curvedSpinorBundleConnection_time_component]
  exact add_sub_cancel_right _ _

/-- The derivative of a pulled-back spinor section along the actual
time-translation flow is the local Kosmann derivative. This identifies the
bundle operator as the infinitesimal generator of the geometric flow, rather
than only as a pointwise cancellation formula. -/
theorem hasDerivAt_timeTranslationPullback_eq_kosmann
    (σ : Base → Vec) (p : Base) (hσ : DifferentiableAt ℝ σ p) :
    HasDerivAt (fun s : ℝ => σ (timeTranslationCurve p s))
      (timeKillingKosmannDerivative σ p) 0 := by
  have hline : HasDerivAt (timeTranslationCurve p) (![1, 0] : Vec) 0 :=
    (hasDerivAt_pi).2 (fun i => by
      fin_cases i
      · simpa [timeTranslationCurve] using
          (hasDerivAt_id (0 : ℝ)).const_add (p 0)
      · simpa [timeTranslationCurve] using
          (hasDerivAt_const (0 : ℝ) (p 1)))
  have hcomp := hσ.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by
    simp [timeTranslationCurve])
  rw [timeKillingKosmannDerivative_eq_mvfderiv]
  change HasDerivAt (fun s : ℝ => σ (timeTranslationCurve p s))
    (mvfderiv BaseModel σ p
      ((tangentSpaceCastModel BaseModel p).symm (![1, 0] : Vec))) 0
  rw [mvfderiv_tangentCastModel]
  simpa [Function.comp_def, timeTranslationCurve] using hcomp

/-- The curved-chart Kosmann derivative has the scalar Leibniz law on smooth
real spinor sections. -/
theorem timeKillingKosmannDerivative_smul
    {σ : Base → Vec} {g : Base → ℝ} {p : Base}
    (hσ : MDifferentiableAt BaseModel 𝓘(ℝ, Vec) σ p)
    (hg : MDifferentiableAt BaseModel 𝓘(ℝ, ℝ) g p) :
    timeKillingKosmannDerivative (g • σ) p =
      g p • timeKillingKosmannDerivative σ p +
        (mvfderiv BaseModel g p (timeTranslationTangent p)) • σ p := by
  rw [timeKillingKosmannDerivative_eq_mvfderiv,
    timeKillingKosmannDerivative_eq_mvfderiv]
  simpa only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] using
    congrArg (fun D : TangentSpace BaseModel p →L[ℝ] Vec =>
      D (timeTranslationTangent p)) (mvfderiv_smul hg hσ)

/-- On a constant real spinor section, the time-frame component of the
curved bundle connection is exactly the real bivector generator previously
derived from the time-translation Killing field. -/
theorem curvedSpinorBundleConnection_timeGenerator (ψ : Vec) (p : Base) :
    curvedSpinorBundleConnection (fun _ : Base => ψ) p
        (timeTranslationTangent p) =
      (kosmannTimeGenerator (p 1)).mulVec ψ := by
  rw [curvedSpinorBundleConnection_apply]
  simp only [mvfderiv_const, zero_apply, zero_add]
  simp only [timeTranslationTangent, ContinuousLinearEquiv.apply_symm_apply]
  have hframe : ((![1, 0] : Vec) 0, (![1, 0] : Vec) 1) = (1, 0) := by
    simp
  rw [hframe, ← kosmannTimeGenerator_eq_spinConnection]

end InfoGeometry.Geometry.CurvedLorentzianKosmannFrame

end
