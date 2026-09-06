import InfoGeometry.Canonical.SplitOctonionBogoliubovCarrierBridge
import InfoGeometry.Lie.SplitOctonionQuaternionParityOrientation
import InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
import InfoGeometry.Canonical.LinearInvolutionFrameTransport
import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Explicit quaternion-coordinate to Bogoliubov carrier equivalence

The coordinate carrier used by the mirror/rail owner is written as
`ℝ × (Fin 3 → ℝ)` in each quaternion slot.  The Bogoliubov carrier uses
`EuclideanSpace ℝ (Fin 4)`.  This file supplies the missing linear
equivalence explicitly, then composes it with the existing split-octonion
and Bogoliubov carrier equivalences.
-/

noncomputable section

namespace InfoGeometry.Canonical.QuaternionCoordinateBogoliubovEquiv

open InfoGeometry.Canonical
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionParityOrientation

abbrev QuaternionCoordinates :=
  InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.QuaternionCoordinates
abbrev CartesianCoordinates :=
  InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CartesianCoordinates
abbrev CoordinateSpace :=
  InfoGeometry.Canonical.SplitOctonionCoordinateSpace
abbrev BogoliubovCarrier := InfoGeometry.Krein.DoubledSpace (Quaternion ℝ)

def scalarVectorEquiv :
    QuaternionCoordinates ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun q := Fin.cons q.1 q.2
  invFun v := (v 0, fun i => v i.succ)
  left_inv q := by
    apply Prod.ext
    · rfl
    · funext i
      simp
  right_inv v := by
    funext i
    exact Fin.cases rfl (fun j => rfl) i
  map_add' q r := by
    funext i
    exact Fin.cases rfl (fun j => rfl) i
  map_smul' c q := by
    funext i
    exact Fin.cases rfl (fun j => rfl) i

def scalarVectorEuclideanEquiv :
    QuaternionCoordinates ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  scalarVectorEquiv.trans
    (WithLp.linearEquiv (2 : ENNReal) ℝ (Fin 4 → ℝ)).symm

def cartesianCoordinateEquiv :
    CartesianCoordinates ≃ₗ[ℝ] CoordinateSpace :=
  LinearEquiv.prodCongr scalarVectorEuclideanEquiv scalarVectorEuclideanEquiv

def mirrorRailBogoliubovCarrierEquiv :
    CartesianCoordinates ≃ₗ[ℝ] BogoliubovCarrier :=
  cartesianCoordinateEquiv.trans
    (splitOctonionCoordinateEquiv.symm.trans
      splitOctonionQuaternionicCarrierEquiv)

noncomputable def mirrorRailSwapJKLinearEquiv :
    CartesianCoordinates ≃ₗ[ℝ] CartesianCoordinates :=
  LinearEquiv.ofLinear mirrorRailSwapJK mirrorRailSwapJK
    (by
      apply LinearMap.ext
      intro x
      exact mirrorRailSwapJK_involutive x)
    (by
      apply LinearMap.ext
      intro x
      exact mirrorRailSwapJK_involutive x)

noncomputable def mirrorRailBogoliubovInvolution :
    BogoliubovCarrier ≃ₗ[ℝ] BogoliubovCarrier :=
  LinearInvolutionFrameTransport.transport
    mirrorRailBogoliubovCarrierEquiv mirrorRailSwapJKLinearEquiv

def quaternionNormQuadratic :
    QuadraticMap ℝ QuaternionCoordinates ℝ :=
  (QuadraticMap.weightedSumSquares ℝ (fun _ : Fin 4 => (1 : ℝ))).comp
    scalarVectorEquiv.toLinearMap

def cartesianNormQuadratic :
    QuadraticMap ℝ CartesianCoordinates ℝ :=
  quaternionNormQuadratic.prod quaternionNormQuadratic

theorem mirrorRailBogoliubovInvolution_apply (x : BogoliubovCarrier) :
    mirrorRailBogoliubovInvolution x =
      mirrorRailBogoliubovCarrierEquiv
        (mirrorRailSwapJKLinearEquiv
          (mirrorRailBogoliubovCarrierEquiv.symm x)) :=
  rfl

theorem mirrorRailBogoliubovInvolution_involutive (x : BogoliubovCarrier) :
    mirrorRailBogoliubovInvolution
        (mirrorRailBogoliubovInvolution x) = x := by
  exact LinearInvolutionFrameTransport.transport_involutive
    mirrorRailBogoliubovCarrierEquiv mirrorRailSwapJKLinearEquiv
    (fun y => mirrorRailSwapJK_involutive y) x

theorem mirrorRailSwapJK_preserves_quaternionNorms
    (x : CartesianCoordinates) :
    quaternionNorm (mirrorRailSwapJK x).1 = quaternionNorm x.1 ∧
      quaternionNorm (mirrorRailSwapJK x).2 = quaternionNorm x.2 := by
  rcases x with ⟨⟨q₀, q⟩, ⟨r₀, r⟩⟩
  simp [mirrorRailSwapJK, quaternionNorm,
    InfoGeometry.Canonical.ZornMatrix.dot, Fin.sum_univ_three]
  constructor <;> ring

theorem mirrorRailSwapJK_preserves_sum_quaternionNorm
    (x : CartesianCoordinates) :
    quaternionNorm (mirrorRailSwapJK x).1 +
        quaternionNorm (mirrorRailSwapJK x).2 =
      quaternionNorm x.1 + quaternionNorm x.2 := by
  exact congrArg₂ (· + ·)
    (mirrorRailSwapJK_preserves_quaternionNorms x).1
    (mirrorRailSwapJK_preserves_quaternionNorms x).2

theorem quaternionNormQuadratic_apply (q : QuaternionCoordinates) :
    quaternionNormQuadratic q = quaternionNorm q := by
  simp [quaternionNormQuadratic, quaternionNorm,
    InfoGeometry.Canonical.ZornMatrix.dot,
    QuadraticMap.weightedSumSquares_apply, scalarVectorEquiv,
    Fin.sum_univ_four, Fin.cons]
  have h1 : Fin.cases q.1 q.2 1 = q.2 0 := rfl
  have h2 : Fin.cases q.1 q.2 2 = q.2 1 := rfl
  have h3 : Fin.cases q.1 q.2 3 = q.2 2 := rfl
  rw [h1, h2, h3]
  ring

theorem cartesianNormQuadratic_apply (x : CartesianCoordinates) :
    cartesianNormQuadratic x = quaternionNorm x.1 + quaternionNorm x.2 := by
  simp [cartesianNormQuadratic, quaternionNormQuadratic_apply]

def mirrorRailSwapJK_isometry :
    cartesianNormQuadratic.IsometryEquiv cartesianNormQuadratic := by
  exact
    { toLinearEquiv := mirrorRailSwapJKLinearEquiv
      map_app' := by
        intro x
        rw [cartesianNormQuadratic_apply, cartesianNormQuadratic_apply]
        exact mirrorRailSwapJK_preserves_sum_quaternionNorm x }

theorem scalarVectorEquiv_apply (q : QuaternionCoordinates) :
    scalarVectorEquiv q = Fin.cons q.1 q.2 :=
  rfl

theorem scalarVectorEuclideanEquiv_apply (q : QuaternionCoordinates) :
    scalarVectorEuclideanEquiv q =
      (WithLp.linearEquiv (2 : ENNReal) ℝ (Fin 4 → ℝ)).symm
        (Fin.cons q.1 q.2) :=
  rfl

theorem mirrorRailBogoliubovCarrierEquiv_apply (x : CartesianCoordinates) :
    mirrorRailBogoliubovCarrierEquiv x =
      splitOctonionQuaternionicCarrierEquiv
        (splitOctonionCoordinateEquiv.symm (cartesianCoordinateEquiv x)) :=
  rfl

end InfoGeometry.Canonical.QuaternionCoordinateBogoliubovEquiv
