import InfoGeometry.Canonical.SplitOctonionAutomorphism
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

/-!
# Algebraic ambient representation of real split-octonion automorphisms

The automorphism owner uses the canonical Zorn carrier.  This file transports
its linear equivalences through the already-proved eight-dimensional
`cartesianZornLinearEquiv`; no topology or manifold structure is introduced.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

noncomputable section

/-- The coordinate action obtained by conjugating a canonical Zorn
automorphism through the existing `(4+4)` coordinate equivalence. -/
def realSplitOctonionAutCartesian
    (g : RealSplitOctonionAut) :
    CartesianCoordinates ≃ₗ[ℝ] CartesianCoordinates :=
  cartesianZornLinearEquiv.trans
    ((g : SplitOctonionAutCandidate ℝ).trans cartesianZornLinearEquiv.symm)

@[simp] theorem realSplitOctonionAutCartesian_apply
    (g : RealSplitOctonionAut) (q : CartesianCoordinates) :
    realSplitOctonionAutCartesian g q =
      cartesianZornLinearEquiv.symm
        ((g : SplitOctonionAutCandidate ℝ) (cartesianZornLinearEquiv q)) :=
  rfl

@[simp] theorem realSplitOctonionAutCartesian_one :
    realSplitOctonionAutCartesian (1 : RealSplitOctonionAut) =
      LinearEquiv.refl ℝ CartesianCoordinates := by
  apply LinearEquiv.ext
  rintro ⟨⟨a, x⟩, ⟨b, y⟩⟩
  simp [realSplitOctonionAutCartesian, cartesianZornLinearEquiv]
  constructor <;> funext i <;>
    simp [Pi.add_apply, Pi.sub_apply, Pi.div_apply] <;> ring

theorem realSplitOctonionAutCartesian_mul
    (g h : RealSplitOctonionAut) :
    realSplitOctonionAutCartesian (g * h) =
      realSplitOctonionAutCartesian g * realSplitOctonionAutCartesian h := by
  apply LinearEquiv.ext
  intro q
  simp only [realSplitOctonionAutCartesian_apply, LinearEquiv.mul_apply]
  rw [LinearEquiv.symm_apply_eq]
  simp only [LinearEquiv.apply_symm_apply]
  rfl

theorem realSplitOctonionAutCartesian_inv
    (g : RealSplitOctonionAut) :
    realSplitOctonionAutCartesian g⁻¹ =
      (realSplitOctonionAutCartesian g)⁻¹ := by
  apply LinearEquiv.ext
  intro q
  change cartesianZornLinearEquiv.symm
      ((g : SplitOctonionAutCandidate ℝ)⁻¹
        (cartesianZornLinearEquiv q)) =
    cartesianZornLinearEquiv.symm
      ((g : SplitOctonionAutCandidate ℝ)⁻¹
        (cartesianZornLinearEquiv q))
  rfl

theorem realSplitOctonionAutCartesian_injective :
    Function.Injective realSplitOctonionAutCartesian := by
  intro g h e
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hx := congrArg
      (fun q => cartesianZornLinearEquiv q)
      (LinearEquiv.congr_fun e (cartesianZornLinearEquiv.symm x))
  simpa only [realSplitOctonionAutCartesian_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] using hx

/-- The faithful algebraic ambient group homomorphism. -/
def realSplitOctonionAutCartesianHom :
    RealSplitOctonionAut →* (CartesianCoordinates ≃ₗ[ℝ] CartesianCoordinates) where
  toFun := realSplitOctonionAutCartesian
  map_one' := realSplitOctonionAutCartesian_one
  map_mul' := realSplitOctonionAutCartesian_mul

theorem realSplitOctonionAutCartesianHom_injective :
    Function.Injective realSplitOctonionAutCartesianHom :=
  realSplitOctonionAutCartesian_injective

/-- The same ambient action upgraded to a continuous linear equivalence.
The upgrade uses the native finite-dimensional normed structure on the
Cartesian coordinate carrier and does not alter the algebraic automorphism
carrier. -/
noncomputable def realSplitOctonionAutCartesianContinuous
    (g : RealSplitOctonionAut) :
    CartesianCoordinates ≃L[ℝ] CartesianCoordinates :=
  (realSplitOctonionAutCartesian g).toContinuousLinearEquiv

@[simp] theorem realSplitOctonionAutCartesianContinuous_apply
    (g : RealSplitOctonionAut) (q : CartesianCoordinates) :
    realSplitOctonionAutCartesianContinuous g q =
      realSplitOctonionAutCartesian g q :=
  rfl

theorem realSplitOctonionAutCartesianContinuous_one :
    realSplitOctonionAutCartesianContinuous (1 : RealSplitOctonionAut) =
      ContinuousLinearEquiv.refl ℝ CartesianCoordinates := by
  apply ContinuousLinearEquiv.ext
  funext q
  simp [realSplitOctonionAutCartesianContinuous]

theorem realSplitOctonionAutCartesianContinuous_mul
    (g h : RealSplitOctonionAut) :
    realSplitOctonionAutCartesianContinuous (g * h) =
      realSplitOctonionAutCartesianContinuous g *
        realSplitOctonionAutCartesianContinuous h := by
  apply ContinuousLinearEquiv.ext
  funext q
  change realSplitOctonionAutCartesian (g * h) q =
    realSplitOctonionAutCartesian g
      (realSplitOctonionAutCartesian h q)
  rw [← LinearEquiv.mul_apply]
  exact congrArg (fun e : CartesianCoordinates ≃ₗ[ℝ] CartesianCoordinates => e q)
    (realSplitOctonionAutCartesian_mul g h)

theorem realSplitOctonionAutCartesianContinuous_injective :
    Function.Injective realSplitOctonionAutCartesianContinuous := by
  intro g h e
  apply realSplitOctonionAutCartesian_injective
  apply LinearEquiv.ext
  intro q
  exact congrArg (fun f : CartesianCoordinates ≃L[ℝ] CartesianCoordinates => f q) e

def realSplitOctonionAutCartesianContinuousHom :
    RealSplitOctonionAut →*
      (CartesianCoordinates ≃L[ℝ] CartesianCoordinates) where
  toFun := realSplitOctonionAutCartesianContinuous
  map_one' := realSplitOctonionAutCartesianContinuous_one
  map_mul' := realSplitOctonionAutCartesianContinuous_mul

theorem realSplitOctonionAutCartesianContinuousHom_injective :
    Function.Injective realSplitOctonionAutCartesianContinuousHom :=
  realSplitOctonionAutCartesianContinuous_injective

end
end InfoGeometry.Canonical
