import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication

namespace InfoGeometry.Canonical

/-!
# Nilpotent left-multiplication differentials

This file deliberately does not identify a square-zero split-octonion element
with an exterior one-form.  It records the valid algebraic statement: left
multiplication by `theta` is a square-zero linear operator when the chosen
multiplication satisfies left alternativity at `theta` and `theta * theta = 0`.
-/

def leftMulDifferential (theta : StandardIntegralSplitOctonion) :
    StandardIntegralSplitOctonion →ₗ[ℤ] StandardIntegralSplitOctonion where
  toFun omega := splitOctonionMul theta omega
  map_add' omega eta := by
    ext r
    fin_cases r <;>
      dsimp [splitOctonionMul, splitQuaternionOf, splitQuaternionLPart,
        splitQuaternionAdd, splitQuaternionMul, splitQuaternionConj,
        splitOctonionOfQuaternionPair] <;>
      ring
  map_smul' a omega := by
    ext r
    fin_cases r <;>
      dsimp [splitOctonionMul, splitQuaternionOf, splitQuaternionLPart,
        splitQuaternionAdd, splitQuaternionMul, splitQuaternionConj,
        splitOctonionOfQuaternionPair] <;>
      ring

theorem leftMulDifferential_apply
    (theta omega : StandardIntegralSplitOctonion) :
    leftMulDifferential theta omega = splitOctonionMul theta omega := rfl

theorem leftMulDifferential_comp_eq_leftMul_sq
    (theta : StandardIntegralSplitOctonion)
    (hleft : ∀ omega : StandardIntegralSplitOctonion,
      splitOctonionMul theta (splitOctonionMul theta omega) =
        splitOctonionMul (splitOctonionMul theta theta) omega) :
      (leftMulDifferential theta).comp (leftMulDifferential theta) =
      leftMulDifferential (splitOctonionMul theta theta) := by
  apply LinearMap.ext
  intro omega
  exact hleft omega

theorem leftMulDifferential_comp_eq_zero
    (theta : StandardIntegralSplitOctonion)
    (hleft : ∀ omega : StandardIntegralSplitOctonion,
      splitOctonionMul theta (splitOctonionMul theta omega) =
        splitOctonionMul (splitOctonionMul theta theta) omega)
    (hsq : splitOctonionMul theta theta = 0) :
    (leftMulDifferential theta).comp (leftMulDifferential theta) = 0 := by
  rw [leftMulDifferential_comp_eq_leftMul_sq theta hleft, hsq]
  apply LinearMap.ext
  intro omega
  ext r
  fin_cases r <;>
    dsimp [leftMulDifferential, splitOctonionMul, splitQuaternionOf,
      splitQuaternionLPart, splitQuaternionAdd, splitQuaternionMul,
      splitQuaternionConj, splitOctonionOfQuaternionPair] <;>
    ring

end InfoGeometry.Canonical
