import InfoGeometry.Volume.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Additive Volume Potential

Introduces the additive potential (Log-Volume) derived from the multiplicative 
volume homomorphism. This formalizes the transition from groups to potentials.
-/

namespace InfoGeometry.Volume.LogPotential

open InfoGeometry.Volume.Base

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/--
Log-Absolute Volume Potential (Φ).
Satisfies Φ(f ∘ g) = Φ(f) + Φ(g), transforming non-commutative products into 
additive potentials.
-/
noncomputable def LogAbsVolume (g : V ≃ₗ[ℝ] V) : ℝ :=
  Real.log |((VolumeHom g : ℝˣ) : ℝ)|

/--
Theorem: The Log-Absolute Volume is additive.
This is the mathematical origin of why entropy and Hamiltonians are additive.
The use of explicit coercions and `Real.log_mul` ensures mathematical rigor.
-/
theorem logAbsVolume_add (f g : V ≃ₗ[ℝ] V) :
    LogAbsVolume (f.trans g) = LogAbsVolume f + LogAbsVolume g := by
  unfold LogAbsVolume
  rw [VolumeHom, LinearEquiv.det_trans]
  -- det(g ∘ f) = det(g) * det(f) in Units ℝ
  rw [mul_comm] -- Units ℝ is commutative since ℝ is commutative
  rw [Units.val_mul, abs_mul, Real.log_mul]
  · exact abs_ne_zero.mpr (Units.ne_zero _)
  · exact abs_ne_zero.mpr (Units.ne_zero _)

end InfoGeometry.Volume.LogPotential
