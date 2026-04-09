import InfoGeometry.Quantum.ParitySupercharge
import InfoGeometry.Quantum.RealMajoranaCategory
import InfoGeometry.Meta.Architecture
import Mathlib.Tactic.Abel

open scoped InnerProductSpace

/-!
# InfoGeometry.Quantum.SplitTrialityKernel

Repo-native triality seed on the real doubled Majorana core.

This file does not claim that the repository already owns the full `Spin(4,4)`
or split-octonionic multiplication package. Instead, it isolates the concrete
triality-shaped kernel that the current formalization really supports:

- the common doubled real Majorana core,
- two null-mode Clifford channels playing the role of left/right spinor maps,
- the canonical spectral polarization recovered from their cross-compositions,
- and the induced real involutive supercharge/Dirac-square seed.
-/

namespace InfoGeometry.Quantum

open InfoGeometry.Krein
open InfoGeometry.Quantum.RealMajoranaCategory

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Xc" => cl11DoubledCore E
local notation "H₂" => DoubledSpace E

/--
Concrete triality kernel on a real doubled Majorana core.

The carrier presentations are kept on the same underlying core; the nontrivial
content lies in the chiral transfer maps and their recomposition laws.
-/
@[rep_depth krein]
structure SplitTrialityKernel where
  core : RealMajoranaCore
  polarization : Polarization core
  vectorToLeftSpinor : core →ₗ[ℝ] core
  vectorToRightSpinor : core →ₗ[ℝ] core
  left_nilpotent : vectorToLeftSpinor.comp vectorToLeftSpinor = 0
  right_nilpotent : vectorToRightSpinor.comp vectorToRightSpinor = 0
  right_comp_left_eq_plus : vectorToRightSpinor.comp vectorToLeftSpinor = polarization.Pplus
  left_comp_right_eq_minus : vectorToLeftSpinor.comp vectorToRightSpinor = polarization.Pminus

namespace SplitTrialityKernel

/-- The odd triality supercharge obtained by summing the two chiral transfer maps. -/
@[rep_depth krein]
noncomputable def trialitySupercharge
    (T : SplitTrialityKernel) : T.core →ₗ[ℝ] T.core :=
  T.vectorToLeftSpinor + T.vectorToRightSpinor

/-- The even Dirac-square/Hamiltonian seed carried by the triality supercharge. -/
@[rep_depth krein]
noncomputable def informationalDiracSquare
    (T : SplitTrialityKernel) : T.core →ₗ[ℝ] T.core :=
  T.trialitySupercharge.comp T.trialitySupercharge

@[rep_depth krein]
theorem informationalDiracSquare_eq_id
    (T : SplitTrialityKernel) :
    T.informationalDiracSquare = LinearMap.id := by
  calc
    T.informationalDiracSquare
        = (T.vectorToLeftSpinor + T.vectorToRightSpinor).comp
            (T.vectorToLeftSpinor + T.vectorToRightSpinor) := by
              rfl
    _ = T.vectorToLeftSpinor.comp T.vectorToLeftSpinor
          + (T.vectorToRightSpinor.comp T.vectorToLeftSpinor
              + (T.vectorToLeftSpinor.comp T.vectorToRightSpinor
                  + T.vectorToRightSpinor.comp T.vectorToRightSpinor)) := by
            simp [LinearMap.add_comp, LinearMap.comp_add, add_assoc]
    _ = T.polarization.Pplus + T.polarization.Pminus := by
          rw [T.left_nilpotent, T.right_nilpotent,
            T.right_comp_left_eq_plus, T.left_comp_right_eq_minus]
          simp
    _ = LinearMap.id := by
          exact T.polarization.sum_id

@[rep_depth krein, simp]
theorem trialitySupercharge_sq_eq_id
    (T : SplitTrialityKernel) :
    T.trialitySupercharge.comp T.trialitySupercharge = LinearMap.id :=
  T.informationalDiracSquare_eq_id

/-- The square of the triality supercharge is the even anticommutator seed of the two chiral transfer maps. -/
@[rep_depth krein]
theorem trialitySupercharge_sq_eq_anticommutator
    (T : SplitTrialityKernel) :
    T.trialitySupercharge.comp T.trialitySupercharge
      =
    anticommutator T.vectorToLeftSpinor T.vectorToRightSpinor := by
  calc
    T.trialitySupercharge.comp T.trialitySupercharge
        = T.vectorToLeftSpinor.comp T.vectorToLeftSpinor
            + (T.vectorToRightSpinor.comp T.vectorToLeftSpinor
                + (T.vectorToLeftSpinor.comp T.vectorToRightSpinor
                    + T.vectorToRightSpinor.comp T.vectorToRightSpinor)) := by
              simp [trialitySupercharge, LinearMap.add_comp, LinearMap.comp_add, add_assoc]
    _ = T.vectorToRightSpinor.comp T.vectorToLeftSpinor
          + T.vectorToLeftSpinor.comp T.vectorToRightSpinor := by
          rw [T.left_nilpotent, T.right_nilpotent]
          simp [add_comm]
    _ = anticommutator T.vectorToLeftSpinor T.vectorToRightSpinor := by
          unfold anticommutator
          rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
          simp [add_comm]

/-- The triality supercharge restricted to the `+` sector is the left-spinor transfer map. -/
@[rep_depth krein]
theorem trialitySupercharge_comp_plus_eq_left
    (T : SplitTrialityKernel) :
    T.trialitySupercharge.comp T.polarization.Pplus = T.vectorToLeftSpinor := by
  have hLeftOnPlus :
      T.vectorToLeftSpinor.comp T.polarization.Pplus = T.vectorToLeftSpinor := by
    have hDecomp :
        T.vectorToLeftSpinor.comp T.polarization.Pplus
          + T.vectorToLeftSpinor.comp T.polarization.Pminus
          = T.vectorToLeftSpinor := by
      calc
        T.vectorToLeftSpinor.comp T.polarization.Pplus
            + T.vectorToLeftSpinor.comp T.polarization.Pminus
            = T.vectorToLeftSpinor.comp
                (T.polarization.Pplus + T.polarization.Pminus) := by
                  simp [LinearMap.comp_add]
        _ = T.vectorToLeftSpinor.comp (LinearMap.id : T.core →ₗ[ℝ] T.core) := by
              rw [T.polarization.sum_id]
        _ = T.vectorToLeftSpinor := by simp
    have hZero :
        T.vectorToLeftSpinor.comp T.polarization.Pminus = 0 := by
      calc
        T.vectorToLeftSpinor.comp T.polarization.Pminus
            = (T.vectorToLeftSpinor.comp T.vectorToLeftSpinor).comp
                T.vectorToRightSpinor := by
                  rw [show T.polarization.Pminus
                    = T.vectorToLeftSpinor.comp T.vectorToRightSpinor by
                      exact T.left_comp_right_eq_minus.symm]
                  simp [LinearMap.comp_assoc]
        _ = 0 := by
              rw [T.left_nilpotent]
              simp
    simpa [hZero] using hDecomp
  have hRightOnPlusZero :
      T.vectorToRightSpinor.comp T.polarization.Pplus = 0 := by
    calc
      T.vectorToRightSpinor.comp T.polarization.Pplus
          = (T.vectorToRightSpinor.comp T.vectorToRightSpinor).comp
              T.vectorToLeftSpinor := by
                rw [show T.polarization.Pplus
                  = T.vectorToRightSpinor.comp T.vectorToLeftSpinor by
                    exact T.right_comp_left_eq_plus.symm]
                simp [LinearMap.comp_assoc]
      _ = 0 := by
            rw [T.right_nilpotent]
            simp
  calc
    T.trialitySupercharge.comp T.polarization.Pplus
        = T.vectorToLeftSpinor.comp T.polarization.Pplus
            + T.vectorToRightSpinor.comp T.polarization.Pplus := by
              simp [trialitySupercharge, LinearMap.add_comp]
    _ = T.vectorToLeftSpinor := by
          simp [hLeftOnPlus, hRightOnPlusZero]

/-- The triality supercharge restricted to the `-` sector is the right-spinor transfer map. -/
@[rep_depth krein]
theorem trialitySupercharge_comp_minus_eq_right
    (T : SplitTrialityKernel) :
    T.trialitySupercharge.comp T.polarization.Pminus = T.vectorToRightSpinor := by
  have hLeftOnMinusZero :
      T.vectorToLeftSpinor.comp T.polarization.Pminus = 0 := by
    calc
      T.vectorToLeftSpinor.comp T.polarization.Pminus
          = (T.vectorToLeftSpinor.comp T.vectorToLeftSpinor).comp
              T.vectorToRightSpinor := by
                rw [show T.polarization.Pminus
                  = T.vectorToLeftSpinor.comp T.vectorToRightSpinor by
                    exact T.left_comp_right_eq_minus.symm]
                simp [LinearMap.comp_assoc]
      _ = 0 := by
            rw [T.left_nilpotent]
            simp
  have hRightOnMinus :
      T.vectorToRightSpinor.comp T.polarization.Pminus = T.vectorToRightSpinor := by
    have hDecomp :
        T.vectorToRightSpinor.comp T.polarization.Pplus
          + T.vectorToRightSpinor.comp T.polarization.Pminus
          = T.vectorToRightSpinor := by
      calc
        T.vectorToRightSpinor.comp T.polarization.Pplus
            + T.vectorToRightSpinor.comp T.polarization.Pminus
            = T.vectorToRightSpinor.comp
                (T.polarization.Pplus + T.polarization.Pminus) := by
                  simp [LinearMap.comp_add]
        _ = T.vectorToRightSpinor.comp (LinearMap.id : T.core →ₗ[ℝ] T.core) := by
              rw [T.polarization.sum_id]
        _ = T.vectorToRightSpinor := by simp
    have hZero :
        T.vectorToRightSpinor.comp T.polarization.Pplus = 0 := by
      calc
        T.vectorToRightSpinor.comp T.polarization.Pplus
            = (T.vectorToRightSpinor.comp T.vectorToRightSpinor).comp
                T.vectorToLeftSpinor := by
                  rw [show T.polarization.Pplus
                    = T.vectorToRightSpinor.comp T.vectorToLeftSpinor by
                      exact T.right_comp_left_eq_plus.symm]
                  simp [LinearMap.comp_assoc]
        _ = 0 := by
              rw [T.right_nilpotent]
              simp
    simpa [hZero] using hDecomp
  calc
    T.trialitySupercharge.comp T.polarization.Pminus
        = T.vectorToLeftSpinor.comp T.polarization.Pminus
            + T.vectorToRightSpinor.comp T.polarization.Pminus := by
              simp [trialitySupercharge, LinearMap.add_comp]
    _ = T.vectorToRightSpinor := by
          simp [hLeftOnMinusZero, hRightOnMinus]

/-- Projecting after the triality supercharge onto the `+` sector recovers the right-spinor transfer map. -/
@[rep_depth krein]
theorem plus_comp_trialitySupercharge_eq_right
    (T : SplitTrialityKernel) :
    T.polarization.Pplus.comp T.trialitySupercharge = T.vectorToRightSpinor := by
  have hPlusOnLeftZero :
      T.polarization.Pplus.comp T.vectorToLeftSpinor = 0 := by
    calc
      T.polarization.Pplus.comp T.vectorToLeftSpinor
          = T.vectorToRightSpinor.comp
              (T.vectorToLeftSpinor.comp T.vectorToLeftSpinor) := by
                rw [show T.polarization.Pplus
                  = T.vectorToRightSpinor.comp T.vectorToLeftSpinor by
                    exact T.right_comp_left_eq_plus.symm]
                simp [LinearMap.comp_assoc]
      _ = 0 := by
            rw [T.left_nilpotent]
            simp
  have hPlusOnRight :
      T.polarization.Pplus.comp T.vectorToRightSpinor = T.vectorToRightSpinor := by
    have hDecomp :
        T.polarization.Pplus.comp T.vectorToRightSpinor
          + T.polarization.Pminus.comp T.vectorToRightSpinor
          = T.vectorToRightSpinor := by
      calc
        T.polarization.Pplus.comp T.vectorToRightSpinor
            + T.polarization.Pminus.comp T.vectorToRightSpinor
            = (T.polarization.Pplus + T.polarization.Pminus).comp
                T.vectorToRightSpinor := by
                  simp [LinearMap.add_comp]
        _ = (LinearMap.id : T.core →ₗ[ℝ] T.core).comp T.vectorToRightSpinor := by
              rw [T.polarization.sum_id]
        _ = T.vectorToRightSpinor := by simp
    have hZero :
        T.polarization.Pminus.comp T.vectorToRightSpinor = 0 := by
      calc
        T.polarization.Pminus.comp T.vectorToRightSpinor
            = T.vectorToLeftSpinor.comp
                (T.vectorToRightSpinor.comp T.vectorToRightSpinor) := by
                  rw [show T.polarization.Pminus
                    = T.vectorToLeftSpinor.comp T.vectorToRightSpinor by
                      exact T.left_comp_right_eq_minus.symm]
                  simp [LinearMap.comp_assoc]
        _ = 0 := by
              rw [T.right_nilpotent]
              simp
    simpa [hZero] using hDecomp
  calc
    T.polarization.Pplus.comp T.trialitySupercharge
        = T.polarization.Pplus.comp T.vectorToLeftSpinor
            + T.polarization.Pplus.comp T.vectorToRightSpinor := by
              simp [trialitySupercharge, LinearMap.comp_add]
    _ = T.vectorToRightSpinor := by
          simp [hPlusOnLeftZero, hPlusOnRight]

/-- Projecting after the triality supercharge onto the `-` sector recovers the left-spinor transfer map. -/
@[rep_depth krein]
theorem minus_comp_trialitySupercharge_eq_left
    (T : SplitTrialityKernel) :
    T.polarization.Pminus.comp T.trialitySupercharge = T.vectorToLeftSpinor := by
  have hMinusOnLeft :
      T.polarization.Pminus.comp T.vectorToLeftSpinor = T.vectorToLeftSpinor := by
    have hDecomp :
        T.polarization.Pplus.comp T.vectorToLeftSpinor
          + T.polarization.Pminus.comp T.vectorToLeftSpinor
          = T.vectorToLeftSpinor := by
      calc
        T.polarization.Pplus.comp T.vectorToLeftSpinor
            + T.polarization.Pminus.comp T.vectorToLeftSpinor
            = (T.polarization.Pplus + T.polarization.Pminus).comp
                T.vectorToLeftSpinor := by
                  simp [LinearMap.add_comp]
        _ = (LinearMap.id : T.core →ₗ[ℝ] T.core).comp T.vectorToLeftSpinor := by
              rw [T.polarization.sum_id]
        _ = T.vectorToLeftSpinor := by simp
    have hZero :
        T.polarization.Pplus.comp T.vectorToLeftSpinor = 0 := by
      calc
        T.polarization.Pplus.comp T.vectorToLeftSpinor
            = T.vectorToRightSpinor.comp
                (T.vectorToLeftSpinor.comp T.vectorToLeftSpinor) := by
                  rw [show T.polarization.Pplus
                    = T.vectorToRightSpinor.comp T.vectorToLeftSpinor by
                      exact T.right_comp_left_eq_plus.symm]
                  simp [LinearMap.comp_assoc]
        _ = 0 := by
              rw [T.left_nilpotent]
              simp
    simpa [hZero] using hDecomp
  have hMinusOnRightZero :
      T.polarization.Pminus.comp T.vectorToRightSpinor = 0 := by
    calc
      T.polarization.Pminus.comp T.vectorToRightSpinor
          = T.vectorToLeftSpinor.comp
              (T.vectorToRightSpinor.comp T.vectorToRightSpinor) := by
                rw [show T.polarization.Pminus
                  = T.vectorToLeftSpinor.comp T.vectorToRightSpinor by
                    exact T.left_comp_right_eq_minus.symm]
                simp [LinearMap.comp_assoc]
      _ = 0 := by
            rw [T.right_nilpotent]
            simp
  calc
    T.polarization.Pminus.comp T.trialitySupercharge
        = T.polarization.Pminus.comp T.vectorToLeftSpinor
            + T.polarization.Pminus.comp T.vectorToRightSpinor := by
              simp [trialitySupercharge, LinearMap.comp_add]
    _ = T.vectorToLeftSpinor := by
          simp [hMinusOnLeft, hMinusOnRightZero]

end SplitTrialityKernel

/-- Canonical left-spinor transfer map generated by the null mode `u_-`. -/
@[rep_depth krein]
noncomputable def vectorToLeftSpinor : Xc →ₗ[ℝ] Xc :=
  (cl11SplitCliffordDatum E).majoranaField (cl11_uMinus (E := E))

/-- Canonical right-spinor transfer map generated by the null mode `u_+`. -/
@[rep_depth krein]
noncomputable def vectorToRightSpinor : Xc →ₗ[ℝ] Xc :=
  (cl11SplitCliffordDatum E).majoranaField (cl11_uPlus (E := E))

@[rep_depth krein, simp]
theorem vectorToLeftSpinor_apply_to_doubled
    (x y : E) :
    vectorToLeftSpinor (E := E) (to_doubled x y : H₂) = to_doubled (0 : E) x := by
  unfold vectorToLeftSpinor
  exact cl11_majoranaField_uMinus_apply_to_doubled (E := E) x y

@[rep_depth krein, simp]
theorem vectorToRightSpinor_apply_to_doubled
    (x y : E) :
    vectorToRightSpinor (E := E) (to_doubled x y : H₂) = to_doubled y (0 : E) := by
  unfold vectorToRightSpinor
  exact cl11_majoranaField_uPlus_apply_to_doubled (E := E) x y

@[rep_depth krein]
theorem vectorToLeftSpinor_nilpotent :
    (((vectorToLeftSpinor (E := E)) : Xc →ₗ[ℝ] Xc).comp
      ((vectorToLeftSpinor (E := E)) : Xc →ₗ[ℝ] Xc)) = 0 := by
  ext v
  have hv : (to_doubled (WithLp.fst v) (WithLp.snd v) : H₂) = v := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hv]
  apply DoubledSpace.ext <;>
    simp [LinearMap.comp_apply]

@[rep_depth krein]
theorem vectorToRightSpinor_nilpotent :
    (((vectorToRightSpinor (E := E)) : Xc →ₗ[ℝ] Xc).comp
      ((vectorToRightSpinor (E := E)) : Xc →ₗ[ℝ] Xc)) = 0 := by
  ext v
  have hv : (to_doubled (WithLp.fst v) (WithLp.snd v) : H₂) = v := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hv]
  apply DoubledSpace.ext <;>
    simp [LinearMap.comp_apply]

@[rep_depth krein]
theorem vectorToRightSpinor_comp_vectorToLeftSpinor_eq_plusProj :
    (((vectorToRightSpinor (E := E)) : Xc →ₗ[ℝ] Xc).comp
      ((vectorToLeftSpinor (E := E)) : Xc →ₗ[ℝ] Xc))
      =
    (cl11CanonicalPolarization (E := E)).Pplus := by
  change (((vectorToRightSpinor (E := E)) : Xc →ₗ[ℝ] Xc).comp
      ((vectorToLeftSpinor (E := E)) : Xc →ₗ[ℝ] Xc))
      =
    (spectralPlusProj (E := E)).toLinearMap
  ext v
  have hv : (to_doubled (WithLp.fst v) (WithLp.snd v) : H₂) = v := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hv]
  simp [LinearMap.comp_apply, vectorToLeftSpinor_apply_to_doubled,
    vectorToRightSpinor_apply_to_doubled]
  exact
    (spectralPlusProj_apply_to_doubled (E := E)
      (x := WithLp.fst v) (y := WithLp.snd v)).symm

@[rep_depth krein]
theorem vectorToLeftSpinor_comp_vectorToRightSpinor_eq_minusProj :
    (((vectorToLeftSpinor (E := E)) : Xc →ₗ[ℝ] Xc).comp
      ((vectorToRightSpinor (E := E)) : Xc →ₗ[ℝ] Xc))
      =
    (cl11CanonicalPolarization (E := E)).Pminus := by
  change (((vectorToLeftSpinor (E := E)) : Xc →ₗ[ℝ] Xc).comp
      ((vectorToRightSpinor (E := E)) : Xc →ₗ[ℝ] Xc))
      =
    (spectralMinusProj (E := E)).toLinearMap
  ext v
  have hv : (to_doubled (WithLp.fst v) (WithLp.snd v) : H₂) = v := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hv]
  simp [LinearMap.comp_apply, vectorToRightSpinor_apply_to_doubled,
    vectorToLeftSpinor_apply_to_doubled]
  exact
    (spectralMinusProj_apply_to_doubled (E := E)
      (x := WithLp.fst v) (y := WithLp.snd v)).symm

/-- Canonical repo-native split-triality kernel on the doubled real Majorana core. -/
@[rep_depth krein]
noncomputable def canonicalSplitTrialityKernel : SplitTrialityKernel where
  core := cl11DoubledCore E
  polarization := cl11CanonicalPolarization (E := E)
  vectorToLeftSpinor := (vectorToLeftSpinor (E := E) : Xc →ₗ[ℝ] Xc)
  vectorToRightSpinor := (vectorToRightSpinor (E := E) : Xc →ₗ[ℝ] Xc)
  left_nilpotent := vectorToLeftSpinor_nilpotent (E := E)
  right_nilpotent := vectorToRightSpinor_nilpotent (E := E)
  right_comp_left_eq_plus := vectorToRightSpinor_comp_vectorToLeftSpinor_eq_plusProj (E := E)
  left_comp_right_eq_minus := vectorToLeftSpinor_comp_vectorToRightSpinor_eq_minusProj (E := E)

namespace canonicalSplitTrialityKernel

/-- The canonical triality supercharge acts as modular swap on doubled states. -/
@[rep_depth krein]
theorem trialitySupercharge_eq_modularJ :
    (canonicalSplitTrialityKernel (E := E)).trialitySupercharge
      =
    (modular_j (E := E)).toLinearMap := by
  ext v
  have hv : (to_doubled (WithLp.fst v) (WithLp.snd v) : H₂) = v := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hv]
  change
    vectorToLeftSpinor (E := E) (to_doubled (WithLp.fst v) (WithLp.snd v))
      +
    vectorToRightSpinor (E := E) (to_doubled (WithLp.fst v) (WithLp.snd v))
      =
    modular_j (E := E) (to_doubled (WithLp.fst v) (WithLp.snd v))
  rw [vectorToLeftSpinor_apply_to_doubled, vectorToRightSpinor_apply_to_doubled,
    modular_j_to_doubled]
  simpa [to_doubled] using
    (WithLp.toLp_add (p := (2 : ENNReal))
      (x := ((0 : E), WithLp.fst v))
      (y := (WithLp.snd v, (0 : E)))).symm

/-- The canonical triality supercharge is odd with respect to the parity involution `Π = ε`. -/
@[rep_depth krein]
theorem trialitySupercharge_anticommutes_Pi :
    (canonicalSplitTrialityKernel (E := E)).trialitySupercharge.comp
        (canonicalSplitTrialityKernel (E := E)).core.Pi
      =
    -((canonicalSplitTrialityKernel (E := E)).core.Pi.comp
        (canonicalSplitTrialityKernel (E := E)).trialitySupercharge) := by
  rw [trialitySupercharge_eq_modularJ (E := E)]
  change (modular_j (E := E)).toLinearMap.comp (spectral_epsilon (E := E)).toLinearMap
      =
    -((spectral_epsilon (E := E)).toLinearMap.comp (modular_j (E := E)).toLinearMap)
  exact congrArg ContinuousLinearMap.toLinearMap
    (modular_j_spectral_epsilon_anticommute (E := E))

/-- Canonical parity-relative supercharge package carried by the triality kernel. -/
@[rep_depth krein]
noncomputable def paritySupercharge :
    ParitySupercharge (cl11DoubledCore E) where
  Q := (canonicalSplitTrialityKernel (E := E)).trialitySupercharge
  odd := by
    exact trialitySupercharge_anticommutes_Pi (E := E)

/-- The canonical Dirac square is the even identity Hamiltonian on the doubled core. -/
@[rep_depth krein, simp]
theorem informationalDiracSquare_eq_id :
    (canonicalSplitTrialityKernel (E := E)).informationalDiracSquare = LinearMap.id := by
  exact SplitTrialityKernel.informationalDiracSquare_eq_id (canonicalSplitTrialityKernel (E := E))

/-- The canonical parity-supercharge Hamiltonian is the identity on the doubled core. -/
@[rep_depth krein, simp]
theorem paritySupercharge_hamiltonian_eq_id :
    (paritySupercharge (E := E)).hamiltonian = LinearMap.id := by
  exact informationalDiracSquare_eq_id (E := E)

/-- The canonical parity-supercharge Hamiltonian is parity-even. -/
@[rep_depth krein]
theorem paritySupercharge_hamiltonian_parityEven :
    RealMajoranaCore.ParityEven (cl11DoubledCore E) (paritySupercharge (E := E)).hamiltonian := by
  exact ParitySupercharge.hamiltonian_parityEven (paritySupercharge (E := E))

end canonicalSplitTrialityKernel

end Core

end InfoGeometry.Quantum
