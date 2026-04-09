import InfoGeometry.Quantum.SplitTrialityKernel
import InfoGeometry.Canonical.BogoliubovFockSuper

/-!
# InfoGeometry.Quantum.SplitTrialityFockBridge

Cross-family identification between the split-triality kernel and the concrete
CAR/Fock owner surface.

This file keeps owner facts in their owner files:
- `SplitTrialityKernel` owns the triality channels and the `Q²` square law,
- `BogoliubovFockSuper` owns the concrete CAR/Fock channels and their even seed.

Here we only identify the two presentations.
-/

namespace InfoGeometry.Quantum.SplitTrialityFockBridge

open InfoGeometry.Krein
open InfoGeometry.Quantum
open InfoGeometry.Quantum.RealMajoranaCategory
open InfoGeometry.Canonical.BogoliubovFockSuper

open scoped InnerProductSpace

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "Xc" => InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E

/-- The triality left-spinor channel is the concrete CAR annihilation map. -/
theorem vectorToLeftSpinor_eq_cliffordConcreteAnnihilation_toLinearMap :
    (InfoGeometry.Quantum.vectorToLeftSpinor (E := E) : Xc →ₗ[ℝ] Xc)
      =
    (cliffordConcreteAnnihilation (E := E)).toLinearMap := by
  rw [cliffordConcreteAnnihilation_toLinearMap]
  rfl

/-- The triality right-spinor channel is the concrete CAR creation map. -/
theorem vectorToRightSpinor_eq_cliffordConcreteCreation_toLinearMap :
    (InfoGeometry.Quantum.vectorToRightSpinor (E := E) : Xc →ₗ[ℝ] Xc)
      =
    (cliffordConcreteCreation (E := E)).toLinearMap := by
  rw [cliffordConcreteCreation_toLinearMap]
  rfl

/--
The even anticommutator seed carried by the triality kernel is exactly the
concrete CAR anticommutator on the continuous Fock surface.
-/
theorem triality_anticommutator_eq_cliffordConcrete_anticommutator :
    InfoGeometry.Quantum.RealMajoranaCategory.anticommutator
        (InfoGeometry.Quantum.vectorToLeftSpinor (E := E))
        (InfoGeometry.Quantum.vectorToRightSpinor (E := E))
      =
    (fockAnticommutator (E := E)
      (cliffordConcreteAnnihilation (E := E))
      (cliffordConcreteCreation (E := E))).toLinearMap := by
  rw [InfoGeometry.Quantum.RealMajoranaCategory.anticommutator, fockAnticommutator]
  unfold InfoGeometry.Canonical.BogoliubovFockSuper.anticommutator
  rw [superBracket_odd_odd]
  simp [vectorToLeftSpinor_eq_cliffordConcreteAnnihilation_toLinearMap,
    vectorToRightSpinor_eq_cliffordConcreteCreation_toLinearMap,
    Module.End.mul_eq_comp, add_comm]

/--
The canonical triality supercharge square lands on the already-owned concrete
CAR anticommutator surface.
-/
theorem trialitySupercharge_square_eq_cliffordConcrete_anticommutator :
    (canonicalSplitTrialityKernel (E := E)).trialitySupercharge.comp
        (canonicalSplitTrialityKernel (E := E)).trialitySupercharge
      =
    (fockAnticommutator (E := E)
      (cliffordConcreteAnnihilation (E := E))
      (cliffordConcreteCreation (E := E))).toLinearMap := by
  calc
    (canonicalSplitTrialityKernel (E := E)).trialitySupercharge.comp
        (canonicalSplitTrialityKernel (E := E)).trialitySupercharge
        =
      InfoGeometry.Quantum.RealMajoranaCategory.anticommutator
        (InfoGeometry.Quantum.vectorToLeftSpinor (E := E))
        (InfoGeometry.Quantum.vectorToRightSpinor (E := E)) := by
          exact SplitTrialityKernel.trialitySupercharge_sq_eq_anticommutator
            (canonicalSplitTrialityKernel (E := E))
    _ = (fockAnticommutator (E := E)
        (cliffordConcreteAnnihilation (E := E))
        (cliffordConcreteCreation (E := E))).toLinearMap := by
          exact triality_anticommutator_eq_cliffordConcrete_anticommutator (E := E)

/--
Reusing the concrete CAR witness already proved in `BogoliubovFockSuper`, the
canonical triality supercharge square closes onto the identity even seed.
-/
@[simp] theorem trialitySupercharge_square_eq_id_via_cliffordConcreteCAR :
    (canonicalSplitTrialityKernel (E := E)).trialitySupercharge.comp
        (canonicalSplitTrialityKernel (E := E)).trialitySupercharge
      =
    LinearMap.id := by
  rcases cliffordConcreteIsCARPair (E := E) with ⟨_, _, hMixed⟩
  calc
    (canonicalSplitTrialityKernel (E := E)).trialitySupercharge.comp
        (canonicalSplitTrialityKernel (E := E)).trialitySupercharge
        =
      (fockAnticommutator (E := E)
        (cliffordConcreteAnnihilation (E := E))
        (cliffordConcreteCreation (E := E))).toLinearMap := by
          exact trialitySupercharge_square_eq_cliffordConcrete_anticommutator (E := E)
    _ = LinearMap.id := by
          exact congrArg ContinuousLinearMap.toLinearMap hMixed

end InfoGeometry.Quantum.SplitTrialityFockBridge
