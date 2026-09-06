import InfoGeometry.Canonical.SplitOctonionBogoliubovGeneratorBridge

/-!
# Multiplicative packaging of the represented hyperbolic flow

For a supplied split-octonion representation and a unit hyperbolic direction,
the already-proved propagator identities package as a homomorphism from the
additive rapidity line (via `Multiplicative`) to units of the represented
endomorphism algebra.
-/

namespace InfoGeometry.Canonical

open BogoliubovVielbein
open InfoGeometry.Krein

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

local notation "EndH" => DoubledSpace E →L[ℝ] DoubledSpace E

namespace SplitOctonionBoostRepresentation

def propagatorUnit
    {g : Quaternion ℝ} {V : BogoliubovVielbeinBundle (E := E)}
    (R : SplitOctonionBoostRepresentation (E := E) g V)
    (hg : Quaternion.normSq g = 1) (η : ℝ) : EndHˣ :=
  Units.mk (R.propagator η) (R.propagator (-η))
    (by
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun T : EndH => T)
          (R.propagator_inverse hg η).2)
    (by
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun T : EndH => T)
          (R.propagator_inverse hg η).1)

theorem propagatorUnit_zero
    {g : Quaternion ℝ} {V : BogoliubovVielbeinBundle (E := E)}
    (R : SplitOctonionBoostRepresentation (E := E) g V)
    (hg : Quaternion.normSq g = 1) :
    R.propagatorUnit hg 0 = 1 := by
  apply Units.ext
  change R.propagator 0 = (1 : EndH)
  rw [R.propagator_zero]
  apply ContinuousLinearMap.ext
  intro z
  rfl

def propagatorHom
    {g : Quaternion ℝ} {V : BogoliubovVielbeinBundle (E := E)}
    (R : SplitOctonionBoostRepresentation (E := E) g V)
    (hg : Quaternion.normSq g = 1) :
    Multiplicative ℝ →* EndHˣ where
  toFun η := R.propagatorUnit hg η
  map_one' := R.propagatorUnit_zero hg
  map_mul' := by
    intro s t
    apply Units.ext
    simp [propagatorUnit]
    exact (R.propagator_add hg s t).symm

end SplitOctonionBoostRepresentation

end

end InfoGeometry.Canonical
