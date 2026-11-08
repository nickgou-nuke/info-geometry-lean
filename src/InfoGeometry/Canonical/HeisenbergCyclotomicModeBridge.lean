import InfoGeometry.External.Virasoro.HeisenbergModeFlip
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Cyclotomic mode readout for the Heisenberg extension

Heisenberg resonance is indexed by `k + l = 0`, while the chiral colour
calculus is naturally indexed by `ZMod 3`.  This owner records the common
arithmetic skeleton and the interaction with the already-proved orientation
reversal.  It does not identify the Heisenberg Lie algebra with a Zorn or
q-CCR algebra.
-/

namespace InfoGeometry.Canonical

open VirasoroProject

/-- The order-three degree of an integer-labelled current mode. -/
def heisenbergModeDegree (k : ℤ) : ZMod 3 := k

@[simp] theorem heisenbergModeDegree_add (k l : ℤ) :
    heisenbergModeDegree (k + l) =
      heisenbergModeDegree k + heisenbergModeDegree l := by
  simp [heisenbergModeDegree]

@[simp] theorem heisenbergModeDegree_neg (k : ℤ) :
    heisenbergModeDegree (-k) = -heisenbergModeDegree k := by
  simp [heisenbergModeDegree]

theorem heisenberg_resonance_has_zero_cyclotomic_degree
    (k l : ℤ) (h : k + l = 0) :
    heisenbergModeDegree k + heisenbergModeDegree l = 0 := by
  calc
    heisenbergModeDegree k + heisenbergModeDegree l =
        heisenbergModeDegree (k + l) := by simp
    _ = 0 := by
      simpa [heisenbergModeDegree] using
        congrArg (fun n : ℤ => (n : ZMod 3)) h

theorem heisenberg_mode_flip_inverts_cyclotomic_degree (k : ℤ) :
    heisenbergModeDegree (-k) = -heisenbergModeDegree k := by
  exact heisenbergModeDegree_neg k

theorem heisenberg_mode_flip_cocycle_sign
    {𝕜 : Type*} [Field 𝕜]
    (k l : ℤ) :
    VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (VirasoroProject.AbelianLieAlgebraOn.modeFlip 𝕜
          (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 k))
        (VirasoroProject.AbelianLieAlgebraOn.modeFlip 𝕜
          (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 l)) =
      -VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 k)
        (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 l) := by
  exact VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycle_modeFlip_jgen_jgen
    𝕜 k l

end InfoGeometry.Canonical
