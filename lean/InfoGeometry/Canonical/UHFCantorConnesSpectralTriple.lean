import Mathlib.Tactic
import InfoGeometry.Canonical.ConnesSpectralTripleBridge

/-!
# Noncommutative Connes distance transport

The former `BitWord`/`DiagAlg` construction supplied a norm as data.  This
owner instead derives the commutator norm from a genuine Dirac element in a
normed noncommutative algebra and proves its transport under an isometric
algebra homomorphism.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFCantorConnesSpectralTriple

open ConnesSpectral
open ConnesSpectral.SpectralTriple

variable {A : Type*} [NormedRing A]

def stageCommutatorNorm (D a : A) : ℝ :=
  ‖D * a - a * D‖

theorem stageCommutatorNorm_nonneg (D a : A) :
    0 ≤ stageCommutatorNorm D a := by
  exact norm_nonneg _

def stageLipschitz (D a : A) : Prop :=
  ConnesSpectral.SpectralTriple.LipschitzFunction D a

def stageConnesDistance (D : A) (p q : A → ℝ) (d : ℝ) : Prop :=
  ConnesSpectral.SpectralTriple.StateDistanceBound D p q d

theorem stageConnesDistance_symm (D : A) (p q : A → ℝ) (d : ℝ)
    (h : stageConnesDistance D p q d) :
    stageConnesDistance D q p d :=
  ConnesSpectral.SpectralTriple.distance_bound_symmetry D p q d h

theorem stageConnesDistance_triangle (D : A) (p q r : A → ℝ) (d1 d2 : ℝ)
    (h1 : stageConnesDistance D p q d1)
    (h2 : stageConnesDistance D q r d2) :
    stageConnesDistance D p r (d1 + d2) :=
  ConnesSpectral.SpectralTriple.distance_bound_triangle D p q r d1 d2 h1 h2

theorem stageCommutatorNorm_map
    {B : Type*} [NormedRing B]
    (φ : A →+* B) (D : A) (E : B)
    (hD : φ D = E)
    (hisom : ∀ x : A, ‖φ x‖ = ‖x‖) (a : A) :
    stageCommutatorNorm E (φ a) = stageCommutatorNorm D a := by
  unfold stageCommutatorNorm
  rw [← hisom (D * a - a * D)]
  congr 1
  simp [hD, map_sub, map_mul]

end InfoGeometry.Canonical.UHFCantorConnesSpectralTriple
