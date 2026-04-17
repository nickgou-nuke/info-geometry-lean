import InfoGeometry.Canonical.KKTCore
import InfoGeometry.Canonical.Cl11LorentzAction
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.WindingOrbitClosure

Formalization of the topological winding number $N$ in the $Cl(1,1)$ operator algebra.

This module implements the Drazin-branch covering map for the modular generator,
grounding the $2\pi N$ periodicity of the modular clock entirely within the
real geometric domain.

The clock tick $N$ represents the winding around the modular singularity,
mapping to the Drazin index of the operator flow.
-/

namespace InfoGeometry.Canonical.WindingOrbitClosure

open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Canonical.Cl11LorentzAction
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Quantum

section Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => DoubledSpace H →L[ℝ] DoubledSpace H

/--
The topological clock generator (unit bivector axis for rotation).
This is the $J\epsilon$ axis, acting as the "Complex I" mask in the real domain.
-/
@[rep_depth transport]
noncomputable def clockAxis (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  modularComplexI (E := E)

/--
The multi-branched modular generator (The Drazin-Branch Covering Map).

$K_N = K_{principal} + 2\pi N J \epsilon$

Where:
- `K_principal` is the base modular Hamiltonian (regular core).
- `N` is the Winding Number (Clock Tick).
-/
@[rep_depth transport]
noncomputable def multiBranchedGenerator (K : EndH) (N : ℤ) : EndH :=
  K + (2 * Real.pi * (N : ℝ)) • clockAxis H

/--
The topo-shift between adjacent winding branches.
-/
@[rep_depth transport]
noncomputable def topoShift (N : ℤ) : EndH :=
  (2 * Real.pi * (N : ℝ)) • clockAxis H

/--
The topo-shift commutes with the base generator if the generator is grade-neutral
or commutes with the clock axis.
-/
theorem topoShift_commute_base
    (K : EndH) (N : ℤ)
    (hComm : Commute K (clockAxis H)) :
    Commute K (topoShift H N) := by
  unfold topoShift
  exact hComm.smul_right (2 * Real.pi * (N : ℝ))

/--
The discrete topo-shift between winding branches $N$ and $N+1$ is additive.
-/
theorem multiBranchedGenerator_shift
    (K : EndH) (N : ℤ) :
    multiBranchedGenerator H K (N + 1) =
      multiBranchedGenerator H K N + (2 * Real.pi) • clockAxis H := by
  unfold multiBranchedGenerator
  simp [topoShift, add_smul, mul_add, add_assoc]
  congr 1
  rw [← add_smul]
  congr
  norm_cast

/--
Winding branches commute with each other.
-/
theorem multiBranchedGenerator_commute
    (K : EndH) (N M : ℤ)
    (hComm : Commute K (clockAxis H)) :
    Commute (multiBranchedGenerator H K N) (multiBranchedGenerator H K M) := by
  unfold multiBranchedGenerator
  apply Commute.add_left
  · apply Commute.add_right
    · exact Commute.refl K
    · exact (hComm.smul_right _).symm
  · apply Commute.add_right
    · exact hComm.smul_left _
    · apply Commute.smul_left
      apply Commute.smul_right
      exact Commute.refl (clockAxis H)

/--
The $2\pi$ modular rotation orbit identity.
In the real doubled representation, the rotation $e^{2\pi J\epsilon}$ resolves
to the identity on the state manifold.
-/
theorem modular_rotation_identity :
    NormedSpace.exp ((2 * Real.pi) • clockAxis H) = (1 : EndH) := by
  -- This requires the exponential form of the complex structure Jε.
  -- In TomitaTakesaki, modularComplexI_sq = -Id.
  -- exp(θ Jε) = cos(θ) Id + sin(θ) Jε.
  have hSq : (clockAxis H).comp (clockAxis H) = -(ContinuousLinearMap.id ℝ (DoubledSpace H)) :=
    modularComplexI_sq (E := H)
  have hExp := InfoGeometry.Canonical.BogoliubovClosedForms.exp_eq_cos_add_sin_of_sq_eq_neg_one
    (E := DoubledSpace H) (G := clockAxis H) hSq (2 * Real.pi)
  simp [hExp]
  -- cos(2π) = 1, sin(2π) = 0
  rw [Real.cos_two_pi, Real.sin_two_pi]
  simp

/--
The Winding Number $N$ acts as a discrete shift that leaves the exponential
transport invariant (The Periodic Closure).
-/
theorem winding_orbit_periodicity (K : EndH) (N : ℤ)
    (hComm : Commute K (clockAxis H)) :
    NormedSpace.exp (multiBranchedGenerator H K N) =
      NormedSpace.exp K := by
  unfold multiBranchedGenerator
  rw [NormedSpace.exp_add_of_commute (hComm.smul_right _)]
  -- exp(2πN Jε) = (exp(2π Jε))^N
  -- Since exp(2π Jε) = Id, Id^N = Id.
  have hBase := modular_rotation_identity H
  have hPower : NormedSpace.exp ((2 * Real.pi * (N : ℝ)) • clockAxis H) = 1 := by
    -- For integer N, exp(N * A) = (exp A)^N
    -- Since exp((2π) * Jε) = 1, any integer power is 1.
    -- We can prove this by induction or using the cos/sin form.
    have hSq : (clockAxis H).comp (clockAxis H) = -(ContinuousLinearMap.id ℝ (DoubledSpace H)) :=
      modularComplexI_sq (E := H)
    have hExp := InfoGeometry.Canonical.BogoliubovClosedForms.exp_eq_cos_add_sin_of_sq_eq_neg_one
      (E := DoubledSpace H) (G := clockAxis H) hSq (2 * Real.pi * (N : ℝ))
    simp [hExp]
    rw [Real.cos_int_mul_two_pi, Real.sin_int_mul_two_pi]
    simp
  rw [hPower]
  simp

end Core

end InfoGeometry.Canonical.WindingOrbitClosure
