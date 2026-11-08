import InfoGeometry.Canonical.ZornFiniteVectorCalculus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Hodge/Helmholtz readout for the finite Zorn vector calculus

This owner separates the algebraic identities available from the differential
carrier from the analytic existence/uniqueness theorem usually called the
Helmholtz decomposition.  The exact channel is a gradient, the coexact
channel is a curl, and the harmonic remainder is explicitly divergence-free
and curl-free.
-/

namespace InfoGeometry.Canonical.ZornHodgeHelmholtzBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.Canonical.ZornFiniteVectorCalculus
open InfoGeometry.Canonical.ZornPotentialDifferentialReadout

variable {R : Type*} [CommRing R]

local notation "Vec3" => ZornVec3 R

def exactVectorPart (D : DifferentialCarrier (R := R)) (potential : R) : Vec3 :=
  gradient D potential

def coexactVectorPart (D : DifferentialCarrier (R := R)) (potential : Vec3) : Vec3 :=
  curl D potential

def IsHarmonicVector (D : DifferentialCarrier (R := R)) (v : Vec3) : Prop :=
  divergence D v = 0 ∧ curl D v = fun _ => 0

def IsHelmholtzDecomposition
    (D : DifferentialCarrier (R := R)) (v : Vec3)
    (potential : R) (coPotential harmonic : Vec3) : Prop :=
  v = exactVectorPart D potential + coexactVectorPart D coPotential + harmonic ∧
    IsHarmonicVector D harmonic

theorem exactVectorPart_is_coclosed
    (D : DifferentialCarrier (R := R)) (potential : R) :
    curl D (exactVectorPart D potential) = fun _ => 0 := by
  exact curl_gradient D potential

theorem coexactVectorPart_is_divergence_free
    (D : DifferentialCarrier (R := R)) (coPotential : Vec3) :
    divergence D (coexactVectorPart D coPotential) = 0 := by
  exact divergence_curl D coPotential

theorem helmholtz_decomposition_readout
    (D : DifferentialCarrier (R := R)) (v : Vec3)
    (potential : R) (coPotential harmonic : Vec3)
    (h : IsHelmholtzDecomposition D v potential coPotential harmonic) :
    v = gradient D potential + curl D coPotential + harmonic ∧
      divergence D harmonic = 0 ∧ curl D harmonic = fun _ => 0 := by
  rcases h with ⟨hv, hh⟩
  exact ⟨hv, hh⟩

theorem helmholtz_exact_coexact_channels_vanish
    (D : DifferentialCarrier (R := R)) (potential : R) (coPotential : Vec3) :
    curl D (exactVectorPart D potential) = (fun _ => 0) ∧
      divergence D (coexactVectorPart D coPotential) = 0 := by
  exact ⟨exactVectorPart_is_coclosed D potential,
    coexactVectorPart_is_divergence_free D coPotential⟩

/-! A spatial vector potential can carry the exact/coexact/harmonic split. -/
def IsVectorPotentialHodgeDecomposition
    (D : DifferentialCarrier (R := R)) (vectorPotential : Vec3)
    (gaugePotential : R) (coPotential harmonic : Vec3) : Prop :=
  vectorPotential = gradient D gaugePotential + curl D coPotential + harmonic ∧
    IsHarmonicVector D harmonic

theorem scalarPotential_exact_channel
    (D : DifferentialCarrier (R := R)) (scalar : R) :
    exactVectorPart D scalar = gradient D scalar :=
  rfl

theorem potentialData_scalarGradient_eq_exact
    (D : DifferentialCarrier (R := R)) (scalar : R) (vector : Vec3) :
    (potentialData D scalar vector).scalarGradient = exactVectorPart D scalar :=
  rfl

theorem potentialData_magneticReadout_eq_coexact
    (D : DifferentialCarrier (R := R)) (scalar : R) (vector : Vec3) :
    magneticReadout (potentialData D scalar vector) =
      coexactVectorPart D vector :=
  rfl

theorem magneticReadout_of_vectorPotential_decomposition
    (D : DifferentialCarrier (R := R)) (scalar : R) (vector : Vec3)
    (gaugePotential : R) (coPotential harmonic : Vec3)
    (h : IsVectorPotentialHodgeDecomposition D vector gaugePotential
      coPotential harmonic) :
    magneticReadout (potentialData D scalar vector) =
      curl D (curl D coPotential) := by
  rcases h with ⟨hv, hh⟩
  rw [potentialData_magneticReadout_eq_coexact]
  rw [hv]
  have hcurl_add (x y : Vec3) :
      curl D (x + y) = curl D x + curl D y := by
    funext i
    fin_cases i <;> simp [curl, D.spatial_add] <;> ring_nf
  calc
    curl D (gradient D gaugePotential + curl D coPotential + harmonic) =
        curl D (gradient D gaugePotential) +
          curl D (curl D coPotential) + curl D harmonic := by
      rw [hcurl_add, hcurl_add]
    _ = curl D (curl D coPotential) := by
      rw [curl_gradient D gaugePotential, hh.2]
      funext i
      simp only [Pi.add_apply, zero_add, add_zero]

theorem electricReadout_of_potentialData
    (D : DifferentialCarrier (R := R)) (scalar : R) (vector : Vec3) :
    electricReadout (potentialData D scalar vector) =
      fun i => -(gradient D scalar i + D.timeDerivative (vector i)) :=
  rfl

end InfoGeometry.Canonical.ZornHodgeHelmholtzBridge
