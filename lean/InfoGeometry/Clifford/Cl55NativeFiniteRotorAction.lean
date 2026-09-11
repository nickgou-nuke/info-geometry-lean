import InfoGeometry.Clifford.Cl55FiniteCommutingRotorAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55RoPESplitTorusBridge
import InfoGeometry.Clifford.Cl55RotorUnitsRepresentation

/-! Native specialization of the generic rank-two rotor closure.

The statement is intentionally finite and concrete: it packages the already
proved disjoint planes `(0,1)` and `(2,3)`, without asserting maximality. -/

noncomputable section

namespace InfoGeometry.Clifford.Cl55NativeFiniteRotorAction

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55RoPESplitTorusBridge
open InfoGeometry.Clifford.FiniteCommutingRotorAction
open InfoGeometry.Clifford.Cl55RotorUnitsRepresentation

def nativeRankTwoRotor (s t : ℝ) : Cl55 :=
  bivectorRotor55 0 1 s * bivectorRotor55 2 3 t

def nativeRankTwoRotorUnit (s t : ℝ) : Cl55ˣ where
  val := nativeRankTwoRotor s t
  inv := nativeRankTwoRotor (-s) (-t)
  val_inv := by
    exact rankTwoRotor_inverse
      (ropeBivector55 0 1) (ropeBivector55 2 3)
      (ropeBivector55_sq 0 1 (by decide))
      (ropeBivector55_sq 2 3 (by decide))
      disjoint_bivector_commute_01_23 s t
  inv_val := by
    simpa only [neg_neg] using (rankTwoRotor_inverse
      (ropeBivector55 0 1) (ropeBivector55 2 3)
      (ropeBivector55_sq 0 1 (by decide))
      (ropeBivector55_sq 2 3 (by decide))
      disjoint_bivector_commute_01_23 (-s) (-t))

def nativeBivectorRotorUnits (theta0 : ℝ) : Multiplicative ℤ →* Cl55ˣ :=
  discreteRotorUnitsHom (ropeBivector55 0 1)
    (ropeBivector55_sq 0 1 (by decide)) theta0

theorem nativeBivectorRotorUnits_map_mul (theta0 : ℝ)
    (m n : Multiplicative ℤ) :
    nativeBivectorRotorUnits theta0 (m * n) =
      nativeBivectorRotorUnits theta0 m * nativeBivectorRotorUnits theta0 n := by
  exact map_mul (nativeBivectorRotorUnits theta0) m n

theorem nativeBivectorRotorUnits_map_one (theta0 : ℝ) :
    nativeBivectorRotorUnits theta0 1 = 1 := by
  exact map_one (nativeBivectorRotorUnits theta0)

theorem nativeRankTwoRotor_add (s₁ s₂ t₁ t₂ : ℝ) :
    nativeRankTwoRotor (s₁ + s₂) (t₁ + t₂) =
      nativeRankTwoRotor s₁ t₁ * nativeRankTwoRotor s₂ t₂ := by
  unfold nativeRankTwoRotor
  simpa [bivectorRotor55, rankTwoRotor, rotor] using
    (rankTwoRotor_add
      (ropeBivector55 0 1) (ropeBivector55 2 3)
      (ropeBivector55_sq 0 1 (by decide))
      (ropeBivector55_sq 2 3 (by decide))
      disjoint_bivector_commute_01_23 s₁ s₂ t₁ t₂)

theorem nativeRankTwoRotorUnit_add (s₁ s₂ t₁ t₂ : ℝ) :
    nativeRankTwoRotorUnit (s₁ + s₂) (t₁ + t₂) =
      nativeRankTwoRotorUnit s₁ t₁ * nativeRankTwoRotorUnit s₂ t₂ := by
  apply Units.ext
  exact nativeRankTwoRotor_add s₁ s₂ t₁ t₂

theorem nativeRankTwoRotor_relative (s t u v : ℝ) :
    nativeRankTwoRotor (-s) (-t) * nativeRankTwoRotor u v =
      nativeRankTwoRotor (u - s) (v - t) := by
  unfold nativeRankTwoRotor
  simpa [bivectorRotor55, rankTwoRotor, rotor] using
    (rankTwoRotor_relative
      (ropeBivector55 0 1) (ropeBivector55 2 3)
      (ropeBivector55_sq 0 1 (by decide))
      (ropeBivector55_sq 2 3 (by decide))
      disjoint_bivector_commute_01_23 s t u v)

theorem nativeRankTwoRotorUnit_relative (s t u v : ℝ) :
    nativeRankTwoRotorUnit (-s) (-t) * nativeRankTwoRotorUnit u v =
      nativeRankTwoRotorUnit (u - s) (v - t) := by
  apply Units.ext
  exact nativeRankTwoRotor_relative s t u v

end InfoGeometry.Clifford.Cl55NativeFiniteRotorAction
