import InfoGeometry.OperatorAlgebra.SuperchargeNilpotence
import InfoGeometry.Algebraic.JordanCliffordLieSplit
import InfoGeometry.Algebra.JordanTripleTKK
import InfoGeometry.Algebra.NonAssocDerivation
import Mathlib.Tactic.NoncommRing

/-!
# Finite Schwinger--Cartan owner

This file is deliberately finite and algebraic.  It does not introduce a
differential graded algebra, a modular logarithm, or an analytic source
functional.  It records the concrete Clifford realization already owned by
`SuperchargeNilpotence` in the operator/scalar-potential notation used by the
finite Schwinger--Cartan layer.
-/

namespace InfoGeometry.Canonical.SchwingerCartanFiniteOwner

open InfoGeometry.OperatorAlgebra.CliffordCAR
open InfoGeometry.OperatorAlgebra.SuperchargeNilpotence
open InfoGeometry.Algebraic.SplitSignature

noncomputable section

/-- The finite operator potential is the concrete odd-plus-adjoint supercharge. -/
def operatorPotential (n : ℕ) (w : Fin n → ℝ) : Clnn n :=
  D n w

/-- The finite scalar potential is the concrete odd--odd anticommutator. -/
def scalarPotential (n : ℕ) (w : Fin n → ℝ) : Clnn n :=
  H n w

theorem operatorPotential_sq_eq_scalarPotential
    (n : ℕ) (w : Fin n → ℝ) :
    operatorPotential n w * operatorPotential n w = scalarPotential n w := by
  exact D_sq_eq_H n w

theorem scalarPotential_eq_weighted_scalar
    (n : ℕ) (w : Fin n → ℝ) :
    scalarPotential n w = s n (∑ i : Fin n, w i * w i) := by
  exact H_eq_sum_squares n w

theorem scalarPotential_mul_eq_mul_scalarPotential
    (n : ℕ) (w : Fin n → ℝ) (x : Clnn n) :
    scalarPotential n w * x = x * scalarPotential n w := by
  rw [scalarPotential_eq_weighted_scalar n w]
  exact Algebra.commutes (∑ i : Fin n, w i * w i) x

theorem operatorPotential_sq_commutes
    (n : ℕ) (w : Fin n → ℝ) (x : Clnn n) :
    (operatorPotential n w * operatorPotential n w) * x =
      x * (operatorPotential n w * operatorPotential n w) := by
  rw [operatorPotential_sq_eq_scalarPotential n w]
  exact scalarPotential_mul_eq_mul_scalarPotential n w x

/--
The complete finite readout: the square of the operator potential is the
Clifford scalar determined by the sum of the mode weights squared.
-/
theorem operatorPotential_sq_eq_weighted_scalar
    (n : ℕ) (w : Fin n → ℝ) :
    operatorPotential n w * operatorPotential n w =
      s n (∑ i : Fin n, w i * w i) := by
  calc
    operatorPotential n w * operatorPotential n w = scalarPotential n w :=
      operatorPotential_sq_eq_scalarPotential n w
    _ = s n (∑ i : Fin n, w i * w i) :=
      scalarPotential_eq_weighted_scalar n w

/-! ## Jordan--Lie split of the finite operator potential -/

/-- The self-Jordan channel of the finite operator potential. -/
noncomputable def operatorJordanChannel (n : ℕ) (w : Fin n → ℝ) : Clnn n :=
  InfoGeometry.Algebraic.jordanProduct (operatorPotential n w) (operatorPotential n w)

/-- The self-Lie channel of the finite operator potential. -/
noncomputable def operatorLieChannel (n : ℕ) (w : Fin n → ℝ) : Clnn n :=
  InfoGeometry.Algebraic.lieBracket (operatorPotential n w) (operatorPotential n w)

theorem operatorLieChannel_eq_zero
    (n : ℕ) (w : Fin n → ℝ) :
    operatorLieChannel n w = 0 := by
  unfold operatorLieChannel InfoGeometry.Algebraic.lieBracket
  simp

theorem operatorPotential_sq_eq_jordanChannel
    (n : ℕ) (w : Fin n → ℝ) :
    operatorPotential n w * operatorPotential n w = operatorJordanChannel n w := by
  have hsplit :=
    InfoGeometry.Algebraic.jordan_lie_split
      (operatorPotential n w) (operatorPotential n w)
  simpa [operatorJordanChannel, InfoGeometry.Algebraic.jordanProduct,
    InfoGeometry.Algebraic.lieBracket, sub_self, smul_zero, add_zero,
    smul_add, add_assoc, add_comm, add_left_comm] using hsplit

/-! ## Associative Jordan triple product -/

/-- The standard associative-algebra Jordan triple product on `Clnn`. -/
def jordanTriple (n : ℕ) (x y z : Clnn n) : Clnn n :=
  (x * y) * z + (z * y) * x

theorem jordanTriple_identity
    (n : ℕ) (x y u v w : Clnn n) :
    jordanTriple n x y (jordanTriple n u v w) -
        jordanTriple n u v (jordanTriple n x y w) =
      jordanTriple n (jordanTriple n x y u) v w -
        jordanTriple n u (jordanTriple n y x v) w := by
  simp only [jordanTriple]
  noncomm_ring

/-- The finite `Clnn` carrier equipped with its associative Jordan triple law. -/
def clnnJordanTripleSystem (n : ℕ) :
    InfoGeometry.Algebra.TKK.JordanTripleSystem (Clnn n) where
  tripleProduct := jordanTriple n
  jordan_identity := jordanTriple_identity n

@[simp] theorem clnnJordanTripleSystem_tripleProduct
    (n : ℕ) (x y z : Clnn n) :
    (clnnJordanTripleSystem n).tripleProduct x y z = jordanTriple n x y z := rfl

/-- The inner commutator derivation on the finite Clifford carrier. -/
def innerDerivation (n : ℕ) (K x : Clnn n) : Clnn n :=
  K * x - x * K

theorem innerDerivation_scalarPotential_eq_zero
    (n : ℕ) (w : Fin n → ℝ) (x : Clnn n) :
    innerDerivation n (scalarPotential n w) x = 0 := by
  unfold innerDerivation
  rw [scalarPotential_mul_eq_mul_scalarPotential n w x]
  simp

theorem innerDerivation_operatorPotential_sq_eq_zero
    (n : ℕ) (w : Fin n → ℝ) (x : Clnn n) :
    innerDerivation n (operatorPotential n w * operatorPotential n w) x = 0 := by
  rw [operatorPotential_sq_eq_scalarPotential n w]
  exact innerDerivation_scalarPotential_eq_zero n w x

theorem innerDerivation_mul
    (n : ℕ) (K x y : Clnn n) :
    innerDerivation n K (x * y) =
      innerDerivation n K x * y + x * innerDerivation n K y := by
  simp only [innerDerivation]
  noncomm_ring

/-- The inner commutator as a genuine real-linear endomorphism of `Clnn n`. -/
def innerDerivationLinear (n : ℕ) (K : Clnn n) : Module.End ℝ (Clnn n) where
  toFun x := innerDerivation n K x
  map_add' x y := by
    simp only [innerDerivation, mul_add, add_mul]
    noncomm_ring
  map_smul' c x := by
    simp only [innerDerivation, Algebra.smul_def]
    have hK : K * (algebraMap ℝ (Clnn n)) c =
        (algebraMap ℝ (Clnn n)) c * K :=
      (Algebra.commutes c K).symm
    calc
      K * ((algebraMap ℝ (Clnn n)) c * x) -
          (algebraMap ℝ (Clnn n)) c * x * K
          = (K * (algebraMap ℝ (Clnn n)) c) * x -
              (algebraMap ℝ (Clnn n)) c * (x * K) := by
                rw [mul_assoc, mul_assoc]
      _ = ((algebraMap ℝ (Clnn n)) c * K) * x -
            (algebraMap ℝ (Clnn n)) c * (x * K) := by rw [hK]
      _ = (algebraMap ℝ (Clnn n)) c * (K * x - x * K) := by
            noncomm_ring

@[simp] theorem innerDerivationLinear_apply
    (n : ℕ) (K x : Clnn n) :
    innerDerivationLinear n K x = innerDerivation n K x := rfl

theorem innerDerivationLinear_isLeibniz
    (n : ℕ) (K : Clnn n) :
    InfoGeometry.Algebra.NonAssocDerivation.IsLeibniz ℝ (Clnn n)
      (innerDerivationLinear n K) := by
  intro x y
  exact innerDerivation_mul n K x y

/-- Inner derivation bundled as a Lie-suitable derivation. -/
def innerDerivationBundled (n : ℕ) (K : Clnn n) :
    InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ (Clnn n) :=
  ⟨innerDerivationLinear n K, innerDerivationLinear_isLeibniz n K⟩

theorem innerDerivation_commutator_closure
    (n : ℕ) (K L x : Clnn n) :
    innerDerivation n K (innerDerivation n L x) -
        innerDerivation n L (innerDerivation n K x) =
      innerDerivation n (K * L - L * K) x := by
  unfold innerDerivation
  noncomm_ring

  
theorem innerDerivationBundled_lie_commutator
    (n : ℕ) (K L x : Clnn n) :
    (((⁅innerDerivationBundled n K, innerDerivationBundled n L⁆ :
          InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ (Clnn n)) :
            Module.End ℝ (Clnn n)) x) =
      innerDerivation n (K * L - L * K) x := by
  change
    innerDerivation n K (innerDerivation n L x) -
      innerDerivation n L (innerDerivation n K x) =
      innerDerivation n (K * L - L * K) x
  exact innerDerivation_commutator_closure n K L x

theorem innerDerivationBundled_lie_commutator_eq
    (n : ℕ) (K L : Clnn n) :
    ⁅innerDerivationBundled n K, innerDerivationBundled n L⁆ =
      innerDerivationBundled n (K * L - L * K) := by
  ext x
  change
    (((⁅innerDerivationBundled n K, innerDerivationBundled n L⁆ :
          InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ (Clnn n)) :
            Module.End ℝ (Clnn n)) x) =
      innerDerivation n (K * L - L * K) x
  exact innerDerivationBundled_lie_commutator n K L x

theorem innerDerivationBundled_scalarPotential_eq_zero
    (n : ℕ) (w : Fin n → ℝ) :
    innerDerivationBundled n (scalarPotential n w) = 0 := by
  ext x
  exact innerDerivation_scalarPotential_eq_zero n w x

theorem innerDerivationBundled_operatorPotential_sq_eq_zero
    (n : ℕ) (w : Fin n → ℝ) :
    innerDerivationBundled n (operatorPotential n w * operatorPotential n w) = 0 := by
  ext x
  exact innerDerivation_operatorPotential_sq_eq_zero n w x

theorem innerDerivationBundled_lie_commutator_scalarPotential_eq_zero
    (n : ℕ) (K : Clnn n) (w : Fin n → ℝ) :
    ⁅innerDerivationBundled n K, innerDerivationBundled n (scalarPotential n w)⁆ = 0 := by
  rw [innerDerivationBundled_lie_commutator_eq]
  have hcomm : K * scalarPotential n w - scalarPotential n w * K = (0 : Clnn n) := by
    calc
      K * scalarPotential n w - scalarPotential n w * K
          = K * scalarPotential n w - K * scalarPotential n w := by
              rw [← scalarPotential_mul_eq_mul_scalarPotential n w K]
      _ = 0 := sub_self _
  rw [hcomm]
  ext x
  simp [innerDerivationBundled, innerDerivation]

theorem innerDerivation_eq_zero_of_commutes_all
    (n : ℕ) (K : Clnn n) (hK : ∀ x : Clnn n, K * x = x * K) :
    innerDerivationBundled n K = 0 := by
  ext x
  simp [innerDerivationBundled, innerDerivation, hK x]

theorem innerDerivationBundled_lie_commutator_eq_zero_of_commutes_all
    (n : ℕ) (K L : Clnn n) (hL : ∀ x : Clnn n, L * x = x * L) :
    ⁅innerDerivationBundled n K, innerDerivationBundled n L⁆ = 0 := by
  have hcomm : K * L - L * K = (0 : Clnn n) := by
    calc
      K * L - L * K = K * L - K * L := by rw [hL K]
      _ = 0 := sub_self _
  rw [innerDerivationBundled_lie_commutator_eq, hcomm]
  ext x
  simp [innerDerivationBundled, innerDerivation]

theorem innerDerivationBundled_jordanTriple_eq_zero_of_commutes
    (n : ℕ) (K x y z : Clnn n) (hK : ∀ x : Clnn n, K * x = x * K) :
    innerDerivation n K (jordanTriple n x y z) = 0 := by
  have hKxyz : K * (x * y * z + z * y * x) = (x * y * z + z * y * x) * K := by
    simpa [mul_add, mul_assoc] using hK (x * y * z + z * y * x)
  calc
    innerDerivation n K (jordanTriple n x y z)
        = K * (x * y * z + z * y * x) - (x * y * z + z * y * x) * K := by
          rfl
    _ = (x * y * z + z * y * x) * K - (x * y * z + z * y * x) * K := by rw [hKxyz]
    _ = 0 := by simp

theorem innerDerivation_jordanTriple
    (n : ℕ) (K x y z : Clnn n) :
    innerDerivation n K (jordanTriple n x y z) =
      jordanTriple n (innerDerivation n K x) y z +
        jordanTriple n x (innerDerivation n K y) z +
          jordanTriple n x y (innerDerivation n K z) := by
  simp only [innerDerivation, jordanTriple]
  noncomm_ring

end

end InfoGeometry.Canonical.SchwingerCartanFiniteOwner
