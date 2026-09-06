import Mathlib.Tactic
import InfoGeometry.Canonical.PauliHestenesSpinMomentum
import InfoGeometry.Canonical.BiQuaternionKahlerFinite

/-!
# Quaternionic Pauli--Dirac soldering

This bridge closes the finite operator core shared by the quaternionic,
Pauli, chiral-cone, and Dirac-symbol lanes.

It proves:

* the co-soldered Pauli paravector factorization
  `sigma(P) * barSigma(P) = barSigma(P) * sigma(P) = Q(P) I`;
* the corresponding square law for the chiral Weyl block operator;
* complementary Peirce projectors and circular square-zero intertwiners;
* the quaternion relations after lifting the existing concrete `R^4`
  matrices to genuine real-linear endomorphisms;
* transport of commutation with two quaternionic axes to the third.

No unbounded operator, analytic domain, spin connection, or curved
Lichnerowicz formula is asserted here.
-/

noncomputable section

namespace InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

open Matrix
open scoped Matrix

open InfoGeometry.Canonical.PauliHestenesSpinMomentum

abbrev PauliBlock := Matrix (Fin 2) (Fin 2) ℂ
abbrev WeylSpinor := Fin 2 → ℂ
abbrev DiracSpinor := WeylSpinor × WeylSpinor

/-! ## Pauli soldering and its metric conjugate -/

/-- The metric-conjugate Pauli representative
`barSigma(P) = E I - p_j sigma_j`. -/
def coSolderingMap (P : PauliParavector) : PauliBlock :=
  !![((P.energy - P.pz : ℝ) : ℂ),
      ((-P.px : ℂ) + Complex.I * (P.py : ℂ));
     ((-P.px : ℂ) - Complex.I * (P.py : ℂ)),
      ((P.energy + P.pz : ℝ) : ℂ)]

theorem coSolderingMap_isHermitian (P : PauliParavector) :
    (coSolderingMap P).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coSolderingMap, Matrix.conjTranspose_apply, Complex.conj_I] <;>
    ring

theorem coSolderingMap_det (P : PauliParavector) :
    Matrix.det (coSolderingMap P) = (P.minkowskiNormSq : ℂ) := by
  simp [coSolderingMap, PauliParavector.minkowskiNormSq, Matrix.det_fin_two]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Weyl factorization of the Minkowski quadratic form. -/
theorem soldering_mul_cosoldering (P : PauliParavector) :
    P.pauliMatrix * coSolderingMap P =
      (P.minkowskiNormSq : ℂ) • (1 : PauliBlock) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PauliParavector.pauliMatrix, coSolderingMap,
      PauliParavector.minkowskiNormSq, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_two] <;>
    ring_nf
  all_goals try rw [Complex.I_sq]
  all_goals ring

/-- The reverse Weyl factorization has the same scalar quadratic form. -/
theorem cosoldering_mul_soldering (P : PauliParavector) :
    coSolderingMap P * P.pauliMatrix =
      (P.minkowskiNormSq : ℂ) • (1 : PauliBlock) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PauliParavector.pauliMatrix, coSolderingMap,
      PauliParavector.minkowskiNormSq, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_two] <;>
    ring_nf
  all_goals try rw [Complex.I_sq]
  all_goals ring

/-! ## Chiral Weyl block square -/

/-- Off-diagonal chiral operator with Weyl factors `A` and `B`. -/
def chiralWeylOperator (A B : PauliBlock) : Module.End ℂ DiracSpinor where
  toFun ψ := (A *ᵥ ψ.2, B *ᵥ ψ.1)
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro c x
    ext <;> simp [Matrix.mulVec_smul]

/-- Squaring the off-diagonal operator produces the two ordered diagonal
products. -/
theorem chiralWeylOperator_sq_apply
    (A B : PauliBlock) (ψ : DiracSpinor) :
    chiralWeylOperator A B (chiralWeylOperator A B ψ) =
      ((A * B) *ᵥ ψ.1, (B * A) *ᵥ ψ.2) := by
  rcases ψ with ⟨ψL, ψR⟩
  apply Prod.ext <;>
    simp [chiralWeylOperator, Matrix.mulVec_mulVec]

/-- The soldered chiral Dirac symbol is an exact square root of the
Minkowski quadratic form in the Clifford sense. -/
theorem soldered_chiralWeylOperator_sq_apply
    (P : PauliParavector) (ψ : DiracSpinor) :
    chiralWeylOperator P.pauliMatrix (coSolderingMap P)
        (chiralWeylOperator P.pauliMatrix (coSolderingMap P) ψ) =
      (P.minkowskiNormSq : ℂ) • ψ := by
  rw [chiralWeylOperator_sq_apply]
  rw [soldering_mul_cosoldering, cosoldering_mul_soldering]
  rcases ψ with ⟨ψL, ψR⟩
  ext i <;> simp

/-! ## Peirce/Witt circular decomposition -/

/-- Chiral grading `Gamma^2 = I`. -/
def chirality : PauliBlock := !![(1 : ℂ), 0; 0, -1]

/-- Positive chiral Peirce projector. -/
def chiralPlus : PauliBlock := !![(1 : ℂ), 0; 0, 0]

/-- Negative chiral Peirce projector. -/
def chiralMinus : PauliBlock := !![(0 : ℂ), 0; 0, 1]

/-- Circular raising/Witt generator. -/
def circularPlus : PauliBlock := !![(0 : ℂ), 1; 0, 0]

/-- Circular lowering/Witt generator. -/
def circularMinus : PauliBlock := !![(0 : ℂ), 0; 1, 0]

theorem chirality_sq : chirality * chirality = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chirality, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralPlus_sq : chiralPlus * chiralPlus = chiralPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralMinus_sq : chiralMinus * chiralMinus = chiralMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiral_projectors_complete : chiralPlus + chiralMinus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralPlus, chiralMinus]

theorem chiral_projectors_orthogonal :
    chiralPlus * chiralMinus = 0 ∧ chiralMinus * chiralPlus = 0 := by
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [chiralPlus, chiralMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem circularPlus_sq_zero : circularPlus * circularPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circularPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem circularMinus_sq_zero : circularMinus * circularMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circularMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem circular_car :
    circularPlus * circularMinus + circularMinus * circularPlus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circularPlus, circularMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem circular_peirce_transport :
    chiralPlus * circularPlus * chiralMinus = circularPlus ∧
    chiralMinus * circularMinus * chiralPlus = circularMinus := by
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [chiralPlus, chiralMinus, circularPlus, circularMinus,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem chirality_circular_commutators :
    chirality * circularPlus - circularPlus * chirality =
        (2 : ℂ) • circularPlus ∧
    chirality * circularMinus - circularMinus * chirality =
        (-2 : ℂ) • circularMinus := by
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [chirality, circularPlus, circularMinus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Quaternionic matrices lifted to real-linear operators -/

namespace QuaternionicOperators

open InfoGeometry.Canonical.BiQuaternionKahlerFinite

abbrev Carrier := R4

def I : Module.End ℝ Carrier := I4c.mulVecLin
def J : Module.End ℝ Carrier := J4c.mulVecLin
def K : Module.End ℝ Carrier := K4c.mulVecLin

theorem I_sq : I.comp I = -(LinearMap.id : Module.End ℝ Carrier) := by
  apply LinearMap.ext
  intro x
  change I4c.mulVec (I4c.mulVec x) = -x
  rw [← Matrix.mulVec_mulVec, I4c_sq]
  simp

theorem J_sq : J.comp J = -(LinearMap.id : Module.End ℝ Carrier) := by
  apply LinearMap.ext
  intro x
  change J4c.mulVec (J4c.mulVec x) = -x
  rw [← Matrix.mulVec_mulVec, J4c_sq]
  simp

theorem K_sq : K.comp K = -(LinearMap.id : Module.End ℝ Carrier) := by
  apply LinearMap.ext
  intro x
  change K4c.mulVec (K4c.mulVec x) = -x
  rw [← Matrix.mulVec_mulVec, K4c_sq]
  simp

theorem I_comp_J : I.comp J = K := by
  apply LinearMap.ext
  intro x
  change I4c.mulVec (J4c.mulVec x) = K4c.mulVec x
  rw [← Matrix.mulVec_mulVec, I4c_mul_J4c]

theorem J_comp_I : J.comp I = -K := by
  apply LinearMap.ext
  intro x
  change J4c.mulVec (I4c.mulVec x) = -(K4c.mulVec x)
  rw [← Matrix.mulVec_mulVec, J4c_mul_I4c]
  simp

theorem quaternionic_operator_packet :
    I.comp I = -(LinearMap.id : Module.End ℝ Carrier) ∧
    J.comp J = -(LinearMap.id : Module.End ℝ Carrier) ∧
    K.comp K = -(LinearMap.id : Module.End ℝ Carrier) ∧
    I.comp J = K ∧ J.comp I = -K :=
  ⟨I_sq, J_sq, K_sq, I_comp_J, J_comp_I⟩

end QuaternionicOperators

/-! ## Compatibility with logarithmic/nilpotent endomorphisms -/

/-- Commutation with two quaternionic axes forces commutation with their
product. This is the reusable operator law needed by a LogCFT nilpotent
intertwiner. -/
theorem commute_third_quaternionic_axis
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    {I J K N : Module.End R V}
    (hK : I * J = K)
    (hNI : N * I = I * N)
    (hNJ : N * J = J * N) :
    N * K = K * N := by
  rw [← hK, mul_assoc, hNI, ← mul_assoc, hNJ, mul_assoc]

/-- A square-zero logarithmic endomorphism commuting with `I` and `J`
therefore preserves the complete quaternionic operator triple. -/
theorem squareZero_log_operator_quaternionic_packet
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {I J K N : Module.End R V}
    (hK : I * J = K)
    (hNI : N * I = I * N)
    (hNJ : N * J = J * N)
    (hN2 : N * N = 0) :
    N * N = 0 ∧ N * I = I * N ∧ N * J = J * N ∧ N * K = K * N :=
  ⟨hN2, hNI, hNJ,
    commute_third_quaternionic_axis hK hNI hNJ⟩

/-- Scalar linear combinations of quaternionic axes are preserved by every
endomorphism commuting with the three axes.  The coefficients are base-ring
scalars; operator-valued coefficients require their own commutation
hypotheses. -/
theorem commute_quaternionic_axis_combination
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    {I J K N : Module.End R V}
    (a b c : R)
    (hNI : N * I = I * N)
    (hNJ : N * J = J * N)
    (hNK : N * K = K * N) :
    N * (a • I + b • J + c • K) =
      (a • I + b • J + c • K) * N := by
  calc
    N * (a • I + b • J + c • K) =
        a • (N * I) + b • (N * J) + c • (N * K) := by
          simp [mul_add, mul_smul_comm]
    _ = a • (I * N) + b • (J * N) + c • (K * N) := by
          rw [hNI, hNJ, hNK]
    _ = (a • I + b • J + c • K) * N := by
          simp [add_mul, smul_mul_assoc]

/-- Commutation with two quaternionic generators is sufficient for every
scalar quaternionic axis once `K = I J` is supplied. -/
theorem commute_every_quaternionic_axis_of_two
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    {I J K N : Module.End R V}
    (a b c : R)
    (hK : I * J = K)
    (hNI : N * I = I * N)
    (hNJ : N * J = J * N) :
    N * (a • I + b • J + c • K) =
      (a • I + b • J + c • K) * N := by
  exact commute_quaternionic_axis_combination a b c hNI hNJ
    (commute_third_quaternionic_axis hK hNI hNJ)

/-- Square-zero logarithmic endomorphisms commuting with two axes preserve
every scalar self-dual/quaternionic linear combination.  This is an algebraic
intertwining theorem, not by itself a topological-protection statement. -/
theorem squareZero_log_operator_commutes_every_quaternionic_axis
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {I J K N : Module.End R V}
    (a b c : R)
    (hK : I * J = K)
    (hNI : N * I = I * N)
    (hNJ : N * J = J * N)
    (hN2 : N * N = 0) :
    N * N = 0 ∧
      N * (a • I + b • J + c • K) =
        (a • I + b • J + c • K) * N :=
  ⟨hN2, commute_every_quaternionic_axis_of_two a b c hK hNI hNJ⟩

end InfoGeometry.Bridge.QuaternionicPauliDiracSoldering
