/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealTwistorFockPairing
import Mathlib.Data.Matrix.Mul

/-!
# A real one-excitation sector of polynomial twistor operators

The sector is the actual range of linear polynomials in the existing real
polynomial representation. Its projector extracts the degree-one coefficients.
Number-conserving bilinears intertwine exactly with finite configuration
operators. Individual creation and annihilation operators are not restricted
to this sector, and no finite-dimensional CCR are asserted.

The auxiliary polynomial degree is not identified with nuclear particle
number, spatial parity, angular momentum, isospin, or physical helicity.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealPolynomialCCR

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Native extraction of the degree-one coefficients. -/
def oneParticleCoeff : WavePolynomial ι →ₗ[ℝ] Coordinates ι where
  toFun p i := p.coeff (Finsupp.single i 1)
  map_add' p q := by ext i; simp
  map_smul' c p := by ext i; simp

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem oneParticleCoeff_apply (p : WavePolynomial ι) (i : ι) :
    oneParticleCoeff p i = p.coeff (Finsupp.single i 1) := rfl

/-- The existing linear polynomial construction as a native linear map. -/
def linearFormMap : Coordinates ι →ₗ[ℝ] WavePolynomial ι where
  toFun := linearForm
  map_add' := linearForm_add
  map_smul' := linearForm_smul

omit [DecidableEq ι] in
@[simp] theorem linearFormMap_apply (a : Coordinates ι) :
    linearFormMap a = linearForm a := rfl

@[simp] theorem linearForm_single (i : ι) :
    linearForm (Pi.single i 1 : Coordinates ι) = MvPolynomial.X i := by
  simp [linearForm, Pi.single_apply]

@[simp] theorem oneParticleCoeff_linearForm (a : Coordinates ι) :
    oneParticleCoeff (linearForm a) = a := by
  ext i
  simp [linearForm]

theorem linearForm_injective : Function.Injective (linearForm (ι := ι)) := by
  intro a b h
  have hc := congrArg (oneParticleCoeff (ι := ι)) h
  simpa only [oneParticleCoeff_linearForm] using hc

/-- The one-excitation sector as an actual polynomial submodule. -/
def oneParticleSector : Submodule ℝ (WavePolynomial ι) :=
  LinearMap.range linearFormMap

/-- The coefficient projector, acting on all polynomial wavefunctions. -/
def oneParticleProjector : Operator ι := linearFormMap.comp oneParticleCoeff

omit [DecidableEq ι] in
@[simp] theorem oneParticleProjector_apply (p : WavePolynomial ι) :
    oneParticleProjector p = linearForm (oneParticleCoeff p) := rfl

@[simp] theorem oneParticleProjector_linearForm (a : Coordinates ι) :
    oneParticleProjector (linearForm a) = linearForm a := by simp

@[simp] theorem oneParticleProjector_idempotent :
    oneParticleProjector (ι := ι) * oneParticleProjector = oneParticleProjector := by
  apply LinearMap.ext
  intro p
  simp only [Module.End.mul_apply, oneParticleProjector_apply,
    oneParticleCoeff_linearForm]

theorem mem_oneParticleSector_iff (p : WavePolynomial ι) :
    p ∈ oneParticleSector ↔ oneParticleProjector p = p := by
  constructor
  · rintro ⟨a, rfl⟩
    exact oneParticleProjector_linearForm a
  · intro hp
    exact ⟨oneParticleCoeff p, hp⟩

@[simp] theorem oneParticleProjector_X (i : ι) :
    oneParticleProjector (MvPolynomial.X i) = MvPolynomial.X i := by
  rw [← linearForm_single i, oneParticleProjector_linearForm]

omit [Fintype ι] in
@[simp] theorem oneParticleCoeff_vacuum :
    oneParticleCoeff (1 : WavePolynomial ι) = 0 := by
  ext i
  simp [MvPolynomial.coeff_one, eq_comm]

@[simp] theorem oneParticleProjector_vacuum :
    oneParticleProjector (1 : WavePolynomial ι) = 0 := by simp

theorem oneParticleProjector_ne_zero [Nonempty ι] :
    oneParticleProjector (ι := ι) ≠ 0 := by
  intro h
  let i : ι := Classical.choice ‹Nonempty ι›
  have heq := congrArg (fun T : Operator ι => T (MvPolynomial.X i)) h
  exact MvPolynomial.X_ne_zero i
    (by simpa only [oneParticleProjector_X, LinearMap.zero_apply] using heq)

theorem oneParticleProjector_ne_one : oneParticleProjector (ι := ι) ≠ 1 := by
  intro h
  have heq := congrArg (fun T : Operator ι => T 1) h
  simp only [oneParticleProjector_vacuum, Module.End.one_apply] at heq
  exact zero_ne_one heq

omit [DecidableEq ι] in
theorem fockPairing_sum_left {κ : Type*} (s : Finset κ)
    (p : κ → WavePolynomial ι) (q : WavePolynomial ι) :
    fockPairing (∑ k ∈ s, p k) q = ∑ k ∈ s, fockPairing (p k) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih => simp [hk, ih]

omit [DecidableEq ι] in
theorem fockPairing_sum_right {κ : Type*} (s : Finset κ)
    (p : WavePolynomial ι) (q : κ → WavePolynomial ι) :
    fockPairing p (∑ k ∈ s, q k) = ∑ k ∈ s, fockPairing p (q k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih => simp [hk, ih]

@[simp] theorem factorialWeight_single_one (i : ι) :
    factorialWeight (Finsupp.single i 1) = 1 := by
  unfold factorialWeight
  apply Finset.prod_eq_one
  intro j _
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

@[simp] theorem fockPairing_X_left (i : ι) (p : WavePolynomial ι) :
    fockPairing (MvPolynomial.X i) p = oneParticleCoeff p i := by
  change fockPairing (MvPolynomial.monomial (Finsupp.single i 1) 1) p = _
  rw [fockPairing_monomial_left, factorialWeight_single_one]
  simp

theorem fockPairing_linearForm_left (a : Coordinates ι) (p : WavePolynomial ι) :
    fockPairing (linearForm a) p = contraction a (oneParticleCoeff p) := by
  simp [linearForm, fockPairing_sum_left, contraction]

/-- The sector coordinate map preserves the actual positive Fock pairing. -/
theorem fockPairing_linearForm (a b : Coordinates ι) :
    fockPairing (linearForm a) (linearForm b) = contraction a b := by
  rw [fockPairing_linearForm_left, oneParticleCoeff_linearForm]

theorem oneParticleProjector_symmetric (p q : WavePolynomial ι) :
    fockPairing (oneParticleProjector p) q =
      fockPairing p (oneParticleProjector q) := by
  rw [oneParticleProjector_apply, oneParticleProjector_apply,
    fockPairing_linearForm_left,
    fockPairing_symmetric p (linearForm (oneParticleCoeff q)),
    fockPairing_linearForm_left, contraction_comm]

@[simp] theorem euler_X (i : ι) :
    euler (MvPolynomial.X i : WavePolynomial ι) = MvPolynomial.X i := by
  simpa [MvPolynomial.X, Finsupp.single_apply] using
    (euler_monomial (Finsupp.single i 1) (1 : ℝ))

theorem euler_linearForm (a : Coordinates ι) : euler (linearForm a) = linearForm a := by
  simp only [linearForm, map_sum, map_smul, euler_X]

theorem euler_oneParticleProjector (p : WavePolynomial ι) :
    euler (oneParticleProjector p) = oneParticleProjector p :=
  euler_linearForm (oneParticleCoeff p)

theorem annihilate_linearForm (i : ι) (a : Coordinates ι) :
    annihilate i (linearForm a) = a i • (1 : WavePolynomial ι) := by
  simp [linearForm, annihilate_apply, map_sum, MvPolynomial.pderiv_X, Pi.single_apply]

theorem create_annihilate_linearForm (i j : ι) (a : Coordinates ι) :
    (create i * annihilate j) (linearForm a) = a j • MvPolynomial.X i := by
  change create i (annihilate j (linearForm a)) = _
  rw [annihilate_linearForm, map_smul, create_apply, mul_one]

/-- The number-conserving differential operator associated with a real matrix. -/
def oneBody (A : Matrix ι ι ℝ) : Operator ι :=
  ∑ i, ∑ j, A i j • (create i * annihilate j)

theorem oneBody_apply (A : Matrix ι ι ℝ) (p : WavePolynomial ι) :
    oneBody A p = ∑ i, ∑ j, A i j • create i (annihilate j p) := by
  simp only [oneBody, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]

/-- Exact intertwining, on the actual polynomial sector. -/
theorem oneBody_linearForm (A : Matrix ι ι ℝ) (a : Coordinates ι) :
    oneBody A (linearForm a) = linearForm (A.mulVec a) := by
  simp only [oneBody, LinearMap.sum_apply, LinearMap.smul_apply,
    create_annihilate_linearForm, smul_smul]
  simp only [linearForm, Matrix.mulVec, dotProduct, Finset.sum_smul]

theorem create_annihilate_pairing (i j : ι) (p q : WavePolynomial ι) :
    fockPairing (create i (annihilate j p)) q =
      fockPairing p (create j (annihilate i q)) := by
  rw [create_annihilate_adjoint, annihilate_create_adjoint]

/-- Matrix transposition is the positive Fock adjoint of the full operator. -/
theorem oneBody_transpose_adjoint (A : Matrix ι ι ℝ) (p q : WavePolynomial ι) :
    fockPairing (oneBody A p) q = fockPairing p (oneBody A.transpose q) := by
  simp only [oneBody_apply, fockPairing_sum_left, fockPairing_sum_right,
    fockPairing_smul_left, fockPairing_smul_right, create_annihilate_pairing,
    Matrix.transpose_apply]
  exact Finset.sum_comm

theorem oneBody_symmetric (A : Matrix ι ι ℝ) (hA : A.transpose = A)
    (p q : WavePolynomial ι) :
    fockPairing (oneBody A p) q = fockPairing p (oneBody A q) := by
  simpa only [hA] using oneBody_transpose_adjoint A p q

theorem oneParticleCoeff_oneBody (A : Matrix ι ι ℝ) (p : WavePolynomial ι) :
    oneParticleCoeff (oneBody A p) = A.mulVec (oneParticleCoeff p) := by
  funext i
  calc
    oneParticleCoeff (oneBody A p) i =
        fockPairing (MvPolynomial.X i) (oneBody A p) := (fockPairing_X_left _ _).symm
    _ = fockPairing (oneBody A.transpose (MvPolynomial.X i)) p := by
      simpa only [Matrix.transpose_transpose] using
        (oneBody_transpose_adjoint A.transpose (MvPolynomial.X i) p).symm
    _ = fockPairing (linearForm (A.transpose.mulVec (Pi.single i 1))) p := by
      rw [← linearForm_single i, oneBody_linearForm]
    _ = contraction (A.transpose.mulVec (Pi.single i 1)) (oneParticleCoeff p) :=
      fockPairing_linearForm_left _ _
    _ = A.mulVec (oneParticleCoeff p) i := by
      rw [Matrix.mulVec_single_one]
      rfl

/-- The coefficient projector commutes with every number-conserving bilinear. -/
theorem oneParticleProjector_oneBody_commute (A : Matrix ι ι ℝ) :
    oneParticleProjector * oneBody A = oneBody A * oneParticleProjector := by
  apply LinearMap.ext
  intro p
  change linearForm (oneParticleCoeff (oneBody A p)) =
    oneBody A (linearForm (oneParticleCoeff p))
  rw [oneParticleCoeff_oneBody, oneBody_linearForm]

/-- Faithfulness follows from the explicit sector intertwiner. -/
theorem oneBody_injective : Function.Injective (oneBody (ι := ι)) := by
  intro A B h
  apply Matrix.ext_of_mulVec_single
  intro j
  apply linearForm_injective
  have heq := congrArg (fun T : Operator ι => T (linearForm (Pi.single j 1))) h
  simpa only [oneBody_linearForm] using heq

end InfoGeometry.Twistor.RealPolynomialCCR
