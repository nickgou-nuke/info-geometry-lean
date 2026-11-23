/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.PenroseTwistor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic
import InfoGeometry.External.Virasoro.IsCentralExtension
import InfoGeometry.External.Virasoro.LieAlgebraRepresentationOfBasis

/-!
# A concrete polynomial realization of the bi-twistor CCR

Source: Penrose, Chapter 7, equations (7.59), (7.82)--(7.90).
The coefficient carrier reuses the repository's complex twistor four-space.
The operators act on the full polynomial algebra, not on a finite-dimensional
matrix space. No commutator relation is postulated. This algebraic model is
not the analytic Hilbert space or Cech cohomology of massless fields.
-/

noncomputable section

namespace InfoGeometry.Twistor.PenrosePolynomialCCR

open InfoGeometry.Twistor.PenroseTwistor
open scoped BigOperators

abbrev Coeff := TwistorCarrier × TwistorCarrier
abbrev WavePolynomial := MvPolynomial (Fin 4) ℂ
abbrev Operator := Module.End ℂ WavePolynomial

/-- Ordinary contraction of a coordinate coefficient and a dual coefficient. -/
def contraction (a b : TwistorCarrier) : ℂ := ∑ i, a i * b i

/-- The linear polynomial with prescribed multiplication coefficients. -/
def linearForm (a : TwistorCarrier) : WavePolynomial :=
  ∑ i, a i • MvPolynomial.X i

/-- Native polynomial derivation specified on the four generators. -/
def directional (b : TwistorCarrier) : Derivation ℂ WavePolynomial WavePolynomial :=
  MvPolynomial.mkDerivation ℂ (fun i => b i • (1 : WavePolynomial))

@[simp] theorem directional_X (b : TwistorCarrier) (j : Fin 4) :
    directional b (MvPolynomial.X j) = b j • (1 : WavePolynomial) := by
  simp [directional]

/-- The displayed derivation is exactly the linear combination of native partials. -/
theorem directional_eq_pderiv_sum (b : TwistorCarrier) :
    directional b = ∑ i : Fin 4, b i • MvPolynomial.pderiv i := by
  apply MvPolynomial.derivation_ext
  intro j
  fin_cases j <;>
    simp [directional, Fin.sum_univ_four, MvPolynomial.pderiv_X, Pi.single_apply]

@[simp] theorem linearForm_add (a b : TwistorCarrier) :
    linearForm (a + b) = linearForm a + linearForm b := by
  simp [linearForm, add_smul, Finset.sum_add_distrib]

@[simp] theorem linearForm_smul (c : ℂ) (a : TwistorCarrier) :
    linearForm (c • a) = c • linearForm a := by
  simp [linearForm, Finset.smul_sum, smul_smul]

@[simp] theorem linearForm_zero : linearForm 0 = 0 := by simp [linearForm]

@[simp] theorem directional_add (a b : TwistorCarrier) :
    directional (a + b) = directional a + directional b := by
  apply MvPolynomial.derivation_ext
  intro j
  simp [add_smul]

@[simp] theorem directional_smul (c : ℂ) (a : TwistorCarrier) :
    directional (c • a) = c • directional a := by
  apply MvPolynomial.derivation_ext
  intro j
  simp [smul_smul]

@[simp] theorem directional_zero : directional 0 = 0 := by
  apply MvPolynomial.derivation_ext
  intro j
  simp

theorem contraction_comm (a b : TwistorCarrier) : contraction a b = contraction b a := by
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem directional_linearForm (a b : TwistorCarrier) :
    directional b (linearForm a) = contraction a b • (1 : WavePolynomial) := by
  simp [linearForm, contraction, map_sum, directional_X, smul_smul, Finset.sum_smul]

theorem directional_mul (b : TwistorCarrier) (p q : WavePolynomial) :
    directional b (p * q) = directional b p * q + p * directional b q := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

/-- Constant-coefficient partial derivations commute; proved on generators. -/
theorem directional_commute (a b : TwistorCarrier) (p : WavePolynomial) :
    directional a (directional b p) = directional b (directional a p) := by
  have h : ⁅directional a, directional b⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [Derivation.commutator_apply]
  have hp := Derivation.congr_fun h p
  exact sub_eq_zero.mp (by simpa [Derivation.commutator_apply] using hp)

/-- `a_i Z_i + b_i W_i`, with `Z_i = X_i` and `W_i = -h partial_i`. -/
def quantize (h : ℂ) (A : Coeff) : Operator where
  toFun p := linearForm A.1 * p - h • directional A.2 p
  map_add' p q := by simp [mul_add, smul_add] <;> abel
  map_smul' c p := by
    simp [Algebra.mul_smul_comm, smul_sub, smul_smul, mul_comm]

@[simp] theorem quantize_apply (h : ℂ) (A : Coeff) (p : WavePolynomial) :
    quantize h A p = linearForm A.1 * p - h • directional A.2 p := rfl

@[simp] theorem quantize_zero (h : ℂ) : quantize h 0 = 0 := by
  apply LinearMap.ext
  intro p
  simp

@[simp] theorem quantize_add (h : ℂ) (A B : Coeff) :
    quantize h (A + B) = quantize h A + quantize h B := by
  apply LinearMap.ext
  intro p
  simp [add_mul, smul_add] <;> abel

@[simp] theorem quantize_smul (h c : ℂ) (A : Coeff) :
    quantize h (c • A) = c • quantize h A := by
  apply LinearMap.ext
  intro p
  simp [Algebra.smul_mul_assoc, smul_sub, smul_smul, mul_comm]

/-- Canonical alternating pairing of the multiplication/differentiation coefficients. -/
def omega (A B : Coeff) : ℂ := contraction A.1 B.2 - contraction A.2 B.1

theorem omega_skew (A B : Coeff) : omega A B = -omega B A := by
  unfold omega
  rw [contraction_comm B.1 A.2, contraction_comm B.2 A.1]
  ring

/-- The canonical alternating form on the bi-twistor coefficient space has
zero radical: its coordinate and derivative slots are detected by pairing
against the opposite pure slot. This is the algebraic nondegeneracy needed
for the associated Heisenberg extension. -/
theorem omega_radical_eq_zero (A : Coeff)
    (hA : ∀ B : Coeff, omega A B = 0) : A = 0 := by
  apply Prod.ext
  · funext i
    have hi := hA (0, Pi.single i 1)
    simpa [omega, contraction, Pi.single_apply] using hi
  · funext i
    have hi := hA (Pi.single i 1, 0)
    simpa [omega, contraction, Pi.single_apply] using hi

/-- Equivalently, only the zero coefficient pairs trivially with every
bi-twistor. -/
theorem omega_eq_zero_forall_iff (A : Coeff) :
    (∀ B : Coeff, omega A B = 0) ↔ A = 0 := by
  constructor
  · exact omega_radical_eq_zero A
  · rintro rfl B
    simp [omega, contraction]

/-- Full CCR on arbitrary linear bi-twistors, derived in the polynomial representation. -/
theorem quantize_commutator (h : ℂ) (A B : Coeff) :
    quantize h A * quantize h B - quantize h B * quantize h A =
      (h * omega A B) • (1 : Operator) := by
  apply LinearMap.ext
  intro p
  change quantize h A (quantize h B p) - quantize h B (quantize h A p) =
    (h * omega A B) • p
  simp only [quantize_apply, map_sub, map_smul, directional_mul, directional_linearForm]
  rw [directional_commute B.2 A.2 p, contraction_comm B.1 A.2]
  simp [omega, Algebra.smul_def] <;> ring

/-! ## Mathlib Heisenberg central extension and polynomial representation

The coefficient space is made into an abelian Lie algebra, and the proved
polynomial CCR pairing is packaged as a genuine `LieTwoCocycle`. Mathlib's
central-extension construction supplies the bracket and Lie laws. The
polynomial action is then bundled as a `LieAlgebra.Representation`. -/

noncomputable instance coeffLieRing : LieRing Coeff where
  bracket _ _ := 0
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp

noncomputable instance coeffLieAlgebra : LieAlgebra ℂ Coeff where
  lie_smul c x y := by
    change (0 : Coeff) = c • (0 : Coeff)
    simp

noncomputable instance coeffIsLieAbelian : IsLieAbelian Coeff where
  trivial _ _ := rfl

/-- The CCR alternating form as an honest bilinear map. -/
private theorem omega_add_left (A B C : Coeff) :
    omega (A + B) C = omega A C + omega B C := by
  simp [omega, contraction, Finset.sum_add_distrib, add_mul]
  abel

private theorem omega_add_right (A B C : Coeff) :
    omega A (B + C) = omega A B + omega A C := by
  simp [omega, contraction, Finset.sum_add_distrib, mul_add]
  abel

private theorem omega_smul_left (c : ℂ) (A B : Coeff) :
    omega (c • A) B = c * omega A B := by
  simp [omega, contraction, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

private theorem omega_smul_right (c : ℂ) (A B : Coeff) :
    omega A (c • B) = c * omega A B := by
  simp [omega, contraction, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

def omegaBilin : Coeff →ₗ[ℂ] Coeff →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ omega
    (by intro A B C; exact omega_add_left A B C)
    (by intro c A B; simpa [smul_eq_mul] using omega_smul_left c A B)
    (by intro A B C; exact omega_add_right A B C)
    (by intro c A B; simpa [smul_eq_mul] using omega_smul_right c A B)

/-- The polynomial CCR define a Lie algebra two-cocycle on the abelian
bi-twistor coefficient space. -/
noncomputable def twistorHeisenbergCocycle (h : ℂ) :
    VirasoroProject.LieTwoCocycle ℂ Coeff ℂ where
  toBilin := h • omegaBilin
  self' A := by
    change h * omega A A = 0
    unfold omega
    rw [contraction_comm]
    ring
  leibniz' A B C := by
    change h * omega A ⁅B, C⁆ =
      h * omega ⁅A, B⁆ C + h * omega B ⁅A, C⁆
    change h * omega A 0 = h * omega 0 C + h * omega B 0
    simp [omega, contraction]

/-- The cocycle evaluates to the central parameter on one canonical
coordinate/derivative pair. Thus its central grade is produced by the
represented CCR rather than appended as an independent scalar summand. -/
theorem twistorHeisenbergCocycle_coordinate_pair (h : ℂ) :
    (twistorHeisenbergCocycle h).toBilin
      (Pi.single (0 : Fin 4) (1 : ℂ), 0)
      (0, Pi.single (0 : Fin 4) 1) = h := by
  change h * omega (Pi.single (0 : Fin 4) (1 : ℂ), 0)
      (0, Pi.single (0 : Fin 4) 1) = h
  simp [omega, contraction, Pi.single_apply]

/-- A nonzero canonical CCR parameter gives a nonzero defining Lie
2-cocycle. This theorem concerns the cocycle as a bilinear map; it does not
classify central extensions up to equivalence. -/
theorem twistorHeisenbergCocycle_ne_zero {h : ℂ} (hh : h ≠ 0) :
    twistorHeisenbergCocycle h ≠ 0 := by
  intro hcocycle
  have heval := congrArg
    (fun c : VirasoroProject.LieTwoCocycle ℂ Coeff ℂ =>
      c.toBilin (Pi.single (0 : Fin 4) (1 : ℂ), 0)
        (0, Pi.single (0 : Fin 4) 1)) hcocycle
  rw [twistorHeisenbergCocycle_coordinate_pair] at heval
  exact hh heval

/-- The cocycle is not a Lie-algebra coboundary when `h ≠ 0`. Every
1-coboundary on the abelian coefficient Lie algebra vanishes on every pair,
whereas the canonical coordinate/derivative pair evaluates to `h`. -/
theorem twistorHeisenbergCocycle_not_coboundary {h : ℂ} (hh : h ≠ 0) :
    ¬ ∃ f : Coeff →ₗ[ℂ] ℂ,
      ∀ A B : Coeff,
        (twistorHeisenbergCocycle h).toBilin A B = f ⁅A, B⁆ := by
  rintro ⟨f, hf⟩
  let eZ : Coeff := ((Pi.single (0 : Fin 4) (1 : ℂ) : TwistorCarrier), 0)
  let eW : Coeff := (0, (Pi.single (0 : Fin 4) (1 : ℂ) : TwistorCarrier))
  have heq := hf eZ eW
  have hvalue : (twistorHeisenbergCocycle h).toBilin eZ eW = h := by
    simpa [eZ, eW] using twistorHeisenbergCocycle_coordinate_pair h
  rw [hvalue] at heq
  have hbracket : ⁅eZ, eW⁆ = (0 : Coeff) := by
    change (0 : Coeff) = 0
    rfl
  rw [hbracket, map_zero] at heq
  exact hh heq

/-- The actual Mathlib central extension associated to the twistor CCR. -/
abbrev TwistorHeisenberg (h : ℂ) :=
  (twistorHeisenbergCocycle h).CentralExtension

noncomputable instance twistorHeisenbergLieRing (h : ℂ) :
    LieRing (TwistorHeisenberg h) :=
  VirasoroProject.LieTwoCocycle.CentralExtension.instLieRing _

noncomputable instance twistorHeisenbergLieAlgebra (h : ℂ) :
    LieAlgebra ℂ (TwistorHeisenberg h) :=
  VirasoroProject.LieTwoCocycle.CentralExtension.instLieAlgebra _

/-- For nonzero CCR parameter, the center of the constructed Heisenberg Lie
algebra is exactly its designated central coordinate: an element commutes
with every extension element iff its bi-twistor coefficient vanishes. -/
theorem twistorHeisenberg_center_fst_eq_zero {h : ℂ} (hh : h ≠ 0)
    (x : TwistorHeisenberg h) :
    (∀ y : TwistorHeisenberg h, ⁅x, y⁆ = 0) ↔ x.fst = 0 := by
  constructor
  · intro hcentral
    apply omega_radical_eq_zero x.fst
    intro B
    have hpair := hcentral ⟨B, 0⟩
    have hsnd := congrArg (fun z : TwistorHeisenberg h => z.snd) hpair
    have hmul : h * omega x.fst B = 0 := by
      change (twistorHeisenbergCocycle h).toBilin x.fst B = 0 at hsnd
      change h * omega x.fst B = 0 at hsnd
      exact hsnd
    rcases mul_eq_zero.mp hmul with hh' | hω
    · exact (hh hh').elim
    · exact hω
  · intro hx y
    rw [VirasoroProject.LieTwoCocycle.CentralExtension.lie_def]
    apply VirasoroProject.LieTwoCocycle.CentralExtension.ext
    · simp [hx]
    · change (twistorHeisenbergCocycle h).toBilin x.fst y.fst = 0
      rw [hx]
      simp [twistorHeisenbergCocycle, omegaBilin, LinearMap.mk₂_apply]

attribute [local instance 100] LieRing.ofAssociativeRing

theorem scalarIdentityOperator_commutes (c : ℂ) (T : Operator) :
    (c • (1 : Operator)) * T = T * (c • (1 : Operator)) := by
  apply LinearMap.ext
  intro p
  change c • T p = T (c • p)
  rw [map_smul]

private theorem twistorHeisenberg_action_commutator (h : ℂ)
    (x y : TwistorHeisenberg h) :
    (quantize h x.fst + x.snd • (1 : Operator)) *
        (quantize h y.fst + y.snd • (1 : Operator)) -
      (quantize h y.fst + y.snd • (1 : Operator)) *
        (quantize h x.fst + x.snd • (1 : Operator)) =
      (h * omega x.fst y.fst) • (1 : Operator) := by
  have hq := quantize_commutator h x.fst y.fst
  calc
    (quantize h x.fst + x.snd • (1 : Operator)) *
        (quantize h y.fst + y.snd • (1 : Operator)) -
      (quantize h y.fst + y.snd • (1 : Operator)) *
        (quantize h x.fst + x.snd • (1 : Operator)) =
      quantize h x.fst * quantize h y.fst - quantize h y.fst * quantize h x.fst := by
      simp only [add_mul, mul_add]
      rw [scalarIdentityOperator_commutes x.snd (quantize h y.fst),
        scalarIdentityOperator_commutes y.snd (quantize h x.fst),
        scalarIdentityOperator_commutes x.snd (y.snd • (1 : Operator)),
        scalarIdentityOperator_commutes y.snd (x.snd • (1 : Operator))]
      abel
    _ = (h * omega x.fst y.fst) • (1 : Operator) := hq

/-- Polynomial Fock action of a central-extension element: its twistor
coefficient acts by the proved quantization and its central coordinate acts
by scalar identity. -/
noncomputable def heisenbergRepresentation (h : ℂ) :
    LieAlgebra.Representation ℂ ℂ (TwistorHeisenberg h) WavePolynomial where
  toLinearMap := {
    toFun := fun x => quantize h x.fst + x.snd • (1 : Operator)
    map_add' := by
      intro x y
      apply LinearMap.ext
      intro p
      simp [quantize_add, add_smul, add_assoc, add_comm, add_left_comm]
    map_smul' := by
      intro c x
      apply LinearMap.ext
      intro p
      simp [quantize_smul, smul_add, smul_smul] }
  map_lie' := by
    intro x y
    rw [VirasoroProject.LieTwoCocycle.CentralExtension.lie_def]
    change quantize h 0 +
        ((twistorHeisenbergCocycle h) x.fst y.fst) • (1 : Operator) =
      (quantize h x.fst + x.snd • (1 : Operator)) *
        (quantize h y.fst + y.snd • (1 : Operator)) -
      (quantize h y.fst + y.snd • (1 : Operator)) *
        (quantize h x.fst + x.snd • (1 : Operator))
    rw [quantize_zero]
    rw [twistorHeisenberg_action_commutator]
    have hcocycle : (twistorHeisenbergCocycle h) x.fst y.fst =
        h * omega x.fst y.fst := by
      change (h • omegaBilin) x.fst y.fst = _
      simp [omegaBilin, LinearMap.mk₂_apply, smul_eq_mul]
    rw [hcocycle]
    simp

/-- Coordinate multiplication operator. -/
def Z (i : Fin 4) : Operator := quantize 1 (Pi.single i 1, 0)

/-- Conjugate polynomial differentiation operator. -/
def W (h : ℂ) (i : Fin 4) : Operator := quantize h (0, Pi.single i 1)

theorem Z_apply (i : Fin 4) (p : WavePolynomial) : Z i p = MvPolynomial.X i * p := by
  simp [Z, linearForm]

theorem W_apply (h : ℂ) (i : Fin 4) (p : WavePolynomial) :
    W h i p = -h • MvPolynomial.pderiv i p := by
  rw [W, quantize_apply, linearForm_zero, directional_eq_pderiv_sum]
  simp

/-- The scalar central coordinate does not alter commutators in the
endomorphism ring of the polynomial module. -/
private theorem quantize_scalar_commutator (h : ℂ) (A B : Coeff) (c : ℂ) :
    (quantize h A + c • (1 : Operator)) * quantize h B -
      quantize h B * (quantize h A + c • (1 : Operator)) =
        (h * omega A B) • (1 : Operator) := by
  calc
    (quantize h A + c • (1 : Operator)) * quantize h B -
        quantize h B * (quantize h A + c • (1 : Operator)) =
          quantize h A * quantize h B - quantize h B * quantize h A := by
            simp only [add_mul, mul_add]
            rw [scalarIdentityOperator_commutes c (quantize h B)]
            abel
    _ = (h * omega A B) • (1 : Operator) := quantize_commutator h A B

/-- The polynomial representation of the twistor Heisenberg central
extension is faithful whenever the central parameter is nonzero. Commuting
with each coordinate and derivative operator recovers all eight linear
coefficients; evaluating the remaining scalar operator on `1` recovers the
central coordinate. -/
theorem heisenbergRepresentation_injective (h : ℂ) (hh : h ≠ 0) :
    Function.Injective (heisenbergRepresentation h) := by
  intro x y hxy
  have hker : ∀ z : TwistorHeisenberg h,
      heisenbergRepresentation h z = 0 → z = 0 := by
    intro z hz
    change quantize h z.fst + z.snd • (1 : Operator) = 0 at hz
    have hZcomm (i : Fin 4) :
        (quantize h z.fst + z.snd • (1 : Operator)) * Z i -
          Z i * (quantize h z.fst + z.snd • (1 : Operator)) =
            (h * omega z.fst (Pi.single i 1, 0)) • (1 : Operator) := by
      have hcoord : quantize h (Pi.single i 1, 0) = Z i := by
        apply LinearMap.ext
        intro p
        simp [Z, quantize_apply, linearForm, directional_zero]
      rw [← hcoord]
      exact quantize_scalar_commutator h z.fst (Pi.single i 1, 0) z.snd
    have hWcomm (i : Fin 4) :
        (quantize h z.fst + z.snd • (1 : Operator)) * W h i -
          W h i * (quantize h z.fst + z.snd • (1 : Operator)) =
            (h * omega z.fst (0, Pi.single i 1)) • (1 : Operator) := by
      exact quantize_scalar_commutator h z.fst (0, Pi.single i 1) z.snd
    have hb (i : Fin 4) : z.fst.2 i = 0 := by
      have hzero := hZcomm i
      rw [hz] at hzero
      simp only [zero_mul, mul_zero, sub_self] at hzero
      have hpoly : (h * omega z.fst (Pi.single i 1, 0)) •
          (1 : WavePolynomial) = 0 := by
        have heval := congrArg (fun T : Operator => T (1 : WavePolynomial)) hzero
        simpa using heval.symm
      have hcoef : h * omega z.fst (Pi.single i 1, 0) = 0 :=
        (smul_eq_zero.mp hpoly).resolve_right one_ne_zero
      have hω : omega z.fst (Pi.single i 1, 0) = 0 := by
        rcases mul_eq_zero.mp hcoef with hh' | hω
        · exact (hh hh').elim
        · exact hω
      simpa [omega, contraction, Pi.single_apply] using hω
    have ha (i : Fin 4) : z.fst.1 i = 0 := by
      have hzero := hWcomm i
      rw [hz] at hzero
      simp only [zero_mul, mul_zero, sub_self] at hzero
      have hpoly : (h * omega z.fst (0, Pi.single i 1)) •
          (1 : WavePolynomial) = 0 := by
        have heval := congrArg (fun T : Operator => T (1 : WavePolynomial)) hzero
        simpa using heval.symm
      have hcoef : h * omega z.fst (0, Pi.single i 1) = 0 :=
        (smul_eq_zero.mp hpoly).resolve_right one_ne_zero
      have hω : omega z.fst (0, Pi.single i 1) = 0 := by
        rcases mul_eq_zero.mp hcoef with hh' | hω
        · exact (hh hh').elim
        · exact hω
      simpa [omega, contraction, Pi.single_apply] using hω
    have hfst : z.fst = 0 := by
      apply Prod.ext
      · funext i
        exact ha i
      · funext i
        exact hb i
    have hcentralOp : z.snd • (1 : Operator) = 0 := by
      simpa [hfst] using hz
    have hcentralPoly : z.snd • (1 : WavePolynomial) = 0 := by
      have heval := congrArg (fun T : Operator => T (1 : WavePolynomial)) hcentralOp
      simpa using heval
    have hcentral : z.snd = 0 :=
      (smul_eq_zero.mp hcentralPoly).resolve_right one_ne_zero
    cases z with
    | mk a b => ext <;> simp_all
  have hxy0 : heisenbergRepresentation h (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hsub := hker (x - y) hxy0
  exact sub_eq_zero.mp hsub

/-- At zero central parameter, the polynomial representation is not faithful:
the pure derivative generator lies in the kernel because its quantization is
`-h ∂` and hence vanishes at `h = 0`. This shows the nonzero hypothesis in
`heisenbergRepresentation_injective` is necessary. -/
theorem heisenbergRepresentation_not_injective_zero :
    ¬ Function.Injective (heisenbergRepresentation 0) := by
  intro hinj
  let z : TwistorHeisenberg 0 := ⟨(0, Pi.single 0 1), 0⟩
  have hz : z ≠ 0 := by
    intro hzero
    have hcoord := congrArg (fun x : TwistorHeisenberg 0 => x.fst.2 0) hzero
    norm_num [z] at hcoord
  have hrep : heisenbergRepresentation 0 z = 0 := by
    apply LinearMap.ext
    intro p
    change (quantize 0 z.fst + z.snd • (1 : Operator)) p = 0
    simp [z, quantize]
  exact hz (hinj (by simpa using hrep))

/-- The Euler operator on the polynomial twistor carrier, expressed as an
ordered sum of coordinate multiplication followed by differentiation. -/
def eulerOperator : Operator := ∑ i : Fin 4, Z i * W (-1) i

/-- Ordered Euler operator in the holomorphic polarization. Since `W 1` acts as
negative differentiation, it has eigenvalue minus the polynomial degree. -/
def homogeneityOperator : Operator := ∑ i : Fin 4, Z i * W 1 i

/-- Each monomial is an Euler eigenvector, with eigenvalue its total exponent.
This is an operator identity on the full polynomial representation. -/
theorem eulerOperator_monomial (m : Fin 4 →₀ ℕ) (c : ℂ) :
    eulerOperator (MvPolynomial.monomial m c) =
      (∑ i : Fin 4, (m i : ℂ)) • MvPolynomial.monomial m c := by
  classical
  have hterm (i : Fin 4) :
      Z i (W (-1) i (MvPolynomial.monomial m c)) =
        (m i : ℂ) • MvPolynomial.monomial m c := by
    simp only [W_apply, neg_neg, one_smul, Z_apply]
    simpa only [← Nat.cast_smul_eq_nsmul ℂ] using
      (MvPolynomial.X_mul_pderiv_monomial (i := i) (m := m) (r := c))
  change (∑ i : Fin 4, Z i (W (-1) i (MvPolynomial.monomial m c))) = _
  simp_rw [hterm]
  rw [Finset.sum_smul]

/-- In the holomorphic polarization `W 1 = -∂`, so the ordered homogeneity
operator has the negative total-degree eigenvalue. -/
theorem homogeneityOperator_monomial (m : Fin 4 →₀ ℕ) (c : ℂ) :
    homogeneityOperator (MvPolynomial.monomial m c) =
      - (∑ i : Fin 4, (m i : ℂ)) • MvPolynomial.monomial m c := by
  classical
  have hterm (i : Fin 4) :
      Z i (W 1 i (MvPolynomial.monomial m c)) =
        -((m i : ℂ) • MvPolynomial.monomial m c) := by
    calc
      Z i (W 1 i (MvPolynomial.monomial m c)) =
          -(MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.monomial m c)) := by
            simp [W_apply, Z_apply]
      _ = -((m i : ℂ) • MvPolynomial.monomial m c) := by
            rw [MvPolynomial.X_mul_pderiv_monomial]
            simp only [← Nat.cast_smul_eq_nsmul ℂ]
  change (∑ i : Fin 4, Z i (W 1 i (MvPolynomial.monomial m c))) = _
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib, neg_smul]
  congr 1
  rw [← Finset.sum_smul]

/-- The Euler action on an arbitrary polynomial is the finite sum of its
monomial degree eigenvalues. The indexing is the polynomial's actual finite
support, so this does not assume homogeneous input. -/
theorem eulerOperator_support_expansion (p : WavePolynomial) :
    eulerOperator p =
      ∑ m ∈ p.support,
        (∑ i : Fin 4, (m i : ℂ)) • MvPolynomial.monomial m (p.coeff m) := by
  calc
    eulerOperator p =
        eulerOperator (∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m)) := by
          exact congrArg eulerOperator (MvPolynomial.as_sum p)
    _ = ∑ m ∈ p.support,
          (∑ i : Fin 4, (m i : ℂ)) • MvPolynomial.monomial m (p.coeff m) := by
          simp only [map_sum]
          apply Finset.sum_congr rfl
          intro m hm
          exact eulerOperator_monomial m (p.coeff m)

/-- A polynomial is homogeneous of degree `n` when every exponent vector in
its finite support has total exponent `n`. -/
def IsHomogeneousOfDegree (n : ℕ) (p : WavePolynomial) : Prop :=
  ∀ m ∈ p.support, (∑ i : Fin 4, m i) = n

/-- On genuinely homogeneous polynomials, the Euler operator acts by the
degree. This derives the eigenspace relation from the polynomial support. -/
theorem eulerOperator_homogeneous (n : ℕ) (p : WavePolynomial)
    (hp : IsHomogeneousOfDegree n p) :
    eulerOperator p = (n : ℂ) • p := by
  rw [eulerOperator_support_expansion]
  calc
    (∑ m ∈ p.support,
        (∑ i : Fin 4, (m i : ℂ)) • MvPolynomial.monomial m (p.coeff m)) =
      ∑ m ∈ p.support,
        (n : ℂ) • MvPolynomial.monomial m (p.coeff m) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [← Nat.cast_sum, hp m hm]
    _ = (n : ℂ) • ∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m) := by
          rw [← Finset.smul_sum]
    _ = (n : ℂ) • p := by
          congr 1
          exact (MvPolynomial.as_sum p).symm

/-- In the holomorphic polarization, the normally ordered homogeneity
operator has eigenvalue `-n` on homogeneous degree-`n` polynomials. This is
the operator statement that supplies the degree input to the projective
weight calculation; it does not identify a sheaf cohomology group. -/
theorem homogeneityOperator_homogeneous (n : ℕ) (p : WavePolynomial)
    (hp : IsHomogeneousOfDegree n p) :
    homogeneityOperator p = -((n : ℂ) • p) := by
  change (∑ i : Fin 4, Z i (W 1 i p)) = -((n : ℂ) • p)
  have hnormal : (∑ i : Fin 4, Z i (W 1 i p)) = -eulerOperator p := by
    have hterm (i : Fin 4) :
        Z i (W 1 i p) = -(Z i (W (-1) i p)) := by
      simp [W_apply]
    calc
      (∑ i : Fin 4, Z i (W 1 i p)) =
          ∑ i : Fin 4, -(Z i (W (-1) i p)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i
      _ = -(∑ i : Fin 4, Z i (W (-1) i p)) := by
            simp only [Finset.sum_neg_distrib]
      _ = -eulerOperator p := rfl
  rw [hnormal, eulerOperator_homogeneous n p hp]

/-- The coordinate CCR are genuine operator equalities, not structure fields. -/
theorem coordinate_CCR (h : ℂ) (i j : Fin 4) :
    Z i * W h j - W h j * Z i = (if i = j then h else 0) • (1 : Operator) := by
  apply LinearMap.ext
  intro p
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Z_apply, W_apply,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
  by_cases hij : i = j
  · subst j
    simp [Algebra.smul_def, Pi.single_apply] <;> ring
  · simp [hij, Ne.symm hij, Algebra.smul_def, Pi.single_apply] <;> ring

/-- For nonzero Planck parameter, a coordinate and its conjugate derivative
are genuinely noncommuting elements of the operator ring. The proof detects
the nonzero central operator by applying it to the constant polynomial. -/
theorem coordinate_derivative_noncommute (h : ℂ) (hh : h ≠ 0) (i : Fin 4) :
    Z i * W h i ≠ W h i * Z i := by
  intro heq
  have hCCR := coordinate_CCR h i i
  rw [heq] at hCCR
  have hcentral : h • (1 : Operator) = 0 := by
    simpa using hCCR.symm
  have hone : h • (1 : WavePolynomial) = 0 := by
    have heval := congrArg (fun T : Operator => T (1 : WavePolynomial)) hcentral
    simpa using heval
  exact hh ((smul_eq_zero.mp hone).resolve_right one_ne_zero)

/-- The four coordinate commutators produce the Weyl-ordering anomaly as an
identity in the noncommutative endomorphism algebra of the full polynomial
carrier. -/
theorem total_coordinate_CCR (h : ℂ) :
    ∑ i : Fin 4, (Z i * W h i - W h i * Z i) =
      (4 * h) • (1 : Operator) := by
  have hdiag (i : Fin 4) :
      Z i * W h i - W h i * Z i = h • (1 : Operator) := by
    simpa using coordinate_CCR h i i
  rw [Fin.sum_univ_four, hdiag 0, hdiag 1, hdiag 2, hdiag 3]
  change h • (1 : Operator) + h • 1 + h • 1 + h • 1 = (4 * h) • (1 : Operator)
  rw [← add_smul, ← add_smul, ← add_smul]
  congr 1
  ring

/-- The four-coordinate Weyl-ordering shift, derived from the represented CCR. -/
theorem weylOrdering_anomaly :
    ∑ i : Fin 4, (Z i * W 1 i + W 1 i * Z i) =
      2 • homogeneityOperator - (4 * (1 : ℂ)) • (1 : Operator) := by
  calc
    ∑ i : Fin 4, (Z i * W 1 i + W 1 i * Z i) =
        2 • homogeneityOperator -
          ∑ i : Fin 4, (Z i * W 1 i - W 1 i * Z i) := by
            simp only [homogeneityOperator, Fin.sum_univ_four]
            abel
    _ = 2 • homogeneityOperator - (4 * (1 : ℂ)) • (1 : Operator) := by
      rw [total_coordinate_CCR (1 : ℂ)]

/-- On a homogeneous degree-`n` state, Weyl ordering gives twice the normally
ordered degree action together with the central four-coordinate shift. The
constant is represented by multiplication by the polynomial constant `C 4`;
the conclusion is an equality in the polynomial module, derived from the
noncommuting operator identity above. -/
theorem weylOrdering_anomaly_homogeneous (n : ℕ) (p : WavePolynomial)
    (hp : IsHomogeneousOfDegree n p) :
    (∑ i : Fin 4, (Z i * W 1 i + W 1 i * Z i)) p =
      2 • (-(n : ℂ) • p) - ((4 : ℂ) • (1 : Operator)) p := by
  have hact := congrArg (fun T : Operator => T p) weylOrdering_anomaly
  rw [LinearMap.sub_apply, LinearMap.smul_apply] at hact
  rw [homogeneityOperator_homogeneous n p hp] at hact
  simpa using hact

/-- The Weyl-ordering action scales linearly with the central parameter `h`.
This keeps the commutator-derived central shift in the actual operator
representation while allowing arbitrary values of the formal Planck
parameter. -/
theorem weylOrdering_anomaly_hbar_homogeneous (h : ℂ) (n : ℕ)
    (p : WavePolynomial) (hp : IsHomogeneousOfDegree n p) :
    (∑ i : Fin 4, (Z i * W h i + W h i * Z i)) p =
      h • (2 • (-(n : ℂ) • p) - ((4 : ℂ) • (1 : Operator)) p) := by
  have hW (i : Fin 4) (q : WavePolynomial) :
      W h i q = h • W 1 i q := by
    simp [W_apply, smul_smul]
  change (∑ i : Fin 4,
      (Z i (W h i p) + W h i (Z i p))) = _
  calc
    (∑ i : Fin 4, (Z i (W h i p) + W h i (Z i p))) =
        ∑ i : Fin 4, h • (Z i (W 1 i p) + W 1 i (Z i p)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hW i p, hW i (Z i p), map_smul]
          simp [smul_add]
    _ = h • ((∑ i : Fin 4, (Z i * W 1 i + W 1 i * Z i)) p) := by
          congr 1
          simp only [LinearMap.sum_apply, LinearMap.add_apply,
            Module.End.mul_apply]
          rw [Finset.smul_sum]
    _ = h • (2 • (-(n : ℂ) • p) - ((4 : ℂ) • (1 : Operator)) p) := by
          rw [weylOrdering_anomaly_homogeneous n p hp]

/-- Explicit degree eigenvalue for the Weyl-ordered four-coordinate operator:
on homogeneous degree `n`, its action is multiplication by
`-(2n + 4) h`. This is the polynomial representation statement underlying
the projective weight shift; it alone does not construct projective
cohomology. -/
theorem weylOrdering_degree_eigenvalue (h : ℂ) (n : ℕ)
    (p : WavePolynomial) (hp : IsHomogeneousOfDegree n p) :
    (∑ i : Fin 4, (Z i * W h i + W h i * Z i)) p =
      (-((2 : ℂ) * (n : ℂ) + 4) * h) • p := by
  rw [weylOrdering_anomaly_hbar_homogeneous h n p hp]
  change h • (2 • (-(n : ℂ) • p) - (4 : ℂ) • p) = _
  simp only [smul_sub, smul_smul]
  module

/-- Multiplication coordinates commute in the actual polynomial model. -/
theorem coordinate_ZZ (i j : Fin 4) : Z i * Z j = Z j * Z i := by
  apply LinearMap.ext
  intro p
  simp only [Module.End.mul_apply, Z_apply]
  ring

/-- Differentiation coordinates also commute; no second CCR is assumed. -/
theorem coordinate_WW (h : ℂ) (i j : Fin 4) : W h i * W h j = W h j * W h i := by
  have hh := quantize_commutator h (0, Pi.single i 1) (0, Pi.single j 1)
  have ho : omega (0, Pi.single i 1) (0, Pi.single j 1) = 0 := by
    simp [omega, contraction]
  rw [ho, mul_zero, zero_smul] at hh
  exact sub_eq_zero.mp hh

/-- The six-term alternating operator product from equation (7.89). -/
def operatorTriple (A B C : Operator) : Operator :=
  Complex.I • (A * B * C + B * C * A + C * A * B -
    A * C * B - B * A * C - C * B * A)

/-- Rewriting the six products uses only associativity of operator composition. -/
theorem operatorTriple_commutators (A B C : Operator) :
    operatorTriple A B C = Complex.I •
      (A * (B * C) - A * (C * B) + B * (C * A) - B * (A * C) +
        C * (A * B) - C * (B * A)) := by
  unfold operatorTriple
  congr 1
  simp only [mul_assoc]
  abel

private theorem alternating_factor (A B C : Operator) :
    A * (B * C) - A * (C * B) + B * (C * A) - B * (A * C) +
        C * (A * B) - C * (B * A) =
      A * (B * C - C * B) + B * (C * A - A * C) +
        C * (A * B - B * A) := by
  simp only [mul_sub]
  abel

/-- Coefficient readout of the CCR-reduced triple; not an octonion associator. -/
def coefficientTriple (h : ℂ) (A B C : Coeff) : Coeff :=
  (Complex.I * h) • (omega B C • A + omega C A • B + omega A B • C)

/-- Every cubic operator term cancels, yielding an actual linear bi-twistor. -/
theorem quantize_triple (h : ℂ) (A B C : Coeff) :
    operatorTriple (quantize h A) (quantize h B) (quantize h C) =
      quantize h (coefficientTriple h A B C) := by
  rw [operatorTriple_commutators]
  rw [alternating_factor]
  rw [quantize_commutator, quantize_commutator, quantize_commutator]
  simp [coefficientTriple, Algebra.mul_smul_comm, smul_add,
    smul_smul, mul_assoc]

/-- On coefficient triples the displayed deformation vanishes at `h = 0`. -/
theorem coefficientTriple_zero (A B C : Coeff) : coefficientTriple 0 A B C = 0 := by
  simp [coefficientTriple]

/-! ## Signed homogeneous modes

The polynomial representation above has only nonnegative total degrees. The
following Laurent carrier has exponent vectors in `Fin 4 → ℤ`, so its
homogeneous modes also include negative degrees. The coordinate and derivative
operators still act by multiplication and differentiation in a genuinely
noncommutative endomorphism ring. This supplies the signed grading needed for
the projective-weight arithmetic, without identifying it with analytic sheaf
cohomology. -/

abbrev LaurentExponent := Fin 4 → ℤ
abbrev LaurentCarrier := AddMonoidAlgebra ℂ LaurentExponent
abbrev LaurentOperator := Module.End ℂ LaurentCarrier

/-- Exponent vector of the `i`th coordinate. -/
def LaurentUnitExponent (i : Fin 4) : LaurentExponent := Pi.single i 1

/-- Laurent monomial with an arbitrary signed exponent vector. -/
def LaurentMonomial (m : LaurentExponent) (c : ℂ) : LaurentCarrier :=
  AddMonoidAlgebra.single m c

/-- Multiplication by the `i`th Laurent coordinate. -/
def LaurentCoordinate (i : Fin 4) : LaurentOperator :=
  LinearMap.mulLeft ℂ (LaurentMonomial (LaurentUnitExponent i) 1)

/-- Formal derivative on a Laurent monomial, extended linearly to finite sums.
The integer exponent is used as the coefficient, so negative powers obey the
usual derivative rule. -/
def LaurentPartial (i : Fin 4) : LaurentCarrier →ₗ[ℂ] LaurentCarrier :=
  (Finsupp.linearCombination ℂ
    (fun m : LaurentExponent =>
      (m i : ℂ) • LaurentMonomial (m - LaurentUnitExponent i) 1)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

/-- The coordinate/derivative operators satisfy the signed monomial rules. -/
theorem LaurentCoordinate_apply_monomial (i : Fin 4)
    (m : LaurentExponent) (c : ℂ) :
    LaurentCoordinate i (LaurentMonomial m c) =
      LaurentMonomial (LaurentUnitExponent i + m) c := by
  simp [LaurentCoordinate, LaurentMonomial, LaurentUnitExponent,
    AddMonoidAlgebra.single_mul_single]

theorem LaurentPartial_apply_monomial (i : Fin 4)
    (m : LaurentExponent) (c : ℂ) :
    LaurentPartial i (LaurentMonomial m c) =
      (m i : ℂ) • LaurentMonomial (m - LaurentUnitExponent i) c := by
  simp [LaurentPartial, LaurentMonomial, LaurentUnitExponent,
    Finsupp.linearCombination_single, smul_smul, mul_comm]

/-- Holomorphic-polarization conjugate coordinate `-h ∂ᵢ` on Laurent modes. -/
def LaurentW (h : ℂ) (i : Fin 4) : LaurentOperator :=
  -h • LaurentPartial i

/-- A Laurent monomial has signed homogeneous degree equal to the sum of its
integer exponents. -/
def LaurentDegree (m : LaurentExponent) : ℤ := ∑ i : Fin 4, m i

/-- The Weyl-ordered Euler operator acts on every signed Laurent monomial by
`-(2 degree + 4) h`. The `4h` shift is derived from the four coordinate
commutators in the noncommutative endomorphism ring. -/
theorem Laurent_weylOrdering_degree_eigenvalue (h : ℂ)
    (m : LaurentExponent) (c : ℂ) :
    (∑ i : Fin 4,
      (LaurentCoordinate i * LaurentW h i + LaurentW h i * LaurentCoordinate i))
        (LaurentMonomial m c) =
      (-((2 : ℂ) * (LaurentDegree m : ℂ) + 4) * h) •
        LaurentMonomial m c := by
  classical
  have hshift (i : Fin 4) :
      LaurentUnitExponent i + m - LaurentUnitExponent i = m := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [LaurentUnitExponent]
    · simp [LaurentUnitExponent, hji, Ne.symm hji]
  have hunit (i : Fin 4) :
      LaurentUnitExponent i + (m - LaurentUnitExponent i) = m := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [LaurentUnitExponent]
    · simp [LaurentUnitExponent, hji, Ne.symm hji]
  have hfirst (i : Fin 4) :
      LaurentCoordinate i (LaurentW h i (LaurentMonomial m c)) =
        ((-h) * (m i : ℂ)) • LaurentMonomial m c := by
    simp only [LaurentW, LinearMap.smul_apply, LinearMap.neg_apply,
      LaurentPartial_apply_monomial, map_smul, LaurentCoordinate_apply_monomial]
    rw [hunit]
    simp [smul_smul, mul_comm]
  have hsecond (i : Fin 4) :
      LaurentW h i (LaurentCoordinate i (LaurentMonomial m c)) =
        ((-h) * ((m i : ℂ) + 1)) • LaurentMonomial m c := by
    simp only [LaurentW, LinearMap.smul_apply, LinearMap.neg_apply,
      LaurentCoordinate_apply_monomial, LaurentPartial_apply_monomial]
    rw [hshift]
    have heval : (LaurentUnitExponent i + m) i = (m i : ℤ) + 1 := by
      simp [LaurentUnitExponent]
      omega
    rw [heval]
    push_cast
    simp [smul_smul, mul_comm]
  have hterm (i : Fin 4) :
      (LaurentCoordinate i * LaurentW h i + LaurentW h i * LaurentCoordinate i)
          (LaurentMonomial m c) =
        (-(2 * (m i : ℂ) + 1) * h) • LaurentMonomial m c := by
    rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply,
      hfirst, hsecond]
    rw [← add_smul]
    congr 1
    ring
  change (∑ i : Fin 4,
      (LaurentCoordinate i * LaurentW h i + LaurentW h i * LaurentCoordinate i)
        (LaurentMonomial m c)) = _
  simp_rw [hterm]
  calc
    _ = (∑ i : Fin 4, (-(2 * (m i : ℂ) + 1) * h)) • LaurentMonomial m c := by
      rw [Finset.sum_smul]
    _ = (-((2 : ℂ) * (LaurentDegree m : ℂ) + 4) * h) •
          LaurentMonomial m c := by
      congr 1
      simp [LaurentDegree, Fin.sum_univ_four]
      ring

/-- At nonzero central parameter, the signed degree eigenvalue condition is
equivalent to the integer projective weight law `n = -2h - 2`. This is only
the algebraic weight relation; no sheaf cohomology group is asserted. -/
theorem signed_penrose_weight_iff {hbar helicity : ℂ} (hh : hbar ≠ 0)
    (n : ℤ) :
    -((2 : ℂ) * (n : ℂ) + 4) * hbar = (4 * helicity) * hbar ↔
      (n : ℂ) = -2 * helicity - 2 := by
  constructor
  · intro heq
    have hzero : (2 * ((n : ℂ) + 2 + 2 * helicity)) * hbar = 0 := by
      calc
        (2 * ((n : ℂ) + 2 + 2 * helicity)) * hbar =
            -(( -((2 : ℂ) * (n : ℂ) + 4) * hbar) - (4 * helicity) * hbar) := by ring
        _ = 0 := by rw [heq]; ring
    rcases mul_eq_zero.mp hzero with hfactor | hh'
    · have hsum : (n : ℂ) + 2 + 2 * helicity = 0 := by
        rcases mul_eq_zero.mp hfactor with htwo | hsum
        · norm_num at htwo
        · exact hsum
      linear_combination hsum
    · exact (hh hh').elim
  · intro hn
    rw [hn]
    ring

end InfoGeometry.Twistor.PenrosePolynomialCCR
