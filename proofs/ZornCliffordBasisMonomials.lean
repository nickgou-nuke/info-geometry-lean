import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Combinatorics.Colex
import proofs.CanonicalZornCliffordIsomorphism

/-!
# Cayley--Dickson Zorn basis and Clifford monomials

This module records both the null coordinate basis of the canonical Zorn
carrier and the historical Cayley--Dickson basis

`{1, i, j, k, ℓ, ℓi, ℓj, ℓk}`.

In the present Zorn convention, with upper/lower nilpotents `E_r`, `F_r`,
the latter basis is

`{I, E₀-F₀, E₁-F₁, E₂-F₂, ℓ, Q₀, Q₁, Q₂}`,

where `Q_r = E_r + F_r` and `ℓ * (E_r - F_r) = Q_r`.

The module also proves the general gamma anticommutator and defines canonical
ordered operator monomials.  Linear independence of all 256 monomials remains
the next PBW-style certificate.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace ZornCliffordBasisMonomials

open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open CanonicalZornFiveGradedClosure
open SplitOctonionBraidSU3
open Module

/-! ## The null coordinate basis -/

def coordinateZornBasis : Basis (Fin 8) ℂ Vector8 :=
  Basis.ofEquivFun (copyLinearEquivCoordinates TrialitySector.vector)

@[simp] theorem coordinateZornBasis_coordinates (i : Fin 8) :
    copyLinearEquivCoordinates TrialitySector.vector (coordinateZornBasis i) =
      Pi.single i 1 := by
  simp [coordinateZornBasis, Basis.coe_ofEquivFun]

/-! ## Change of coordinates to the Sage/Cayley--Dickson basis -/

/-- Synthesize standard Zorn coordinates from coefficients in the ordered
Cayley--Dickson basis `{1,i,j,k,ℓ,ℓi,ℓj,ℓk}`. -/
def cayleyToCoordinates (x : Fin 8 → ℂ) : Fin 8 → ℂ := fun i =>
  match i with
  | ⟨0, _⟩ => x 0 + x 4
  | ⟨1, _⟩ => x 1 + x 5
  | ⟨2, _⟩ => x 2 + x 6
  | ⟨3, _⟩ => x 3 + x 7
  | ⟨4, _⟩ => -x 1 + x 5
  | ⟨5, _⟩ => -x 2 + x 6
  | ⟨6, _⟩ => -x 3 + x 7
  | ⟨7, _⟩ => x 0 - x 4

/-- Recover Cayley--Dickson coefficients from standard Zorn coordinates. -/
def coordinatesToCayley (y : Fin 8 → ℂ) : Fin 8 → ℂ := fun i =>
  match i with
  | ⟨0, _⟩ => (y 0 + y 7) / 2
  | ⟨1, _⟩ => (y 1 - y 4) / 2
  | ⟨2, _⟩ => (y 2 - y 5) / 2
  | ⟨3, _⟩ => (y 3 - y 6) / 2
  | ⟨4, _⟩ => (y 0 - y 7) / 2
  | ⟨5, _⟩ => (y 1 + y 4) / 2
  | ⟨6, _⟩ => (y 2 + y 5) / 2
  | ⟨7, _⟩ => (y 3 + y 6) / 2

/-- The explicit invertible Hadamard change of coordinates between the null
Zorn basis and the Cayley--Dickson basis. -/
def cayleyCoordinateEquiv : (Fin 8 → ℂ) ≃ₗ[ℂ] (Fin 8 → ℂ) where
  toFun := cayleyToCoordinates
  invFun := coordinatesToCayley
  map_add' x y := by
    funext i
    fin_cases i <;> simp [cayleyToCoordinates] <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp [cayleyToCoordinates] <;> ring
  left_inv x := by
    funext i
    fin_cases i <;> simp [cayleyToCoordinates, coordinatesToCayley] <;> ring
  right_inv y := by
    funext i
    fin_cases i <;> simp [cayleyToCoordinates, coordinatesToCayley] <;> ring

def sageCayleySynthesis : (Fin 8 → ℂ) ≃ₗ[ℂ] Vector8 :=
  cayleyCoordinateEquiv.trans
    (copyLinearEquivCoordinates TrialitySector.vector).symm

/-- The exact Sage/Cayley--Dickson basis on the typed Zorn vector carrier. -/
def sageZornBasis : Basis (Fin 8) ℂ Vector8 :=
  Basis.ofEquivFun sageCayleySynthesis.symm

@[simp] theorem sageZornBasis_coordinates (i : Fin 8) :
    copyLinearEquivCoordinates TrialitySector.vector (sageZornBasis i) =
      cayleyToCoordinates (Pi.single i 1) := by
  simp [sageZornBasis, Basis.coe_ofEquivFun, sageCayleySynthesis,
    cayleyCoordinateEquiv]

/-! ## Identification with `{1,i,j,k,ℓ,ℓi,ℓj,ℓk}` -/

def cayleyImaginary (k : Fin 3) : Zorn := zornSub (E_k k) (F_k k)

def sageCayleyVector (i : Fin 8) : Vector8 :=
  match i with
  | ⟨0, _⟩ => ⟨I_zorn⟩
  | ⟨1, _⟩ => ⟨cayleyImaginary 0⟩
  | ⟨2, _⟩ => ⟨cayleyImaginary 1⟩
  | ⟨3, _⟩ => ⟨cayleyImaginary 2⟩
  | ⟨4, _⟩ => ⟨ell⟩
  | ⟨5, _⟩ => ⟨Q_k 0⟩
  | ⟨6, _⟩ => ⟨Q_k 1⟩
  | ⟨7, _⟩ => ⟨Q_k 2⟩

theorem sageZornBasis_eq_cayleyVector (i : Fin 8) :
    sageZornBasis i = sageCayleyVector i := by
  apply (copyLinearEquivCoordinates TrialitySector.vector).injective
  rw [sageZornBasis_coordinates]
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [sageCayleyVector, cayleyToCoordinates, cayleyImaginary,
      copyLinearEquivCoordinates, copyEquivCoordinates, zornCoordinates,
      I_zorn, ell, Q_k, E_k, F_k, zornSub, e_k]

/-- In the Zorn convention, left multiplication by the split unit sends the
imaginary generator `E_k-F_k` to `E_k+F_k`. -/
theorem ell_mul_cayleyImaginary (k : Fin 3) :
    zornMul ell (cayleyImaginary k) = Q_k k := by
  apply zorn_ext
  · fin_cases k <;> simp [ell, cayleyImaginary, zornMul, zornSub, E_k,
      F_k, Q_k, e_k, dot3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [ell, cayleyImaginary, zornMul, zornSub, E_k, F_k, Q_k,
        e_k, cross3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [ell, cayleyImaginary, zornMul, zornSub, E_k, F_k, Q_k,
        e_k, cross3]
  · fin_cases k <;> simp [ell, cayleyImaginary, zornMul, zornSub, E_k,
      F_k, Q_k, e_k, dot3]

theorem cayleyImaginary_sq (k : Fin 3) :
    zornMul (cayleyImaginary k) (cayleyImaginary k) =
      zornSmul (-1) I_zorn := by
  apply zorn_ext
  · fin_cases k <;> simp [cayleyImaginary, zornMul, zornSub, E_k,
      F_k, I_zorn, zornSmul, e_k, dot3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [cayleyImaginary, zornMul, zornSub, E_k, F_k, I_zorn,
        zornSmul, e_k, cross3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [cayleyImaginary, zornMul, zornSub, E_k, F_k, I_zorn,
        zornSmul, e_k, cross3]
  · fin_cases k <;> simp [cayleyImaginary, zornMul, zornSub, E_k,
      F_k, I_zorn, zornSmul, e_k, dot3]

theorem ell_sq : zornMul ell ell = I_zorn := by
  apply zorn_ext
  · simp [ell, zornMul, I_zorn, dot3]
  · funext i
    fin_cases i <;> simp [ell, zornMul, I_zorn, cross3]
  · funext i
    fin_cases i <;> simp [ell, zornMul, I_zorn, cross3]
  · simp [ell, zornMul, I_zorn, dot3]

/-! ## Gamma operators and ordered Clifford monomials -/

def basisGamma (i : Fin 8) : Module.End ℂ DiracSpinor16 :=
  diracGamma (sageZornBasis i)

theorem diracGamma_anticommutator (V W : Vector8) :
    diracGamma V * diracGamma W + diracGamma W * diracGamma V =
      algebraMap ℂ (Module.End ℂ DiracSpinor16) (zornPolar V.val W.val) := by
  apply LinearMap.ext
  intro Ψ
  apply Prod.ext
  · apply ZornCopy.ext
    simpa [diracGamma, copy_add_val, copy_smul_val] using
      clifford_polarized_plus V W Ψ.1
  · apply ZornCopy.ext
    simpa [diracGamma, copy_add_val, copy_smul_val] using
      clifford_polarized_minus V W Ψ.2

theorem basisGamma_anticommutator (i j : Fin 8) :
    basisGamma i * basisGamma j + basisGamma j * basisGamma i =
      algebraMap ℂ (Module.End ℂ DiracSpinor16)
        (zornPolar (sageZornBasis i).val (sageZornBasis j).val) := by
  exact diracGamma_anticommutator (sageZornBasis i) (sageZornBasis j)

/-- Canonical noncommutative product, ordered by the natural order on `Fin 8`.
Using `List.prod` is essential: `Finset.prod` would incorrectly demand a
commutative multiplication on endomorphisms. -/
def cliffordMonomial (I : Finset (Fin 8)) : Module.End ℂ DiracSpinor16 :=
  ((I.sort (· ≤ ·)).map basisGamma).prod

@[simp] theorem cliffordMonomial_empty : cliffordMonomial ∅ = 1 := by
  simp [cliffordMonomial]

/-! ## A simultaneous eigenspace certificate for the 256 monomials -/

/-- The first four Cayley generators square to `+1`; the last four square to
`-1` in the gamma convention induced by the Zorn norm. -/
def cayleySign (i : Fin 8) : ℂ := if i.1 < 4 then 1 else -1

theorem sageZornBasis_polar (i j : Fin 8) :
    zornPolar (sageZornBasis i).val (sageZornBasis j).val =
      if i = j then 2 * cayleySign i else 0 := by
  rw [sageZornBasis_eq_cayleyVector, sageZornBasis_eq_cayleyVector]
  fin_cases i <;> fin_cases j <;>
    simp [sageCayleyVector, cayleyImaginary, zornPolar, zornNorm, zornAdd,
      I_zorn, ell, Q_k, E_k, F_k, zornSub, e_k, dot3, cayleySign] <;> ring

theorem basisGamma_sq (i : Fin 8) :
    basisGamma i * basisGamma i =
      algebraMap ℂ (Module.End ℂ DiracSpinor16) (cayleySign i) := by
  rw [basisGamma, diracGamma_sq, vectorQuadratic_apply]
  rw [sageZornBasis_eq_cayleyVector]
  fin_cases i <;>
    simp [sageCayleyVector, cayleyImaginary, vectorNorm, zornNorm,
      I_zorn, ell, Q_k, E_k, F_k, zornSub, e_k, dot3, cayleySign]

theorem basisGamma_anticommute {i j : Fin 8} (hij : i ≠ j) :
    basisGamma i * basisGamma j = -(basisGamma j * basisGamma i) := by
  have h := basisGamma_anticommutator i j
  rw [sageZornBasis_polar, if_neg hij] at h
  have hzero :
      basisGamma i * basisGamma j + basisGamma j * basisGamma i = 0 := by
    simpa using h
  exact eq_neg_of_add_eq_zero_left hzero

end ZornCliffordBasisMonomials

end noncomputable section
