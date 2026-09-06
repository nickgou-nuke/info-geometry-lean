import proofs.HestenesBivectorSelfDuality
import proofs.HestenesBivectorBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Dimensions of the self-dual bivector sectors

The explicit six-element real bivector basis consists of three Hodge pairs.
After base change to `ℂ`, projecting the first member of every pair gives
three independent vectors in each spectral range.  Complementarity and total
dimension six then force both complex dimensions to be three.
-/

noncomputable section
namespace HestenesBivectorSelfDualFinrank

set_option synthInstance.maxHeartbeats 100000

open HestenesCl14 HestenesCliffordCenter HestenesBivectorCarrier
open HestenesBivectorBasis HestenesBivectorSelfDuality

attribute [local instance high] Module.Free.of_divisionRing

def complexBivectorBasis : Module.Basis (Fin 6) ℂ ComplexBivector :=
  bivectorBasis.baseChange ℂ

def firstIndex (k : Fin 3) : Fin 6 := ⟨k, by omega⟩
def secondIndex (k : Fin 3) : Fin 6 := ⟨k + 3, by omega⟩

theorem hodgeBivector_val_eq_neg_omega_mul (B : Bivector) :
    (hodgeBivector B : Cl14) =
      -((spacetimePseudoscalar : Cl14) * B) := by
  rw [hodgeBivector_val, HestenesHodgeParityBridge.hodge, reverse_bivector]
  rw [neg_mul, omega_comm_bivector]

theorem hodge_basis_first (k : Fin 3) :
    hodgeBivector (basisBivector (firstIndex k)) =
      -basisBivector (secondIndex k) := by
  apply Subtype.ext
  rw [hodgeBivector_val_eq_neg_omega_mul]
  fin_cases k <;>
    simp [firstIndex, secondIndex, basisBivector, rawBivector,
      spacetimePseudoscalar_eq_volumeEven]

theorem hodge_basis_second (k : Fin 3) :
    hodgeBivector (basisBivector (secondIndex k)) =
      basisBivector (firstIndex k) := by
  have h := congrArg hodgeBivector (hodge_basis_first k)
  rw [map_neg, hodge_sq_bivector] at h
  exact (neg_injective h).symm

def firstComplexBivector (k : Fin 3) : ComplexBivector :=
  (1 : ℂ) ⊗ₜ[ℝ] basisBivector (firstIndex k)

def selfDualBasisVector (k : Fin 3) : selfDualProj.range :=
  ⟨selfDualProj (firstComplexBivector k), LinearMap.mem_range_self _ _⟩

def antiSelfDualBasisVector (k : Fin 3) : antiSelfDualProj.range :=
  ⟨antiSelfDualProj (firstComplexBivector k), LinearMap.mem_range_self _ _⟩

@[simp] theorem complexBasis_repr_tmul (i j : Fin 6) :
    complexBivectorBasis.repr
        ((1 : ℂ) ⊗ₜ[ℝ] basisBivector i) j = if i = j then 1 else 0 := by
  have hr : bivectorBasis.repr (basisBivector i) j =
      if i = j then 1 else 0 := by
    rw [← bivectorBasis_apply]
    have h := DFunLike.congr_fun (bivectorBasis.repr_self i) j
    by_cases hij : i = j
    · subst j
      simpa using h
    · simpa [hij, Ne.symm hij] using h
  change ((bivectorBasis.baseChange ℂ).repr
    ((1 : ℂ) ⊗ₜ[ℝ] basisBivector i)) j = _
  rw [Module.Basis.baseChange_repr_tmul]
  rw [hr]
  split <;> simp_all

theorem firstIndex_injective : Function.Injective firstIndex := by
  intro i j h
  apply Fin.ext
  simpa [firstIndex] using congrArg Fin.val h

theorem secondIndex_ne_firstIndex (i j : Fin 3) :
    secondIndex i ≠ firstIndex j := by
  intro h
  have := congrArg Fin.val h
  simp [secondIndex, firstIndex] at this
  omega

theorem complexHodge_first (k : Fin 3) :
    complexHodgeStar (firstComplexBivector k) =
      -((1 : ℂ) ⊗ₜ[ℝ] basisBivector (secondIndex k)) := by
  rw [firstComplexBivector, complexHodgeStar_tmul, hodge_basis_first]
  rw [TensorProduct.tmul_neg]

theorem selfDualBasisVector_formula (k : Fin 3) :
    (selfDualBasisVector k : ComplexBivector) =
      (2 : ℂ)⁻¹ •
        ((1 : ℂ) ⊗ₜ[ℝ] basisBivector (firstIndex k) +
          Complex.I • ((1 : ℂ) ⊗ₜ[ℝ] basisBivector (secondIndex k))) := by
  change selfDualProj (firstComplexBivector k) = _
  rw [selfDualProj_apply, firstComplexBivector,
    complexHodgeStar_tmul, hodge_basis_first, TensorProduct.tmul_neg]
  module

theorem antiSelfDualBasisVector_formula (k : Fin 3) :
    (antiSelfDualBasisVector k : ComplexBivector) =
      (2 : ℂ)⁻¹ •
        ((1 : ℂ) ⊗ₜ[ℝ] basisBivector (firstIndex k) -
          Complex.I • ((1 : ℂ) ⊗ₜ[ℝ] basisBivector (secondIndex k))) := by
  change antiSelfDualProj (firstComplexBivector k) = _
  rw [antiSelfDualProj_apply, firstComplexBivector,
    complexHodgeStar_tmul, hodge_basis_first, TensorProduct.tmul_neg]
  module

theorem selfDualBasisVector_linearIndependent :
    LinearIndependent ℂ selfDualBasisVector := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have hv : ∑ j, g j • (selfDualBasisVector j : ComplexBivector) = 0 := by
    exact congrArg Subtype.val hg
  have hrepr := congrArg complexBivectorBasis.repr hv
  have hc := congrArg (fun f : Fin 6 →₀ ℂ => f (firstIndex k)) hrepr
  simp only [map_sum, map_smul, map_zero] at hc
  simp only [selfDualBasisVector_formula, map_smul, map_add] at hc
  have hindex (j : Fin 3) : (firstIndex j = firstIndex k) = (j = k) := by
    apply propext
    constructor
    · intro h; exact firstIndex_injective h
    · exact congrArg firstIndex
  simp [hindex, secondIndex_ne_firstIndex] at hc
  exact hc

theorem antiSelfDualBasisVector_linearIndependent :
    LinearIndependent ℂ antiSelfDualBasisVector := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have hv : ∑ j, g j • (antiSelfDualBasisVector j : ComplexBivector) = 0 := by
    exact congrArg Subtype.val hg
  have hrepr := congrArg complexBivectorBasis.repr hv
  have hc := congrArg (fun f : Fin 6 →₀ ℂ => f (firstIndex k)) hrepr
  simp only [map_sum, map_smul, map_zero] at hc
  simp only [antiSelfDualBasisVector_formula, map_smul, map_sub] at hc
  have hindex (j : Fin 3) : (firstIndex j = firstIndex k) = (j = k) := by
    apply propext
    constructor
    · intro h; exact firstIndex_injective h
    · exact congrArg firstIndex
  simp [hindex, secondIndex_ne_firstIndex] at hc
  exact hc

theorem finrank_complexBivector : Module.finrank ℂ ComplexBivector = 6 := by
  rw [Module.finrank_eq_card_basis complexBivectorBasis]
  simp

theorem finrank_selfDual_range : Module.finrank ℂ selfDualProj.range = 3 := by
  have hplus : 3 ≤ Module.finrank ℂ selfDualProj.range := by
    simpa using selfDualBasisVector_linearIndependent.fintype_card_le_finrank
  have hminus : 3 ≤ Module.finrank ℂ antiSelfDualProj.range := by
    simpa using antiSelfDualBasisVector_linearIndependent.fintype_card_le_finrank
  have hsum : 6 = Module.finrank ℂ selfDualProj.range +
      Module.finrank ℂ antiSelfDualProj.range := by
    rw [← finrank_complexBivector, ← Module.finrank_prod]
    exact LinearEquiv.finrank_eq complexBivectorSpectralEquiv
  omega

theorem finrank_antiSelfDual_range :
    Module.finrank ℂ antiSelfDualProj.range = 3 := by
  have hplus : 3 ≤ Module.finrank ℂ selfDualProj.range := by
    simpa using selfDualBasisVector_linearIndependent.fintype_card_le_finrank
  have hminus : 3 ≤ Module.finrank ℂ antiSelfDualProj.range := by
    simpa using antiSelfDualBasisVector_linearIndependent.fintype_card_le_finrank
  have hsum : 6 = Module.finrank ℂ selfDualProj.range +
      Module.finrank ℂ antiSelfDualProj.range := by
    rw [← finrank_complexBivector, ← Module.finrank_prod]
    exact LinearEquiv.finrank_eq complexBivectorSpectralEquiv
  omega

theorem selfDual_finrank_packet :
    Module.finrank ℂ selfDualProj.range = 3 ∧
      Module.finrank ℂ antiSelfDualProj.range = 3 :=
  ⟨finrank_selfDual_range, finrank_antiSelfDual_range⟩

end HestenesBivectorSelfDualFinrank
end noncomputable section
