/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Clifford.Cl44Witt
import InfoGeometry.Clifford.KoszulFoundation
import InfoGeometry.Clifford.Cl55OperatorZ2Grading

/-!
# Gate 0 proposal: ordered real `Cl(4,4)` volume element

This scratch candidate uses the native `Cl44` carrier and its actual eight
quadratic-form basis vectors.  It does not identify Clifford multiplication
with matrix multiplication, and makes no dimension or nonzero-rank claim.
The `Cl(5,5)` import is used as the repository precedent for a native ordered
volume and involution-derived projector laws.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Clifford.Cl44VolumeElementCandidate

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Clifford.KoszulFoundation
open CliffordAlgebra

/-- The eight ordered orthogonal vectors defining the `Cl(4,4)` volume. -/
def volumeVector : Fin 8 → Fin 8 → ℝ
  | 0 => eVec 0
  | 1 => eVec 1
  | 2 => eVec 2
  | 3 => eVec 3
  | 4 => fVec 0
  | 5 => fVec 1
  | 6 => fVec 2
  | 7 => fVec 3

/-- The ordered basis-vector list `(e₀,e₁,e₂,e₃,f₀,f₁,f₂,f₃)`. -/
def volumeVectorList : List (Fin 8 → ℝ) := List.ofFn volumeVector

/-- Native ordered Clifford product for the split `(4,4)` carrier. -/
def volumeElement : Cl44 :=
  cliffordVolumeElement splitQ44 volumeVectorList

private theorem volumeVectorList_pairwise :
    volumeVectorList.Pairwise (QuadraticMap.IsOrtho splitQ44) := by
  rw [volumeVectorList, List.pairwise_ofFn]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [QuadraticMap.IsOrtho, volumeVector, eVec, fVec, splitQ44_apply]

/-- The ordered real `Cl(4,4)` volume element squares to `+1`. -/
theorem volumeElement_sq : volumeElement * volumeElement = 1 := by
  rw [volumeElement,
    cliffordVolumeElement_sq_of_pairwise volumeVectorList
      volumeVectorList_pairwise]
  norm_num [volumeVectorList, volumeVector, cliffordVolumeSquareScalar,
    splitQ44_apply, eVec, fVec, Pi.single_eq_same,
    Pi.single_eq_of_ne]

private theorem volumeList_even : Even volumeVectorList.length := by
  norm_num [volumeVectorList, volumeVector]

private theorem volume_anticommutes_of_even_pairwise
    (vectors : List (Fin 8 → ℝ))
    (hpair : vectors.Pairwise (QuadraticMap.IsOrtho splitQ44))
    (heven : Even vectors.length) {v : Fin 8 → ℝ} (hv : v ∈ vectors) :
    CliffordAlgebra.ι splitQ44 v * cliffordVolumeElement splitQ44 vectors =
      -(cliffordVolumeElement splitQ44 vectors * CliffordAlgebra.ι splitQ44 v) := by
  obtain ⟨s, t, rfl⟩ := List.mem_iff_append.mp hv
  have hsplit := List.pairwise_append.mp hpair
  have hvs : ∀ w ∈ s, QuadraticMap.IsOrtho splitQ44 v w := by
    intro w hw
    exact (hsplit.2.2 w hw v (by simp)).symm
  have hvt : ∀ w ∈ t, QuadraticMap.IsOrtho splitQ44 v w := by
    intro w hw
    exact (List.pairwise_cons.mp hsplit.2.1).1 w hw
  have hs := clifford_anticommute_listProduct v s hvs
  have ht := clifford_anticommute_listProduct v t hvt
  have hodd : Odd (s.length + t.length) := by
    rcases heven with ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    simp only [List.length_append, List.length_cons] at hk
    omega
  have hpow : (-1 : ℝ) ^ (s.length + t.length) = -1 := by
    rcases hodd with ⟨k, hk⟩
    rw [hk]
    simp [pow_add]
  simp only [cliffordVolumeElement, List.map_append, List.prod_append,
    List.map_cons, List.prod_cons]
  calc
    _ = ((CliffordAlgebra.ι splitQ44 v) *
        (List.map (CliffordAlgebra.ι splitQ44) s).prod) *
        ((CliffordAlgebra.ι splitQ44 v) *
          (List.map (CliffordAlgebra.ι splitQ44) t).prod) := by noncomm_ring
    _ = (((-1 : ℝ) ^ s.length •
        ((List.map (CliffordAlgebra.ι splitQ44) s).prod *
          CliffordAlgebra.ι splitQ44 v)) *
        ((-1 : ℝ) ^ t.length •
          ((List.map (CliffordAlgebra.ι splitQ44) t).prod *
            CliffordAlgebra.ι splitQ44 v))) := by rw [hs, ht]
    _ = (-1 : ℝ) ^ (s.length + t.length) •
        (((List.map (CliffordAlgebra.ι splitQ44) s).prod *
          CliffordAlgebra.ι splitQ44 v) *
          ((List.map (CliffordAlgebra.ι splitQ44) t).prod *
            CliffordAlgebra.ι splitQ44 v)) := by
          simp only [Algebra.smul_def]
          let X := (List.map (CliffordAlgebra.ι splitQ44) s).prod *
            CliffordAlgebra.ι splitQ44 v
          let Y := (List.map (CliffordAlgebra.ι splitQ44) t).prod *
            CliffordAlgebra.ι splitQ44 v
          have hcommX :
              X * algebraMap ℝ (CliffordAlgebra splitQ44) ((-1 : ℝ) ^ t.length) =
                algebraMap ℝ (CliffordAlgebra splitQ44) ((-1 : ℝ) ^ t.length) * X :=
            (Algebra.commutes ((-1 : ℝ) ^ t.length) X).symm
          have hscalar :
              algebraMap ℝ (CliffordAlgebra splitQ44) ((-1 : ℝ) ^ s.length) *
                  algebraMap ℝ (CliffordAlgebra splitQ44) ((-1 : ℝ) ^ t.length) =
                algebraMap ℝ (CliffordAlgebra splitQ44)
                  ((-1 : ℝ) ^ (s.length + t.length)) := by
            rw [← map_mul, ← pow_add]
          change algebraMap ℝ (CliffordAlgebra splitQ44) ((-1 : ℝ) ^ s.length) * X *
            (algebraMap ℝ (CliffordAlgebra splitQ44) ((-1 : ℝ) ^ t.length) * Y) =
              algebraMap ℝ (CliffordAlgebra splitQ44)
                ((-1 : ℝ) ^ (s.length + t.length)) * (X * Y)
          calc
            _ = algebraMap ℝ (CliffordAlgebra splitQ44) ((-1 : ℝ) ^ s.length) *
                (X * algebraMap ℝ (CliffordAlgebra splitQ44) ((-1 : ℝ) ^ t.length)) * Y := by
                  noncomm_ring
            _ = algebraMap ℝ (CliffordAlgebra splitQ44) ((-1 : ℝ) ^ s.length) *
                (algebraMap ℝ (CliffordAlgebra splitQ44) ((-1 : ℝ) ^ t.length) * X) * Y := by
                  rw [hcommX]
            _ = (algebraMap ℝ (CliffordAlgebra splitQ44) ((-1 : ℝ) ^ s.length) *
                algebraMap ℝ (CliffordAlgebra splitQ44) ((-1 : ℝ) ^ t.length)) *
                (X * Y) := by noncomm_ring
            _ = _ := by rw [hscalar]
    _ = -(((List.map (CliffordAlgebra.ι splitQ44) s).prod *
          CliffordAlgebra.ι splitQ44 v) *
          ((List.map (CliffordAlgebra.ι splitQ44) t).prod *
            CliffordAlgebra.ι splitQ44 v)) := by rw [hpow]; simp
    _ = -((List.map (CliffordAlgebra.ι splitQ44) s).prod *
          ((CliffordAlgebra.ι splitQ44 v) *
            (List.map (CliffordAlgebra.ι splitQ44) t).prod) *
          CliffordAlgebra.ι splitQ44 v) := by noncomm_ring

private theorem eVec_mem_volumeVectorList (i : Fin 4) : eVec i ∈ volumeVectorList := by
  fin_cases i <;> simp [volumeVectorList, volumeVector]

private theorem fVec_mem_volumeVectorList (i : Fin 4) : fVec i ∈ volumeVectorList := by
  fin_cases i <;> simp [volumeVectorList, volumeVector]

/-- The ordered `(4,4)` volume anticommutes with every positive generator.

The proof normalizes the concrete eight-factor product using only the
pairwise Clifford anticommutation relations and the positive generator square.
-/
theorem volumeElement_anticommutes_e (i : Fin 4) :
    volumeElement * e i = -(e i * volumeElement) := by
  have h := volume_anticommutes_of_even_pairwise volumeVectorList
    volumeVectorList_pairwise volumeList_even (eVec_mem_volumeVectorList i)
  calc
    volumeElement * e i = -(-(volumeElement * e i)) := by simp
    _ = -(e i * volumeElement) := by
      simpa [volumeElement, e] using congrArg Neg.neg h.symm

/-- The ordered `(4,4)` volume anticommutes with every negative generator. -/
theorem volumeElement_anticommutes_f (i : Fin 4) :
    volumeElement * f i = -(f i * volumeElement) := by
  have h := volume_anticommutes_of_even_pairwise volumeVectorList
    volumeVectorList_pairwise volumeList_even (fVec_mem_volumeVectorList i)
  calc
    volumeElement * f i = -(-(volumeElement * f i)) := by simp
    _ = -(f i * volumeElement) := by
      simpa [volumeElement, f] using congrArg Neg.neg h.symm

/-- The two chiral projectors are obtained from the genuine volume element. -/
def chiralInvolution : InfoGeometry.OperatorAlgebra.ChiralInvolution Cl44 where
  chi := volumeElement
  chi_sq := volumeElement_sq

def evenProjector : Cl44 := chiralInvolution.Pleft

def oddProjector : Cl44 := chiralInvolution.Pright

theorem evenProjector_idem : evenProjector * evenProjector = evenProjector :=
  chiralInvolution.Pleft_idem

theorem oddProjector_idem : oddProjector * oddProjector = oddProjector :=
  chiralInvolution.Pright_idem

theorem evenProjector_mul_oddProjector : evenProjector * oddProjector = 0 :=
  chiralInvolution.Pleft_mul_Pright

theorem oddProjector_mul_evenProjector : oddProjector * evenProjector = 0 :=
  chiralInvolution.Pright_mul_Pleft

theorem projectors_complement : evenProjector + oddProjector = 1 :=
  chiralInvolution.Pleft_add_Pright

end InfoGeometry.Clifford.Cl44VolumeElementCandidate

end
