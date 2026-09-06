import InfoGeometry.Clifford.Cl55SpinBivectorImage
import InfoGeometry.Clifford.Cl55RealSplitPinVolumeAnticommutation

/-!
# Native bivector commutation with the `(5,5)` volume element

This owner isolates the theorem-safe part of chiral equivariance: native
Clifford bivectors commute with the even Witt volume.  It deliberately does
not identify an arbitrary `G₂` action with a spinor action, nor does it infer
chirality from a dimension count.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge

open CliffordAlgebra
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinBivectorImage
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.CliffordTower

abbrev SpinBivector55 := Cl55SpinBivectorImage.SpinBivector55

/-- The spinor-matrix image of the native Witt volume element. -/
def spinorWittVolume : SpinorMatrix 5 :=
  cl55SpinorAlgEquiv cl55WittVolume

private lemma foldl_mul_one_eq_prod {M : Type*} [Monoid M] (L : List M) :
    L.foldl (· * ·) 1 = L.prod := by
  have h (a : M) : L.foldl (· * ·) a = a * L.prod := by
    induction L generalizing a with
    | nil => simp
    | cons x xs ih =>
        simp only [List.foldl_cons, List.prod_cons, ih]
        rw [mul_assoc]
  have h1 := h 1
  rw [one_mul] at h1
  exact h1

private theorem cl55ToSplitCl55_map_volume :
    cl55ToSplitCl55 cl55WittVolume = orderedCliffordVolume55 := by
  have hmap (L : List V55) :
      cl55ToSplitCl55 ((L.map (ι55)).prod) =
        (L.map (fun v => cl55ToSplitCl55 (ι55 v))).prod := by
    induction L with
    | nil => simp
    | cons v L ih =>
        simp only [List.map_cons, List.prod_cons, map_mul]
        rw [ih]
  dsimp [cl55WittVolume, KoszulFoundation.cliffordVolumeElement, orderedCliffordVolume55]
  rw [hmap]
  rw [foldl_mul_one_eq_prod]
  have hfn : ((fun v => cl55ToSplitCl55 (ι55 v)) ∘ cl55WittBasisFin) = gammaBasisClifford55 := by
    funext i
    rw [Function.comp_apply, cl55ToSplitCl55_map_ι, q55ToSplit5_wittBasis]
    rfl
  rw [cl55WittVolumeList, List.map_ofFn, hfn]

theorem spinorWittVolume_eq_chirality55 :
    spinorWittVolume = chirality55 := by
  change cl55SpinorAlgEquiv.toAlgHom cl55WittVolume = chiralityMatrix
  rw [cl55SpinorAlgEquiv_toAlgHom_eq_representation]
  rw [cl55SpinorRepresentation]
  change spinorRepresentation 5 (cl55ToSplitCl55 cl55WittVolume) = chiralityMatrix
  rw [cl55ToSplitCl55_map_volume]
  exact orderedGammaVolume55_eq_chiralityMatrix

private theorem commutator_vector_commutes_volume (u v : V55) :
    ⁅ι55 u, ι55 v⁆ * cl55WittVolume =
      cl55WittVolume * ⁅ι55 u, ι55 v⁆ := by
  have hu := cl55WittVolume_anticommutes u
  have hv := cl55WittVolume_anticommutes v
  simp only [Ring.lie_def]
  rw [mul_sub, sub_mul]
  have huv : ι55 u * ι55 v * cl55WittVolume =
      cl55WittVolume * ι55 u * ι55 v := by
    calc
      ι55 u * ι55 v * cl55WittVolume =
          ι55 u * (ι55 v * cl55WittVolume) := by noncomm_ring
      _ = ι55 u * (-(cl55WittVolume * ι55 v)) := by rw [hv]
      _ = -((ι55 u * cl55WittVolume) * ι55 v) := by noncomm_ring
      _ = -((-(cl55WittVolume * ι55 u)) * ι55 v) := by rw [hu]
      _ = cl55WittVolume * ι55 u * ι55 v := by noncomm_ring
  have hvu : ι55 v * ι55 u * cl55WittVolume =
      cl55WittVolume * ι55 v * ι55 u := by
    calc
      ι55 v * ι55 u * cl55WittVolume =
          ι55 v * (ι55 u * cl55WittVolume) := by noncomm_ring
      _ = ι55 v * (-(cl55WittVolume * ι55 u)) := by rw [hu]
      _ = -((ι55 v * cl55WittVolume) * ι55 u) := by noncomm_ring
      _ = -((-(cl55WittVolume * ι55 v)) * ι55 u) := by rw [hv]
      _ = cl55WittVolume * ι55 v * ι55 u := by noncomm_ring
  rw [huv, hvu]
  noncomm_ring

theorem spinBivector_commutes_wittVolume (X : SpinBivector55) :
    (X : Cl55) * cl55WittVolume = cl55WittVolume * (X : Cl55) := by
  have hmem : ∀ (x : Cl55), x ∈ soLieAlgebra Q55 →
      x * cl55WittVolume = cl55WittVolume * x := by
    intro x hx
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem x hx =>
        rcases hx with ⟨⟨u, v⟩, rfl⟩
        exact commutator_vector_commutes_volume u v
    | zero => simp
    | add x y _ _ hx hy =>
        simp only [add_mul, mul_add] at *
        rw [hx, hy]
    | smul r x _ hx =>
        change algebraMap ℝ Cl55 r * x * cl55WittVolume =
          cl55WittVolume * (algebraMap ℝ Cl55 r * x)
        calc
          algebraMap ℝ Cl55 r * x * cl55WittVolume =
              algebraMap ℝ Cl55 r * (x * cl55WittVolume) := by rw [mul_assoc]
          _ = algebraMap ℝ Cl55 r * (cl55WittVolume * x) := by rw [hx]
          _ = (algebraMap ℝ Cl55 r * cl55WittVolume) * x := by rw [mul_assoc]
          _ = (cl55WittVolume * algebraMap ℝ Cl55 r) * x := by
            rw [Algebra.commutes]
          _ = cl55WittVolume * (algebraMap ℝ Cl55 r * x) := by rw [mul_assoc]
    | lie x y _ _ hx hy =>
        have hxy : x * y * cl55WittVolume =
            cl55WittVolume * (x * y) := by
          calc
            x * y * cl55WittVolume = x * (y * cl55WittVolume) := by noncomm_ring
            _ = x * (cl55WittVolume * y) := by rw [hy]
            _ = (x * cl55WittVolume) * y := by noncomm_ring
            _ = (cl55WittVolume * x) * y := by rw [hx]
            _ = cl55WittVolume * (x * y) := by noncomm_ring
        have hyx : y * x * cl55WittVolume =
            cl55WittVolume * (y * x) := by
          calc
            y * x * cl55WittVolume = y * (x * cl55WittVolume) := by noncomm_ring
            _ = y * (cl55WittVolume * x) := by rw [hx]
            _ = (y * cl55WittVolume) * x := by noncomm_ring
            _ = (cl55WittVolume * y) * x := by rw [hy]
            _ = cl55WittVolume * (y * x) := by noncomm_ring
        simp only [Ring.lie_def, mul_sub, sub_mul]
        rw [hxy, hyx]
  exact hmem (X : Cl55) X.property

theorem spinBivectorMatrix_commutes_spinorWittVolume (X : SpinBivector55) :
    spinBivectorMatrixLinear X * spinorWittVolume =
      spinorWittVolume * spinBivectorMatrixLinear X := by
  change cl55SpinorAlgEquiv (X : Cl55) *
      cl55SpinorAlgEquiv cl55WittVolume =
    cl55SpinorAlgEquiv cl55WittVolume * cl55SpinorAlgEquiv (X : Cl55)
  rw [← map_mul, ← map_mul, spinBivector_commutes_wittVolume X]

theorem spinBivectorMatrix_commutes_chirality55 (X : SpinBivector55) :
    spinBivectorMatrixLinear X * chirality55 =
      chirality55 * spinBivectorMatrixLinear X := by
  simpa only [spinorWittVolume_eq_chirality55] using
    spinBivectorMatrix_commutes_spinorWittVolume X

theorem spinBivectorMatrix_commutes_chiralPlusProjector (X : SpinBivector55) :
    spinBivectorMatrixLinear X * chiralPlusProjector =
      chiralPlusProjector * spinBivectorMatrixLinear X := by
  dsimp [chiralPlusProjector]
  have h := spinBivectorMatrix_commutes_chirality55 X
  simp [mul_add, add_mul, h]

theorem spinBivectorMatrix_commutes_chiralMinusProjector (X : SpinBivector55) :
    spinBivectorMatrixLinear X * chiralMinusProjector =
      chiralMinusProjector * spinBivectorMatrixLinear X := by
  dsimp [chiralMinusProjector]
  have h := spinBivectorMatrix_commutes_chirality55 X
  simp [mul_sub, sub_mul, h]

end InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
