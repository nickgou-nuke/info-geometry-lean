import InfoGeometry.Clifford.Cl55RealSplitPinKernelVolumeElimination
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55NativeCenterScalar
import InfoGeometry.Clifford.Cl55RealSplitPinVolume
import InfoGeometry.Clifford.Cl55RealSplitPinKernelNative

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Clifford.KoszulFoundation

noncomputable section

private theorem volume_anticommutes_of_even_pairwise
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (vectors : List M)
    (hpair : vectors.Pairwise (QuadraticMap.IsOrtho Q))
    (heven : Even vectors.length) {v : M} (hv : v ∈ vectors) :
    CliffordAlgebra.ι Q v * cliffordVolumeElement Q vectors =
      -(cliffordVolumeElement Q vectors * CliffordAlgebra.ι Q v) := by
  obtain ⟨s, t, rfl⟩ := List.mem_iff_append.mp hv
  have hsplit := List.pairwise_append.mp hpair
  have hvs : ∀ w ∈ s, QuadraticMap.IsOrtho Q v w := by
    intro w hw
    exact (hsplit.2.2 w hw v (by simp)).symm
  have hvt : ∀ w ∈ t, QuadraticMap.IsOrtho Q v w := by
    intro w hw
    exact (List.pairwise_cons.mp hsplit.2.1).1 w hw
  have hs := clifford_anticommute_listProduct v s hvs
  have ht := clifford_anticommute_listProduct v t hvt
  have hodd : Odd (s.length + t.length) := by
    rcases heven with ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    simp only [List.length_append, List.length_cons] at hk
    omega
  have hpow : (-1 : R) ^ (s.length + t.length) = -1 := by
    rcases hodd with ⟨k, hk⟩
    rw [hk]
    simp [pow_add]
  simp only [cliffordVolumeElement, List.map_append, List.prod_append,
    List.map_cons, List.prod_cons]
  calc
    _ = ((CliffordAlgebra.ι Q v) *
        (List.map (CliffordAlgebra.ι Q) s).prod) *
        ((CliffordAlgebra.ι Q v) *
          (List.map (CliffordAlgebra.ι Q) t).prod) := by noncomm_ring
    _ = (((-1 : R) ^ s.length •
        ((List.map (CliffordAlgebra.ι Q) s).prod *
          CliffordAlgebra.ι Q v)) *
        ((-1 : R) ^ t.length •
          ((List.map (CliffordAlgebra.ι Q) t).prod *
            CliffordAlgebra.ι Q v))) := by rw [hs, ht]
    _ = (-1 : R) ^ (s.length + t.length) •
        (((List.map (CliffordAlgebra.ι Q) s).prod *
          CliffordAlgebra.ι Q v) *
          ((List.map (CliffordAlgebra.ι Q) t).prod *
            CliffordAlgebra.ι Q v)) := by
          simp only [Algebra.smul_def]
          let X := (List.map (CliffordAlgebra.ι Q) s).prod *
            CliffordAlgebra.ι Q v
          let Y := (List.map (CliffordAlgebra.ι Q) t).prod *
            CliffordAlgebra.ι Q v
          have hcommX :
              X * algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ t.length) =
                algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ t.length) * X :=
            (Algebra.commutes ((-1 : R) ^ t.length) X).symm
          have hscalar :
              algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ s.length) *
                  algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ t.length) =
                algebraMap R (CliffordAlgebra Q)
                  ((-1 : R) ^ (s.length + t.length)) := by
            rw [← map_mul, ← pow_add]
          change algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ s.length) * X *
            (algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ t.length) * Y) =
              algebraMap R (CliffordAlgebra Q)
                ((-1 : R) ^ (s.length + t.length)) * (X * Y)
          calc
            _ = algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ s.length) *
                (X * algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ t.length)) * Y := by
                  noncomm_ring
            _ = algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ s.length) *
                (algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ t.length) * X) * Y := by
                  rw [hcommX]
            _ = (algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ s.length) *
                algebraMap R (CliffordAlgebra Q) ((-1 : R) ^ t.length)) *
                (X * Y) := by noncomm_ring
            _ = _ := by rw [hscalar]
    _ = -(((List.map (CliffordAlgebra.ι Q) s).prod *
          CliffordAlgebra.ι Q v) *
          ((List.map (CliffordAlgebra.ι Q) t).prod *
            CliffordAlgebra.ι Q v)) := by rw [hpow]; simp
    _ = -((List.map (CliffordAlgebra.ι Q) s).prod *
          ((CliffordAlgebra.ι Q v) *
            (List.map (CliffordAlgebra.ι Q) t).prod) *
          CliffordAlgebra.ι Q v) := by noncomm_ring

private theorem cl55WittVolumeList_pairwise :
    cl55WittVolumeList.Pairwise (QuadraticMap.IsOrtho Q55) := by
  rw [cl55WittVolumeList, List.pairwise_ofFn]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [QuadraticMap.isOrtho_def, cl55WittBasisFin, wittBasis,
      Q55_apply, e_pos, f_neg,
      Fin.sum_univ_succ] <;> native_decide

private theorem cl55WittVolumeList_even : Even cl55WittVolumeList.length := by
  norm_num [cl55WittVolumeList]

theorem cl55WittVolume_anticommutes_basis
    (i : Fin 10) :
    ι55 (cl55WittBasisFin i) * cl55WittVolume =
      -(cl55WittVolume * ι55 (cl55WittBasisFin i)) := by
  apply volume_anticommutes_of_even_pairwise
    (vectors := cl55WittVolumeList)
    (v := cl55WittBasisFin i)
  · exact cl55WittVolumeList_pairwise
  · exact cl55WittVolumeList_even
  · exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem cl55WittVolume_anticommutes_wittBasis
    (i : WittIndex) :
    ι55 (wittBasis i) * cl55WittVolume =
      -(cl55WittVolume * ι55 (wittBasis i)) := by
  apply volume_anticommutes_of_even_pairwise
    (vectors := cl55WittVolumeList)
    (v := wittBasis i)
  · rw [cl55WittVolumeList, List.pairwise_ofFn]
    exact List.pairwise_ofFn.mp cl55WittVolumeList_pairwise
  · exact cl55WittVolumeList_even
  · cases i with
    | inl i =>
        fin_cases i
        · exact List.mem_ofFn.mpr ⟨(0 : Fin 10), rfl⟩
        · exact List.mem_ofFn.mpr ⟨(1 : Fin 10), rfl⟩
        · exact List.mem_ofFn.mpr ⟨(2 : Fin 10), rfl⟩
        · exact List.mem_ofFn.mpr ⟨(3 : Fin 10), rfl⟩
        · exact List.mem_ofFn.mpr ⟨(4 : Fin 10), rfl⟩
    | inr i =>
        fin_cases i
        · exact List.mem_ofFn.mpr ⟨(5 : Fin 10), rfl⟩
        · exact List.mem_ofFn.mpr ⟨(6 : Fin 10), rfl⟩
        · exact List.mem_ofFn.mpr ⟨(7 : Fin 10), rfl⟩
        · exact List.mem_ofFn.mpr ⟨(8 : Fin 10), rfl⟩
        · exact List.mem_ofFn.mpr ⟨(9 : Fin 10), rfl⟩

theorem cl55WittVolume_anticommutes
    (v : V55) :
    ι55 v * cl55WittVolume = -(cl55WittVolume * ι55 v) := by
  have hv : v ∈ Submodule.span ℝ (Set.range wittBasis) := by
    rw [wittBasis_span_eq_top]
    trivial
  refine Submodule.span_induction (p := fun x _ =>
      ι55 x * cl55WittVolume = -(cl55WittVolume * ι55 x)) ?_ ?_ ?_ ?_ hv
  · rintro x ⟨i, rfl⟩
    exact cl55WittVolume_anticommutes_wittBasis i
  · simp
  · intro x y _ _ hx hy
    calc
      ι55 (x + y) * cl55WittVolume =
          (ι55 x + ι55 y) * cl55WittVolume := by rw [map_add]
      _ = ι55 x * cl55WittVolume + ι55 y * cl55WittVolume := by rw [add_mul]
      _ = -(cl55WittVolume * ι55 x) +
          -(cl55WittVolume * ι55 y) := by rw [hx, hy]
      _ = -(cl55WittVolume * ι55 (x + y)) := by
        rw [map_add, mul_add, neg_add]
  · intro r x _ hx
    calc
      ι55 (r • x) * cl55WittVolume =
          (r • ι55 x) * cl55WittVolume := by rw [map_smul]
      _ = r • (ι55 x * cl55WittVolume) := by rw [smul_mul_assoc]
      _ = r • (-(cl55WittVolume * ι55 x)) := by rw [hx]
      _ = -(cl55WittVolume * ι55 (r • x)) := by
        simp [map_smul, smul_neg]

theorem realSplitPin_kernel_pm_one
    (g : realSplitPin55)
    (hg : g ∈ (realSplitPinOrthogonalAction).ker) :
    (g : Cl55ˣ) = 1 ∨ (g : Cl55ˣ) = -1 := by
  rcases realSplitPin_involute_eq_or_neg (g : Cl55ˣ) g.property with hinv | hinv
  · exact realSplitPin_kernel_pm_one_of_center cl55SpinorAlgEquiv g
      (realSplitPin_kernel_mem_center_of_involute_eq g hg hinv)
  · exfalso
    exact realSplitPin_kernel_neg_involute_impossible_of_antivolume
      g hg hinv cl55WittVolumeUnit
      (fun v => by
        have hvolume := cl55WittVolume_anticommutes v
        have hvolume' :
            cl55WittVolume * ι55 v = -(ι55 v * cl55WittVolume) := by
          calc
            cl55WittVolume * ι55 v =
                -(-(cl55WittVolume * ι55 v)) := by simp
            _ = -(ι55 v * cl55WittVolume) := by rw [hvolume]
        calc
          (cl55WittVolumeUnit : Cl55) * ι55 v =
              cl55WittVolume * ι55 v := by
                rw [cl55WittVolumeUnit_coe]
          _ = -(ι55 v * cl55WittVolume) := hvolume'
          _ = -(ι55 v * (cl55WittVolumeUnit : Cl55)) := by
                rw [cl55WittVolumeUnit_coe])
      cl55WittVolume_involute (fun hz => cl55_center_scalar hz)

end

end InfoGeometry.Clifford.Clifford55
