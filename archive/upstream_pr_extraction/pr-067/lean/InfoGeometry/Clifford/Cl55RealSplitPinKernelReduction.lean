import InfoGeometry.Clifford.Cl55RealSplitPinAction

namespace InfoGeometry.Clifford.Clifford55

/-!
# Kernel reduction for the real split-Pin action

This file identifies the kernel condition with pointwise triviality of the
twisted adjoint action on the embedded Clifford vector space.  It does not
classify the resulting centralizer.
-/

theorem realSplitPinOrthogonalAction_mem_kernel_iff
    (g : realSplitPin55) :
    g ∈ (realSplitPinOrthogonalAction).ker ↔
      ∀ v : V55, realSplitPinTwistedAdj g v = ι55 v := by
  constructor
  · intro hg v
    have hgroup : realSplitPinOrthogonalAction g = 1 := hg
    have hlinear :
        (realSplitPinOrthogonalAction g).1 =
          (1 : orthogonalGroup55).1 :=
      congrArg Subtype.val hgroup
    have hv := congrArg (fun f : V55 ≃ₗ[ℝ] V55 => f v) hlinear
    change realSplitPinTwistedAction g v = v at hv
    rw [← realSplitPinTwistedAction_apply_ι]
    simpa using congrArg (fun x : V55 => ι55 x) hv
  · intro h
    change realSplitPinOrthogonalAction g = 1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply ι55_injective
    change ι55 (realSplitPinTwistedAction g v) = ι55 v
    rw [realSplitPinTwistedAction_apply_ι]
    exact h v

theorem realSplitPin_involute_eq_or_neg
    (x : Cl55ˣ) (hx : x ∈ realSplitPin55) :
    CliffordAlgebra.involute (x : Cl55) = (x : Cl55) ∨
      CliffordAlgebra.involute (x : Cl55) = -(x : Cl55) := by
  change x ∈ realSplitPin55 at hx
  induction hx using Subgroup.closure_induction'' with
  | mem x hx =>
      obtain ⟨v, _, hv⟩ := hx
      right
      simpa [hv] using (CliffordAlgebra.involute_ι (Q := Q55) v)
  | inv_mem x hx =>
      obtain ⟨v, _, hv⟩ := hx
      right
      change CliffordAlgebra.involute (↑(x⁻¹) : Cl55) =
        -(↑(x⁻¹) : Cl55)
      have hinv_mul :
          CliffordAlgebra.involute (↑(x⁻¹) : Cl55) *
              CliffordAlgebra.involute (x : Cl55) = 1 := by
        have h := congrArg (CliffordAlgebra.involute (Q := Q55))
          (Units.inv_mul x : (↑(x⁻¹) : Cl55) * (x : Cl55) = 1)
        simpa only [map_mul, map_one] using h
      have hright :
          (x : Cl55) * (↑(x⁻¹) : Cl55) = 1 := Units.mul_inv x
      have hinv_mul' :
          CliffordAlgebra.involute (↑(x⁻¹) : Cl55) *
              (-(x : Cl55)) = 1 := by
        simpa [← hv, CliffordAlgebra.involute_ι] using hinv_mul
      have hprod :
          CliffordAlgebra.involute (↑(x⁻¹) : Cl55) * (x : Cl55) = -1 := by
        calc
          CliffordAlgebra.involute (↑(x⁻¹) : Cl55) * (x : Cl55) =
              -(CliffordAlgebra.involute (↑(x⁻¹) : Cl55) *
                (-(x : Cl55))) := by
                  noncomm_ring
          _ = -1 := by rw [hinv_mul']
      calc
        CliffordAlgebra.involute (↑(x⁻¹) : Cl55) =
            CliffordAlgebra.involute (↑(x⁻¹) : Cl55) * 1 := by simp
        _ = CliffordAlgebra.involute (↑(x⁻¹) : Cl55) *
            ((x : Cl55) * (↑(x⁻¹) : Cl55)) := by rw [hright]
        _ = (CliffordAlgebra.involute (↑(x⁻¹) : Cl55) *
            (x : Cl55)) * (↑(x⁻¹) : Cl55) := by noncomm_ring
        _ = (-1) * (↑(x⁻¹) : Cl55) := by rw [hprod]
        _ = -(↑(x⁻¹) : Cl55) := by simp
  | one =>
      left
      simp
  | mul y z _ _ hy hz =>
      rcases hy with hy | hy <;> rcases hz with hz | hz
      · left
        simpa [map_mul, Units.val_mul, hy, hz]
      · right
        simpa [map_mul, Units.val_mul, hy, hz]
      · right
        simpa [map_mul, Units.val_mul, hy, hz]
      · left
        simpa [map_mul, Units.val_mul, hy, hz]

theorem realSplitPin_kernel_twisted_commutation
    (g : realSplitPin55)
    (hg : g ∈ (realSplitPinOrthogonalAction).ker)
    (v : V55) :
    CliffordAlgebra.involute (Q := Q55) ((g : Cl55ˣ) : Cl55) * ι55 v =
      ι55 v * ((g : Cl55ˣ) : Cl55) := by
  have hfix : realSplitPinTwistedAdj g v = ι55 v :=
    (realSplitPinOrthogonalAction_mem_kernel_iff g).mp hg v
  have hunit :
      (↑((g : Cl55ˣ)⁻¹) : Cl55) * ((g : Cl55ˣ) : Cl55) = 1 := by
    exact Units.inv_mul (g : Cl55ˣ)
  calc
    CliffordAlgebra.involute (Q := Q55) ((g : Cl55ˣ) : Cl55) * ι55 v =
        (CliffordAlgebra.involute (Q := Q55) ((g : Cl55ˣ) : Cl55) *
          ι55 v * (↑((g : Cl55ˣ)⁻¹) : Cl55)) *
          ((g : Cl55ˣ) : Cl55) := by
      rw [mul_assoc, hunit]
      simp
    _ = realSplitPinTwistedAdj g v * ((g : Cl55ˣ) : Cl55) := by
      simp only [realSplitPinTwistedAdj]
    _ = ι55 v * ((g : Cl55ˣ) : Cl55) := by rw [hfix]

theorem realSplitPin_kernel_commutation_or_anticommutation
    (g : realSplitPin55)
    (hg : g ∈ (realSplitPinOrthogonalAction).ker)
    (v : V55) :
    ((g : Cl55ˣ) : Cl55) * ι55 v =
        ι55 v * ((g : Cl55ˣ) : Cl55) ∨
      ((g : Cl55ˣ) : Cl55) * ι55 v =
        -(ι55 v * ((g : Cl55ˣ) : Cl55)) := by
  rcases realSplitPin_involute_eq_or_neg (g : Cl55ˣ) g.property with h | h
  · left
    calc
      ((g : Cl55ˣ) : Cl55) * ι55 v =
          CliffordAlgebra.involute (Q := Q55) ((g : Cl55ˣ) : Cl55) * ι55 v := by
            rw [h]
      _ = ι55 v * ((g : Cl55ˣ) : Cl55) :=
        realSplitPin_kernel_twisted_commutation g hg v
  · right
    calc
      ((g : Cl55ˣ) : Cl55) * ι55 v =
          (-CliffordAlgebra.involute (Q := Q55) ((g : Cl55ˣ) : Cl55)) * ι55 v := by
            rw [h]
            noncomm_ring
      _ = -(CliffordAlgebra.involute (Q := Q55)
          ((g : Cl55ˣ) : Cl55) * ι55 v) := by
            noncomm_ring
      _ = -(ι55 v * ((g : Cl55ˣ) : Cl55)) := by
        rw [realSplitPin_kernel_twisted_commutation g hg v]

theorem realSplitPin_kernel_conjugation_eq_id_or_neg
    (g : realSplitPin55)
    (hg : g ∈ (realSplitPinOrthogonalAction).ker)
    (v : V55) :
    ((g : Cl55ˣ) : Cl55) * ι55 v *
        (↑((g : Cl55ˣ)⁻¹) : Cl55) = ι55 v ∨
      ((g : Cl55ˣ) : Cl55) * ι55 v *
          (↑((g : Cl55ˣ)⁻¹) : Cl55) = -(ι55 v) := by
  rcases realSplitPin_involute_eq_or_neg (g : Cl55ˣ) g.property with h | h
  · left
    have hcomm := realSplitPin_kernel_twisted_commutation g hg v
    calc
      ((g : Cl55ˣ) : Cl55) * ι55 v *
          (↑((g : Cl55ˣ)⁻¹) : Cl55) =
          (ι55 v * ((g : Cl55ˣ) : Cl55)) *
            (↑((g : Cl55ˣ)⁻¹) : Cl55) := by rw [← hcomm, h]
      _ = ι55 v := by
        rw [mul_assoc, Units.mul_inv]
        simp
  · right
    have hcomm := realSplitPin_kernel_twisted_commutation g hg v
    calc
      ((g : Cl55ˣ) : Cl55) * ι55 v *
          (↑((g : Cl55ˣ)⁻¹) : Cl55) =
          -(ι55 v * ((g : Cl55ˣ) : Cl55)) *
            (↑((g : Cl55ˣ)⁻¹) : Cl55) := by
              rw [← hcomm, h]
              noncomm_ring
      _ = -(ι55 v) := by
        rw [neg_mul, mul_assoc, Units.mul_inv]
        simp

end InfoGeometry.Clifford.Clifford55
