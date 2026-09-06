import InfoGeometry.Topology.SymbolicLatentQuotientOrbitClosureTopCat
import InfoGeometry.Topology.SymbolicLatentQuotientFlowHomeomorph

/-!
# Restricted flow homeomorphisms on quotient orbit closures

The quotient flow owner proves that a time slice maps an orbit closure onto
the orbit closure of the transported base point.  This owner packages that
set-level fact as a native `Homeomorph` between the corresponding closed
subspaces.  The inverse is the negative-time slice.
-/

namespace InfoGeometry.Topology

noncomputable section

def SymbolicLatentFlowQuotient.orbitClosureFlowHomeomorph
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) (t : ℝ) :
    SymbolicLatentOrbitClosure K q ≃ₜ
      SymbolicLatentOrbitClosure K (K.act t q) where
  toFun := fun y =>
    ⟨K.act t y.1, by
      rw [← K.actHomeomorph_image_orbitClosure t q]
      exact ⟨y.1, y.2, rfl⟩⟩
  invFun := fun y =>
    ⟨K.act (-t) y.1, by
      have hy :
          K.act (-t) y.1 ∈
            K.orbitClosure (K.act (-t) (K.act t q)) := by
        rw [← K.actHomeomorph_image_orbitClosure (-t) (K.act t q)]
        exact ⟨y.1, y.2, rfl⟩
      have hzero : K.act (-t) (K.act t q) = q := by
        calc
          K.act (-t) (K.act t q) = K.act (-t + t) q :=
            (K.act_add (-t) t q).symm
          _ = q := by rw [neg_add_cancel, K.act_zero]
      rwa [hzero] at hy⟩
  left_inv := by
    intro y
    apply Subtype.ext
    dsimp
    calc
      K.act (-t) (K.act t y.1) = K.act (-t + t) y.1 :=
        (K.act_add (-t) t y.1).symm
      _ = y.1 := by rw [neg_add_cancel, K.act_zero]
  right_inv := by
    intro y
    apply Subtype.ext
    dsimp
    calc
      K.act t (K.act (-t) y.1) = K.act (t + -t) y.1 :=
        (K.act_add t (-t) y.1).symm
      _ = y.1 := by rw [add_neg_cancel, K.act_zero]
  continuous_toFun :=
    ((K.actHomeomorph t).continuous_toFun.comp continuous_subtype_val).subtype_mk
      (fun y => by
        rw [← K.actHomeomorph_image_orbitClosure t q]
        exact ⟨y.1, y.2, rfl⟩)
  continuous_invFun :=
    ((K.actHomeomorph (-t)).continuous_toFun.comp continuous_subtype_val).subtype_mk
      (fun y => by
        have hy :
            K.act (-t) y.1 ∈
              K.orbitClosure (K.act (-t) (K.act t q)) := by
          rw [← K.actHomeomorph_image_orbitClosure (-t) (K.act t q)]
          exact ⟨y.1, y.2, rfl⟩
        have hzero : K.act (-t) (K.act t q) = q := by
          calc
            K.act (-t) (K.act t q) = K.act (-t + t) q :=
              (K.act_add (-t) t q).symm
            _ = q := by rw [neg_add_cancel, K.act_zero]
        rwa [hzero] at hy)

@[simp] theorem SymbolicLatentFlowQuotient.orbitClosureFlowHomeomorph_apply
    {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
    {Φ : SymbolicLatentModularFlow X}
    (K : SymbolicLatentFlowQuotient X Q Φ) (q : Q) (t : ℝ)
    (y : SymbolicLatentOrbitClosure K q) :
    K.orbitClosureFlowHomeomorph q t y =
      ⟨K.act t y.1, by
        rw [← K.actHomeomorph_image_orbitClosure t q]
        exact ⟨y.1, y.2, rfl⟩⟩ :=
  rfl

end
end InfoGeometry.Topology
