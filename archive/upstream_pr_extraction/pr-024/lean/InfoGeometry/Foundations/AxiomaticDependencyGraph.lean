import Mathlib

namespace Audit

section HodgeKreinTriFacet

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

class Node0_KreinSpace (V : Type*) [AddCommGroup V] [Module ℝ V] where
  B : V → V → ℝ
  B_add_left : ∀ x y z, B (x + y) z = B x z + B y z
  B_smul_left : ∀ c x y, B (c • x) y = c * B x y
  B_comm : ∀ x y, B x y = B y x
  J : V →ₗ[ℝ] V
  J_sq : ∀ x, J (J x) = x
  J_adj : ∀ x y, B (J x) y = B x (J y)

class Node1_TriFacetOperator (V : Type*) [AddCommGroup V] [Module ℝ V] [Node0_KreinSpace V] where
  O : V →ₗ[ℝ] V
  O_cubed : ∀ x, O (O (O x)) = O x
  O_adj : ∀ x y, Node0_KreinSpace.B (O x) y = Node0_KreinSpace.B x (O y)

variable [Node0_KreinSpace V] [Node1_TriFacetOperator V]

noncomputable def exact_projector (x : V) : V :=
  (1 / 2 : ℝ) • (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) + Node1_TriFacetOperator.O x)

noncomputable def coexact_projector (x : V) : V :=
  (1 / 2 : ℝ) • (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) - Node1_TriFacetOperator.O x)

def harmonic_projector (x : V) : V :=
  x - Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x)

/-- `exact_projector` as a linear map. -/
noncomputable def exact_projector_lin : V →ₗ[ℝ] V where
  toFun := exact_projector
  map_add' x y := by
    unfold exact_projector
    simp only [map_add, smul_add]
    abel
  map_smul' r x := by
    unfold exact_projector
    simp only [map_smul, RingHom.id_apply, smul_add]
    rw [smul_comm r (1 / 2 : ℝ), smul_comm r (1 / 2 : ℝ)]

/-- `coexact_projector` as a linear map. -/
noncomputable def coexact_projector_lin : V →ₗ[ℝ] V where
  toFun := coexact_projector
  map_add' x y := by
    unfold coexact_projector
    simp only [map_add, smul_add, smul_sub]
    abel
  map_smul' r x := by
    unfold coexact_projector
    simp only [map_smul, RingHom.id_apply, smul_sub]
    rw [smul_comm r (1 / 2 : ℝ), smul_comm r (1 / 2 : ℝ)]

/-- `harmonic_projector` as a linear map. -/
def harmonic_projector_lin : V →ₗ[ℝ] V where
  toFun := harmonic_projector
  map_add' x y := by
    unfold harmonic_projector
    simp only [map_add, sub_eq_add_neg, neg_add]
    abel
  map_smul' r x := by
    unfold harmonic_projector
    simp only [map_smul, RingHom.id_apply, smul_sub]

theorem tri_facet_resolution (x : V) :
    exact_projector x + coexact_projector x + harmonic_projector x = x := by
  unfold exact_projector coexact_projector harmonic_projector
  rw [smul_add, smul_sub]
  let O := Node1_TriFacetOperator.O (V := V)
  have h :
      (1 / 2 : ℝ) • O (O x) + (1 / 2 : ℝ) • O x +
          ((1 / 2 : ℝ) • O (O x) - (1 / 2 : ℝ) • O x) =
        (1 / 2 : ℝ) • O (O x) + (1 / 2 : ℝ) • O (O x) := by
    abel
  rw [h, ← add_smul]
  have hhalf : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  rw [hhalf, one_smul]
  abel

lemma O_exact_projector (x : V) :
    Node1_TriFacetOperator.O (exact_projector x) = exact_projector x := by
  unfold exact_projector
  rw [LinearMap.map_smul, LinearMap.map_add, Node1_TriFacetOperator.O_cubed x, add_comm]

lemma OO_exact_projector (x : V) :
    Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (exact_projector x)) =
      exact_projector x := by
  rw [O_exact_projector x, O_exact_projector x]

lemma O_coexact_projector (x : V) :
    Node1_TriFacetOperator.O (coexact_projector x) = -coexact_projector x := by
  unfold coexact_projector
  rw [LinearMap.map_smul, LinearMap.map_sub, Node1_TriFacetOperator.O_cubed x]
  have h :
      Node1_TriFacetOperator.O x - Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) =
        -(Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) -
          Node1_TriFacetOperator.O x) := by
    abel
  rw [h, smul_neg]

lemma OO_coexact_projector (x : V) :
    Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (coexact_projector x)) =
      coexact_projector x := by
  rw [O_coexact_projector x, LinearMap.map_neg, O_coexact_projector x, neg_neg]

lemma O_harmonic_projector (x : V) :
    Node1_TriFacetOperator.O (harmonic_projector x) = 0 := by
  unfold harmonic_projector
  rw [LinearMap.map_sub, Node1_TriFacetOperator.O_cubed x, sub_self]

lemma OO_harmonic_projector (x : V) :
    Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (harmonic_projector x)) = 0 := by
  rw [O_harmonic_projector x, LinearMap.map_zero]

theorem exact_projector_idempotent (x : V) :
    exact_projector (exact_projector x) = exact_projector x := by
  change
    (1 / 2 : ℝ) •
        (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (exact_projector x)) +
          Node1_TriFacetOperator.O (exact_projector x)) =
      exact_projector x
  rw [OO_exact_projector x, O_exact_projector x, smul_add, ← add_smul]
  norm_num

theorem coexact_projector_idempotent (x : V) :
    coexact_projector (coexact_projector x) = coexact_projector x := by
  change
    (1 / 2 : ℝ) •
        (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (coexact_projector x)) -
          Node1_TriFacetOperator.O (coexact_projector x)) =
      coexact_projector x
  rw [OO_coexact_projector x, O_coexact_projector x, sub_neg_eq_add, smul_add,
    ← add_smul]
  norm_num

theorem harmonic_projector_idempotent (x : V) :
    harmonic_projector (harmonic_projector x) = harmonic_projector x := by
  change
    harmonic_projector x -
        Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (harmonic_projector x)) =
      harmonic_projector x
  rw [OO_harmonic_projector x, sub_zero]

theorem exact_coexact_disjoint (x : V) :
    exact_projector (coexact_projector x) = 0 := by
  change
    (1 / 2 : ℝ) •
        (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (coexact_projector x)) +
          Node1_TriFacetOperator.O (coexact_projector x)) =
      0
  rw [OO_coexact_projector x, O_coexact_projector x]
  have h : coexact_projector x + -coexact_projector x = 0 := by
    abel
  rw [h, smul_zero]

theorem coexact_exact_disjoint (x : V) :
    coexact_projector (exact_projector x) = 0 := by
  change
    (1 / 2 : ℝ) •
        (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (exact_projector x)) -
          Node1_TriFacetOperator.O (exact_projector x)) =
      0
  rw [OO_exact_projector x, O_exact_projector x, sub_self, smul_zero]

theorem exact_harmonic_disjoint (x : V) :
    exact_projector (harmonic_projector x) = 0 := by
  change
    (1 / 2 : ℝ) •
        (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (harmonic_projector x)) +
          Node1_TriFacetOperator.O (harmonic_projector x)) =
      0
  rw [OO_harmonic_projector x, O_harmonic_projector x, add_zero, smul_zero]

theorem coexact_harmonic_disjoint (x : V) :
    coexact_projector (harmonic_projector x) = 0 := by
  change
    (1 / 2 : ℝ) •
        (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (harmonic_projector x)) -
          Node1_TriFacetOperator.O (harmonic_projector x)) =
      0
  rw [OO_harmonic_projector x, O_harmonic_projector x, sub_zero, smul_zero]

theorem harmonic_exact_disjoint (x : V) :
    harmonic_projector (exact_projector x) = 0 := by
  change
    exact_projector x -
        Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (exact_projector x)) =
      0
  rw [OO_exact_projector x, sub_self]

theorem harmonic_coexact_disjoint (x : V) :
    harmonic_projector (coexact_projector x) = 0 := by
  change
    coexact_projector x -
        Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (coexact_projector x)) =
      0
  rw [OO_coexact_projector x, sub_self]

theorem hodge_krein_orthogonality (x y : V) :
    Node0_KreinSpace.B (exact_projector x) (coexact_projector y) = 0 := by
  let B := Node0_KreinSpace.B (V := V)
  let O := Node1_TriFacetOperator.O (V := V)
  have hB_smul_left : ∀ c u v, B (c • u) v = c * B u v :=
    Node0_KreinSpace.B_smul_left
  have hB_comm : ∀ u v, B u v = B v u := Node0_KreinSpace.B_comm
  have hB_smul_right : ∀ c u v, B u (c • v) = c * B u v := by
    intro c u v
    rw [hB_comm, hB_smul_left, hB_comm]
  have hB_neg_right : ∀ u v, B u (-v) = -B u v := by
    intro u v
    have hv : -v = (-1 : ℝ) • v := (neg_one_smul ℝ v).symm
    rw [hv, hB_smul_right]
    ring
  have hneg :
      B (exact_projector x) (coexact_projector y) =
        -B (exact_projector x) (coexact_projector y) := by
    calc
      B (exact_projector x) (coexact_projector y)
          = B (O (exact_projector x)) (coexact_projector y) := by
            rw [O_exact_projector x]
      _ = B (exact_projector x) (O (coexact_projector y)) :=
        Node1_TriFacetOperator.O_adj (exact_projector x) (coexact_projector y)
      _ = B (exact_projector x) (-coexact_projector y) := by
        rw [O_coexact_projector y]
      _ = -B (exact_projector x) (coexact_projector y) := hB_neg_right _ _
  linarith

class Node3_NilpotentShear (V : Type*) [AddCommGroup V] [Module ℝ V]
  [Node0_KreinSpace V] [Node1_TriFacetOperator V] where
  N : V →ₗ[ℝ] V
  N_nilpotent : ∀ x, N (N x) = 0
  N_locks_kernel : ∀ x, Node1_TriFacetOperator.O x = 0 → N x = 0

section NilpotentShear

variable [Node3_NilpotentShear V]

theorem shear_preserves_kernel (x : V) :
    Node1_TriFacetOperator.O x = 0 →
    Node1_TriFacetOperator.O (Node3_NilpotentShear.N x) = 0 := by
  intro h
  rw [Node3_NilpotentShear.N_locks_kernel x h]
  exact LinearMap.map_zero Node1_TriFacetOperator.O

theorem shear_zero_on_harmonic_image (x : V) :
    Node3_NilpotentShear.N (harmonic_projector x) = 0 :=
  Node3_NilpotentShear.N_locks_kernel (harmonic_projector x)
    (O_harmonic_projector (V := V) x)

end NilpotentShear

class Node4_MajoranaBEC (V : Type*) [AddCommGroup V] [Module ℝ V]
  [Node0_KreinSpace V] [Node1_TriFacetOperator V] [Node3_NilpotentShear V] where
  B_condensate : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  Condensate_energy_zero :
    ∀ x y,
    Node1_TriFacetOperator.O x = 0 →
    Node1_TriFacetOperator.O y = 0 →
    B_condensate x y = 0

class Node5_VerlindeFusionRing (Idx : Type*) [Fintype Idx] where
  vac : Idx
  S : Idx → Idx → ℝ
  N_fuse : Idx → Idx → Idx → ℝ
  verlinde_formula :
    ∀ a b c, N_fuse a b c = ∑ x, (S a x * S b x * S c x) / S vac x

theorem verlinde_symm_ab {Idx : Type*} [Fintype Idx] [Node5_VerlindeFusionRing Idx] (a b c : Idx) :
    Node5_VerlindeFusionRing.N_fuse a b c = Node5_VerlindeFusionRing.N_fuse b a c := by
  rw [Node5_VerlindeFusionRing.verlinde_formula a b c]
  rw [Node5_VerlindeFusionRing.verlinde_formula b a c]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem verlinde_symm_bc {Idx : Type*} [Fintype Idx] [Node5_VerlindeFusionRing Idx] (a b c : Idx) :
    Node5_VerlindeFusionRing.N_fuse a b c = Node5_VerlindeFusionRing.N_fuse a c b := by
  rw [Node5_VerlindeFusionRing.verlinde_formula a b c]
  rw [Node5_VerlindeFusionRing.verlinde_formula a c b]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem verlinde_symm_ac {Idx : Type*} [Fintype Idx] [Node5_VerlindeFusionRing Idx] (a b c : Idx) :
    Node5_VerlindeFusionRing.N_fuse a b c = Node5_VerlindeFusionRing.N_fuse c b a := by
  rw [Node5_VerlindeFusionRing.verlinde_formula a b c]
  rw [Node5_VerlindeFusionRing.verlinde_formula c b a]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The tri-facet decomposition as a direct-sum relation of linear maps. -/
theorem tri_facet_resolution_lin : (exact_projector_lin : V →ₗ[ℝ] V) + coexact_projector_lin + harmonic_projector_lin = LinearMap.id := by
  ext x
  simp only [LinearMap.add_apply, LinearMap.id_apply]
  exact tri_facet_resolution x

/-- `exact_projector_lin` is idempotent. -/
theorem exact_projector_lin_idempotent : (exact_projector_lin : V →ₗ[ℝ] V).comp exact_projector_lin = exact_projector_lin := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply]
  exact exact_projector_idempotent x

/-- `coexact_projector_lin` is idempotent. -/
theorem coexact_projector_lin_idempotent : (coexact_projector_lin : V →ₗ[ℝ] V).comp coexact_projector_lin = coexact_projector_lin := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply]
  exact coexact_projector_idempotent x

/-- `harmonic_projector_lin` is idempotent. -/
theorem harmonic_projector_lin_idempotent : (harmonic_projector_lin : V →ₗ[ℝ] V).comp harmonic_projector_lin = harmonic_projector_lin := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply]
  exact harmonic_projector_idempotent x

/-- `exact_projector_lin` and `coexact_projector_lin` annihilate each other. -/
theorem exact_comp_coexact_lin : (exact_projector_lin : V →ₗ[ℝ] V).comp coexact_projector_lin = 0 := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply]
  exact exact_coexact_disjoint x

theorem coexact_comp_exact_lin : (coexact_projector_lin : V →ₗ[ℝ] V).comp exact_projector_lin = 0 := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply]
  exact coexact_exact_disjoint x

/-- `exact_projector_lin` and `harmonic_projector_lin` annihilate each other. -/
theorem exact_comp_harmonic_lin : (exact_projector_lin : V →ₗ[ℝ] V).comp harmonic_projector_lin = 0 := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply]
  exact exact_harmonic_disjoint x

theorem harmonic_comp_exact_lin : (harmonic_projector_lin : V →ₗ[ℝ] V).comp exact_projector_lin = 0 := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply]
  exact harmonic_exact_disjoint x

/-- `coexact_projector_lin` and `harmonic_projector_lin` annihilate each other. -/
theorem coexact_comp_harmonic_lin : (coexact_projector_lin : V →ₗ[ℝ] V).comp harmonic_projector_lin = 0 := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply]
  exact coexact_harmonic_disjoint x

theorem harmonic_comp_coexact_lin : (harmonic_projector_lin : V →ₗ[ℝ] V).comp coexact_projector_lin = 0 := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply]
  exact harmonic_coexact_disjoint x

/-- A vector lies in the range of the exact projector iff it is fixed by `O`. -/
theorem mem_range_exact_projector_lin_iff (x : V) :
    x ∈ LinearMap.range (exact_projector_lin : V →ₗ[ℝ] V) ↔ Node1_TriFacetOperator.O x = x := by
  constructor
  · rintro ⟨y, rfl⟩; exact O_exact_projector y
  · intro h; refine ⟨x, ?_⟩; have hO2 : Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) = x := by
      rw [h, h]
    dsimp [exact_projector_lin, exact_projector]; rw [hO2, h]; calc
      (1/2 : ℝ) • (x + x) = (1/2 : ℝ) • x + (1/2 : ℝ) • x := by rw [smul_add]
      _ = ((1/2 : ℝ) + (1/2 : ℝ)) • x := by rw [add_smul]
      _ = (1 : ℝ) • x := by norm_num
      _ = x := by simp

/-- A vector lies in the range of the coexact projector iff it is anti-fixed by `O`. -/
theorem mem_range_coexact_projector_lin_iff (x : V) :
    x ∈ LinearMap.range (coexact_projector_lin : V →ₗ[ℝ] V) ↔ Node1_TriFacetOperator.O x = -x := by
  constructor
  · rintro ⟨y, rfl⟩; exact O_coexact_projector y
  · intro h; refine ⟨x, ?_⟩; have hO2 : Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) = x := by calc
      Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) = Node1_TriFacetOperator.O (-x) := by rw [h]
      _ = - Node1_TriFacetOperator.O x := by rw [map_neg]
      _ = - (-x) := by rw [h]
      _ = x := by simp
    dsimp [coexact_projector_lin, coexact_projector]; rw [hO2, h]; calc
      (1/2 : ℝ) • (x - (-x)) = (1/2 : ℝ) • (x + x) := by rw [sub_neg_eq_add]
      _ = (1/2 : ℝ) • x + (1/2 : ℝ) • x := by rw [smul_add]
      _ = ((1/2 : ℝ) + (1/2 : ℝ)) • x := by rw [add_smul]
      _ = (1 : ℝ) • x := by norm_num
      _ = x := by simp

/-- A vector lies in the range of the harmonic projector iff it is annihilated by `O`. -/
theorem mem_range_harmonic_projector_lin_iff (x : V) :
    x ∈ LinearMap.range (harmonic_projector_lin : V →ₗ[ℝ] V) ↔ Node1_TriFacetOperator.O x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩; exact O_harmonic_projector y
  · intro h; refine ⟨x, ?_⟩; simp [harmonic_projector_lin, harmonic_projector, h]

/-- The zero operator is a concrete nilpotent shear, proving `Node3_NilpotentShear` is
not vacuous. -/
def nilpotentShearZero : Node3_NilpotentShear V where
  N := (0 : V →ₗ[ℝ] V)
  N_nilpotent x := by simp
  N_locks_kernel x h := by simp

instance : Node3_NilpotentShear V := nilpotentShearZero

end HodgeKreinTriFacet

end Audit
