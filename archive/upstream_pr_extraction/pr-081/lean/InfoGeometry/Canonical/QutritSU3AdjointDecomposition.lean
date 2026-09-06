import Mathlib
import InfoGeometry.Canonical.QutritGellMannOperatorBasis

/-!
# The scalar/traceless decomposition of the qutrit operator space

This is the matrix-level content of the familiar `1 ⊕ 8` decomposition.  It
deliberately states the result for the adjoint *operator space*: no claim about
an `SU(3)` group representation is made here.  The latter requires a separate
intertwining theorem for conjugation by special-unitary matrices.
-/

noncomputable section

namespace InfoGeometry.Canonical.QutritSU3AdjointDecomposition

open Matrix
open InfoGeometry.Canonical.QutritGellMannOperatorBasis

abbrev QutritMatrix := Matrix (Fin 3) (Fin 3) ℂ

/-! ## The two canonical subspaces -/

/-- The traceless operator subspace of `M₃(ℂ)`. -/
def traceless : Submodule ℂ QutritMatrix :=
  (Matrix.traceLinearMap (Fin 3) ℂ ℂ).ker

/-- The scalar operator line `ℂ · I₃`. -/
def scalar : Submodule ℂ QutritMatrix :=
  Submodule.span ℂ ({(1 : QutritMatrix)} : Set QutritMatrix)

theorem trace_one : Matrix.trace (1 : QutritMatrix) = 3 := by
  simp [Matrix.trace_one]

theorem scalar_mem_iff (A : QutritMatrix) : A ∈ scalar ↔ ∃ c : ℂ, c • (1 : QutritMatrix) = A := by
  constructor
  · intro h
    exact Submodule.mem_span_singleton.mp h
  · rintro ⟨c, rfl⟩
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))

theorem scalar_traceless_disjoint : Disjoint scalar traceless := by
  rw [Submodule.disjoint_def]
  intro A hA hT
  obtain ⟨c, rfl⟩ := (scalar_mem_iff A).mp hA
  have ht : Matrix.trace (c • (1 : QutritMatrix)) = 0 := hT
  rw [Matrix.trace_smul, trace_one] at ht
  have : c = 0 := by
    apply (mul_eq_zero.mp ht).resolve_right
    norm_num
  simpa [this]

/-! ## Dimensions -/

theorem trace_range_eq_top : (Matrix.traceLinearMap (Fin 3) ℂ ℂ).range = ⊤ := by
  apply top_unique
  intro c hc
  let A : QutritMatrix := (c / 3) • (1 : QutritMatrix)
  have hA : Matrix.traceLinearMap (Fin 3) ℂ ℂ A = c := by
    change Matrix.trace A = c
    simp [A, Matrix.trace_smul, trace_one]
  exact ⟨A, hA⟩

theorem traceless_finrank : Module.finrank ℂ traceless = 8 := by
  have hrank :=
    LinearMap.finrank_range_add_finrank_ker
      (Matrix.traceLinearMap (Fin 3) ℂ ℂ)
  rw [trace_range_eq_top] at hrank
  have hmatrix : Module.finrank ℂ QutritMatrix = 9 := by
    simp [Module.finrank_matrix]
  have htop : Module.finrank ℂ (⊤ : Submodule ℂ ℂ) = 1 := by simp
  rw [htop] at hrank
  rw [hmatrix] at hrank
  dsimp [traceless]
  linarith

theorem scalar_finrank : Module.finrank ℂ scalar = 1 := by
  exact finrank_span_singleton (by simp : (1 : QutritMatrix) ≠ 0)

/-! ## Explicit `1 ⊕ 8` decomposition -/

/-- Every qutrit operator has a unique scalar part and traceless part. -/
theorem scalar_traceless_decomposition (A : QutritMatrix) :
    ((Matrix.trace A) / 3) • (1 : QutritMatrix) +
        (A - ((Matrix.trace A) / 3) • (1 : QutritMatrix)) = A := by
  have htrace : Matrix.trace (1 : QutritMatrix) = 3 := trace_one
  ext i j
  simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, htrace]

theorem scalar_traceless_decomposition_mem (A : QutritMatrix) :
    A - ((Matrix.trace A) / 3) • (1 : QutritMatrix) ∈ traceless := by
  change Matrix.trace (A - ((Matrix.trace A) / 3) • (1 : QutritMatrix)) = 0
  simp [Matrix.trace_sub, Matrix.trace_smul, trace_one]

theorem adjoint_decomposition_finrank :
    Module.finrank ℂ scalar + Module.finrank ℂ traceless =
      Module.finrank ℂ QutritMatrix := by
  rw [scalar_finrank, traceless_finrank]
  simp [Module.finrank_matrix]

theorem adjoint_decomposition_dimensions :
    Module.finrank ℂ scalar = 1 ∧
      Module.finrank ℂ traceless = 8 ∧
      Module.finrank ℂ QutritMatrix = 9 := by
  simp [scalar_finrank, traceless_finrank, Module.finrank_matrix]

/-! ## Relation with the already proved Gell--Mann channels -/

theorem gellMann_nonidentity_mem_traceless (r : Fin 8) :
    gellMannFamily (Fin.succ r) ∈ traceless := by
  change Matrix.trace (gellMannFamily (Fin.succ r)) = 0
  simpa using gellMannFamily_trace (Fin.succ r)

/-! ## Native unitary adjoint action -/

abbrev SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ

/-- The usual matrix adjoint action, restricted to the qutrit special-unitary
group.  The determinant-one condition is not needed for trace preservation,
but records the intended `SU(3)` carrier. -/
def adjoint (g : SU3) : QutritMatrix →ₗ[ℂ] QutritMatrix :=
  (LinearMap.mulRight ℂ (star (g : QutritMatrix))).comp
    (LinearMap.mulLeft ℂ (g : QutritMatrix))

theorem adjoint_apply (g : SU3) (A : QutritMatrix) :
    adjoint g A = (g : QutritMatrix) * A * star (g : QutritMatrix) := rfl

theorem adjoint_trace (g : SU3) (A : QutritMatrix) :
    Matrix.trace (adjoint g A) = Matrix.trace A := by
  have hu : star (g : QutritMatrix) * (g : QutritMatrix) = 1 := by
    exact (Matrix.mem_unitaryGroup_iff'.mp
      ((Matrix.mem_specialUnitaryGroup_iff.mp g.property).1))
  rw [adjoint_apply, Matrix.trace_mul_comm]
  rw [← Matrix.mul_assoc, hu, Matrix.one_mul]

theorem adjoint_preserves_traceless (g : SU3) :
    Submodule.map (adjoint g) traceless ≤ traceless := by
  rintro B ⟨A, hA, rfl⟩
  change Matrix.trace A = 0 at hA
  change Matrix.trace (adjoint g A) = 0
  rw [adjoint_trace, hA]

theorem adjoint_preserves_scalar (g : SU3) :
    Submodule.map (adjoint g) scalar ≤ scalar := by
  rintro B ⟨A, hA, rfl⟩
  obtain ⟨c, rfl⟩ := (scalar_mem_iff A).mp hA
  refine (scalar_mem_iff _).mpr ⟨c, ?_⟩
  rw [map_smul, adjoint_apply]
  have hu : (g : QutritMatrix) * star (g : QutritMatrix) = 1 := by
    exact (Matrix.mem_unitaryGroup_iff.mp
      ((Matrix.mem_specialUnitaryGroup_iff.mp g.property).1))
  simp [hu]

theorem adjoint_scalar (g : SU3) (c : ℂ) :
    adjoint g (c • (1 : QutritMatrix)) = c • (1 : QutritMatrix) := by
  rw [adjoint_apply]
  have hu : (g : QutritMatrix) * star (g : QutritMatrix) = 1 := by
    exact (Matrix.mem_unitaryGroup_iff.mp
      ((Matrix.mem_specialUnitaryGroup_iff.mp g.property).1))
  simp [hu]

theorem adjoint_preserves_scalar_eq (g : SU3) :
    Submodule.map (adjoint g) scalar = scalar := by
  apply le_antisymm
  · exact adjoint_preserves_scalar g
  · rintro A hA
    obtain ⟨c, rfl⟩ := (scalar_mem_iff A).mp hA
    refine ⟨c • (1 : QutritMatrix), ?_, ?_⟩
    · exact Submodule.smul_mem scalar c (Submodule.subset_span (Set.mem_singleton _))
    · exact adjoint_scalar g c

/-! ## A genuine linear equivalence for `1 ⊕ 8` -/

/-- Coordinates consisting of the scalar trace coefficient and the traceless
remainder. -/
def decompositionMap : QutritMatrix →ₗ[ℂ] ℂ × traceless :=
  { toFun := fun A =>
      (Matrix.trace A / 3,
        ⟨A - (Matrix.trace A / 3) • (1 : QutritMatrix),
          scalar_traceless_decomposition_mem A⟩)
    map_add' := by
      intro A B
      ext <;> simp [Matrix.trace_add, sub_eq_add_neg, add_smul] <;> ring
    map_smul' := by
      intro c A
      ext <;> simp [Matrix.trace_smul, sub_eq_add_neg, smul_add] <;> ring }

theorem decompositionMap_injective : Function.Injective decompositionMap := by
  intro A B h
  have hscalar := congrArg Prod.fst h
  change Matrix.trace A / 3 = Matrix.trace B / 3 at hscalar
  have htraceless := congrArg Prod.snd h
  change
    (⟨A - (Matrix.trace A / 3) • (1 : QutritMatrix),
      scalar_traceless_decomposition_mem A⟩ : traceless) =
      ⟨B - (Matrix.trace B / 3) • (1 : QutritMatrix),
        scalar_traceless_decomposition_mem B⟩ at htraceless
  have hA := scalar_traceless_decomposition A
  have hB := scalar_traceless_decomposition B
  have hrem :
      A - (Matrix.trace A / 3) • (1 : QutritMatrix) =
        B - (Matrix.trace B / 3) • (1 : QutritMatrix) := by
    exact congrArg Subtype.val htraceless
  calc
    A = (Matrix.trace A / 3) • (1 : QutritMatrix) +
        (A - (Matrix.trace A / 3) • (1 : QutritMatrix)) := hA.symm
    _ = (Matrix.trace A / 3) • (1 : QutritMatrix) +
        (B - (Matrix.trace B / 3) • (1 : QutritMatrix)) := by
          exact congrArg (fun X => (Matrix.trace A / 3) • (1 : QutritMatrix) + X) hrem
    _ = (Matrix.trace B / 3) • (1 : QutritMatrix) +
        (B - (Matrix.trace B / 3) • (1 : QutritMatrix)) := by rw [hscalar]
    _ = B := hB

theorem decompositionMap_surjective : Function.Surjective decompositionMap := by
  rintro ⟨c, H⟩
  let A : QutritMatrix := c • (1 : QutritMatrix) + H.1
  have hH : Matrix.trace H.1 = 0 := H.property
  refine ⟨A, ?_⟩
  change decompositionMap A = (c, H)
  apply Prod.ext
  · simp [decompositionMap, A, hH, Matrix.trace_add, Matrix.trace_smul, trace_one]
  · apply Subtype.ext
    simp [decompositionMap, A, hH, Matrix.trace_add, Matrix.trace_smul, trace_one]

/-- Canonical operator-space form of the adjoint decomposition:
`M₃(ℂ) ≃ ℂ × sl₃(ℂ)`, with the second factor represented concretely by
the trace kernel. -/
def adjointDecompositionEquiv : QutritMatrix ≃ₗ[ℂ] ℂ × traceless :=
  LinearEquiv.ofBijective decompositionMap
    ⟨decompositionMap_injective, decompositionMap_surjective⟩

theorem adjointDecompositionEquiv_finrank :
    Module.finrank ℂ QutritMatrix =
      Module.finrank ℂ ℂ + Module.finrank ℂ traceless := by
  rw [adjointDecompositionEquiv.finrank_eq, Module.finrank_prod]

theorem adjointDecompositionEquiv_dimensions :
    Module.finrank ℂ QutritMatrix = 1 + 8 := by
  rw [adjointDecompositionEquiv_finrank, traceless_finrank]
  simp

theorem decompositionMap_adjoint_scalar (g : SU3) (A : QutritMatrix) :
    (decompositionMap (adjoint g A)).1 = (decompositionMap A).1 := by
  simp [decompositionMap, adjoint_trace]

theorem decompositionMap_adjoint_traceless (g : SU3) (A : QutritMatrix) :
    (decompositionMap (adjoint g A)).2.1 =
      adjoint g (decompositionMap A).2.1 := by
  change adjoint g A - (Matrix.trace (adjoint g A) / 3) • (1 : QutritMatrix) =
    adjoint g (A - (Matrix.trace A / 3) • (1 : QutritMatrix))
  rw [adjoint_trace]
  have h1 : adjoint g (1 : QutritMatrix) = 1 := by
    simpa using adjoint_scalar g 1
  simp [map_sub, map_smul, h1]

end InfoGeometry.Canonical.QutritSU3AdjointDecomposition

end noncomputable section
