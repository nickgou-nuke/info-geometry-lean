import InfoGeometry.Canonical.ExteriorSpinorChiralityBridge
import InfoGeometry.Clifford.SplitClifford55ExteriorFiniteGraded
import InfoGeometry.Clifford.Cl55ExteriorSpinorCoordinateReadout
import Mathlib.LinearAlgebra.CliffordAlgebra.Even

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55ExteriorParity

open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor

abbrev Spinor := ExteriorAlgebra ℝ V5

abbrev NeutralQ :=
  InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
    (E := V5)

local instance : FiniteDimensional ℝ Spinor := spinor_finiteDimensional

noncomputable def gradeInvolution : Spinor →ₐ[ℝ] Spinor :=
  InfoGeometry.Canonical.ExteriorSpinorChiralityBridge.gradeInvolution
    (R := ℝ) (V := V5)

noncomputable def neutralCliffordRepEven :
    CliffordAlgebra.even NeutralQ →ₐ[ℝ] SpinorEnd :=
  neutralCliffordRep.comp (CliffordAlgebra.even NeutralQ).val

@[simp] theorem neutralCliffordRepEven_ι (w z : NeutralSpace) :
    neutralCliffordRepEven ((CliffordAlgebra.even.ι NeutralQ).bilin w z) =
      neutralAction w * neutralAction z := by
  change neutralCliffordRep
      (CliffordAlgebra.ι NeutralQ w * CliffordAlgebra.ι NeutralQ z) = _
  rw [map_mul, neutralCliffordRep_ι, neutralCliffordRep_ι]

@[simp] theorem gradeInvolution_ι (v : V5) :
    gradeInvolution (ExteriorAlgebra.ι ℝ v) = -ExteriorAlgebra.ι ℝ v := by
  exact InfoGeometry.Canonical.ExteriorSpinorChiralityBridge.gradeInvolution_ι v

theorem gradeInvolution_involutive (ψ : Spinor) :
    gradeInvolution (gradeInvolution ψ) = ψ := by
  exact InfoGeometry.Canonical.ExteriorSpinorChiralityBridge.gradeInvolution_involutive ψ

theorem gradeInvolution_wedge (v : V5) (ψ : Spinor) :
    gradeInvolution (wedge v ψ) = -(wedge v (gradeInvolution ψ)) := by
  change gradeInvolution (ExteriorAlgebra.ι ℝ v * ψ) =
    -(ExteriorAlgebra.ι ℝ v * gradeInvolution ψ)
  rw [map_mul, gradeInvolution_ι]
  simp

theorem gradeInvolution_contract (φ : Module.Dual ℝ V5) (ψ : Spinor) :
    gradeInvolution (contract φ ψ) =
      -(contract φ (gradeInvolution ψ)) := by
  induction ψ using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp [contract]
  | add x y hx hy =>
      simp only [map_add, hx, hy, neg_add]
  | ι_mul a x hx =>
      change gradeInvolution (contract φ (wedge x a)) =
        -(contract φ (gradeInvolution (wedge x a)))
      rw [contract_wedge, map_sub, map_smul]
      rw [gradeInvolution_wedge x a]
      simp only [map_neg, neg_neg]
      rw [gradeInvolution_wedge x (contract φ a), hx,
        contract_wedge φ x (gradeInvolution a)]
      simp only [map_neg, neg_neg]

theorem gradeInvolution_neutralAction (w : NeutralSpace) (ψ : Spinor) :
    gradeInvolution (neutralAction w ψ) =
      -(neutralAction w (gradeInvolution ψ)) := by
  rcases w with ⟨v, φ⟩
  change gradeInvolution (wedge v ψ + contract φ ψ) =
    -(wedge v (gradeInvolution ψ) + contract φ (gradeInvolution ψ))
  rw [map_add, gradeInvolution_wedge, gradeInvolution_contract]
  abel

noncomputable def gradeLinear : SpinorEnd := gradeInvolution.toLinearMap

@[simp] theorem gradeLinear_apply (ψ : Spinor) :
    gradeLinear ψ = gradeInvolution ψ :=
  rfl

theorem gradeLinear_sq : gradeLinear * gradeLinear = (1 : SpinorEnd) := by
  apply LinearMap.ext
  intro ψ
  simp only [Module.End.mul_apply, Module.End.one_apply]
  change gradeInvolution (gradeInvolution ψ) = ψ
  exact gradeInvolution_involutive ψ

noncomputable def chiralProjectorPlus : SpinorEnd :=
  (1 / 2 : ℝ) • (1 + gradeLinear)

noncomputable def chiralProjectorMinus : SpinorEnd :=
  (1 / 2 : ℝ) • (1 - gradeLinear)

theorem chiralProjectors_add :
    chiralProjectorPlus + chiralProjectorMinus = (1 : SpinorEnd) := by
  simp only [chiralProjectorPlus, chiralProjectorMinus, smul_add, smul_sub]
  module

theorem chiralProjectors_sub :
    chiralProjectorPlus - chiralProjectorMinus = gradeLinear := by
  simp only [chiralProjectorPlus, chiralProjectorMinus, smul_add, smul_sub]
  module

theorem chiralProjectorPlus_apply (ψ : Spinor) :
    chiralProjectorPlus ψ = (1 / 2 : ℝ) • (ψ + gradeInvolution ψ) := by
  simp [chiralProjectorPlus, gradeLinear]

theorem chiralProjectorMinus_apply (ψ : Spinor) :
    chiralProjectorMinus ψ = (1 / 2 : ℝ) • (ψ - gradeInvolution ψ) := by
  simp [chiralProjectorMinus, gradeLinear]

theorem gradeInvolution_chiralProjectorPlus (ψ : Spinor) :
    gradeInvolution (chiralProjectorPlus ψ) = chiralProjectorPlus ψ := by
  rw [chiralProjectorPlus_apply]
  simp only [map_smul, map_add, gradeInvolution_involutive]
  module

theorem gradeInvolution_chiralProjectorMinus (ψ : Spinor) :
    gradeInvolution (chiralProjectorMinus ψ) =
      -(chiralProjectorMinus ψ) := by
  rw [chiralProjectorMinus_apply]
  simp only [map_smul, map_sub, gradeInvolution_involutive]
  module

theorem chiralProjectorPlus_idempotent :
    chiralProjectorPlus * chiralProjectorPlus = chiralProjectorPlus := by
  apply LinearMap.ext
  intro ψ
  calc
    chiralProjectorPlus (chiralProjectorPlus ψ) =
        (1 / 2 : ℝ) •
          (chiralProjectorPlus ψ +
            gradeInvolution (chiralProjectorPlus ψ)) :=
      chiralProjectorPlus_apply (chiralProjectorPlus ψ)
    _ = chiralProjectorPlus ψ := by
      rw [gradeInvolution_chiralProjectorPlus]
      module

theorem chiralProjectorMinus_idempotent :
    chiralProjectorMinus * chiralProjectorMinus = chiralProjectorMinus := by
  apply LinearMap.ext
  intro ψ
  calc
    chiralProjectorMinus (chiralProjectorMinus ψ) =
        (1 / 2 : ℝ) •
          (chiralProjectorMinus ψ -
            gradeInvolution (chiralProjectorMinus ψ)) :=
      chiralProjectorMinus_apply (chiralProjectorMinus ψ)
    _ = chiralProjectorMinus ψ := by
      rw [gradeInvolution_chiralProjectorMinus]
      module

theorem chiralProjectors_plus_mul_minus :
    chiralProjectorPlus * chiralProjectorMinus = 0 := by
  apply LinearMap.ext
  intro ψ
  calc
    chiralProjectorPlus (chiralProjectorMinus ψ) =
        (1 / 2 : ℝ) •
          (chiralProjectorMinus ψ +
            gradeInvolution (chiralProjectorMinus ψ)) :=
      chiralProjectorPlus_apply (chiralProjectorMinus ψ)
    _ = 0 := by
      rw [gradeInvolution_chiralProjectorMinus]
      module

theorem chiralProjectors_minus_mul_plus :
    chiralProjectorMinus * chiralProjectorPlus = 0 := by
  apply LinearMap.ext
  intro ψ
  calc
    chiralProjectorMinus (chiralProjectorPlus ψ) =
        (1 / 2 : ℝ) •
          (chiralProjectorPlus ψ -
            gradeInvolution (chiralProjectorPlus ψ)) :=
      chiralProjectorMinus_apply (chiralProjectorPlus ψ)
    _ = 0 := by
      rw [gradeInvolution_chiralProjectorPlus]
      module

theorem chiralProjector_ranges_sup :
    LinearMap.range chiralProjectorPlus ⊔
        LinearMap.range chiralProjectorMinus = ⊤ := by
  apply top_unique
  intro ψ _
  have h := congrArg (fun T : SpinorEnd => T ψ) chiralProjectors_add
  have hdecomp : ψ = chiralProjectorPlus ψ + chiralProjectorMinus ψ := by
    simpa using h.symm
  rw [hdecomp]
  exact add_mem
    ((le_sup_left : LinearMap.range chiralProjectorPlus ≤
      LinearMap.range chiralProjectorPlus ⊔ LinearMap.range chiralProjectorMinus)
      (LinearMap.mem_range_self _ ψ))
    ((le_sup_right : LinearMap.range chiralProjectorMinus ≤
      LinearMap.range chiralProjectorPlus ⊔ LinearMap.range chiralProjectorMinus)
      (LinearMap.mem_range_self _ ψ))

theorem chiralProjector_ranges_inf :
    LinearMap.range chiralProjectorPlus ⊓
        LinearMap.range chiralProjectorMinus = ⊥ := by
  apply bot_unique
  rintro ψ ⟨hψPlus, hψMinus⟩
  rcases hψPlus with ⟨u, rfl⟩
  rcases hψMinus with ⟨v, hv⟩
  have hfixed : chiralProjectorPlus (chiralProjectorPlus u) =
      chiralProjectorPlus u := by
    have h := congrArg (fun T : SpinorEnd => T u)
      chiralProjectorPlus_idempotent
    simpa [Module.End.mul_apply] using h
  have hzero : chiralProjectorPlus (chiralProjectorPlus u) = 0 := by
    rw [← hv]
    have h := congrArg (fun T : SpinorEnd => T v)
      chiralProjectors_plus_mul_minus
    simpa [Module.End.mul_apply] using h
  rw [hfixed] at hzero
  simpa using hzero

theorem chiralProjectors_decomposition (ψ : Spinor) :
    chiralProjectorPlus ψ + chiralProjectorMinus ψ = ψ := by
  have h := congrArg (fun T : SpinorEnd => T ψ) chiralProjectors_add
  simpa using h

theorem mem_range_chiralProjectorPlus_iff (ψ : Spinor) :
    ψ ∈ LinearMap.range chiralProjectorPlus ↔
      gradeInvolution ψ = ψ := by
  constructor
  · rintro ⟨u, rfl⟩
    exact gradeInvolution_chiralProjectorPlus u
  · intro h
    refine ⟨ψ, ?_⟩
    rw [chiralProjectorPlus_apply, h]
    module

theorem mem_range_chiralProjectorMinus_iff (ψ : Spinor) :
    ψ ∈ LinearMap.range chiralProjectorMinus ↔
      gradeInvolution ψ = -ψ := by
  constructor
  · rintro ⟨u, rfl⟩
    exact gradeInvolution_chiralProjectorMinus u
  · intro h
    refine ⟨ψ, ?_⟩
    rw [chiralProjectorMinus_apply, h]
    module

theorem neutralAction_mem_chiralProjectorMinus_of_mem_plus
    (w : NeutralSpace) (ψ : Spinor)
    (hψ : ψ ∈ LinearMap.range chiralProjectorPlus) :
    neutralAction w ψ ∈ LinearMap.range chiralProjectorMinus := by
  rw [mem_range_chiralProjectorMinus_iff]
  rw [gradeInvolution_neutralAction]
  rw [mem_range_chiralProjectorPlus_iff] at hψ
  rw [hψ]

theorem neutralAction_mem_chiralProjectorPlus_of_mem_minus
    (w : NeutralSpace) (ψ : Spinor)
    (hψ : ψ ∈ LinearMap.range chiralProjectorMinus) :
    neutralAction w ψ ∈ LinearMap.range chiralProjectorPlus := by
  rw [mem_range_chiralProjectorPlus_iff]
  rw [gradeInvolution_neutralAction]
  rw [mem_range_chiralProjectorMinus_iff] at hψ
  rw [hψ]
  simp

theorem gradeInvolution_neutralAction_pair (w z : NeutralSpace) (ψ : Spinor) :
    gradeInvolution (neutralAction w (neutralAction z ψ)) =
      neutralAction w (neutralAction z (gradeInvolution ψ)) := by
  rw [gradeInvolution_neutralAction, gradeInvolution_neutralAction]
  simp only [map_neg, neg_neg]

theorem neutralAction_pair_mem_same_chirality_of_mem_plus
    (w z : NeutralSpace) (ψ : Spinor)
    (hψ : ψ ∈ LinearMap.range chiralProjectorPlus) :
    neutralAction w (neutralAction z ψ) ∈
      LinearMap.range chiralProjectorPlus := by
  rw [mem_range_chiralProjectorPlus_iff]
  rw [gradeInvolution_neutralAction_pair]
  rw [mem_range_chiralProjectorPlus_iff] at hψ
  rw [hψ]

theorem neutralAction_pair_mem_same_chirality_of_mem_minus
    (w z : NeutralSpace) (ψ : Spinor)
    (hψ : ψ ∈ LinearMap.range chiralProjectorMinus) :
    neutralAction w (neutralAction z ψ) ∈
      LinearMap.range chiralProjectorMinus := by
  rw [mem_range_chiralProjectorMinus_iff]
  rw [gradeInvolution_neutralAction_pair]
  rw [mem_range_chiralProjectorMinus_iff] at hψ
  rw [hψ]
  simp

theorem neutralCliffordRepEven_mem_plus
    (a : CliffordAlgebra.even NeutralQ) (ψ : Spinor)
    (hψ : ψ ∈ LinearMap.range chiralProjectorPlus) :
    neutralCliffordRepEven a ψ ∈ LinearMap.range chiralProjectorPlus := by
  rw [mem_range_chiralProjectorPlus_iff] at hψ ⊢
  let motive : ∀ x, x ∈ CliffordAlgebra.evenOdd NeutralQ 0 → Prop :=
    fun x _ => gradeInvolution (neutralCliffordRep x ψ) =
      neutralCliffordRep x ψ
  have hm := CliffordAlgebra.even_induction (Q := NeutralQ)
    (motive := motive)
    (algebraMap := by
      intro r
      simp [motive, hψ])
    (add := by
      intro x y hx hy ihx ihy
      simp only [motive, map_add, LinearMap.add_apply, ihx, ihy]
      )
    (ι_mul_ι_mul := by
      intro m₁ m₂ x hx ih
      simp only [motive, map_mul, neutralCliffordRep_ι,
        Module.End.mul_apply]
      have ih' : neutralCliffordRep x ψ ∈
          LinearMap.range chiralProjectorPlus :=
        (mem_range_chiralProjectorPlus_iff _).2 ih
      exact (mem_range_chiralProjectorPlus_iff _).1
        (neutralAction_pair_mem_same_chirality_of_mem_plus m₁ m₂
          (neutralCliffordRep x ψ) ih'))
    a.1 a.2
  change gradeInvolution (neutralCliffordRep a.1 ψ) =
    neutralCliffordRep a.1 ψ
  exact hm

theorem neutralCliffordRepEven_mem_minus
    (a : CliffordAlgebra.even NeutralQ) (ψ : Spinor)
    (hψ : ψ ∈ LinearMap.range chiralProjectorMinus) :
    neutralCliffordRepEven a ψ ∈ LinearMap.range chiralProjectorMinus := by
  rw [mem_range_chiralProjectorMinus_iff] at hψ ⊢
  let motive : ∀ x, x ∈ CliffordAlgebra.evenOdd NeutralQ 0 → Prop :=
    fun x _ => gradeInvolution (neutralCliffordRep x ψ) =
      -(neutralCliffordRep x ψ)
  have hm := CliffordAlgebra.even_induction (Q := NeutralQ)
    (motive := motive)
    (algebraMap := by
      intro r
      simp [motive, hψ])
    (add := by
      intro x y hx hy ihx ihy
      simp only [motive, map_add, LinearMap.add_apply, ihx, ihy]
      abel)
    (ι_mul_ι_mul := by
      intro m₁ m₂ x hx ih
      simp only [motive, map_mul, neutralCliffordRep_ι,
        Module.End.mul_apply]
      have ih' : neutralCliffordRep x ψ ∈
          LinearMap.range chiralProjectorMinus :=
        (mem_range_chiralProjectorMinus_iff _).2 ih
      exact (mem_range_chiralProjectorMinus_iff _).1
        (neutralAction_pair_mem_same_chirality_of_mem_minus m₁ m₂
          (neutralCliffordRep x ψ) ih'))
    a.1 a.2
  change gradeInvolution (neutralCliffordRep a.1 ψ) =
    -(neutralCliffordRep a.1 ψ)
  exact hm

noncomputable def neutralCliffordRepEvenPlus
    (a : CliffordAlgebra.even NeutralQ) :
    Module.End ℝ (LinearMap.range chiralProjectorPlus) where
  toFun ψ :=
    ⟨neutralCliffordRepEven a ψ,
      neutralCliffordRepEven_mem_plus a ψ ψ.property⟩
  map_add' ψ φ := by
    apply Subtype.ext
    exact map_add (neutralCliffordRepEven a) (ψ : Spinor) (φ : Spinor)
  map_smul' c ψ := by
    apply Subtype.ext
    exact map_smul (neutralCliffordRepEven a) c (ψ : Spinor)

@[simp] theorem neutralCliffordRepEvenPlus_apply
    (a : CliffordAlgebra.even NeutralQ)
    (ψ : LinearMap.range chiralProjectorPlus) :
    (neutralCliffordRepEvenPlus a ψ : Spinor) =
      neutralCliffordRepEven a ψ :=
  rfl

noncomputable def neutralCliffordRepEvenMinus
    (a : CliffordAlgebra.even NeutralQ) :
    Module.End ℝ (LinearMap.range chiralProjectorMinus) where
  toFun ψ :=
    ⟨neutralCliffordRepEven a ψ,
      neutralCliffordRepEven_mem_minus a ψ ψ.property⟩
  map_add' ψ φ := by
    apply Subtype.ext
    exact map_add (neutralCliffordRepEven a) (ψ : Spinor) (φ : Spinor)
  map_smul' c ψ := by
    apply Subtype.ext
    exact map_smul (neutralCliffordRepEven a) c (ψ : Spinor)

@[simp] theorem neutralCliffordRepEvenMinus_apply
    (a : CliffordAlgebra.even NeutralQ)
    (ψ : LinearMap.range chiralProjectorMinus) :
    (neutralCliffordRepEvenMinus a ψ : Spinor) =
      neutralCliffordRepEven a ψ :=
  rfl

noncomputable def neutralCliffordRepEvenPlusAlgHom :
    CliffordAlgebra.even NeutralQ →ₐ[ℝ]
      Module.End ℝ (LinearMap.range chiralProjectorPlus) where
  toFun := neutralCliffordRepEvenPlus
  map_one' := by
    ext ψ
    simp [neutralCliffordRepEvenPlus, neutralCliffordRepEven]
  map_mul' a b := by
    ext ψ
    change neutralCliffordRepEven (a * b) ψ =
      neutralCliffordRepEven a (neutralCliffordRepEven b ψ)
    simp [neutralCliffordRepEven]
  map_zero' := by
    ext ψ
    simp [neutralCliffordRepEvenPlus, neutralCliffordRepEven]
  map_add' a b := by
    ext ψ
    simp [neutralCliffordRepEvenPlus, neutralCliffordRepEven]
  commutes' r := by
    ext ψ
    simp [neutralCliffordRepEvenPlus, neutralCliffordRepEven]

noncomputable def neutralCliffordRepEvenMinusAlgHom :
    CliffordAlgebra.even NeutralQ →ₐ[ℝ]
      Module.End ℝ (LinearMap.range chiralProjectorMinus) where
  toFun := neutralCliffordRepEvenMinus
  map_one' := by
    ext ψ
    simp [neutralCliffordRepEvenMinus, neutralCliffordRepEven]
  map_mul' a b := by
    ext ψ
    change neutralCliffordRepEven (a * b) ψ =
      neutralCliffordRepEven a (neutralCliffordRepEven b ψ)
    simp [neutralCliffordRepEven]
  map_zero' := by
    ext ψ
    simp [neutralCliffordRepEvenMinus, neutralCliffordRepEven]
  map_add' a b := by
    ext ψ
    simp [neutralCliffordRepEvenMinus, neutralCliffordRepEven]
  commutes' r := by
    ext ψ
    simp [neutralCliffordRepEvenMinus, neutralCliffordRepEven]

@[simp] theorem neutralCliffordRepEvenPlusAlgHom_ι
    (w z : NeutralSpace) (ψ : LinearMap.range chiralProjectorPlus) :
    (neutralCliffordRepEvenPlusAlgHom
        ((CliffordAlgebra.even.ι NeutralQ).bilin w z) ψ : Spinor) =
      neutralAction w (neutralAction z ψ) := by
  change (neutralCliffordRepEven
      ((CliffordAlgebra.even.ι NeutralQ).bilin w z) ψ : Spinor) = _
  rw [neutralCliffordRepEven_ι]
  rfl

@[simp] theorem neutralCliffordRepEvenMinusAlgHom_ι
    (w z : NeutralSpace) (ψ : LinearMap.range chiralProjectorMinus) :
    (neutralCliffordRepEvenMinusAlgHom
        ((CliffordAlgebra.even.ι NeutralQ).bilin w z) ψ : Spinor) =
      neutralAction w (neutralAction z ψ) := by
  change (neutralCliffordRepEven
      ((CliffordAlgebra.even.ι NeutralQ).bilin w z) ψ : Spinor) = _
  rw [neutralCliffordRepEven_ι]
  rfl

theorem chiralProjector_ranges_finrank_add :
    Module.finrank ℝ (LinearMap.range chiralProjectorPlus) +
        Module.finrank ℝ (LinearMap.range chiralProjectorMinus) =
      Module.finrank ℝ Spinor := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range chiralProjectorPlus)
    (LinearMap.range chiralProjectorMinus)
  rw [chiralProjector_ranges_sup, chiralProjector_ranges_inf,
    finrank_top, finrank_bot] at h
  exact h.symm

noncomputable def chiralRangesLinearEquiv :
    LinearMap.range chiralProjectorPlus ≃ₗ[ℝ]
      LinearMap.range chiralProjectorMinus :=
  let γ : SpinorEnd := gammaPlus 0
  have hγ (ψ : Spinor) :
      gradeInvolution (γ ψ) = -(γ (gradeInvolution ψ)) := by
    simpa [γ, gammaPlus] using
      gradeInvolution_neutralAction
        (basisVector 0, dualBasisVector 0) ψ
  have hγsq (ψ : Spinor) : γ (γ ψ) = ψ := by
    have h := congrArg (fun T : SpinorEnd => T ψ) (gammaPlus_sq 0)
    simpa only [γ, Module.End.mul_apply, Module.End.one_apply, one_smul] using h
  { toFun := fun ψ =>
        ⟨γ ψ,
        (mem_range_chiralProjectorMinus_iff (γ ψ)).2 (by
          rw [hγ]
          have hψ :=
            (mem_range_chiralProjectorPlus_iff (ψ : Spinor)).1 ψ.property
          rw [hψ])⟩
    invFun := fun ψ =>
        ⟨γ ψ,
        (mem_range_chiralProjectorPlus_iff (γ ψ)).2 (by
          rw [hγ]
          have hψ :=
            (mem_range_chiralProjectorMinus_iff (ψ : Spinor)).1 ψ.property
          rw [hψ]
          simp)⟩
    left_inv := by
      intro ψ
      apply Subtype.ext
      exact hγsq ψ
    right_inv := by
      intro ψ
      apply Subtype.ext
      exact hγsq ψ
    map_add' := by
      intro ψ φ
      apply Subtype.ext
      exact map_add γ (ψ : Spinor) (φ : Spinor)
    map_smul' := by
      intro c ψ
      apply Subtype.ext
      exact map_smul γ c (ψ : Spinor) }

theorem chiralProjectorPlus_finrank :
    Module.finrank ℝ (LinearMap.range chiralProjectorPlus) = 16 := by
  have heq := chiralRangesLinearEquiv.finrank_eq
  have hsum := chiralProjector_ranges_finrank_add
  rw [heq] at hsum
  rw [spinor_finrank] at hsum
  omega

theorem chiralProjectorMinus_finrank :
    Module.finrank ℝ (LinearMap.range chiralProjectorMinus) = 16 := by
  have heq := chiralRangesLinearEquiv.finrank_eq
  have hsum := chiralProjector_ranges_finrank_add
  rw [heq] at hsum
  rw [spinor_finrank] at hsum
  omega

/-! Coordinate matrix readouts of the two restricted even actions.  The bases
    are obtained only after the intrinsic dimensions `16 + 16` are proved. -/

noncomputable def chiralPlusBasis :
    Module.Basis (Fin 16) ℝ (LinearMap.range chiralProjectorPlus) :=
  Module.finBasisOfFinrankEq ℝ _ chiralProjectorPlus_finrank

noncomputable def chiralMinusBasis :
    Module.Basis (Fin 16) ℝ (LinearMap.range chiralProjectorMinus) :=
  Module.finBasisOfFinrankEq ℝ _ chiralProjectorMinus_finrank

noncomputable def neutralCliffordRepEvenPlusMatrix :
    CliffordAlgebra.even NeutralQ →ₐ[ℝ]
      Matrix (Fin 16) (Fin 16) ℝ :=
  (LinearMap.toMatrixAlgEquiv chiralPlusBasis).toAlgHom.comp
    neutralCliffordRepEvenPlusAlgHom

noncomputable def neutralCliffordRepEvenMinusMatrix :
    CliffordAlgebra.even NeutralQ →ₐ[ℝ]
      Matrix (Fin 16) (Fin 16) ℝ :=
  (LinearMap.toMatrixAlgEquiv chiralMinusBasis).toAlgHom.comp
    neutralCliffordRepEvenMinusAlgHom

@[simp] theorem neutralCliffordRepEvenPlusMatrix_ι
    (w z : NeutralSpace) :
    neutralCliffordRepEvenPlusMatrix
        ((CliffordAlgebra.even.ι NeutralQ).bilin w z) =
      (LinearMap.toMatrixAlgEquiv chiralPlusBasis)
        (neutralCliffordRepEvenPlusAlgHom
          ((CliffordAlgebra.even.ι NeutralQ).bilin w z)) := by
  rfl

@[simp] theorem neutralCliffordRepEvenMinusMatrix_ι
    (w z : NeutralSpace) :
    neutralCliffordRepEvenMinusMatrix
        ((CliffordAlgebra.even.ι NeutralQ).bilin w z) =
      (LinearMap.toMatrixAlgEquiv chiralMinusBasis)
        (neutralCliffordRepEvenMinusAlgHom
          ((CliffordAlgebra.even.ι NeutralQ).bilin w z)) := by
  rfl

noncomputable def chiralDecompositionEquiv :
    Spinor ≃ₗ[ℝ]
      LinearMap.range chiralProjectorPlus ×
        LinearMap.range chiralProjectorMinus :=
  let hplus (ψ : LinearMap.range chiralProjectorPlus) :
      chiralProjectorPlus ψ = ψ := by
    rcases ψ.property with ⟨u, hu⟩
    rw [← hu]
    have h := congrArg (fun T : SpinorEnd => T u)
      chiralProjectorPlus_idempotent
    simpa [Module.End.mul_apply] using h
  let hminus (ψ : LinearMap.range chiralProjectorMinus) :
      chiralProjectorMinus ψ = ψ := by
    rcases ψ.property with ⟨u, hu⟩
    rw [← hu]
    have h := congrArg (fun T : SpinorEnd => T u)
      chiralProjectorMinus_idempotent
    simpa [Module.End.mul_apply] using h
  let hplusMinus (ψ : LinearMap.range chiralProjectorMinus) :
      chiralProjectorPlus ψ = 0 := by
    rcases ψ.property with ⟨u, hu⟩
    rw [← hu]
    have h := congrArg (fun T : SpinorEnd => T u)
      chiralProjectors_plus_mul_minus
    simpa [Module.End.mul_apply] using h
  let hminusPlus (ψ : LinearMap.range chiralProjectorPlus) :
      chiralProjectorMinus ψ = 0 := by
    rcases ψ.property with ⟨u, hu⟩
    rw [← hu]
    have h := congrArg (fun T : SpinorEnd => T u)
      chiralProjectors_minus_mul_plus
    simpa [Module.End.mul_apply] using h
  { toFun := fun ψ =>
      ⟨⟨chiralProjectorPlus ψ, LinearMap.mem_range_self _ ψ⟩,
        ⟨chiralProjectorMinus ψ, LinearMap.mem_range_self _ ψ⟩⟩
    invFun := fun p => p.1 + p.2
    left_inv := by
      intro ψ
      exact chiralProjectors_decomposition ψ
    right_inv := by
      intro p
      apply Prod.ext
      · apply Subtype.ext
        change chiralProjectorPlus (p.1 + p.2) = p.1
        rw [map_add, hplus p.1, hplusMinus p.2, add_zero]
      · apply Subtype.ext
        change chiralProjectorMinus (p.1 + p.2) = p.2
        rw [map_add, hminusPlus p.1, hminus p.2, zero_add]
    map_add' := by
      intro ψ φ
      apply Prod.ext
      · apply Subtype.ext
        change chiralProjectorPlus (ψ + φ) =
          chiralProjectorPlus ψ + chiralProjectorPlus φ
        exact map_add chiralProjectorPlus ψ φ
      · apply Subtype.ext
        change chiralProjectorMinus (ψ + φ) =
          chiralProjectorMinus ψ + chiralProjectorMinus φ
        exact map_add chiralProjectorMinus ψ φ
    map_smul' := by
      intro c ψ
      apply Prod.ext
      · apply Subtype.ext
        change chiralProjectorPlus (c • ψ) =
          c • chiralProjectorPlus ψ
        exact map_smul chiralProjectorPlus c ψ
      · apply Subtype.ext
        change chiralProjectorMinus (c • ψ) =
          c • chiralProjectorMinus ψ
        exact map_smul chiralProjectorMinus c ψ }

end InfoGeometry.Clifford.SplitClifford55ExteriorParity
