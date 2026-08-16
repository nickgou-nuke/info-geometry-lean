import InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
import InfoGeometry.Clifford.Cl55ChevalleySpinorActionBridge

/-!
# Identification of the two neutral quadratic-form presentations

The Chevalley carrier uses the quadratic form `splitQ` on `W × W*`.  The
native `Q55` transport owner uses `canonicalNeutralFormUnscaled` on the same
neutral carrier.  This file proves that these are the same form, so the
existing explicit isometry to `Q55` can be consumed by the Chevalley layer.

No explicit basis-by-basis identification with a chosen gamma-matrix basis,
and no physical spin interpretation, is claimed here.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55NeutralFormBridge

open InfoGeometry.Lie.ChevalleySpinor
open InfoGeometry.Clifford.Cl55ChevalleySpinorActionBridge
open InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open CliffordAlgebra

abbrev W5 := Fin 5 → ℝ
abbrev Neutral55 := SplitV ℝ W5
abbrev ChevalleyQ55 : QuadraticForm ℝ Neutral55 :=
  splitQ (R := ℝ) (W := W5)
abbrev ChevalleySpin55 := spinGroup ChevalleyQ55
abbrev SpinMatrixGL55 := Matrix.GeneralLinearGroup (Fin (2 ^ 5)) ℝ

theorem splitQ_eq_canonicalNeutralFormUnscaled :
    ChevalleyQ55 = canonicalNeutralFormUnscaled (E := W5) := by
  ext x
  rcases x with ⟨v, φ⟩
  simp [ChevalleyQ55, splitQ, splitBilin,
    canonicalNeutralFormUnscaled_apply]

theorem splitQ_apply (v : W5) (φ : Module.Dual ℝ W5) :
    ChevalleyQ55 (v, φ) = φ v := by
  simp [ChevalleyQ55, splitQ, splitBilin]

theorem splitQ_eq_q55_after_neutralToV55 (x : Neutral55) :
    Clifford55.Q55 (neutralToV55 x) = ChevalleyQ55 x := by
  rw [q55_neutralToV55]
  rw [splitQ_eq_canonicalNeutralFormUnscaled]

noncomputable def neutralToV55_isometry_for_chevalleyQ :
    QuadraticMap.IsometryEquiv ChevalleyQ55 Clifford55.Q55 := by
  exact {
    toLinearEquiv := neutralToV55
    map_app' := by
      intro x
      exact splitQ_eq_q55_after_neutralToV55 x
  }

noncomputable def neutralCliffordAlgEquiv_for_chevalleyQ :
    CliffordAlgebra ChevalleyQ55 ≃ₐ[ℝ] Clifford55.Cl55 :=
  CliffordAlgebra.equivOfIsometry neutralToV55_isometry_for_chevalleyQ

private theorem algEquiv_transport_ι
    {q q' : QuadraticForm ℝ Neutral55}
    (h : q = q')
    (e : CliffordAlgebra q' ≃ₐ[ℝ]
      InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)
    (x : Neutral55) :
    (h ▸ e) (CliffordAlgebra.ι q x) =
      e (CliffordAlgebra.ι q' x) := by
  subst q'
  rfl

noncomputable def neutralChevalleySpinorAlgEquiv :
    CliffordAlgebra ChevalleyQ55 ≃ₐ[ℝ]
      InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 := by
  let h := splitQ_eq_canonicalNeutralFormUnscaled
  exact h ▸ neutralCliffordMatrixAlgEquiv

@[simp] theorem neutralCliffordAlgEquiv_for_chevalleyQ_ι
    (x : Neutral55) :
    neutralCliffordAlgEquiv_for_chevalleyQ
        (CliffordAlgebra.ι ChevalleyQ55 x) =
      Clifford55.ι55 (neutralToV55 x) := by
  exact CliffordAlgebra.map_apply_ι _ _

private theorem equiv_map_involute (x : CliffordAlgebra ChevalleyQ55) :
    neutralCliffordAlgEquiv_for_chevalleyQ (CliffordAlgebra.involute x) =
      CliffordAlgebra.involute
        (neutralCliffordAlgEquiv_for_chevalleyQ x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    simp [neutralCliffordAlgEquiv_for_chevalleyQ,
      CliffordAlgebra.equivOfIsometry]
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem equiv_map_reverse (x : CliffordAlgebra ChevalleyQ55) :
    neutralCliffordAlgEquiv_for_chevalleyQ (CliffordAlgebra.reverse x) =
      CliffordAlgebra.reverse
        (neutralCliffordAlgEquiv_for_chevalleyQ x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    simp [neutralCliffordAlgEquiv_for_chevalleyQ,
      CliffordAlgebra.equivOfIsometry]
  | mul a b ha hb => simp only [CliffordAlgebra.reverse.map_mul, map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem neutralCliffordAlgEquiv_map_star (x : CliffordAlgebra ChevalleyQ55) :
    neutralCliffordAlgEquiv_for_chevalleyQ (star x) =
      star (neutralCliffordAlgEquiv_for_chevalleyQ x) := by
  simp only [CliffordAlgebra.star_def, equiv_map_involute, equiv_map_reverse]

set_option maxHeartbeats 5000000 in
theorem neutralCliffordAlgEquiv_maps_lipschitzGroup
    {u : (CliffordAlgebra ChevalleyQ55)ˣ}
    (hu : u ∈ lipschitzGroup ChevalleyQ55) :
    Units.map neutralCliffordAlgEquiv_for_chevalleyQ.toRingEquiv.toMonoidHom u ∈
      lipschitzGroup Clifford55.Q55 := by
  unfold lipschitzGroup at hu ⊢
  induction hu using Subgroup.closure_induction'' with
  | mem u hu =>
    rcases hu with ⟨m, hm⟩
    refine Subgroup.subset_closure ?_
    refine ⟨neutralToV55 m, ?_⟩
    change (CliffordAlgebra.ι Clifford55.Q55) (neutralToV55 m) =
      neutralCliffordAlgEquiv_for_chevalleyQ
        (u : CliffordAlgebra ChevalleyQ55)
    rw [← hm, neutralCliffordAlgEquiv_for_chevalleyQ_ι]
  | inv_mem u hu =>
    rcases hu with ⟨m, hm⟩
    have hgen :
        Units.map neutralCliffordAlgEquiv_for_chevalleyQ.toRingEquiv.toMonoidHom u ∈
          Subgroup.closure
            ((↑) ⁻¹' Set.range (CliffordAlgebra.ι Clifford55.Q55) :
              Set (Clifford55.Cl55)ˣ) := by
      refine Subgroup.subset_closure ?_
      refine ⟨neutralToV55 m, ?_⟩
      change (CliffordAlgebra.ι Clifford55.Q55) (neutralToV55 m) =
        neutralCliffordAlgEquiv_for_chevalleyQ
          (u : CliffordAlgebra ChevalleyQ55)
      rw [← hm, neutralCliffordAlgEquiv_for_chevalleyQ_ι]
    simpa only [map_inv] using Subgroup.inv_mem _ hgen
  | one => simpa only [map_one] using Subgroup.one_mem _
  | mul u v _ _ hu hv =>
    simpa only [map_mul] using Subgroup.mul_mem _ hu hv

set_option maxHeartbeats 5000000 in
private theorem map_even
    {x : CliffordAlgebra ChevalleyQ55}
    (hx : x ∈ CliffordAlgebra.even ChevalleyQ55) :
    neutralCliffordAlgEquiv_for_chevalleyQ x ∈
      CliffordAlgebra.even Clifford55.Q55 := by
  change x ∈ CliffordAlgebra.evenOdd ChevalleyQ55 0 at hx
  change neutralCliffordAlgEquiv_for_chevalleyQ x ∈
    CliffordAlgebra.evenOdd Clifford55.Q55 0
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
    rw [neutralCliffordAlgEquiv_for_chevalleyQ.commutes]
    exact SetLike.algebraMap_mem_graded
      (CliffordAlgebra.evenOdd Clifford55.Q55) r
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    simp only [map_mul, neutralCliffordAlgEquiv_for_chevalleyQ_ι]
    exact (zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded
      (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero
        Clifford55.Q55 (neutralToV55 m₁) (neutralToV55 m₂)) ih)

private theorem map_spinGroup_mem {g : ChevalleySpin55} :
    neutralCliffordAlgEquiv_for_chevalleyQ
        (g : CliffordAlgebra ChevalleyQ55) ∈ Clifford55.Spin55 := by
  rw [spinGroup.mem_iff]
  constructor
  · rw [pinGroup.mem_iff]
    constructor
    · refine (Submonoid.mem_map).2 ⟨
        Units.map neutralCliffordAlgEquiv_for_chevalleyQ.toRingEquiv.toMonoidHom
          (spinGroup.toUnits g), ?_, rfl⟩
      change Units.map
        neutralCliffordAlgEquiv_for_chevalleyQ.toRingEquiv.toMonoidHom
          (spinGroup.toUnits g) ∈ (lipschitzGroup Clifford55.Q55).toSubmonoid
      exact neutralCliffordAlgEquiv_maps_lipschitzGroup
        (spinGroup.units_mem_lipschitzGroup (x := spinGroup.toUnits g) g.prop)
    · rw [Unitary.mem_iff]
      constructor
      · have h := congrArg (neutralCliffordAlgEquiv_for_chevalleyQ)
          ((pinGroup.mem_unitary (spinGroup.mem_pin g.prop)).1)
        simpa only [map_mul, neutralCliffordAlgEquiv_map_star, map_one] using h
      · have h' := congrArg (neutralCliffordAlgEquiv_for_chevalleyQ)
          ((pinGroup.mem_unitary (spinGroup.mem_pin g.prop)).2)
        simpa only [map_mul, neutralCliffordAlgEquiv_map_star, map_one] using h'
  · change neutralCliffordAlgEquiv_for_chevalleyQ
      (g : CliffordAlgebra ChevalleyQ55) ∈
      CliffordAlgebra.evenOdd Clifford55.Q55 0
    exact map_even (spinGroup.mem_even g.prop)

@[simp] private theorem neutralCliffordAlgEquiv_symm_ι (y : Clifford55.V55) :
    neutralCliffordAlgEquiv_for_chevalleyQ.symm
        (Clifford55.ι55 y) =
      CliffordAlgebra.ι ChevalleyQ55 (neutralToV55.symm y) := by
  apply neutralCliffordAlgEquiv_for_chevalleyQ.injective
  rw [neutralCliffordAlgEquiv_for_chevalleyQ.apply_symm_apply]
  rw [neutralCliffordAlgEquiv_for_chevalleyQ_ι]
  simp

@[simp] theorem neutralCliffordAlgEquiv_for_chevalleyQ_symm_ι
    (y : Clifford55.V55) :
    neutralCliffordAlgEquiv_for_chevalleyQ.symm
        (Clifford55.ι55 y) =
      CliffordAlgebra.ι ChevalleyQ55 (neutralToV55.symm y) := by
  exact neutralCliffordAlgEquiv_symm_ι y

private theorem equiv_symm_map_involute (x : Clifford55.Cl55) :
    neutralCliffordAlgEquiv_for_chevalleyQ.symm (CliffordAlgebra.involute x) =
      CliffordAlgebra.involute
        (neutralCliffordAlgEquiv_for_chevalleyQ.symm x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    simp [neutralCliffordAlgEquiv_symm_ι]
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem equiv_symm_map_reverse (x : Clifford55.Cl55) :
    neutralCliffordAlgEquiv_for_chevalleyQ.symm (CliffordAlgebra.reverse x) =
      CliffordAlgebra.reverse
        (neutralCliffordAlgEquiv_for_chevalleyQ.symm x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    simp [neutralCliffordAlgEquiv_symm_ι]
  | mul a b ha hb => simp only [CliffordAlgebra.reverse.map_mul, map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem neutralCliffordAlgEquiv_symm_map_star (x : Clifford55.Cl55) :
    neutralCliffordAlgEquiv_for_chevalleyQ.symm (star x) =
      star (neutralCliffordAlgEquiv_for_chevalleyQ.symm x) := by
  simp only [CliffordAlgebra.star_def, equiv_symm_map_involute,
    equiv_symm_map_reverse]

set_option maxHeartbeats 5000000 in
theorem neutralCliffordAlgEquiv_symm_maps_lipschitzGroup
    {u : Clifford55.Cl55ˣ}
    (hu : u ∈ lipschitzGroup Clifford55.Q55) :
    Units.map neutralCliffordAlgEquiv_for_chevalleyQ.symm.toRingEquiv.toMonoidHom u
      ∈ lipschitzGroup ChevalleyQ55 := by
  unfold lipschitzGroup at hu ⊢
  induction hu using Subgroup.closure_induction'' with
  | mem u hu =>
    rcases hu with ⟨m, hm⟩
    refine Subgroup.subset_closure ?_
    refine ⟨neutralToV55.symm m, ?_⟩
    change (CliffordAlgebra.ι ChevalleyQ55) (neutralToV55.symm m) =
      neutralCliffordAlgEquiv_for_chevalleyQ.symm (u : Clifford55.Cl55)
    rw [← hm, neutralCliffordAlgEquiv_symm_ι]
  | inv_mem u hu =>
    rcases hu with ⟨m, hm⟩
    have hgen :
        Units.map neutralCliffordAlgEquiv_for_chevalleyQ.symm.toRingEquiv.toMonoidHom u ∈
          Subgroup.closure
            ((↑) ⁻¹' Set.range (CliffordAlgebra.ι ChevalleyQ55) :
              Set (CliffordAlgebra ChevalleyQ55)ˣ) := by
      refine Subgroup.subset_closure ?_
      refine ⟨neutralToV55.symm m, ?_⟩
      change (CliffordAlgebra.ι ChevalleyQ55) (neutralToV55.symm m) =
        neutralCliffordAlgEquiv_for_chevalleyQ.symm (u : Clifford55.Cl55)
      rw [← hm, neutralCliffordAlgEquiv_symm_ι]
    simpa only [map_inv] using Subgroup.inv_mem _ hgen
  | one => simpa only [map_one] using Subgroup.one_mem _
  | mul u v _ _ hu hv => simpa only [map_mul] using Subgroup.mul_mem _ hu hv

set_option maxHeartbeats 5000000 in
private theorem map_even_symm
    {x : Clifford55.Cl55}
    (hx : x ∈ CliffordAlgebra.even Clifford55.Q55) :
    neutralCliffordAlgEquiv_for_chevalleyQ.symm x
      ∈ CliffordAlgebra.even ChevalleyQ55 := by
  change x ∈ CliffordAlgebra.evenOdd Clifford55.Q55 0 at hx
  change neutralCliffordAlgEquiv_for_chevalleyQ.symm x ∈
    CliffordAlgebra.evenOdd ChevalleyQ55 0
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
    rw [neutralCliffordAlgEquiv_for_chevalleyQ.symm.commutes]
    exact SetLike.algebraMap_mem_graded
      (CliffordAlgebra.evenOdd ChevalleyQ55) r
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    simp only [map_mul, neutralCliffordAlgEquiv_symm_ι]
    exact (zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded
      (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero
        ChevalleyQ55 (neutralToV55.symm m₁) (neutralToV55.symm m₂)) ih)

private theorem map_spinGroup_mem_symm {g : Clifford55.Spin55} :
    neutralCliffordAlgEquiv_for_chevalleyQ.symm (g : Clifford55.Cl55)
      ∈ ChevalleySpin55 := by
  rw [spinGroup.mem_iff]
  constructor
  · rw [pinGroup.mem_iff]
    constructor
    · refine (Submonoid.mem_map).2 ⟨
        Units.map neutralCliffordAlgEquiv_for_chevalleyQ.symm.toRingEquiv.toMonoidHom
          (spinGroup.toUnits g), ?_, rfl⟩
      change Units.map
        neutralCliffordAlgEquiv_for_chevalleyQ.symm.toRingEquiv.toMonoidHom
          (spinGroup.toUnits g) ∈ (lipschitzGroup ChevalleyQ55).toSubmonoid
      exact neutralCliffordAlgEquiv_symm_maps_lipschitzGroup
        (spinGroup.units_mem_lipschitzGroup (x := spinGroup.toUnits g) g.prop)
    · rw [Unitary.mem_iff]
      constructor
      · have h := congrArg (neutralCliffordAlgEquiv_for_chevalleyQ.symm)
          ((pinGroup.mem_unitary (spinGroup.mem_pin g.prop)).1)
        simpa only [map_mul, neutralCliffordAlgEquiv_symm_map_star, map_one] using h
      · have h' := congrArg (neutralCliffordAlgEquiv_for_chevalleyQ.symm)
          ((pinGroup.mem_unitary (spinGroup.mem_pin g.prop)).2)
        simpa only [map_mul, neutralCliffordAlgEquiv_symm_map_star, map_one] using h'
  · change neutralCliffordAlgEquiv_for_chevalleyQ.symm
      (g : Clifford55.Cl55) ∈ CliffordAlgebra.evenOdd ChevalleyQ55 0
    exact map_even_symm (spinGroup.mem_even g.prop)

noncomputable def spinGroupTransport
    (g : ChevalleySpin55) : Clifford55.Spin55 :=
  ⟨neutralCliffordAlgEquiv_for_chevalleyQ
      (g : CliffordAlgebra ChevalleyQ55), map_spinGroup_mem⟩

@[simp] theorem spinGroupTransport_coe (g : ChevalleySpin55) :
    (spinGroupTransport g : Clifford55.Cl55) =
      neutralCliffordAlgEquiv_for_chevalleyQ
        (g : CliffordAlgebra ChevalleyQ55) := by
  rfl

noncomputable def spinGroupTransportHom :
    ChevalleySpin55 →* Clifford55.Spin55 where
  toFun := spinGroupTransport
  map_one' := by
    apply Subtype.ext
    simp [spinGroupTransport]
  map_mul' g h := by
    apply Subtype.ext
    simp [spinGroupTransport]

theorem spinGroupTransportHom_injective :
    Function.Injective spinGroupTransportHom := by
  intro g h gh
  apply Subtype.ext
  apply neutralCliffordAlgEquiv_for_chevalleyQ.injective
  have hcoe := congrArg (fun z : Clifford55.Spin55 =>
    (z : Clifford55.Cl55)) gh
  simpa only [spinGroupTransport_coe] using hcoe

theorem spinGroupTransportHom_surjective :
    Function.Surjective spinGroupTransportHom := by
  intro g
  refine ⟨⟨neutralCliffordAlgEquiv_for_chevalleyQ.symm
      (g : Clifford55.Cl55), map_spinGroup_mem_symm⟩, ?_⟩
  apply Subtype.ext
  change neutralCliffordAlgEquiv_for_chevalleyQ
      (neutralCliffordAlgEquiv_for_chevalleyQ.symm (g : Clifford55.Cl55)) =
    (g : Clifford55.Cl55)
  exact neutralCliffordAlgEquiv_for_chevalleyQ.apply_symm_apply _

noncomputable def spinGroupTransportEquiv :
    ChevalleySpin55 ≃* Clifford55.Spin55 :=
  MulEquiv.ofBijective spinGroupTransportHom
    ⟨spinGroupTransportHom_injective, spinGroupTransportHom_surjective⟩

@[simp] theorem spinGroupTransportEquiv_apply (g : ChevalleySpin55) :
    spinGroupTransportEquiv g = spinGroupTransportHom g := rfl

@[simp] theorem neutralChevalleySpinorAlgEquiv_ι
    (x : Neutral55) :
    neutralChevalleySpinorAlgEquiv
        (CliffordAlgebra.ι ChevalleyQ55 x) =
      Clifford55.cl55SpinorRepresentation
        (Clifford55.ι55 (neutralToV55 x)) := by
  exact algEquiv_transport_ι splitQ_eq_canonicalNeutralFormUnscaled
    neutralCliffordMatrixAlgEquiv x |>.trans (neutralCliffordMatrixAlgEquiv_ι x)

/-! The algebra equivalence also transports native spin-group elements to
matrix units.  This is only an algebraic group representation; no compact,
Spin/Pin covering, or physical representation claim is made here. -/

noncomputable def matrixSpinRepresentation :
    ChevalleySpin55 →* SpinMatrixGL55 :=
  (Units.map neutralChevalleySpinorAlgEquiv.toRingEquiv.toMonoidHom).comp
    spinGroup.toUnits

theorem matrixSpinRepresentation_val (g : ChevalleySpin55) :
    ((matrixSpinRepresentation g : SpinMatrixGL55) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) =
      neutralChevalleySpinorAlgEquiv
        (g : CliffordAlgebra ChevalleyQ55) := by
  rfl

theorem matrixSpinRepresentation_mul (g h : ChevalleySpin55) :
    matrixSpinRepresentation (g * h) =
      matrixSpinRepresentation g * matrixSpinRepresentation h := by
  exact map_mul matrixSpinRepresentation g h

theorem matrixSpinRepresentation_inv (g : ChevalleySpin55) :
    matrixSpinRepresentation g⁻¹ =
      (matrixSpinRepresentation g)⁻¹ := by
  exact map_inv matrixSpinRepresentation g

theorem matrixSpinRepresentation_one :
    matrixSpinRepresentation (1 : ChevalleySpin55) = 1 := by
  exact map_one matrixSpinRepresentation

theorem matrixSpinRepresentation_injective :
    Function.Injective matrixSpinRepresentation := by
  intro g h gh
  apply Subtype.ext
  apply neutralChevalleySpinorAlgEquiv.injective
  have hmatrix := congrArg
    (fun A : SpinMatrixGL55 =>
      (A : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)) gh
  simpa only [matrixSpinRepresentation_val] using hmatrix

/-! The matrix representation can now be read on the native `Q55` Spin
group by precomposition with the proved cross-form group equivalence. -/

noncomputable def nativeMatrixSpinRepresentation :
    Clifford55.Spin55 →* SpinMatrixGL55 :=
  matrixSpinRepresentation.comp spinGroupTransportEquiv.symm.toMonoidHom

theorem nativeMatrixSpinRepresentation_injective :
    Function.Injective nativeMatrixSpinRepresentation := by
  intro g h gh
  apply spinGroupTransportEquiv.symm.injective
  apply matrixSpinRepresentation_injective
  exact gh

theorem nativeMatrixSpinRepresentation_mul (g h : Clifford55.Spin55) :
    nativeMatrixSpinRepresentation (g * h) =
      nativeMatrixSpinRepresentation g * nativeMatrixSpinRepresentation h := by
  exact map_mul nativeMatrixSpinRepresentation g h

theorem nativeMatrixSpinRepresentation_inv (g : Clifford55.Spin55) :
    nativeMatrixSpinRepresentation g⁻¹ =
      (nativeMatrixSpinRepresentation g)⁻¹ := by
  exact map_inv nativeMatrixSpinRepresentation g

theorem nativeMatrixSpinRepresentation_one :
    nativeMatrixSpinRepresentation (1 : Clifford55.Spin55) = 1 := by
  exact map_one nativeMatrixSpinRepresentation

theorem nativeMatrixSpinRepresentation_val (g : Clifford55.Spin55) :
    ((nativeMatrixSpinRepresentation g : SpinMatrixGL55) :
        InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) =
      neutralChevalleySpinorAlgEquiv
        ((spinGroupTransportEquiv.symm g : ChevalleySpin55) :
          CliffordAlgebra ChevalleyQ55) := by
  rfl

end InfoGeometry.Clifford.SplitClifford55NeutralFormBridge
