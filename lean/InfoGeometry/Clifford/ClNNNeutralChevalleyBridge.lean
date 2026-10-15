import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import InfoGeometry.Clifford.ClNN
import InfoGeometry.Clifford.ChevalleyPureSpinor
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
import InfoGeometry.Canonical.SuperGrassmannianManifold

/-!
# The recursive split tower and the neutral Chevalley carrier

For every finite rank `n`, this file identifies the recursive symmetric split
quadratic space `SplitSpace n` with the evaluation-paired neutral space
`(Fin n → ℝ) × (Fin n → ℝ)ᴰ`.  The map is coordinatewise
`(u,φ) ↦ ((uᵢ + φᵢ)/2, (uᵢ - φᵢ)/2)`.  Its quadratic-form identity lifts by
Mathlib's `CliffordAlgebra.equivOfIsometry` to the corresponding algebra
equivalence.  This is the all-rank carrier bridge; it does not identify wedge
product with Clifford multiplication.
-/

noncomputable section

namespace InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

abbrev TowerSpace (n : ℕ) := InfoGeometry.CliffordTower.SplitSpace n
abbrev TowerForm (n : ℕ) := InfoGeometry.CliffordTower.Qsplit n

abbrev Vector (n : ℕ) := Fin n → ℝ
abbrev Neutral (n : ℕ) := PhaseSpaceCarrier (Vector n)

/-- Coordinates of a covector in the dual basis associated to `Pi.basisFun`. -/
def dualCoordinates (n : ℕ) :
    Module.Dual ℝ (Vector n) ≃ₗ[ℝ] Vector n :=
  (Pi.basisFun ℝ (Fin n)).toDualEquiv.symm

theorem dualCoordinates_apply (n : ℕ) (φ : Module.Dual ℝ (Vector n)) (i : Fin n) :
    dualCoordinates n φ i = φ (Pi.single i 1) := by
  simpa [dualCoordinates] using
    (Module.Basis.coord_toDualEquiv_symm_apply
      (Pi.basisFun ℝ (Fin n)) i φ)

/-- Evaluation is the dot product of a vector with the dual coordinates. -/
theorem dualCoordinates_eval (n : ℕ) (u : Vector n)
    (φ : Module.Dual ℝ (Vector n)) :
    (∑ i : Fin n, u i * dualCoordinates n φ i) = φ u := by
  classical
  calc
    (∑ i : Fin n, u i * dualCoordinates n φ i) =
        ∑ i : Fin n, φ (u i • (Pi.single i (1 : ℝ) : Vector n)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [dualCoordinates_apply]
          simp [smul_eq_mul]
    _ = φ (∑ i : Fin n, u i • (Pi.single i (1 : ℝ) : Vector n)) := by
          rw [map_sum]
    _ = φ u := by
          congr 1
          funext j
          simp [Pi.single_apply]

/-- The coordinatewise light-cone change of variables from the neutral pair
to the recursive split coordinates. -/
def neutralToWittCoordinates (n : ℕ) :
    Neutral n ≃ₗ[ℝ] (Fin n → ℝ × ℝ) where
  toFun X := fun i =>
    ((X.1 i + dualCoordinates n X.2 i) / 2,
      (X.1 i - dualCoordinates n X.2 i) / 2)
  invFun z :=
    (fun i => (z i).1 + (z i).2,
      (dualCoordinates n).symm (fun i => (z i).1 - (z i).2))
  left_inv := by
    rintro ⟨u, φ⟩
    apply Prod.ext
    · funext i
      change ((u i + dualCoordinates n φ i) / 2 +
        (u i - dualCoordinates n φ i) / 2) = u i
      ring
    · apply (dualCoordinates n).injective
      change dualCoordinates n
          ((dualCoordinates n).symm (fun i =>
            (u i + dualCoordinates n φ i) / 2 -
              (u i - dualCoordinates n φ i) / 2)) = dualCoordinates n φ
      rw [(dualCoordinates n).apply_symm_apply]
      funext i
      ring
  right_inv := by
    intro z
    funext i
    change (((z i).1 + (z i).2 +
        dualCoordinates n ((dualCoordinates n).symm
          (fun j => (z j).1 - (z j).2)) i) / 2,
      ((z i).1 + (z i).2 -
        dualCoordinates n ((dualCoordinates n).symm
          (fun j => (z j).1 - (z j).2)) i) / 2) = z i
    rw [(dualCoordinates n).apply_symm_apply]
    apply Prod.ext <;> ring
  map_add' := by
    intro X Y
    rcases X with ⟨u, φ⟩
    rcases Y with ⟨v, ψ⟩
    funext i
    apply Prod.ext <;> simp [map_add] <;> ring
  map_smul' := by
    intro c X
    rcases X with ⟨u, φ⟩
    funext i
    apply Prod.ext <;> simp [map_smul] <;> ring

/-- Repack a finite family of split planes into the tower's recursive
head-tail presentation. -/
def packSplitCoordinates : (n : ℕ) →
    (Fin n → ℝ × ℝ) ≃ₗ[ℝ] TowerSpace n
  | 0 => LinearEquiv.refl ℝ _
  | n + 1 => by
      letI : AddCommGroup (TowerSpace n) :=
        InfoGeometry.CliffordTower.splitSpaceAddCommGroup n
      letI : Module ℝ (TowerSpace n) :=
        InfoGeometry.CliffordTower.splitSpaceModule n
      exact
        { toFun := fun z => (z 0, packSplitCoordinates n (fun i => z i.succ))
          invFun := fun x => Fin.cases x.1
            (fun i => (packSplitCoordinates n).symm x.2 i)
          left_inv := by
            intro z
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · rfl
            · simp
          right_inv := by
            intro x
            rcases x with ⟨head, tail⟩
            apply Prod.ext
            · rfl
            · exact (packSplitCoordinates n).right_inv tail
          map_add' := by
            intro x y
            apply Prod.ext
            · rfl
            · change packSplitCoordinates n
                ((fun i => x i.succ) + (fun i => y i.succ)) =
                  packSplitCoordinates n (fun i => x i.succ) +
                    packSplitCoordinates n (fun i => y i.succ)
              rw [(packSplitCoordinates n).map_add]
          map_smul' := by
            intro c x
            apply Prod.ext
            · rfl
            · change packSplitCoordinates n
                (c • (fun i => x i.succ)) =
                  c • packSplitCoordinates n (fun i => x i.succ)
              rw [(packSplitCoordinates n).map_smul]
              }

@[simp] theorem packSplitCoordinates_succ_apply (n : ℕ)
    (z : Fin (n + 1) → ℝ × ℝ) :
    packSplitCoordinates (n + 1) z =
      (z 0, packSplitCoordinates n (fun i => z i.succ)) := rfl

/-- The recursive tower quadratic form is the sum of its split-plane
coordinate forms. -/
theorem Qsplit_packSplitCoordinates (n : ℕ)
    (z : Fin n → ℝ × ℝ) :
    TowerForm n (packSplitCoordinates n z) =
      ∑ i : Fin n, ((z i).1 ^ 2 - (z i).2 ^ 2) := by
  induction n with
  | zero => simp [TowerForm, InfoGeometry.CliffordTower.Qsplit]
  | succ n ih =>
      rw [packSplitCoordinates_succ_apply,
        InfoGeometry.CliffordTower.Qsplit_succ_apply]
      rw [ih]
      simp only [Fin.sum_univ_succ,
        InfoGeometry.CliffordTower.Q11_apply]
      ring

/-- The explicit all-rank linear equivalence from the neutral Chevalley
phase space to the recursively presented symmetric split space. -/
def neutralToSplit (n : ℕ) : Neutral n ≃ₗ[ℝ] TowerSpace n :=
  (neutralToWittCoordinates n).trans (packSplitCoordinates n)

/-- The recursive symmetric split quadratic form is exactly evaluation on
the neutral phase-space carrier. -/
theorem Qsplit_neutralToSplit (n : ℕ) (X : Neutral n) :
    TowerForm n (neutralToSplit n X) =
      canonicalNeutralFormUnscaled (E := Vector n) X := by
  rcases X with ⟨u, φ⟩
  change TowerForm n
    (packSplitCoordinates n (neutralToWittCoordinates n (u, φ))) = _
  rw [Qsplit_packSplitCoordinates]
  rw [canonicalNeutralFormUnscaled_apply]
  calc
    (∑ i : Fin n,
        (((u i + dualCoordinates n φ i) / 2) ^ 2 -
          ((u i - dualCoordinates n φ i) / 2) ^ 2)) =
        ∑ i : Fin n, u i * dualCoordinates n φ i := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = φ u := dualCoordinates_eval n u φ

/-- The quadratic form used by the generic Chevalley spinor owner is the same
evaluation form as the repository's neutral phase-space owner. -/
theorem chevelleyQsplit_eq_neutralForm (n : ℕ) :
    InfoGeometry.Clifford.Qsplit (Vector n) =
      canonicalNeutralFormUnscaled (E := Vector n) := by
  ext X
  rcases X with ⟨u, φ⟩
  simp [InfoGeometry.Clifford.Qsplit,
    InfoGeometry.Clifford.Bsplit,
    canonicalNeutralFormUnscaled_apply]

/-- The finite Chevalley split form itself, not only its neutral-form alias,
is carried to the recursive symmetric split quadratic form. -/
theorem Qsplit_neutralToSplit_chevalley (n : ℕ) (X : Neutral n) :
    TowerForm n (neutralToSplit n X) =
      InfoGeometry.Clifford.Qsplit (Vector n) X := by
  rw [chevelleyQsplit_eq_neutralForm]
  exact Qsplit_neutralToSplit n X

/-- Isometry from the canonical neutral Chevalley form to the recursive
`symmetric split` form, valid at every natural-number rank. -/
def neutralToSplitIsometry (n : ℕ) :
    (InfoGeometry.Clifford.Qsplit (Vector n)).IsometryEquiv
      (TowerForm n) where
  __ := neutralToSplit n
  map_app' := Qsplit_neutralToSplit_chevalley n

/-- Native Mathlib Clifford-algebra equivalence between the neutral
Chevalley presentation and the recursive `Cl(n,n)` stage. -/
def neutralCliffordEquiv (n : ℕ) :
    CliffordAlgebra
        (InfoGeometry.Clifford.Qsplit (Vector n)) ≃ₐ[ℝ]
      CliffordAlgebra (TowerForm n) :=
  CliffordAlgebra.equivOfIsometry (neutralToSplitIsometry n)

@[simp] theorem neutralCliffordEquiv_ι (n : ℕ) (X : Neutral n) :
    neutralCliffordEquiv n
        (CliffordAlgebra.ι (InfoGeometry.Clifford.Qsplit (Vector n)) X) =
      CliffordAlgebra.ι (TowerForm n) (neutralToSplit n X) := by
  exact CliffordAlgebra.map_apply_ι _ _

/-- The recursive symmetric split Clifford algebra acts on the existing
Chevalley exterior-Fock spinor module by transporting its native neutral
creation/contraction representation along `neutralCliffordEquiv`. -/
noncomputable def towerSpinorRep (n : ℕ) :
    CliffordAlgebra (TowerForm n) →ₐ[ℝ]
      Module.End ℝ (InfoGeometry.Clifford.SpinorSpace (Vector n)) :=
  (InfoGeometry.Clifford.abstractSpinorRep (Vector n)).comp
    (neutralCliffordEquiv n).symm.toAlgHom

/-- On Clifford generators, the transported tower representation is exactly
the repository's Chevalley spinor action of the inverse neutral coordinate
map. -/
theorem towerSpinorRep_generator (n : ℕ) (x : TowerSpace n) :
    towerSpinorRep n (CliffordAlgebra.ι (TowerForm n) x) =
      InfoGeometry.Clifford.spinorAction
        ((neutralToSplit n).symm x) := by
  let X : Neutral n := (neutralToSplit n).symm x
  have hgen : neutralCliffordEquiv n
      (CliffordAlgebra.ι (InfoGeometry.Clifford.Qsplit (Vector n)) X) =
      CliffordAlgebra.ι (TowerForm n) x := by
    rw [neutralCliffordEquiv_ι]
    exact congrArg (CliffordAlgebra.ι (TowerForm n))
      ((neutralToSplit n).apply_symm_apply x)
  have hinv : (neutralCliffordEquiv n).symm
      (CliffordAlgebra.ι (TowerForm n) x) =
    CliffordAlgebra.ι (InfoGeometry.Clifford.Qsplit (Vector n)) X := by
    rw [← hgen]
    exact (neutralCliffordEquiv n).symm_apply_apply _
  change (InfoGeometry.Clifford.abstractSpinorRep (Vector n))
      ((neutralCliffordEquiv n).symm (CliffordAlgebra.ι (TowerForm n) x)) = _
  rw [hinv]
  simp [InfoGeometry.Clifford.abstractSpinorRep, X]

theorem neutralCliffordEquiv_involute (n : ℕ)
    (x : CliffordAlgebra (InfoGeometry.Clifford.Qsplit (Vector n))) :
    CliffordAlgebra.involute (neutralCliffordEquiv n x) =
      neutralCliffordEquiv n (CliffordAlgebra.involute x) := by
  have hhom :
      (CliffordAlgebra.involute (Q := TowerForm n)).comp
          (neutralCliffordEquiv n).toAlgHom =
        (neutralCliffordEquiv n).toAlgHom.comp
          (CliffordAlgebra.involute (Q :=
            InfoGeometry.Clifford.Qsplit (Vector n))) := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change CliffordAlgebra.involute
        ((neutralCliffordEquiv n)
          (CliffordAlgebra.ι (InfoGeometry.Clifford.Qsplit (Vector n)) v)) =
      (neutralCliffordEquiv n)
        (CliffordAlgebra.involute
          (CliffordAlgebra.ι (InfoGeometry.Clifford.Qsplit (Vector n)) v))
    rw [neutralCliffordEquiv_ι, CliffordAlgebra.involute_ι,
      CliffordAlgebra.involute_ι, map_neg, neutralCliffordEquiv_ι]
  exact congrArg (fun f => f x) hhom

/-- Over `ℝ`, the minus-eigenspace of the native Clifford grade involution is
exactly Mathlib's odd Clifford component. -/
theorem involute_eq_neg_iff_mem_odd
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) (x : CliffordAlgebra Q) :
    CliffordAlgebra.involute x = -x ↔
      x ∈ CliffordAlgebra.evenOdd Q 1 := by
  constructor
  · intro hneg
    obtain ⟨e, o, heo, _⟩ :=
      Submodule.existsUnique_add_of_isCompl
        (CliffordAlgebra.evenOdd_isCompl (Q := Q)) x
    have hinvol : CliffordAlgebra.involute x =
        (e : CliffordAlgebra Q) - o := by
      rw [← heo, map_add,
        CliffordAlgebra.involute_eq_of_mem_even e.property,
        CliffordAlgebra.involute_eq_of_mem_odd o.property]
      simp only [sub_eq_add_neg]
    have hdecomp :
        (e : CliffordAlgebra Q) - o = -((e : CliffordAlgebra Q) + o) := by
      calc
        (e : CliffordAlgebra Q) - o = CliffordAlgebra.involute x := hinvol.symm
        _ = -x := hneg
        _ = -((e : CliffordAlgebra Q) + o) := by rw [heo]
    have hneg_e : (e : CliffordAlgebra Q) = -(e : CliffordAlgebra Q) := by
      have h' : (e : CliffordAlgebra Q) + -(o : CliffordAlgebra Q) =
          -(e : CliffordAlgebra Q) + -(o : CliffordAlgebra Q) := by
        simpa only [sub_eq_add_neg, neg_add] using hdecomp
      exact add_right_cancel h'
    have htwo : (e : CliffordAlgebra Q) + e = 0 := by
      calc
        (e : CliffordAlgebra Q) + e =
            (e : CliffordAlgebra Q) + (-(e : CliffordAlgebra Q)) :=
          congrArg (fun z : CliffordAlgebra Q => (e : CliffordAlgebra Q) + z) hneg_e
        _ = 0 := add_neg_cancel _
    have hezero : (e : CliffordAlgebra Q) = 0 := by
      have hscalar : (2 : ℝ) • (e : CliffordAlgebra Q) = 0 := by
        simpa [two_smul] using htwo
      exact (smul_eq_zero.mp hscalar).resolve_left (by norm_num)
    have hx : x = o := by
      calc
        x = (e : CliffordAlgebra Q) + o := heo.symm
        _ = o := by rw [hezero, zero_add]
    rw [hx]
    exact o.property
  · exact CliffordAlgebra.involute_eq_of_mem_odd

/-- The all-rank neutral-to-tower Clifford equivalence preserves the native
even super-grade. -/
theorem neutralCliffordEquiv_mem_even (n : ℕ)
    {x : CliffordAlgebra (InfoGeometry.Clifford.Qsplit (Vector n))}
    (hx : x ∈ CliffordAlgebra.evenOdd
      (InfoGeometry.Clifford.Qsplit (Vector n)) 0) :
    neutralCliffordEquiv n x ∈ CliffordAlgebra.evenOdd (TowerForm n) 0 := by
  apply (InfoGeometry.Canonical.SplitCliffordSuperGradeColimit.clifford_involute_eq_self_iff_mem_even
    (TowerForm n) _).mp
  rw [neutralCliffordEquiv_involute,
    CliffordAlgebra.involute_eq_of_mem_even hx]

/-- The all-rank neutral-to-tower Clifford equivalence preserves the native
odd super-grade. -/
theorem neutralCliffordEquiv_mem_odd (n : ℕ)
    {x : CliffordAlgebra (InfoGeometry.Clifford.Qsplit (Vector n))}
    (hx : x ∈ CliffordAlgebra.evenOdd
      (InfoGeometry.Clifford.Qsplit (Vector n)) 1) :
    neutralCliffordEquiv n x ∈ CliffordAlgebra.evenOdd (TowerForm n) 1 := by
  apply (involute_eq_neg_iff_mem_odd (TowerForm n) _).mp
  rw [neutralCliffordEquiv_involute,
    CliffordAlgebra.involute_eq_of_mem_odd hx, map_neg]

/-- Isotropy in the recursively presented split space, using the native
polarization of its quadratic form. -/
def TowerIsIsotropic (n : ℕ) (S : Set (TowerSpace n)) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S →
    QuadraticMap.polar (TowerForm n) x y = 0

/-- Maximality among totally isotropic subsets of the recursive split space. -/
def TowerIsMaximalIsotropic (n : ℕ) (S : Set (TowerSpace n)) : Prop :=
  TowerIsIsotropic n S ∧
    ∀ T, TowerIsIsotropic n T → S ⊆ T → T ⊆ S

/-- The all-rank neutral-to-tower isometry preserves the associated
polarization, not just the quadratic values. -/
theorem neutralToSplit_polar (n : ℕ) (x y : Neutral n) :
    QuadraticMap.polar (TowerForm n)
        (neutralToSplit n x) (neutralToSplit n y) =
      QuadraticMap.polar (InfoGeometry.Clifford.Qsplit (Vector n)) x y := by
  rw [QuadraticMap.polar, QuadraticMap.polar]
  rw [← (neutralToSplit n).map_add x y]
  rw [Qsplit_neutralToSplit_chevalley n (x + y),
    Qsplit_neutralToSplit_chevalley n x,
    Qsplit_neutralToSplit_chevalley n y]

/-- The image in the recursive `Cl(n,n)` vector space of the scalar-vacuum
annihilator is a maximal totally isotropic subspace, for every finite rank.
This is the arbitrary-rank Grassmannian point supplied by the Chevalley
pure-spinor owner; it does not assert a classification of all such points. -/
theorem neutralVacuumSheet_isMaximalIsotropic (n : ℕ) :
    TowerIsMaximalIsotropic n
      (neutralToSplit n ''
        InfoGeometry.Clifford.annihilator
          (1 : InfoGeometry.Clifford.SpinorSpace (Vector n))) := by
  have hsource :=
    InfoGeometry.Clifford.vacuum_annihilator_isMaximalIsotropic
      (L := Vector n)
  constructor
  · intro x hx y hy
    rcases hx with ⟨x₀, hx₀, rfl⟩
    rcases hy with ⟨y₀, hy₀, rfl⟩
    rw [neutralToSplit_polar]
    exact hsource.1 hx₀ hy₀
  · intro T hT hST y hy
    let U : Set (Neutral n) := {x | neutralToSplit n x ∈ T}
    have hU : InfoGeometry.Clifford.IsIsotropic U := by
      intro x hx x' hx'
      change neutralToSplit n x ∈ T at hx
      change neutralToSplit n x' ∈ T at hx'
      rw [← neutralToSplit_polar]
      exact hT hx hx'
    have hSU :
        InfoGeometry.Clifford.annihilator
          (1 : InfoGeometry.Clifford.SpinorSpace (Vector n)) ⊆ U := by
      intro x hx
      change neutralToSplit n x ∈ T
      exact hST ⟨x, hx, rfl⟩
    let x := (neutralToSplit n).symm y
    have hxU : x ∈ U := by
      change neutralToSplit n x ∈ T
      simpa [x] using hy
    have hxS := hsource.2 U hU hSU hxU
    exact ⟨x, hxS, (neutralToSplit n).apply_symm_apply y⟩

/-- The vacuum sheet as a linear subspace of the recursive split carrier,
parametrized by the covector half of the neutral phase space. -/
def neutralVacuumSheetMap (n : ℕ) :
    Module.Dual ℝ (Vector n) →ₗ[ℝ] TowerSpace n where
  toFun φ := neutralToSplit n (0, φ)
  map_add' φ ψ := by
    calc
      neutralToSplit n (0, φ + ψ) =
          neutralToSplit n ((0, φ) + (0, ψ)) := by
            congr 1
            ext <;> simp
      _ = neutralToSplit n (0, φ) + neutralToSplit n (0, ψ) :=
        (neutralToSplit n).map_add _ _
  map_smul' c φ := by
    calc
      neutralToSplit n (0, c • φ) =
          neutralToSplit n (c • (0, φ)) := by
            congr 1
            ext <;> simp
      _ = c • neutralToSplit n (0, φ) :=
        (neutralToSplit n).map_smul c _

/-- The transported `Cl(n,n)` action annihilates the scalar exterior-Fock
vacuum on the entire covector half of the maximal isotropic vacuum sheet. -/
theorem towerSpinorRep_vacuum_annihilates_sheet (n : ℕ)
    (φ : Module.Dual ℝ (Vector n)) :
    towerSpinorRep n
        (CliffordAlgebra.ι (TowerForm n) (neutralVacuumSheetMap n φ))
        (1 : InfoGeometry.Clifford.SpinorSpace (Vector n)) = 0 := by
  rw [towerSpinorRep_generator]
  change InfoGeometry.Clifford.spinorAction
      ((neutralToSplit n).symm (neutralToSplit n (0, φ)))
      (1 : InfoGeometry.Clifford.SpinorSpace (Vector n)) = 0
  rw [(neutralToSplit n).symm_apply_apply]
  rw [InfoGeometry.Clifford.spinorAction_vacuum]
  simp

/-- The kernel on the scalar Fock vacuum of the represented vector action is
exactly the maximal isotropic covector sheet. This identifies the recursive
split-space annihilator with the existing Chevalley pure-spinor annihilator. -/
theorem towerSpinorRep_vacuum_kernel_eq_sheet (n : ℕ) :
    {x : TowerSpace n |
      towerSpinorRep n (CliffordAlgebra.ι (TowerForm n) x)
        (1 : InfoGeometry.Clifford.SpinorSpace (Vector n)) = 0} =
      (LinearMap.range (neutralVacuumSheetMap n) : Set (TowerSpace n)) := by
  ext x
  constructor
  · intro hx
    change towerSpinorRep n (CliffordAlgebra.ι (TowerForm n) x)
      (1 : InfoGeometry.Clifford.SpinorSpace (Vector n)) = 0 at hx
    rw [towerSpinorRep_generator] at hx
    let y : Neutral n := (neutralToSplit n).symm x
    have hy : y ∈ InfoGeometry.Clifford.annihilator
        (1 : InfoGeometry.Clifford.SpinorSpace (Vector n)) := by
      change InfoGeometry.Clifford.spinorAction y
        (1 : InfoGeometry.Clifford.SpinorSpace (Vector n)) = 0
      simpa [y] using hx
    have hxcoord : neutralToSplit n y = x :=
      (neutralToSplit n).apply_symm_apply x
    rcases y with ⟨u, φ⟩
    have hu := (InfoGeometry.Clifford.vacuum_annihilator_iff
      (L := Vector n) u φ).mp hy
    have hyx : neutralToSplit n (u, φ) = x := by
      simpa using hxcoord
    change ∃ ψ : Module.Dual ℝ (Vector n), neutralVacuumSheetMap n ψ = x
    refine ⟨φ, ?_⟩
    calc
      neutralToSplit n (0, φ) = neutralToSplit n (u, φ) := by rw [hu]
      _ = x := hyx
  · change x ∈ LinearMap.range (neutralVacuumSheetMap n) → _
    intro hx
    change ∃ φ : Module.Dual ℝ (Vector n), neutralVacuumSheetMap n φ = x at hx
    rcases hx with ⟨φ, rfl⟩
    change towerSpinorRep n
      (CliffordAlgebra.ι (TowerForm n) (neutralVacuumSheetMap n φ))
      (1 : InfoGeometry.Clifford.SpinorSpace (Vector n)) = 0
    rw [towerSpinorRep_generator]
    rw [show neutralVacuumSheetMap n φ = neutralToSplit n (0, φ) by rfl]
    rw [(neutralToSplit n).symm_apply_apply]
    change InfoGeometry.Clifford.spinorAction (0, φ)
      (1 : InfoGeometry.Clifford.SpinorSpace (Vector n)) = 0
    rw [InfoGeometry.Clifford.spinorAction_vacuum]
    simp

/-- The covector parametrization of the vacuum sheet is injective. -/
theorem neutralVacuumSheetMap_injective (n : ℕ) :
    Function.Injective (neutralVacuumSheetMap n) := by
  intro φ ψ h
  have hp := congrArg Prod.snd ((neutralToSplit n).injective h)
  exact hp

/-- The range of the rank-`n` sheet map is exactly the image of the
Chevalley scalar-vacuum annihilator in recursive split coordinates. -/
theorem neutralVacuumSheet_range_eq_annihilator_image (n : ℕ) :
    (LinearMap.range (neutralVacuumSheetMap n) : Set (TowerSpace n)) =
      neutralToSplit n ''
        InfoGeometry.Clifford.annihilator
          (1 : InfoGeometry.Clifford.SpinorSpace (Vector n)) := by
  ext z
  constructor
  · rintro ⟨φ, hφ⟩
    change neutralToSplit n (0, φ) = z at hφ
    refine ⟨(0, φ), ?_, hφ⟩
    exact (InfoGeometry.Clifford.vacuum_annihilator_iff (L := Vector n)
      0 φ).2 rfl
  · rintro ⟨x, hx, hzx⟩
    rcases x with ⟨u, φ⟩
    have hu := (InfoGeometry.Clifford.vacuum_annihilator_iff
      (L := Vector n) u φ).mp hx
    subst u
    refine ⟨φ, ?_⟩
    change neutralToSplit n (0, φ) = z
    exact hzx

/-- Hence the rank-`n` covector image is a maximal totally isotropic
subspace in the recursive symmetric split quadratic space. -/
theorem neutralVacuumSheet_range_isMaximalIsotropic (n : ℕ) :
    TowerIsMaximalIsotropic n
      (LinearMap.range (neutralVacuumSheetMap n) : Set (TowerSpace n)) := by
  rw [neutralVacuumSheet_range_eq_annihilator_image]
  exact neutralVacuumSheet_isMaximalIsotropic n

/-- The vacuum sheet has dimension `n`, the maximal isotropic rank in
`Cl(n,n)`. -/
theorem neutralVacuumSheet_finrank (n : ℕ) :
    Module.finrank ℝ (LinearMap.range (neutralVacuumSheetMap n)) = n := by
  rw [LinearMap.finrank_range_of_inj (neutralVacuumSheetMap_injective n),
    (dualCoordinates n).finrank_eq, Module.finrank_pi]
  simp

/-- The coordinate tail map from the `(n+1)`-dimensional vector stage to
the recursive `n`-dimensional tail. -/
def vectorTail (n : ℕ) : Vector (n + 1) →ₗ[ℝ] Vector n where
  toFun z i := z i.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extend a covector on the old stage to the new stage by making it vanish
on the newly added head coordinate. -/
def dualTailMap (n : ℕ) :
    Module.Dual ℝ (Vector n) →ₗ[ℝ] Module.Dual ℝ (Vector (n + 1)) where
  toFun φ := φ.comp (vectorTail n)
  map_add' _ _ := by
    ext z
    simp
  map_smul' _ _ := by
    ext z
    simp

@[simp] theorem dualTailMap_coordinate_zero (n : ℕ)
    (φ : Module.Dual ℝ (Vector n)) :
    dualCoordinates (n + 1) (dualTailMap n φ) 0 = 0 := by
  rw [dualCoordinates_apply]
  change φ (fun _ => 0) = 0
  exact map_zero φ

@[simp] theorem dualTailMap_coordinate_succ (n : ℕ)
    (φ : Module.Dual ℝ (Vector n)) (i : Fin n) :
    dualCoordinates (n + 1) (dualTailMap n φ) i.succ =
      dualCoordinates n φ i := by
  rw [dualCoordinates_apply, dualCoordinates_apply]
  change φ (vectorTail n (Pi.single i.succ 1)) = φ (Pi.single i 1)
  congr 1
  funext j
  simp [vectorTail, Pi.single_apply, Fin.succ_inj]

/-- Insert a zero in the newly added head coordinate of a finite vector. -/
def vectorHeadZero (n : ℕ) : Vector n →ₗ[ℝ] Vector (n + 1) where
  toFun u := Fin.cases 0 u
  map_add' u v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rfl
  map_smul' c u := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rfl

@[simp] theorem vectorHeadZero_coordinate_zero (n : ℕ) (u : Vector n) :
    vectorHeadZero n u 0 = 0 := by
  simp [vectorHeadZero]

@[simp] theorem vectorHeadZero_coordinate_succ (n : ℕ) (u : Vector n)
    (i : Fin n) :
    vectorHeadZero n u i.succ = u i := by
  simp [vectorHeadZero]

/-- Forgetting the new head coordinate after its zero insertion recovers the
original finite vector. -/
@[simp] theorem vectorTail_vectorHeadZero (n : ℕ) (u : Vector n) :
    vectorTail n (vectorHeadZero n u) = u := by
  ext i
  rfl

/-- The zero-quadratic Chevalley Fock spaces inherit the same finite-stage
inclusion by Mathlib's native Clifford algebra map. -/
def fockTailIsometry (n : ℕ) :
    (0 : QuadraticForm ℝ (Vector n)) →qᵢ
      (0 : QuadraticForm ℝ (Vector (n + 1))) where
  __ := vectorHeadZero n
  map_app' _ := rfl

noncomputable def fockTailMap (n : ℕ) :
    InfoGeometry.Clifford.SpinorSpace (Vector n) →ₐ[ℝ]
      InfoGeometry.Clifford.SpinorSpace (Vector (n + 1)) :=
  CliffordAlgebra.map (fockTailIsometry n)

@[simp] theorem fockTailMap_generator (n : ℕ) (u : Vector n) :
    fockTailMap n (CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector n)) u) =
      CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector (n + 1)))
        (vectorHeadZero n u) := by
  exact CliffordAlgebra.map_apply_ι _ _

/-- Mathlib's left contraction is natural for the paired vector/covector
tail maps on the zero-quadratic exterior-Fock carriers. The proof follows the
native Clifford left-induction recursion and checks the dual pairing on each
generator. -/
theorem fockTailMap_contractLeft (n : ℕ)
    (φ : Module.Dual ℝ (Vector n))
    (x : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    fockTailMap n
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Vector n))) φ x) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Vector (n + 1))))
        (dualTailMap n φ) (fockTailMap n x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [fockTailMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul v x hx =>
      rw [CliffordAlgebra.contractLeft_ι_mul]
      rw [map_sub, map_smul, map_mul, fockTailMap_generator, hx]
      have hprod : fockTailMap n
          (CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector n)) x * v) =
          CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector (n + 1)))
            (vectorHeadZero n x) * fockTailMap n v := by
        rw [map_mul, fockTailMap_generator]
      rw [hprod, CliffordAlgebra.contractLeft_ι_mul]
      have hpair : dualTailMap n φ (vectorHeadZero n x) = φ x := by
        change φ (vectorTail n (vectorHeadZero n x)) = φ x
        rw [vectorTail_vectorHeadZero]
      rw [hpair]

/-- The neutral phase-space inclusion corresponding to the recursive
split-space tail inclusion: both the vector and covector vanish on the new
head coordinate. -/
def neutralTailMap (n : ℕ) : Neutral n →ₗ[ℝ] Neutral (n + 1) where
  toFun X := (vectorHeadZero n X.1, dualTailMap n X.2)
  map_add' X Y := by
    apply Prod.ext
    · change vectorHeadZero n (X.1 + Y.1) =
        vectorHeadZero n X.1 + vectorHeadZero n Y.1
      exact (vectorHeadZero n).map_add X.1 Y.1
    · ext z
      simp [dualTailMap]
  map_smul' c X := by
    apply Prod.ext
    · change vectorHeadZero n (c • X.1) =
        c • vectorHeadZero n X.1
      exact (vectorHeadZero n).map_smul c X.1
    · ext z
      simp [dualTailMap]

/-- The Chevalley spinor action is natural for the zero-head inclusion of
neutral phase space. Creation is transported by the exterior-algebra map and
contraction by `fockTailMap_contractLeft`. -/
theorem fockTailMap_spinorAction (n : ℕ) (X : Neutral n)
    (ψ : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    fockTailMap n (InfoGeometry.Clifford.spinorAction X ψ) =
      InfoGeometry.Clifford.spinorAction (neutralTailMap n X)
        (fockTailMap n ψ) := by
  rcases X with ⟨u, φ⟩
  change fockTailMap n
      (CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector n)) u * ψ +
        CliffordAlgebra.contractLeft φ ψ) =
    CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector (n + 1)))
        (vectorHeadZero n u) * fockTailMap n ψ +
      CliffordAlgebra.contractLeft (dualTailMap n φ) (fockTailMap n ψ)
  rw [map_add, map_mul, fockTailMap_generator, fockTailMap_contractLeft]

/-- The all-rank neutral-to-split isometry commutes with the finite-stage
inclusion. This is the coordinate-level compatibility needed to induce the
corresponding Clifford algebra map. -/
theorem neutralToSplit_tail (n : ℕ) (X : Neutral n) :
    neutralToSplit (n + 1) (neutralTailMap n X) =
      InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageVectorInclude n
        (neutralToSplit n X) := by
  rcases X with ⟨u, φ⟩
  change
    (neutralToWittCoordinates (n + 1) (vectorHeadZero n u, dualTailMap n φ) 0,
      packSplitCoordinates n (fun i =>
        neutralToWittCoordinates (n + 1)
          (vectorHeadZero n u, dualTailMap n φ) i.succ)) =
      (0, neutralToSplit n (u, φ))
  apply Prod.ext
  · change
      ((vectorHeadZero n u 0 +
          dualCoordinates (n + 1) (dualTailMap n φ) 0) / 2,
        (vectorHeadZero n u 0 -
          dualCoordinates (n + 1) (dualTailMap n φ) 0) / 2) = (0, 0)
    rw [vectorHeadZero_coordinate_zero, dualTailMap_coordinate_zero]
    simp
  · change packSplitCoordinates n (fun i =>
        ((vectorHeadZero n u i.succ +
            dualCoordinates (n + 1) (dualTailMap n φ) i.succ) / 2,
          (vectorHeadZero n u i.succ -
            dualCoordinates (n + 1) (dualTailMap n φ) i.succ) / 2)) =
      packSplitCoordinates n (fun i =>
        ((u i + dualCoordinates n φ i) / 2,
          (u i - dualCoordinates n φ i) / 2))
    congr 1
    funext i
    rw [vectorHeadZero_coordinate_succ, dualTailMap_coordinate_succ]

/-- Every neutral vector's exterior generator is natural for the native
super-Grassmannian exterior-stage map. -/
@[simp] theorem neutralToSplit_exterior_tail (n : ℕ) (X : Neutral n) :
    InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageExteriorMap n
        (ExteriorAlgebra.ι ℝ (neutralToSplit n X)) =
      ExteriorAlgebra.ι ℝ
        (neutralToSplit (n + 1) (neutralTailMap n X)) := by
  rw [InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageExteriorMap_generator,
    neutralToSplit_tail]

/-- Isometric zero-head inclusion on the neutral Chevalley carriers. -/
def neutralTailIsometry (n : ℕ) :
    InfoGeometry.Clifford.Qsplit (Vector n) →qᵢ
      InfoGeometry.Clifford.Qsplit (Vector (n + 1)) where
  __ := neutralTailMap n
  map_app' X := by
    calc
      InfoGeometry.Clifford.Qsplit (Vector (n + 1)) (neutralTailMap n X) =
          TowerForm (n + 1) (neutralToSplit (n + 1) (neutralTailMap n X)) :=
        (Qsplit_neutralToSplit_chevalley (n + 1) (neutralTailMap n X)).symm
      _ = TowerForm (n + 1)
          (InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageVectorInclude n
            (neutralToSplit n X)) := by rw [neutralToSplit_tail]
      _ = TowerForm n (neutralToSplit n X) := by
        change TowerForm (n + 1) (0, neutralToSplit n X) = _
        rw [InfoGeometry.CliffordTower.Qsplit_succ_apply]
        simp
      _ = InfoGeometry.Clifford.Qsplit (Vector n) X :=
        Qsplit_neutralToSplit_chevalley n X

/-- The full neutral Clifford action, not only its vector generators,
intertwines with the Fock tail inclusion. The proof extends generator
naturality by Mathlib's native Clifford left-induction principle. -/
theorem abstractSpinorRep_tail (n : ℕ)
    (a : CliffordAlgebra (InfoGeometry.Clifford.Qsplit (Vector n)))
    (ψ : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    fockTailMap n
        (InfoGeometry.Clifford.abstractSpinorRep (Vector n) a ψ) =
      InfoGeometry.Clifford.abstractSpinorRep (Vector (n + 1))
        (CliffordAlgebra.map (neutralTailIsometry n) a)
        (fockTailMap n ψ) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => simp [fockTailMap]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | ι_mul a X ha =>
      have hsource :
          InfoGeometry.Clifford.abstractSpinorRep (Vector n)
              (CliffordAlgebra.ι (InfoGeometry.Clifford.Qsplit (Vector n)) X * a) =
            InfoGeometry.Clifford.abstractSpinorRep (Vector n)
                (CliffordAlgebra.ι (InfoGeometry.Clifford.Qsplit (Vector n)) X) *
              InfoGeometry.Clifford.abstractSpinorRep (Vector n) a := map_mul _ _ _
      have hmap :
          CliffordAlgebra.map (neutralTailIsometry n)
              (CliffordAlgebra.ι (InfoGeometry.Clifford.Qsplit (Vector n)) X * a) =
            CliffordAlgebra.ι (InfoGeometry.Clifford.Qsplit (Vector (n + 1)))
                (neutralTailMap n X) * CliffordAlgebra.map (neutralTailIsometry n) a := by
        rw [map_mul, CliffordAlgebra.map_apply_ι]
        congr 1
      have htarget :
          InfoGeometry.Clifford.abstractSpinorRep (Vector (n + 1))
              (CliffordAlgebra.map (neutralTailIsometry n)
                (CliffordAlgebra.ι (InfoGeometry.Clifford.Qsplit (Vector n)) X * a)) =
            InfoGeometry.Clifford.abstractSpinorRep (Vector (n + 1))
                (CliffordAlgebra.ι (InfoGeometry.Clifford.Qsplit (Vector (n + 1)))
                  (neutralTailMap n X)) *
              InfoGeometry.Clifford.abstractSpinorRep (Vector (n + 1))
                (CliffordAlgebra.map (neutralTailIsometry n) a) := by
        rw [hmap, map_mul]
      rw [hsource, htarget, Module.End.mul_apply, Module.End.mul_apply]
      simp only [InfoGeometry.Clifford.abstractSpinorRep,
        CliffordAlgebra.lift_ι_apply]
      change fockTailMap n
          (InfoGeometry.Clifford.spinorAction X
            (InfoGeometry.Clifford.abstractSpinorRep (Vector n) a ψ)) =
        InfoGeometry.Clifford.spinorAction (neutralTailMap n X)
          (InfoGeometry.Clifford.abstractSpinorRep (Vector (n + 1))
            (CliffordAlgebra.map (neutralTailIsometry n) a)
            (fockTailMap n ψ))
      rw [fockTailMap_spinorAction, ha]

/-- The neutral Chevalley Clifford map and the canonical recursive
`Cl(n,n)` stage map commute exactly. Thus the all-rank neutral presentation
is a morphism of the repository's finite-stage Clifford systems. -/
theorem neutralCliffordEquiv_map_tail (n : ℕ)
    (x : CliffordAlgebra (InfoGeometry.Clifford.Qsplit (Vector n))) :
    neutralCliffordEquiv (n + 1)
        (CliffordAlgebra.map (neutralTailIsometry n) x) =
      InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageCliffordMap n
        (neutralCliffordEquiv n x) := by
  let f : CliffordAlgebra (InfoGeometry.Clifford.Qsplit (Vector n)) →ₐ[ℝ]
      CliffordAlgebra (TowerForm (n + 1)) :=
    (neutralCliffordEquiv (n + 1)).toAlgHom.comp
      (CliffordAlgebra.map (neutralTailIsometry n))
  let g : CliffordAlgebra (InfoGeometry.Clifford.Qsplit (Vector n)) →ₐ[ℝ]
      CliffordAlgebra (TowerForm (n + 1)) :=
    (InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageCliffordMap n).comp
      (neutralCliffordEquiv n).toAlgHom
  have hfg : f = g := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro X
    change neutralCliffordEquiv (n + 1)
        (CliffordAlgebra.map (neutralTailIsometry n)
          (CliffordAlgebra.ι (InfoGeometry.Clifford.Qsplit (Vector n)) X)) =
      InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageCliffordMap n
        (neutralCliffordEquiv n
          (CliffordAlgebra.ι (InfoGeometry.Clifford.Qsplit (Vector n)) X))
    rw [CliffordAlgebra.map_apply_ι, neutralCliffordEquiv_ι]
    rw [neutralCliffordEquiv_ι]
    rw [InfoGeometry.Clifford.ClNNSuperGrassmannianBridge.splitStageCliffordMap_generator_eq_gammaTail]
    exact congrArg (CliffordAlgebra.ι (TowerForm (n + 1)))
      (neutralToSplit_tail n X)
  change f x = g x
  exact congrArg (fun h : CliffordAlgebra (InfoGeometry.Clifford.Qsplit (Vector n)) →ₐ[ℝ]
      CliffordAlgebra (TowerForm (n + 1)) => h x) hfg

/-- The complete recursive symmetric split Clifford representation on the
Chevalley Fock spaces intertwines with both native stage inclusions: the
Clifford input uses the super-Grassmannian `Cl(n,n)` map and the spinor input
uses the zero-head Fock map. -/
theorem towerSpinorRep_tail (n : ℕ)
    (a : CliffordAlgebra (TowerForm n))
    (ψ : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    fockTailMap n (towerSpinorRep n a ψ) =
      towerSpinorRep (n + 1)
        (InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageCliffordMap n a)
        (fockTailMap n ψ) := by
  let a₀ := (neutralCliffordEquiv n).symm a
  have hneutral := neutralCliffordEquiv_map_tail n a₀
  have hsource : neutralCliffordEquiv n a₀ = a := by
    simp [a₀]
  have hmap :
      CliffordAlgebra.map (neutralTailIsometry n) a₀ =
        (neutralCliffordEquiv (n + 1)).symm
          (InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageCliffordMap n a) := by
    apply (neutralCliffordEquiv (n + 1)).injective
    rw [hneutral, hsource]
    exact ((neutralCliffordEquiv (n + 1)).apply_symm_apply _).symm
  change fockTailMap n
      (InfoGeometry.Clifford.abstractSpinorRep (Vector n) a₀ ψ) =
    InfoGeometry.Clifford.abstractSpinorRep (Vector (n + 1))
      ((neutralCliffordEquiv (n + 1)).symm
        (InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageCliffordMap n a))
      (fockTailMap n ψ)
  rw [abstractSpinorRep_tail, hmap]

/-- The neutral Chevalley algebra at each finite rank maps into the
repository's canonical direct limit of symmetric split Clifford algebras. -/
noncomputable def neutralCliffordToInfinity (n : ℕ) :
    CliffordAlgebra (InfoGeometry.Clifford.Qsplit (Vector n)) →ₐ[ℝ]
      InfoGeometry.Canonical.SplitCliffordDirectLimit.SplitCliffordInfinity :=
  (DirectLimit.Algebra.of
      InfoGeometry.Canonical.SplitCliffordTensorBridge.SplitClNNAlg
      (fun i j hij =>
        InfoGeometry.Canonical.SplitCliffordDirectLimit.splitCliffordMap i j hij) n).comp
    (neutralCliffordEquiv n).toAlgHom

/-- The maps from neutral finite stages to the canonical `Cl(N,N)` colimit
form a compatible cocone. This is the colimit-level consequence of the
finite-stage Clifford intertwining theorem above. -/
theorem neutralCliffordToInfinity_map_tail (n : ℕ)
    (x : CliffordAlgebra (InfoGeometry.Clifford.Qsplit (Vector n))) :
    neutralCliffordToInfinity (n + 1)
        (CliffordAlgebra.map (neutralTailIsometry n) x) =
      neutralCliffordToInfinity n x := by
  change DirectLimit.Algebra.of
      InfoGeometry.Canonical.SplitCliffordTensorBridge.SplitClNNAlg
      (fun i j hij =>
        InfoGeometry.Canonical.SplitCliffordDirectLimit.splitCliffordMap i j hij)
      (n + 1)
      (neutralCliffordEquiv (n + 1)
        (CliffordAlgebra.map (neutralTailIsometry n) x)) =
    DirectLimit.Algebra.of
      InfoGeometry.Canonical.SplitCliffordTensorBridge.SplitClNNAlg
      (fun i j hij =>
        InfoGeometry.Canonical.SplitCliffordDirectLimit.splitCliffordMap i j hij)
      n (neutralCliffordEquiv n x)
  rw [neutralCliffordEquiv_map_tail,
    InfoGeometry.Canonical.SplitCliffordExteriorTowerBridge.stageCliffordMap_eq_canonicalStep]
  have hstep :
      InfoGeometry.Canonical.SplitCliffordDirectLimit.splitCliffordMap n (n + 1)
          (Nat.le_trans (Nat.le_refl n) (Nat.le_succ n)) =
        InfoGeometry.Canonical.SplitCliffordDirectLimit.splitCliffordStep n := by
    rw [InfoGeometry.Canonical.SplitCliffordDirectLimit.splitCliffordMap_succ
      n n (Nat.le_refl n),
      InfoGeometry.Canonical.SplitCliffordDirectLimit.splitCliffordMap_refl]
    simp
  rw [← hstep]
  exact DirectLimit.Algebra.of_f
    (f := fun i j hij =>
      InfoGeometry.Canonical.SplitCliffordDirectLimit.splitCliffordMap i j hij)
    (Nat.le_trans (Nat.le_refl n) (Nat.le_succ n))
    (neutralCliffordEquiv n x)

/-- The finite-stage inclusion preserves the vacuum sheet: its extension on
`E*` is the tail-covector map, and the resulting square commutes exactly. -/
theorem neutralVacuumSheetMap_tail (n : ℕ)
    (φ : Module.Dual ℝ (Vector n)) :
    neutralVacuumSheetMap (n + 1) (dualTailMap n φ) =
      InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageVectorInclude n
        (neutralVacuumSheetMap n φ) := by
  change
    (neutralToWittCoordinates (n + 1) (0, dualTailMap n φ) 0,
      packSplitCoordinates n (fun i =>
        neutralToWittCoordinates (n + 1) (0, dualTailMap n φ) i.succ)) =
      (0, neutralToSplit n (0, φ))
  apply Prod.ext
  · change ((0 + dualCoordinates (n + 1) (dualTailMap n φ) 0) / 2,
      (0 - dualCoordinates (n + 1) (dualTailMap n φ) 0) / 2) = (0, 0)
    rw [dualTailMap_coordinate_zero]
    simp
  · change packSplitCoordinates n (fun i =>
        ((0 + dualCoordinates (n + 1) (dualTailMap n φ) i.succ) / 2,
          (0 - dualCoordinates (n + 1) (dualTailMap n φ) i.succ) / 2)) =
      packSplitCoordinates n (fun i =>
        ((0 + dualCoordinates n φ i) / 2,
          (0 - dualCoordinates n φ i) / 2))
    congr 1
    funext i
    rw [dualTailMap_coordinate_succ]

/-- The rank-generic vacuum-sheet generator is natural for the native
super-Grassmannian exterior-stage map. This identifies the covector extension
with zero on the new head and the repository's exterior-algebra inclusion. -/
@[simp] theorem neutralVacuumSheet_exterior_tail (n : ℕ)
    (φ : Module.Dual ℝ (Vector n)) :
    InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageExteriorMap n
        (ExteriorAlgebra.ι ℝ (neutralVacuumSheetMap n φ)) =
      ExteriorAlgebra.ι ℝ
        (neutralVacuumSheetMap (n + 1) (dualTailMap n φ)) := by
  rw [InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageExteriorMap_generator,
    neutralVacuumSheetMap_tail]

local instance splitTwoInvertible : Invertible (2 : ℝ) :=
  invertibleOfNonzero (by norm_num)

/-- Every vector in the arbitrary-rank Chevalley vacuum sheet is null for
the recursive symmetric split form. -/
@[simp] theorem neutralVacuumSheetMap_isotropic (n : ℕ)
    (φ : Module.Dual ℝ (Vector n)) :
    TowerForm n (neutralVacuumSheetMap n φ) = 0 := by
  change TowerForm n (neutralToSplit n (0, φ)) = 0
  rw [Qsplit_neutralToSplit]
  simp [canonicalNeutralFormUnscaled_apply]

/-! The neutral para-complex structure splits the phase space into the
primal and covector sheets. The Chevalley vacuum sheet is the negative
eigensheet, linking the split-Clifford pure-spinor geometry to the native
SuperGrassmannian para-Kähler API. -/

/-- The normalized neutral metric has the same diagonal as the unscaled
quadratic form defining the symmetric `Cl(n,n)` carrier. -/
noncomputable def neutralPhaseMetric (n : ℕ) :
    Neutral n →ₗ[ℝ] Neutral n →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) • canonicalNeutralBilin (E := Vector n)

/-- The compatible skew form; this sign makes the metric equal to
`ω(X, K Y)` for the primal-fixed neutral para-involution. -/
noncomputable def neutralPhaseTwoForm (n : ℕ) :
    Neutral n →ₗ[ℝ] Neutral n →ₗ[ℝ] ℝ :=
  -(1 / 2 : ℝ) • neutralOmega (E := Vector n)

/-- The evaluation-paired neutral phase space carries its canonical
para-Kähler structure, with metric diagonal equal to the `Cl(n,n)` form. -/
theorem neutralPhaseParaKahlerStructure (n : ℕ) :
    InfoGeometry.Canonical.SuperGrassmannianManifold.ParaKahlerStructure
      (neutralPhaseMetric n) (neutralPhaseTwoForm n)
      (neutralParaInvolution (E := Vector n)) := by
  constructor
  · intro X Y
    rcases X with ⟨x, ξ⟩
    rcases Y with ⟨y, η⟩
    simp [neutralPhaseMetric, canonicalNeutralBilin_apply]
    ring
  · intro X Y
    rcases X with ⟨x, ξ⟩
    rcases Y with ⟨y, η⟩
    simp [neutralPhaseTwoForm, neutralOmega_apply]
    ring
  · intro X Y
    rcases X with ⟨x, ξ⟩
    rcases Y with ⟨y, η⟩
    simp [neutralPhaseMetric, neutralPhaseTwoForm,
      canonicalNeutralBilin_apply, neutralOmega_apply,
      neutralParaInvolution]
    ring
  · intro X Y
    rcases X with ⟨x, ξ⟩
    rcases Y with ⟨y, η⟩
    simp [neutralPhaseTwoForm, neutralOmega_apply,
      neutralParaInvolution]
    ring

/-- Every covector in the Chevalley vacuum sheet belongs to the negative
eigensheet of the canonical neutral para-complex involution. -/
theorem neutralVacuumSheet_in_paraMinus (n : ℕ)
    (φ : Module.Dual ℝ (Vector n)) :
    InfoGeometry.Canonical.SuperGrassmannianManifold.InTMinus
      (neutralParaInvolution (E := Vector n)) (0, φ) := by
  change neutralParaInvolution (0, φ) = -(0, φ)
  simp [neutralParaInvolution]

/-- The neutral metric diagonal is the recursively split quadratic form. -/
theorem neutralPhaseMetric_self_eq_splitForm (n : ℕ) (X : Neutral n) :
    neutralPhaseMetric n X X =
      canonicalNeutralFormUnscaled (E := Vector n) X := by
  rcases X with ⟨x, ξ⟩
  simp [neutralPhaseMetric, canonicalNeutralBilin_apply,
    canonicalNeutralFormUnscaled_apply]
  ring

/-- The `Cl(n,n)` vacuum-sheet vector is isotropic by the native
SuperGrassmannian theorem for the negative para-complex sheet. -/
theorem neutralVacuumSheet_isotropic_of_paraKahler (n : ℕ)
    (φ : Module.Dual ℝ (Vector n)) :
    TowerForm n (neutralVacuumSheetMap n φ) = 0 := by
  let X : Neutral n := (0, φ)
  have hsheet :=
    InfoGeometry.Canonical.SuperGrassmannianManifold.tminus_isotropic_two_mul
      (neutralPhaseMetric n) (neutralPhaseTwoForm n)
      (neutralParaInvolution (E := Vector n))
      ⟨by
        intro Y
        rcases Y with ⟨y, η⟩
        simp [neutralParaInvolution]⟩
      (neutralPhaseParaKahlerStructure n) X
      (neutralVacuumSheet_in_paraMinus n φ)
  have hq : canonicalNeutralFormUnscaled (E := Vector n) X = 0 := by
    rw [neutralPhaseMetric_self_eq_splitForm n X] at hsheet
    nlinarith
  change TowerForm n (neutralToSplit n X) = 0
  rw [Qsplit_neutralToSplit]
  exact hq

/-- The projection onto the covector factor of the neutral phase space. -/
def neutralCovectorSheetProjector (n : ℕ) : Module.End ℝ (Neutral n) where
  toFun X := (0, X.2)
  map_add' X Y := by
    rcases X with ⟨x, ξ⟩
    rcases Y with ⟨y, η⟩
    simp
  map_smul' r X := by
    rcases X with ⟨x, ξ⟩
    simp

/-- The complementary projection onto the primal factor of the neutral phase
space. -/
def neutralPrimalSheetProjector (n : ℕ) : Module.End ℝ (Neutral n) where
  toFun X := (X.1, 0)
  map_add' X Y := by
    rcases X with ⟨x, ξ⟩
    rcases Y with ⟨y, η⟩
    simp
  map_smul' r X := by
    rcases X with ⟨x, ξ⟩
    simp

@[simp] theorem neutralPrimalSheetProjector_apply (n : ℕ)
    (X : Neutral n) :
    neutralPrimalSheetProjector n X = (X.1, 0) := rfl

/-- The two neutral sheet projections recover the full phase-space vector. -/
theorem neutralSheetProjectors_sum (n : ℕ) (X : Neutral n) :
    neutralPrimalSheetProjector n X + neutralCovectorSheetProjector n X = X := by
  rcases X with ⟨x, φ⟩
  apply Prod.ext
  · simp [neutralPrimalSheetProjector, neutralCovectorSheetProjector]
  · simp [neutralPrimalSheetProjector, neutralCovectorSheetProjector]

/-- The primal sheet of the recursive symmetric split carrier, parametrized
by the vector half of the neutral phase space. -/
def neutralPrimalSheetMap (n : ℕ) : Vector n →ₗ[ℝ] TowerSpace n where
  toFun u := neutralToSplit n (u, 0)
  map_add' u v := by
    rw [← (neutralToSplit n).map_add]
    congr 1
    ext <;> simp
  map_smul' c u := by
    rw [← (neutralToSplit n).map_smul]
    congr 1
    ext <;> simp

/-- The primal sheet parametrization is injective. -/
theorem neutralPrimalSheetMap_injective (n : ℕ) :
    Function.Injective (neutralPrimalSheetMap n) := by
  intro u v h
  have h' := congrArg Prod.fst ((neutralToSplit n).injective h)
  exact h'

/-- Parametrization of the primal sheet as a subspace of `Cl(n,n)`. -/
noncomputable def neutralPrimalSheetParametrization (n : ℕ) :
    Vector n ≃ₗ[ℝ] LinearMap.range (neutralPrimalSheetMap n) :=
  LinearEquiv.ofBijective (neutralPrimalSheetMap n).rangeRestrict
    ⟨by
      intro u v h
      apply neutralPrimalSheetMap_injective n
      exact congrArg Subtype.val h,
      LinearMap.surjective_rangeRestrict _⟩

/-- Parametrization of the covector vacuum sheet as a subspace of `Cl(n,n)`. -/
noncomputable def neutralVacuumSheetParametrization (n : ℕ) :
    Module.Dual ℝ (Vector n) ≃ₗ[ℝ]
      LinearMap.range (neutralVacuumSheetMap n) :=
  LinearEquiv.ofBijective (neutralVacuumSheetMap n).rangeRestrict
    ⟨by
      intro φ ψ h
      apply neutralVacuumSheetMap_injective n
      exact congrArg Subtype.val h,
      LinearMap.surjective_rangeRestrict _⟩

/-- The covector vacuum sheet is canonically the algebraic dual of the primal
sheet. The equivalence is induced by the nondegenerate cross-pairing of the
two maximal isotropic sheets. -/
noncomputable def neutralVacuumSheetDualEquiv (n : ℕ) :
    LinearMap.range (neutralVacuumSheetMap n) ≃ₗ[ℝ]
      Module.Dual ℝ (LinearMap.range (neutralPrimalSheetMap n)) :=
  (neutralVacuumSheetParametrization n).symm.trans
    ((neutralPrimalSheetParametrization n).dualMap).symm

/-- Evaluation under the sheet duality equivalence is exactly the recursive
split Clifford polarization between the primal and covector sheets. -/
theorem neutralVacuumSheetDualEquiv_apply (n : ℕ)
    (u : Vector n) (φ : Module.Dual ℝ (Vector n)) :
    neutralVacuumSheetDualEquiv n
        (neutralVacuumSheetParametrization n φ)
        (neutralPrimalSheetParametrization n u) = φ u := by
  change ((neutralPrimalSheetParametrization n).dualMap).symm
      ((neutralVacuumSheetParametrization n).symm
        (neutralVacuumSheetParametrization n φ))
      (neutralPrimalSheetParametrization n u) = φ u
  rw [(neutralVacuumSheetParametrization n).symm_apply_apply]
  have h := congrArg (fun f : Module.Dual ℝ (Vector n) => f u)
    ((neutralPrimalSheetParametrization n).dualMap.apply_symm_apply φ)
  simpa only [LinearEquiv.dualMap_apply] using h

/-- The cross-pairing of the two recursive split sheets is the original
evaluation pairing between vectors and algebraic covectors. -/
theorem neutralToSplit_polar_primal_covector (n : ℕ)
    (u : Vector n) (φ : Module.Dual ℝ (Vector n)) :
    QuadraticMap.polar (TowerForm n)
        (neutralPrimalSheetMap n u) (neutralVacuumSheetMap n φ) = φ u := by
  change QuadraticMap.polar (TowerForm n)
    (neutralToSplit n (u, 0)) (neutralToSplit n (0, φ)) = φ u
  rw [neutralToSplit_polar]
  rw [chevelleyQsplit_eq_neutralForm,
    canonicalNeutralFormUnscaled_polar]
  simp [canonicalNeutralBilin_apply]

/-- The recursive `Cl(n,n)` quadratic form is the cross-pairing of its
primal and covector projections, with the normalization fixed by the
repository's half-scaled para-Kähler metric. -/
theorem Qsplit_eq_two_neutralPhaseMetric_cross (n : ℕ)
    (X : Neutral n) :
    TowerForm n (neutralToSplit n X) =
      2 * neutralPhaseMetric n (neutralPrimalSheetProjector n X)
        (neutralCovectorSheetProjector n X) := by
  rcases X with ⟨u, φ⟩
  rw [Qsplit_neutralToSplit]
  simp [neutralPhaseMetric, canonicalNeutralFormUnscaled_apply,
    neutralPrimalSheetProjector, neutralCovectorSheetProjector,
    canonicalNeutralBilin_apply]

@[simp] theorem neutralCovectorSheetProjector_apply (n : ℕ)
    (X : Neutral n) :
    neutralCovectorSheetProjector n X = (0, X.2) := rfl

/-- The covector-sheet projector is the negative Peirce projector of the
neutral para-involution. -/
theorem neutralCovectorSheetProjector_eq_half_one_sub_para (n : ℕ) :
    neutralCovectorSheetProjector n =
      (1 / 2 : ℝ) •
        (1 - neutralParaInvolution (E := Vector n)) := by
  apply LinearMap.ext
  intro X
  rcases X with ⟨x, ξ⟩
  simp [neutralCovectorSheetProjector, neutralParaInvolution]
  rw [← add_smul]
  norm_num

/-- The covector-sheet projection is idempotent, so it is a native
SuperGrassmannian projector on the neutral carrier. -/
theorem neutralCovectorSheetProjector_isGrassmannianProjector (n : ℕ) :
    InfoGeometry.Canonical.SuperGrassmannianManifold.GrassmannianProjector
      (neutralCovectorSheetProjector n) := by
  constructor
  intro X
  rcases X with ⟨x, ξ⟩
  rfl

/-- Transport the neutral covector-sheet projector to the recursive
symmetric split carrier by conjugation with the established linear
equivalence. -/
def splitVacuumSheetProjector (n : ℕ) : Module.End ℝ (TowerSpace n) :=
  (neutralToSplit n).toLinearMap.comp
    ((neutralCovectorSheetProjector n).comp
      (neutralToSplit n).symm.toLinearMap)

@[simp] theorem splitVacuumSheetProjector_apply (n : ℕ)
    (x : TowerSpace n) :
    splitVacuumSheetProjector n x =
      neutralVacuumSheetMap n ((neutralToSplit n).symm x).2 := by
  simp [splitVacuumSheetProjector, neutralVacuumSheetMap,
    neutralCovectorSheetProjector, LinearMap.comp_apply]

/-- The transported vacuum-sheet projection remains idempotent on the
recursive split carrier. -/
theorem splitVacuumSheetProjector_isGrassmannianProjector (n : ℕ) :
    InfoGeometry.Canonical.SuperGrassmannianManifold.GrassmannianProjector
      (splitVacuumSheetProjector n) := by
  constructor
  intro x
  simp [splitVacuumSheetProjector, neutralCovectorSheetProjector,
    LinearMap.comp_apply]

/-- The range of the transported SuperGrassmannian projector is exactly the
`Cl(n,n)` Chevalley vacuum sheet. -/
theorem splitVacuumSheetProjector_range_eq_vacuumSheet (n : ℕ) :
    (LinearMap.range (splitVacuumSheetProjector n) : Set (TowerSpace n)) =
      (LinearMap.range (neutralVacuumSheetMap n) : Set (TowerSpace n)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [splitVacuumSheetProjector_apply]
    exact ⟨((neutralToSplit n).symm y).2, rfl⟩
  · rintro ⟨φ, hφ⟩
    subst x
    refine ⟨neutralToSplit n (0, φ), ?_⟩
    rw [splitVacuumSheetProjector_apply]
    simp [neutralVacuumSheetMap]

/-- The projector range is maximal isotropic for the symmetric split form. -/
theorem splitVacuumSheetProjector_range_isMaximalIsotropic (n : ℕ) :
    TowerIsMaximalIsotropic n
      (LinearMap.range (splitVacuumSheetProjector n) : Set (TowerSpace n)) := by
  rw [splitVacuumSheetProjector_range_eq_vacuumSheet]
  exact neutralVacuumSheet_range_isMaximalIsotropic n

/-- The exterior-algebra image of a vacuum-sheet vector belongs to odd
super-grade. This is the transported Mathlib Clifford parity grading, with
the exterior wedge product kept distinct from Clifford geometric product. -/
theorem neutralVacuumSheet_exterior_mem_superGrade_one (n : ℕ)
    (φ : Module.Dual ℝ (Vector n)) :
    ExteriorAlgebra.ι ℝ (neutralVacuumSheetMap n φ) ∈
      InfoGeometry.Algebra.SuperGrassmannianClifford.superGrade
        (TowerForm n) (1 : ZMod 2) := by
  exact InfoGeometry.Algebra.SuperGrassmannianClifford.exteriorGenerator_mem_superGrade_one
    (TowerForm n) (neutralVacuumSheetMap n φ)

/-- The Clifford geometric square of a vacuum-sheet exterior generator
vanishes, because the corresponding vector is isotropic. -/
@[simp] theorem neutralVacuumSheet_exterior_geometricProduct_sq (n : ℕ)
    (φ : Module.Dual ℝ (Vector n)) :
    InfoGeometry.Algebra.SuperGrassmannianClifford.geometricProduct
        (TowerForm n)
        (ExteriorAlgebra.ι ℝ (neutralVacuumSheetMap n φ))
        (ExteriorAlgebra.ι ℝ (neutralVacuumSheetMap n φ)) = 0 := by
  rw [InfoGeometry.Algebra.SuperGrassmannianClifford.geometricProduct_vector_square]
  rw [neutralVacuumSheetMap_isotropic, map_zero]

/-- A finite-stage vacuum-sheet Clifford generator is odd in Mathlib's native
even/odd grading of the symmetric split Clifford algebra. -/
theorem neutralVacuumSheet_clifford_mem_odd (n : ℕ)
    (φ : Module.Dual ℝ (Vector n)) :
    CliffordAlgebra.ι (TowerForm n) (neutralVacuumSheetMap n φ) ∈
      CliffordAlgebra.evenOdd (TowerForm n) 1 :=
  CliffordAlgebra.ι_mem_evenOdd_one (Q := TowerForm n) _

/-- The image of every finite-rank vacuum-sheet generator remains odd in the
repository's canonical direct-limit `Cl(N,N)` algebra. -/
theorem neutralVacuumSheet_colimit_odd (n : ℕ)
    (φ : Module.Dual ℝ (Vector n)) :
    InfoGeometry.Canonical.SplitCliffordSuperGradeColimit.splitCliffordInfinityInvolute
        (DirectLimit.Algebra.of
          InfoGeometry.Canonical.SplitCliffordTensorBridge.SplitClNNAlg
          (fun i j hij =>
            InfoGeometry.Canonical.SplitCliffordDirectLimit.splitCliffordMap i j hij)
          n (CliffordAlgebra.ι (TowerForm n) (neutralVacuumSheetMap n φ))) =
      -DirectLimit.Algebra.of
        InfoGeometry.Canonical.SplitCliffordTensorBridge.SplitClNNAlg
        (fun i j hij =>
          InfoGeometry.Canonical.SplitCliffordDirectLimit.splitCliffordMap i j hij)
        n (CliffordAlgebra.ι (TowerForm n) (neutralVacuumSheetMap n φ)) := by
  exact InfoGeometry.Canonical.SplitCliffordSuperGradeColimit.directLimit_of_odd_negated
    n (neutralVacuumSheet_clifford_mem_odd n φ)

end InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

end
