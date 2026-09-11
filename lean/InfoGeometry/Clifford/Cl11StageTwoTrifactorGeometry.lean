import InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl11MoritaNeutralStabilization
import InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv
import InfoGeometry.Projective.ExteriorKleinTwoPlaneIncidence

noncomputable section

namespace InfoGeometry.Clifford.Cl11StageTwoTrifactorGeometry

open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.Cl11StageTwoMatrixEquivalence
open InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows
open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv
open InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient
open InfoGeometry.Projective.ExteriorKleinProjective
open InfoGeometry.Projective.ExteriorKleinTwoPlaneIncidence

abbrev StageTwo := MatStage 2

theorem stageTwo_finPowTwo_eq_four : (2 : ℕ) ^ 2 = 4 := by norm_num

theorem stageTwo_index_card : Fintype.card (TowerMatrix.Idx 2) = 4 := by
  simpa using TowerMatrix.idx_card_pow_two 2

/-! --------------------------------------------------------------------------
    Stage-two action reindexing
    -------------------------------------------------------------------------- -/

/-- The existing four-coordinate carrier reindexed to the standard `Fin 4`
matrix coordinates used by `matEquivFinPowTwo 2`. -/
noncomputable def vec4ToFin4 :
    Vec4 ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.piCongrLeft ℝ (fun _ : Fin 4 => ℝ)
    (Fintype.equivFin I4)

/-- The native stage-two matrix transported to the standard `4 × 4` matrix
coordinates. -/
noncomputable def stageTwoMatrix4 (A : StageTwo) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  TowerMatrix.matEquivFinPowTwo 2 A

@[simp] theorem stageTwoMatrix4_mul (A B : StageTwo) :
    stageTwoMatrix4 (A * B) = stageTwoMatrix4 A * stageTwoMatrix4 B := by
  exact (TowerMatrix.matEquivFinPowTwo 2).map_mul A B

@[simp] theorem stageTwoMatrix4_one :
    stageTwoMatrix4 (1 : StageTwo) = 1 := by
  exact (TowerMatrix.matEquivFinPowTwo 2).map_one

/-- The linear action of a native stage-two element on the existing real
four-vector carrier. -/
noncomputable def stageTwoAction (A : StageTwo) :
    Vec4 →ₗ[ℝ] Vec4 :=
  vec4ToFin4.symm.toLinearMap.comp
    ((Matrix.toLin' (stageTwoMatrix4 A)).comp vec4ToFin4.toLinearMap)

@[simp] theorem stageTwoAction_one :
    stageTwoAction (1 : StageTwo) = LinearMap.id := by
  ext v i
  simp [stageTwoAction, vec4ToFin4, stageTwoMatrix4]

theorem stageTwoAction_mul (A B : StageTwo) :
    stageTwoAction (A * B) =
      (stageTwoAction A).comp (stageTwoAction B) := by
  ext v
  simp only [stageTwoAction, stageTwoMatrix4_mul, Matrix.toLin'_mul,
    LinearMap.comp_apply, LinearEquiv.coe_coe, Function.comp_apply]
  simp

/-- Units of the native stage-two algebra act by linear equivalences on the
existing four-vector carrier. -/
noncomputable def stageTwoActionEquiv (u : StageTwoˣ) :
    Vec4 ≃ₗ[ℝ] Vec4 where
  toFun := stageTwoAction (u : StageTwo)
  invFun := stageTwoAction (↑(u⁻¹) : StageTwo)
  map_add' := (stageTwoAction (u : StageTwo)).map_add
  map_smul' := (stageTwoAction (u : StageTwo)).map_smul
  left_inv := by
    intro v
    have h := congrArg
      (fun f : Vec4 →ₗ[ℝ] Vec4 => f v)
      (stageTwoAction_mul (↑(u⁻¹) : StageTwo) (u : StageTwo))
    simpa [LinearMap.comp_apply] using h.symm
  right_inv := by
    intro v
    have h := congrArg
      (fun f : Vec4 →ₗ[ℝ] Vec4 => f v)
      (stageTwoAction_mul (u : StageTwo) (↑(u⁻¹) : StageTwo))
    simpa [LinearMap.comp_apply] using h.symm

theorem stageTwoActionEquiv_mul (u v : StageTwoˣ) :
    stageTwoActionEquiv (u * v) =
      (stageTwoActionEquiv v).trans (stageTwoActionEquiv u) := by
  apply LinearEquiv.ext
  intro x
  change stageTwoAction (u * v : StageTwo) x =
    stageTwoAction (u : StageTwo)
      (stageTwoAction (v : StageTwo) x)
  simpa [LinearMap.comp_apply] using
    congrArg (fun f : Vec4 →ₗ[ℝ] Vec4 => f x)
      (stageTwoAction_mul (u : StageTwo) (v : StageTwo))

theorem stageTwoActionEquiv_matrix4_readout
    (u : StageTwoˣ) (x : Vec4) :
    vec4ToFin4 (stageTwoActionEquiv u x) =
      (InfoGeometry.Canonical.Cl11MoritaNeutralStabilization.stageTwoMatrix4Unit u)
        *ᵥ vec4ToFin4 x := by
  simp [stageTwoActionEquiv, stageTwoAction, stageTwoMatrix4,
    InfoGeometry.Canonical.Cl11MoritaNeutralStabilization.stageTwoMatrix4Unit]

@[simp] theorem stageTwoActionEquiv_one :
    stageTwoActionEquiv (1 : StageTwoˣ) = LinearEquiv.refl ℝ Vec4 := by
  apply LinearEquiv.ext
  intro x
  change stageTwoAction (1 : StageTwo) x = x
  simp

def IsEllipticGenerator (J : StageTwo) : Prop :=
  J * J = -(1 : StageTwo) ∧ Matrix.transpose J = -J

def IsHyperbolicGenerator (H : StageTwo) : Prop := H * H = (1 : StageTwo)

def IsParabolicGenerator (N : StageTwo) : Prop := N * N = 0

def IsLoxodromicPair (J H : StageTwo) : Prop :=
  IsEllipticGenerator J ∧ IsHyperbolicGenerator H ∧ Commute J H

def ellipticFlow (J : StageTwo) (t : ℝ) : StageTwo :=
  InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows.ellipticFlow J t

def hyperbolicFlow (H : StageTwo) (t : ℝ) : StageTwo :=
  InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows.hyperbolicFlow H t

def parabolicFlow (N : StageTwo) (t : ℝ) : StageTwo :=
  InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows.parabolicFlow N t

theorem ellipticFlow_zero (J : StageTwo) : ellipticFlow J 0 = 1 := by
  simpa [ellipticFlow] using
    InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows.ellipticFlow_zero J

theorem ellipticFlow_add {J : StageTwo} (hJ : IsEllipticGenerator J) (s t : ℝ) :
    ellipticFlow J s * ellipticFlow J t = ellipticFlow J (s + t) := by
  exact InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows.ellipticFlow_add J hJ.1 s t

theorem ellipticFlow_mul_neg {J : StageTwo} (hJ : IsEllipticGenerator J) (t : ℝ) :
    ellipticFlow J t * ellipticFlow J (-t) = 1 := by
  exact InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows.ellipticFlow_inverse J hJ.1 t

theorem ellipticFlow_neg_mul {J : StageTwo} (hJ : IsEllipticGenerator J) (t : ℝ) :
    ellipticFlow J (-t) * ellipticFlow J t = 1 := by
  simpa [ellipticFlow] using ellipticFlow_mul_neg hJ (-t)

theorem ellipticFlow_transpose {J : StageTwo}
    (hJ : IsEllipticGenerator J) (t : ℝ) :
    Matrix.transpose (ellipticFlow J t) = ellipticFlow J (-t) := by
  unfold ellipticFlow InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows.ellipticFlow
  simp [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
    hJ.2, Real.cos_neg, Real.sin_neg]

theorem ellipticFlow_transpose_mul_self {J : StageTwo}
    (hJ : IsEllipticGenerator J) (t : ℝ) :
    Matrix.transpose (ellipticFlow J t) * ellipticFlow J t = 1 := by
  rw [ellipticFlow_transpose hJ]
  exact ellipticFlow_neg_mul hJ t

theorem ellipticFlow_mul_transpose {J : StageTwo}
    (hJ : IsEllipticGenerator J) (t : ℝ) :
    ellipticFlow J t * Matrix.transpose (ellipticFlow J t) = 1 := by
  rw [ellipticFlow_transpose hJ]
  exact ellipticFlow_mul_neg hJ t

theorem hyperbolicFlow_zero (H : StageTwo) : hyperbolicFlow H 0 = 1 := by
  simpa [hyperbolicFlow] using
    InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows.hyperbolicFlow_zero H

theorem hyperbolicFlow_add {H : StageTwo}
    (hH : IsHyperbolicGenerator H) (s t : ℝ) :
    hyperbolicFlow H s * hyperbolicFlow H t = hyperbolicFlow H (s + t) := by
  exact InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows.hyperbolicFlow_add H hH s t

theorem hyperbolicFlow_mul_neg {H : StageTwo}
    (hH : IsHyperbolicGenerator H) (t : ℝ) :
    hyperbolicFlow H t * hyperbolicFlow H (-t) = 1 := by
  exact InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows.hyperbolicFlow_inverse H hH t

theorem hyperbolicFlow_neg_mul {H : StageTwo}
    (hH : IsHyperbolicGenerator H) (t : ℝ) :
    hyperbolicFlow H (-t) * hyperbolicFlow H t = 1 := by
  simpa [hyperbolicFlow] using hyperbolicFlow_mul_neg hH (-t)

theorem parabolicFlow_zero (N : StageTwo) : parabolicFlow N 0 = 1 := by
  simpa [parabolicFlow] using
    InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows.parabolicFlow_zero N

theorem parabolicFlow_add {N : StageTwo}
    (hN : IsParabolicGenerator N) (s t : ℝ) :
    parabolicFlow N s * parabolicFlow N t = parabolicFlow N (s + t) := by
  exact InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows.parabolicFlow_add N hN s t

theorem parabolicFlow_mul_neg {N : StageTwo}
    (hN : IsParabolicGenerator N) (t : ℝ) :
    parabolicFlow N t * parabolicFlow N (-t) = 1 := by
  exact InfoGeometry.Canonical.Cl11StageTwoTrifactorFlows.parabolicFlow_inverse N hN t

theorem parabolicFlow_neg_mul {N : StageTwo}
    (hN : IsParabolicGenerator N) (t : ℝ) :
    parabolicFlow N (-t) * parabolicFlow N t = 1 := by
  simpa [parabolicFlow] using parabolicFlow_mul_neg hN (-t)

theorem parabolicFlow_sub_one_sq {N : StageTwo}
    (hN : IsParabolicGenerator N) (t : ℝ) :
    (parabolicFlow N t - 1) * (parabolicFlow N t - 1) = 0 := by
  change ((1 : StageTwo) + t • N - 1) * ((1 : StageTwo) + t • N - 1) = 0
  have hsub : (1 : StageTwo) + t • N - 1 = t • N := by module
  have hNN : N * N = 0 := hN
  rw [hsub]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hNN, smul_zero]

theorem ellipticFlow_commutes_hyperbolicFlow
    {J H : StageTwo} (hcomm : Commute J H) (t s : ℝ) :
    ellipticFlow J t * hyperbolicFlow H s =
      hyperbolicFlow H s * ellipticFlow J t := by
  exact ellipticFlow_hyperbolicFlow_commute J H hcomm.eq t s

def loxodromicFlow (J H : StageTwo) (t : ℝ) : StageTwo :=
  ellipticFlow J t * hyperbolicFlow H t

theorem loxodromicFlow_zero (J H : StageTwo) : loxodromicFlow J H 0 = 1 := by
  simp [loxodromicFlow, ellipticFlow_zero, hyperbolicFlow_zero]

theorem loxodromicFlow_add {J H : StageTwo}
    (h : IsLoxodromicPair J H) (s t : ℝ) :
    loxodromicFlow J H s * loxodromicFlow J H t =
      loxodromicFlow J H (s + t) := by
  rcases h with ⟨hJ, hH, hcomm⟩
  unfold loxodromicFlow
  calc
    (ellipticFlow J s * hyperbolicFlow H s) *
        (ellipticFlow J t * hyperbolicFlow H t) =
        ellipticFlow J s *
          (hyperbolicFlow H s * ellipticFlow J t) *
            hyperbolicFlow H t := by simp only [mul_assoc]
    _ = ellipticFlow J s *
          (ellipticFlow J t * hyperbolicFlow H s) *
            hyperbolicFlow H t := by
      have hc := ellipticFlow_hyperbolicFlow_commute J H hcomm.eq t s
      exact congrArg (fun X => ellipticFlow J s * X * hyperbolicFlow H t) hc.symm
    _ = (ellipticFlow J s * ellipticFlow J t) *
          (hyperbolicFlow H s * hyperbolicFlow H t) := by
      simp only [mul_assoc]
    _ = ellipticFlow J (s + t) * hyperbolicFlow H (s + t) := by
      rw [ellipticFlow_add hJ s t, hyperbolicFlow_add hH s t]

theorem loxodromicFlow_mul_neg {J H : StageTwo}
    (h : IsLoxodromicPair J H) (t : ℝ) :
    loxodromicFlow J H t * loxodromicFlow J H (-t) = 1 := by
  rw [loxodromicFlow_add h t (-t)]
  simp [loxodromicFlow_zero]

noncomputable def mapRealTwoPlane
    (g : Vec4 ≃ₗ[ℝ] Vec4) (P : RealTwoPlane) : RealTwoPlane :=
  ⟨P.1.map g.toLinearMap, by
    rw [g.finrank_map_eq]
    exact P.2⟩

@[simp] theorem mapRealTwoPlane_refl (P : RealTwoPlane) :
    mapRealTwoPlane (LinearEquiv.refl ℝ Vec4) P = P := by
  apply Subtype.ext
  simp [mapRealTwoPlane]

@[simp] theorem mapRealTwoPlane_trans
    (g h : Vec4 ≃ₗ[ℝ] Vec4) (P : RealTwoPlane) :
    mapRealTwoPlane (g.trans h) P = mapRealTwoPlane h (mapRealTwoPlane g P) := by
  apply Subtype.ext
  apply Submodule.ext
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

@[simp] theorem mapRealTwoPlane_symm_apply
    (g : Vec4 ≃ₗ[ℝ] Vec4) (P : RealTwoPlane) :
    mapRealTwoPlane g.symm (mapRealTwoPlane g P) = P := by
  rw [← mapRealTwoPlane_trans]
  simpa using mapRealTwoPlane_refl P

/-- The induced bijection on the existing two-plane carrier.  This is the
linear-action part of the Grassmannian readout; no new Grassmannian type is
introduced here. -/
noncomputable def mapRealTwoPlaneEquiv
    (g : Vec4 ≃ₗ[ℝ] Vec4) : RealTwoPlane ≃ RealTwoPlane :=
  { toFun := mapRealTwoPlane g
    invFun := mapRealTwoPlane g.symm
    left_inv := by intro P; exact mapRealTwoPlane_symm_apply g P
    right_inv := by intro P; exact mapRealTwoPlane_symm_apply g.symm P }

@[simp] theorem mapRealTwoPlaneEquiv_apply
    (g : Vec4 ≃ₗ[ℝ] Vec4) (P : RealTwoPlane) :
    mapRealTwoPlaneEquiv g P = mapRealTwoPlane g P :=
  rfl

@[simp] theorem mapRealTwoPlaneEquiv_symm_apply
    (g : Vec4 ≃ₗ[ℝ] Vec4) (P : RealTwoPlane) :
    (mapRealTwoPlaneEquiv g).symm P = mapRealTwoPlane g.symm P :=
  rfl

@[simp] theorem mapRealTwoPlaneEquiv_trans
    (g h : Vec4 ≃ₗ[ℝ] Vec4) (P : RealTwoPlane) :
    mapRealTwoPlaneEquiv (g.trans h) P =
      mapRealTwoPlaneEquiv h (mapRealTwoPlaneEquiv g P) := by
  exact mapRealTwoPlane_trans g h P

noncomputable def stageTwoUnitPlaneAction (u : StageTwoˣ) :
    RealTwoPlane ≃ RealTwoPlane :=
  mapRealTwoPlaneEquiv (stageTwoActionEquiv u)

@[simp] theorem stageTwoUnitPlaneAction_one :
    stageTwoUnitPlaneAction 1 = Equiv.refl RealTwoPlane := by
  have hOne :
      stageTwoActionEquiv (1 : StageTwoˣ) = LinearEquiv.refl ℝ Vec4 := by
    apply LinearEquiv.ext
    intro x
    have h := congrArg (fun f : Vec4 →ₗ[ℝ] Vec4 => f x)
      (stageTwoAction_one)
    simpa [stageTwoActionEquiv] using h
  apply Equiv.ext
  intro P
  change mapRealTwoPlaneEquiv (stageTwoActionEquiv (1 : StageTwoˣ)) P = P
  rw [hOne]
  exact mapRealTwoPlane_refl P

theorem stageTwoUnitPlaneAction_mul (u v : StageTwoˣ) :
    stageTwoUnitPlaneAction (u * v) =
      (stageTwoUnitPlaneAction v).trans
        (stageTwoUnitPlaneAction u) := by
  apply Equiv.ext
  intro P
  change mapRealTwoPlaneEquiv (stageTwoActionEquiv (u * v)) P =
    (mapRealTwoPlaneEquiv (stageTwoActionEquiv v)).trans
      (mapRealTwoPlaneEquiv (stageTwoActionEquiv u)) P
  rw [stageTwoActionEquiv_mul]
  exact mapRealTwoPlaneEquiv_trans
    (stageTwoActionEquiv v) (stageTwoActionEquiv u) P

/-! --------------------------------------------------------------------------
    Native Klein-locus action
    -------------------------------------------------------------------------- -/

noncomputable def mapKleinLocusEquiv
    (g : Vec4 ≃ₗ[ℝ] Vec4) :
    InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus ≃
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus :=
  (realTwoPlaneEquivKleinLocus.symm.trans (mapRealTwoPlaneEquiv g)).trans
    realTwoPlaneEquivKleinLocus

theorem mapKleinLocusEquiv_apply
    (g : Vec4 ≃ₗ[ℝ] Vec4)
    (p : InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    mapKleinLocusEquiv g p =
      realTwoPlaneEquivKleinLocus
        (mapRealTwoPlaneEquiv g
          (realTwoPlaneEquivKleinLocus.symm p)) :=
  rfl

@[simp] theorem mapKleinLocusEquiv_refl
    (p : InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    mapKleinLocusEquiv (LinearEquiv.refl ℝ Vec4) p = p := by
  simp [mapKleinLocusEquiv]

@[simp] theorem mapKleinLocusEquiv_trans
    (g h : Vec4 ≃ₗ[ℝ] Vec4)
    (p : InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    mapKleinLocusEquiv (g.trans h) p =
      mapKleinLocusEquiv h (mapKleinLocusEquiv g p) := by
  simp only [mapKleinLocusEquiv, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  rw [mapRealTwoPlaneEquiv_trans]

@[simp] theorem mapKleinLocusEquiv_symm_apply
    (g : Vec4 ≃ₗ[ℝ] Vec4)
    (p : InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    (mapKleinLocusEquiv g).symm p = mapKleinLocusEquiv g.symm p := by
  simp [mapKleinLocusEquiv, mapRealTwoPlaneEquiv]

theorem mapRealTwoPlane_preserves_incidence
    (g : Vec4 ≃ₗ[ℝ] Vec4) (P Q : RealTwoPlane) :
    PlanesIncident P Q ↔
      PlanesIncident (mapRealTwoPlane g P) (mapRealTwoPlane g Q) := by
  constructor
  · intro h
    obtain ⟨x, hx, hxP, hxQ⟩ :=
      (planesIncident_iff_exists_nonzero_mem P Q).1 h
    apply (planesIncident_iff_exists_nonzero_mem
      (mapRealTwoPlane g P) (mapRealTwoPlane g Q)).2
    refine ⟨g x, ?_, ⟨x, hxP, rfl⟩, ⟨x, hxQ, rfl⟩⟩
    intro hzero
    apply hx
    apply g.injective
    rw [map_zero]
    exact hzero
  · intro h
    obtain ⟨x, hx, hxP, hxQ⟩ :=
      (planesIncident_iff_exists_nonzero_mem
        (mapRealTwoPlane g P) (mapRealTwoPlane g Q)).1 h
    apply (planesIncident_iff_exists_nonzero_mem P Q).2
    refine ⟨g.symm x, ?_, ?_, ?_⟩
    · intro hzero
      apply hx
      apply g.symm.injective
      rw [map_zero]
      exact hzero
    · rcases hxP with ⟨y, hy, rfl⟩
      convert hy using 1 <;> simp
    · rcases hxQ with ⟨y, hy, rfl⟩
      convert hy using 1 <;> simp

theorem mapKleinLocusEquiv_preserves_incidence
    (g : Vec4 ≃ₗ[ℝ] Vec4)
    (p q : InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    KleinIncident p q ↔
      KleinIncident (mapKleinLocusEquiv g p) (mapKleinLocusEquiv g q) := by
  change PlanesIncident (realTwoPlaneEquivKleinLocus.symm p)
      (realTwoPlaneEquivKleinLocus.symm q) ↔
    PlanesIncident
      (realTwoPlaneEquivKleinLocus.symm (mapKleinLocusEquiv g p))
      (realTwoPlaneEquivKleinLocus.symm (mapKleinLocusEquiv g q))
  rw [mapKleinLocusEquiv_apply, mapKleinLocusEquiv_apply]
  simp only [Equiv.symm_apply_apply]
  exact mapRealTwoPlane_preserves_incidence g _ _

noncomputable def stageTwoUnitKleinAction (u : StageTwoˣ) :
    InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus ≃
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus :=
  mapKleinLocusEquiv (stageTwoActionEquiv u)

@[simp] theorem stageTwoUnitKleinAction_one (p :
    InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    stageTwoUnitKleinAction 1 p = p := by
  simp [stageTwoUnitKleinAction]

@[simp] theorem stageTwoUnitKleinAction_mul (u v : StageTwoˣ) (p :
    InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    stageTwoUnitKleinAction (u * v) p =
      stageTwoUnitKleinAction u (stageTwoUnitKleinAction v p) := by
  change mapKleinLocusEquiv (stageTwoActionEquiv (u * v)) p =
    mapKleinLocusEquiv (stageTwoActionEquiv u)
      (mapKleinLocusEquiv (stageTwoActionEquiv v) p)
  rw [stageTwoActionEquiv_mul, mapKleinLocusEquiv_trans]

theorem stageTwoActionEquiv_symm (u : StageTwoˣ) :
    (stageTwoActionEquiv u).symm = stageTwoActionEquiv (u⁻¹) := by
  rfl

theorem stageTwoUnitKleinAction_symm_apply
    (u : StageTwoˣ)
    (p : InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    (stageTwoUnitKleinAction u).symm p =
      stageTwoUnitKleinAction (u⁻¹) p := by
  change mapKleinLocusEquiv (stageTwoActionEquiv u).symm p =
    mapKleinLocusEquiv (stageTwoActionEquiv (u⁻¹)) p
  rw [stageTwoActionEquiv_symm]

theorem stageTwoUnitKleinAction_symm
    (u : StageTwoˣ) :
    (stageTwoUnitKleinAction u).symm =
      stageTwoUnitKleinAction (u⁻¹) := by
  apply Equiv.ext
  intro p
  exact stageTwoUnitKleinAction_symm_apply u p

theorem stageTwoUnitKleinAction_preserves_incidence
    (u : StageTwoˣ)
    (p q : InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    KleinIncident p q ↔
      KleinIncident (stageTwoUnitKleinAction u p)
        (stageTwoUnitKleinAction u q) := by
  exact mapKleinLocusEquiv_preserves_incidence
    (stageTwoActionEquiv u) p q

/-! --------------------------------------------------------------------------
    Filtered-colimit readback of the finite flows
    -------------------------------------------------------------------------- -/

theorem limit_ellipticFlow_add
    {J : StageTwo}
    (hJ : IsEllipticGenerator J)
    (s t : ℝ) :
    ofStage 2 (ellipticFlow J s) * ofStage 2 (ellipticFlow J t) =
      ofStage 2 (ellipticFlow J (s + t)) := by
  rw [← ofStage_mul]
  exact congrArg (ofStage 2) (ellipticFlow_add hJ s t)

theorem limit_hyperbolicFlow_add
    {H : StageTwo}
    (hH : IsHyperbolicGenerator H)
    (s t : ℝ) :
    ofStage 2 (hyperbolicFlow H s) * ofStage 2 (hyperbolicFlow H t) =
      ofStage 2 (hyperbolicFlow H (s + t)) := by
  rw [← ofStage_mul]
  exact congrArg (ofStage 2) (hyperbolicFlow_add hH s t)

theorem limit_parabolicFlow_add
    {N : StageTwo}
    (hN : IsParabolicGenerator N)
    (s t : ℝ) :
    ofStage 2 (parabolicFlow N s) * ofStage 2 (parabolicFlow N t) =
      ofStage 2 (parabolicFlow N (s + t)) := by
  rw [← ofStage_mul]
  exact congrArg (ofStage 2) (parabolicFlow_add hN s t)

theorem limit_loxodromicFlow_add
    {J H : StageTwo}
    (h : IsLoxodromicPair J H)
    (s t : ℝ) :
    ofStage 2 (loxodromicFlow J H s) *
        ofStage 2 (loxodromicFlow J H t) =
      ofStage 2 (loxodromicFlow J H (s + t)) := by
  rw [← ofStage_mul]
  exact congrArg (ofStage 2) (loxodromicFlow_add h s t)

theorem limit_ellipticFlow_mul_neg
    {J : StageTwo}
    (hJ : IsEllipticGenerator J)
    (t : ℝ) :
    ofStage 2 (ellipticFlow J t) *
        ofStage 2 (ellipticFlow J (-t)) = 1 := by
  rw [← ofStage_mul, ellipticFlow_mul_neg hJ]
  exact ofStage_one 2

theorem limit_hyperbolicFlow_mul_neg
    {H : StageTwo}
    (hH : IsHyperbolicGenerator H)
    (t : ℝ) :
    ofStage 2 (hyperbolicFlow H t) *
        ofStage 2 (hyperbolicFlow H (-t)) = 1 := by
  rw [← ofStage_mul, hyperbolicFlow_mul_neg hH]
  exact ofStage_one 2

theorem limit_parabolicFlow_mul_neg
    {N : StageTwo}
    (hN : IsParabolicGenerator N)
    (t : ℝ) :
    ofStage 2 (parabolicFlow N t) *
        ofStage 2 (parabolicFlow N (-t)) = 1 := by
  rw [← ofStage_mul, parabolicFlow_mul_neg hN]
  exact ofStage_one 2

theorem limit_loxodromicFlow_mul_neg
    {J H : StageTwo}
    (h : IsLoxodromicPair J H)
    (t : ℝ) :
    ofStage 2 (loxodromicFlow J H t) *
        ofStage 2 (loxodromicFlow J H (-t)) = 1 := by
  rw [← ofStage_mul, loxodromicFlow_mul_neg h]
  exact ofStage_one 2

theorem limit_ellipticFlow_neg_mul
    {J : StageTwo}
    (hJ : IsEllipticGenerator J)
    (t : ℝ) :
    ofStage 2 (ellipticFlow J (-t)) *
        ofStage 2 (ellipticFlow J t) = 1 := by
  rw [← ofStage_mul, ellipticFlow_neg_mul hJ]
  exact ofStage_one 2

theorem limit_hyperbolicFlow_neg_mul
    {H : StageTwo}
    (hH : IsHyperbolicGenerator H)
    (t : ℝ) :
    ofStage 2 (hyperbolicFlow H (-t)) *
        ofStage 2 (hyperbolicFlow H t) = 1 := by
  rw [← ofStage_mul, hyperbolicFlow_neg_mul hH]
  exact ofStage_one 2

theorem limit_parabolicFlow_neg_mul
    {N : StageTwo}
    (hN : IsParabolicGenerator N)
    (t : ℝ) :
    ofStage 2 (parabolicFlow N (-t)) *
        ofStage 2 (parabolicFlow N t) = 1 := by
  rw [← ofStage_mul, parabolicFlow_neg_mul hN]
  exact ofStage_one 2

theorem limit_loxodromicFlow_neg_mul
    {J H : StageTwo}
    (h : IsLoxodromicPair J H)
    (t : ℝ) :
    ofStage 2 (loxodromicFlow J H (-t)) *
        ofStage 2 (loxodromicFlow J H t) = 1 := by
  rw [← ofStage_mul]
  have h' := loxodromicFlow_add h (-t) t
  have h'' := congrArg (ofStage 2) h'
  have hz : -t + t = (0 : ℝ) := by ring
  rw [hz, loxodromicFlow_zero, ofStage_one] at h''
  exact h''

theorem limit_ellipticFlow_commutes_hyperbolicFlow
    {J H : StageTwo}
    (h : IsLoxodromicPair J H)
    (s t : ℝ) :
    ofStage 2 (ellipticFlow J s) *
        ofStage 2 (hyperbolicFlow H t) =
      ofStage 2 (hyperbolicFlow H t) *
        ofStage 2 (ellipticFlow J s) := by
  rw [← ofStage_mul, ← ofStage_mul]
  exact congrArg (ofStage 2)
    (ellipticFlow_commutes_hyperbolicFlow h.2.2 s t)

theorem limit_parabolicFlow_sub_one_sq
    {N : StageTwo}
    (hN : IsParabolicGenerator N)
    (t : ℝ) :
    (ofStage 2 (parabolicFlow N t) - 1) *
        (ofStage 2 (parabolicFlow N t) - 1) = 0 := by
  simpa only [ofStage_sub, ofStage_one, ofStage_mul, ofStage_zero] using
    congrArg (ofStage 2) (parabolicFlow_sub_one_sq hN t)

noncomputable def ellipticFlowUnit
    (J : StageTwo) (hJ : IsEllipticGenerator J) (t : ℝ) : StageTwoˣ :=
  Units.mkOfMulEqOne (ellipticFlow J t) (ellipticFlow J (-t))
    (ellipticFlow_mul_neg hJ t)

@[simp] theorem ellipticFlowUnit_val
    (J : StageTwo) (hJ : IsEllipticGenerator J) (t : ℝ) :
    (ellipticFlowUnit J hJ t : StageTwo) = ellipticFlow J t :=
  Units.val_mkOfMulEqOne _

noncomputable def hyperbolicFlowUnit
    (H : StageTwo) (hH : IsHyperbolicGenerator H) (t : ℝ) : StageTwoˣ :=
  Units.mkOfMulEqOne (hyperbolicFlow H t) (hyperbolicFlow H (-t))
    (hyperbolicFlow_mul_neg hH t)

@[simp] theorem hyperbolicFlowUnit_val
    (H : StageTwo) (hH : IsHyperbolicGenerator H) (t : ℝ) :
    (hyperbolicFlowUnit H hH t : StageTwo) = hyperbolicFlow H t :=
  Units.val_mkOfMulEqOne _

noncomputable def parabolicFlowUnit
    (N : StageTwo) (hN : IsParabolicGenerator N) (t : ℝ) : StageTwoˣ :=
  Units.mkOfMulEqOne (parabolicFlow N t) (parabolicFlow N (-t))
    (parabolicFlow_mul_neg hN t)

@[simp] theorem parabolicFlowUnit_val
    (N : StageTwo) (hN : IsParabolicGenerator N) (t : ℝ) :
    (parabolicFlowUnit N hN t : StageTwo) = parabolicFlow N t :=
  Units.val_mkOfMulEqOne _

noncomputable def loxodromicFlowUnit
    (J H : StageTwo) (h : IsLoxodromicPair J H) (t : ℝ) : StageTwoˣ :=
  Units.mkOfMulEqOne (loxodromicFlow J H t) (loxodromicFlow J H (-t))
    (loxodromicFlow_mul_neg h t)

@[simp] theorem loxodromicFlowUnit_val
    (J H : StageTwo) (h : IsLoxodromicPair J H) (t : ℝ) :
    (loxodromicFlowUnit J H h t : StageTwo) = loxodromicFlow J H t :=
  Units.val_mkOfMulEqOne _

noncomputable def limitEllipticFlowUnit
    (J : StageTwo) (hJ : IsEllipticGenerator J) (t : ℝ) :
    (Cl11TensorTowerLimit.Limit)ˣ :=
  Units.map (ofStage 2).toMonoidHom (ellipticFlowUnit J hJ t)

@[simp] theorem limitEllipticFlowUnit_val
    (J : StageTwo) (hJ : IsEllipticGenerator J) (t : ℝ) :
    (limitEllipticFlowUnit J hJ t : Cl11TensorTowerLimit.Limit) =
      ofStage 2 (ellipticFlow J t) := by
  simp [limitEllipticFlowUnit]

noncomputable def limitHyperbolicFlowUnit
    (H : StageTwo) (hH : IsHyperbolicGenerator H) (t : ℝ) :
    (Cl11TensorTowerLimit.Limit)ˣ :=
  Units.map (ofStage 2).toMonoidHom (hyperbolicFlowUnit H hH t)

@[simp] theorem limitHyperbolicFlowUnit_val
    (H : StageTwo) (hH : IsHyperbolicGenerator H) (t : ℝ) :
    (limitHyperbolicFlowUnit H hH t : Cl11TensorTowerLimit.Limit) =
      ofStage 2 (hyperbolicFlow H t) := by
  simp [limitHyperbolicFlowUnit]

noncomputable def limitParabolicFlowUnit
    (N : StageTwo) (hN : IsParabolicGenerator N) (t : ℝ) :
    (Cl11TensorTowerLimit.Limit)ˣ :=
  Units.map (ofStage 2).toMonoidHom (parabolicFlowUnit N hN t)

@[simp] theorem limitParabolicFlowUnit_val
    (N : StageTwo) (hN : IsParabolicGenerator N) (t : ℝ) :
    (limitParabolicFlowUnit N hN t : Cl11TensorTowerLimit.Limit) =
      ofStage 2 (parabolicFlow N t) := by
  simp [limitParabolicFlowUnit]

noncomputable def limitLoxodromicFlowUnit
    (J H : StageTwo) (h : IsLoxodromicPair J H) (t : ℝ) :
    (Cl11TensorTowerLimit.Limit)ˣ :=
  Units.map (ofStage 2).toMonoidHom (loxodromicFlowUnit J H h t)

@[simp] theorem limitLoxodromicFlowUnit_val
    (J H : StageTwo) (h : IsLoxodromicPair J H) (t : ℝ) :
    (limitLoxodromicFlowUnit J H h t : Cl11TensorTowerLimit.Limit) =
      ofStage 2 (loxodromicFlow J H t) := by
  simp [limitLoxodromicFlowUnit]

theorem limitEllipticFlowUnit_add
    (J : StageTwo) (hJ : IsEllipticGenerator J) (s t : ℝ) :
    limitEllipticFlowUnit J hJ (s + t) =
      limitEllipticFlowUnit J hJ s * limitEllipticFlowUnit J hJ t := by
  apply Units.ext
  change ofStage 2 (ellipticFlow J (s + t)) =
    ofStage 2 (ellipticFlow J s) * ofStage 2 (ellipticFlow J t)
  rw [← ofStage_mul]
  exact congrArg (ofStage 2) (ellipticFlow_add hJ s t).symm

theorem limitHyperbolicFlowUnit_add
    (H : StageTwo) (hH : IsHyperbolicGenerator H) (s t : ℝ) :
    limitHyperbolicFlowUnit H hH (s + t) =
      limitHyperbolicFlowUnit H hH s * limitHyperbolicFlowUnit H hH t := by
  apply Units.ext
  change ofStage 2 (hyperbolicFlow H (s + t)) =
    ofStage 2 (hyperbolicFlow H s) * ofStage 2 (hyperbolicFlow H t)
  rw [← ofStage_mul]
  exact congrArg (ofStage 2) (hyperbolicFlow_add hH s t).symm

theorem limitParabolicFlowUnit_add
    (N : StageTwo) (hN : IsParabolicGenerator N) (s t : ℝ) :
    limitParabolicFlowUnit N hN (s + t) =
      limitParabolicFlowUnit N hN s * limitParabolicFlowUnit N hN t := by
  apply Units.ext
  change ofStage 2 (parabolicFlow N (s + t)) =
    ofStage 2 (parabolicFlow N s) * ofStage 2 (parabolicFlow N t)
  rw [← ofStage_mul]
  exact congrArg (ofStage 2) (parabolicFlow_add hN s t).symm

theorem limitLoxodromicFlowUnit_add
    (J H : StageTwo) (h : IsLoxodromicPair J H) (s t : ℝ) :
    limitLoxodromicFlowUnit J H h (s + t) =
      limitLoxodromicFlowUnit J H h s * limitLoxodromicFlowUnit J H h t := by
  apply Units.ext
  change ofStage 2 (loxodromicFlow J H (s + t)) =
    ofStage 2 (loxodromicFlow J H s) * ofStage 2 (loxodromicFlow J H t)
  rw [← ofStage_mul]
  exact congrArg (ofStage 2) (loxodromicFlow_add h s t).symm

noncomputable def ellipticFlowKleinAction
    (J : StageTwo) (hJ : IsEllipticGenerator J) (t : ℝ) :
    InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus ≃
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus :=
  stageTwoUnitKleinAction (ellipticFlowUnit J hJ t)

theorem ellipticFlowUnit_add
    (J : StageTwo) (hJ : IsEllipticGenerator J) (s t : ℝ) :
    ellipticFlowUnit J hJ (s + t) =
      ellipticFlowUnit J hJ s * ellipticFlowUnit J hJ t := by
  apply Units.ext
  change ellipticFlow J (s + t) =
    ellipticFlow J s * ellipticFlow J t
  exact (ellipticFlow_add hJ s t).symm

theorem ellipticFlowKleinAction_add
    (J : StageTwo) (hJ : IsEllipticGenerator J) (s t : ℝ) (p :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    ellipticFlowKleinAction J hJ (s + t) p =
      ellipticFlowKleinAction J hJ s
        (ellipticFlowKleinAction J hJ t p) := by
  change stageTwoUnitKleinAction
      (ellipticFlowUnit J hJ (s + t)) p =
    stageTwoUnitKleinAction (ellipticFlowUnit J hJ s)
      (stageTwoUnitKleinAction (ellipticFlowUnit J hJ t) p)
  rw [ellipticFlowUnit_add, stageTwoUnitKleinAction_mul]

noncomputable def hyperbolicFlowKleinAction
    (H : StageTwo) (hH : IsHyperbolicGenerator H) (t : ℝ) :
    InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus ≃
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus :=
  stageTwoUnitKleinAction (hyperbolicFlowUnit H hH t)

theorem hyperbolicFlowUnit_add
    (H : StageTwo) (hH : IsHyperbolicGenerator H) (s t : ℝ) :
    hyperbolicFlowUnit H hH (s + t) =
      hyperbolicFlowUnit H hH s * hyperbolicFlowUnit H hH t := by
  apply Units.ext
  change hyperbolicFlow H (s + t) =
    hyperbolicFlow H s * hyperbolicFlow H t
  exact (hyperbolicFlow_add hH s t).symm

theorem hyperbolicFlowKleinAction_add
    (H : StageTwo) (hH : IsHyperbolicGenerator H) (s t : ℝ) (p :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    hyperbolicFlowKleinAction H hH (s + t) p =
      hyperbolicFlowKleinAction H hH s
        (hyperbolicFlowKleinAction H hH t p) := by
  change stageTwoUnitKleinAction
      (hyperbolicFlowUnit H hH (s + t)) p =
    stageTwoUnitKleinAction (hyperbolicFlowUnit H hH s)
      (stageTwoUnitKleinAction (hyperbolicFlowUnit H hH t) p)
  rw [hyperbolicFlowUnit_add, stageTwoUnitKleinAction_mul]

noncomputable def parabolicFlowKleinAction
    (N : StageTwo) (hN : IsParabolicGenerator N) (t : ℝ) :
    InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus ≃
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus :=
  stageTwoUnitKleinAction (parabolicFlowUnit N hN t)

theorem parabolicFlowUnit_add
    (N : StageTwo) (hN : IsParabolicGenerator N) (s t : ℝ) :
    parabolicFlowUnit N hN (s + t) =
      parabolicFlowUnit N hN s * parabolicFlowUnit N hN t := by
  apply Units.ext
  change parabolicFlow N (s + t) =
    parabolicFlow N s * parabolicFlow N t
  exact (parabolicFlow_add hN s t).symm

theorem parabolicFlowKleinAction_add
    (N : StageTwo) (hN : IsParabolicGenerator N) (s t : ℝ) (p :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    parabolicFlowKleinAction N hN (s + t) p =
      parabolicFlowKleinAction N hN s
        (parabolicFlowKleinAction N hN t p) := by
  change stageTwoUnitKleinAction
      (parabolicFlowUnit N hN (s + t)) p =
    stageTwoUnitKleinAction (parabolicFlowUnit N hN s)
      (stageTwoUnitKleinAction (parabolicFlowUnit N hN t) p)
  rw [parabolicFlowUnit_add, stageTwoUnitKleinAction_mul]

noncomputable def loxodromicFlowKleinAction
    (J H : StageTwo) (h : IsLoxodromicPair J H) (t : ℝ) :
    InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus ≃
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus :=
  stageTwoUnitKleinAction (loxodromicFlowUnit J H h t)

theorem loxodromicFlowUnit_add
    (J H : StageTwo) (h : IsLoxodromicPair J H) (s t : ℝ) :
    loxodromicFlowUnit J H h (s + t) =
      loxodromicFlowUnit J H h s * loxodromicFlowUnit J H h t := by
  apply Units.ext
  change loxodromicFlow J H (s + t) =
    loxodromicFlow J H s * loxodromicFlow J H t
  exact (loxodromicFlow_add h s t).symm

theorem loxodromicFlowKleinAction_add
    (J H : StageTwo) (h : IsLoxodromicPair J H) (s t : ℝ) (p :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    loxodromicFlowKleinAction J H h (s + t) p =
      loxodromicFlowKleinAction J H h s
        (loxodromicFlowKleinAction J H h t p) := by
  change stageTwoUnitKleinAction
      (loxodromicFlowUnit J H h (s + t)) p =
    stageTwoUnitKleinAction (loxodromicFlowUnit J H h s)
      (stageTwoUnitKleinAction (loxodromicFlowUnit J H h t) p)
  rw [loxodromicFlowUnit_add, stageTwoUnitKleinAction_mul]

theorem ellipticFlowKleinAction_zero
    (J : StageTwo) (hJ : IsEllipticGenerator J) (p :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    ellipticFlowKleinAction J hJ 0 p = p := by
  change stageTwoUnitKleinAction (ellipticFlowUnit J hJ 0) p = p
  have hu : ellipticFlowUnit J hJ 0 = 1 := by
    apply Units.ext
    change ellipticFlow J 0 = 1
    exact ellipticFlow_zero J
  rw [hu]
  exact stageTwoUnitKleinAction_one p

theorem hyperbolicFlowKleinAction_zero
    (H : StageTwo) (hH : IsHyperbolicGenerator H) (p :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    hyperbolicFlowKleinAction H hH 0 p = p := by
  change stageTwoUnitKleinAction (hyperbolicFlowUnit H hH 0) p = p
  have hu : hyperbolicFlowUnit H hH 0 = 1 := by
    apply Units.ext
    change hyperbolicFlow H 0 = 1
    exact hyperbolicFlow_zero H
  rw [hu]
  exact stageTwoUnitKleinAction_one p

theorem parabolicFlowKleinAction_zero
    (N : StageTwo) (hN : IsParabolicGenerator N) (p :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    parabolicFlowKleinAction N hN 0 p = p := by
  change stageTwoUnitKleinAction (parabolicFlowUnit N hN 0) p = p
  have hu : parabolicFlowUnit N hN 0 = 1 := by
    apply Units.ext
    change parabolicFlow N 0 = 1
    exact parabolicFlow_zero N
  rw [hu]
  exact stageTwoUnitKleinAction_one p

theorem loxodromicFlowKleinAction_zero
    (J H : StageTwo) (h : IsLoxodromicPair J H) (p :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    loxodromicFlowKleinAction J H h 0 p = p := by
  change stageTwoUnitKleinAction (loxodromicFlowUnit J H h 0) p = p
  have hu : loxodromicFlowUnit J H h 0 = 1 := by
    apply Units.ext
    change loxodromicFlow J H 0 = 1
    exact loxodromicFlow_zero J H
  rw [hu]
  exact stageTwoUnitKleinAction_one p

theorem ellipticFlowKleinAction_neg_apply
    (J : StageTwo) (hJ : IsEllipticGenerator J) (t : ℝ) (p :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    ellipticFlowKleinAction J hJ (-t)
        (ellipticFlowKleinAction J hJ t p) = p := by
  have h := ellipticFlowKleinAction_add J hJ (-t) t p
  have hz : -t + t = (0 : ℝ) := by ring
  rw [hz, ellipticFlowKleinAction_zero] at h
  exact h.symm

theorem hyperbolicFlowKleinAction_neg_apply
    (H : StageTwo) (hH : IsHyperbolicGenerator H) (t : ℝ) (p :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    hyperbolicFlowKleinAction H hH (-t)
        (hyperbolicFlowKleinAction H hH t p) = p := by
  have h := hyperbolicFlowKleinAction_add H hH (-t) t p
  have hz : -t + t = (0 : ℝ) := by ring
  rw [hz, hyperbolicFlowKleinAction_zero] at h
  exact h.symm

theorem parabolicFlowKleinAction_neg_apply
    (N : StageTwo) (hN : IsParabolicGenerator N) (t : ℝ) (p :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    parabolicFlowKleinAction N hN (-t)
        (parabolicFlowKleinAction N hN t p) = p := by
  have h := parabolicFlowKleinAction_add N hN (-t) t p
  have hz : -t + t = (0 : ℝ) := by ring
  rw [hz, parabolicFlowKleinAction_zero] at h
  exact h.symm

theorem loxodromicFlowKleinAction_neg_apply
    (J H : StageTwo) (h : IsLoxodromicPair J H) (t : ℝ) (p :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    loxodromicFlowKleinAction J H h (-t)
        (loxodromicFlowKleinAction J H h t p) = p := by
  have h' := loxodromicFlowKleinAction_add J H h (-t) t p
  have hz : -t + t = (0 : ℝ) := by ring
  rw [hz, loxodromicFlowKleinAction_zero] at h'
  exact h'.symm

theorem ellipticFlowKleinAction_preserves_incidence
    (J : StageTwo) (hJ : IsEllipticGenerator J) (t : ℝ) (p q :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    KleinIncident p q ↔
      KleinIncident (ellipticFlowKleinAction J hJ t p)
        (ellipticFlowKleinAction J hJ t q) := by
  exact stageTwoUnitKleinAction_preserves_incidence
    (ellipticFlowUnit J hJ t) p q

theorem hyperbolicFlowKleinAction_preserves_incidence
    (H : StageTwo) (hH : IsHyperbolicGenerator H) (t : ℝ) (p q :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    KleinIncident p q ↔
      KleinIncident (hyperbolicFlowKleinAction H hH t p)
        (hyperbolicFlowKleinAction H hH t q) := by
  exact stageTwoUnitKleinAction_preserves_incidence
    (hyperbolicFlowUnit H hH t) p q

theorem parabolicFlowKleinAction_preserves_incidence
    (N : StageTwo) (hN : IsParabolicGenerator N) (t : ℝ) (p q :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    KleinIncident p q ↔
      KleinIncident (parabolicFlowKleinAction N hN t p)
        (parabolicFlowKleinAction N hN t q) := by
  exact stageTwoUnitKleinAction_preserves_incidence
    (parabolicFlowUnit N hN t) p q

theorem loxodromicFlowKleinAction_preserves_incidence
    (J H : StageTwo) (h : IsLoxodromicPair J H) (t : ℝ) (p q :
      InfoGeometry.Projective.ExteriorKleinProjective.KleinLocus) :
    KleinIncident p q ↔
      KleinIncident (loxodromicFlowKleinAction J H h t p)
        (loxodromicFlowKleinAction J H h t q) := by
  exact stageTwoUnitKleinAction_preserves_incidence
    (loxodromicFlowUnit J H h t) p q

end InfoGeometry.Clifford.Cl11StageTwoTrifactorGeometry
