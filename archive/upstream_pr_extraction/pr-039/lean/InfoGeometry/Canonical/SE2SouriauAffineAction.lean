import InfoGeometry.Canonical.SE2SouriauAction

/-!
# The affine `SE(2)` action on Euclidean points

This is the ordinary affine chart of the homogeneous matrix action: the
rotation block acts linearly and the last two coordinates provide translation.
-/

namespace InfoGeometry.Canonical.SE2SouriauCocycle

open InfoGeometry.Canonical.Barbaresco2020Souriau

def homogeneousLift (v : Point2) : HomogeneousPoint :=
  ![v.1, v.2, 1]

def affineChart : Set HomogeneousPoint :=
  {x | x 2 = 1}

theorem continuous_homogeneousLift : Continuous homogeneousLift := by
  unfold homogeneousLift
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem homogeneousLift_injective : Function.Injective homogeneousLift := by
  intro v w h
  apply Prod.ext
  · exact congrFun h 0
  · exact congrFun h 1

theorem homogeneousLift_range :
    Set.range homogeneousLift = affineChart := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    simp [affineChart, homogeneousLift]
  · intro hx
    refine ⟨(x 0, x 1), ?_⟩
    funext i
    fin_cases i
    · simp [homogeneousLift]
    · simp [homogeneousLift]
    · simpa [homogeneousLift, affineChart] using hx.symm

theorem isClosed_affineChart : IsClosed affineChart := by
  unfold affineChart
  exact isClosed_singleton.preimage (continuous_apply 2)

theorem isClosed_homogeneousLift_range :
    IsClosed (Set.range homogeneousLift) := by
  rw [homogeneousLift_range]
  exact isClosed_affineChart

def affineChartHomeomorph : Point2 ≃ₜ affineChart where
  toFun := fun v =>
    ⟨homogeneousLift v, by
      simp [affineChart, homogeneousLift]⟩
  invFun := fun x => (x.1 0, x.1 1)
  left_inv := by
    intro v
    ext <;> rfl
  right_inv := by
    intro x
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact x.2.symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_homogeneousLift
  continuous_invFun := by
    change Continuous (fun x : affineChart => (x.1 0, x.1 1))
    exact (continuous_apply 0).prodMk (continuous_apply 1) |>.comp
      continuous_subtype_val

theorem se2MatrixAction_mapsTo_affineChart
    (g : SE2RotationCarrier) :
    Set.MapsTo (se2MatrixAction g) affineChart affineChart := by
  intro x hx
  change (se2MatrixAction g x) 2 = 1
  simpa [se2MatrixAction, se2MatrixRepresentation, se2GroupMatrix,
    affineChart, Matrix.mulVec] using hx

theorem se2MatrixAction_affineChart_image
    (g : SE2RotationCarrier) :
    Set.image (se2MatrixAction g) affineChart = affineChart := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact se2MatrixAction_mapsTo_affineChart g hx
  · intro y hy
    refine ⟨se2MatrixAction g⁻¹ y,
      se2MatrixAction_mapsTo_affineChart g⁻¹ hy, ?_⟩
    rw [← se2MatrixAction_mul]
    rw [mul_inv_cancel, se2MatrixAction_one]

def affineChartAction (g : SE2RotationCarrier) :
    affineChart → affineChart := fun x =>
  ⟨se2MatrixAction g x.1,
    se2MatrixAction_mapsTo_affineChart g x.2⟩

theorem continuous_affineChartAction (g : SE2RotationCarrier) :
    Continuous (affineChartAction g) := by
  apply Continuous.subtype_mk
  exact continuous_se2MatrixAction.comp
    (continuous_const.prodMk continuous_subtype_val)

def affineChartActionHomeomorph (g : SE2RotationCarrier) :
    affineChart ≃ₜ affineChart where
  toFun := affineChartAction g
  invFun := affineChartAction g⁻¹
  left_inv := by
    intro x
    apply Subtype.ext
    change se2MatrixAction g⁻¹ (se2MatrixAction g x.1) = x.1
    rw [← se2MatrixAction_mul, inv_mul_cancel, se2MatrixAction_one]
  right_inv := by
    intro x
    apply Subtype.ext
    change se2MatrixAction g (se2MatrixAction g⁻¹ x.1) = x.1
    rw [← se2MatrixAction_mul, mul_inv_cancel, se2MatrixAction_one]
  continuous_toFun := continuous_affineChartAction g
  continuous_invFun := continuous_affineChartAction g⁻¹

theorem affineChartActionHomeomorph_apply_mul
    (g h : SE2RotationCarrier) (x : affineChart) :
    affineChartActionHomeomorph (g * h) x =
      affineChartActionHomeomorph g (affineChartActionHomeomorph h x) := by
  apply Subtype.ext
  change se2MatrixAction (g * h) x.1 =
    se2MatrixAction g (se2MatrixAction h x.1)
  exact se2MatrixAction_mul g h x.1

theorem affineChartActionHomeomorph_one :
    affineChartActionHomeomorph (1 : SE2RotationCarrier) =
      Homeomorph.refl affineChart := by
  apply Homeomorph.ext
  intro x
  apply Subtype.ext
  change se2MatrixAction (1 : SE2RotationCarrier) x.1 = x.1
  exact se2MatrixAction_one x.1

def affinePointAction (g : SE2RotationCarrier) (v : Point2) : Point2 :=
  (g.1.1 * v.1 - g.1.2.1 * v.2 + g.1.2.2.1,
    g.1.2.1 * v.1 + g.1.1 * v.2 + g.1.2.2.2)

theorem se2MatrixAction_homogeneousLift
    (g : SE2RotationCarrier) (v : Point2) :
    se2MatrixAction g (homogeneousLift v) =
      homogeneousLift (affinePointAction g v) := by
  funext i
  fin_cases i <;>
    simp [se2MatrixAction, se2MatrixRepresentation, se2GroupMatrix,
      homogeneousLift, affinePointAction, Matrix.mulVec] <;>
    ring

theorem affinePointAction_one (v : Point2) :
    affinePointAction (1 : SE2RotationCarrier) v = v := by
  change affinePointAction rotationCarrierIdentity v = v
  ext <;> dsimp [affinePointAction, rotationCarrierIdentity,
    se2ParameterIdentity] <;> ring

theorem affinePointAction_mul
    (g h : SE2RotationCarrier) (v : Point2) :
    affinePointAction (g * h) v =
      affinePointAction g (affinePointAction h v) := by
  change affinePointAction (rotationCarrierProduct g h) v =
    affinePointAction g (affinePointAction h v)
  ext <;> dsimp [affinePointAction, rotationCarrierProduct,
    left_se2ParameterTranslation, se2ParameterProduct] <;> ring

instance : MulAction SE2RotationCarrier Point2 where
  smul := affinePointAction
  one_smul := affinePointAction_one
  mul_smul := affinePointAction_mul

theorem affineChartHomeomorph_equivariant
    (g : SE2RotationCarrier) (v : Point2) :
    affineChartHomeomorph (g • v) =
      affineChartActionHomeomorph g (affineChartHomeomorph v) := by
  apply Subtype.ext
  change homogeneousLift (affinePointAction g v) =
    se2MatrixAction g (homogeneousLift v)
  exact (se2MatrixAction_homogeneousLift g v).symm

theorem continuous_affinePointAction :
    Continuous (fun p : SE2RotationCarrier × Point2 => p.1 • p.2) := by
  change Continuous (fun p : SE2RotationCarrier × Point2 =>
    (p.1.1.1 * p.2.1 - p.1.1.2.1 * p.2.2 + p.1.1.2.2.1,
      p.1.1.2.1 * p.2.1 + p.1.1.1 * p.2.2 + p.1.1.2.2.2))
  fun_prop

instance : ContinuousSMul SE2RotationCarrier Point2 where
  continuous_smul := continuous_affinePointAction

theorem continuous_affinePointAction_fixed (g : SE2RotationCarrier) :
    Continuous (affinePointAction g) := by
  unfold affinePointAction
  fun_prop

def affinePointActionHomeomorph (g : SE2RotationCarrier) :
    Point2 ≃ₜ Point2 where
  toFun := affinePointAction g
  invFun := affinePointAction g⁻¹
  left_inv := by
    intro v
    rw [← affinePointAction_mul, inv_mul_cancel, affinePointAction_one]
  right_inv := by
    intro v
    rw [← affinePointAction_mul, mul_inv_cancel, affinePointAction_one]
  continuous_toFun := continuous_affinePointAction_fixed g
  continuous_invFun := continuous_affinePointAction_fixed g⁻¹

theorem affinePointActionHomeomorph_apply_mul
    (g h : SE2RotationCarrier) (v : Point2) :
    affinePointActionHomeomorph (g * h) v =
      affinePointActionHomeomorph g (affinePointActionHomeomorph h v) := by
  exact affinePointAction_mul g h v

theorem affinePointActionHomeomorph_one :
    affinePointActionHomeomorph (1 : SE2RotationCarrier) =
      Homeomorph.refl Point2 := by
  apply Homeomorph.ext
  intro v
  exact affinePointAction_one v

def affineOrbitMap (v : Point2) :
    SE2RotationCarrier → Point2 := fun g => g • v

theorem homogeneousLift_affineOrbitMap
    (v : Point2) :
    homogeneousLift ∘ affineOrbitMap v =
      homogeneousOrbitMap (homogeneousLift v) := by
  funext g
  change homogeneousLift (affinePointAction g v) =
    se2MatrixAction g (homogeneousLift v)
  exact (se2MatrixAction_homogeneousLift g v).symm

theorem continuous_affineOrbitMap (v : Point2) :
    Continuous (affineOrbitMap v) := by
  unfold affineOrbitMap
  simpa only [Function.comp_apply] using
    continuous_affinePointAction.comp (continuous_id.prodMk continuous_const)

def affineOrbitContinuousMap (v : Point2) :
    C(SE2RotationCarrier, Point2) :=
  { toFun := affineOrbitMap v
    continuous_toFun := continuous_affineOrbitMap v }

theorem affineOrbitContinuousMap_apply
    (v : Point2) (g : SE2RotationCarrier) :
    affineOrbitContinuousMap v g = affineOrbitMap v g := rfl

def affineOrbit (v : Point2) : Set Point2 := Set.range (affineOrbitMap v)

theorem affineOrbit_nonempty (v : Point2) :
    (affineOrbit v).Nonempty := by
  exact ⟨v, ⟨1, one_smul SE2RotationCarrier v⟩⟩

def translationCarrier (p : Point2) : SE2RotationCarrier :=
  ⟨(1, 0, p.1, p.2), by
    norm_num [se2RotationParameters, rotationConstraint]
  ⟩

theorem affinePointAction_translationCarrier (p v : Point2) :
    affinePointAction (translationCarrier p) v =
      (v.1 + p.1, v.2 + p.2) := by
  ext <;> dsimp [affinePointAction, translationCarrier]
  · ring
  · ring

def affineOrbitSection (v : Point2) :
    Point2 → SE2RotationCarrier := fun w =>
      translationCarrier (w.1 - v.1, w.2 - v.2)

theorem continuous_affineOrbitSection (v : Point2) :
    Continuous (affineOrbitSection v) := by
  unfold affineOrbitSection translationCarrier
  apply Continuous.subtype_mk
  fun_prop

theorem affineOrbitMap_section (v w : Point2) :
    affineOrbitMap v (affineOrbitSection v w) = w := by
  unfold affineOrbitMap affineOrbitSection
  change affinePointAction (translationCarrier (w.1 - v.1, w.2 - v.2)) v = w
  rw [affinePointAction_translationCarrier]
  ext <;> dsimp <;> ring

theorem affineOrbitMap_surjective (v : Point2) :
    Function.Surjective (affineOrbitMap v) := by
  intro w
  exact ⟨affineOrbitSection v w, affineOrbitMap_section v w⟩

theorem isEmbedding_affineOrbitSection (v : Point2) :
    Topology.IsEmbedding (affineOrbitSection v) := by
  have hleft : Function.LeftInverse (affineOrbitMap v)
      (affineOrbitSection v) := by
    intro w
    exact affineOrbitMap_section v w
  exact hleft.isEmbedding (continuous_affineOrbitMap v)
    (continuous_affineOrbitSection v)

theorem isClosedEmbedding_affineOrbitSection (v : Point2) :
    Topology.IsClosedEmbedding (affineOrbitSection v) := by
  have hleft : Function.LeftInverse (affineOrbitMap v)
      (affineOrbitSection v) := by
    intro w
    exact affineOrbitMap_section v w
  exact hleft.isClosedEmbedding (continuous_affineOrbitMap v)
    (continuous_affineOrbitSection v)

theorem isClosedMap_affineOrbitSection (v : Point2) :
    IsClosedMap (affineOrbitSection v) := by
  exact (isClosedEmbedding_affineOrbitSection v).isClosedMap

theorem isProperMap_affineOrbitSection (v : Point2) :
    IsProperMap (affineOrbitSection v) := by
  exact (isClosedEmbedding_affineOrbitSection v).isProperMap

def affineOrbitContinuousSection (v : Point2) :
    C(Point2, SE2RotationCarrier) :=
  { toFun := affineOrbitSection v
    continuous_toFun := continuous_affineOrbitSection v }

theorem affineOrbitContinuousSection_apply (v w : Point2) :
    affineOrbitContinuousSection v w = affineOrbitSection v w := rfl

theorem affineOrbitContinuousMap_comp_section (v : Point2) :
    (affineOrbitContinuousMap v).comp
        (affineOrbitContinuousSection v) =
      ContinuousMap.id Point2 := by
  apply ContinuousMap.ext
  intro w
  rw [ContinuousMap.comp_apply, ContinuousMap.id_apply,
    affineOrbitContinuousMap_apply,
    affineOrbitContinuousSection_apply]
  exact affineOrbitMap_section v w

theorem affineOrbit_eq_univ (v : Point2) :
    affineOrbit v = Set.univ := by
  apply Set.eq_univ_of_forall
  intro w
  let p : Point2 := (w.1 - v.1, w.2 - v.2)
  have htranslate : affinePointAction (translationCarrier p) v = w := by
    rw [affinePointAction_translationCarrier]
    dsimp [p]
    ext <;> ring
  exact ⟨translationCarrier p, htranslate⟩

def affineOrbitSetoid : Setoid Point2 where
  r v w := affineOrbit v = affineOrbit w
  iseqv := {
    refl := by intro v; rfl
    symm := by intro v w h; exact h.symm
    trans := by intro u v w huv hvw; exact huv.trans hvw }

theorem affineOrbitSetoid_rel_universal (v w : Point2) :
    affineOrbitSetoid.r v w := by
  change affineOrbit v = affineOrbit w
  rw [affineOrbit_eq_univ, affineOrbit_eq_univ]

def affineOrbitQuotientEquivPUnit :
    Quotient affineOrbitSetoid ≃ PUnit where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => Quotient.mk'' (0, 0)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h v =>
        apply Quotient.sound
        exact affineOrbitSetoid_rel_universal (0, 0) v
  right_inv := by
    intro u
    cases u
    rfl

noncomputable def affineOrbitQuotientHomeomorph :
    Quotient affineOrbitSetoid ≃ₜ PUnit where
  toFun := affineOrbitQuotientEquivPUnit
  invFun := affineOrbitQuotientEquivPUnit.symm
  left_inv := affineOrbitQuotientEquivPUnit.left_inv
  right_inv := affineOrbitQuotientEquivPUnit.right_inv
  continuous_toFun := continuous_const
  continuous_invFun := by
    change Continuous (fun _ : PUnit => Quotient.mk'' (0, 0))
    fun_prop

theorem isClosed_affineOrbitSetoid_relation :
    IsClosed {p : Point2 × Point2 | affineOrbitSetoid.r p.1 p.2} := by
  rw [show {p : Point2 × Point2 | affineOrbitSetoid.r p.1 p.2} = Set.univ by
    apply Set.eq_univ_of_forall
    intro p
    exact affineOrbitSetoid_rel_universal p.1 p.2]
  exact isClosed_univ

theorem isCompact_affineOrbitQuotient_univ :
    IsCompact (Set.univ : Set (Quotient affineOrbitSetoid)) := by
  let h : Quotient affineOrbitSetoid ≃ₜ PUnit.{1} :=
    affineOrbitQuotientHomeomorph
  have hc : IsCompact (h.symm '' (Set.univ : Set PUnit.{1})) :=
    isCompact_univ.image h.symm.continuous
  rw [Set.image_univ] at hc
  rw [h.symm.surjective.range_eq] at hc
  exact hc

theorem pathConnectedSpace_affineOrbitQuotient :
    PathConnectedSpace (Quotient affineOrbitSetoid) := by
  let h : Quotient affineOrbitSetoid ≃ₜ PUnit.{1} :=
    affineOrbitQuotientHomeomorph
  exact h.symm.surjective.pathConnectedSpace h.symm.continuous_toFun

theorem isPathConnected_affineOrbitQuotient_univ :
    IsPathConnected (Set.univ : Set (Quotient affineOrbitSetoid)) := by
  letI := pathConnectedSpace_affineOrbitQuotient
  exact isPathConnected_univ

theorem isConnected_affineOrbitQuotient_univ :
    IsConnected (Set.univ : Set (Quotient affineOrbitSetoid)) :=
  (isPathConnected_affineOrbitQuotient_univ).isConnected

theorem t2Space_affineOrbitQuotient :
    T2Space (Quotient affineOrbitSetoid) := by
  let h : Quotient affineOrbitSetoid ≃ₜ PUnit.{1} :=
    affineOrbitQuotientHomeomorph
  exact h.symm.t2Space

theorem locallyCompactSpace_affineOrbitQuotient :
    LocallyCompactSpace (Quotient affineOrbitSetoid) := by
  let h : Quotient affineOrbitSetoid ≃ₜ PUnit.{1} :=
    affineOrbitQuotientHomeomorph
  exact h.isClosedEmbedding.locallyCompactSpace

theorem isQuotientMap_affineOrbitQuotientHomeomorph :
    Topology.IsQuotientMap (affineOrbitQuotientHomeomorph :
      Quotient affineOrbitSetoid → PUnit.{1}) := by
  exact affineOrbitQuotientHomeomorph.isQuotientMap

theorem homogeneousOrbit_eq_affineChart (v : Point2) :
    homogeneousOrbit (homogeneousLift v) = affineChart := by
  apply Set.Subset.antisymm
  · rintro x ⟨g, rfl⟩
    exact se2MatrixAction_mapsTo_affineChart g
      (by simp [affineChart, homogeneousLift])
  · intro x hx
    have hxrange : x ∈ Set.range homogeneousLift := by
      rw [homogeneousLift_range]
      exact hx
    rcases hxrange with ⟨w, rfl⟩
    have hw : w ∈ affineOrbit v := by
      rw [affineOrbit_eq_univ]
      trivial
    rcases hw with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    change se2MatrixAction g (homogeneousLift v) = homogeneousLift w
    rw [se2MatrixAction_homogeneousLift]
    change affinePointAction g v = w at hg
    exact congrArg homogeneousLift hg

theorem affineOrbitMap_mul (v : Point2)
    (g h : SE2RotationCarrier) :
    affineOrbitMap v (g * h) =
      affineOrbitMap (affineOrbitMap v h) g := by
  simp [affineOrbitMap, mul_smul]

end InfoGeometry.Canonical.SE2SouriauCocycle
