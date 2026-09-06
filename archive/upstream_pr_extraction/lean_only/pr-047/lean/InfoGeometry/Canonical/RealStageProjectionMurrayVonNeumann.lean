import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Clifford.Cl11TensorTowerKroneckerRangeRank
import InfoGeometry.Canonical.RealStageEuclideanAction

/-!
# Finite-stage Murray--von Neumann projection data

This owner uses the native real matrix stages and their native star and
algebra-embedding APIs.  It does not claim a `K₀` or `KO₀` identification.
The relation is recorded at a finite stage; classification by range rank is a
separate theorem boundary.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Clifford.Cl11TensorTower

abbrev IsStageProjection (n : ℕ) (p : MatStage n) : Prop :=
  IsIdempotentElem p ∧ star p = p

def MurrayVonNeumannEquivalent {n : ℕ}
    (p q : MatStage n) : Prop :=
  ∃ v : MatStage n, star v * v = p ∧ v * star v = q

noncomputable def rangeMvnEquiv {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V]
    (P Q Vop Wop : V →ₗ[K] V)
    (hWV : Wop.comp Vop = P)
    (hVW : Vop.comp Wop = Q)
    (hP : P.comp P = P)
    (hQ : Q.comp Q = Q) :
    LinearMap.range P ≃ₗ[K] LinearMap.range Q := by
  have hQV : Q.comp Vop = Vop.comp P := by
    calc
      Q.comp Vop = (Vop.comp Wop).comp Vop := by rw [hVW]
      _ = Vop.comp (Wop.comp Vop) := by rw [LinearMap.comp_assoc]
      _ = Vop.comp P := by rw [hWV]
  have hPW : P.comp Wop = Wop.comp Q := by
    calc
      P.comp Wop = (Wop.comp Vop).comp Wop := by rw [hWV]
      _ = Wop.comp (Vop.comp Wop) := by rw [LinearMap.comp_assoc]
      _ = Wop.comp Q := by rw [hVW]
  let forward : LinearMap.range P →ₗ[K] LinearMap.range Q :=
    LinearMap.codRestrict (LinearMap.range Q)
      (Vop.comp (Submodule.subtype (LinearMap.range P))) (by
        intro x
        rcases x.property with ⟨y, hy⟩
        refine ⟨Vop y, ?_⟩
        calc
          Q (Vop y) = Vop (P y) := LinearMap.congr_fun hQV y
          _ = Vop x.1 := congrArg Vop hy)
  let backward : LinearMap.range Q →ₗ[K] LinearMap.range P :=
    LinearMap.codRestrict (LinearMap.range P)
      (Wop.comp (Submodule.subtype (LinearMap.range Q))) (by
        intro x
        rcases x.property with ⟨y, hy⟩
        refine ⟨Wop y, ?_⟩
        calc
          P (Wop y) = Wop (Q y) := LinearMap.congr_fun hPW y
          _ = Wop x.1 := congrArg Wop hy)
  have hP_fix (x : LinearMap.range P) : P x.1 = x.1 := by
    rcases x.property with ⟨y, hy⟩
    calc
      P x.1 = P (P y) := congrArg P hy.symm
      _ = P y := LinearMap.congr_fun hP y
      _ = x.1 := hy
  have hQ_fix (x : LinearMap.range Q) : Q x.1 = x.1 := by
    rcases x.property with ⟨y, hy⟩
    calc
      Q x.1 = Q (Q y) := congrArg Q hy.symm
      _ = Q y := LinearMap.congr_fun hQ y
      _ = x.1 := hy
  exact LinearEquiv.ofBijective forward ⟨
    (by
      intro x y hxy
      apply Subtype.ext
      calc
        x.1 = P x.1 := (hP_fix x).symm
        _ = Wop (Vop x.1) := (LinearMap.congr_fun hWV x.1).symm
        _ = Wop (Vop y.1) := congrArg Wop (congrArg Subtype.val hxy)
        _ = P y.1 := LinearMap.congr_fun hWV y.1
        _ = y.1 := hP_fix y),
    (by
      intro y
      refine ⟨backward y, ?_⟩
      apply Subtype.ext
      calc
        Vop (Wop y.1) = Q y.1 := LinearMap.congr_fun hVW y.1
      _ = y.1 := hQ_fix y)⟩

noncomputable def rangeIsometryOfFinrankEq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {P Q : E →ₗ[ℝ] E}
    (h : Module.finrank ℝ (LinearMap.range P) =
      Module.finrank ℝ (LinearMap.range Q)) :
    LinearMap.range P ≃ₗᵢ[ℝ] LinearMap.range Q := by
  let bP := stdOrthonormalBasis ℝ (LinearMap.range P)
  let bQ := stdOrthonormalBasis ℝ (LinearMap.range Q)
  exact OrthonormalBasis.equiv bP bQ (finCongr h)

noncomputable def partialIsometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {P Q : E →ₗ[ℝ] E}
    (U : LinearMap.range P ≃ₗᵢ[ℝ] LinearMap.range Q) : E →ₗ[ℝ] E :=
  (Submodule.subtype (LinearMap.range Q)).comp
    (U.toLinearMap.comp
      (LinearMap.codRestrict (LinearMap.range P) P (by
        intro x
        exact ⟨x, rfl⟩)))

@[simp] theorem partialIsometry_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {P Q : E →ₗ[ℝ] E}
    (U : LinearMap.range P ≃ₗᵢ[ℝ] LinearMap.range Q) (x : E) :
    partialIsometry U x = U ⟨P x, ⟨x, rfl⟩⟩ := rfl

theorem partialIsometry_adjoint_comp
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {P Q : E →ₗ[ℝ] E}
    (hP : IsStarProjection P)
    (U : LinearMap.range P ≃ₗᵢ[ℝ] LinearMap.range Q) :
    (LinearMap.adjoint (partialIsometry U)).comp
        (partialIsometry U) = P := by
  let V := partialIsometry U
  have hPsp := LinearMap.isStarProjection_iff_isSymmetricProjection.mp hP
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  change inner ℝ y (LinearMap.adjoint V (V x)) = inner ℝ y (P x)
  rw [LinearMap.adjoint_inner_right]
  rw [partialIsometry_apply, partialIsometry_apply]
  change inner ℝ (U ⟨P y, ⟨y, rfl⟩⟩) (U ⟨P x, ⟨x, rfl⟩⟩) =
    inner ℝ y (P x)
  rw [U.inner_map_map]
  change inner ℝ (P y) (P x) = inner ℝ y (P x)
  rw [hPsp.isSymmetric y (P x)]
  exact congrArg (inner ℝ y) (LinearMap.congr_fun hPsp.isIdempotentElem x)

theorem partialIsometry_comp_adjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {P Q : E →ₗ[ℝ] E}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (U : LinearMap.range P ≃ₗᵢ[ℝ] LinearMap.range Q) :
    (partialIsometry U).comp (LinearMap.adjoint (partialIsometry U)) = Q := by
  let V := partialIsometry U
  have hleft : (LinearMap.adjoint V).comp V = P :=
    partialIsometry_adjoint_comp hP U
  have hPsp := LinearMap.isStarProjection_iff_isSymmetricProjection.mp hP
  have hpfix (z : E) : P (P z) = P z :=
    LinearMap.congr_fun hPsp.isIdempotentElem z
  have hPfix_mem (a : LinearMap.range P) : P a.1 = a.1 := by
    rcases a.property with ⟨b, hb⟩
    calc
      P a.1 = P (P b) := congrArg P hb.symm
      _ = P b := hpfix b
      _ = a.1 := hb
  have hVP : V.comp P = V := by
    ext x
    rw [LinearMap.comp_apply, partialIsometry_apply]
    dsimp [V, partialIsometry]
    have hc : (LinearMap.codRestrict (LinearMap.range P) P (by
        intro z
        exact ⟨z, rfl⟩)) x = ⟨P x, ⟨x, rfl⟩⟩ := rfl
    rw [hc]
    have hu : U ⟨P (P x), ⟨P x, rfl⟩⟩ = U ⟨P x, ⟨x, rfl⟩⟩ := by
      congr 1
      apply Subtype.ext
      exact hpfix x
    exact congrArg Subtype.val hu
  have hsym : (V.comp (LinearMap.adjoint V)).IsSymmetric := by
    intro x y
    change inner ℝ (V (LinearMap.adjoint V x)) y =
      inner ℝ x (V (LinearMap.adjoint V y))
    calc
      inner ℝ (V (LinearMap.adjoint V x)) y =
          inner ℝ (LinearMap.adjoint V x) (LinearMap.adjoint V y) :=
        (LinearMap.adjoint_inner_right V (LinearMap.adjoint V x) y).symm
      _ = inner ℝ x (V (LinearMap.adjoint V y)) :=
        LinearMap.adjoint_inner_left V (LinearMap.adjoint V y) x
  have hidem : IsIdempotentElem (V.comp (LinearMap.adjoint V)) := by
    apply LinearMap.ext
    intro x
    change V (LinearMap.adjoint V (V (LinearMap.adjoint V x))) =
      V (LinearMap.adjoint V x)
    change V ((LinearMap.adjoint V).comp V (LinearMap.adjoint V x)) =
      V (LinearMap.adjoint V x)
    rw [hleft]
    exact LinearMap.congr_fun hVP (LinearMap.adjoint V x)
  have hstar : IsStarProjection (V.comp (LinearMap.adjoint V)) :=
    (LinearMap.isStarProjection_iff_isSymmetricProjection).2 ⟨hidem, hsym⟩
  have hVrange : LinearMap.range V = LinearMap.range Q := by
    apply le_antisymm
    · rintro z ⟨x, rfl⟩
      exact (U ⟨P x, ⟨x, rfl⟩⟩).property
    · rintro z ⟨x, hx⟩
      let zq : LinearMap.range Q := ⟨z, ⟨x, hx⟩⟩
      let a : LinearMap.range P := U.symm zq
      refine ⟨a.1, ?_⟩
      dsimp [V, partialIsometry]
      change (U ⟨P a.1, ⟨a.1, rfl⟩⟩ : E) = z
      have hu : U ⟨P a.1, ⟨a.1, rfl⟩⟩ = U a := by
        congr 1
        apply Subtype.ext
        exact hPfix_mem a
      exact (congrArg Subtype.val hu).trans
        (congrArg Subtype.val (U.apply_symm_apply zq))
  have hTrange : LinearMap.range (V.comp (LinearMap.adjoint V)) =
      LinearMap.range V := by
    apply le_antisymm
    · rintro z ⟨x, rfl⟩
      exact ⟨LinearMap.adjoint V x, rfl⟩
    · rintro z ⟨x, rfl⟩
      refine ⟨V x, ?_⟩
      change V (LinearMap.adjoint V (V x)) = V x
      change V ((LinearMap.adjoint V).comp V x) = V x
      rw [hleft]
      exact LinearMap.congr_fun hVP x
  exact LinearMap.IsStarProjection.ext hstar hQ (hTrange.trans hVrange)

theorem exists_partial_isometry_of_finrank_range_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {P Q : E →ₗ[ℝ] E}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (h : Module.finrank ℝ (LinearMap.range P) =
      Module.finrank ℝ (LinearMap.range Q)) :
    ∃ V : E →ₗ[ℝ] E,
      (LinearMap.adjoint V).comp V = P ∧
        V.comp (LinearMap.adjoint V) = Q := by
  let U := rangeIsometryOfFinrankEq h
  exact ⟨partialIsometry U,
    partialIsometry_adjoint_comp hP U,
    partialIsometry_comp_adjoint hP hQ U⟩

theorem stageEuclideanRank_eq_stageRank
    (n : ℕ) (A : MatStage n) :
    Module.finrank ℝ
        (LinearMap.range (stageEuclideanAction n A)) =
      stageRank n A := by
  unfold stageRank stageEuclideanAction
  rw [LinearMap.range_comp, LinearMap.range_comp]
  rw [(stageVectorEquiv n).finrank_map_eq]
  have hrange : LinearMap.range (stageVectorEquiv n).symm.toLinearMap = ⊤ :=
    LinearMap.range_eq_top_of_surjective _ (stageVectorEquiv n).symm.surjective
  rw [hrange, Submodule.map_top]
  rfl

theorem isStarProjection_stageEuclideanAction
    {n : ℕ} {p : MatStage n}
    (hp : IsStageProjection n p) :
    IsStarProjection (stageEuclideanAction n p) := by
  apply (LinearMap.isStarProjection_iff_isSymmetricProjection).2
  constructor
  · change (stageEuclideanAction n p).comp (stageEuclideanAction n p) =
      stageEuclideanAction n p
    rw [← stageEuclideanAction_mul, hp.1]
  · intro x y
    simpa [hp.2] using
      stageEuclideanAction_star_inner n p x y

theorem mvn_of_stageRank_eq {n : ℕ} {p q : MatStage n}
    (hp : IsStageProjection n p)
    (hq : IsStageProjection n q)
    (h : stageRank n p = stageRank n q) :
    MurrayVonNeumannEquivalent p q := by
  let P := stageEuclideanAction n p
  let Q := stageEuclideanAction n q
  have hP : IsStarProjection P := isStarProjection_stageEuclideanAction hp
  have hQ : IsStarProjection Q := isStarProjection_stageEuclideanAction hq
  have hfin : Module.finrank ℝ (LinearMap.range P) =
      Module.finrank ℝ (LinearMap.range Q) := by
    simpa [P, Q, stageEuclideanRank_eq_stageRank] using h
  rcases exists_partial_isometry_of_finrank_range_eq hP hQ hfin with
    ⟨V, hVleft, hVright⟩
  let v : MatStage n := stageMatrixOfEuclideanMap n V
  refine ⟨v, ?_, ?_⟩
  · apply (stageEuclideanAction_injective n)
    rw [stageEuclideanAction_mul, ← stageEuclideanAction_adjoint n v]
    rw [stageEuclideanAction_matrixOfEuclideanMap]
    simpa [v, P] using hVleft
  · apply (stageEuclideanAction_injective n)
    rw [stageEuclideanAction_mul, ← stageEuclideanAction_adjoint n v]
    rw [stageEuclideanAction_matrixOfEuclideanMap]
    simpa [v, Q] using hVright

theorem mvn_implies_stageRank_eq {n : ℕ}
    {p q : MatStage n}
    (hp : IsStageProjection n p)
    (hq : IsStageProjection n q)
    (h : MurrayVonNeumannEquivalent p q) :
    stageRank n p = stageRank n q := by
  rcases h with ⟨v, hvp, hvq⟩
  let P := realStageMatrixAction n p
  let Q := realStageMatrixAction n q
  let Vop := realStageMatrixAction n v
  let Wop := realStageMatrixAction n (star v)
  have hWV : Wop.comp Vop = P := by
    dsimp [Wop, Vop, P]
    rw [← realStageMatrixAction_mul, hvp]
  have hVW : Vop.comp Wop = Q := by
    dsimp [Vop, Wop, Q]
    rw [← realStageMatrixAction_mul, hvq]
  have hP : P.comp P = P := by
    dsimp [P]
    rw [← realStageMatrixAction_mul, hp.1]
  have hQ : Q.comp Q = Q := by
    dsimp [Q]
    rw [← realStageMatrixAction_mul, hq.1]
  exact (rangeMvnEquiv P Q Vop Wop hWV hVW hP hQ).finrank_eq

theorem projection_stageRank_embed {n : ℕ}
    (p : MatStage n)
    (_hp : IsStageProjection n p) :
    stageRank (n + 1) (matStageEmbed n p) = 2 * stageRank n p :=
  stageRank_embed n p

theorem mvn_refl {n : ℕ} {p : MatStage n}
    (hp : IsStageProjection n p) :
    MurrayVonNeumannEquivalent p p := by
  refine ⟨p, ?_, ?_⟩
  · rw [hp.2, hp.1]
  · rw [hp.2, hp.1]

theorem mvn_symm {n : ℕ} {p q : MatStage n}
    (h : MurrayVonNeumannEquivalent p q) :
    MurrayVonNeumannEquivalent q p := by
  rcases h with ⟨v, hvp, hvq⟩
  refine ⟨star v, ?_, ?_⟩
  · simpa using hvq
  · simpa using hvp

theorem mvn_trans {n : ℕ} {p q r : MatStage n}
    (hp : IsStageProjection n p)
    (hr : IsStageProjection n r)
    (hpq : MurrayVonNeumannEquivalent p q)
    (hqr : MurrayVonNeumannEquivalent q r) :
    MurrayVonNeumannEquivalent p r := by
  rcases hpq with ⟨v, hvp, hvq⟩
  rcases hqr with ⟨w, hwq, hwr⟩
  refine ⟨w * v, ?_, ?_⟩
  · calc
      star (w * v) * (w * v) = (star v * star w) * (w * v) := by
        rw [star_mul]
      _ = star v * (star w * w) * v := by
        simp only [mul_assoc]
      _ = star v * q * v := by rw [hwq]
      _ = star v * (v * star v) * v := by rw [hvq]
      _ = (star v * v) * (star v * v) := by
        simp only [mul_assoc]
      _ = p * p := by rw [hvp]
      _ = p := hp.1
  · calc
      (w * v) * star (w * v) = (w * v) * (star v * star w) := by
        rw [star_mul]
      _ = w * (v * star v) * star w := by
        simp only [mul_assoc]
      _ = w * q * star w := by rw [hvq]
      _ = w * (star w * w) * star w := by rw [hwq]
      _ = (w * star w) * (w * star w) := by
        simp only [mul_assoc]
      _ = r * r := by rw [hwr]
      _ = r := hr.1

theorem mvn_stageEmbed {n : ℕ} {p q : MatStage n}
    (h : MurrayVonNeumannEquivalent p q) :
    MurrayVonNeumannEquivalent (stageEmbed n p) (stageEmbed n q) := by
  rcases h with ⟨v, hvp, hvq⟩
  refine ⟨stageEmbed n v, ?_, ?_⟩
  · calc
      star (stageEmbed n v) * stageEmbed n v =
          stageEmbed n (star v) * stageEmbed n v := by
            rw [stageEmbed_star]
      _ = stageEmbed n (star v * v) := by rw [map_mul]
      _ = stageEmbed n p := by rw [hvp]
  · calc
      stageEmbed n v * star (stageEmbed n v) =
          stageEmbed n v * stageEmbed n (star v) := by
            rw [stageEmbed_star]
      _ = stageEmbed n (v * star v) := by rw [map_mul]
      _ = stageEmbed n q := by rw [hvq]

theorem stageProjection_mvn_refl {n : ℕ} {p : MatStage n}
    (hp : IsStageProjection n p) :
    MurrayVonNeumannEquivalent p p := mvn_refl hp

theorem stageProjection_mvn_embed {n : ℕ}
    {p q : MatStage n}
    (h : MurrayVonNeumannEquivalent p q) :
    MurrayVonNeumannEquivalent (stageEmbed n p) (stageEmbed n q) :=
  mvn_stageEmbed h

end InfoGeometry.Canonical
