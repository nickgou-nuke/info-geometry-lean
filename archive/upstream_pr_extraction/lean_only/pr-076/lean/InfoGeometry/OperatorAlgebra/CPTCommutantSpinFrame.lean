import InfoGeometry.OperatorAlgebra.SpectralTriple
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SpectralTriple

theorem realStructure_comp_inv_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H} {signs : KOSigns}
    (J : RealStructure H K signs) (x : H) :
    J.J.val (J.J⁻¹.val x) = x := by
  have h := congrArg (fun T : EndR H => T x) (Units.mul_inv J.J)
  simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using h

theorem realStructure_inv_comp_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H} {signs : KOSigns}
    (J : RealStructure H K signs) (x : H) :
    J.J⁻¹.val (J.J.val x) = x := by
  have h := congrArg (fun T : EndR H => T x) (Units.inv_mul J.J)
  simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using h

/-! The KO sign is the exact bounded-operator two-cycle law.  In particular,
the involutive case is obtained only after supplying `epsJ = 1`; no global
holonomy or mapping-torus claim is implicit here. -/
theorem realStructure_two_cycle_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H} {signs : KOSigns}
    (J : RealStructure H K signs) (x : H) :
    J.J.val (J.J.val x) = signs.epsJ • x := by
  have h := congrArg (fun T : EndR H => T x) J.J_square
  simpa only [ContinuousLinearMap.comp_apply, smul_eq_mul] using h

theorem realStructure_two_cycle_apply_of_epsJ_one
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H} {signs : KOSigns}
    (J : RealStructure H K signs) (hJ : signs.epsJ = 1) (x : H) :
    J.J.val (J.J.val x) = x := by
  rw [realStructure_two_cycle_apply J x, hJ, one_smul]

/-! Operator-star compatibility is conditional: `RepresentedAlgebra` itself
only carries a ring hom, while the real-linear endomorphism carrier acquires
the adjoint star under the stated Hilbert-space hypotheses. -/
noncomputable def operatorAdjoint
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] : EndR H → EndR H :=
  fun T => (ContinuousLinearMap.adjoint :
    (H →L[ℝ] H) → (H →L[ℝ] H)) T

theorem oppositeRep_star_compatibility
    {A H : Type*}
    [Ring A] [StarRing A]
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    {K : PhaseAxis H} {signs : KOSigns}
    (ρ : RepresentedAlgebra A H)
    (J : RealStructure H K signs)
    (hρ : ∀ a : A, ρ.rep (star a) = operatorAdjoint (ρ.rep a))
    (hJ : operatorAdjoint J.J.val = J.J⁻¹.val)
    (a : A) :
    oppositeRep (H := H) ρ J (star a) =
      operatorAdjoint (oppositeRep (H := H) ρ J a) := by
  unfold oppositeRep
  rw [star_involutive a]
  unfold operatorAdjoint at hJ ⊢
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp]
  have hJinv : operatorAdjoint J.J⁻¹.val = J.J.val := by
    unfold operatorAdjoint
    rw [← hJ]
    exact ContinuousLinearMap.adjoint_adjoint J.J.val
  unfold operatorAdjoint at hJinv
  have hρa := hρ a
  unfold operatorAdjoint at hρa
  rw [hJinv, hρa, ContinuousLinearMap.adjoint_adjoint, hJ]
  simp [ContinuousLinearMap.comp_assoc]

theorem oppositeRep_one
    {A H : Type*}
    [Ring A] [StarRing A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (ρ : RepresentedAlgebra A H)
    (J : RealStructure H K signs) :
    oppositeRep ρ J 1 = ContinuousLinearMap.id ℝ H := by
  ext x
  simp only [oppositeRep, star_one, map_one, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.one_apply]
  exact realStructure_comp_inv_apply J x

theorem oppositeRep_mul
    {A H : Type*}
    [Ring A] [StarRing A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (ρ : RepresentedAlgebra A H)
    (J : RealStructure H K signs)
    (a b : A) :
    oppositeRep ρ J (a * b) =
      (oppositeRep ρ J b).comp (oppositeRep ρ J a) := by
  ext x
  simp only [oppositeRep, ContinuousLinearMap.comp_apply, star_mul,
    map_mul, ContinuousLinearMap.mul_apply]
  have h := realStructure_inv_comp_apply J
    ((ρ.rep (star a)) ((↑(J.J⁻¹) : EndR H) x))
  rw [h]

theorem oppositeRep_sub
    {A H : Type*}
    [Ring A] [StarRing A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (ρ : RepresentedAlgebra A H)
    (J : RealStructure H K signs)
    (a b : A) :
    oppositeRep ρ J (a - b) =
      oppositeRep ρ J a - oppositeRep ρ J b := by
  ext x
  simp [oppositeRep, ContinuousLinearMap.comp_apply]

theorem oppositeRep_zero
    {A H : Type*}
    [Ring A] [StarRing A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (ρ : RepresentedAlgebra A H)
    (J : RealStructure H K signs) :
    oppositeRep ρ J 0 = 0 := by
  ext x
  simp [oppositeRep, ContinuousLinearMap.comp_apply]

theorem oppositeRep_add
    {A H : Type*}
    [Ring A] [StarRing A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (ρ : RepresentedAlgebra A H)
    (J : RealStructure H K signs)
    (a b : A) :
    oppositeRep ρ J (a + b) =
      oppositeRep ρ J a + oppositeRep ρ J b := by
  ext x
  simp [oppositeRep, ContinuousLinearMap.comp_apply]

theorem oppositeRep_neg
    {A H : Type*}
    [Ring A] [StarRing A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (ρ : RepresentedAlgebra A H)
    (J : RealStructure H K signs)
    (a : A) :
    oppositeRep ρ J (-a) = -oppositeRep ρ J a := by
  ext x
  simp [oppositeRep, ContinuousLinearMap.comp_apply]

/-- The opposite representation as a genuine representation of `Aᵐᵒᵖ`. -/
def oppositeRepRingHom
    {A H : Type*}
    [Ring A] [StarRing A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (ρ : RepresentedAlgebra A H)
    (J : RealStructure H K signs) :
    Aᵐᵒᵖ →+* EndR H where
  toFun := fun b => oppositeRep ρ J b.unop
  map_one' := by
    exact oppositeRep_one ρ J
  map_mul' := by
    intro a b
    change oppositeRep ρ J (b.unop * a.unop) =
      (oppositeRep ρ J a.unop).comp (oppositeRep ρ J b.unop)
    exact oppositeRep_mul ρ J b.unop a.unop
  map_zero' := by
    exact oppositeRep_zero ρ J
  map_add' := by
    intro a b
    change oppositeRep ρ J (a.unop + b.unop) =
      oppositeRep ρ J a.unop + oppositeRep ρ J b.unop
    exact oppositeRep_add ρ J a.unop b.unop

theorem oppositeRep_comp_realStructure
    {A H : Type*}
    [Ring A] [StarRing A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (ρ : RepresentedAlgebra A H)
    (J : RealStructure H K signs)
    (b : A) :
    (oppositeRep ρ J b).comp J.J.val =
      J.J.val.comp (ρ.rep (star b)) := by
  ext x
  change J.J.val ((ρ.rep (star b)) ((↑(J.J⁻¹) : EndR H) (J.J.val x))) =
    J.J.val ((ρ.rep (star b)) x)
  have h := realStructure_inv_comp_apply J x
  rw [h]

end InfoGeometry.OperatorAlgebra.SpectralTriple
