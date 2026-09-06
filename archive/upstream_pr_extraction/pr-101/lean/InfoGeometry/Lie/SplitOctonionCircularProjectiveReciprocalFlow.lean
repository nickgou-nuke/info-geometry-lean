import InfoGeometry.Lie.SplitOctonionCircularProjectiveNullBoundary
import InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow
import InfoGeometry.Lie.SplitOctonionCircularReciprocalWittBridge
import InfoGeometry.Twistor.ProjectiveNullIsometryIncidence

/-!
# Projectivized reciprocal circular flow

The reciprocal circular flow is already a quadratic isometry on the finite
Witt coordinate carrier.  This file restricts its projectivization to the
projective null boundary using the generic Mathlib-native null-isometry API.
No compactification by `±∞`, topology, or physical-time interpretation is
introduced here.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Lie.SplitOctonionCircularProjectiveReciprocalFlow

open InfoGeometry.Lie.SplitOctonionCircularProjectiveNullBoundary
open InfoGeometry.Lie.SplitOctonionCircularReciprocalWittBridge
open InfoGeometry.Lie.SplitOctonionCircularQuadraticCoherence
open InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow
open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates
open InfoGeometry.Twistor
open InfoGeometry.Twistor.ProjectiveNullIsometryIncidence

abbrev Coord := Fin 8 → ℝ
abbrev CircularNullBoundary := TwistorSpace circularPeirceQuadratic

/-- The projective null ray of a circular coordinate basis vector. -/
noncomputable def circularBasisNullRay (i : Fin 8) : CircularNullBoundary :=
  twistorMk circularPeirceQuadratic (Pi.single i (1 : ℝ)) (by
    intro h
    have hi := congrFun h i
    simpa using hi) (by
    rw [circularPeirceQuadratic_eq_circularWittQuadratic]
    fin_cases i <;> simp [circularWittQuadratic, Pi.single_apply])

/-- The circular hyperbolic flow as an isometry of the transported quadratic form. -/
noncomputable def circularFlowQuadraticIsometry (t : ℝ) :
    circularPeirceQuadratic.IsometryEquiv circularPeirceQuadratic :=
  QuadraticMap.IsometryEquiv.mk (hyperbolicFlowCoordinateEquiv t) (by
    intro x
    rw [circularPeirceQuadratic_eq_circularWittQuadratic,
      circularPeirceQuadratic_eq_circularWittQuadratic]
    exact hyperbolicFlowCoordinate_preserves_circularWittNorm t x)

/-- The reciprocal flow restricted to projective circular null rays. -/
noncomputable def circularNullBoundaryFlow (t : ℝ) :
    CircularNullBoundary ≃ CircularNullBoundary :=
  nullIsometryEquiv (circularFlowQuadraticIsometry t)

theorem circularNullBoundaryFlow_mk
    (t : ℝ) (x : Coord) (hx : x ≠ 0)
    (hQ : circularPeirceQuadratic x = 0) :
    circularNullBoundaryFlow t (twistorMk circularPeirceQuadratic x hx hQ) =
      ⟨Projectivization.mk ℝ (hyperbolicFlowCoordinate t x)
          (by simpa using (hyperbolicFlowCoordinateEquiv t).injective.ne hx),
        by
          rw [isNull_mk_iff]
          rw [circularPeirceQuadratic_eq_circularWittQuadratic]
          rw [circularPeirceQuadratic_eq_circularWittQuadratic] at hQ
          exact (hyperbolicFlowCoordinate_preserves_circularWittNorm t x).trans hQ⟩ := by
  rfl

theorem circularNullBoundaryFlow_mk_axialFlow
    (t : ℝ) (x : Coord) (hx : x ≠ 0)
    (hQ : circularPeirceQuadratic x = 0) :
    circularNullBoundaryFlow t (twistorMk circularPeirceQuadratic x hx hQ) =
      ⟨Projectivization.mk ℝ (axialFlowCoordinate t x)
          (by simpa [axialFlowCoordinate_eq_hyperbolicFlowCoordinate t] using
            (hyperbolicFlowCoordinateEquiv t).injective.ne hx),
        by
          rw [isNull_mk_iff]
          rw [circularPeirceQuadratic_eq_circularWittQuadratic]
          rw [circularPeirceQuadratic_eq_circularWittQuadratic] at hQ
          rw [axialFlowCoordinate_eq_hyperbolicFlowCoordinate t]
          exact (hyperbolicFlowCoordinate_preserves_circularWittNorm t x).trans hQ⟩ := by
  simpa only [axialFlowCoordinate_eq_hyperbolicFlowCoordinate] using
    (circularNullBoundaryFlow_mk t x hx hQ)

@[simp] theorem circularNullBoundaryFlow_zero :
    circularNullBoundaryFlow 0 = Equiv.refl CircularNullBoundary := by
  apply Equiv.ext
  intro p
  apply Subtype.ext
  change projectiveIsometryMap (circularFlowQuadraticIsometry 0) p.1 = p.1
  refine Projectivization.ind (p := p.1) ?_
  intro x hx
  rw [projectiveIsometryMap_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  refine ⟨1, ?_⟩
  change (1 : ℝ) • x = (hyperbolicFlowCoordinateEquiv 0) x
  rw [hyperbolicFlowCoordinateEquiv_apply, hyperbolicFlowCoordinate_zero]
  simp

theorem circularNullBoundaryFlow_add (s t : ℝ) :
    circularNullBoundaryFlow (s + t) =
      (circularNullBoundaryFlow s).trans (circularNullBoundaryFlow t) := by
  apply Equiv.ext
  intro p
  apply Subtype.ext
  dsimp [circularNullBoundaryFlow, nullIsometryEquiv]
  change (nullIsometryMap (circularFlowQuadraticIsometry (s + t)) p).1 =
    (nullIsometryMap (circularFlowQuadraticIsometry t)
      (nullIsometryMap (circularFlowQuadraticIsometry s) p)).1
  change projectiveIsometryMap (circularFlowQuadraticIsometry (s + t)) p.1 =
    projectiveIsometryMap (circularFlowQuadraticIsometry t)
      (projectiveIsometryMap (circularFlowQuadraticIsometry s) p.1)
  refine Projectivization.ind (p := p.1) ?_
  intro x hx
  rw [projectiveIsometryMap_mk, projectiveIsometryMap_mk,
    projectiveIsometryMap_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  refine ⟨1, ?_⟩
  simp only [one_smul]
  change (hyperbolicFlowCoordinateEquiv t)
      ((hyperbolicFlowCoordinateEquiv s) x) =
    (hyperbolicFlowCoordinateEquiv (s + t)) x
  simp only [hyperbolicFlowCoordinateEquiv_apply]
  have h := congrArg (fun f : Coord →ₗ[ℝ] Coord => f x)
    (hyperbolicFlowCoordinate_add t s)
  simp only [LinearMap.comp_apply] at h
  rw [add_comm] at h
  exact h.symm

theorem circularNullBoundaryFlow_neg (t : ℝ) :
    circularNullBoundaryFlow (-t) =
      (circularNullBoundaryFlow t).symm := by
  apply Equiv.ext
  intro p
  apply (circularNullBoundaryFlow t).injective
  rw [Equiv.apply_symm_apply]
  have h := congrArg (fun e : CircularNullBoundary ≃ CircularNullBoundary => e p)
    (circularNullBoundaryFlow_add (-t) t)
  simpa using h.symm

theorem circularNullBoundaryFlow_basis_fixed (t : ℝ) (i : Fin 8) :
    circularNullBoundaryFlow t (circularBasisNullRay i) =
      circularBasisNullRay i := by
  apply Subtype.ext
  change projectiveIsometryMap (circularFlowQuadraticIsometry t)
      (Projectivization.mk ℝ (Pi.single i (1 : ℝ)) _) =
    Projectivization.mk ℝ (Pi.single i (1 : ℝ)) _
  rw [projectiveIsometryMap_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  refine ⟨Units.mk0
      (Real.exp (t * InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight i))
      (Real.exp_ne_zero _), ?_⟩
  change Real.exp
      (t * InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight i) •
      (Pi.single i (1 : ℝ) : Coord) =
    hyperbolicFlowCoordinate t (Pi.single i (1 : ℝ) : Coord)
  rw [hyperbolicFlowCoordinate_basis_action]

/-- Multiplicative packaging of the additive projective-flow parameter. -/
noncomputable def circularNullBoundaryFlowHom :
    Multiplicative ℝ →* Equiv.Perm CircularNullBoundary where
  toFun t := circularNullBoundaryFlow t.toAdd
  map_one' := by
    rw [Equiv.Perm.one_def]
    exact circularNullBoundaryFlow_zero
  map_mul' := by
    intro s t
    apply Equiv.ext
    intro p
    change circularNullBoundaryFlow (s.toAdd + t.toAdd) p =
      (circularNullBoundaryFlow s.toAdd *
        circularNullBoundaryFlow t.toAdd) p
    rw [Equiv.Perm.mul_apply]
    have h := congrArg
      (fun e : CircularNullBoundary ≃ CircularNullBoundary => e p)
      (circularNullBoundaryFlow_add t.toAdd s.toAdd)
    simpa [add_comm] using h

end InfoGeometry.Lie.SplitOctonionCircularProjectiveReciprocalFlow
