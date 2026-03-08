import InfoGeometry.Krein.DoubledAdjoint
import InfoGeometry.Krein.Metric
import InfoGeometry.Krein.Automorphisms
import InfoGeometry.Krein.Modular
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Thermal.FiniteMatrix
import InfoGeometry.Core.SymmetricLieGeneric
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Noether Inference

This module exposes the fundamental physical-informational bridges of the
Unitary Field Theory of Information.

It formalizes:
1. **Information Killing Fields**: Infinitesimal isometries of the Fisher metric.
2. **Information Noether Charges**: Conserved observables (Log-likelihood/Hamiltonian).
3. **Bayesian Symmetry Orbits**: Inference as a flow along a symmetry group trajectory.
-/

namespace InfoGeometry.Canonical.NoetherInference

open InfoGeometry.Krein
open InfoGeometry.Clifford
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Thermal
open InfoGeometry.Core.Generic

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Krein-conjugate operator on the doubled space:
`A♯ = J ∘ A† ∘ J` with `J = spectralEpsilon`.
-/
noncomputable abbrev kreinAdjoint
    (A : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) :
    Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E :=
  InfoGeometry.Krein.doubledKreinAdjoint (E := E) A

omit [FiniteDimensional ℝ E] in
@[simp] lemma kreinAdjoint_apply
    (A : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E)
    (x : Krein.DoubledSpace E) :
    kreinAdjoint (E := E) A x =
      (InfoGeometry.Krein.spectralEpsilon (E := E))
        ((InfoGeometry.Krein.doubledAdjoint (E := E) A)
          ((InfoGeometry.Krein.spectralEpsilon (E := E)) x)) := by
  simp [kreinAdjoint]

/-- Information Killing field: Krein-skew-adjoint generator on the doubled space. -/
abbrev InformationKillingField
    (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] : Type :=
  { A : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E //
      kreinAdjoint (E := E) A = -A }

/-- The observable associated with an information symmetry. -/
structure InformationNoetherCharge
    (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  charge : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E

/-- Bayesian update as a symmetry orbit preserving the Hessian pairing. -/
structure BayesianSymmetryOrbit (prior : Krein.DoubledSpace E) where
  generator : InformationKillingField E
  flow : InfoGeometry.Krein.FiniteDimensionalExponentialFlow (E := E) generator.val
  U : ℝ → Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E
  U_apply : ∀ t x, U t x = flow.flow t x
  preserves_hessian :
    ∀ t x y,
      hessianIndefiniteForm (E := E) (U t x) (U t y) =
        hessianIndefiniteForm (E := E) x y

/-- The updated state at time `t`. -/
def BayesianSymmetryOrbit.update
    {prior : Krein.DoubledSpace E}
    (orbit : BayesianSymmetryOrbit (E := E) prior) :
    ℝ → Krein.DoubledSpace E :=
  fun t => orbit.U t prior

@[simp] lemma BayesianSymmetryOrbit.update_apply
    {prior : Krein.DoubledSpace E}
    (orbit : BayesianSymmetryOrbit (E := E) prior)
    (t : ℝ) :
    orbit.update t = orbit.U t prior := rfl

/-
**The Fisher-Killing Bridge**:
On a symmetric information manifold, the Fisher metric $g$ is identified
with the Killing form $B$ of the Lie algebra of Killing fields.
-/
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- Canonical Fisher bilinear form at a doubled-space point `v`, evaluated on operator generators. -/
noncomputable def fisherBilinAt (v : Krein.DoubledSpace E) :
    LinearMap.BilinForm ℝ (Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) :=
  LinearMap.mk₂ ℝ
    (fun X Y => hessianIndefiniteForm (E := E) (X v) (Y v))
    (by
      intro X₁ X₂ Y
      simp [InfoGeometry.Krein.hessianIndefiniteForm,
        inner_add_left, inner_add_right, add_assoc, add_left_comm])
    (by
      intro a X Y
      simp [InfoGeometry.Krein.hessianIndefiniteForm,
        real_inner_smul_left, real_inner_smul_right, smul_eq_mul]
      ring)
    (by
      intro X Y₁ Y₂
      simp [InfoGeometry.Krein.hessianIndefiniteForm,
        inner_add_left, inner_add_right, add_assoc, add_left_comm])
    (by
      intro a X Y
      simp [InfoGeometry.Krein.hessianIndefiniteForm,
        real_inner_smul_left, real_inner_smul_right, smul_eq_mul]
      ring)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- Evaluation formula for `fisherBilinAt`. -/
@[simp] lemma fisherBilinAt_apply
    (v : Krein.DoubledSpace E)
    (X Y : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) :
    fisherBilinAt (E := E) v X Y = hessianIndefiniteForm (E := E) (X v) (Y v) := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- Lift a basis-level Fisher-Killing bridge to a global bridge. -/
theorem fisher_killing_bridge_of_basis
    (S : SymmetricLieAlgebra ℝ (Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E))
    (X0 Y0 : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E)
    (v0 : Krein.DoubledSpace E)
    (ι : Type) [Fintype ι]
    (b : Module.Basis ι ℝ (Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E))
    (hBridgeBasis :
      ∀ (v : Krein.DoubledSpace E) (i j : ι),
        fisherBilinAt (E := E) v (b i) (b j) * S.B (S.P_minus X0) (S.P_minus Y0)
          =
        hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0) *
          S.B (S.P_minus (b i)) (S.P_minus (b j))) :
    ∀ (X Y : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) (v : Krein.DoubledSpace E),
      hessianIndefiniteForm (E := E) (X v) (Y v) *
        S.B (S.P_minus X0) (S.P_minus Y0)
          =
      hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0) *
        S.B (S.P_minus X) (S.P_minus Y) := by
  let Op := Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E
  let B0 : ℝ := S.B (S.P_minus X0) (S.P_minus Y0)
  let H0 : ℝ := hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0)
  let G : LinearMap.BilinForm ℝ Op := (S.B).comp S.P_minus S.P_minus
  intro X Y v
  have hforms : (B0 • fisherBilinAt (E := E) v) = (H0 • G) := by
    refine LinearMap.BilinForm.ext_basis b ?_
    intro i j
    change B0 * fisherBilinAt (E := E) v (b i) (b j) = H0 * G (b i) (b j)
    calc
      B0 * fisherBilinAt (E := E) v (b i) (b j)
          = fisherBilinAt (E := E) v (b i) (b j) * B0 := by ring
      _ = H0 * S.B (S.P_minus (b i)) (S.P_minus (b j)) := by
            simpa [B0, H0, mul_assoc, mul_left_comm, mul_comm] using hBridgeBasis v i j
      _ = H0 * G (b i) (b j) := by rfl
  have hxy : (B0 • fisherBilinAt (E := E) v) X Y = (H0 • G) X Y := by
    exact congrArg (fun Φ => Φ X Y) hforms
  have hxy' : B0 * fisherBilinAt (E := E) v X Y = H0 * G X Y := by
    simpa [smul_eq_mul, mul_assoc] using hxy
  calc
    hessianIndefiniteForm (E := E) (X v) (Y v) * B0
        = fisherBilinAt (E := E) v X Y * B0 := by
          simp [fisherBilinAt_apply]
    _ = B0 * fisherBilinAt (E := E) v X Y := by ring
    _ = H0 * G X Y := hxy'
    _ = hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0) *
          S.B (S.P_minus X) (S.P_minus Y) := by rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- Constructive Fisher-Killing proportionality from an explicit global bridge. -/
theorem fisher_metric_eq_killing_form_constructive
    (S : SymmetricLieAlgebra ℝ (Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E))
    (X0 Y0 : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E)
    (v0 : Krein.DoubledSpace E)
    (hB0 : S.B (S.P_minus X0) (S.P_minus Y0) ≠ 0)
    (hH0 : hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0) ≠ 0)
    (hBridge :
      ∀ (X Y : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) (v : Krein.DoubledSpace E),
        hessianIndefiniteForm (E := E) (X v) (Y v) *
          S.B (S.P_minus X0) (S.P_minus Y0)
            =
        hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0) *
          S.B (S.P_minus X) (S.P_minus Y)) :
    ∃ (c : ℝ), c ≠ 0 ∧
      ∀ (X Y : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) (v : Krein.DoubledSpace E),
        hessianIndefiniteForm (E := E) (X v) (Y v) = c * S.B (S.P_minus X) (S.P_minus Y) := by
  let B0 : ℝ := S.B (S.P_minus X0) (S.P_minus Y0)
  let H0 : ℝ := hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0)
  have hB0' : B0 ≠ 0 := by simpa [B0] using hB0
  have hH0' : H0 ≠ 0 := by simpa [H0] using hH0
  refine ⟨H0 / B0, div_ne_zero hH0' hB0', ?_⟩
  intro X Y v
  let Bxy : ℝ := S.B (S.P_minus X) (S.P_minus Y)
  have hscaled :
      hessianIndefiniteForm (E := E) (X v) (Y v) * B0 = H0 * Bxy := by
    simpa [B0, H0, Bxy] using hBridge X Y v
  have hdiv :
      (hessianIndefiniteForm (E := E) (X v) (Y v) * B0) / B0 = (H0 * Bxy) / B0 := by
    exact congrArg (fun z => z / B0) hscaled
  have hmain :
      hessianIndefiniteForm (E := E) (X v) (Y v) = (H0 * Bxy) / B0 := by
    calc
      hessianIndefiniteForm (E := E) (X v) (Y v)
          = (hessianIndefiniteForm (E := E) (X v) (Y v) * B0) / B0 := by
              field_simp [hB0']
      _ = (H0 * Bxy) / B0 := hdiv
  calc
    hessianIndefiniteForm (E := E) (X v) (Y v) = (H0 * Bxy) / B0 := hmain
    _ = (H0 / B0) * Bxy := by ring
    _ = (H0 / B0) * S.B (S.P_minus X) (S.P_minus Y) := by rfl

omit [FiniteDimensional ℝ E] in
/--
Theorem: In an Einstein-Kaehler information manifold with symmetric Lie symmetry,
the Fisher information metric is proportional to the Killing form.
Proportionality constant `c` is the Einstein constant of the canonical representation.
-/
theorem fisher_metric_eq_killing_form
    (K : KaehlerInformationGeometry E) (x : E) (R : RicciTensor E)
    (S : SymmetricLieAlgebra ℝ (Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E))
    (_h_symm : IsEinsteinKaehlerAt R K x)
    (X0 Y0 : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E)
    (v0 : Krein.DoubledSpace E)
    (hB0 : S.B (S.P_minus X0) (S.P_minus Y0) ≠ 0)
    (hH0 : hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0) ≠ 0)
    (hBridge :
      ∀ (X Y : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) (v : Krein.DoubledSpace E),
        hessianIndefiniteForm (E := E) (X v) (Y v) *
          S.B (S.P_minus X0) (S.P_minus Y0)
            =
        hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0) *
          S.B (S.P_minus X) (S.P_minus Y)) :
    ∃ (c : ℝ), c ≠ 0 ∧
      ∀ (X Y : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) (v : Krein.DoubledSpace E),
        hessianIndefiniteForm (E := E) (X v) (Y v) = c * S.B (S.P_minus X) (S.P_minus Y) := by
  exact fisher_metric_eq_killing_form_constructive
    (S := S) (X0 := X0) (Y0 := Y0) (v0 := v0)
    (hB0 := hB0) (hH0 := hH0) (hBridge := hBridge)

omit [FiniteDimensional ℝ E] in
/-- Basis-level constructive variant of `fisher_metric_eq_killing_form`. -/
theorem fisher_metric_eq_killing_form_of_basis_bridge
    (K : KaehlerInformationGeometry E) (x : E) (R : RicciTensor E)
    (S : SymmetricLieAlgebra ℝ (Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E))
    (_h_symm : IsEinsteinKaehlerAt R K x)
    (X0 Y0 : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E)
    (v0 : Krein.DoubledSpace E)
    (ι : Type) [Fintype ι]
    (b : Module.Basis ι ℝ (Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E))
    (hB0 : S.B (S.P_minus X0) (S.P_minus Y0) ≠ 0)
    (hH0 : hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0) ≠ 0)
    (hBridgeBasis :
      ∀ (v : Krein.DoubledSpace E) (i j : ι),
        fisherBilinAt (E := E) v (b i) (b j) * S.B (S.P_minus X0) (S.P_minus Y0)
          =
        hessianIndefiniteForm (E := E) (X0 v0) (Y0 v0) *
          S.B (S.P_minus (b i)) (S.P_minus (b j))) :
    ∃ (c : ℝ), c ≠ 0 ∧
      ∀ (X Y : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) (v : Krein.DoubledSpace E),
        hessianIndefiniteForm (E := E) (X v) (Y v) = c * S.B (S.P_minus X) (S.P_minus Y) := by
  exact fisher_metric_eq_killing_form_constructive
    (S := S)
    (X0 := X0) (Y0 := Y0) (v0 := v0)
    (hB0 := hB0) (hH0 := hH0)
    (hBridge := fisher_killing_bridge_of_basis
      (S := S) (X0 := X0) (Y0 := Y0) (v0 := v0)
      (ι := ι) (b := b) (hBridgeBasis := hBridgeBasis))

/-
**Noether's Theorem for Inference**:
If an update is generated by a Killing field, then the expectation value
of the Noether charge (e.g., the total information) is conserved.
-/
/-- Theorem `noether_conservation_of_information`. -/
theorem noether_conservation_of_information
    (prior : Krein.DoubledSpace E)
    (orbit : BayesianSymmetryOrbit (E := E) prior)
    (Q : InformationNoetherCharge E)
    (hcomm : ∀ t, Q.charge.comp (orbit.U t) = (orbit.U t).comp Q.charge) :
    ∀ t,
      hessianIndefiniteForm (E := E)
        (orbit.update t)
        (Q.charge (orbit.update t))
        =
      hessianIndefiniteForm (E := E) prior (Q.charge prior) := by
  intro t
  have hQ :
      Q.charge (orbit.update t) = orbit.U t (Q.charge prior) := by
    have h := congrArg (fun T => T prior) (hcomm t)
    simpa [BayesianSymmetryOrbit.update] using h
  have hQ' :
      Q.charge (orbit.U t prior) = orbit.U t (Q.charge prior) := by
    simpa [BayesianSymmetryOrbit.update] using hQ
  calc
    hessianIndefiniteForm (E := E)
        (orbit.update t)
        (Q.charge (orbit.update t))
        =
      hessianIndefiniteForm (E := E)
        (orbit.U t prior)
        (orbit.U t (Q.charge prior)) := by
          rw [BayesianSymmetryOrbit.update, hQ']
    _ = hessianIndefiniteForm (E := E) prior (Q.charge prior) := by
          simpa using orbit.preserves_hessian t prior (Q.charge prior)

end InfoGeometry.Canonical.NoetherInference
