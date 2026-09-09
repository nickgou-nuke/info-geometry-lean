import Mathlib.Tactic
import InfoGeometry.Canonical.OperatorFenchelRegularCone
import InfoGeometry.OperatorAlgebra.ErlangenConformalInvariant
import InfoGeometry.OperatorAlgebra.SymmetricSplitSelfDualCartanSpaces
import InfoGeometry.Canonical.WeylMobiusReflection
import InfoGeometry.Canonical.WeylA1Character
import InfoGeometry.Canonical.ConformalSL2GeneratorBridge

/-!
# InfoGeometry.Canonical.SelfDualWeylRootKleinBridge

Lean-side packet for the finite dictionary requested in the repository:

- self-dual regular-positive cones on doubled operators,
- Fenchel--Legendre duality lifted to operator potentials,
- fixed-point transport along equivariant maps (Erlangen view),
- split-Cartan self-duality readback under involutive symmetries,
- finite `A₁` Weyl/reflection and maximal-torus checks,
- finite Klein-bottle affine relation `A B A⁻¹ = B⁻¹`.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace InfoGeometry.Canonical.SelfDualWeylRootKleinBridge

open Matrix
open BigOperators
open InfoGeometry.Canonical.OperatorFenchelRegularCone
open InfoGeometry.OperatorAlgebra.ErlangenConformalInvariant
open InfoGeometry.OperatorAlgebra.SymmetricSplitSelfDualCartanSpaces
open InfoGeometry.Canonical.WeylMobiusReflection
open InfoGeometry.Canonical.WeylA1Character
open InfoGeometry.Geometry
open InfoGeometry.OperatorAlgebra.SelfDualConeColimit

abbrev M2R : Type _ := Matrix (Fin 2) (Fin 2) ℝ
abbrev M3R : Type _ := Matrix (Fin 3) (Fin 3) ℝ

/-- Support projection to the Drazin regular block. -/
theorem regularPositiveConeOmegaD_support_via_owner
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    {H : (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E)}
    (hH : regularPositiveConeOmegaD (E := E) c H) :
    compress c.Preg H = H :=
  InfoGeometry.Canonical.OperatorFenchelRegularCone.regularPositiveConeOmegaD_support
    (c := c) (H := H) hH

/-- Strictly positive spectrum inside the regular branch. -/
theorem regularPositiveConeOmegaD_spectrum_pos_via_owner
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E)}
    {H : (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E)}
    (hH : regularPositiveConeOmegaD (E := E) c H) :
    spectrum ℝ H ⊆ Set.Ioi (0 : ℝ) :=
  InfoGeometry.Canonical.OperatorFenchelRegularCone.regularPositiveConeOmegaD_spectrum_pos
    (c := c) (H := H) hH

/-- Fenchel--Young inequality on the regular branch. -/
theorem fenchelYoung_on_regular_positive
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (c : CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace E))
    (hPos : c.RegularSpectrumPositive)
    (ω : (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) →L[ℝ] ℝ)
    (ψStar : ((InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) →L[ℝ] ℝ) → ℝ)
    (hConj : InfoGeometry.Geometry.IsFenchelMajorized
      (operatorFenchelPotentialOnRegularCone (E := E) ω) ψStar)
    (H : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E)
    (η : (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) →L[ℝ] ℝ)
    (hH : regularPositiveConeOmegaD (E := E) c H) :
    η H ≤ operatorFenchelPotentialOnRegularCone (E := E) ω H + ψStar η :=
  InfoGeometry.Canonical.OperatorFenchelRegularCone.operatorFenchelYoung_on_doubledKrein
    (E := E) c hPos ω ψStar hConj H η hH

/-- Hesse/entropy inverse packet for operatorial Legendre duals. -/
theorem operatorLegendreHessian_inverse_packet
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (D : LegendreContinuousLinearEquivInverseData (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E)) :
    D.toLegendreHessianInverseContext.moment =
        dualCoord D.massieu D.beta
      ∧ D.entropyGradient D.toLegendreHessianInverseContext.moment = D.beta
      ∧ D.toLegendreHessianInverseContext.fisherHessian =
        hessian D.massieu D.beta
      ∧ D.toLegendreHessianInverseContext.entropyHessian =
        fderiv ℝ D.entropyGradient D.toLegendreHessianInverseContext.moment
      ∧ D.toLegendreHessianInverseContext.entropyHessian.comp
          D.toLegendreHessianInverseContext.fisherHessian =
        ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E)
      ∧ D.toLegendreHessianInverseContext.fisherHessian.comp
          D.toLegendreHessianInverseContext.entropyHessian =
        ContinuousLinearMap.id ℝ (MomentCoord (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E)) :=
  InfoGeometry.Canonical.OperatorFenchelRegularCone.operatorLegendreHessianInverse_packet_of_continuousLinearEquiv
    (D := D)

/-- Fixed-point pullback is the basic finite-stage invariant transport map. -/
theorem invariant_pullback_of_equivariance
    {G : Type*} [Group G]
    {A B : Type*} [Ring A] [Algebra ℝ A] [Ring B] [Algebra ℝ B]
    (actA : GroupAction G A) (actB : GroupAction G B)
    (φ : A →ₐ[ℝ] B)
    (h : EquivariantHom actA actB φ)
    (x : A)
    (hx : x ∈ actA.fixedSubalgebra) :
    φ x ∈ actB.fixedSubalgebra :=
  EquivariantHom.fixedSubalgebra_pullback (actA := actA) (actB := actB) (φ := φ) h x hx

/-- The induced homomorphism on fixed-point subalgebras. -/
def fixedSubalgebra_hom_of_equivariance
    {G : Type*} [Group G]
    {A B : Type*} [Ring A] [Algebra ℝ A] [Ring B] [Algebra ℝ B]
    (actA : GroupAction G A) (actB : GroupAction G B)
    (φ : A →ₐ[ℝ] B)
    (h : EquivariantHom actA actB φ) :
    actA.fixedSubalgebra →ₐ[ℝ] actB.fixedSubalgebra :=
  EquivariantHom.fixedSubalgebraHom (actA := actA) (actB := actB) h

open InfoGeometry.Geometry.Cartan

/-- Finite-stage self-dual readback under an involutive stage-preserving symmetry. -/
theorem splitCartan_stage_symmetry_readback
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (pairing : SplitCartanAmbient X → SplitCartanAmbient X → ℝ)
    (θ : (SplitCartanAmbient X) → (SplitCartanAmbient X))
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (splitCartanStageCarrier X n))
    (hstage : ∀ z : SplitCartanAmbient X, (θ z).1 = z.1)
    (hinvol : ∀ z : SplitCartanAmbient X, θ (θ z) = z)
    (hpair : ∀ x y, pairing (θ x) (θ y) = pairing x y)
    (n : ℕ) (x : SplitCartanAmbient X) :
    θ x ∈ splitCartanStageCarrier X n ↔
      ∀ y, y ∈ splitCartanStageCarrier X n → 0 ≤ pairing x y := by
  exact InfoGeometry.OperatorAlgebra.SymmetricSplitSelfDualCartanSpaces.splitCartan_stage_cartan_selfDual_readback
    (X := X) pairing θ hself hstage hinvol hpair n x

/-- Colimit readback under an involutive pairing-preserving symmetry. -/
theorem splitCartan_colimit_symmetry_readback
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (pairing : SplitCartanAmbient X → SplitCartanAmbient X → ℝ)
    (θ : (SplitCartanAmbient X) → (SplitCartanAmbient X))
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (splitCartanStageCarrier X n))
    (hstage : ∀ z : SplitCartanAmbient X, (θ z).1 = z.1)
    (hinvol : ∀ z : SplitCartanAmbient X, θ (θ z) = z)
    (hpair : ∀ x y, pairing (θ x) (θ y) = pairing x y)
    (x : SplitCartanAmbient X) :
    θ x ∈ Set.iUnion (splitCartanStageCarrier X) ↔
      ∀ y, y ∈ Set.iUnion (splitCartanStageCarrier X) → 0 ≤ pairing x y := by
  exact InfoGeometry.OperatorAlgebra.SymmetricSplitSelfDualCartanSpaces.splitCartan_cartan_selfDual_readback
    (X := X) pairing θ hself hstage hinvol hpair x

/-- Symmetry commutes with colimit support and dual positivity. -/
theorem splitCartan_symmetry_preserves_colimit_dual
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (θ : SplitCartanAmbient X → SplitCartanAmbient X)
    (hstage : ∀ z : SplitCartanAmbient X, (θ z).1 = z.1)
    (x : SplitCartanAmbient X) :
    x ∈ Set.iUnion (splitCartanStageCarrier X) →
      θ x ∈ Set.iUnion (splitCartanStageCarrier X) := by
  intro hx
  exact (InfoGeometry.OperatorAlgebra.SymmetricSplitSelfDualCartanSpaces.splitCartan_symmetry_preserves_colimit
    (X := X) θ hstage) hx


-- Finite `A₁ × A₁` Weyl/reflection and maximal-torus checks in `M₂(ℝ)`.
namespace FiniteWeyl

abbrev r1 : M2R := !![(-1 : ℝ), 0; 0, 1]
abbrev r2 : M2R := !![(1 : ℝ), 0; 0, -1]
abbrev r3 : M2R := !![(-1 : ℝ), 0; 0, (-1 : ℝ)]
abbrev H : M2R := !![(1 : ℝ), 0; 0, -1]
abbrev G : M2R := !![(2 : ℝ), 0; 0, 2]

private lemma r1_transpose : (r1 : M2R)ᵀ = r1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [r1]

private lemma r2_transpose : (r2 : M2R)ᵀ = r2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [r2]

private lemma r3_transpose : (r3 : M2R)ᵀ = r3 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [r3]

/-- Two simple reflections are involutive. -/
theorem r1_sq : r1 * r1 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [r1]

theorem r2_sq : r2 * r2 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [r2]

theorem r3_sq : r3 * r3 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [r3]

/-- They commute and the product is `-I`. -/
theorem r1_r2_comm : r1 * r2 = r2 * r1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [r1, r2]

theorem r3_def : r3 = r1 * r2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [r1, r2, r3]

/-- Cartan generator is fixed by the finite Weyl reflections. -/
theorem r1_H : r1 * H * r1 = H := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [r1, H]

theorem r2_H : r2 * H * r2 = H := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [r2, H]

theorem r3_H : r3 * H * r3 = H := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [r3, H]

/-- The Weyl reflections preserve the `A₁` Cartan matrix. -/
theorem r1_G : r1ᵀ * G * r1 = G := by
  rw [r1_transpose]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [r1, G]

theorem r2_G : r2ᵀ * G * r2 = G := by
  rw [r2_transpose]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [r2, G]

theorem r3_G : r3ᵀ * G * r3 = G := by
  rw [r3_transpose]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [r3, G]

/-- Finite `A₁` character identity `Σ_{i=0}^m x^i y^(m-i) (x - y) = x^(m+1)-y^(m+1)`. -/
theorem finite_a1_character_identity
    {R : Type*} [CommRing R] (x y : R) (m : ℕ) :
    a1CharacterSum x y m * a1Denominator x y = x ^ (m + 1) - y ^ (m + 1) :=
  a1CharacterSum_mul_denominator (R := R) x y m

/-- Conformal-reflection side of the finite Weyl reflection: `W * N * W = -N`. -/
theorem conformalWeyl_conj_N :
    W * InfoGeometry.Algebra.HypercomplexTriad.N * W =
      -InfoGeometry.Algebra.HypercomplexTriad.N := by
  simpa [W] using (InfoGeometry.Canonical.WeylMobiusReflection.weyl_conj_N
    : W * InfoGeometry.Algebra.HypercomplexTriad.N * W =
      -InfoGeometry.Algebra.HypercomplexTriad.N)

/-- Conformal-reflection side of the finite Weyl reflection: `W * K * W = K`. -/
theorem conformalWeyl_conj_K :
    W * InfoGeometry.Canonical.ModularLorentzBoost.K * W =
      InfoGeometry.Canonical.ModularLorentzBoost.K := by
  simpa [W] using (InfoGeometry.Canonical.WeylMobiusReflection.weyl_conj_K
    : W * InfoGeometry.Canonical.ModularLorentzBoost.K * W =
      InfoGeometry.Canonical.ModularLorentzBoost.K)

end FiniteWeyl

-- Finite affine presentation of the Klein bottle orientation-reversing quotient
-- relation used in several corridor scripts.
section KleinBottleFinite

abbrev kleinA : M3R := !![(1 : ℝ), 0, (1 / 2 : ℝ); 0, -1, 0; 0, 0, 1]
abbrev kleinA_inv : M3R := !![(1 : ℝ), 0, (-1 / 2 : ℝ); 0, -1, 0; 0, 0, 1]
abbrev kleinB : M3R := !![(1 : ℝ), 0, 0; 0, 1, 1; 0, 0, 1]
abbrev kleinB_inv : M3R := !![(1 : ℝ), 0, 0; 0, 1, (-1 : ℝ); 0, 0, 1]

/-- `A` is invertible with the displayed inverse. -/
theorem kleinA_inv_right : kleinA * kleinA_inv = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [kleinA, kleinA_inv]

theorem kleinA_inv_left : kleinA_inv * kleinA = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [kleinA, kleinA_inv]

theorem kleinB_inv_right : kleinB * kleinB_inv = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [kleinB, kleinB_inv]

theorem kleinB_inv_left : kleinB_inv * kleinB = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [kleinB, kleinB_inv]

/-- `A B A⁻¹ = B⁻¹` for the affine Klein-bottle relation. -/
theorem kleinBottle_orientifold_relation :
    kleinA * kleinB * kleinA_inv = kleinB_inv := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [kleinA, kleinA_inv, kleinB, kleinB_inv]

/-- Weyl-type reflection on the first affine coordinate. -/
def kleinW : M3R := !![(-1 : ℝ), 0, 0; 0, 1, 0; 0, 0, 1]

/-- First-coordinate unit translation. -/
def kleinBx : M3R := !![1, 0, (-1 : ℝ); 0, 1, 0; 0, 0, 1]

/-- `kleinA` conjugates `kleinW` by a non-trivial lattice translation.

This is the finite affine cocycle witness: `A` and `W` do not commute, but their
defect is exactly a unit translation in the first torus coordinate.
-/
theorem kleinA_conj_kleinW_translation :
    kleinA * kleinW * kleinA_inv = kleinW * kleinBx := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [kleinA, kleinA_inv, kleinW, kleinBx]

/-- Re-associate the conjugation formula to the semidirect-product form:
`A` commutes with `W` up to a right translation by `Bx`.
-/
theorem kleinA_mul_kleinW_eq_kleinW_mul_kleinBx_mul_kleinA :
    kleinA * kleinW = kleinW * kleinBx * kleinA := by
  calc
    kleinA * kleinW = kleinA * kleinW * (kleinA_inv * kleinA) := by
      rw [kleinA_inv_left, Matrix.mul_one]
    _ = (kleinA * kleinW * kleinA_inv) * kleinA := by
      simp [Matrix.mul_assoc]
    _ = kleinW * kleinBx * kleinA := by
      rw [kleinA_conj_kleinW_translation]

/-- `A` and `W` do not commute on the nose: the defect is a unit affine
translation in the first coordinate. -/
theorem kleinA_kleinW_noncommute :
    kleinA * kleinW ≠ kleinW * kleinA := by
  intro h
  have h00 : (kleinA * kleinW) 0 2 = (kleinW * kleinA) 0 2 := by
    exact congrArg (fun M : M3R => M 0 2) h
  have h00' : (2 : ℝ)⁻¹ = -(2 : ℝ)⁻¹ := by
    simpa [kleinA, kleinW] using h00
  norm_num at h00'

/-- Affine-coordinate form of the same noncommutation on maximal-torus-like variables. -/
def kleinTorusAction (θ1 θ2 : ℝ) : ℝ × ℝ := (θ1 + Real.pi, -θ2)

/-- Finite Weyl reflection on the same coordinates. -/
def weylTorusAction (θ1 θ2 : ℝ) : ℝ × ℝ := (-θ1 + θ2, θ2)

/-- In these coordinates, `kleinTorus` and `weylTorus` do not commute.
    The defect is a first-coordinate affine shift by `2*θ2 + 2π`. -/
theorem klein_weyl_torus_noncommute (θ1 θ2 : ℝ) :
    kleinTorusAction (weylTorusAction θ1 θ2).1 (weylTorusAction θ1 θ2).2 -
        weylTorusAction (kleinTorusAction θ1 θ2).1 (kleinTorusAction θ1 θ2).2 =
      (2 * θ2 + 2 * Real.pi, (0 : ℝ)) := by
  ext <;> simp [kleinTorusAction, weylTorusAction]
  ring

/-- Opposite-order defect for the same two actions:
    `W∘K - K∘W = (-2 θ₂ - 2π, 0)`. -/
theorem weyl_klein_torus_noncommute (θ1 θ2 : ℝ) :
    weylTorusAction (kleinTorusAction θ1 θ2).1 (kleinTorusAction θ1 θ2).2 -
        kleinTorusAction (weylTorusAction θ1 θ2).1 (weylTorusAction θ1 θ2).2 =
      (-2 * θ2 - 2 * Real.pi, (0 : ℝ)) := by
  ext <;> simp [kleinTorusAction, weylTorusAction]
  ring

end KleinBottleFinite

end InfoGeometry.Canonical.SelfDualWeylRootKleinBridge

end
