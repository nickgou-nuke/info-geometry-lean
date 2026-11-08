/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Core.JordanAssociatorRing
import InfoGeometry.Algebra.UnipotentReflexivePairFactorization
import InfoGeometry.Canonical.ReflexiveNilpotentFlows
import InfoGeometry.Canonical.PeirceWeightedTrace
import InfoGeometry.Algebra.ZornColorGL31Obstruction
import InfoGeometry.Lie.SplitOctonionCliffordNoninjective
import InfoGeometry.Lie.SplitOctonionNonmultiplicativity
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Meta.EpistemicCompilerChain
import InfoGeometry.Meta.MetaEpistemicCompiler

/-!
# Algebraic identities for a reflexive square-zero pair

The historical geometric names below denote ring expressions, not constructed
manifolds, connections, modular automorphism groups or exceptional Lie algebras.
The precise scope is:

* `X - X*D*X = X*(1-D*X) = (1-X*D)*X`. Nilpotency requires separate Drazin
  hypotheses (`mat2Z_kantorDefect_not_nilpotent_without_drazin` shows `X=1, D=0`
  gives idempotent residual `1`).
* Idempotent Peirce commutators anticommute with `2 • P - 1` and recover the
  off-diagonal part; this does not separate eigenspaces in characteristic two.
* A reflexive square-zero pair with self-adjoint support projections gives an
  algebraic orthogonal decomposition. Its existence is an explicit hypothesis.
* `Γ² = Δ` is an active-support `t²-1` identity, not `Φ₂(t)=t+1`
  (`mat2Z_ehresmann_not_phi2`). The `Φ₃`, `Φ₄`, and `Φ₆` identities do not imply
  primitive roots or exact orders in arbitrary characteristic, nor a Kähler
  structure or exceptional triality.
* The three-shear product swaps support projections and satisfies both two-sided
  inverse equations and `w_J ^ 4 = 1` (`UnipotentReflexivePairFactorization`);
  this is not a construction of a projective plane or a faithful deck action.
* The weighted-support identities are algebraic intertwining equations. No
  positive normalized state, analytic KMS condition or Tomita operator is built.
* The symmetrized-product operator commutator is `[[S,T],X] = [X,[T,S]]`, with
  this exact sign (`mat2Z_jordanAssociator_sign_refutation`). This
  associative-envelope identity does not identify `E₆`, `F₄`, or their
  symmetric decomposition.
* For the split-octonion left-multiplication lift (Breakthrough 4), the native
  domain boundaries are explicitly linked: `nonmultiplicativity_obstruction`
  (nonzero associator `(XY)Z - X(YZ)`), `splitOctonionLeftCliffordRepresentation_not_injective`
  (128D Clifford algebra to 64D endomorphism algebra), and
  `not_faithful_gl31_with_CAR_odd` (central raw CAR odd brackets vs noncentral
  `gl(3|1)` odd brackets).

The final finite schedule certifies only its explicitly stated claims, with
`unifiedPillarRules` consuming prerequisite proofs along the causal poset.
-/

namespace InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance

section AbstractFivePillarSynthesis

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

/-!
## 1. Fundamental Geometric & Operator-Algebraic Primitives in `A`
-/

/-- Symmetrized Jordan product / anticommutator `{X, Y} = X Y + Y X`. -/
def jordanProd (X Y : A) : A := X * Y + Y * X

/-- Antisymmetric Lie commutator / adjoint derivative `[X, Y] = X Y - Y X`. -/
def lieBracket (X Y : A) : A := X * Y - Y * X

/-- Jordan associator `[X, Y, Z]_∘ = (X ∘ Y) ∘ Z - X ∘ (Y ∘ Z)`. -/
def jordanAssociator (X Y Z : A) : A :=
  jordanProd (jordanProd X Y) Z - jordanProd X (jordanProd Y Z)

/-- Kantor triple defect `K(X, D) = X - X D X` measuring departure from regularity. -/
def kantorTripleDefect (X D : A) : A := X - X * D * X

/-- Spectral Cartan grading involution `Γ_S = 2 • P_D - 1`. -/
def spectralCartanInvolution (P_D : A) : A := 2 • P_D - 1

/-- Cartan anomaly commutator `χ(P_D, P_M) = [P_D, P_M]` between oblique spectral
    idempotent `P_D` and orthogonal projection `P_M`. -/
def cartanAnomaly (P_D P_M : A) : A := lieBracket P_D P_M

/-- Dual nilpotent Peirce pair `(d, B)` with self-adjoint range/co-range projections. -/
def IsGeometricPeircePair [StarRing A] (d B : A) : Prop :=
  d * d = 0 ∧ B * B = 0 ∧ d * B * d = d ∧ B * d * B = B ∧
  star (d * B) = d * B ∧ star (B * d) = B * d

/-- Positive pole / exact range projection `P_+ = d B`. -/
def projPlus (d B : A) : A := d * B

/-- Negative pole / co-exact co-range projection `P_- = B d`. -/
def projMinus (d B : A) : A := B * d

/-- Active support `Δ = P_+ + P_-`; not a metric Laplacian without extra data. -/
def hodgeLaplacian (d B : A) : A := projPlus d B + projMinus d B

/-- Complementary support `P_0 = 1 - Δ`; harmonic terminology is algebraic here. -/
def projHarmonic (d B : A) : A := 1 - hodgeLaplacian d B

/-- Support grading `Γ = [d,B]`; no geometric connection is specified. -/
def ehresmannCurvature (d B : A) : A := projPlus d B - projMinus d B

/-- Active-support square root of minus the support: `J₄ = d - B`. -/
def kahlerStructure (d B : A) : A := d - B

/-- Active-support cubic root; no exact-order or exceptional-triality claim. -/
def trialityOperator (d B : A) : A := -projMinus d B + d - B

/-- Active-support sixth-cyclotomic expression `ω₆ = P_- - d + B = -ω₃`. -/
def hexalityOperator (d B : A) : A := projMinus d B - d + B

/-- Weyl-type unit expression `w_J = P_0 + (d-B)`, of order dividing four. -/
def bruhatWeylReflection (d B : A) : A := projHarmonic d B + kahlerStructure d B

/-- Inverse Weyl-type expression `P_0 - (d-B)` for a reflexive square-zero pair. -/
def bruhatWeylReflectionInv (d B : A) : A := projHarmonic d B - kahlerStructure d B

/-- Algebraic weighted support `ρ = u² • P_- + v² • P_+`; not a state. -/
def kmsModularWeight (u v : R) (d B : A) : A :=
  (u * u) • projMinus d B + (v * v) • projPlus d B

/-!
## 2. Breakthrough 1: Non-Normal Calculus (Kantor Defect & Cartan Anomaly)
-/

/-- Two factorizations of the inverse defect. No nilpotency follows without
additional inverse hypotheses. The historical theorem name is retained. -/
theorem kantorTripleDefect_eq_nilpotent_residual (X D : A) :
    kantorTripleDefect X D = X * (1 - D * X) ∧
    kantorTripleDefect X D = (1 - X * D) * X := by
  unfold kantorTripleDefect
  constructor <;> noncomm_ring

/-- For any idempotent `P_D`, the Cartan anomaly `χ = [P_D, P_M]` anti-commutes with the
    spectral Cartan involution `Γ_S = 2 • P_D - 1`: `{Γ_S, χ} = 0`. -/
theorem cartanAnomaly_anticommutes_spectralInvolution {P_D : A}
    (hPD : IsIdempotentElem P_D) (P_M : A) :
    jordanProd (spectralCartanInvolution P_D) (cartanAnomaly P_D P_M) = 0 := by
  have hP : P_D * P_D = P_D := hPD.eq
  unfold jordanProd spectralCartanInvolution cartanAnomaly lieBracket
  calc (2 • P_D - 1) * (P_D * P_M - P_M * P_D) +
       (P_D * P_M - P_M * P_D) * (2 • P_D - 1)
    _ = 2 • ((P_D * P_D - P_D) * P_M) - 2 • (P_M * (P_D * P_D - P_D)) := by
        rw [two_nsmul]
        noncomm_ring
    _ = 0 := by rw [hP, sub_self, mul_zero, zero_mul, smul_zero, sub_self]

/-- The off-diagonal Peirce tangent part of `P_M` relative to `P_D` is reconstructed
    directly from the product `Γ_S * χ(P_D, P_M)`. -/
theorem offDiag_reconstructs_from_cartanAnomaly {P_D : A}
    (hPD : IsIdempotentElem P_D) (P_M : A) :
    P_D * P_M * (1 - P_D) + (1 - P_D) * P_M * P_D =
      spectralCartanInvolution P_D * cartanAnomaly P_D P_M := by
  have hP : P_D * P_D = P_D := hPD.eq
  unfold spectralCartanInvolution cartanAnomaly lieBracket
  calc P_D * P_M * (1 - P_D) + (1 - P_D) * P_M * P_D
    _ = (P_D + P_D - 1) * (P_D * P_M - P_M * P_D) -
        2 • ((P_D * P_D - P_D) * P_M) := by noncomm_ring
    _ = (2 • P_D - 1) * (P_D * P_M - P_M * P_D) := by
        rw [hP, sub_self, zero_mul, smul_zero, sub_zero, two_nsmul]

/-!
## 3. Modular Helper Lemmas for Pillars I–V
-/

lemma projPlus_idem {d B : A} (hdBd : d * B * d = d) :
    projPlus d B * projPlus d B = projPlus d B := by
  unfold projPlus
  calc (d * B) * (d * B) = (d * B * d) * B := by noncomm_ring
    _ = d * B := by rw [hdBd]

lemma projMinus_idem {d B : A} (hBdB : B * d * B = B) :
    projMinus d B * projMinus d B = projMinus d B := by
  unfold projMinus
  calc (B * d) * (B * d) = (B * d * B) * d := by noncomm_ring
    _ = B * d := by rw [hBdB]

lemma projPlus_mul_projMinus {d B : A} (hB : B * B = 0) :
    projPlus d B * projMinus d B = 0 := by
  unfold projPlus projMinus
  calc (d * B) * (B * d) = d * (B * B) * d := by noncomm_ring
    _ = 0 := by rw [hB, mul_zero, zero_mul]

lemma projMinus_mul_projPlus {d B : A} (hd : d * d = 0) :
    projMinus d B * projPlus d B = 0 := by
  unfold projPlus projMinus
  calc (B * d) * (d * B) = B * (d * d) * B := by noncomm_ring
    _ = 0 := by rw [hd, mul_zero, zero_mul]

lemma projPlus_mul_d {d B : A} (hdBd : d * B * d = d) :
    projPlus d B * d = d := hdBd

lemma d_mul_projMinus {d B : A} (hdBd : d * B * d = d) :
    d * projMinus d B = d := by
  unfold projMinus; rw [← mul_assoc, hdBd]

lemma d_mul_projPlus {d : A} (B : A) (hd : d * d = 0) :
    d * projPlus d B = 0 := by
  unfold projPlus; rw [← mul_assoc, hd, zero_mul]

lemma projMinus_mul_d (B : A) {d : A} (hd : d * d = 0) :
    projMinus d B * d = 0 := by
  unfold projMinus; rw [mul_assoc, hd, mul_zero]

lemma projMinus_mul_B {d B : A} (hBdB : B * d * B = B) :
    projMinus d B * B = B := hBdB

lemma B_mul_projPlus {d B : A} (hBdB : B * d * B = B) :
    B * projPlus d B = B := by
  unfold projPlus; rw [← mul_assoc, hBdB]

lemma B_mul_projMinus (d : A) {B : A} (hB : B * B = 0) :
    B * projMinus d B = 0 := by
  unfold projMinus; rw [← mul_assoc, hB, zero_mul]

lemma projPlus_mul_B (d : A) {B : A} (hB : B * B = 0) :
    projPlus d B * B = 0 := by
  unfold projPlus; rw [mul_assoc, hB, mul_zero]

lemma hodge_partition_of_unity (d B : A) :
    projPlus d B + projMinus d B + projHarmonic d B = 1 := by
  unfold projHarmonic hodgeLaplacian; abel

lemma star_projHarmonic [StarRing A] {d B : A}
    (hsa_plus : star (d * B) = d * B) (hsa_minus : star (B * d) = B * d) :
    star (projHarmonic d B) = projHarmonic d B := by
  unfold projHarmonic hodgeLaplacian projPlus projMinus
  rw [star_sub, star_one, star_add, hsa_plus, hsa_minus]

lemma lieBracket_projPlus_ehresmann {d B : A}
    (hd : d * d = 0) (hB : B * B = 0) (hdBd : d * B * d = d) :
    lieBracket (projPlus d B) (ehresmannCurvature d B) = 0 := by
  unfold lieBracket ehresmannCurvature
  rw [mul_sub, sub_mul, projPlus_idem hdBd, projPlus_mul_projMinus hB,
      projMinus_mul_projPlus hd, sub_self]

lemma lieBracket_projMinus_ehresmann {d B : A}
    (hd : d * d = 0) (hB : B * B = 0) (hBdB : B * d * B = B) :
    lieBracket (projMinus d B) (ehresmannCurvature d B) = 0 := by
  unfold lieBracket ehresmannCurvature
  rw [mul_sub, sub_mul, projMinus_mul_projPlus hd, projMinus_idem hBdB,
      projPlus_mul_projMinus hB, sub_self]

lemma lieBracket_ehresmann_d {d B : A}
    (hd : d * d = 0) (hdBd : d * B * d = d) :
    lieBracket (ehresmannCurvature d B) d = 2 • d := by
  have h1 : ehresmannCurvature d B * d = d := by
    unfold ehresmannCurvature
    rw [sub_mul, projPlus_mul_d hdBd, projMinus_mul_d B hd, sub_zero]
  have h2 : d * ehresmannCurvature d B = -d := by
    unfold ehresmannCurvature
    rw [mul_sub, d_mul_projPlus B hd, d_mul_projMinus hdBd, zero_sub]
  unfold lieBracket
  rw [h1, h2, sub_neg_eq_add, two_nsmul]

lemma lieBracket_ehresmann_B {d B : A}
    (hB : B * B = 0) (hBdB : B * d * B = B) :
    lieBracket (ehresmannCurvature d B) B = -(2 • B) := by
  have h1 : ehresmannCurvature d B * B = -B := by
    unfold ehresmannCurvature
    rw [sub_mul, projPlus_mul_B d hB, projMinus_mul_B hBdB, zero_sub]
  have h2 : B * ehresmannCurvature d B = B := by
    unfold ehresmannCurvature
    rw [mul_sub, B_mul_projPlus hBdB, B_mul_projMinus d hB, sub_zero]
  unfold lieBracket
  rw [h1, h2, two_nsmul]
  abel

lemma ehresmannCurvature_sq_sub_laplacian {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    ehresmannCurvature d B * ehresmannCurvature d B - hodgeLaplacian d B = 0 := by
  unfold ehresmannCurvature hodgeLaplacian
  rw [sub_mul, mul_sub, mul_sub, projPlus_idem hdBd, projPlus_mul_projMinus hB,
      projMinus_mul_projPlus hd, projMinus_idem hBdB]
  abel

lemma kahlerStructure_sq {d B : A} (hd : d * d = 0) (hB : B * B = 0) :
    kahlerStructure d B * kahlerStructure d B = -hodgeLaplacian d B := by
  unfold kahlerStructure hodgeLaplacian projPlus projMinus
  calc (d - B) * (d - B) = d * d - (d * B + B * d) + B * B := by noncomm_ring
    _ = -(d * B + B * d) := by rw [hd, hB]; abel

lemma kahlerStructure_sq_add_laplacian {d B : A} (hd : d * d = 0) (hB : B * B = 0) :
    kahlerStructure d B * kahlerStructure d B + hodgeLaplacian d B = 0 := by
  rw [kahlerStructure_sq hd hB, neg_add_cancel]

lemma trialityOperator_sq {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    trialityOperator d B * trialityOperator d B = -projPlus d B - d + B := by
  unfold trialityOperator
  calc (-projMinus d B + d - B) * (-projMinus d B + d - B)
    _ = projMinus d B * projMinus d B - projMinus d B * d + projMinus d B * B -
        d * projMinus d B + d * d - d * B +
        B * projMinus d B - B * d + B * B := by noncomm_ring
    _ = projMinus d B - 0 + B - d + 0 - projPlus d B + 0 - projMinus d B + 0 := by
        rw [projMinus_idem hBdB, projMinus_mul_d B hd, projMinus_mul_B hBdB,
            d_mul_projMinus hdBd, hd, B_mul_projMinus d hB, hB]; rfl
    _ = -projPlus d B - d + B := by abel

lemma trialityOperator_quad_law {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    trialityOperator d B * trialityOperator d B + trialityOperator d B +
      hodgeLaplacian d B = 0 := by
  rw [trialityOperator_sq hd hB hdBd hBdB]
  unfold trialityOperator hodgeLaplacian
  abel

lemma trialityOperator_cube {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    trialityOperator d B ^ 3 = hodgeLaplacian d B := by
  calc trialityOperator d B ^ 3
    _ = (trialityOperator d B * trialityOperator d B) * trialityOperator d B := by
        noncomm_ring
    _ = (-projPlus d B - d + B) * (-projMinus d B + d - B) := by
        rw [trialityOperator_sq hd hB hdBd hBdB]; rfl
    _ = projPlus d B * projMinus d B - projPlus d B * d + projPlus d B * B +
        d * projMinus d B - d * d + d * B -
        B * projMinus d B + B * d - B * B := by noncomm_ring
    _ = 0 - d + 0 + d - 0 + projPlus d B - 0 + projMinus d B - 0 := by
        rw [projPlus_mul_projMinus hB, projPlus_mul_d hdBd, projPlus_mul_B d hB,
            d_mul_projMinus hdBd, hd, B_mul_projMinus d hB, hB]; rfl
    _ = hodgeLaplacian d B := by unfold hodgeLaplacian; abel

lemma hexalityOperator_eq_neg_triality (d B : A) :
    hexalityOperator d B = -trialityOperator d B := by
  unfold hexalityOperator trialityOperator
  abel

lemma hexalityOperator_quad_law {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    hexalityOperator d B * hexalityOperator d B - hexalityOperator d B +
      hodgeLaplacian d B = 0 := by
  rw [hexalityOperator_eq_neg_triality, neg_mul_neg, sub_neg_eq_add]
  exact trialityOperator_quad_law hd hB hdBd hBdB

lemma hexalityOperator_cube {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    hexalityOperator d B ^ 3 = -hodgeLaplacian d B := by
  calc hexalityOperator d B ^ 3
    _ = -(trialityOperator d B ^ 3) := by
        rw [hexalityOperator_eq_neg_triality]
        noncomm_ring
    _ = -hodgeLaplacian d B := by rw [trialityOperator_cube hd hB hdBd hBdB]

lemma hexalityOperator_pow_six {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    hexalityOperator d B ^ 6 = hodgeLaplacian d B := by
  have hS : hodgeLaplacian d B * hodgeLaplacian d B = hodgeLaplacian d B :=
    InfoGeometry.Algebra.UnipotentReflexivePairFactorization.support_square hd hB hdBd hBdB
  calc hexalityOperator d B ^ 6
    _ = (hexalityOperator d B ^ 3) * (hexalityOperator d B ^ 3) := by noncomm_ring
    _ = (-hodgeLaplacian d B) * (-hodgeLaplacian d B) := by
        rw [hexalityOperator_cube hd hB hdBd hBdB]
    _ = hodgeLaplacian d B := by rw [neg_mul_neg, hS]

/-- Supported cyclotomic operators recover the forward transvection: `(-J₄) * ω₃ = Δ + d`. -/
lemma kahler_triality_transvection_recovery {d B : A}
    (hd : d * d = 0) (hB : B * B = 0) (hdBd : d * B * d = d) :
    (-kahlerStructure d B) * trialityOperator d B = hodgeLaplacian d B + d := by
  unfold kahlerStructure trialityOperator hodgeLaplacian projPlus projMinus
  calc (-(d - B)) * (-(B * d) + d - B)
    _ = (d * B * d) - d * d + d * B - (B * B) * d + B * d - B * B := by noncomm_ring
    _ = (d * B + B * d) + d := by rw [hdBd, hd, hB, zero_mul]; abel

lemma bruhat_triple_product {d B : A}
    (hd : d * d = 0) (hdBd : d * B * d = d) :
    (1 + d) * (1 - B) * (1 + d) = bruhatWeylReflection d B := by
  have h := InfoGeometry.Algebra.UnipotentReflexivePairFactorization.unipotent_triple_factorization hd hdBd
  unfold bruhatWeylReflection projHarmonic hodgeLaplacian kahlerStructure projPlus projMinus
  calc (1 + d) * (1 - B) * (1 + d)
    _ = 1 - d * B - B * d + d - B := h
    _ = 1 - (d * B + B * d) + (d - B) := by abel

lemma projHarmonic_orthog {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    projPlus d B * projHarmonic d B = 0 ∧
    projMinus d B * projHarmonic d B = 0 ∧
    projHarmonic d B * projPlus d B = 0 ∧
    projHarmonic d B * projMinus d B = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold projHarmonic hodgeLaplacian
    rw [mul_sub, mul_one, mul_add, projPlus_idem hdBd, projPlus_mul_projMinus hB, add_zero, sub_self]
  · unfold projHarmonic hodgeLaplacian
    rw [mul_sub, mul_one, mul_add, projMinus_mul_projPlus hd, projMinus_idem hBdB, zero_add, sub_self]
  · unfold projHarmonic hodgeLaplacian
    rw [sub_mul, one_mul, add_mul, projPlus_idem hdBd, projMinus_mul_projPlus hd, add_zero, sub_self]
  · unfold projHarmonic hodgeLaplacian
    rw [sub_mul, one_mul, add_mul, projPlus_mul_projMinus hB, projMinus_idem hBdB, zero_add, sub_self]

lemma projHarmonic_idem {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    projHarmonic d B * projHarmonic d B = projHarmonic d B := by
  obtain ⟨h1, h2, _, _⟩ := projHarmonic_orthog hd hB hdBd hBdB
  calc projHarmonic d B * projHarmonic d B
    _ = (1 - (projPlus d B + projMinus d B)) * projHarmonic d B := rfl
    _ = projHarmonic d B := by
        rw [sub_mul, one_mul, add_mul, h1, h2, add_zero, sub_zero]

lemma projHarmonic_annihilates_d_B {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    projHarmonic d B * d = 0 ∧ d * projHarmonic d B = 0 ∧
    projHarmonic d B * B = 0 ∧ B * projHarmonic d B = 0 := by
  obtain ⟨hPp0, hPm0, h0Pp, h0Pm⟩ := projHarmonic_orthog hd hB hdBd hBdB
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc projHarmonic d B * d
      _ = (projHarmonic d B * projPlus d B) * d := by rw [mul_assoc, projPlus_mul_d hdBd]
      _ = 0 := by rw [h0Pp, zero_mul]
  · calc d * projHarmonic d B
      _ = d * (projMinus d B * projHarmonic d B) := by rw [← mul_assoc, d_mul_projMinus hdBd]
      _ = 0 := by rw [hPm0, mul_zero]
  · calc projHarmonic d B * B
      _ = (projHarmonic d B * projMinus d B) * B := by rw [mul_assoc, projMinus_mul_B hBdB]
      _ = 0 := by rw [h0Pm, zero_mul]
  · calc B * projHarmonic d B
      _ = B * (projPlus d B * projHarmonic d B) := by rw [← mul_assoc, B_mul_projPlus hBdB]
      _ = 0 := by rw [hPp0, mul_zero]

lemma projHarmonic_annihilates_kahler {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    projHarmonic d B * kahlerStructure d B = 0 ∧
    kahlerStructure d B * projHarmonic d B = 0 := by
  obtain ⟨h0d, hd0, h0B, hB0⟩ := projHarmonic_annihilates_d_B hd hB hdBd hBdB
  unfold kahlerStructure
  exact ⟨by rw [mul_sub, h0d, h0B, sub_zero], by rw [sub_mul, hd0, hB0, sub_zero]⟩

lemma bruhatWeylReflection_mul_inv {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    bruhatWeylReflection d B * bruhatWeylReflectionInv d B = 1 := by
  obtain ⟨h0J, hJ0⟩ := projHarmonic_annihilates_kahler hd hB hdBd hBdB
  unfold bruhatWeylReflection bruhatWeylReflectionInv
  rw [add_mul, mul_sub, mul_sub, projHarmonic_idem hd hB hdBd hBdB,
      h0J, hJ0, kahlerStructure_sq hd hB]
  unfold projHarmonic
  abel

lemma bruhatWeylReflectionInv_mul {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    bruhatWeylReflectionInv d B * bruhatWeylReflection d B = 1 := by
  obtain ⟨h0J, hJ0⟩ := projHarmonic_annihilates_kahler hd hB hdBd hBdB
  unfold bruhatWeylReflection bruhatWeylReflectionInv
  rw [sub_mul, mul_add, mul_add, projHarmonic_idem hd hB hdBd hBdB,
      h0J, hJ0, kahlerStructure_sq hd hB]
  unfold projHarmonic
  abel

lemma bruhatWeylReflection_pow_four {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    bruhatWeylReflection d B ^ 4 = 1 := by
  have hform : bruhatWeylReflection d B = 1 - d * B - B * d + d - B := by
    unfold bruhatWeylReflection projHarmonic hodgeLaplacian kahlerStructure projPlus projMinus
    abel
  rw [hform]
  exact InfoGeometry.Algebra.UnipotentReflexivePairFactorization.ambient_skew_fourth hd hB hdBd hBdB

lemma bruhatWeylReflection_conj_projPlus {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    bruhatWeylReflection d B * projPlus d B * bruhatWeylReflectionInv d B = projMinus d B := by
  obtain ⟨_, _, h0Pp, _⟩ := projHarmonic_orthog hd hB hdBd hBdB
  obtain ⟨_, _, _, hB0⟩ := projHarmonic_annihilates_d_B hd hB hdBd hBdB
  have h_left : bruhatWeylReflection d B * projPlus d B = -B := by
    unfold bruhatWeylReflection kahlerStructure
    rw [add_mul, sub_mul, h0Pp, d_mul_projPlus B hd, B_mul_projPlus hBdB, zero_sub, zero_add]
  rw [h_left]
  unfold bruhatWeylReflectionInv kahlerStructure
  calc -B * (projHarmonic d B - (d - B))
    _ = -(B * projHarmonic d B) + B * d - B * B := by noncomm_ring
    _ = projMinus d B := by rw [hB0, hB]; unfold projMinus; abel

lemma bruhatWeylReflection_conj_projMinus {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    bruhatWeylReflection d B * projMinus d B * bruhatWeylReflectionInv d B = projPlus d B := by
  obtain ⟨_, _, _, h0Pm⟩ := projHarmonic_orthog hd hB hdBd hBdB
  obtain ⟨_, hd0, _, _⟩ := projHarmonic_annihilates_d_B hd hB hdBd hBdB
  have h_left : bruhatWeylReflection d B * projMinus d B = d := by
    unfold bruhatWeylReflection kahlerStructure
    rw [add_mul, sub_mul, h0Pm, d_mul_projMinus hdBd, B_mul_projMinus d hB, sub_zero, zero_add]
  rw [h_left]
  unfold bruhatWeylReflectionInv kahlerStructure
  calc d * (projHarmonic d B - (d - B))
    _ = d * projHarmonic d B - d * d + d * B := by noncomm_ring
    _ = projPlus d B := by rw [hd0, hd]; unfold projPlus; abel

lemma bruhatWeylReflection_conj_d {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    bruhatWeylReflection d B * d * bruhatWeylReflectionInv d B = -B := by
  obtain ⟨_, hPm0, _, _⟩ := projHarmonic_orthog hd hB hdBd hBdB
  obtain ⟨h0d, _, _, _⟩ := projHarmonic_annihilates_d_B hd hB hdBd hBdB
  have h_left : bruhatWeylReflection d B * d = -projMinus d B := by
    unfold bruhatWeylReflection kahlerStructure projMinus
    rw [add_mul, sub_mul, h0d, hd, zero_sub, zero_add]
  rw [h_left]
  unfold bruhatWeylReflectionInv kahlerStructure
  calc -projMinus d B * (projHarmonic d B - (d - B))
    _ = -(projMinus d B * projHarmonic d B) + projMinus d B * d - projMinus d B * B := by
        noncomm_ring
    _ = -B := by rw [hPm0, projMinus_mul_d B hd, projMinus_mul_B hBdB]; abel

lemma bruhatWeylReflection_conj_B {d B : A}
    (hB : B * B = 0) (hdBd : d * B * d = d) (hBdB : B * d * B = B) :
    bruhatWeylReflection d B * B * bruhatWeylReflectionInv d B = -d :=
  InfoGeometry.Canonical.ReflexiveNilpotentFlows.weyl_swap_B hB hdBd hBdB

/-- Genuine ambient unit `bruhatWeylUnit : Aˣ` with carrier `bruhatWeylReflection d B`
    and inverse `bruhatWeylReflectionInv d B`. -/
def bruhatWeylUnit {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) : Aˣ where
  val := bruhatWeylReflection d B
  inv := bruhatWeylReflectionInv d B
  val_inv := bruhatWeylReflection_mul_inv hd hB hdBd hBdB
  inv_val := bruhatWeylReflectionInv_mul hd hB hdBd hBdB

lemma kmsModularWeight_intertwines_d {d B : A}
    (hd : d * d = 0) (hdBd : d * B * d = d) (u v : R) :
    (u * u) • (kmsModularWeight u v d B * d) =
      (v * v) • (d * kmsModularWeight u v d B) := by
  have h_left : kmsModularWeight u v d B * d = (v * v) • d := by
    unfold kmsModularWeight
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, projMinus_mul_d B hd,
        projPlus_mul_d hdBd, smul_zero, zero_add]
  have h_right : d * kmsModularWeight u v d B = (u * u) • d := by
    unfold kmsModularWeight
    rw [mul_add, mul_smul_comm, mul_smul_comm, d_mul_projMinus hdBd,
        d_mul_projPlus B hd, smul_zero, add_zero]
  rw [h_left, h_right, smul_smul, smul_smul, mul_comm (u * u) (v * v)]

lemma kmsModularWeight_intertwines_B {d B : A}
    (hB : B * B = 0) (hBdB : B * d * B = B) (u v : R) :
    (v * v) • (kmsModularWeight u v d B * B) =
      (u * u) • (B * kmsModularWeight u v d B) := by
  have h_left : kmsModularWeight u v d B * B = (u * u) • B := by
    unfold kmsModularWeight
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, projMinus_mul_B hBdB,
        projPlus_mul_B d hB, smul_zero, add_zero]
  have h_right : B * kmsModularWeight u v d B = (v * v) • B := by
    unfold kmsModularWeight
    rw [mul_add, mul_smul_comm, mul_smul_comm, B_mul_projMinus d hB,
        B_mul_projPlus hBdB, smul_zero, zero_add]
  rw [h_left, h_right, smul_smul, smul_smul, mul_comm (v * v) (u * u)]

lemma jordanProd_commutator_eq_associator (S T X : A) :
    jordanProd S (jordanProd T X) - jordanProd T (jordanProd S X) =
      jordanAssociator T X S := by
  unfold jordanAssociator jordanProd
  noncomm_ring

/-- Corrected inner-bracket order, reusing the division-free ring owner. -/
lemma jordanAssociator_eq_double_lieBracket (S T X : A) :
    jordanAssociator T X S = lieBracket (lieBracket S T) X := by
  rw [← jordanProd_commutator_eq_associator]
  exact InfoGeometry.Core.JordanAssociator.symm_operator_commutator S T X

/-- Equivalent `[X, [T, S]]` form directly from `Core.JordanAssociator.symm_associator_eq_double_commutator`. -/
lemma jordanAssociator_eq_commutator_right (S T X : A) :
    jordanAssociator T X S = lieBracket X (lieBracket T S) :=
  InfoGeometry.Core.JordanAssociator.symm_associator_eq_double_commutator T X S

/-- Square-zero does not annihilate every Jordan associator: `[d, d, B]_∘ = -(2 • d)`. -/
lemma square_zero_jordanAssociator_eq_neg_two_smul {d B : A}
    (hd : d * d = 0) (hdBd : d * B * d = d) :
    jordanAssociator d d B = -(2 • d) :=
  InfoGeometry.Core.JordanAssociator.symm_associator_square_zero_inner_inverse hd hdBd

/-- Tracial functional boundary intertwining law for `kmsModularWeight u v d B`,
    reusing `InfoGeometry.Canonical.PeirceWeightedTrace.weighted_trace_boundary`. -/
lemma kmsModularWeight_trace_boundary
    (τ : InfoGeometry.NCG.TracialFunctional R A) {d B : A}
    (hd : d * d = 0) (hB : B * B = 0)
    (hdBd : d * B * d = d) (hBdB : B * d * B = B) (u v : R) (x : A) :
    (u * u) * InfoGeometry.OperatorAlgebra.TracialCARDensity.weighted τ
      (kmsModularWeight u v d B) (d * x) =
      (v * v) * InfoGeometry.OperatorAlgebra.TracialCARDensity.weighted τ
        (kmsModularWeight u v d B) (x * d) ∧
    (v * v) * InfoGeometry.OperatorAlgebra.TracialCARDensity.weighted τ
      (kmsModularWeight u v d B) (B * x) =
      (u * u) * InfoGeometry.OperatorAlgebra.TracialCARDensity.weighted τ
        (kmsModularWeight u v d B) (x * B) :=
  InfoGeometry.Canonical.PeirceWeightedTrace.weighted_trace_boundary
    τ hd hB hdBd hBdB (u * u) (v * v) x

/-!
## 4. The Five-Pillar Geometric–Operator Synthesis Theorem
-/

/-- A package of support, polynomial, shear, weighted-intertwining and
symmetrized-product identities. The title does not assert geometric or
operator-analytic structures beyond the displayed equations. -/
theorem five_pillar_geometry_operator_synthesis [StarRing A]
    {d B : A} (hG : IsGeometricPeircePair d B) (u v : R) (S T X : A) :
    let P_pos := projPlus d B
    let P_neg := projMinus d B
    let P_0 := projHarmonic d B
    let Δ := hodgeLaplacian d B
    let Γ := ehresmannCurvature d B
    let J₄ := kahlerStructure d B
    let ω₃ := trialityOperator d B
    let ω₆ := hexalityOperator d B
    let w_J := bruhatWeylReflection d B
    let w_J_inv := bruhatWeylReflectionInv d B
    let ρ := kmsModularWeight u v d B
    (P_pos + P_neg + P_0 = 1 ∧
     star P_pos = P_pos ∧ star P_neg = P_neg ∧ star P_0 = P_0 ∧
     lieBracket P_pos Γ = 0 ∧ lieBracket P_neg Γ = 0 ∧
     lieBracket Γ d = 2 • d ∧ lieBracket Γ B = -(2 • B)) ∧
    (Γ * Γ - Δ = 0 ∧
     J₄ * J₄ + Δ = 0 ∧
     ω₃ * ω₃ + ω₃ + Δ = 0 ∧ ω₃ ^ 3 = Δ ∧
     ω₆ * ω₆ - ω₆ + Δ = 0 ∧ ω₆ ^ 3 = -Δ ∧ ω₆ ^ 6 = Δ ∧
     (-J₄) * ω₃ = Δ + d) ∧
    ((1 + d) * (1 - B) * (1 + d) = w_J ∧
     w_J * w_J_inv = 1 ∧ w_J_inv * w_J = 1 ∧ w_J ^ 4 = 1 ∧
     w_J * P_pos * w_J_inv = P_neg ∧
     w_J * P_neg * w_J_inv = P_pos ∧
     w_J * d * w_J_inv = -B ∧ w_J * B * w_J_inv = -d) ∧
    ((u * u) • (ρ * d) = (v * v) • (d * ρ) ∧
     (v * v) • (ρ * B) = (u * u) • (B * ρ)) ∧
    (jordanProd S (jordanProd T X) - jordanProd T (jordanProd S X) =
       jordanAssociator T X S ∧
     jordanAssociator T X S = lieBracket (lieBracket S T) X ∧
     jordanAssociator T X S = lieBracket X (lieBracket T S) ∧
     jordanAssociator d d B = -(2 • d)) := by
  rcases hG with ⟨hd, hB, hdBd, hBdB, hsa_plus, hsa_minus⟩
  exact ⟨⟨hodge_partition_of_unity d B, hsa_plus, hsa_minus, star_projHarmonic hsa_plus hsa_minus,
          lieBracket_projPlus_ehresmann hd hB hdBd, lieBracket_projMinus_ehresmann hd hB hBdB,
          lieBracket_ehresmann_d hd hdBd, lieBracket_ehresmann_B hB hBdB⟩,
         ⟨ehresmannCurvature_sq_sub_laplacian hd hB hdBd hBdB, kahlerStructure_sq_add_laplacian hd hB,
          trialityOperator_quad_law hd hB hdBd hBdB, trialityOperator_cube hd hB hdBd hBdB,
          hexalityOperator_quad_law hd hB hdBd hBdB, hexalityOperator_cube hd hB hdBd hBdB,
          hexalityOperator_pow_six hd hB hdBd hBdB, kahler_triality_transvection_recovery hd hB hdBd⟩,
         ⟨bruhat_triple_product hd hdBd, bruhatWeylReflection_mul_inv hd hB hdBd hBdB,
          bruhatWeylReflectionInv_mul hd hB hdBd hBdB, bruhatWeylReflection_pow_four hd hB hdBd hBdB,
          bruhatWeylReflection_conj_projPlus hd hB hdBd hBdB,
          bruhatWeylReflection_conj_projMinus hd hB hdBd hBdB,
          bruhatWeylReflection_conj_d hd hB hdBd hBdB, bruhatWeylReflection_conj_B hB hdBd hBdB⟩,
         ⟨kmsModularWeight_intertwines_d hd hdBd u v, kmsModularWeight_intertwines_B hB hBdB u v⟩,
         ⟨jordanProd_commutator_eq_associator S T X, jordanAssociator_eq_double_lieBracket S T X,
          jordanAssociator_eq_commutator_right S T X,
          square_zero_jordanAssociator_eq_neg_two_smul hd hdBd⟩⟩

end AbstractFivePillarSynthesis

/-!
## 5. Noncommutative Matrix Operator Realization (`Matrix (Fin 2) (Fin 2) ℤ`)
-/

section NoncommutativeMatrixRealization

open Matrix

abbrev Mat2Z := Matrix (Fin 2) (Fin 2) ℤ

/-- Forward nilpotent matrix root of zero `d = E₀₁` in `Matrix (Fin 2) (Fin 2) ℤ`. -/
def matD : Mat2Z := !![0, 1; 0, 0]

/-- Backward nilpotent matrix root of zero `B = E₁₀` in `Matrix (Fin 2) (Fin 2) ℤ`. -/
def matB : Mat2Z := !![0, 0; 1, 0]

/-- Oblique non-normal idempotent `P_D = E₀₀ + E₀₁` (`P_D² = P_D`, `P_Dᵀ ≠ P_D`). -/
def matPD : Mat2Z := !![1, 1; 0, 0]

/-- Orthogonal range projection `P_M = E₀₀` (`P_M² = P_M`, `P_Mᵀ = P_M`). -/
def matPM : Mat2Z := !![1, 0; 0, 0]

/-- Concrete verification of all five pillars and Breakthrough 1 on `Matrix (Fin 2) (Fin 2) ℤ`:
    non-commutativity `matD * matB ≠ matB * matD`, non-normality `matPD * matPM ≠ matPM * matPD`,
    Cartan anomaly anticommutation `{Γ_S, χ} = 0`, Tits–Bruhat–Moufang inversion, and KMS
    modular intertwining. -/
theorem mat2Z_five_pillar_witness :
    matD * matB ≠ matB * matD ∧
    matPD * matPM ≠ matPM * matPD ∧
    IsIdempotentElem matPD ∧
    jordanProd (spectralCartanInvolution matPD) (cartanAnomaly matPD matPM) = 0 ∧
    (1 + matD) * (1 - matB) * (1 + matD) = bruhatWeylReflection matD matB ∧
    bruhatWeylReflection matD matB * projPlus matD matB * bruhatWeylReflectionInv matD matB =
      projMinus matD matB ∧
    ((2 : ℤ) * 2) • (kmsModularWeight (2 : ℤ) (3 : ℤ) matD matB * matD) =
      ((3 : ℤ) * 3) • (matD * kmsModularWeight (2 : ℤ) (3 : ℤ) matD matB) := by
  refine ⟨by decide, by decide,
          by change matPD * matPD = matPD; decide,
          by decide, by decide, by decide, by decide⟩

/-- Without Drazin inverse hypotheses, `kantorTripleDefect X D` is not nilpotent:
    at `X = 1, D = 0` in `Mat2Z`, `kantorTripleDefect 1 0 = 1` and its square is non-zero. -/
theorem mat2Z_kantorDefect_not_nilpotent_without_drazin :
    kantorTripleDefect (1 : Mat2Z) 0 = 1 ∧
    (kantorTripleDefect (1 : Mat2Z) 0) ^ 2 ≠ 0 :=
  ⟨by decide, by decide⟩

/-- Refutation of the `Φ₂(t) = t + 1` misidentification: `Γ = ehresmannCurvature matD matB`
    satisfies the involution identity `Γ² - Δ = 0` on the active support `Δ`, whereas
    `Γ + Δ ≠ 0`. -/
theorem mat2Z_ehresmann_not_phi2 :
    ehresmannCurvature matD matB * ehresmannCurvature matD matB -
      hodgeLaplacian matD matB = 0 ∧
    ehresmannCurvature matD matB + hodgeLaplacian matD matB ≠ 0 :=
  ⟨by decide, by decide⟩

/-- Explicit integer-matrix witness (`T = matPM = E₀₀`, `S = matD = E₀₁`, `X = 1 - matPM = E₁₁`)
    confirming the exact sign `jordanAssociator T X S = [[S, T], X]` and refuting the reversed
    inner-bracket sign `[[T, S], X]` over `ℤ`. -/
theorem mat2Z_jordanAssociator_sign_refutation :
    jordanAssociator matPM (1 - matPM) matD =
      lieBracket (lieBracket matD matPM) (1 - matPM) ∧
    jordanAssociator matPM (1 - matPM) matD ≠
      lieBracket (lieBracket matPM matD) (1 - matPM) :=
  ⟨by decide, by decide⟩

abbrev Mat3Z := Matrix (Fin 3) (Fin 3) ℤ

/-- Forward square-zero `3 × 3` matrix `E₀₁` with non-zero harmonic complement `E₂₂`. -/
def mat3D : Mat3Z := !![0, 1, 0; 0, 0, 0; 0, 0, 0]

/-- Backward square-zero `3 × 3` matrix `E₁₀` with non-zero harmonic complement `E₂₂`. -/
def mat3B : Mat3Z := !![0, 0, 0; 1, 0, 0; 0, 0, 0]

/-- Integral `3 × 3` proper-support witness (`Δ ≠ 1`):
    1. `Δ = hodgeLaplacian mat3D mat3B ≠ 1`, so `ω₃ ^ 3 = Δ ≠ 1`,
    2. the ambient harmonic-completed Weyl reflection `w_J` still satisfies `w_J ^ 4 = 1`,
    3. `(-J₄) * ω₃ = Δ + mat3D` recovers the forward transvection on the active support, and
    4. square-zero does not annihilate the Jordan associator: `[mat3D, mat3D, mat3B]_∘ = -(2 • mat3D) ≠ 0`. -/
theorem mat3Z_proper_support_weyl_cyclotomic_witness :
    hodgeLaplacian mat3D mat3B ≠ (1 : Mat3Z) ∧
    trialityOperator mat3D mat3B ^ 3 ≠ (1 : Mat3Z) ∧
    bruhatWeylReflection mat3D mat3B ^ 4 = (1 : Mat3Z) ∧
    (-kahlerStructure mat3D mat3B) * trialityOperator mat3D mat3B =
      hodgeLaplacian mat3D mat3B + mat3D ∧
    jordanAssociator mat3D mat3D mat3B = -(2 • mat3D) ∧
    jordanAssociator mat3D mat3D mat3B ≠ 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end NoncommutativeMatrixRealization

/-!
## 5B. Breakthrough 4: Split-Octonion Left-Multiplication Lift & Exact Obstruction Boundaries
-/

noncomputable section Breakthrough4AlternativeObstructionBoundaries

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Lie.SplitOctonionNonmultiplicativity
open InfoGeometry.Algebra.ZornColorOperatorCoordinates
open InfoGeometry.Canonical.GLSupermatrixGradedLie

/-- The left-multiplication operator lift on `CanonicalZorn` has non-zero homomorphism
    curvature (associator): there exist imaginary split octonions `X, Y, Z` with
    `(X * Y) * Z ≠ X * (Y * Z)` and `L_X ∘ L_Y ≠ L_{X * Y}`. -/
theorem zorn_leftMul_nonmultiplicativity_boundary :
    (∃ (X Y : Imaginary) (h : realZornTrace (X.1 * Y.1) = 0),
      imaginaryLeftMul X * imaginaryLeftMul Y ≠
      imaginaryLeftMul (⟨X.1 * Y.1, (mem_imaginary_iff (X.1 * Y.1)).mpr h⟩ : Imaginary)) ∧
    (∃ (X Y Z : Imaginary), (X.1 * Y.1) * Z.1 ≠ X.1 * (Y.1 * Z.1)) :=
  ⟨nonmultiplicativity_obstruction, associator_obstruction⟩

/-- Dimensional boundary of the 7-generator left Clifford representation on `CanonicalZorn`:
    `finrank ℝ (CliffordAlgebra leftCliffordQuadratic) = 128`, whereas
    `finrank ℝ (Module.End ℝ CanonicalZorn) = 64`, so the full representation is not injective. -/
theorem zorn_clifford_128_to_64_noninjective_boundary :
    Module.finrank ℝ (CliffordAlgebra leftCliffordQuadratic) = 128 ∧
    Module.finrank ℝ (Module.End ℝ CanonicalZorn) = 64 ∧
    ¬ Function.Injective splitOctonionLeftCliffordRepresentation :=
  ⟨leftClifford_finrank, canonicalZornEnd_finrank,
   splitOctonionLeftCliffordRepresentation_not_injective⟩

/-- Exact `gl(3|1)` vs raw CAR odd-space boundary: `gl(3|1)` has a non-central odd
    superbracket, so no homogeneous-bracket-preserving linear map `SuperMatrix 3 1 R →ₗ[R] Op R`
    sending the odd part into the raw 6D CAR `oddPart` can be injective. -/
theorem zorn_gl31_car_odd_obstruction_boundary {R : Type*} [CommRing R] [Nontrivial R]
    (F : SuperMatrix 3 1 R →ₗ[R] Op R)
    (hodd : ∀ X, IsHomogeneous .odd X → F X ∈ oddPart)
    (hbracket : ∀ (p q : Parity) (X Y : SuperMatrix 3 1 R),
      IsHomogeneous p X → IsHomogeneous q Y →
      F (ringSuperbracket p q X Y) = ringSuperbracket p q (F X) (F Y)) :
    (∃ X Y Z : SuperMatrix 3 1 R,
      IsHomogeneous .odd X ∧ IsHomogeneous .odd Y ∧ IsHomogeneous .even Z ∧
      ringSuperbracket .even .even (ringSuperbracket .odd .odd X Y) Z ≠ 0) ∧
    ¬ Function.Injective F :=
  ⟨gl31_odd_bracket_noncentral, not_faithful_gl31_with_CAR_odd F hodd hbracket⟩

end Breakthrough4AlternativeObstructionBoundaries

/-!
## 6. Lean 4 Meta Epistemic Compiler Schedule & Certified Archetype Registration

We encode the 5-node Causal Poset from Section 2 (`UnifiedPillarArchetype`) and
certify all 5 pillars through the Lean 4 Meta Epistemic Compiler
(`InfoGeometry.MetaCompiler.TypedArchetype`, `#register_archetype`, `#audit_archetype`,
and `InfoGeometry.MetaCompiler.executable_certified_compilation`).
-/

section MetaEpistemicCompilerCertification

open InfoGeometry.MetaCompiler
open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.ProofCarryingSchedule

/-- Causal poset of the 5 Unified Geometric–Operator Pillars. -/
inductive UnifiedPillarArchetype where
  | nonNormalOperatorCalculus
  | hodgeDiracGrassmannianGeometry
  | bruhatMoebiusKmsModularDynamics
  | alternativeLiftAndJordanE6
  | machineCheckedFivePillarSynthesis
  deriving DecidableEq, Repr, Inhabited

namespace UnifiedPillarArchetype

private def equivFin : UnifiedPillarArchetype ≃ Fin 5 where
  toFun
    | .nonNormalOperatorCalculus => 0
    | .hodgeDiracGrassmannianGeometry => 1
    | .bruhatMoebiusKmsModularDynamics => 2
    | .alternativeLiftAndJordanE6 => 3
    | .machineCheckedFivePillarSynthesis => 4
  invFun
    | 0 => .nonNormalOperatorCalculus
    | 1 => .hodgeDiracGrassmannianGeometry
    | 2 => .bruhatMoebiusKmsModularDynamics
    | 3 => .alternativeLiftAndJordanE6
    | _ => .machineCheckedFivePillarSynthesis
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance instFintype : Fintype UnifiedPillarArchetype :=
  Fintype.ofEquiv (Fin 5) equivFin.symm

/-- Exact diamond causal poset from Section 2:
    `1 (nonNormalOperatorCalculus) → 2 (hodgeDiracGrassmannianGeometry) → {3 (bruhatMoebiusKmsModularDynamics), 4 (alternativeLiftAndJordanE6)} → 5 (machineCheckedFivePillarSynthesis)`. -/
def prerequisites : UnifiedPillarArchetype → Finset UnifiedPillarArchetype
  | .nonNormalOperatorCalculus => {.nonNormalOperatorCalculus}
  | .hodgeDiracGrassmannianGeometry =>
      {.nonNormalOperatorCalculus, .hodgeDiracGrassmannianGeometry}
  | .bruhatMoebiusKmsModularDynamics =>
      {.nonNormalOperatorCalculus, .hodgeDiracGrassmannianGeometry,
       .bruhatMoebiusKmsModularDynamics}
  | .alternativeLiftAndJordanE6 =>
      {.nonNormalOperatorCalculus, .hodgeDiracGrassmannianGeometry,
       .alternativeLiftAndJordanE6}
  | .machineCheckedFivePillarSynthesis =>
      {.nonNormalOperatorCalculus, .hodgeDiracGrassmannianGeometry,
       .bruhatMoebiusKmsModularDynamics, .alternativeLiftAndJordanE6,
       .machineCheckedFivePillarSynthesis}

instance instPartialOrder : PartialOrder UnifiedPillarArchetype where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro a b
    cases a <;> cases b <;> decide

instance instDecidableLE : DecidableLE UnifiedPillarArchetype := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

instance instDecidableLT : DecidableLT UnifiedPillarArchetype := fun a b =>
  decidable_of_iff (a ≤ b ∧ ¬ b ≤ a) lt_iff_le_not_ge.symm

theorem branches_incomparable :
    ¬ (bruhatMoebiusKmsModularDynamics ≤ alternativeLiftAndJordanE6) ∧
    ¬ (alternativeLiftAndJordanE6 ≤ bruhatMoebiusKmsModularDynamics) := by
  decide

def canonicalPending : List UnifiedPillarArchetype :=
  [.machineCheckedFivePillarSynthesis, .alternativeLiftAndJordanE6,
   .bruhatMoebiusKmsModularDynamics, .hodgeDiracGrassmannianGeometry,
   .nonNormalOperatorCalculus]

def canonicalSchedule : List UnifiedPillarArchetype :=
  [.nonNormalOperatorCalculus, .hodgeDiracGrassmannianGeometry,
   .alternativeLiftAndJordanE6, .bruhatMoebiusKmsModularDynamics,
   .machineCheckedFivePillarSynthesis]

theorem canonicalPending_nodup : canonicalPending.Nodup := by decide

theorem canonicalPending_univ : canonicalPending.toFinset = Finset.univ := by decide

theorem compile_canonicalPending :
    compile (∅ : Finset UnifiedPillarArchetype) canonicalPending =
      some canonicalSchedule := by
  decide

end UnifiedPillarArchetype

/-- Proved `TypedArchetype` for Node 1: Non-Normal Operator Calculus (Kantor Defect & Cartan Anomaly). -/
def pillar1NonNormalCalculus : TypedArchetype (Mat2Z × Mat2Z) .proved where
  name := `InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance.pillar1NonNormalCalculus
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun p =>
    kantorTripleDefect p.1 p.2 = p.1 * (1 - p.2 * p.1) ∧
    jordanProd (spectralCartanInvolution matPD) (cartanAnomaly matPD p.1) = 0
  evidence := fun p =>
    ⟨(kantorTripleDefect_eq_nilpotent_residual p.1 p.2).1,
     cartanAnomaly_anticommutes_spectralInvolution mat2Z_five_pillar_witness.2.2.1 p.1⟩

/-- Node 2 certifies only the displayed finite support and polynomial identities. -/
def pillar2HodgeDiracKahler : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance.pillar2HodgeDiracKahler
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    projPlus matD matB + projMinus matD matB + projHarmonic matD matB = 1 ∧
    lieBracket (ehresmannCurvature matD matB) matD = 2 • matD ∧
    kahlerStructure matD matB * kahlerStructure matD matB + hodgeLaplacian matD matB = 0
  evidence := fun _ =>
    ⟨hodge_partition_of_unity matD matB,
     by decide,
     by decide⟩

/-- Node 3 certifies the three-shear and weighted-support equations, not KMS dynamics. -/
def pillar3BruhatKmsModular : TypedArchetype (ℤ × ℤ) .proved where
  name := `InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance.pillar3BruhatKmsModular
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun uv =>
    (1 + matD) * (1 - matB) * (1 + matD) = bruhatWeylReflection matD matB ∧
    (uv.1 * uv.1) • (kmsModularWeight uv.1 uv.2 matD matB * matD) =
      (uv.2 * uv.2) • (matD * kmsModularWeight uv.1 uv.2 matD matB)
  evidence := fun uv =>
    ⟨mat2Z_five_pillar_witness.2.2.2.2.1,
     kmsModularWeight_intertwines_d (by decide) (by decide) uv.1 uv.2⟩

/-- Node 4 certifies the associative Jordan-operator identity. Its historical
name does not supply an exceptional Lie-algebra construction. -/
def pillar4JordanCartanE6 : TypedArchetype (Mat2Z × Mat2Z × Mat2Z) .proved where
  name := `InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance.pillar4JordanCartanE6
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun t =>
    jordanProd t.1 (jordanProd t.2.1 t.2.2) - jordanProd t.2.1 (jordanProd t.1 t.2.2) =
      jordanAssociator t.2.1 t.2.2 t.1 ∧
    jordanAssociator t.2.1 t.2.2 t.1 = lieBracket (lieBracket t.1 t.2.1) t.2.2
  evidence := fun t =>
    ⟨jordanProd_commutator_eq_associator t.1 t.2.1 t.2.2,
     jordanAssociator_eq_double_lieBracket t.1 t.2.1 t.2.2⟩

/-- Proved `TypedArchetype` for Node 5: Machine-Checked Five-Pillar Synthesis. -/
def pillar5UnifiedSynthesis : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance.pillar5UnifiedSynthesis
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    matD * matB ≠ matB * matD ∧
    bruhatWeylReflection matD matB * projPlus matD matB * bruhatWeylReflectionInv matD matB =
      projMinus matD matB
  evidence := fun _ =>
    ⟨mat2Z_five_pillar_witness.1,
     mat2Z_five_pillar_witness.2.2.2.2.2.1⟩

#register_archetype pillar1NonNormalCalculus
#register_archetype pillar2HodgeDiracKahler
#register_archetype pillar3BruhatKmsModular
#register_archetype pillar4JordanCartanE6
#register_archetype pillar5UnifiedSynthesis

#audit_archetype pillar1NonNormalCalculus
#audit_archetype pillar2HodgeDiracKahler
#audit_archetype pillar3BruhatKmsModular
#audit_archetype pillar4JordanCartanE6
#audit_archetype pillar5UnifiedSynthesis

/-- Cumulative target statement map on `UnifiedPillarArchetype` along the causal poset
    `1 (nonNormalOperatorCalculus) → 2 (hodgeDiracGrassmannianGeometry) → {3 (bruhatMoebiusKmsModularDynamics), 4 (alternativeLiftAndJordanE6)} → 5 (machineCheckedFivePillarSynthesis)`. -/
def unifiedPillarStatement : UnifiedPillarArchetype → Prop
  | .nonNormalOperatorCalculus =>
      ∀ p : Mat2Z × Mat2Z, pillar1NonNormalCalculus.claim p
  | .hodgeDiracGrassmannianGeometry =>
      (∀ p : Mat2Z × Mat2Z, pillar1NonNormalCalculus.claim p) ∧
      pillar2HodgeDiracKahler.claim ()
  | .bruhatMoebiusKmsModularDynamics =>
      ((∀ p : Mat2Z × Mat2Z, pillar1NonNormalCalculus.claim p) ∧
       pillar2HodgeDiracKahler.claim ()) ∧
      ∀ uv : ℤ × ℤ, pillar3BruhatKmsModular.claim uv
  | .alternativeLiftAndJordanE6 =>
      ((∀ p : Mat2Z × Mat2Z, pillar1NonNormalCalculus.claim p) ∧
       pillar2HodgeDiracKahler.claim ()) ∧
      ∀ t : Mat2Z × Mat2Z × Mat2Z, pillar4JordanCartanE6.claim t
  | .machineCheckedFivePillarSynthesis =>
      (((∀ p : Mat2Z × Mat2Z, pillar1NonNormalCalculus.claim p) ∧
        pillar2HodgeDiracKahler.claim ()) ∧
       ∀ uv : ℤ × ℤ, pillar3BruhatKmsModular.claim uv) ∧
      (((∀ p : Mat2Z × Mat2Z, pillar1NonNormalCalculus.claim p) ∧
        pillar2HodgeDiracKahler.claim ()) ∧
       ∀ t : Mat2Z × Mat2Z × Mat2Z, pillar4JordanCartanE6.claim t) ∧
      pillar5UnifiedSynthesis.claim ()

/-- Prerequisite-consuming `ProofRules` for `unifiedPillarStatement`: every non-root node
    explicitly invokes `hprereq` on its strict causal predecessors (`b < target`) before
    discharging its own `TypedArchetype` claim. -/
lemma unifiedPillarRules : ProofRules unifiedPillarStatement := by
  intro target hprereq
  cases target with
  | nonNormalOperatorCalculus =>
      exact fun p => pillar1NonNormalCalculus.discharge p
  | hodgeDiracGrassmannianGeometry =>
      exact ⟨hprereq .nonNormalOperatorCalculus (by decide),
             pillar2HodgeDiracKahler.discharge ()⟩
  | bruhatMoebiusKmsModularDynamics =>
      exact ⟨hprereq .hodgeDiracGrassmannianGeometry (by decide),
             fun uv => pillar3BruhatKmsModular.discharge uv⟩
  | alternativeLiftAndJordanE6 =>
      exact ⟨hprereq .hodgeDiracGrassmannianGeometry (by decide),
             fun t => pillar4JordanCartanE6.discharge t⟩
  | machineCheckedFivePillarSynthesis =>
      exact ⟨hprereq .bruhatMoebiusKmsModularDynamics (by decide),
             hprereq .alternativeLiftAndJordanE6 (by decide),
             pillar5UnifiedSynthesis.discharge ()⟩

/-- Certified execution of the Meta Epistemic Compiler on the 5-node `UnifiedPillarArchetype` poset. -/
theorem unified_five_pillar_executable_certified_compilation :
    ∃ schedule : List UnifiedPillarArchetype,
      compile ∅ UnifiedPillarArchetype.canonicalPending = some schedule ∧
      ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧
      schedule.length = Fintype.card UnifiedPillarArchetype ∧
      schedule.toFinset = Finset.univ ∧
      ∀ target, unifiedPillarStatement target :=
  executable_certified_compilation
    unifiedPillarStatement
    unifiedPillarRules
    UnifiedPillarArchetype.canonicalPending
    UnifiedPillarArchetype.canonicalPending_nodup
    UnifiedPillarArchetype.canonicalPending_univ

end MetaEpistemicCompilerCertification

end InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance
