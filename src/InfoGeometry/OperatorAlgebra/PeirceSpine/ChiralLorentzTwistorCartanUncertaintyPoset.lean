/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ParaKahlerBregmanModularNoetherPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornPeirceTetradPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorCornerAnomaly
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceMaurerCartanCurvatureWitness
import InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty

/-!
# 10-Stage Causal Poset of the Chiral Dual Real Lorentz Representation, Poincaré–SUSY Closure, Super-Grassmannian Para-Kähler Twistor–Amplituhedron Geometry, Élie Cartan Spin-Connection Gravity Created by Uncertainty, and the Higher-Grade Uncertainty Anomaly (`CL₁ → CL₁₀`)

This module executes the Epistemic Compiler (`solve et coagula`) on the mathematical synthesis of:
- the **chiral dual real representation of the Lorentz algebra** (`Φ = N_+ + N_-` vs. `J = N_+ - N_-`
  intertwined by the chiral grading `S_P = 2P - 1`),
- the **Poincaré semidirect translation ideal and `ℤ₂`-graded SUSY superalgebra** (`{N_+, N_-} = V`),
- the **super-Grassmannian para-Kähler geometry, twistor incidence, and positive amplituhedron**
  (`seedPositivityForm`),
- the **uncertainty commutator `Σ = [N_+, N_-]` as the necessary and sufficient creator of both the
  emergent spacetime metric `V = S_P Σ` and Élie Cartan spin-connection torsion/curvature**, and
- the **anomaly of the uncertainty commutator as a generator in the higher grade (`±2`) of the
  5-graded Kantor–Koecher–Tits symmetry closure group** (`Σ_{A,C} N_+(Z) - Σ_{Z,C} N_+(A)` and
  `kantorGp2`/`kantorGm2` bilateral reconstruction).

All definitions, lemmas, and theorems are formulated and proved over an arbitrary non-commutative
associative ring `[Ring B]` (with `[StarRing B]` for Hermitian amplituhedron positivity and
`NormalizedState H` for the Hilbert-space Cramér–Rao commutator uncertainty bound), with zero
scalar, diagonal, or commuting surrogates and zero `sorry`s.

## Three-Bucket Audit Classification

- **BUCKET 1 (`KERNEL_PROVED`):**
  All 10 stages `CL₁ → CL₁₀` (`ChiralLorentzTwistorCartanStage`), chiral dual real Lorentz
  representation, Poincaré–SUSY superalgebra, super-Grassmannian para-Kähler twistor incidence,
  Élie Cartan spin-connection torsion/curvature, and higher-grade uncertainty anomaly in `[Ring B]`.
- **BUCKET 2 (`EXPLICIT_HYPOTHESIS`):**
  Idempotency `hP : P * P = P` (or nilpotency/von Neumann regularity `N_+² = 0`, `N_+ N_+^* N_+ = N_+`)
  and `NormalizedState H` for Hilbert-space Cramér–Rao commutator bounds.
- **BUCKET 3 (`OPEN_HORIZON`):**
  Non-perturbative all-loop Grassmannian amplituhedron volume integration over continuous momentum twistors.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

/-! ## 1. The 10-Stage Acyclic Causal Poset (`ChiralLorentzTwistorCartanStage : CL₁ → CL₁₀`) -/

/-- The 10-stage causal poset (`CL₁ → CL₁₀`) from the primordial chiral cut to the master
synthesis of Lorentz–Poincaré–SUSY, super-Grassmannian para-Kähler twistor–amplituhedron geometry,
Élie Cartan spin-connection curvature created by uncertainty, and the higher-grade (`±2`)
uncertainty anomaly. -/
inductive ChiralLorentzTwistorCartanStage : Type
  | CL1_PrimordialChiralCutAndFourfoldPeirceAnatomy
  | CL2_ChiralDualRealLorentzRepresentation
  | CL3_PoincareSemidirectAndSUSYSuperalgebra
  | CL4_SuperGrassmannianParaKahlerStructure
  | CL5_TwistorIncidenceAndPositiveAmplituhedron
  | CL6_UncertaintyAsCreatorOfMetricAndSpinCurvature
  | CL7_ElieCartanTorsionAndSpinConnectionGravity
  | CL8_HigherGradeUncertaintyAnomalyInSymmetryClosure
  | CL9_RecursiveMetaTowerAndHilbertCramerRaoCurvatureBound
  | CL10_MasterChiralLorentzTwistorCartanUncertaintySynthesis
  deriving DecidableEq, Repr, Inhabited

namespace ChiralLorentzTwistorCartanStage

/-- Topological rank (`0` through `9`) of each stage in `ChiralLorentzTwistorCartanStage`. -/
def rank : ChiralLorentzTwistorCartanStage → ℕ
  | .CL1_PrimordialChiralCutAndFourfoldPeirceAnatomy          => 0
  | .CL2_ChiralDualRealLorentzRepresentation                  => 1
  | .CL3_PoincareSemidirectAndSUSYSuperalgebra                => 2
  | .CL4_SuperGrassmannianParaKahlerStructure                 => 3
  | .CL5_TwistorIncidenceAndPositiveAmplituhedron             => 4
  | .CL6_UncertaintyAsCreatorOfMetricAndSpinCurvature          => 5
  | .CL7_ElieCartanTorsionAndSpinConnectionGravity            => 6
  | .CL8_HigherGradeUncertaintyAnomalyInSymmetryClosure       => 7
  | .CL9_RecursiveMetaTowerAndHilbertCramerRaoCurvatureBound  => 8
  | .CL10_MasterChiralLorentzTwistorCartanUncertaintySynthesis => 9

/-- The topological rank map on `ChiralLorentzTwistorCartanStage` is injective. -/
theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

instance instLinearOrder : LinearOrder ChiralLorentzTwistorCartanStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed cover relation `u ≺ v` in the 10-stage poset (`CL₁ → CL₁₀`). -/
inductive causalEdge : ChiralLorentzTwistorCartanStage → ChiralLorentzTwistorCartanStage → Prop
  | cl1_to_cl2 :
      causalEdge .CL1_PrimordialChiralCutAndFourfoldPeirceAnatomy
        .CL2_ChiralDualRealLorentzRepresentation
  | cl2_to_cl3 :
      causalEdge .CL2_ChiralDualRealLorentzRepresentation
        .CL3_PoincareSemidirectAndSUSYSuperalgebra
  | cl3_to_cl4 :
      causalEdge .CL3_PoincareSemidirectAndSUSYSuperalgebra
        .CL4_SuperGrassmannianParaKahlerStructure
  | cl4_to_cl5 :
      causalEdge .CL4_SuperGrassmannianParaKahlerStructure
        .CL5_TwistorIncidenceAndPositiveAmplituhedron
  | cl5_to_cl6 :
      causalEdge .CL5_TwistorIncidenceAndPositiveAmplituhedron
        .CL6_UncertaintyAsCreatorOfMetricAndSpinCurvature
  | cl6_to_cl7 :
      causalEdge .CL6_UncertaintyAsCreatorOfMetricAndSpinCurvature
        .CL7_ElieCartanTorsionAndSpinConnectionGravity
  | cl7_to_cl8 :
      causalEdge .CL7_ElieCartanTorsionAndSpinConnectionGravity
        .CL8_HigherGradeUncertaintyAnomalyInSymmetryClosure
  | cl8_to_cl9 :
      causalEdge .CL8_HigherGradeUncertaintyAnomalyInSymmetryClosure
        .CL9_RecursiveMetaTowerAndHilbertCramerRaoCurvatureBound
  | cl9_to_cl10 :
      causalEdge .CL9_RecursiveMetaTowerAndHilbertCramerRaoCurvatureBound
        .CL10_MasterChiralLorentzTwistorCartanUncertaintySynthesis

/-- Every directed causal edge in `ChiralLorentzTwistorCartanStage` strictly increases topological rank. -/
theorem causalEdge_strict_rank {u v : ChiralLorentzTwistorCartanStage}
    (h : causalEdge u v) : rank u < rank v := by
  cases h <;> decide

/-- Transitive chains of causal edges in `ChiralLorentzTwistorCartanStage` strictly increase topological rank. -/
theorem transGen_causalEdge_strict_rank {u v : ChiralLorentzTwistorCartanStage}
    (h : Relation.TransGen causalEdge u v) : rank u < rank v := by
  induction h with
  | single hEdge => exact causalEdge_strict_rank hEdge
  | tail _ hEdge ih => exact Nat.lt_trans ih (causalEdge_strict_rank hEdge)

/-- Strict acyclicity of the 10-stage causal poset (`CL₁ → CL₁₀`). -/
theorem causalEdge_acyclic (u : ChiralLorentzTwistorCartanStage) :
    ¬ Relation.TransGen causalEdge u u := by
  intro hCycle
  exact Nat.lt_irrefl (rank u) (transGen_causalEdge_strict_rank hCycle)

end ChiralLorentzTwistorCartanStage

/-! ## 2. Stage `CL₁`: Primordial Chiral Cut (`P` vs. `1 - P`) & Fourfold Peirce Anatomy -/

/-- **Stage `CL₁` (`archetype_CL1_primordial_chiral_cut_and_fourfold_peirce_anatomy`)**:
For any idempotent `P * P = P` in a non-commutative ring `B` and any `A, C, X : B`:
1. **Fourfold Peirce Partition**:
   `P * X * P + conePlus P X + coneMinus P X + (1 - P) * X * (1 - P) = X` and
   `evenGrade P X + oddGrade P X = X`,
2. **Chiral Grading Involution (`S_P = 2P - 1`)**:
   `invS P * invS P = 1`, `invS P * evenGrade P X * invS P = evenGrade P X`, and
   `invS P * oddGrade P X * invS P = -oddGrade P X`,
3. **Nilpotent Chiral Cones & Boost Eigenvalue Ladder**:
   `conePlus P A * conePlus P X = 0`, `coneMinus P C * coneMinus P X = 0`,
   `comm (invS P) (conePlus P A) = (2 : ℤ) • conePlus P A`, and
   `comm (invS P) (coneMinus P C) = -((2 : ℤ) • coneMinus P C)`. -/
theorem archetype_CL1_primordial_chiral_cut_and_fourfold_peirce_anatomy
    {P : B} (hP : P * P = P) (A C X : B) :
    P * X * P + conePlus P X + coneMinus P X + (1 - P) * X * (1 - P) = X ∧
    invS P * invS P = 1 ∧
    invS P * evenGrade P X * invS P = evenGrade P X ∧
    invS P * oddGrade P X * invS P = -oddGrade P X ∧
    conePlus P A * conePlus P X = 0 ∧
    coneMinus P C * coneMinus P X = 0 ∧
    comm (invS P) (conePlus P A) = (2 : ℤ) • conePlus P A ∧
    comm (invS P) (coneMinus P C) = -((2 : ℤ) • coneMinus P C) := by
  refine ⟨by simp only [conePlus, coneMinus]; noncomm_ring, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    peirce_nf hP

/-! ## 3. Stage `CL₂`: Chiral Dual Real Representation of the Lorentz Algebra -/

/-- **Stage `CL₂` (`archetype_CL2_chiral_dual_real_lorentz_representation`)**:
In any non-commutative ring `B` with idempotent `P * P = P`, the real symmetric boost generator
`Φ_i = genPhi P A_i C_i = N_+(A_i) + N_-(C_i)` and skew spin rotation generator
`J_i = genJ P A_i C_i = N_+(A_i) - N_-(C_i)` form a coordinate-free **chiral dual real
representation of the Lorentz algebra** intertwined by `S_P = invS P`:
1. **Chiral Duality Between Boost (`Φ`) and Rotation (`J`) Without Scalar `i`:**
   `invS P * genPhi P A₁ C₁ = genJ P A₁ C₁`, `genPhi P A₁ C₁ * invS P = -genJ P A₁ C₁`,
   `invS P * genJ P A₁ C₁ = genPhi P A₁ C₁`, and `genJ P A₁ C₁ * invS P = -genPhi P A₁ C₁`.
2. **Two-Mode Lorentz Closure (`[Φ₁, Φ₂] = -[J₁, J₂]` and `[Φ₁, J₂] = -[J₁, Φ₂]`):**
   `comm (genPhi P A₁ C₁) (genPhi P A₂ C₂) = zornTetradSkew P A₁ C₁ A₂ C₂`,
   `comm (genJ P A₁ C₁) (genJ P A₂ C₂) = -zornTetradSkew P A₁ C₁ A₂ C₂`,
   `comm (genPhi P A₁ C₁) (genJ P A₂ C₂) = -invS P * zornTetradSym P A₁ C₁ A₂ C₂`, and
   `comm (genJ P A₁ C₁) (genPhi P A₂ C₂) = invS P * zornTetradSym P A₁ C₁ A₂ C₂`.
3. **Orthogonal Left/Right Chiral Ideal Split (`P [Φ₁, Φ₂] P` vs. `(1 - P) [Φ₁, Φ₂] (1 - P)`):**
   `comm P (zornTetradSkew P A₁ C₁ A₂ C₂) = 0`,
   `P * zornTetradSkew P A₁ C₁ A₂ C₂ * P = conePlus P A₁ * coneMinus P C₂ - conePlus P A₂ * coneMinus P C₁`,
   `(1 - P) * zornTetradSkew P A₁ C₁ A₂ C₂ * (1 - P) = coneMinus P C₁ * conePlus P A₂ - coneMinus P C₂ * conePlus P A₁`,
   and `(P * zornTetradSkew P A₁ C₁ A₂ C₂ * P) * ((1 - P) * zornTetradSkew P A₁ C₁ A₂ C₂ * (1 - P)) = 0`. -/
theorem archetype_CL2_chiral_dual_real_lorentz_representation
    {P : B} (hP : P * P = P) (A₁ C₁ A₂ C₂ : B) :
    invS P * genPhi P A₁ C₁ = genJ P A₁ C₁ ∧
    genPhi P A₁ C₁ * invS P = -genJ P A₁ C₁ ∧
    invS P * genJ P A₁ C₁ = genPhi P A₁ C₁ ∧
    genJ P A₁ C₁ * invS P = -genPhi P A₁ C₁ ∧
    comm (genPhi P A₁ C₁) (genPhi P A₂ C₂) = zornTetradSkew P A₁ C₁ A₂ C₂ ∧
    comm (genJ P A₁ C₁) (genJ P A₂ C₂) = -zornTetradSkew P A₁ C₁ A₂ C₂ ∧
    comm (genPhi P A₁ C₁) (genJ P A₂ C₂) = -invS P * zornTetradSym P A₁ C₁ A₂ C₂ ∧
    comm (genJ P A₁ C₁) (genPhi P A₂ C₂) = invS P * zornTetradSym P A₁ C₁ A₂ C₂ ∧
    comm P (zornTetradSkew P A₁ C₁ A₂ C₂) = 0 ∧
    P * zornTetradSkew P A₁ C₁ A₂ C₂ * P =
      conePlus P A₁ * coneMinus P C₂ - conePlus P A₂ * coneMinus P C₁ ∧
    (1 - P) * zornTetradSkew P A₁ C₁ A₂ C₂ * (1 - P) =
      coneMinus P C₁ * conePlus P A₂ - coneMinus P C₂ * conePlus P A₁ ∧
    (P * zornTetradSkew P A₁ C₁ A₂ C₂ * P) *
      ((1 - P) * zornTetradSkew P A₁ C₁ A₂ C₂ * (1 - P)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [zornTetradSkew, zornTetradSym]); peirce_nf hP)

/-- **Krein–Dirac Adjoint (`kreinAdjoint P X = S_P X⋆ S_P`)** on the real doubled Left/Right
operator carrier `[Ring B] [StarRing B]`. -/
def kreinAdjoint [Star B] (P X : B) : B :=
  invS P * star X * invS P

/-- **Theorem `CL₂.2` (`hestenes_krein_real_doubled_geometric_algebra_and_krein_adjoint`)**:
Replaces the commutative scalar imaginary unit `i` with the **Hestenes–Krein geometric algebra of
the non-commutative operator ring** acting on the Left (`P`) / Right (`1 - P`) doubled states:
1. **Hestenes–Krein Real Operator Bivector Product (`J * Φ = Σ`, `Φ * J = -Σ`):**
   - `genPhi P A C * genPhi P A C = genV P A C` and `genJ P A C * genJ P A C = -genV P A C`,
   - `anticomm (genPhi P A C) (genJ P A C) = 0`,
   - `genJ P A C * genPhi P A C = genSig P A C` and `genPhi P A C * genJ P A C = -genSig P A C`,
   - `comm (genJ P A C) (genPhi P A C) = (2 : ℤ) • genSig P A C`.
2. **Real Operator Metriplectic QGT Decomposition (Without Scalar `i`):**
   - `(2 : ℤ) • qgtPlus P A C = genV P A C + genSig P A C` and
     `(2 : ℤ) • qgtPlus P A C = genPhi P A C * genPhi P A C + genJ P A C * genPhi P A C`,
   - `(2 : ℤ) • qgtMinus P A C = genV P A C - genSig P A C` and
     `(2 : ℤ) • qgtMinus P A C = genPhi P A C * genPhi P A C - genJ P A C * genPhi P A C`.
3. **Krein–Dirac Involution (`kreinAdjoint P X = S_P X⋆ S_P`) in any `[StarRing B]` (`star P = P`):**
   - `kreinAdjoint P (kreinAdjoint P X) = X` and
     `kreinAdjoint P (X * Y) = kreinAdjoint P Y * kreinAdjoint P X`,
   - `kreinAdjoint P (conePlus P A) = -coneMinus P (star A)` and
     `kreinAdjoint P (coneMinus P (star A)) = -conePlus P A`,
   - `kreinAdjoint P (genPhi P A (star A)) = -genPhi P A (star A)` and
     `kreinAdjoint P (genJ P A (star A)) = genJ P A (star A)`,
   - `kreinAdjoint P (genV P A (star A)) = genV P A (star A)` and
     `kreinAdjoint P (genSig P A (star A)) = genSig P A (star A)`
     (under the Krein–Dirac adjoint, both the emergent metric `V` and the uncertainty curvature `Σ`
     and the Hestenes bivector `J` are Krein-self-adjoint!). -/
theorem hestenes_krein_real_doubled_geometric_algebra_and_krein_adjoint
    [StarRing B] {P : B} (hP : P * P = P) (hPstar : star P = P) (A C X Y : B) :
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    anticomm (genPhi P A C) (genJ P A C) = 0 ∧
    genJ P A C * genPhi P A C = genSig P A C ∧
    genPhi P A C * genJ P A C = -genSig P A C ∧
    comm (genJ P A C) (genPhi P A C) = (2 : ℤ) • genSig P A C ∧
    (2 : ℤ) • qgtPlus P A C = genV P A C + genSig P A C ∧
    (2 : ℤ) • qgtPlus P A C = genPhi P A C * genPhi P A C + genJ P A C * genPhi P A C ∧
    (2 : ℤ) • qgtMinus P A C = genV P A C - genSig P A C ∧
    (2 : ℤ) • qgtMinus P A C = genPhi P A C * genPhi P A C - genJ P A C * genPhi P A C ∧
    kreinAdjoint P (kreinAdjoint P X) = X ∧
    kreinAdjoint P (X * Y) = kreinAdjoint P Y * kreinAdjoint P X ∧
    kreinAdjoint P (conePlus P A) = -coneMinus P (star A) ∧
    kreinAdjoint P (coneMinus P (star A)) = -conePlus P A ∧
    kreinAdjoint P (genPhi P A (star A)) = -genPhi P A (star A) ∧
    kreinAdjoint P (genJ P A (star A)) = genJ P A (star A) ∧
    kreinAdjoint P (genV P A (star A)) = genV P A (star A) ∧
    kreinAdjoint P (genSig P A (star A)) = genSig P A (star A) := by
  have hSstar : star (invS P) = invS P := by
    simp only [invS, star_sub, star_one, hPstar]
  have hS2 : invS P * invS P = 1 := by peirce_nf hP
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP,
          by simp only [qgtPlus]; peirce_nf hP,
          by simp only [qgtPlus]; peirce_nf hP,
          by simp only [qgtMinus]; peirce_nf hP,
          by simp only [qgtMinus]; peirce_nf hP,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      kreinAdjoint P (kreinAdjoint P X) =
          (invS P * invS P) * X * (invS P * invS P) := by
        simp only [kreinAdjoint, star_mul, star_star, hSstar]
        noncomm_ring
      _ = X := by rw [hS2]; noncomm_ring
  · calc
      kreinAdjoint P (X * Y) = invS P * star Y * (invS P * invS P) * star X * invS P := by
        simp only [kreinAdjoint, star_mul, hS2]
        noncomm_ring
      _ = kreinAdjoint P Y * kreinAdjoint P X := by
        simp only [kreinAdjoint]; noncomm_ring
  · simp only [kreinAdjoint, conePlus, coneMinus, star_mul, star_sub, star_one, hPstar]
    peirce_nf hP
  · simp only [kreinAdjoint, conePlus, coneMinus, star_mul, star_sub, star_one, star_star, hPstar]
    peirce_nf hP
  · simp only [kreinAdjoint, genPhi, conePlus, coneMinus, star_add, star_mul, star_sub, star_one,
      star_star, hPstar]
    peirce_nf hP
  · simp only [kreinAdjoint, genJ, conePlus, coneMinus, star_sub, star_mul, star_one,
      star_star, hPstar]
    peirce_nf hP
  · simp only [kreinAdjoint, genV, anticomm, conePlus, coneMinus, star_add, star_mul, star_sub,
      star_one, star_star, hPstar]
    peirce_nf hP
  · simp only [kreinAdjoint, genSig, comm, conePlus, coneMinus, star_sub, star_mul, star_one,
      star_star, hPstar]
    peirce_nf hP

/-! ## 4. Stage `CL₃`: Poincaré Semidirect Translation Ideal & `ℤ₂`-Graded SUSY Superalgebra -/

/-- **Stage `CL₃` (`archetype_CL3_poincare_semidirect_and_susy_superalgebra`)**:
1. **Abelian Poincaré Translation Cones & Semidirect Lorentz Action (`𝔤₀ ltimes 𝔤_{±1}`):**
   - `comm (conePlus P A₁) (conePlus P A₂) = 0` and `comm (coneMinus P C₁) (coneMinus P C₂) = 0`,
   - For any even-grade Lorentz generator `evenGrade P L`, the commutator `comm (evenGrade P L) (conePlus P A₁)`
     lies strictly in the upper translation cone (`P * comm (evenGrade P L) (conePlus P A₁) * (1 - P) = comm (evenGrade P L) (conePlus P A₁)`),
     and `comm (evenGrade P L) (coneMinus P C₁)` lies strictly in the lower translation cone.
2. **`ℤ₂`-Graded SUSY Superalgebra Anticommutator (`{Q_α, Q_β} = P_{αβ}`):**
   - `anticomm (conePlus P A₁) (coneMinus P C₁) = genV P A₁ C₁`,
   - `anticomm (genPhi P A₁ C₁) (genPhi P A₂ C₂) = zornTetradSym P A₁ C₁ A₂ C₂`,
   - `anticomm (genJ P A₁ C₁) (genJ P A₂ C₂) = -zornTetradSym P A₁ C₁ A₂ C₂`,
   - `comm P (zornTetradSym P A₁ C₁ A₂ C₂) = 0` (the symmetric SUSY translation `zornTetradSym` is strictly bosonic/even-graded).
3. **Centrality of the Bosonic Energy-Momentum `V = genV P A₁ C₁` on the Supercharge Multiplet:**
   - `comm (genV P A₁ C₁) (conePlus P A₁) = 0`, `comm (genV P A₁ C₁) (coneMinus P C₁) = 0`,
   - `comm (genV P A₁ C₁) (genPhi P A₁ C₁) = 0`, and `comm (genV P A₁ C₁) (genJ P A₁ C₁) = 0`. -/
theorem archetype_CL3_poincare_semidirect_and_susy_superalgebra
    {P : B} (hP : P * P = P) (L A₁ C₁ A₂ C₂ : B) :
    comm (conePlus P A₁) (conePlus P A₂) = 0 ∧
    comm (coneMinus P C₁) (coneMinus P C₂) = 0 ∧
    P * comm (evenGrade P L) (conePlus P A₁) * (1 - P) =
      comm (evenGrade P L) (conePlus P A₁) ∧
    (1 - P) * comm (evenGrade P L) (coneMinus P C₁) * P =
      comm (evenGrade P L) (coneMinus P C₁) ∧
    anticomm (conePlus P A₁) (coneMinus P C₁) = genV P A₁ C₁ ∧
    anticomm (genPhi P A₁ C₁) (genPhi P A₂ C₂) = zornTetradSym P A₁ C₁ A₂ C₂ ∧
    anticomm (genJ P A₁ C₁) (genJ P A₂ C₂) = -zornTetradSym P A₁ C₁ A₂ C₂ ∧
    comm P (zornTetradSym P A₁ C₁ A₂ C₂) = 0 ∧
    comm (genV P A₁ C₁) (conePlus P A₁) = 0 ∧
    comm (genV P A₁ C₁) (coneMinus P C₁) = 0 ∧
    comm (genV P A₁ C₁) (genPhi P A₁ C₁) = 0 ∧
    comm (genV P A₁ C₁) (genJ P A₁ C₁) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [zornTetradSym]); peirce_nf hP)

/-! ## 5. Stage `CL₄`: Super-Grassmannian Charts, Socratic Aporia (`Ψ² - Ψ = V`), & Para-Kähler Curvature -/

/-- Forward unipotent super-Grassmannian chart `(1 + N_+(A)) * P * (1 - N_+(A)) = P - N_+(A)`. -/
def superGrassmannChartPlus (P A : B) : B :=
  (1 + conePlus P A) * P * (1 - conePlus P A)

/-- Backward unipotent super-Grassmannian chart `(1 - N_-(C)) * P * (1 + N_-(C)) = P - N_-(C)`. -/
def superGrassmannChartMinus (P C : B) : B :=
  (1 - coneMinus P C) * P * (1 + coneMinus P C)

/-- **Stage `CL₄` (`archetype_CL4_super_grassmannian_parakahler_structure`)**:
1. **First-Order Socratic Aporia (`Ψ² - Ψ = V`) vs. Unipotent Super-Grassmannian Idempotency:**
   - The naive additive first-order state `Ψ = P + genPhi P A C` fails idempotency by the exact
     Fubini–Study metric tensor: `(P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C) = genV P A C`,
   - Both chiral unipotent super-Grassmannian charts are exact idempotents:
     `superGrassmannChartPlus P A = P - conePlus P A`,
     `superGrassmannChartMinus P C = P - coneMinus P C`,
     `superGrassmannChartPlus P A * superGrassmannChartPlus P A = superGrassmannChartPlus P A`, and
     `superGrassmannChartMinus P C * superGrassmannChartMinus P C = superGrassmannChartMinus P C`.
2. **Non-Commutative Super-Grassmannian Chart Commutator & Anticommutator:**
   - The commutator of the forward and backward super-Grassmannian charts splits into the even
     **uncertainty commutator `Σ = [N_+, N_-]`** and the odd boost `Φ = N_+ + N_-`:
     `comm (superGrassmannChartPlus P A) (superGrassmannChartMinus P C) = genSig P A C + genPhi P A C`
     and `evenGrade P (comm (superGrassmannChartPlus P A) (superGrassmannChartMinus P C)) = genSig P A C`,
   - Their anticommutator recovers the emergent metric `V = {N_+, N_-}`:
     `anticomm (superGrassmannChartPlus P A) (superGrassmannChartMinus P C) - (2 : ℤ) • P = genV P A C - genPhi P A C`.
3. **Para-Kähler Curvature 2-Form & Hessian Split on the Super-Grassmannian:**
   - `comm (conePlus P A) (comm (coneMinus P C) X) - comm (coneMinus P C) (comm (conePlus P A) X) = comm (genSig P A C) X`,
   - `-(2 : ℤ) • (comm (conePlus P A) (comm (coneMinus P C) X) + comm (coneMinus P C) (comm (conePlus P A) X)) = derivSqPhi P A C X + derivSqJ P A C X`. -/
theorem archetype_CL4_super_grassmannian_parakahler_structure
    {P : B} (hP : P * P = P) (A C X : B) :
    (P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C) = genV P A C ∧
    superGrassmannChartPlus P A = P - conePlus P A ∧
    superGrassmannChartMinus P C = P - coneMinus P C ∧
    superGrassmannChartPlus P A * superGrassmannChartPlus P A = superGrassmannChartPlus P A ∧
    superGrassmannChartMinus P C * superGrassmannChartMinus P C = superGrassmannChartMinus P C ∧
    comm (superGrassmannChartPlus P A) (superGrassmannChartMinus P C) =
      genSig P A C + genPhi P A C ∧
    anticomm (superGrassmannChartPlus P A) (superGrassmannChartMinus P C) - (2 : ℤ) • P =
      genV P A C - genPhi P A C ∧
    comm (conePlus P A) (comm (coneMinus P C) X) -
      comm (coneMinus P C) (comm (conePlus P A) X) = comm (genSig P A C) X ∧
    -(2 : ℤ) • (comm (conePlus P A) (comm (coneMinus P C) X) +
      comm (coneMinus P C) (comm (conePlus P A) X)) =
      derivSqPhi P A C X + derivSqJ P A C X := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [superGrassmannChartPlus, superGrassmannChartMinus, derivSqPhi, derivSqJ]);
      peirce_nf hP)

/-! ## 6. Stage `CL₅`: Twistor Incidence, Bicolored Plabic Shears, & Positive Amplituhedron (`StarRing`) -/

/-- **Stage `CL₅` (`archetype_CL5_twistor_incidence_and_positive_amplituhedron`)**:
1. **Bicolored Plabic Shear Non-Commutativity (`[U_+, U_-] = -Σ`) & Frozen Target/Source Discrepancy:**
   - `comm (plabicWhiteShear P A) (plabicBlackShear P C) = -genSig P A C`,
   - `plabicFrozenTarget P A C - plabicFrozenSource P A C = -genSig P A C`,
   - `plabicFrozenTarget P A C * plabicFrozenSource P A C = 1 - genV P A C`.
2. **Non-Commutative Three-Term Plücker–Twistor Exchange (`opPluckerBivector`):**
   - `opPluckerBivector P X₁ X₃ Y₁ Y₂ = opPluckerBivector P X₁ X₂ Y₁ Y₂ + opPluckerBivector P X₂ X₃ Y₁ Y₂`.
3. **Hermitian Amplituhedron Seed Positivity (`seedPositivityForm`) in any `[StarRing B]` (`star P = P`):**
   - `star (qgtPlus P A (star A)) = qgtPlus P A (star A)` and `star (qgtMinus P A (star A)) = qgtMinus P A (star A)`,
   - `star (genV P A (star A)) = genV P A (star A)` and `star (genSig P A (star A)) = genSig P A (star A)`
     (while `star (genJ P A (star A)) = -genJ P A (star A)`),
   - `seedPositivityForm P A X = star (coneMinus P (star A) * X) * (coneMinus P (star A) * X) + star (conePlus P A * X) * (conePlus P A * X)`
     (every amplituhedron seed form `X⋆ V X` decomposes into a sum of two non-commutative Hermitian squares!). -/
theorem archetype_CL5_twistor_incidence_and_positive_amplituhedron
    [StarRing B] {P : B} (hP : P * P = P) (hPstar : star P = P) (A C X X₁ X₂ X₃ Y₁ Y₂ : B) :
    comm (plabicWhiteShear P A) (plabicBlackShear P C) = -genSig P A C ∧
    plabicFrozenTarget P A C - plabicFrozenSource P A C = -genSig P A C ∧
    plabicFrozenTarget P A C * plabicFrozenSource P A C = 1 - genV P A C ∧
    opPluckerBivector P X₁ X₃ Y₁ Y₂ =
      opPluckerBivector P X₁ X₂ Y₁ Y₂ + opPluckerBivector P X₂ X₃ Y₁ Y₂ ∧
    star (qgtPlus P A (star A)) = qgtPlus P A (star A) ∧
    star (qgtMinus P A (star A)) = qgtMinus P A (star A) ∧
    star (genV P A (star A)) = genV P A (star A) ∧
    star (genSig P A (star A)) = genSig P A (star A) ∧
    seedPositivityForm P A X =
      star (coneMinus P (star A) * X) * (coneMinus P (star A) * X) +
        star (conePlus P A * X) * (conePlus P A * X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [plabicWhiteShear, plabicBlackShear]; peirce_nf hP
  · simp only [plabicFrozenTarget, plabicFrozenSource, qgtPlus, qgtMinus]; peirce_nf hP
  · simp only [plabicFrozenTarget, plabicFrozenSource, qgtPlus, qgtMinus]; peirce_nf hP
  · simp only [opPluckerBivector, projChartPlus, projChartMinus]; peirce_nf hP
  · simp only [qgtPlus, conePlus, coneMinus, star_mul, star_sub, star_one, star_star, hPstar]
    peirce_nf hP
  · simp only [qgtMinus, conePlus, coneMinus, star_mul, star_sub, star_one, star_star, hPstar]
    peirce_nf hP
  · simp only [genV, anticomm, conePlus, coneMinus, star_add, star_mul, star_sub, star_one,
      star_star, hPstar]
    peirce_nf hP
  · simp only [genSig, comm, conePlus, coneMinus, star_sub, star_mul, star_one, star_star, hPstar]
    peirce_nf hP
  · simp only [seedPositivityForm, genV, anticomm, conePlus, coneMinus, star_mul, star_sub,
      star_one, star_star, hPstar]
    peirce_nf hP

/-! ## 7. Stage `CL₆`: Uncertainty Commutator `Σ = [N_+, N_-]` as the Creator of Metric Gravity `V` & Curvature -/

/-- **Stage `CL₆` (`archetype_CL6_uncertainty_as_creator_of_metric_and_spin_curvature`)**:
Proves the fundamental theorem that the **non-commuting uncertainty bracket `Σ = [N_+(A), N_-(C)]`
is the necessary and sufficient creator of both the emergent spacetime metric `V = {N_+(A), N_-(C)}`
and the QGT projector sheets `Q_+ = N_+ N_-`, `Q_- = N_- N_+`**:
1. **Exact Chiral Intertwining of Metric `V` and Uncertainty `Σ` (`V = S_P Σ = Σ S_P`):**
   - `P * genSig P A C * P = qgtPlus P A C` and `(1 - P) * genSig P A C * (1 - P) = -qgtMinus P A C`,
   - `genV P A C = invS P * genSig P A C` and `genV P A C = genSig P A C * invS P`,
   - `genSig P A C = invS P * genV P A C` and `genSig P A C = genV P A C * invS P`.
2. **Necessary & Sufficient Creation Law (`Σ = 0 ↔ V = 0 ↔ (Q_+ = 0 ∧ Q_- = 0)`):**
   - The uncertainty commutator `genSig P A C = [N_+(A), N_-(C)]` vanishes if and only if the
     emergent spacetime metric `genV P A C = {N_+(A), N_-(C)}` vanishes, if and only if both
     chiral QGT sheets `qgtPlus P A C` and `qgtMinus P A C` vanish!
   - Equivalently, `genSig P A C ≠ 0 ↔ genV P A C ≠ 0`: non-vanishing commutator uncertainty creates
     non-vanishing metric gravity! -/
theorem archetype_CL6_uncertainty_as_creator_of_metric_and_spin_curvature
    {P : B} (hP : P * P = P) (A C : B) :
    P * genSig P A C * P = qgtPlus P A C ∧
    (1 - P) * genSig P A C * (1 - P) = -qgtMinus P A C ∧
    genV P A C = invS P * genSig P A C ∧
    genV P A C = genSig P A C * invS P ∧
    genSig P A C = invS P * genV P A C ∧
    genSig P A C = genV P A C * invS P ∧
    (genSig P A C = 0 ↔ genV P A C = 0) ∧
    (genSig P A C = 0 ↔ (qgtPlus P A C = 0 ∧ qgtMinus P A C = 0)) ∧
    (genSig P A C ≠ 0 ↔ genV P A C ≠ 0) := by
  have hQplus : P * genSig P A C * P = qgtPlus P A C := by
    simp only [genSig, qgtPlus]; peirce_nf hP
  have hQminus : (1 - P) * genSig P A C * (1 - P) = -qgtMinus P A C := by
    simp only [genSig, qgtMinus]; peirce_nf hP
  have hVS : genV P A C = invS P * genSig P A C := by peirce_nf hP
  have hVS' : genV P A C = genSig P A C * invS P := by peirce_nf hP
  have hSV : genSig P A C = invS P * genV P A C := by peirce_nf hP
  have hSV' : genSig P A C = genV P A C * invS P := by peirce_nf hP
  have hSigIffV : genSig P A C = 0 ↔ genV P A C = 0 := by
    constructor
    · intro hSig
      rw [hVS, hSig, mul_zero]
    · intro hV
      rw [hSV, hV, mul_zero]
  have hSigIffSheets : genSig P A C = 0 ↔ (qgtPlus P A C = 0 ∧ qgtMinus P A C = 0) := by
    constructor
    · intro hSig
      refine ⟨?_, ?_⟩
      · rw [← hQplus, hSig]; noncomm_ring
      · have h0 : (1 - P) * genSig P A C * (1 - P) = 0 := by rw [hSig]; noncomm_ring
        rw [hQminus] at h0
        exact neg_eq_zero.mp h0
    · rintro ⟨hQp, hQm⟩
      have hSub : genSig P A C = qgtPlus P A C - qgtMinus P A C := rfl
      rw [hSub, hQp, hQm, sub_self]
  refine ⟨hQplus, hQminus, hVS, hVS', hSV, hSV', hSigIffV, hSigIffSheets, not_congr hSigIffV⟩

/-! ## 8. Stage `CL₇`: Élie Cartan Torsion, Soldered Spin Connection, & Maurer–Cartan Curvature -/

/-- Base chiral grading exterior differential `d₀(X) = [P, X]`. -/
def chiralExtDeriv (P X : B) : B := comm P X

/-- Maurer–Cartan curvature 2-form `𝓕₀(Ω) = d₀(Ω) + Ω * Ω = [P, Ω] + Ω²` of an operator 1-form `Ω`. -/
def cartanCurvature2Form (P Ω : B) : B :=
  chiralExtDeriv P Ω + Ω * Ω

/-- Élie Cartan covariant torsion 2-form `𝓣(ω, E) = d₀(E) + [ω, E] = [P, E] + [ω, E]` of a frame
tetrad `E` with respect to an even spin connection `ω`. -/
def cartanCovariantTorsion (P ω E : B) : B :=
  chiralExtDeriv P E + comm ω E

/-- **Stage `CL₇` (`archetype_CL7_elie_cartan_torsion_and_spin_connection_gravity`)**:
Formalizes Élie Cartan torsion and spin-connection curvature induced by the uncertainty commutator
`ω_spin = Σ = [N_+(A), N_-(C)]`:
1. **Soldered Frame Maurer–Cartan Curvature (`𝓕₀(Φ) = J + V`, `𝓕₀(J) = Φ - V`):**
   - `cartanCurvature2Form P (genPhi P A C) = genJ P A C + genV P A C`
     (splitting into the odd chiral torsion `d₀(Φ) = J` and the even metric curvature `Φ² = V = S_P Σ`!),
   - `cartanCurvature2Form P (genJ P A C) = genPhi P A C - genV P A C`,
   - `peirceMaurerCartanForm (comm P) (1 + conePlus P A) (1 - conePlus P A) = conePlus P A` and
     `cartanCurvature2Form P (peirceMaurerCartanForm (comm P) (1 + conePlus P A) (1 - conePlus P A)) = conePlus P A`.
2. **Uncertainty Spin Connection (`ω_spin = Σ = genSig P A C`) Curvature & Covariant Torsion:**
   - The uncertainty commutator `Σ` is closed under the base differential (`chiralExtDeriv P (genSig P A C) = 0`),
     so its Cartan curvature 2-form is pure Riemann-Casimir square:
     `cartanCurvature2Form P (genSig P A C) = genV P A C * genV P A C`,
   - Its Élie Cartan covariant torsion on the soldered tetrads `(Φ, J)` and chiral null frames `(N_+, N_-)` is:
     `cartanCovariantTorsion P (genSig P A C) (genPhi P A C) = (1 + (2 : ℤ) • genV P A C) * genJ P A C`,
     `cartanCovariantTorsion P (genSig P A C) (genJ P A C) = (1 + (2 : ℤ) • genV P A C) * genPhi P A C`,
     `cartanCovariantTorsion P (genSig P A C) (conePlus P A) = (1 + (2 : ℤ) • genV P A C) * conePlus P A`,
     `cartanCovariantTorsion P (genSig P A C) (coneMinus P C) = -((1 + (2 : ℤ) • genV P A C) * coneMinus P C)`.
3. **Exact Differential & Covariant Bianchi Identity for the Uncertainty Spin Connection:**
   - `chiralExtDeriv P (cartanCurvature2Form P (genSig P A C)) = 0` and
     `comm (genSig P A C) (cartanCurvature2Form P (genSig P A C)) = 0`. -/
theorem archetype_CL7_elie_cartan_torsion_and_spin_connection_gravity
    {P : B} (hP : P * P = P) (A C : B) :
    cartanCurvature2Form P (genPhi P A C) = genJ P A C + genV P A C ∧
    cartanCurvature2Form P (genJ P A C) = genPhi P A C - genV P A C ∧
    cartanCurvature2Form P
        (peirceMaurerCartanForm (comm P) (1 + conePlus P A) (1 - conePlus P A)) =
      conePlus P A ∧
    chiralExtDeriv P (genSig P A C) = 0 ∧
    cartanCurvature2Form P (genSig P A C) = genV P A C * genV P A C ∧
    cartanCovariantTorsion P (genSig P A C) (genPhi P A C) =
      (1 + (2 : ℤ) • genV P A C) * genJ P A C ∧
    cartanCovariantTorsion P (genSig P A C) (genJ P A C) =
      (1 + (2 : ℤ) • genV P A C) * genPhi P A C ∧
    cartanCovariantTorsion P (genSig P A C) (conePlus P A) =
      (1 + (2 : ℤ) • genV P A C) * conePlus P A ∧
    cartanCovariantTorsion P (genSig P A C) (coneMinus P C) =
      -((1 + (2 : ℤ) • genV P A C) * coneMinus P C) ∧
    chiralExtDeriv P (cartanCurvature2Form P (genSig P A C)) = 0 ∧
    comm (genSig P A C) (cartanCurvature2Form P (genSig P A C)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [cartanCurvature2Form, cartanCovariantTorsion, chiralExtDeriv,
      peirceMaurerCartanForm]); peirce_nf hP)

/-- **Theorem `CL₇.2` (`cartanEhresmann_commutator_and_chiral_gamma5_anomaly_cocycle`)**:
Formalizes the unified Cartan–Ehresmann gauge connection `A_Φ = Σ + Φ` (combining the spin
connection `ω = Σ = [N_+, N_-]` and the solder form `e = Φ = N_+ + N_-`), its dual `A_J = Σ + J`,
and the chiral `γ₅ = S_P` anomaly cocycle:
1. **Anticommutativity of Spin Connection `Σ` and Solder Forms `Φ, J`:**
   `anticomm (genSig P A C) (genPhi P A C) = 0` and `anticomm (genSig P A C) (genJ P A C) = 0`.
2. **Unified Cartan–Ehresmann Curvature 2-Form (`𝓕₀(Σ + Φ) = (V² + V) + J`):**
   `cartanCurvature2Form P (genSig P A C + genPhi P A C) = (genV P A C * genV P A C + genV P A C) + genJ P A C`
   (splitting into the even Riemann-metric curvature `V² + V` in `𝔤₀` and the odd Cartan torsion `J` in `𝔤_{±1}`).
3. **Cartan–Ehresmann Connection Commutator (`[Σ + Φ, Σ + J] = -2Σ + 2V(Φ - J)`):**
   `comm (genSig P A C + genPhi P A C) (genSig P A C + genJ P A C) = -((2 : ℤ) • genSig P A C) + (2 : ℤ) • (genV P A C * (genPhi P A C - genJ P A C))`,
   whose even-grade part is the Lorentz rotation curvature `-2Σ` and whose odd-grade part is the
   translational torsion `2V(Φ - J)`.
4. **Chiral `γ₅ = S_P` Anomaly Cocycle (`S_P [Φ, J] = -2V`):**
   `invS P * comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genV P A C)` and
   `evenGrade P (invS P * comm (genSig P A C + genPhi P A C) (genSig P A C + genJ P A C)) = -((2 : ℤ) • genV P A C)`. -/
theorem cartanEhresmann_commutator_and_chiral_gamma5_anomaly_cocycle
    {P : B} (hP : P * P = P) (A C : B) :
    anticomm (genSig P A C) (genPhi P A C) = 0 ∧
    anticomm (genSig P A C) (genJ P A C) = 0 ∧
    cartanCurvature2Form P (genSig P A C + genPhi P A C) =
      (genV P A C * genV P A C + genV P A C) + genJ P A C ∧
    comm (genSig P A C + genPhi P A C) (genSig P A C + genJ P A C) =
      -((2 : ℤ) • genSig P A C) + (2 : ℤ) • (genV P A C * (genPhi P A C - genJ P A C)) ∧
    evenGrade P (comm (genSig P A C + genPhi P A C) (genSig P A C + genJ P A C)) =
      -((2 : ℤ) • genSig P A C) ∧
    oddGrade P (comm (genSig P A C + genPhi P A C) (genSig P A C + genJ P A C)) =
      (2 : ℤ) • (genV P A C * (genPhi P A C - genJ P A C)) ∧
    invS P * comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genV P A C) ∧
    evenGrade P (invS P * comm (genSig P A C + genPhi P A C) (genSig P A C + genJ P A C)) =
      -((2 : ℤ) • genV P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [cartanCurvature2Form, chiralExtDeriv]); peirce_nf hP)

/-! ## 9. Stage `CL₈`: The Anomaly of Uncertainty as a Generator in the Higher Grade (`±2`) of the 5-Graded Symmetry Closure -/

/-- **Stage `CL₈` (`archetype_CL8_higher_grade_uncertainty_anomaly_in_symmetry_closure`)**:
Establishes how the non-commuting uncertainty commutator `Σ_{A,C} = genSig P A C = [N_+(A), N_-(C)]`
generates the higher-grade (`±2`) Kantor–Koecher–Tits conformal closure and the skew Kantor corner
anomaly:
1. **Uncertainty Factorization of the Higher-Grade Cubic (`Σ_{A,C} N_+(Z) = -N_+(A) Σ_{Z,C}`):**
   - `genSig P A C * conePlus P Z = conePlus P A * coneMinus P C * conePlus P Z` and
     `conePlus P A * genSig P Z C = -(conePlus P A * coneMinus P C * conePlus P Z)`,
   - Consequently, the **Kantor Corner Anomaly (`upperHomotopeBracket P C A Z`)** is the exact
     **skew uncertainty-commutator anomaly**:
     `genSig P A C * conePlus P Z - genSig P Z C * conePlus P A = upperHomotopeBracket P C A Z`,
   - While their symmetric sum is the grade-`+1` uncertainty boost:
     `genSig P A C * conePlus P Z + genSig P Z C * conePlus P A = comm (genSig P A C) (conePlus P Z)`.
2. **Jacobi Identity & Nilpotency of the Uncertainty Anomaly Bracket (`upperHomotopeBracket`):**
   - `upperHomotopeBracket P C A (upperHomotopeBracket P C Z W) + upperHomotopeBracket P C Z (upperHomotopeBracket P C W A) + upperHomotopeBracket P C W (upperHomotopeBracket P C A Z) = 0`,
   - `upperHomotopeBracket P C A Z * upperHomotopeBracket P C A Z = 0`.
3. **Grade-`±2` Extremal Kantor Generators (`kantorGp2`, `kantorGm2`) & Bilateral Uncertainty Sandwich (`Σ X Σ`):**
   - Evaluating the grade-`+2` generator `kantorGp2 P A` on `coneMinus P C` produces the single-mode
     uncertainty cubic:
     `kantorGp2 P A (coneMinus P C) = genSig P A C * conePlus P A`,
     and dually `kantorGm2 P C (conePlus P A) = -genSig P A C * coneMinus P C`,
   - The commutator of the grade-`+2` and grade-`-2` operators is the crossed-support bracket of the
     two uncertainty sheets `Q_+ = P Σ P` and `Q_- = -(1 - P) Σ (1 - P)`:
     `kantorGp2 P A (kantorGm2 P C X) - kantorGm2 P C (kantorGp2 P A X) = qgtPlus P A C * X * qgtMinus P A C - qgtMinus P A C * X * qgtPlus P A C`,
   - And the difference between the square of the grade-`0` operator `kantorG0` and the anticommutator
     of the grade-`±2` operators `kantorGp2`, `kantorGm2` is the **double-sided uncertainty sandwich `Σ X Σ`**:
     `kantorG0 P A C (kantorG0 P A C X) - (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) = genSig P A C * X * genSig P A C`. -/
theorem archetype_CL8_higher_grade_uncertainty_anomaly_in_symmetry_closure
    {P : B} (hP : P * P = P) (A C Z W X : B) :
    genSig P A C * conePlus P Z = conePlus P A * coneMinus P C * conePlus P Z ∧
    conePlus P A * genSig P Z C = -(conePlus P A * coneMinus P C * conePlus P Z) ∧
    genSig P A C * conePlus P Z - genSig P Z C * conePlus P A =
      upperHomotopeBracket P C A Z ∧
    genSig P A C * conePlus P Z + genSig P Z C * conePlus P A =
      comm (genSig P A C) (conePlus P Z) ∧
    upperHomotopeBracket P C A (upperHomotopeBracket P C Z W) +
      upperHomotopeBracket P C Z (upperHomotopeBracket P C W A) +
      upperHomotopeBracket P C W (upperHomotopeBracket P C A Z) = 0 ∧
    upperHomotopeBracket P C A Z * upperHomotopeBracket P C A Z = 0 ∧
    kantorGp2 P A (coneMinus P C) = genSig P A C * conePlus P A ∧
    kantorGm2 P C (conePlus P A) = -genSig P A C * coneMinus P C ∧
    kantorGp2 P A (kantorGm2 P C X) - kantorGm2 P C (kantorGp2 P A X) =
      qgtPlus P A C * X * qgtMinus P A C - qgtMinus P A C * X * qgtPlus P A C ∧
    kantorG0 P A C (kantorG0 P A C X) -
      (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) =
      genSig P A C * X * genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_, upper_homotope_jacobi hP C A Z W,
          (upper_kantor_anomaly_corner hP A C Z).2, ?_, ?_, ?_, ?_⟩
  · simp only [genSig]; peirce_nf hP
  · simp only [genSig]; peirce_nf hP
  · simp only [upperHomotopeBracket, opKantorAnomaly, genSig]; peirce_nf hP
  · simp only [genSig]; peirce_nf hP
  · simp only [kantorGp2, genSig]; peirce_nf hP
  · simp only [kantorGm2, genSig]; peirce_nf hP
  · simp only [kantorGp2, kantorGm2, qgtPlus, qgtMinus]; peirce_nf hP
  · simp only [kantorG0, kantorTriple, kantorGp2, kantorGm2, genSig]; peirce_nf hP

/-! ## 10. Stage `CL₉`: Recursive Meta-Cognitive Defect Tower & Hilbert-Space Cramér–Rao Curvature Bound -/

/-- **Stage `CL₉` (`archetype_CL9_recursive_meta_tower_and_hilbert_cramer_rao_curvature_bound`)**:
1. **Iterated Uncertainty Spin-Curvature Eigenequation & Recursive Newton–Peirce Defect Compression:**
   - `comm (genSig P A C) (comm (genSig P A C) (genPhi P A C)) = (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C)`,
   - `comm (genSig P A C) (comm (genSig P A C) (genJ P A C)) = (4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C)`,
   - For any off-shell approximate projector `Q : B`, the Newton–Peirce purification step
     `Q' = 3 Q² - 2 Q³` squares the idempotency aporia `D = Q² - Q`:
     `(3 * (Q * Q) - 2 * (Q * Q * Q)) * (3 * (Q * Q) - 2 * (Q * Q * Q)) - (3 * (Q * Q) - 2 * (Q * Q * Q)) = (Q * Q - Q) * (Q * Q - Q) * (4 * (Q * Q - Q) - 3)`.
2. **Hilbert-Space Metriplectic Cramér–Rao / Robertson–Schrödinger Uncertainty Bound on Curvature:**
   - For any normalized Hilbert state `ψ : NormalizedState H` and continuous linear operators
     `X_op, Y_op : H →L[ℂ] H`, the squared Quantum Geometric Tensor splits orthogonally into the
     symmetric Fubini–Study metric `g(X, Y)` and the skew Berry/commutator curvature `Ω(X, Y)`:
     `Complex.normSq (QGT ψ X_op Y_op) = (g X_op Y_op) ^ 2 + (1 / 4 : ℝ) * (Ω X_op Y_op) ^ 2`,
   - And the metric variance product is bounded below by the commutator curvature:
     `g X_op X_op * g Y_op Y_op ≥ (g X_op Y_op) ^ 2 + (1 / 4 : ℝ) * (Ω X_op Y_op) ^ 2` and
     `g X_op X_op * g Y_op Y_op ≥ (1 / 4 : ℝ) * (Ω X_op Y_op) ^ 2`. -/
theorem archetype_CL9_recursive_meta_tower_and_hilbert_cramer_rao_curvature_bound
    {P : B} (hP : P * P = P) (A C Q : B)
    {H_hilb : Type*} [NormedAddCommGroup H_hilb] [InnerProductSpace ℂ H_hilb] [CompleteSpace H_hilb]
    (ψ : InfoGeometry.QuantumGeometry.Projective.NormalizedState H_hilb)
    (X_op Y_op : H_hilb →L[ℂ] H_hilb) :
    let g := InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty.onsagerDissipativeMetric ψ
    let Ω := InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty.onsagerReversibleBracket ψ
    comm (genSig P A C) (comm (genSig P A C) (genPhi P A C)) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) ∧
    comm (genSig P A C) (comm (genSig P A C) (genJ P A C)) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C) ∧
    (3 * (Q * Q) - 2 * (Q * Q * Q)) * (3 * (Q * Q) - 2 * (Q * Q * Q)) -
      (3 * (Q * Q) - 2 * (Q * Q * Q)) =
      (Q * Q - Q) * (Q * Q - Q) * (4 * (Q * Q - Q) - 3) ∧
    Complex.normSq (InfoGeometry.QuantumGeometry.Projective.QGT ψ X_op Y_op) =
      (g X_op Y_op) ^ 2 + (1 / 4 : ℝ) * (Ω X_op Y_op) ^ 2 ∧
    g X_op X_op * g Y_op Y_op ≥ (g X_op Y_op) ^ 2 + (1 / 4 : ℝ) * (Ω X_op Y_op) ^ 2 ∧
    g X_op X_op * g Y_op Y_op ≥ (1 / 4 : ℝ) * (Ω X_op Y_op) ^ 2 := by
  refine ⟨?_, ?_, by noncomm_ring,
    InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty.onsager_QGT_split ψ X_op Y_op,
    InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty.cramerRao_metriplectic_full_bound ψ X_op Y_op,
    InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty.cramerRao_commutator_uncertainty_bound ψ X_op Y_op⟩
  · peirce_nf hP
  · peirce_nf hP

/-! ## 11. Stage `CL₁₀`: Master Structural Synthesis & Non-Commutative Matrix Witnesses (`T16`/`T17`) -/

/-- **Stage `CL₁₀` (`stage_CL10_master_chiral_lorentz_twistor_cartan_uncertainty_synthesis`)**:
Coagulates the entire 10-stage poset (`CL₁ → CL₁₀`) into a single self-verifying master theorem:
1. Strict acyclicity of `ChiralLorentzTwistorCartanStage.causalEdge`,
2. Chiral dual real Lorentz representation (`[Φ₁, Φ₂] = -[J₁, J₂] = zornTetradSkew`),
3. Poincaré translation ideal & SUSY anticommutator (`{Φ₁, Φ₂} = zornTetradSym`),
4. Super-Grassmannian chart commutator (`[P_+(A), P_-(C)] = Σ`) & Para-Kähler curvature (`[δ_+, δ_-](X) = [Σ, X]`),
5. Twistor-amplituhedron Hermitian square positivity (`seedPositivityForm`),
6. Uncertainty as the necessary and sufficient creator of emergent metric gravity (`Σ = 0 ↔ V = 0`, `V = S_P Σ`),
7. Élie Cartan soldered curvature (`𝓕₀(Φ) = J + V`) & uncertainty spin-connection torsion (`𝓣_Σ(Φ) = (1 + 2V) J`),
8. Higher-grade (`±2`) Kantor uncertainty anomaly (`Σ_{A,C} N_+(Z) - Σ_{Z,C} N_+(A) = upperHomotopeBracket P C A Z`)
   and bilateral uncertainty sandwich (`kantorG0² - {kantorGp2, kantorGm2} = Σ X Σ`),
9. Metriplectic Cramér–Rao commutator uncertainty bound (`g(X,X) g(Y,Y) ≥ g(X,Y)² + Ω(X,Y)²/4`). -/
theorem stage_CL10_master_chiral_lorentz_twistor_cartan_uncertainty_synthesis
    [StarRing B] {P : B} (hP : P * P = P) (hPstar : star P = P)
    (A₁ C₁ A₂ C₂ Z X : B)
    {H_hilb : Type*} [NormedAddCommGroup H_hilb] [InnerProductSpace ℂ H_hilb] [CompleteSpace H_hilb]
    (ψ : InfoGeometry.QuantumGeometry.Projective.NormalizedState H_hilb)
    (X_op Y_op : H_hilb →L[ℂ] H_hilb) :
    let g := InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty.onsagerDissipativeMetric ψ
    let Ω := InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty.onsagerReversibleBracket ψ
    (∀ u : ChiralLorentzTwistorCartanStage,
      ¬ Relation.TransGen ChiralLorentzTwistorCartanStage.causalEdge u u) ∧
    (comm (genPhi P A₁ C₁) (genPhi P A₂ C₂) = zornTetradSkew P A₁ C₁ A₂ C₂ ∧
      comm (genJ P A₁ C₁) (genJ P A₂ C₂) = -zornTetradSkew P A₁ C₁ A₂ C₂) ∧
    (anticomm (genPhi P A₁ C₁) (genPhi P A₂ C₂) = zornTetradSym P A₁ C₁ A₂ C₂ ∧
      comm P (zornTetradSym P A₁ C₁ A₂ C₂) = 0) ∧
    (comm (superGrassmannChartPlus P A₁) (superGrassmannChartMinus P C₁) =
      genSig P A₁ C₁ + genPhi P A₁ C₁ ∧
      comm (conePlus P A₁) (comm (coneMinus P C₁) X) -
        comm (coneMinus P C₁) (comm (conePlus P A₁) X) = comm (genSig P A₁ C₁) X) ∧
    (seedPositivityForm P A₁ X =
      star (coneMinus P (star A₁) * X) * (coneMinus P (star A₁) * X) +
        star (conePlus P A₁ * X) * (conePlus P A₁ * X)) ∧
    (genV P A₁ C₁ = invS P * genSig P A₁ C₁ ∧
      (genSig P A₁ C₁ = 0 ↔ genV P A₁ C₁ = 0)) ∧
    (cartanCurvature2Form P (genPhi P A₁ C₁) = genJ P A₁ C₁ + genV P A₁ C₁ ∧
      cartanCovariantTorsion P (genSig P A₁ C₁) (genPhi P A₁ C₁) =
        (1 + (2 : ℤ) • genV P A₁ C₁) * genJ P A₁ C₁) ∧
    (genSig P A₁ C₁ * conePlus P Z - genSig P Z C₁ * conePlus P A₁ =
      upperHomotopeBracket P C₁ A₁ Z ∧
      kantorG0 P A₁ C₁ (kantorG0 P A₁ C₁ X) -
        (kantorGp2 P A₁ (kantorGm2 P C₁ X) + kantorGm2 P C₁ (kantorGp2 P A₁ X)) =
        genSig P A₁ C₁ * X * genSig P A₁ C₁) ∧
    (g X_op X_op * g Y_op Y_op ≥ (g X_op Y_op) ^ 2 + (1 / 4 : ℝ) * (Ω X_op Y_op) ^ 2) := by
  have hCL2 := archetype_CL2_chiral_dual_real_lorentz_representation hP A₁ C₁ A₂ C₂
  have hCL3 := archetype_CL3_poincare_semidirect_and_susy_superalgebra hP X A₁ C₁ A₂ C₂
  have hCL4 := archetype_CL4_super_grassmannian_parakahler_structure hP A₁ C₁ X
  have hCL5 := archetype_CL5_twistor_incidence_and_positive_amplituhedron hP hPstar A₁ C₁ X X X X X X
  have hCL6 := archetype_CL6_uncertainty_as_creator_of_metric_and_spin_curvature hP A₁ C₁
  have hCL7 := archetype_CL7_elie_cartan_torsion_and_spin_connection_gravity hP A₁ C₁
  have hCL8 := archetype_CL8_higher_grade_uncertainty_anomaly_in_symmetry_closure hP A₁ C₁ Z Z X
  have hCL9 := archetype_CL9_recursive_meta_tower_and_hilbert_cramer_rao_curvature_bound hP A₁ C₁ X ψ X_op Y_op
  exact ⟨ChiralLorentzTwistorCartanStage.causalEdge_acyclic,
    ⟨hCL2.2.2.2.2.1, hCL2.2.2.2.2.2.1⟩,
    ⟨hCL3.2.2.2.2.2.1, hCL3.2.2.2.2.2.2.2.1⟩,
    ⟨hCL4.2.2.2.2.2.1, hCL4.2.2.2.2.2.2.2.1⟩,
    hCL5.2.2.2.2.2.2.2.2,
    ⟨hCL6.2.2.1, hCL6.2.2.2.2.2.2.1⟩,
    ⟨hCL7.1, hCL7.2.2.2.2.2.1⟩,
    ⟨hCL8.2.2.1, hCL8.2.2.2.2.2.2.2.2.2⟩,
    hCL9.2.2.2.2.1⟩

/-! ## 12. Clifford–Krein Geometric Product, Grade-3 Jordan Associator Curvature Anomaly, & Nilpotent-First Élie Cartan Gravity -/

/-- The Grade-3 Jordan Associator Anomaly `JordanAssoc(X, Y, Z) = {{X, Y}, Z} - {X, {Y, Z}}`,
measuring the exact failure of the symmetric uncertainty product `{·, ·}` to associate. -/
def JordanAssoc (X Y Z : B) : B :=
  anticomm (anticomm X Y) Z - anticomm X (anticomm Y Z)

/-- Two-index Information Metric / SUSY Torsion Tensor `G_{μν} = {∇_μ, ∇_ν*}`. -/
def G_metric [Star B] (N_mu N_nu : B) : B := anticomm N_mu (star N_nu)

/-- Two-index Élie Cartan Spin Curvature Tensor `R_{μν} = [∇_μ, ∇_ν*]`. -/
def R_cartan [Star B] (N_mu N_nu : B) : B := comm N_mu (star N_nu)

/-- The emergent Spacetime Momentum / Information Metric `P_mom = {N_+, N_+*}`. -/
def P_mom [Star B] (N_plus : B) : B := N_plus * star N_plus + star N_plus * N_plus

/-- The Chiral Lorentz / Para-Complex / Spin Curvature operator `Sigma_op = [N_+, N_+*]`. -/
def Sigma_op [Star B] (N_plus : B) : B := N_plus * star N_plus - star N_plus * N_plus

/-- Positive-chirality Twistor / Grassmannian projector `P_twistor = N_+ N_+*`. -/
def P_twistor [Star B] (N_plus : B) : B := N_plus * star N_plus

/-- Negative-chirality dual Twistor / Grassmannian projector `Q_twistor = N_+* N_+`. -/
def Q_twistor [Star B] (N_plus : B) : B := star N_plus * N_plus

/-- **Universal Clifford–Krein Geometric Product & Jordan Associator Anomaly (`clifford_krein_geometric_product_and_jordan_associator_law`)**:
1. **The Geometric Product Split (`2 X Y = {X, Y} + [X, Y] = 2(X · Y + X ∧ Y)`):**
   `(2 : ℤ) • (X * Y) = anticomm X Y + comm X Y` and
   `(2 : ℤ) • (Y * X) = anticomm X Y - comm X Y`.
2. **Clifford–Krein Reversion Modulus (`(g + I Ω)(g - I Ω) = g² - (I Ω)² + [g, I Ω]`):**
   `(g_op + I_op * Ω_op) * (g_op - I_op * Ω_op) = g_op * g_op - (I_op * Ω_op) * (I_op * Ω_op) - comm g_op (I_op * Ω_op)`,
   and for the Peirce QGT split `2 Q_± = V ± Σ = Φ² ± J Φ`, the Clifford–Krein modulus vanishes
   along the null lightcone (Bogomolny saturation):
   `(genV P A C + genSig P A C) * (genV P A C - genSig P A C) = 0` and
   `genV P A C * genV P A C - genSig P A C * genSig P A C = 0`.
3. **Universal Grade-3 Jordan Associator Curvature Identity (`{{X, Y}, Z} - {X, {Y, Z}} = [[Z, X], Y]`):**
   In any non-commutative ring `B`, the associative anomaly of the symmetric uncertainty product
   `{·, ·}` is identically the Riemann–Cartan double commutator:
   `JordanAssoc X Y Z = comm (comm Z X) Y`,
   and on the Peirce chiral cones (`N_+ = conePlus P A`, `N_- = coneMinus P C`):
   `JordanAssoc (coneMinus P C) (conePlus P A) (conePlus P A) = comm (genSig P A C) (conePlus P A)`
   (`= (2 : ℤ) • (genV P A C * conePlus P A)`). -/
theorem clifford_krein_geometric_product_and_jordan_associator_law
    {P : B} (hP : P * P = P) (A C X Y Z g_op I_op Ω_op : B) :
    (2 : ℤ) • (X * Y) = anticomm X Y + comm X Y ∧
    (2 : ℤ) • (Y * X) = anticomm X Y - comm X Y ∧
    (g_op + I_op * Ω_op) * (g_op - I_op * Ω_op) =
      g_op * g_op - (I_op * Ω_op) * (I_op * Ω_op) - comm g_op (I_op * Ω_op) ∧
    (genV P A C + genSig P A C) * (genV P A C - genSig P A C) = 0 ∧
    genV P A C * genV P A C - genSig P A C * genSig P A C = 0 ∧
    JordanAssoc X Y Z = comm (comm Z X) Y ∧
    JordanAssoc (coneMinus P C) (conePlus P A) (conePlus P A) =
      comm (genSig P A C) (conePlus P A) ∧
    comm X (Y * Z) = comm X Y * Z + Y * comm X Z := by
  refine ⟨by simp only [anticomm, comm]; noncomm_ring,
          by simp only [anticomm, comm]; noncomm_ring,
          by simp only [comm]; noncomm_ring,
          by peirce_nf hP,
          by peirce_nf hP,
          by simp only [JordanAssoc, anticomm, comm]; noncomm_ring,
          by simp only [JordanAssoc]; peirce_nf hP,
          by simp only [comm]; noncomm_ring⟩

/-- If `N_plus` is square-zero (`N_plus * N_plus = 0`), then its star-adjoint `star N_plus` is also square-zero. -/
theorem star_N_plus_sq [StarRing B] (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    star N_plus * star N_plus = 0 := by
  rw [← star_mul, h_nil, star_zero]

/-- If `N_plus` is von Neumann regular (`N_plus * star N_plus * N_plus = N_plus`), then `star N_plus` is also von Neumann regular. -/
theorem star_N_plus_reg [StarRing B] (N_plus : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * N_plus * star N_plus = star N_plus := by
  have h := congrArg star h_reg
  rw [star_mul, star_mul, star_star, ← mul_assoc] at h
  exact h

/-- **Nilpotent-First Chiral Lorentz, Twistor Incidence, & Élie Cartan Gravity (`nilpotent_first_chiral_lorentz_twistor_cartan_gravity`)**:
For any nilpotent Von Neumann regular operator `N_plus : B` (`N_plus * N_plus = 0` and
`N_plus * star N_plus * N_plus = N_plus`) in any `[Ring B] [StarRing B]`:
1. **Para-Kähler Split Square & Chiral Eigenvalues:**
   `Sigma_op N_plus * Sigma_op N_plus = P_mom N_plus`,
   `Sigma_op N_plus * N_plus = N_plus`, `N_plus * Sigma_op N_plus = -N_plus`,
   `Sigma_op N_plus * star N_plus = -star N_plus`, and `star N_plus * Sigma_op N_plus = star N_plus`.
2. **Emergent SUSY Superalgebra & Poincaré Translation Invariance:**
   `anticomm N_plus (star N_plus) = P_mom N_plus`,
   `anticomm N_plus N_plus = 0`, `anticomm (star N_plus) (star N_plus) = 0`,
   `comm (P_mom N_plus) N_plus = 0`, `comm (P_mom N_plus) (star N_plus) = 0`,
   `comm (Sigma_op N_plus) N_plus = N_plus + N_plus`, and
   `comm (Sigma_op N_plus) (star N_plus) = -(star N_plus + star N_plus)`.
3. **Twistor Incidence & Para-Kähler Isotropic Off-Diagonal Sandwich:**
   `P_twistor N_plus * N_plus = N_plus`, `P_twistor N_plus * star N_plus = 0`, and
   `P_twistor N_plus * N_plus * Q_twistor N_plus = N_plus`.
4. **The Uncertainty–Curvature Anomaly Theorem (`JordanAssoc (star N_+) N_+ N_+ = [Σ, N_+]`) & Two-Index Cartan Symmetries:**
   `JordanAssoc (star N_plus) N_plus N_plus = comm (Sigma_op N_plus) N_plus`,
   `star (G_metric N_mu N_nu) = G_metric N_nu N_mu`,
   `star (R_cartan N_mu N_nu) = R_cartan N_nu N_mu`,
   `G_metric (star N_mu) (star N_nu) = G_metric N_nu N_mu`, and
   `R_cartan (star N_mu) (star N_nu) = -R_cartan N_nu N_mu`. -/
theorem nilpotent_first_chiral_lorentz_twistor_cartan_gravity
    [StarRing B] (N_plus N_mu N_nu : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma_op N_plus * Sigma_op N_plus = P_mom N_plus ∧
    Sigma_op N_plus * N_plus = N_plus ∧
    N_plus * Sigma_op N_plus = -N_plus ∧
    Sigma_op N_plus * star N_plus = -star N_plus ∧
    star N_plus * Sigma_op N_plus = star N_plus ∧
    anticomm N_plus (star N_plus) = P_mom N_plus ∧
    anticomm N_plus N_plus = 0 ∧
    anticomm (star N_plus) (star N_plus) = 0 ∧
    comm (P_mom N_plus) N_plus = 0 ∧
    comm (P_mom N_plus) (star N_plus) = 0 ∧
    comm (Sigma_op N_plus) N_plus = N_plus + N_plus ∧
    comm (Sigma_op N_plus) (star N_plus) = -(star N_plus + star N_plus) ∧
    P_twistor N_plus * N_plus = N_plus ∧
    P_twistor N_plus * star N_plus = 0 ∧
    P_twistor N_plus * N_plus * Q_twistor N_plus = N_plus ∧
    JordanAssoc (star N_plus) N_plus N_plus = comm (Sigma_op N_plus) N_plus ∧
    star (G_metric N_mu N_nu) = G_metric N_nu N_mu ∧
    star (R_cartan N_mu N_nu) = R_cartan N_nu N_mu ∧
    G_metric (star N_mu) (star N_nu) = G_metric N_nu N_mu ∧
    R_cartan (star N_mu) (star N_nu) = -R_cartan N_nu N_mu := by
  have h_star_nil := star_N_plus_sq N_plus h_nil
  have h_star_reg := star_N_plus_reg N_plus h_reg
  have h_Sig_N : Sigma_op N_plus * N_plus = N_plus := by
    dsimp [Sigma_op]
    rw [sub_mul, h_reg, mul_assoc (star N_plus) N_plus N_plus, h_nil, mul_zero, sub_zero]
  have h_N_Sig : N_plus * Sigma_op N_plus = -N_plus := by
    dsimp [Sigma_op]
    rw [mul_sub, ← mul_assoc N_plus N_plus (star N_plus), h_nil, zero_mul,
        ← mul_assoc N_plus (star N_plus) N_plus, h_reg, zero_sub]
  have h_Sig_sN : Sigma_op N_plus * star N_plus = -star N_plus := by
    dsimp [Sigma_op]
    rw [sub_mul, mul_assoc N_plus (star N_plus) (star N_plus), h_star_nil, mul_zero,
        h_star_reg, zero_sub]
  have h_sN_Sig : star N_plus * Sigma_op N_plus = star N_plus := by
    dsimp [Sigma_op]
    rw [mul_sub, ← mul_assoc (star N_plus) N_plus (star N_plus), h_star_reg,
        ← mul_assoc (star N_plus) (star N_plus) N_plus, h_star_nil, zero_mul, sub_zero]
  have h_P_N : P_mom N_plus * N_plus = N_plus := by
    dsimp [P_mom]
    rw [add_mul, h_reg, mul_assoc (star N_plus) N_plus N_plus, h_nil, mul_zero, add_zero]
  have h_N_P : N_plus * P_mom N_plus = N_plus := by
    dsimp [P_mom]
    rw [mul_add, ← mul_assoc N_plus N_plus (star N_plus), h_nil, zero_mul,
        ← mul_assoc N_plus (star N_plus) N_plus, h_reg, zero_add]
  have h_P_sN : P_mom N_plus * star N_plus = star N_plus := by
    dsimp [P_mom]
    rw [add_mul, mul_assoc N_plus (star N_plus) (star N_plus), h_star_nil, mul_zero,
        h_star_reg, zero_add]
  have h_sN_P : star N_plus * P_mom N_plus = star N_plus := by
    dsimp [P_mom]
    rw [mul_add, ← mul_assoc (star N_plus) N_plus (star N_plus), h_star_reg,
        ← mul_assoc (star N_plus) (star N_plus) N_plus, h_star_nil, zero_mul, add_zero]
  refine ⟨?_, h_Sig_N, h_N_Sig, h_Sig_sN, h_sN_Sig, rfl,
          by dsimp [anticomm]; rw [h_nil, add_zero],
          by dsimp [anticomm]; rw [h_star_nil, add_zero],
          by dsimp [comm]; rw [h_P_N, h_N_P, sub_self],
          by dsimp [comm]; rw [h_P_sN, h_sN_P, sub_self],
          by dsimp [comm]; rw [h_Sig_N, h_N_Sig, sub_eq_add_neg, neg_neg],
          by dsimp [comm]; rw [h_Sig_sN, h_sN_Sig, sub_eq_add_neg, ← neg_add],
          h_reg,
          by dsimp [P_twistor]; rw [mul_assoc, h_star_nil, mul_zero],
          ?_, ?_,
          by dsimp [G_metric, anticomm]; rw [star_add, star_mul, star_mul, star_star],
          by dsimp [R_cartan, comm]; rw [star_sub, star_mul, star_mul, star_star],
          by dsimp [G_metric, anticomm]; rw [star_star, add_comm],
          by dsimp [R_cartan, comm]; rw [star_star, neg_sub]⟩
  · calc Sigma_op N_plus * Sigma_op N_plus
      _ = (Sigma_op N_plus * N_plus) * star N_plus -
          (Sigma_op N_plus * star N_plus) * N_plus := by
        dsimp [Sigma_op]; noncomm_ring
      _ = P_mom N_plus := by
        rw [h_Sig_N, h_Sig_sN]; dsimp [P_mom]; noncomm_ring
  · dsimp [P_twistor, Q_twistor]
    calc (N_plus * star N_plus) * N_plus * (star N_plus * N_plus)
      _ = N_plus * (star N_plus * N_plus) := by rw [h_reg]
      _ = N_plus * star N_plus * N_plus := by rw [← mul_assoc N_plus (star N_plus) N_plus]
      _ = N_plus := h_reg
  · calc JordanAssoc (star N_plus) N_plus N_plus
      _ = comm (comm N_plus (star N_plus)) N_plus := by
        simp only [JordanAssoc, anticomm, comm]; noncomm_ring
      _ = comm (Sigma_op N_plus) N_plus := rfl

/-- Concrete non-commutativity (`T16`) and non-vacuity (`T17`) witness in `Matrix (Fin 2) (Fin 2) ℤ`:
certifies that for `curvatureWitnessP = !![1, 0; 0, 0]`, `curvatureWitnessA = !![0, 1; 0, 0]`,
and `curvatureWitnessE10 = !![0, 0; 1, 0]`:
- `curvatureWitnessP` is idempotent (`P² = P`) and non-commuting (`P * E₁₀ ≠ E₁₀ * P`),
- the uncertainty commutator `genSig P A E₁₀` is strictly non-zero (`≠ 0`),
- the emergent metric `genV P A E₁₀` is strictly non-zero (`≠ 0`),
- the soldered Cartan curvature `cartanCurvature2Form P (genPhi P A E₁₀)` is strictly non-zero (`≠ 0`),
- and the grade-`+2` Kantor uncertainty cubic `kantorGp2 P A (coneMinus P E₁₀)` is strictly non-zero (`≠ 0`)! -/
theorem cltcWitness_noncomm_and_nonvanishing_uncertainty_curvature :
    curvatureWitnessP * curvatureWitnessP = curvatureWitnessP ∧
    curvatureWitnessP * curvatureWitnessE10 ≠ curvatureWitnessE10 * curvatureWitnessP ∧
    genSig curvatureWitnessP curvatureWitnessA curvatureWitnessE10 ≠ 0 ∧
    genV curvatureWitnessP curvatureWitnessA curvatureWitnessE10 ≠ 0 ∧
    cartanCurvature2Form curvatureWitnessP
      (genPhi curvatureWitnessP curvatureWitnessA curvatureWitnessE10) ≠ 0 ∧
    kantorGp2 curvatureWitnessP curvatureWitnessA
      (coneMinus curvatureWitnessP curvatureWitnessE10) ≠ 0 := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_⟩
  · intro h
    have h00 := congrArg (fun M : Mat2 => M 0 0) h
    revert h00; decide
  · intro h
    have h00 := congrArg (fun M : Mat2 => M 0 0) h
    revert h00; decide
  · intro h
    have h00 := congrArg (fun M : Mat2 => M 0 0) h
    revert h00; decide
  · intro h
    have h01 := congrArg (fun M : Mat2 => M 0 1) h
    revert h01; decide

end InfoGeometry.OperatorAlgebra.PeirceSpine
