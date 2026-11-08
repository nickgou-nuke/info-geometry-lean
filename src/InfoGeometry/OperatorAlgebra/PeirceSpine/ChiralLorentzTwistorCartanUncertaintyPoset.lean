/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ParaKahlerBregmanModularNoetherPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornPeirceTetradPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorCornerAnomaly
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceMaurerCartanCurvatureWitness
import InfoGeometry.OperatorAlgebra.PeirceSpine.WilsonPlaquette
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

theorem causalEdge_strict_rank {u v : ChiralLorentzTwistorCartanStage}
    (h : causalEdge u v) : rank u < rank v := by
  cases h <;> decide

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

/-! ## 5. Stage `CL₄`: Peirce Chart Idempotency, Aporia, & Double-Commutator Identity -/

/-- Forward Peirce chart expression `(1 + N₊(A)) * P * (1 - N₊(A))`. -/
def superGrassmannChartPlus (P A : B) : B :=
  (1 + conePlus P A) * P * (1 - conePlus P A)

/-- Backward Peirce chart expression `(1 - N₋(C)) * P * (1 + N₋(C))`. -/
def superGrassmannChartMinus (P C : B) : B :=
  (1 - coneMinus P C) * P * (1 + coneMinus P C)

/-- **Stage `CL₄` (`archetype_CL4_super_grassmannian_parakahler_structure`)**:
1. **Idempotency Defect of the Additive Peirce Perturbation:**
   - The additive perturbation `Ψ = P + genPhi P A C` has the exact algebraic idempotency
     defect `(P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C) = genV P A C`,
   - Both chiral unipotent Peirce chart expressions are exact idempotents:
     `superGrassmannChartPlus P A = P - conePlus P A`,
     `superGrassmannChartMinus P C = P - coneMinus P C`,
     `superGrassmannChartPlus P A * superGrassmannChartPlus P A = superGrassmannChartPlus P A`, and
     `superGrassmannChartMinus P C * superGrassmannChartMinus P C = superGrassmannChartMinus P C`.
2. **Non-Commutative Peirce Chart Commutator & Anticommutator:**
   - The commutator of the forward and backward Peirce chart expressions splits into the even
     **uncertainty commutator `Σ = [N_+, N_-]`** and the odd boost `Φ = N_+ + N_-`:
     `comm (superGrassmannChartPlus P A) (superGrassmannChartMinus P C) = genSig P A C + genPhi P A C`
     and `evenGrade P (comm (superGrassmannChartPlus P A) (superGrassmannChartMinus P C)) = genSig P A C`,
   - Their anticommutator is the algebraic term `genV`:
     `anticomm (superGrassmannChartPlus P A) (superGrassmannChartMinus P C) - (2 : ℤ) • P = genV P A C - genPhi P A C`.
3. **Double-Commutator Identity and Second-Order Split:**
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
  have hCross : P * genPhi P A C + genPhi P A C * P = genPhi P A C := by
    peirce_nf hP
  have hAporia :
      (P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C) =
        genV P A C := by
    have hDefect := idempotencyDefect_idempotent_add_of_cross_sum hP hCross
    have hPhiSq : genPhi P A C * genPhi P A C = genV P A C := by
      peirce_nf hP
    simpa [idempotencyDefect, hPhiSq] using hDefect
  refine ⟨hAporia, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
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
     `kantorG0 P A C (kantorG0 P A C X) - (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) = genSig P A C * X * genSig P A C`.
4. **Reference-Corner Curvature Pairing:** With `K = upperHomotopeBracket P C A Z` and `D = coneMinus P C`,
   `comm K D = comm (genSig P A C) (genV P Z C)`, while
   `anticomm K D = comm (genSig P A C) (genSig P Z C)`. -/
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
      genSig P A C * X * genSig P A C ∧
    comm (upperHomotopeBracket P C A Z) (coneMinus P C) =
      comm (genSig P A C) (genV P Z C) ∧
    anticomm (upperHomotopeBracket P C A Z) (coneMinus P C) =
      comm (genSig P A C) (genSig P Z C) := by
  refine ⟨?_, ?_, ?_, ?_, upper_homotope_jacobi hP C A Z W,
          (upper_kantor_anomaly_corner hP A C Z).2, ?_, ?_, ?_, ?_,
          upper_anomaly_reference_commutator hP A C Z,
          upper_anomaly_reference_anticommutator hP A C Z⟩
  · simp only [genSig]; peirce_nf hP
  · simp only [genSig]; peirce_nf hP
  · simp only [upperHomotopeBracket, opKantorAnomaly, genSig]; peirce_nf hP
  · simp only [genSig]; peirce_nf hP
  · simp only [kantorGp2, genSig]; peirce_nf hP
  · simp only [kantorGm2, genSig]; peirce_nf hP
  · simp only [kantorGp2, kantorGm2, qgtPlus, qgtMinus]; peirce_nf hP
  · simp only [kantorG0, kantorTriple, kantorGp2, kantorGm2, genSig]; peirce_nf hP

/-- The higher-grade uncertainty anomaly is the translation commutator for two
upper-cone modes.  For an idempotent cut, the products of the two upper cones
vanish, so `[V(A,C), N₊(Z)]` is exactly the skew associative corner product
already owned by `upperHomotopeBracket`. -/
theorem translation_commutator_eq_upper_uncertainty_anomaly
    {P : B} (hP : P * P = P) (A C Z : B) :
    comm (genV P A C) (conePlus P Z) = upperHomotopeBracket P C A Z := by
  simp only [genV, anticomm, comm, upperHomotopeBracket, opKantorAnomaly,
    conePlus, coneMinus]
  peirce_nf hP

/-! ### EC₆ countermodel: the two reference-corner pairings are ordered oppositely
to the later prose claim.  This is a genuine `4 × 4` integer operator matrix
model with a rank-two Peirce cut and noncommuting matrix-unit channel data. -/

private abbrev EC6CounterMatrix := Matrix (Fin 4) (Fin 4) ℤ

private def ec6CounterCut : EC6CounterMatrix :=
  Matrix.single 0 0 1 + Matrix.single 1 1 1

private def ec6CounterA₁ : EC6CounterMatrix := Matrix.single 0 3 1

private def ec6CounterA₂ : EC6CounterMatrix := Matrix.single 1 2 1

private def ec6CounterC₀ : EC6CounterMatrix :=
  Matrix.single 2 0 1 + Matrix.single 3 1 1

/-- Concrete evaluation of the EC₆ reference-corner pairings.  The commutator
of the Kantor anomaly with the lower corner is the mixed `Σ`–`V` bracket;
the anticommutator is the `Σ`–`Σ` bracket.  In particular, this model refutes
the swapped universal assignment in the raw proposal. -/
theorem ec6_reference_pairing_order_countermodel :
    comm
        (upperHomotopeBracket ec6CounterCut ec6CounterC₀
          ec6CounterA₁ ec6CounterA₂)
        (coneMinus ec6CounterCut ec6CounterC₀) =
      comm (genSig ec6CounterCut ec6CounterA₁ ec6CounterC₀)
        (genV ec6CounterCut ec6CounterA₂ ec6CounterC₀) ∧
    anticomm
        (upperHomotopeBracket ec6CounterCut ec6CounterC₀
          ec6CounterA₁ ec6CounterA₂)
        (coneMinus ec6CounterCut ec6CounterC₀) =
      comm (genSig ec6CounterCut ec6CounterA₁ ec6CounterC₀)
        (genSig ec6CounterCut ec6CounterA₂ ec6CounterC₀) ∧
    comm
        (upperHomotopeBracket ec6CounterCut ec6CounterC₀
          ec6CounterA₁ ec6CounterA₂)
        (coneMinus ec6CounterCut ec6CounterC₀) ≠
      comm (genSig ec6CounterCut ec6CounterA₁ ec6CounterC₀)
        (genSig ec6CounterCut ec6CounterA₂ ec6CounterC₀) := by
  decide

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
    (P * X * P + conePlus P X + coneMinus P X + (1 - P) * X * (1 - P) = X ∧
      invS P * invS P = 1 ∧
      invS P * evenGrade P X * invS P = evenGrade P X ∧
      invS P * oddGrade P X * invS P = -oddGrade P X ∧
      conePlus P A₁ * conePlus P X = 0 ∧
      coneMinus P C₁ * coneMinus P X = 0 ∧
      comm (invS P) (conePlus P A₁) = (2 : ℤ) • conePlus P A₁ ∧
      comm (invS P) (coneMinus P C₁) = -((2 : ℤ) • coneMinus P C₁)) ∧
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
    comm (upperHomotopeBracket P C₁ A₁ Z) (coneMinus P C₁) =
      comm (genSig P A₁ C₁) (genV P Z C₁) ∧
    anticomm (upperHomotopeBracket P C₁ A₁ Z) (coneMinus P C₁) =
      comm (genSig P A₁ C₁) (genSig P Z C₁) ∧
    (g X_op X_op * g Y_op Y_op ≥ (g X_op Y_op) ^ 2 + (1 / 4 : ℝ) * (Ω X_op Y_op) ^ 2) := by
  have hCL1 := archetype_CL1_primordial_chiral_cut_and_fourfold_peirce_anatomy hP A₁ C₁ X
  have hCL2 := archetype_CL2_chiral_dual_real_lorentz_representation hP A₁ C₁ A₂ C₂
  have hCL3 := archetype_CL3_poincare_semidirect_and_susy_superalgebra hP X A₁ C₁ A₂ C₂
  have hCL4 := archetype_CL4_super_grassmannian_parakahler_structure hP A₁ C₁ X
  have hCL5 := archetype_CL5_twistor_incidence_and_positive_amplituhedron hP hPstar A₁ C₁ X X X X X X
  have hCL6 := archetype_CL6_uncertainty_as_creator_of_metric_and_spin_curvature hP A₁ C₁
  have hCL7 := archetype_CL7_elie_cartan_torsion_and_spin_connection_gravity hP A₁ C₁
  have hCL8 := archetype_CL8_higher_grade_uncertainty_anomaly_in_symmetry_closure hP A₁ C₁ Z Z X
  have hCL9 := archetype_CL9_recursive_meta_tower_and_hilbert_cramer_rao_curvature_bound hP A₁ C₁ X ψ X_op Y_op
  exact ⟨ChiralLorentzTwistorCartanStage.causalEdge_acyclic, hCL1,
    ⟨hCL2.2.2.2.2.1, hCL2.2.2.2.2.2.1⟩,
    ⟨hCL3.2.2.2.2.2.1, hCL3.2.2.2.2.2.2.2.1⟩,
    ⟨hCL4.2.2.2.2.2.1, hCL4.2.2.2.2.2.2.2.1⟩,
    hCL5.2.2.2.2.2.2.2.2,
    ⟨hCL6.2.2.1, hCL6.2.2.2.2.2.2.1⟩,
    ⟨hCL7.1, hCL7.2.2.2.2.2.1⟩,
    ⟨hCL8.2.2.1, hCL8.2.2.2.2.2.2.2.2.2.1⟩,
    hCL8.2.2.2.2.2.2.2.2.2.2.1,
    hCL8.2.2.2.2.2.2.2.2.2.2.2,
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

theorem star_N_plus_sq [StarRing B] (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    star N_plus * star N_plus = 0 := by
  rw [← star_mul, h_nil, star_zero]

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

/-- **Nilpotent-First Orthogonal Projector & Emergent Dirac Metric Reconstruction
(`nilpotent_first_orthogonal_projector_and_dirac_metric_reconstruction`, Turns 34–40)**:
In any `[Ring B] [StarRing B]`, a single nilpotent Von Neumann regular operator `N_plus`
(`N_plus * N_plus = 0` and `N_plus * star N_plus * N_plus = N_plus`) reconstructs:
1. **Orthogonal Self-Adjoint Projectors (`P_twistor`, `Q_twistor`) Without a Prior Idempotent:**
   - `P_twistor N_plus * P_twistor N_plus = P_twistor N_plus` and `star (P_twistor N_plus) = P_twistor N_plus`,
   - `Q_twistor N_plus * Q_twistor N_plus = Q_twistor N_plus` and `star (Q_twistor N_plus) = Q_twistor N_plus`,
   - `P_twistor N_plus * Q_twistor N_plus = 0` and `Q_twistor N_plus * P_twistor N_plus = 0`.
2. **Dynamic Ladder Commutators (`[P, N_+] = N_+`, `[P, N_+⋆] = -N_+⋆`):**
   - `comm (P_twistor N_plus) N_plus = N_plus` and `comm (P_twistor N_plus) (star N_plus) = -star N_plus`.
3. **Emergent Dirac–Clifford Metric Algebra (`Φ_nil = N_+ + N_+⋆`, `J_nil = N_+ - N_+⋆`):**
   - `(N_plus + star N_plus) * (N_plus + star N_plus) = P_mom N_plus`,
   - `(N_plus - star N_plus) * (N_plus - star N_plus) = -P_mom N_plus`,
   - `anticomm (N_plus + star N_plus) (N_plus - star N_plus) = 0`,
   - `comm (N_plus + star N_plus) (N_plus - star N_plus) = -(Sigma_op N_plus + Sigma_op N_plus)`. -/
theorem nilpotent_first_orthogonal_projector_and_dirac_metric_reconstruction
    [StarRing B] (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P_twistor N_plus * P_twistor N_plus = P_twistor N_plus ∧
    star (P_twistor N_plus) = P_twistor N_plus ∧
    Q_twistor N_plus * Q_twistor N_plus = Q_twistor N_plus ∧
    star (Q_twistor N_plus) = Q_twistor N_plus ∧
    P_twistor N_plus * Q_twistor N_plus = 0 ∧
    Q_twistor N_plus * P_twistor N_plus = 0 ∧
    comm (P_twistor N_plus) N_plus = N_plus ∧
    comm (P_twistor N_plus) (star N_plus) = -star N_plus ∧
    (N_plus + star N_plus) * (N_plus + star N_plus) = P_mom N_plus ∧
    (N_plus - star N_plus) * (N_plus - star N_plus) = -P_mom N_plus ∧
    anticomm (N_plus + star N_plus) (N_plus - star N_plus) = 0 ∧
    comm (N_plus + star N_plus) (N_plus - star N_plus) = -(Sigma_op N_plus + Sigma_op N_plus) := by
  have h_star_nil := star_N_plus_sq N_plus h_nil
  have h_star_reg := star_N_plus_reg N_plus h_reg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [P_twistor]
    calc (N_plus * star N_plus) * (N_plus * star N_plus)
      _ = (N_plus * star N_plus * N_plus) * star N_plus := by simp only [mul_assoc]
      _ = N_plus * star N_plus := by rw [h_reg]
  · dsimp [P_twistor]; rw [star_mul, star_star]
  · dsimp [Q_twistor]
    calc (star N_plus * N_plus) * (star N_plus * N_plus)
      _ = (star N_plus * N_plus * star N_plus) * N_plus := by simp only [mul_assoc]
      _ = star N_plus * N_plus := by rw [h_star_reg]
  · dsimp [Q_twistor]; rw [star_mul, star_star]
  · dsimp [P_twistor, Q_twistor]
    calc (N_plus * star N_plus) * (star N_plus * N_plus)
      _ = N_plus * (star N_plus * star N_plus) * N_plus := by simp only [mul_assoc]
      _ = 0 := by rw [h_star_nil, mul_zero, zero_mul]
  · dsimp [P_twistor, Q_twistor]
    calc (star N_plus * N_plus) * (N_plus * star N_plus)
      _ = star N_plus * (N_plus * N_plus) * star N_plus := by simp only [mul_assoc]
      _ = 0 := by rw [h_nil, mul_zero, zero_mul]
  · dsimp [P_twistor, comm]
    rw [h_reg, ← mul_assoc N_plus N_plus (star N_plus), h_nil, zero_mul, sub_zero]
  · dsimp [P_twistor, comm]
    rw [mul_assoc N_plus (star N_plus) (star N_plus), h_star_nil, mul_zero,
        ← mul_assoc (star N_plus) N_plus (star N_plus), h_star_reg, zero_sub]
  · dsimp [P_mom]
    rw [add_mul, mul_add, mul_add, h_nil, h_star_nil]; abel
  · dsimp [P_mom]
    rw [sub_mul, mul_sub, mul_sub, h_nil, h_star_nil]; noncomm_ring
  · dsimp [anticomm]
    have h1 : (N_plus + star N_plus) * (N_plus - star N_plus) =
        -(N_plus * star N_plus) + star N_plus * N_plus := by
      rw [add_mul, mul_sub, mul_sub, h_nil, h_star_nil]; noncomm_ring
    have h2 : (N_plus - star N_plus) * (N_plus + star N_plus) =
        N_plus * star N_plus - star N_plus * N_plus := by
      rw [sub_mul, mul_add, mul_add, h_nil, h_star_nil]; noncomm_ring
    rw [h1, h2]; noncomm_ring
  · dsimp [comm, Sigma_op]
    have h1 : (N_plus + star N_plus) * (N_plus - star N_plus) =
        -(N_plus * star N_plus) + star N_plus * N_plus := by
      rw [add_mul, mul_sub, mul_sub, h_nil, h_star_nil]; noncomm_ring
    have h2 : (N_plus - star N_plus) * (N_plus + star N_plus) =
        N_plus * star N_plus - star N_plus * N_plus := by
      rw [sub_mul, mul_add, mul_add, h_nil, h_star_nil]; noncomm_ring
    rw [h1, h2]; noncomm_ring

/-! ## 13. Archetype XVII: Élie Cartan Supergravity, MacDowell–Mansouri Curvature–Torsion Split, & Order-3 Nilpotent Flag Reconstruction -/

/-- Even-grade Lorentz Spin Connection `Ω = P W P + (1 - P) W (1 - P) ∈ 𝔤₀`. -/
def spinConn (P W : B) : B :=
  P * W * P + (1 - P) * W * (1 - P)

/-- Unified Élie Cartan Super-Connection `𝓐 = Ω + Φ = spinConn P W + genPhi P A C ∈ 𝔤₀ ⊕ 𝔤₁`. -/
def cartanConn (P W A C : B) : B :=
  spinConn P W + genPhi P A C

/-- Full Cartan Curvature 2-Form `𝓕₁₂ = [𝓐₁, 𝓐₂]`. -/
def cartanFullCurv (P W₁ A₁ C₁ W₂ A₂ C₂ : B) : B :=
  comm (cartanConn P W₁ A₁ C₁) (cartanConn P W₂ A₂ C₂)

/-- Even Bosonic Riemann–Cartan / MacDowell–Mansouri Curvature `𝓡₁₂ = [Ω₁, Ω₂] + [Φ₁, Φ₂] ∈ 𝔤₀`. -/
def riemannCartanCurv (P W₁ A₁ C₁ W₂ A₂ C₂ : B) : B :=
  comm (spinConn P W₁) (spinConn P W₂) + comm (genPhi P A₁ C₁) (genPhi P A₂ C₂)

/-- Odd Fermionic Élie Cartan Covariant Torsion `𝓣₁₂ = [Ω₁, Φ₂] - [Ω₂, Φ₁] ∈ 𝔤₁`. -/
def elieCartanTorsion (P W₁ A₁ C₁ W₂ A₂ C₂ : B) : B :=
  comm (spinConn P W₁) (genPhi P A₂ C₂) - comm (spinConn P W₂) (genPhi P A₁ C₁)

/-- **Archetype XVII (`elie_cartan_supergravity_macdowell_mansouri_and_bianchi_closure`, Turns 54–62)**:
1. **Cartan Curvature–Torsion Decomposition (`[𝓐₁, 𝓐₂] = 𝓡₁₂ + 𝓣₁₂`):**
   `cartanFullCurv P W₁ A₁ C₁ W₂ A₂ C₂ = riemannCartanCurv P W₁ A₁ C₁ W₂ A₂ C₂ + elieCartanTorsion P W₁ A₁ C₁ W₂ A₂ C₂`.
2. **Exact `ℤ₂` Chiral Grading of Curvature (`[S_P, 𝓡₁₂] = 0`) and Torsion (`{S_P, 𝓣₁₂} = 0`):**
   `comm (invS P) (riemannCartanCurv P W₁ A₁ C₁ W₂ A₂ C₂) = 0` and
   `anticomm (invS P) (elieCartanTorsion P W₁ A₁ C₁ W₂ A₂ C₂) = 0`.
3. **Single-Operator MacDowell–Mansouri Cartan Square (`(Ω + Φ)² = (Ω² + V) + {Ω, Φ}`):**
   `cartanConn P W₁ A₁ C₁ * cartanConn P W₁ A₁ C₁ = (spinConn P W₁ * spinConn P W₁ + genV P A₁ C₁) + anticomm (spinConn P W₁) (genPhi P A₁ C₁)`.
4. **Spontaneous Gravitational Curvature from Pure Frame Uncertainty (`W₁ = W₂ = 0`):**
   `cartanFullCurv P 0 A₁ C₁ 0 A₂ C₂ = comm (genPhi P A₁ C₁) (genPhi P A₂ C₂)`.
5. **Unified Bianchi–Cartan Jacobi Identity (`[𝓐₁, 𝓕₂₃] + [𝓐₂, 𝓕₃₁] + [𝓐₃, 𝓕₁₂] = 0`):**
   `comm (cartanConn P W₁ A₁ C₁) (cartanFullCurv P W₂ A₂ C₂ W₃ A₃ C₃) + comm (cartanConn P W₂ A₂ C₂) (cartanFullCurv P W₃ A₃ C₃ W₁ A₁ C₁) + comm (cartanConn P W₃ A₃ C₃) (cartanFullCurv P W₁ A₁ C₁ W₂ A₂ C₂) = 0`. -/
theorem elie_cartan_supergravity_macdowell_mansouri_and_bianchi_closure
    {P : B} (hP : P * P = P) (W₁ A₁ C₁ W₂ A₂ C₂ W₃ A₃ C₃ : B) :
    cartanFullCurv P W₁ A₁ C₁ W₂ A₂ C₂ =
      riemannCartanCurv P W₁ A₁ C₁ W₂ A₂ C₂ + elieCartanTorsion P W₁ A₁ C₁ W₂ A₂ C₂ ∧
    comm (invS P) (riemannCartanCurv P W₁ A₁ C₁ W₂ A₂ C₂) = 0 ∧
    anticomm (invS P) (elieCartanTorsion P W₁ A₁ C₁ W₂ A₂ C₂) = 0 ∧
    cartanConn P W₁ A₁ C₁ * cartanConn P W₁ A₁ C₁ =
      (spinConn P W₁ * spinConn P W₁ + genV P A₁ C₁) +
        anticomm (spinConn P W₁) (genPhi P A₁ C₁) ∧
    cartanFullCurv P 0 A₁ C₁ 0 A₂ C₂ = comm (genPhi P A₁ C₁) (genPhi P A₂ C₂) ∧
    comm (cartanConn P W₁ A₁ C₁) (cartanFullCurv P W₂ A₂ C₂ W₃ A₃ C₃) +
      comm (cartanConn P W₂ A₂ C₂) (cartanFullCurv P W₃ A₃ C₃ W₁ A₁ C₁) +
      comm (cartanConn P W₃ A₃ C₃) (cartanFullCurv P W₁ A₁ C₁ W₂ A₂ C₂) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cartanFullCurv, cartanConn, riemannCartanCurv, elieCartanTorsion, comm]
    noncomm_ring
  · simp only [riemannCartanCurv, spinConn]; peirce_nf hP
  · simp only [elieCartanTorsion, spinConn]; peirce_nf hP
  · simp only [cartanConn, spinConn]; peirce_nf hP
  · simp only [cartanFullCurv, cartanConn, spinConn, mul_zero, zero_mul, add_zero, zero_add]
  · simp only [cartanFullCurv, comm]; noncomm_ring

/-- Principal Order-3 Nilpotent Raising Operator `N₃ ∈ Matrix (Fin 3) (Fin 3) ℤ` (`N₃² ≠ 0`, `N₃³ = 0`). -/
def nilRaise3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     0, 0, 0]

/-- Principal Order-3 Nilpotent Lowering Operator `M₃ ∈ Matrix (Fin 3) (Fin 3) ℤ` (`M₃² ≠ 0`, `M₃³ = 0`). -/
def nilLower3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 0;
     2, 0, 0;
     0, 2, 0]

/-- Emergent `sl₂` Cartan Grading Diagonal `H₃ = [N₃, M₃] = diag(2, 0, -2)`. -/
def cartanDiag3 : Matrix (Fin 3) (Fin 3) ℤ :=
  nilRaise3 * nilLower3 - nilLower3 * nilRaise3

/-- Highest-weight spectral projector `P₁ = diag(1, 0, 0)` reconstructed from `N₃² M₃²`. -/
def nilFlagProj1 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 0;
     0, 0, 0]

/-- Middle-weight spectral projector `P₂ = diag(0, 1, 0)` reconstructed from `2 N₃ M₃ - N₃² M₃²`. -/
def nilFlagProj2 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 0;
     0, 1, 0;
     0, 0, 0]

/-- Lowest-weight spectral projector `P₃ = diag(0, 0, 1)` reconstructed from `M₃² N₃²`. -/
def nilFlagProj3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 0;
     0, 0, 0;
     0, 0, 1]

/-- Non-commutativity witness for the `3 × 3` order-3 nilpotent carrier (`N₃ M₃ ≠ M₃ N₃`). -/
theorem nilRaise3_nilLower3_noncomm :
    nilRaise3 * nilLower3 ≠ nilLower3 * nilRaise3 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 0 0) h
  revert h00; decide

/-- **Order-3 Jacobson–Morozov Nilpotent Flag & Spectral Projector Reconstruction
(`order3_nilpotent_flag_projector_reconstruction`, Turns 30, 33, 34)**:
1. **Strict Order-3 Nilpotency (`N₃² ≠ 0`, `N₃³ = 0`):**
   `nilRaise3 * nilRaise3 ≠ 0` and `nilRaise3 * nilRaise3 * nilRaise3 = 0`.
2. **Jacobson–Morozov `sl₂` Commutation (`[H₃, N₃] = 2 N₃`, `[H₃, M₃] = -2 M₃`):**
   `cartanDiag3 * nilRaise3 - nilRaise3 * cartanDiag3 = (2 : ℤ) • nilRaise3` and
   `cartanDiag3 * nilLower3 - nilLower3 * cartanDiag3 = -((2 : ℤ) • nilLower3)`.
3. **Nilpotent Reconstruction of the 3-State Orthogonal Projector Flag (`P₁, P₂, P₃`):**
   - `(nilRaise3 * nilRaise3) * (nilLower3 * nilLower3) = (4 : ℤ) • nilFlagProj1`,
   - `(2 : ℤ) • (nilRaise3 * nilLower3) - (nilRaise3 * nilRaise3) * (nilLower3 * nilLower3) = (4 : ℤ) • nilFlagProj2`,
   - `(nilLower3 * nilLower3) * (nilRaise3 * nilRaise3) = (4 : ℤ) • nilFlagProj3`,
   - `nilFlagProj1 + nilFlagProj2 + nilFlagProj3 = 1`,
   - `nilFlagProj1 * nilFlagProj1 = nilFlagProj1`, `nilFlagProj2 * nilFlagProj2 = nilFlagProj2`,
     `nilFlagProj3 * nilFlagProj3 = nilFlagProj3`, and `nilFlagProj1 * nilFlagProj2 = 0`. -/
theorem order3_nilpotent_flag_projector_reconstruction :
    nilRaise3 * nilRaise3 ≠ 0 ∧
    nilRaise3 * nilRaise3 * nilRaise3 = 0 ∧
    cartanDiag3 * nilRaise3 - nilRaise3 * cartanDiag3 = (2 : ℤ) • nilRaise3 ∧
    cartanDiag3 * nilLower3 - nilLower3 * cartanDiag3 = -((2 : ℤ) • nilLower3) ∧
    (nilRaise3 * nilRaise3) * (nilLower3 * nilLower3) = (4 : ℤ) • nilFlagProj1 ∧
    (2 : ℤ) • (nilRaise3 * nilLower3) - (nilRaise3 * nilRaise3) * (nilLower3 * nilLower3) =
      (4 : ℤ) • nilFlagProj2 ∧
    (nilLower3 * nilLower3) * (nilRaise3 * nilRaise3) = (4 : ℤ) • nilFlagProj3 ∧
    nilFlagProj1 + nilFlagProj2 + nilFlagProj3 = 1 ∧
    nilFlagProj1 * nilFlagProj1 = nilFlagProj1 ∧
    nilFlagProj2 * nilFlagProj2 = nilFlagProj2 ∧
    nilFlagProj3 * nilFlagProj3 = nilFlagProj3 ∧
    nilFlagProj1 * nilFlagProj2 = 0 := by
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide, by decide, by decide⟩
  intro h
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 0 2) h
  revert h02; decide

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

/-- In the concrete noncommutative `2 × 2` operator carrier, the additive
chiral perturbation of the Peirce cut has defect exactly equal to the local
identity. This realizes the general aporia formula with nonzero support. -/
theorem cltcWitness_additive_chiral_aporia_eq_one :
    let Ψ := curvatureWitnessP +
      genPhi curvatureWitnessP curvatureWitnessA curvatureWitnessE10
    Ψ * Ψ - Ψ = (1 : Mat2) := by
  have hP : curvatureWitnessP * curvatureWitnessP = curvatureWitnessP := by decide
  calc
    _ = genV curvatureWitnessP curvatureWitnessA curvatureWitnessE10 :=
      (archetype_CL4_super_grassmannian_parakahler_structure hP
        curvatureWitnessA curvatureWitnessE10 0).1
    _ = 1 := by decide

/-- This finite matrix perturbation is not idempotent: its defect is the
nonzero identity operator. -/
theorem cltcWitness_additive_chiral_perturbation_not_idempotent :
    (curvatureWitnessP +
      genPhi curvatureWitnessP curvatureWitnessA curvatureWitnessE10) *
      (curvatureWitnessP +
        genPhi curvatureWitnessP curvatureWitnessA curvatureWitnessE10) ≠
      curvatureWitnessP +
        genPhi curvatureWitnessP curvatureWitnessA curvatureWitnessE10 := by
  intro hIdem
  have hDefect := cltcWitness_additive_chiral_aporia_eq_one
  change (curvatureWitnessP +
      genPhi curvatureWitnessP curvatureWitnessA curvatureWitnessE10) *
      (curvatureWitnessP +
        genPhi curvatureWitnessP curvatureWitnessA curvatureWitnessE10) -
      (curvatureWitnessP +
        genPhi curvatureWitnessP curvatureWitnessA curvatureWitnessE10) =
      (1 : Mat2) at hDefect
  rw [hIdem, sub_self] at hDefect
  exact one_ne_zero hDefect.symm

/-! ## 14. Chunks 200–217: ordered products, projector identities, star-Gramian identities, power-vanishing consequences, and selected `4 × 4` matrix commutator identities -/

/-- 4-Link Élie Cartan Holonomy Plaquette Loop `U_□ = (1 + N_+)(1 + N_-)(1 - N_+)(1 - N_-)`. -/
def cartanPlaquette (P A C : B) : B :=
  (1 + conePlus P A) * (1 + coneMinus P C) * (1 - conePlus P A) * (1 - coneMinus P C)

/-- Reversed 4-Link Élie Cartan Holonomy Plaquette Loop `U_□^rev = (1 + N_-)(1 + N_+)(1 - N_-)(1 - N_+)`. -/
def cartanPlaquetteRev (P A C : B) : B :=
  (1 + coneMinus P C) * (1 + conePlus P A) * (1 - coneMinus P C) * (1 - conePlus P A)

/-- **Stage P₁ (`stage_P1_nilpotent_first_genesis_of_projectors`, Chunk 217 of `1ofaG3fBD1VlprR7ShtsdctpOVRjmjB9f`)**:
From two square-zero nilpotents `N_p * N_p = 0`, `N_m * N_m = 0` satisfying the von Neumann / Jordan
regularity pairing `N_p * N_m * N_p = N_p` and `N_m * N_p * N_m = N_m` (without postulating an
idempotent `P` in advance), the products `P := N_p * N_m` and `Q := N_m * N_p` precipitate out as
mutually orthogonal idempotents, `V := P + Q` is an idempotent metric, and `Φ := N_p + N_m`,
`J := N_p - N_m` are tripotent Dirac generators (`Φ³ = Φ`, `J³ = -J`). -/
theorem stage_P1_nilpotent_first_genesis_of_projectors
    {N_p N_m : B} (hp2 : N_p * N_p = 0) (hm2 : N_m * N_m = 0)
    (hRegP : N_p * N_m * N_p = N_p) (hRegM : N_m * N_p * N_m = N_m) :
    let P := N_p * N_m
    let Q := N_m * N_p
    let V := P + Q
    let Φ := N_p + N_m
    let J := N_p - N_m
    P * P = P ∧
    Q * Q = Q ∧
    P * Q = 0 ∧
    Q * P = 0 ∧
    V * V = V ∧
    Φ * Φ = V ∧
    J * J = -V ∧
    Φ * Φ * Φ = Φ ∧
    J * J * J = -J := by
  intro P Q V Φ J
  have hP_idem : P * P = P := by
    change (N_p * N_m) * (N_p * N_m) = N_p * N_m
    rw [← mul_assoc (N_p * N_m) N_p N_m, hRegP]
  have hQ_idem : Q * Q = Q := by
    change (N_m * N_p) * (N_m * N_p) = N_m * N_p
    rw [← mul_assoc (N_m * N_p) N_m N_p, hRegM]
  have hPQ : P * Q = 0 := by
    change (N_p * N_m) * (N_m * N_p) = 0
    calc (N_p * N_m) * (N_m * N_p)
      _ = N_p * (N_m * N_m) * N_p := by simp only [mul_assoc]
      _ = 0 := by rw [hm2, mul_zero, zero_mul]
  have hQP : Q * P = 0 := by
    change (N_m * N_p) * (N_p * N_m) = 0
    calc (N_m * N_p) * (N_p * N_m)
      _ = N_m * (N_p * N_p) * N_m := by simp only [mul_assoc]
      _ = 0 := by rw [hp2, mul_zero, zero_mul]
  have hV_idem : V * V = V := by
    change (P + Q) * (P + Q) = P + Q
    simp only [add_mul, mul_add, hP_idem, hQ_idem, hPQ, hQP, add_zero, zero_add]
  have hPhi2 : Φ * Φ = V := by
    change (N_p + N_m) * (N_p + N_m) = N_p * N_m + N_m * N_p
    simp only [add_mul, mul_add, hp2, hm2, add_zero, zero_add]
    abel
  have hJ2 : J * J = -V := by
    change (N_p - N_m) * (N_p - N_m) = -(N_p * N_m + N_m * N_p)
    simp only [sub_mul, mul_sub, hp2, hm2]; abel
  have hVNp : V * N_p = N_p := by
    change (N_p * N_m + N_m * N_p) * N_p = N_p
    rw [add_mul, hRegP, mul_assoc N_m N_p N_p, hp2, mul_zero, add_zero]
  have hVNm : V * N_m = N_m := by
    change (N_p * N_m + N_m * N_p) * N_m = N_m
    rw [add_mul, mul_assoc N_p N_m N_m, hm2, mul_zero, zero_add, hRegM]
  refine ⟨hP_idem, hQ_idem, hPQ, hQP, hV_idem, hPhi2, hJ2, ?_, ?_⟩
  · rw [hPhi2]
    change V * (N_p + N_m) = N_p + N_m
    rw [mul_add, hVNp, hVNm]
  · rw [hJ2]
    change (-V) * (N_p - N_m) = -(N_p - N_m)
    rw [neg_mul, mul_sub, hVNp, hVNm]

/-- **Stage P₃ (`stage_P3_uncertainty_creates_elie_cartan_curvature_and_torsion`, Chunk 217 of `1ofaG3fBD1VlprR7ShtsdctpOVRjmjB9f`)**:
The ordered plaquettes retain their quadratic Peirce-corner terms. Their sum has symmetric even
defect `-V²`, and their difference has odd part `-2 VJ`; these formulas do not assume the corner
products are idempotent. -/
theorem stage_P3_uncertainty_creates_elie_cartan_curvature_and_torsion
    {P : B} (hP : P * P = P) (A C : B) :
    cartanPlaquette P A C - 1 =
      genSig P A C - genV P A C * genJ P A C +
        qgtPlus P A C * qgtPlus P A C ∧
    evenGrade P (cartanPlaquette P A C - cartanPlaquetteRev P A C) =
      (2 : ℤ) • genSig P A C +
        (qgtPlus P A C * qgtPlus P A C - qgtMinus P A C * qgtMinus P A C) ∧
    evenGrade P ((1 - cartanPlaquette P A C) + (1 - cartanPlaquetteRev P A C)) =
      -(genV P A C * genV P A C) ∧
    oddGrade P (cartanPlaquette P A C - 1) =
      -(genV P A C * genJ P A C) ∧
    oddGrade P (cartanPlaquette P A C - cartanPlaquetteRev P A C) =
      -((2 : ℤ) • (genV P A C * genJ P A C)) := by
  dsimp only [cartanPlaquette, cartanPlaquetteRev, evenGrade, oddGrade,
    qgtPlus, qgtMinus]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Chunk 209 (`peirce_star_gramian_and_fubini_study_chordal_metric` of `1ofaG3fBD1VlprR7ShtsdctpOVRjmjB9f`)**:
In any `[Ring B] [StarRing B]`, when `P` is a self-adjoint projection (`P * P = P`, `star P = P`)
and `X` is self-adjoint (`star X = X`):
1. `star (conePlus P X) = coneMinus P X` and `star (coneMinus P X) = conePlus P X`,
2. `star (genPhi P X X) = genPhi P X X`, `star (genJ P X X) = -genJ P X X`,
   `star (genV P X X) = genV P X X`, and `star (genSig P X X) = genSig P X X`,
3. `genV P X X = conePlus P X * star (conePlus P X) + star (conePlus P X) * conePlus P X`
   (Gramian decomposition of the Fubini–Study / BKM metric seed),
4. `qgtPlus P X X * qgtMinus P X X = 0` and `qgtMinus P X X * qgtPlus P X X = 0`,
5. `genPhi P X X * star (genPhi P X X) = genV P X X` and `star (genPhi P X X) * genPhi P X X = genV P X X`. -/
theorem peirce_star_gramian_and_fubini_study_chordal_metric
    [StarRing B] {P X : B} (hP : P * P = P) (hP_star : star P = P) (hX_star : star X = X) :
    star (conePlus P X) = coneMinus P X ∧
    star (coneMinus P X) = conePlus P X ∧
    star (genPhi P X X) = genPhi P X X ∧
    star (genJ P X X) = -genJ P X X ∧
    star (genV P X X) = genV P X X ∧
    star (genSig P X X) = genSig P X X ∧
    genV P X X = conePlus P X * star (conePlus P X) + star (conePlus P X) * conePlus P X ∧
    qgtPlus P X X * qgtMinus P X X = 0 ∧
    qgtMinus P X X * qgtPlus P X X = 0 ∧
    genPhi P X X * star (genPhi P X X) = genV P X X ∧
    star (genPhi P X X) * genPhi P X X = genV P X X := by
  have h1mP : star (1 - P) = 1 - P := by rw [star_sub, star_one, hP_star]
  have hNp : star (conePlus P X) = coneMinus P X := by
    simp only [conePlus, coneMinus, star_mul, h1mP, hX_star, hP_star, mul_assoc]
  have hNm : star (coneMinus P X) = conePlus P X := by
    simp only [conePlus, coneMinus, star_mul, h1mP, hX_star, hP_star, mul_assoc]
  have hPhi : star (genPhi P X X) = genPhi P X X := by
    simp only [genPhi, star_add, hNp, hNm, add_comm]
  have hJ : star (genJ P X X) = -genJ P X X := by
    simp only [genJ, star_sub, hNp, hNm]; abel
  have hV : star (genV P X X) = genV P X X := by
    simp only [genV, anticomm, star_add, star_mul, hNp, hNm, add_comm]
  have hSig : star (genSig P X X) = genSig P X X := by
    simp only [genSig, comm, star_sub, star_mul, hNp, hNm]
  have hVgram : genV P X X = conePlus P X * star (conePlus P X) + star (conePlus P X) * conePlus P X := by
    simp only [genV, anticomm, hNp]
  have hPhiSq : genPhi P X X * genPhi P X X = genV P X X := by peirce_nf hP
  refine ⟨hNp, hNm, hPhi, hJ, hV, hSig, hVgram,
          by simp only [qgtPlus, qgtMinus]; peirce_nf hP,
          by simp only [qgtPlus, qgtMinus]; peirce_nf hP,
          by rw [hPhi, hPhiSq],
          by rw [hPhi, hPhiSq]⟩

/-- **Chunk 211 (`higher_rank_nilpotent_hierarchy_and_jordan_cancellation` of `1ofaG3fBD1VlprR7ShtsdctpOVRjmjB9f`, Archetype A₈₉)**:
1. **Power-vanishing consequences (`T⁴ = 0 → (T²)² = 0 ∧ (T³)² = 0`):**
   The hypothesis is fourth-power vanishing; it does not assert an operator rank.
2. **Cubic nilpotency consequences (`N_+³ = 0`):**
   `(N_+²)² = 0`, `comm N_+ (N_+²) = 0`, `N_+ * N_+² = 0`, and `N_+² * N_+ = 0`.
3. **Jordan Chain Commutator Sandwich Cancellation (`T² = 0`):**
   `T * T = 0` and `T * comm T X * T = 0` for all `X : B`. -/
theorem higher_rank_nilpotent_hierarchy_and_jordan_cancellation
    (T N_plus T_nil X : B)
    (hT4 : T ^ 4 = 0) (hN3 : N_plus ^ 3 = 0) (hT2 : T_nil ^ 2 = 0) :
    ((T ^ 2) ^ 2 = 0 ∧ (T ^ 3) ^ 2 = 0) ∧
    ((N_plus ^ 2) ^ 2 = 0 ∧
     comm N_plus (N_plus ^ 2) = 0 ∧
     N_plus * (N_plus ^ 2) = 0 ∧
     (N_plus ^ 2) * N_plus = 0) ∧
    (T_nil * T_nil = 0 ∧ T_nil * comm T_nil X * T_nil = 0) := by
  have hT2_sq : (T ^ 2) ^ 2 = 0 := by
    calc (T ^ 2) ^ 2 = T ^ (2 * 2) := by rw [← pow_mul]
      _ = T ^ 4 := rfl
      _ = 0 := hT4
  have hT3_sq : (T ^ 3) ^ 2 = 0 := by
    calc (T ^ 3) ^ 2 = T ^ (3 * 2) := by rw [← pow_mul]
      _ = T ^ (4 + 2) := rfl
      _ = T ^ 4 * T ^ 2 := by rw [pow_add]
      _ = 0 := by rw [hT4, zero_mul]
  have hN_sq_sq : (N_plus ^ 2) ^ 2 = 0 := by
    calc (N_plus ^ 2) ^ 2 = N_plus ^ (2 * 2) := by rw [← pow_mul]
      _ = N_plus ^ (3 + 1) := rfl
      _ = N_plus ^ 3 * N_plus ^ 1 := by rw [pow_add]
      _ = 0 := by rw [hN3, zero_mul]
  have hN_right : N_plus * (N_plus ^ 2) = 0 := by
    calc N_plus * (N_plus ^ 2) = N_plus ^ 1 * N_plus ^ 2 := by rw [pow_one]
      _ = N_plus ^ (1 + 2) := by rw [← pow_add]
      _ = N_plus ^ 3 := rfl
      _ = 0 := hN3
  have hN_left : (N_plus ^ 2) * N_plus = 0 := by
    calc (N_plus ^ 2) * N_plus = N_plus ^ 2 * N_plus ^ 1 := by rw [pow_one]
      _ = N_plus ^ (2 + 1) := by rw [← pow_add]
      _ = N_plus ^ 3 := rfl
      _ = 0 := hN3
  have hN_comm : comm N_plus (N_plus ^ 2) = 0 := by
    dsimp [comm]; rw [hN_right, hN_left, sub_self]
  have hTnil_mul : T_nil * T_nil = 0 := by
    simpa [sq] using hT2
  have hTnil_sand : T_nil * comm T_nil X * T_nil = 0 := by
    dsimp [comm]
    calc T_nil * (T_nil * X - X * T_nil) * T_nil
      _ = (T_nil * T_nil) * X * T_nil - T_nil * X * (T_nil * T_nil) := by noncomm_ring
      _ = 0 := by rw [hTnil_mul]; noncomm_ring
  exact ⟨⟨hT2_sq, hT3_sq⟩, ⟨hN_sq_sq, hN_comm, hN_right, hN_left⟩, ⟨hTnil_mul, hTnil_sand⟩⟩

/-- Grade `+1` generator in the `4 × 4` contact Kantor–Koecher–Tits 5-graded algebra
(`Chunk 204` of `1ofaG3fBD1VlprR7ShtsdctpOVRjmjB9f`). -/
def kktGradePlus1 {K : Type*} [CommRing K] (A B : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, A, B, 0;
     0, 0, 0, B;
     0, 0, 0, -A;
     0, 0, 0, 0]

/-- Grade `+2` generator in the `4 × 4` contact Kantor–Koecher–Tits 5-graded algebra
(`Chunk 204` of `1ofaG3fBD1VlprR7ShtsdctpOVRjmjB9f`). -/
def kktGradePlus2 {K : Type*} [CommRing K] (Z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, Z;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- First elementary `4 × 4` matrix witness `E_{01}` over `K`. -/
def kktWitnessA {K : Type*} [CommRing K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Second elementary `4 × 4` matrix witness `E_{12}` over `K`. -/
def kktWitnessB {K : Type*} [CommRing K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Non-commutativity witness for `Matrix (Fin 4) (Fin 4) K` over any nontrivial commutative ring `K`:
`kktWitnessA * kktWitnessB ≠ kktWitnessB * kktWitnessA`. -/
theorem kktWitnessA_kktWitnessB_noncomm {K : Type*} [CommRing K] [Nontrivial K] :
    (kktWitnessA : Matrix (Fin 4) (Fin 4) K) * (kktWitnessB : Matrix (Fin 4) (Fin 4) K) ≠
      (kktWitnessB : Matrix (Fin 4) (Fin 4) K) * (kktWitnessA : Matrix (Fin 4) (Fin 4) K) := by
  intro h
  have h02 := congrArg (fun M => M 0 2) h
  simp [kktWitnessA, kktWitnessB, Matrix.mul_apply, Fin.sum_univ_four] at h02

/-- Non-commutativity witness for `kktGradePlus1` in `Matrix (Fin 4) (Fin 4) ℤ`:
`kktGradePlus1 1 0 * kktGradePlus1 0 1 ≠ kktGradePlus1 0 1 * kktGradePlus1 1 0`. -/
theorem kktGradePlus1_noncomm :
    kktGradePlus1 (1 : ℤ) 0 * kktGradePlus1 (0 : ℤ) 1 ≠
      kktGradePlus1 (0 : ℤ) 1 * kktGradePlus1 (1 : ℤ) 0 := by
  intro h
  have h03 := congrArg (fun M => M 0 3) h
  revert h03; decide

/-- For the explicitly defined `4 × 4` matrices over a commutative ring, these two
commutator identities hold: the selected `kktGradePlus1` products have the stated
`kktGradePlus2` difference, and `kktGradePlus1` commutes with `kktGradePlus2`.
This theorem proves these matrix identities only; it does not establish a graded
Lie algebra structure or a general contact/KKT construction. The historical
source archetype is Chunk 204 of `1ofaG3fBD1VlprR7ShtsdctpOVRjmjB9f`. -/
theorem kkt_bracket_p1_p1_eq_p2_and_p1_p2_zero {K : Type*} [CommRing K] (A B A' B' Z : K) :
    (kktGradePlus1 A B * kktGradePlus1 A' B' - kktGradePlus1 A' B' * kktGradePlus1 A B =
       kktGradePlus2 (2 * (A * B' - B * A'))) ∧
    (kktGradePlus1 A B * kktGradePlus2 Z - kktGradePlus2 Z * kktGradePlus1 A B = 0) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> (simp [kktGradePlus1, kktGradePlus2]; try ring)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [kktGradePlus1, kktGradePlus2]

/-! ## 15. Chunks 121–125 & 156: explicit matrix identities over a ring, an ordered bilinear expansion, and nilpotent commutator identities -/

/-- The diagonal matrix `diag(1, -1)` over a ring; its square is the identity. -/
def kreinSigmaZ {K : Type*} [Ring K] : Matrix (Fin 2) (Fin 2) K :=
  !![1, 0;
     0, -1]

/-- The matrix `[[0, -1], [1, 0]]` over a ring; its square is minus the identity. -/
def kreinJ2 {K : Type*} [Ring K] : Matrix (Fin 2) (Fin 2) K :=
  !![0, -1;
     1, 0]

/-- The explicitly defined matrix `[[s, a], [-a, s]]` over a ring. -/
def realDoubleKrein {K : Type*} [Ring K] (s a : K) : Matrix (Fin 2) (Fin 2) K :=
  !![s, a;
     -a, s]

/-- A `4 × 4` block matrix with two copies of the displayed `2 × 2` matrix. -/
def kreinJ4 {K : Type*} [Ring K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, -1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, -1;
     0, 0, 1, 0]

/-- The `4 × 4` diagonal matrix `diag(1, 1, -1, -1)`. -/
def kreinGamma5 {K : Type*} [Ring K] : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- Non-commutativity witness for `kreinSigmaZ` and `kreinJ2` over `ℤ`:
`kreinSigmaZ * kreinJ2 ≠ kreinJ2 * kreinSigmaZ`. -/
theorem kreinSigmaZ_kreinJ2_noncomm :
    (kreinSigmaZ : Matrix (Fin 2) (Fin 2) ℤ) * kreinJ2 ≠
      kreinJ2 * (kreinSigmaZ : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro h
  have h01 := congrArg (fun M => M 0 1) h
  revert h01; decide

/-- **Chunks 121–125 (`real_doubled_krein_clifford_and_rope_symplectic_attention_split` of `1xSSy_Z8fOSORG_mJGQISEOkQzV5lsP_1`)**:
The matrix identities below hold over every ring, with no real structure or bilinear form assumed.
1. **Two matrix square identities and an anticommutation identity:**
   `kreinSigmaZ * kreinSigmaZ = 1`, `kreinJ2 * kreinJ2 = -1`, and
   `kreinSigmaZ * kreinJ2 + kreinJ2 * kreinSigmaZ = 0`.
2. **Product and conjugation identities for the defined block matrices:**
   - `realDoubleKrein s₁ a₁ * realDoubleKrein s₂ a₂ = realDoubleKrein (s₁ * s₂ - a₁ * a₂) (s₁ * a₂ + a₁ * s₂)`,
   - `kreinSigmaZ * realDoubleKrein s a * kreinSigmaZ = realDoubleKrein s (-a)`.
3. **Two `4 × 4` matrix identities:**
   `kreinJ4 * kreinJ4 = -1`, `kreinGamma5 * kreinGamma5 = 1`, and
   `kreinGamma5 * kreinJ4 - kreinJ4 * kreinGamma5 = 0`.
4. **Ordered bilinear expansion (historically labeled Chunk 123):**
   The final clause is a distributive identity in an arbitrary ring. The symbols
   `c_m`, `s_m`, `c_n`, and `s_n` are unconstrained coefficients; this proposition
   does not assert trigonometric, rotation, or attention semantics. -/
theorem real_doubled_krein_clifford_and_rope_symplectic_attention_split
    {K : Type*} [Ring K] (s₁ a₁ s₂ a₂ q₁ q₂ k₁ k₂ c_m s_m c_n s_n : K) :
    (kreinSigmaZ : Matrix (Fin 2) (Fin 2) K) * kreinSigmaZ = 1 ∧
    (kreinJ2 : Matrix (Fin 2) (Fin 2) K) * kreinJ2 = -1 ∧
    (kreinSigmaZ : Matrix (Fin 2) (Fin 2) K) * kreinJ2 +
      kreinJ2 * (kreinSigmaZ : Matrix (Fin 2) (Fin 2) K) = 0 ∧
    realDoubleKrein s₁ a₁ * realDoubleKrein s₂ a₂ =
      realDoubleKrein (s₁ * s₂ - a₁ * a₂) (s₁ * a₂ + a₁ * s₂) ∧
    kreinSigmaZ * realDoubleKrein s₁ a₁ * kreinSigmaZ = realDoubleKrein s₁ (-a₁) ∧
    (kreinJ4 : Matrix (Fin 4) (Fin 4) K) * kreinJ4 = -1 ∧
    (kreinGamma5 : Matrix (Fin 4) (Fin 4) K) * kreinGamma5 = 1 ∧
    (kreinGamma5 : Matrix (Fin 4) (Fin 4) K) * kreinJ4 -
      kreinJ4 * (kreinGamma5 : Matrix (Fin 4) (Fin 4) K) = 0 ∧
    ((q₁ * c_m - q₂ * s_m) * (k₁ * c_n - k₂ * s_n) +
     (q₁ * s_m + q₂ * c_m) * (k₁ * s_n + k₂ * c_n) =
       (q₁ * c_m * k₁ * c_n - q₁ * c_m * k₂ * s_n -
        q₂ * s_m * k₁ * c_n + q₂ * s_m * k₂ * s_n +
        q₁ * s_m * k₁ * s_n + q₁ * s_m * k₂ * c_n +
        q₂ * c_m * k₁ * s_n + q₂ * c_m * k₂ * c_n)) := by
  have h_rope :
      (q₁ * c_m - q₂ * s_m) * (k₁ * c_n - k₂ * s_n) +
        (q₁ * s_m + q₂ * c_m) * (k₁ * s_n + k₂ * c_n) =
        (q₁ * c_m * k₁ * c_n - q₁ * c_m * k₂ * s_n -
         q₂ * s_m * k₁ * c_n + q₂ * s_m * k₂ * s_n +
         q₁ * s_m * k₁ * s_n + q₁ * s_m * k₂ * c_n +
         q₂ * c_m * k₁ * s_n + q₂ * c_m * k₂ * c_n) := by noncomm_ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_rope⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [kreinSigmaZ]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [kreinJ2]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [kreinSigmaZ, kreinJ2]
  · ext i j; fin_cases i <;> fin_cases j <;> (simp [realDoubleKrein]; try noncomm_ring)
  · ext i j; fin_cases i <;> fin_cases j <;> simp [kreinSigmaZ, realDoubleKrein]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [kreinJ4]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [kreinGamma5]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [kreinGamma5, kreinJ4]

/-- Sandwich product `N_+ W N_+` for a square-zero element `N_+` (source Chunk 156). -/
def nilKantorGp2 (Np W : B) : B :=
  Np * W * Np

/-- Sandwich product `N_- W N_-` for a square-zero element `N_-` (source Chunk 156). -/
def nilKantorGm2 (Nm W : B) : B :=
  Nm * W * Nm

/-- **Chunk 156 (`nilpotent_first_cartan_dirac_and_kantor_5graded_closure` of `1xSSy_Z8fOSORG_mJGQISEOkQzV5lsP_1`)**:
For ANY pair of square-zero nilpotent operators `Np, Nm : B` (`hp : Np * Np = 0`, `hm : Nm * Nm = 0`)
in any non-commutative ring `B` (without requiring a prior idempotent `P` or von Neumann regularity):
1. **Dirac–Kähler Split-Quaternionic Genesis from Pure Nilpotents (`Φ = N_+ + N_-`, `J = N_+ - N_-`):**
   - `(Np + Nm) * (Np + Nm) = anticomm Np Nm` (`Φ² = V`),
   - `(Np - Nm) * (Np - Nm) = -anticomm Np Nm` (`J² = -V`),
   - `anticomm (Np + Nm) (Np - Nm) = 0` (`{Φ, J} = 0`),
   - `comm (Np + Nm) (Np - Nm) = -((2 : ℤ) • comm Np Nm)` (`[Φ, J] = -2 Σ`).
2. **Jordan Associator Anomaly on Pure Nilpotents:**
   - `JordanAssoc Nm Np Np = comm (comm Np Nm) Np`,
   - `JordanAssoc Np Nm Nm = -comm (comm Np Nm) Nm`.
3. **Commutator identities for the sandwich products:**
   - `comm (comm Np W) Np = (2 : ℤ) • nilKantorGp2 Np W`,
   - `comm (comm Nm W) Nm = (2 : ℤ) • nilKantorGm2 Nm W`,
   - `comm (nilKantorGp2 Np W) Np = 0`,
   - `comm (nilKantorGm2 Nm W) Nm = 0`.
These identities alone do not define a 5-grading or a Kantor–Koecher–Tits algebra. -/
theorem nilpotent_first_cartan_dirac_and_kantor_5graded_closure
    {Np Nm : B} (hp : Np * Np = 0) (hm : Nm * Nm = 0) (W : B) :
    (Np + Nm) * (Np + Nm) = anticomm Np Nm ∧
    (Np - Nm) * (Np - Nm) = -anticomm Np Nm ∧
    anticomm (Np + Nm) (Np - Nm) = 0 ∧
    comm (Np + Nm) (Np - Nm) = -((2 : ℤ) • comm Np Nm) ∧
    JordanAssoc Nm Np Np = comm (comm Np Nm) Np ∧
    JordanAssoc Np Nm Nm = -comm (comm Np Nm) Nm ∧
    comm (comm Np W) Np = (2 : ℤ) • nilKantorGp2 Np W ∧
    comm (comm Nm W) Nm = (2 : ℤ) • nilKantorGm2 Nm W ∧
    comm (nilKantorGp2 Np W) Np = 0 ∧
    comm (nilKantorGm2 Nm W) Nm = 0 := by
  have hp_left : ∀ X : B, Np * (Np * X) = 0 := fun X => by rw [← mul_assoc, hp, zero_mul]
  have hm_left : ∀ X : B, Nm * (Nm * X) = 0 := fun X => by rw [← mul_assoc, hm, zero_mul]
  refine ⟨?_, ?_, ?_, ?_,
          by simp only [JordanAssoc, anticomm, comm]; noncomm_ring,
          by simp only [JordanAssoc, anticomm, comm]; noncomm_ring,
          ?_, ?_, ?_, ?_⟩
  · dsimp [anticomm]
    simp only [add_mul, mul_add, hp, hm]; abel
  · dsimp [anticomm]
    simp only [sub_mul, mul_sub, hp, hm]; noncomm_ring
  · dsimp [anticomm]
    simp only [add_mul, sub_mul, mul_add, mul_sub, hp, hm]; noncomm_ring
  · dsimp [comm]
    simp only [add_mul, sub_mul, mul_add, mul_sub, hp, hm]; noncomm_ring
  · dsimp [comm, nilKantorGp2]
    have hkill := hp_left W
    simp only [sub_mul, mul_sub, mul_assoc, hp, mul_zero, sub_zero]
    rw [hkill]
    abel
  · dsimp [comm, nilKantorGm2]
    have hkill := hm_left W
    simp only [sub_mul, mul_sub, mul_assoc, hm, mul_zero, sub_zero]
    rw [hkill]
    abel
  · dsimp [comm, nilKantorGp2]
    have hright : (Np * W * Np) * Np = 0 := by
      rw [mul_assoc (Np * W) Np Np, hp, mul_zero]
    have hleft : Np * (Np * W * Np) = 0 := by
      simpa only [mul_assoc] using hp_left (W * Np)
    rw [hright, hleft, sub_self]
  · dsimp [comm, nilKantorGm2]
    have hright : (Nm * W * Nm) * Nm = 0 := by
      rw [mul_assoc (Nm * W) Nm Nm, hm, mul_zero]
    have hleft : Nm * (Nm * W * Nm) = 0 := by
      simpa only [mul_assoc] using hm_left (W * Nm)
    rw [hright, hleft, sub_self]

/-- Algebraic commutant closure, Peirce commutation, and nilpotent-conjugation identities
(historically sourced from an archetype labeled “Erlangen 2.0”). The hypotheses and
conclusion below are ring equations. They do not provide a von Neumann algebra, a state,
a modular operator or flow, a Cartan/Casimir subalgebra, or an exponential map.
1. **Peirce commutation consequences (`hP : P * P = P`):**
   The displayed elements `genV P A C` and `invS P`, `conePlus P A`, `coneMinus P C`,
   `genPhi P A C`, `genJ P A C`, and `genSig P A C` satisfy the listed commutator
   identities under the idempotence hypothesis on `P`.
2. **Commutant closure and derivation identity (`[K, Q₁] = 0`, `[K, Q₂] = 0`):**
   - **Subring Closure**: `[K, Q₁ * Q₂] = 0`,
   - Commutator closure: `[K, [Q₁, Q₂]] = 0`,
   - Anticommutator closure: `[K, {Q₁, Q₂}] = 0`,
   - The displayed nested-commutator identity follows from the assumed commutation relations.
3. **Conjugation identities:**
   - `invS P` conjugates the displayed Peirce expressions `genV` and `genSig` to themselves.
   - For `N² = 0`, the following unipotent conjugation identities hold; no exponential is defined here:
     `(1 + N)(1 - N) = 1`, `(1 + N) X (1 - N) = X + [N, X] - N X N`, and every Noether charge `Q`
     commuting with `N` (`[N, Q] = 0`) is preserved by this conjugation:
     `(1 + N) Q (1 - N) = Q`. -/
theorem erlangen2_von_neumann_tomita_takesaki_modular_centralizer_and_noether_killing_invariants
    {P K Q₁ Q₂ N Q : B} (hP : P * P = P)
    (hQ1 : comm K Q₁ = 0) (hQ2 : comm K Q₂ = 0)
    (hN : N * N = 0) (hQN : comm N Q = 0) (A C X : B) :
    -- 1. Central Action of Cartan & Casimir Observables on Peirce Operator Modules:
    comm (invS P) (genV P A C) = 0 ∧
    comm (genV P A C) (conePlus P A) = 0 ∧
    comm (genV P A C) (coneMinus P C) = 0 ∧
    comm (genV P A C) (genPhi P A C) = 0 ∧
    comm (genV P A C) (genJ P A C) = 0 ∧
    comm (genV P A C) (genSig P A C) = 0 ∧
    -- 2. Closure identities for elements commuting with K:
    comm K (Q₁ * Q₂) = 0 ∧
    comm K (comm Q₁ Q₂) = 0 ∧
    comm K (anticomm Q₁ Q₂) = 0 ∧
    comm K (comm Q₁ X) - comm Q₁ (comm K X) = 0 ∧
    -- 3. Peirce and nilpotent-conjugation identities:
    invS P * genV P A C * invS P = genV P A C ∧
    invS P * genSig P A C * invS P = genSig P A C ∧
    (1 + N) * (1 - N) = 1 ∧
    (1 + N) * X * (1 - N) = X + comm N X - N * X * N ∧
    (1 + N) * Q * (1 - N) = Q := by
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          ?_, ?_, ?_, ?_,
          by peirce_nf hP, by peirce_nf hP,
          ?_, by simp only [comm]; noncomm_ring, ?_⟩
  · calc comm K (Q₁ * Q₂)
      _ = comm K Q₁ * Q₂ + Q₁ * comm K Q₂ := by simp only [comm]; noncomm_ring
      _ = 0 := by rw [hQ1, hQ2]; noncomm_ring
  · calc comm K (comm Q₁ Q₂)
      _ = comm (comm K Q₁) Q₂ + comm Q₁ (comm K Q₂) := by simp only [comm]; noncomm_ring
      _ = 0 := by rw [hQ1, hQ2]; simp only [comm]; noncomm_ring
  · calc comm K (anticomm Q₁ Q₂)
      _ = anticomm (comm K Q₁) Q₂ + anticomm Q₁ (comm K Q₂) := by simp only [comm, anticomm]; noncomm_ring
      _ = 0 := by rw [hQ1, hQ2]; simp only [anticomm]; noncomm_ring
  · calc comm K (comm Q₁ X) - comm Q₁ (comm K X)
      _ = comm (comm K Q₁) X := by simp only [comm]; noncomm_ring
      _ = 0 := by rw [hQ1]; simp only [comm]; noncomm_ring
  · calc (1 + N) * (1 - N)
      _ = 1 - N * N := by noncomm_ring
      _ = 1 := by rw [hN, sub_zero]
  · calc (1 + N) * Q * (1 - N)
      _ = Q * (1 - N * N) + comm N Q * (1 - N) := by simp only [comm]; noncomm_ring
      _ = Q := by rw [hN, hQN]; noncomm_ring

end InfoGeometry.OperatorAlgebra.PeirceSpine
