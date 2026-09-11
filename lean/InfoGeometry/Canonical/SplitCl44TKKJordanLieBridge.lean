import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauConformalKKTContext
import InfoGeometry.Canonical.NoetherInference
import InfoGeometry.Quantum.SplitTrialityKernel

/-!
# Split `Cl(4,4)` / TKK / Jordan-Lie Bridge

This module records the repo-native part of the `Cl(4,4)` prose corridor.

It deliberately does not assert the missing classification theorems:

* no global `Cl(4,4) ≃ Matrix (Fin 16) (Fin 16) ℝ` theorem,
* no full `Spin(4,4)` triality theorem,
* no split-octonion algebra theorem.

Instead it links the formal surfaces already owned by the repository:

* the recursive split `Cl(4,4)` head factor,
* the real doubled triality kernel proxy,
* operatorial Weyl/TKK/KKT closure,
* symmetric Jordan and antisymmetric Lie products,
* Fisher/Killing base-relation transport under explicit hypotheses.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge

open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Canonical.SouriauConformalKKT
open InfoGeometry.Canonical.NoetherInference
open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Krein
open InfoGeometry.Quantum

variable {α : Type _}
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace H
local notation "EndH₂" => H₂ →L[ℝ] H₂
local notation "cl11" => doubledSpaceCl11Action (E := H)

/-! ## Recursive split `Cl(4,4)` stage -/

/--
The repository-owned `Cl(4,4)` fact: the fourth split Clifford stage factors
as one `Cl(1,1)` head channel tensored with the `Cl(3,3)` tail.
-/
@[rep_depth krein]
theorem splitCl44_recursive_head_factor
    (x : ℝ × ℝ) :
    splitCl44_headFactorEquiv
        (CliffordAlgebra.ι SplitCl44Quad
          (InfoGeometry.Clifford.ClNN.headPair 3 x))
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 x)
          ᵍ⊗ₜ (1 : CliffordAlgebra (InfoGeometry.CliffordTower.Qsplit 3)) := by
  simpa using splitCl44_headFactor x

/--
The tail channel of the recursive `Cl(4,4)` presentation is the split
`Cl(3,3)` remainder.
-/
@[rep_depth krein]
theorem splitCl44_recursive_tail_factor
    (xs : SplitClNNCarrier 3) :
    splitCl44_headFactorEquiv
        (CliffordAlgebra.ι SplitCl44Quad (InfoGeometry.Clifford.ClNN.tailLift 3 xs))
      = (1 : CliffordAlgebra InfoGeometry.CliffordTower.Q11)
          ᵍ⊗ₜ (CliffordAlgebra.ι (InfoGeometry.CliffordTower.Qsplit 3) xs) := by
  simpa using splitCl44_tailFactor xs

/-! ## Triality-shaped kernel proxy -/

/--
The formal triality kernel owned by the repo has an involutive Dirac-square
seed.  This is the proved proxy, not the full `Spin(4,4)` triality theorem.
-/
@[rep_depth krein]
theorem splitTriality_informationalDiracSquare_eq_id
    (T : SplitTrialityKernel) :
    T.informationalDiracSquare = LinearMap.id :=
  T.informationalDiracSquare_eq_id

/--
The triality supercharge squares to identity in the real doubled kernel.
-/
@[rep_depth krein]
theorem splitTriality_supercharge_sq_eq_id
    (T : SplitTrialityKernel) :
    T.trialitySupercharge.comp T.trialitySupercharge = LinearMap.id :=
  T.trialitySupercharge_sq_eq_id

/--
The Hestenes phase axis anticommutes with the triality supercharge in the
split-octonionic proxy lane.
-/
@[rep_depth krein]
theorem splitTriality_phaseAxis_anticommutes
    (T : SplitTrialityKernel) :
    T.trialitySupercharge.comp (T.polarization.Pplus - T.polarization.Pminus)
      =
    -((T.polarization.Pplus - T.polarization.Pminus).comp T.trialitySupercharge) :=
  T.k_acts_as_imaginary

/-! ## Operatorial TKK/KKT/Jordan-Lie packet -/

/--
Proof-carrying packet connecting the recursive split `Cl(4,4)` stage to the
operatorial Weyl/TKK/KKT/Jordan-Lie closure surface.
-/
@[rep_depth transport]
structure SplitCl44TKKJordanLiePacket where
  closure : ConformalWeylTKKKKTJordanLieContext (α := α) (H := H)
  triality : SplitTrialityKernel

namespace SplitCl44TKKJordanLiePacket

variable (P : SplitCl44TKKJordanLiePacket (α := α) (H := H))

/-- The packet carries the explicit operatorial TKK master relation. -/
@[rep_depth transport]
theorem tkkMasterRelation :
    P.closure.gibbs.SatisfiesOperatorTKKMasterRelation P.closure.tkkParameter :=
  P.closure.tkkMasterRelation

/-- The packet carries the explicit operatorial admissibility/KKT gate. -/
@[rep_depth transport]
theorem operatorAdmissible :
    P.closure.gibbs.IsOperatorAdmissible :=
  P.closure.operatorAdmissible

/-- The conformal dilation lies in the KKT grade-zero lane. -/
@[rep_depth transport]
theorem dilation_isGZero :
    IsGZero cl11 P.closure.gibbs.DGenerator :=
  P.closure.dilation_isGZero

/-- Circular polarization closes in grade zero: `[u₊ X, u₋ Y] ∈ 𝔤₀`. -/
@[rep_depth transport]
theorem circularPolarizedCommutator_isGZero :
    IsGZero cl11 P.closure.circularPolarizedCommutator :=
  P.closure.circularPolarizedCommutator_isGZero

/-- The full operatorial KKT/TKK/Weyl/Jordan-Lie closure proposition. -/
@[rep_depth transport]
theorem satisfiesKKT_TKK_Weyl_JordanLieClosure :
    P.closure.SatisfiesKKT_TKK_Weyl_JordanLieClosure :=
  P.closure.satisfiesKKT_TKK_Weyl_JordanLieClosure

/-- The commutator channel is exactly twice the antisymmetric Lie product. -/
@[rep_depth transport]
theorem fockCommutator_temperature_weyl_eq_two_smul_lieProduct :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator (E := H)
      P.closure.gibbs.conformalGeometricTemperature P.closure.weylTemperature =
        (2 : ℝ) • P.closure.lieProductTemperatureWeyl :=
  P.closure.fockCommutator_temperature_weyl_eq_two_smul_lieProduct

/-- The anticommutator channel is exactly twice the symmetric Jordan product. -/
@[rep_depth transport]
theorem fockAnticommutator_temperature_weyl_eq_two_smul_jordanProduct :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator (E := H)
      P.closure.gibbs.conformalGeometricTemperature P.closure.weylTemperature =
        (2 : ℝ) • P.closure.jordanProductTemperatureWeyl :=
  P.closure.fockAnticommutator_temperature_weyl_eq_two_smul_jordanProduct

/-- The packet's triality proxy carries an involutive Dirac-square seed. -/
@[rep_depth krein]
theorem triality_informationalDiracSquare_eq_id :
    P.triality.informationalDiracSquare = LinearMap.id :=
  P.triality.informationalDiracSquare_eq_id

/--
Consolidated constructive packet for the repo-owned `Cl(4,4)` / TKK /
Jordan-Lie corridor.

This is intentionally the reduced theorem surface:

* recursive split `Cl(4,4)` head/tail factorization;
* real doubled triality-kernel proxy identities;
* operatorial TKK/KKT/Weyl closure;
* symmetric Jordan and antisymmetric Lie channel readouts.

It does not assert the unavailable global `Cl(4,4) ≃ M₁₆(ℝ)`, full
`Spin(4,4)` triality, split-octonion, `F₄`, or `E₈` classification theorem.
-/
@[rep_depth transport]
theorem splitCl44_TKK_JordanLie_constructive_packet
    (x : ℝ × ℝ) (xs : SplitClNNCarrier 3) :
    splitCl44_headFactorEquiv
        (CliffordAlgebra.ι SplitCl44Quad
          (InfoGeometry.Clifford.ClNN.headPair 3 x))
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 x)
          ᵍ⊗ₜ (1 : CliffordAlgebra (InfoGeometry.CliffordTower.Qsplit 3))
      ∧ splitCl44_headFactorEquiv
        (CliffordAlgebra.ι SplitCl44Quad (InfoGeometry.Clifford.ClNN.tailLift 3 xs))
      = (1 : CliffordAlgebra InfoGeometry.CliffordTower.Q11)
          ᵍ⊗ₜ (CliffordAlgebra.ι (InfoGeometry.CliffordTower.Qsplit 3) xs)
      ∧ P.triality.informationalDiracSquare = LinearMap.id
      ∧ P.triality.trialitySupercharge.comp P.triality.trialitySupercharge =
        LinearMap.id
      ∧ P.triality.trialitySupercharge.comp
          (P.triality.polarization.Pplus - P.triality.polarization.Pminus)
        =
        -((P.triality.polarization.Pplus - P.triality.polarization.Pminus).comp
          P.triality.trialitySupercharge)
      ∧ P.closure.gibbs.SatisfiesOperatorTKKMasterRelation P.closure.tkkParameter
      ∧ P.closure.gibbs.IsOperatorAdmissible
      ∧ IsGZero cl11 P.closure.gibbs.DGenerator
      ∧ IsGZero cl11 P.closure.circularPolarizedCommutator
      ∧ P.closure.SatisfiesKKT_TKK_Weyl_JordanLieClosure
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator (E := H)
          P.closure.gibbs.conformalGeometricTemperature P.closure.weylTemperature =
        (2 : ℝ) • P.closure.lieProductTemperatureWeyl
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator (E := H)
          P.closure.gibbs.conformalGeometricTemperature P.closure.weylTemperature =
        (2 : ℝ) • P.closure.jordanProductTemperatureWeyl := by
  exact
    ⟨splitCl44_recursive_head_factor (x := x),
      splitCl44_recursive_tail_factor (xs := xs),
      P.triality_informationalDiracSquare_eq_id,
      P.triality.trialitySupercharge_sq_eq_id,
      P.triality.k_acts_as_imaginary,
      P.tkkMasterRelation,
      P.operatorAdmissible,
      P.dilation_isGZero,
      P.circularPolarizedCommutator_isGZero,
      P.satisfiesKKT_TKK_Weyl_JordanLieClosure,
      P.fockCommutator_temperature_weyl_eq_two_smul_lieProduct,
      P.fockAnticommutator_temperature_weyl_eq_two_smul_jordanProduct⟩

end SplitCl44TKKJordanLiePacket

/-! ## Fisher/Killing bridge with explicit base relation -/

section FisherKilling

variable [FiniteDimensional ℝ H]
variable [Invertible (2 : ℝ)]
variable [Module.Free ℝ (Op H)] [Module.Finite ℝ (Op H)]

/--
Fisher/Killing compatibility is transported from an explicit base relation
along any Hessian-preserving orbit equivalence.

This is the legitimate theorem presently owned by the repo: proportionality is
not inferred from `Cl(4,4)` or triality; it is transported after being supplied
as a base hypothesis.
-/
@[rep_depth transport]
theorem fisherKilling_baseRelation_transports
    (S : InfoGeometry.Core.Generic.SymmetricLieAlgebra ℝ (Op H))
    (U : DSpace H ≃L[ℝ] DSpace H)
    (hU :
      ∀ x y : DSpace H,
        hessian_indefinite_form (E := H) (U x) (U y)
          = hessian_indefinite_form (E := H) x y)
    (v0 : DSpace H)
    (c : ℝ)
    (hBase :
      ∀ (X Y : Op H),
        fisherBilinAt (E := H) v0 X Y =
          c * S.B (S.P_minus X) (S.P_minus Y)) :
    ∀ (X Y : Op H),
      fisherBilinAt (E := H) (U v0)
        (InfoGeometry.Krein.conjugateCLM U X)
        (InfoGeometry.Krein.conjugateCLM U Y)
        =
      c * S.B (S.P_minus X) (S.P_minus Y) :=
  fisher_metric_eq_killing_form_of_orbit_base_relation
    (E := H) S U hU v0 c hBase

end FisherKilling

end InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge
