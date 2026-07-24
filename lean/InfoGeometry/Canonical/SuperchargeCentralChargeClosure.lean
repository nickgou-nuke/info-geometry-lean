import InfoGeometry.Canonical.OperatorialCentralCharge
import InfoGeometry.Canonical.CentralChargeKKTParityBridge
import InfoGeometry.Canonical.SuperchargeGapHessianBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SuperchargeCentralChargeClosure

Closure package for the currently-owned operatorial supercharge lane.

This file does not postulate a new “gap = charge” ontology. It only places the
existing owners on one transport slice:

- `SuperchargeGapHessianBridge` supplies the CPT-supercharge CCR anchor, the
  first odd-odd gap seed landing, and the second Hessian/curvature landing;
- `OperatorialCentralCharge` supplies the KK/Fredholm analytical-index owner
  and its transport-protected nonvanishing law.

The result is a single closure theorem surface for downstream DIII/topological
transport files.
-/

namespace InfoGeometry.Canonical.SuperchargeCentralChargeClosure

open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.SuperchargeGapHessianBridge
open InfoGeometry.Canonical.SuperchargeGapBridge
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.CentralChargeKKTParityBridge
open InfoGeometry.Canonical.ChiralDefectIndexBridge
open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Canonical.SuperchargeTransportBridge
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Krein

section RecursiveAlgebra

/--
The square of a recursively extended odd supercharge.

For `Qnext = Q + R`, the new square is the old square plus the
odd--odd cross bracket plus the new square.
-/
@[rep_depth transport]
theorem recursive_supercharge_square
    {A : Type*} [Ring A]
    (Q R : A) :
    (Q + R) * (Q + R) =
      Q * Q + (Q * R + R * Q) + R * R := by
  noncomm_ring

/--
If both odd layers are nilpotent, the square of the recursive supercharge is
exactly the odd--odd anticommutator.
-/
@[rep_depth transport]
theorem recursive_nilpotent_supercharge_square_eq_anticommutator
    {A : Type*} [Ring A]
    {Q R : A}
    (hQ : Q * Q = 0)
    (hR : R * R = 0) :
    (Q + R) * (Q + R) = Q * R + R * Q := by
  calc
    (Q + R) * (Q + R)
        = Q * Q + (Q * R + R * Q) + R * R := by
          exact recursive_supercharge_square Q R
    _ = 0 + (Q * R + R * Q) + 0 := by
          rw [hQ, hR]
    _ = Q * R + R * Q := by
          simp

/--
Central-charge extraction from two nilpotent recursive supercharges.

If the odd--odd cross bracket is `Z`, then the square of the extended
supercharge is exactly `Z`.
-/
@[rep_depth transport]
theorem recursive_nilpotent_supercharge_square_eq_centralCharge
    {A : Type*} [Ring A]
    {Q R Z : A}
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hZ : Q * R + R * Q = Z) :
    (Q + R) * (Q + R) = Z := by
  rw [recursive_nilpotent_supercharge_square_eq_anticommutator hQ hR]
  exact hZ

/--
If the odd--odd cross bracket is a central element `Z`, then the recursive
supercharge square is central.
-/
@[rep_depth transport]
theorem recursive_supercharge_square_is_central
    {A : Type*} [Ring A]
    {Q R Z : A}
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hZ : Q * R + R * Q = Z)
    (hCentral : ∀ X : A, Z * X = X * Z) :
    ∀ X : A, ((Q + R) * (Q + R)) * X = X * ((Q + R) * (Q + R)) := by
  intro X
  rw [recursive_nilpotent_supercharge_square_eq_centralCharge hQ hR hZ]
  exact hCentral X

/--
Ring homomorphisms preserve the odd--odd anticommutator.

This is the finite functorial transport lemma for the central obstruction.
-/
@[rep_depth transport]
theorem ringHom_map_anticommutator
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    (Q R : A) :
    φ (Q * R + R * Q) =
      φ Q * φ R + φ R * φ Q := by
  simp

/--
A ring homomorphism transports the recursive central-charge equation.

If `{Q,R}=Z` in the source algebra, then `{φQ,φR}=φZ` in the target algebra.
-/
@[rep_depth transport]
theorem ringHom_preserves_centralCharge_bracket
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    {Q R Z : A}
    (hZ : Q * R + R * Q = Z) :
    φ Q * φ R + φ R * φ Q = φ Z := by
  rw [← ringHom_map_anticommutator φ Q R]
  rw [hZ]

/--
A ring homomorphism transports nilpotent recursive supercharge closure.

If `Q²=0`, `R²=0`, and `{Q,R}=Z`, then the transported extended supercharge
has square `φ Z`.
-/
@[rep_depth transport]
theorem ringHom_preserves_recursive_nilpotent_centralCharge_square
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    {Q R Z : A}
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hZ : Q * R + R * Q = Z) :
    (φ Q + φ R) * (φ Q + φ R) = φ Z := by
  have hφQ : φ Q * φ Q = 0 := by
    rw [← map_mul, hQ, map_zero]
  have hφR : φ R * φ R = 0 := by
    rw [← map_mul, hR, map_zero]
  have hφZ : φ Q * φ R + φ R * φ Q = φ Z :=
    ringHom_preserves_centralCharge_bracket φ hZ
  exact recursive_nilpotent_supercharge_square_eq_centralCharge hφQ hφR hφZ

/--
Centrality is preserved by a surjective ring homomorphism.

This is the finite quotient/transport form needed for bonding maps: if `Z` is
central in `A` and every target element is hit by `φ`, then `φ Z` is central in
`B`.
-/
@[rep_depth transport]
theorem ringHom_preserves_central_of_surjective
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    {Z : A}
    (hCentral : ∀ X : A, Z * X = X * Z)
    (hSurj : Function.Surjective φ) :
    ∀ Y : B, φ Z * Y = Y * φ Z := by
  intro Y
  rcases hSurj Y with ⟨X, rfl⟩
  calc
    φ Z * φ X = φ (Z * X) := by
      rw [map_mul]
    _ = φ (X * Z) := by
      rw [hCentral X]
    _ = φ X * φ Z := by
      rw [map_mul]

/--
Surjective transport of the whole recursive central-charge square: the
transported square equals `φ Z`, and `φ Z` is central.
-/
@[rep_depth transport]
theorem ringHom_preserves_recursive_central_square_and_centrality
    {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B)
    {Q R Z : A}
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hZ : Q * R + R * Q = Z)
    (hCentral : ∀ X : A, Z * X = X * Z)
    (hSurj : Function.Surjective φ) :
    ((φ Q + φ R) * (φ Q + φ R) = φ Z)
      ∧
    (∀ Y : B, φ Z * Y = Y * φ Z) := by
  exact
    ⟨ringHom_preserves_recursive_nilpotent_centralCharge_square φ hQ hR hZ,
      ringHom_preserves_central_of_surjective φ hCentral hSurj⟩

/--
Finite three-layer expansion.

All self-squares plus all odd--odd cross anticommutators appear explicitly.
-/
@[rep_depth transport]
theorem three_supercharge_square
    {A : Type*} [Ring A]
    (Q₁ Q₂ Q₃ : A) :
    (Q₁ + Q₂ + Q₃) * (Q₁ + Q₂ + Q₃) =
      Q₁ * Q₁ + Q₂ * Q₂ + Q₃ * Q₃
      + (Q₁ * Q₂ + Q₂ * Q₁)
      + (Q₁ * Q₃ + Q₃ * Q₁)
      + (Q₂ * Q₃ + Q₃ * Q₂) := by
  noncomm_ring

/--
If three recursive odd layers are nilpotent, the square of their sum is exactly
the sum of the three pairwise odd--odd anticommutators.
-/
@[rep_depth transport]
theorem three_nilpotent_supercharge_square_eq_pairwise_anticommutators
    {A : Type*} [Ring A]
    {Q₁ Q₂ Q₃ : A}
    (h₁ : Q₁ * Q₁ = 0)
    (h₂ : Q₂ * Q₂ = 0)
    (h₃ : Q₃ * Q₃ = 0) :
    (Q₁ + Q₂ + Q₃) * (Q₁ + Q₂ + Q₃) =
      (Q₁ * Q₂ + Q₂ * Q₁)
      + (Q₁ * Q₃ + Q₃ * Q₁)
      + (Q₂ * Q₃ + Q₃ * Q₂) := by
  calc
    (Q₁ + Q₂ + Q₃) * (Q₁ + Q₂ + Q₃)
        =
      Q₁ * Q₁ + Q₂ * Q₂ + Q₃ * Q₃
      + (Q₁ * Q₂ + Q₂ * Q₁)
      + (Q₁ * Q₃ + Q₃ * Q₁)
      + (Q₂ * Q₃ + Q₃ * Q₂) := by
        exact three_supercharge_square Q₁ Q₂ Q₃
    _ =
      0 + 0 + 0
      + (Q₁ * Q₂ + Q₂ * Q₁)
      + (Q₁ * Q₃ + Q₃ * Q₁)
      + (Q₂ * Q₃ + Q₃ * Q₂) := by
        rw [h₁, h₂, h₃]
    _ =
      (Q₁ * Q₂ + Q₂ * Q₁)
      + (Q₁ * Q₃ + Q₃ * Q₁)
      + (Q₂ * Q₃ + Q₃ * Q₂) := by
        simp

end RecursiveAlgebra

section Core

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- Local alias for the owned CPT gap/Hessian closure proposition. -/
@[rep_depth transport]
def cptGapHessianClosure
    (V : BogoliubovVielbeinBundle (E := E)) : Prop :=
  ((paritySuperchargeOp (E := E)).comp (modularSuperchargeOp (E := E))
      - (modularSuperchargeOp (E := E)).comp (paritySuperchargeOp (E := E))
      = (2 : ℝ) • cptSuperchargeOp (E := E))
    ∧
  (transportedParityModularGapSeed (E := E) V
      =
    CARBracket (E := E)
      (transportCommutator (E := E) V.connectionGenerator (paritySuperchargeOp (E := E)))
      (modularSuperchargeOp (E := E)))
    ∧
  (let X := V.connectionGenerator;
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    operatorInformationHessian (E := E) X (paritySuperchargeOp (E := E)))
    ∧
  (let X := V.connectionGenerator;
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    operatorInformationMetricPart (E := E) X X (paritySuperchargeOp (E := E))
      + ((2 : ℝ)⁻¹) • operatorInformationCurvaturePart (E := E) X X
          (paritySuperchargeOp (E := E)))

/-- Root-name form of the same transported gap/Hessian closure proposition. -/
@[rep_depth transport]
def rootGapHessianClosure
    (V : BogoliubovVielbeinBundle (E := E)) : Prop :=
  ((modular_j (E := E)).comp (spectral_epsilon (E := E))
      - (spectral_epsilon (E := E)).comp (modular_j (E := E))
      = (2 : ℝ) • complex_i (E := E))
    ∧
  (transportedParityModularGapSeed (E := E) V
      =
    CARBracket (E := E)
      (transportCommutator (E := E) V.connectionGenerator (modular_j (E := E)))
      (spectral_epsilon (E := E)))
    ∧
  (let X := V.connectionGenerator;
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    operatorInformationHessian (E := E) X (modular_j (E := E)))
    ∧
  (let X := V.connectionGenerator;
    deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
      =
    operatorInformationMetricPart (E := E) X X (modular_j (E := E))
      + ((2 : ℝ)⁻¹) • operatorInformationCurvaturePart (E := E) X X
          (modular_j (E := E)))

-- The root-name and bilingual CPT-name closure propositions are equivalent.
omit [KreinSpace H₂] [KreinGradedModule H₂] in
@[rep_depth transport]
theorem rootGapHessianClosure_iff_cptGapHessianClosure
    (V : BogoliubovVielbeinBundle (E := E)) :
    rootGapHessianClosure (E := E) V ↔ cptGapHessianClosure (E := E) V := by
  constructor <;> intro h
  · rcases h with ⟨hCCR, hGap, hHess, hSplit⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [cptSuperchargeOp_eq_complex_i] using hCCR
    · simpa using hGap
    · simpa using hHess
    · simpa using hSplit
  · rcases h with ⟨hCCR, hGap, hHess, hSplit⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [cptSuperchargeOp_eq_complex_i] using hCCR
    · simpa using hGap
    · simpa using hHess
    · simpa using hSplit

/--
On every Bogoliubov transport slice, the operatorial KK index is exactly the
operatorial central charge.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_eq_operatorialCentralCharge_on_cpt_lane
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX := by
  exact operatorialCentralCharge_eq_transport_slice
    (A := A) (B := B) (E := E) V X hX hEven t

/--
Closure package for the CPT-supercharge lane:

1. primitive `J/ε` CCR anchor,
2. first transport landing as the odd-odd gap seed,
3. second transport landing as the operatorial Hessian,
4. Hessian split into metric plus half-curvature,
5. transported analytical index equals the operatorial central charge,
6. nonzero operatorial central charge forces nonvanishing transported index.
-/
@[rep_depth transport]
theorem cpt_gap_hessian_centralCharge_closure
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    cptGapHessianClosure (E := E) V
      ∧
    (quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX)
      ∧
    (operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 →
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
        ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact transported_gapSeed_hessian_curvature_cpt_package (E := E) V
  · exact quasilatticeAnalyticalIndex_eq_operatorialCentralCharge_on_cpt_lane
      (A := A) (B := B) (E := E) V X hX hEven t
  · intro hCentral
    exact quasilatticeSlice_ne_zero_of_operatorialCentralCharge_ne_zero
      (A := A) (B := B) (E := E) V X hX hEven hCentral t

/--
Parity/KKT extension of the CPT-supercharge closure:

1. keeps the existing transported CPT gap/Hessian closure package,
2. upgrades nonzero `Z₂` central-charge parity to transported chiral mismatch,
3. and carries the same Dirac carrier through the KKT odd split with
   grade-zero odd-odd commutator once `gradeCLM = eps`.
-/
@[rep_depth transport]
theorem cpt_gap_hessian_parity_kkt_closure
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hGrade : KreinGradedModule.gradeCLM (H := H₂) = X.cl11.eps) :
    cptGapHessianClosure (E := E) V
      ∧
    TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E)
      V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ∧
    X.F = gOnePart X.cl11 X.F + gNegOnePart X.cl11 X.F
      ∧
    IsGZero X.cl11 (commutator (gOnePart X.cl11 X.F) (gNegOnePart X.cl11 X.F)) := by
  rcases cpt_gap_hessian_centralCharge_closure
      (A := A) (B := B) (E := E) V X hX hEven t with ⟨hGap, _, _⟩
  have hMismatch :
      TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E)
        V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) :=
    transportedChiralKernelDimMismatch_of_operatorialCentralChargeParity_ne_zero
      (A := A) (B := B) (E := E) V X hX hEven t hParity
  have hKKT :
      X.F = gOnePart X.cl11 X.F + gNegOnePart X.cl11 X.F
        ∧ IsGZero X.cl11 (commutator (gOnePart X.cl11 X.F) (gNegOnePart X.cl11 X.F)) :=
    dirac_kkt_odd_split_and_commutator_isGZero_of_gradeCLM_eq_eps
      (A := A) (B := B) (E := E) X hGrade
  exact ⟨hGap, hMismatch, hKKT.1, hKKT.2⟩

/--
Extended closure package:
the concrete oscillator/CAR spine, transported gap/Hessian closure, and
transported central-charge/index closure are carried on the same lane.
-/
@[rep_depth transport]
theorem cpt_gap_hessian_centralCharge_with_oscillator_spine
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    (CARBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E))
      = 0
      ∧ CCRBracket (E := E)
          (paritySuperchargeOp (E := E))
          (modularSuperchargeOp (E := E))
        = (2 : ℝ) • cptSuperchargeOp (E := E)
      ∧ (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E))
          = -(ContinuousLinearMap.id ℝ (DoubledSpace E))
      ∧ CARBracket (E := E)
          (concreteCARAnnihilation (E := E))
          (concreteCARAnnihilation (E := E))
        = 0
      ∧ CARBracket (E := E)
          (concreteCARCreation (E := E))
          (concreteCARCreation (E := E))
        = 0
      ∧ CARBracket (E := E)
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
        = ContinuousLinearMap.id ℝ (DoubledSpace E))
      ∧
    cptGapHessianClosure (E := E) V
      ∧
    (quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX)
      ∧
    (operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 →
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
        ≠ 0) := by
  rcases cpt_gap_hessian_centralCharge_closure
      (A := A) (B := B) (E := E) V X hX hEven t with
    ⟨hGap, hIdx, hNz⟩
  exact ⟨harmonic_oscillator_spine (E := E), hGap, hIdx, hNz⟩

/--
Root-name form of the full supercharge/gap/Hessian/central-charge closure
package.
-/
@[rep_depth transport]
theorem root_gap_hessian_centralCharge_closure
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    rootGapHessianClosure (E := E) V
      ∧
    (quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX)
      ∧
    (operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 →
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
        ≠ 0) := by
  rcases cpt_gap_hessian_centralCharge_closure
      (A := A) (B := B) (E := E) V X hX hEven t with ⟨hGap, hIdx, hNz⟩
  refine ⟨?_, hIdx, hNz⟩
  exact (rootGapHessianClosure_iff_cptGapHessianClosure (E := E) V).2 hGap

/--
Root-name parity/KKT extension of the transported supercharge closure.
-/
@[rep_depth transport]
theorem root_gap_hessian_parity_kkt_closure
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hGrade : KreinGradedModule.gradeCLM (H := H₂) = X.cl11.eps) :
    rootGapHessianClosure (E := E) V
      ∧
    TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E)
      V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ∧
    X.F = gOnePart X.cl11 X.F + gNegOnePart X.cl11 X.F
      ∧
    IsGZero X.cl11 (commutator (gOnePart X.cl11 X.F) (gNegOnePart X.cl11 X.F)) := by
  rcases cpt_gap_hessian_parity_kkt_closure
      (A := A) (B := B) (E := E) V X hX hEven t hParity hGrade with
    ⟨hGap, hMismatch, hSplit, hCommZero⟩
  refine ⟨?_, hMismatch, hSplit, hCommZero⟩
  exact (rootGapHessianClosure_iff_cptGapHessianClosure (E := E) V).2 hGap

/--
Root-name Lichnerowicz/charge closure on the transported supercharge lane:

1. the second transported parity-supercharge variation is the repo-native
   Laplace term `operatorInformationMetricPart` plus half the curvature
   correction,
2. the transported analytical index equals the operatorial central charge,
3. nonzero operatorial central charge forces nonvanishing transported index.
-/
@[rep_depth transport]
theorem root_supercharge_lichnerowicz_centralCharge_closure
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    (let X := V.connectionGenerator;
      deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
        =
      operatorInformationMetricPart (E := E) X X (modular_j (E := E))
        + ((2 : ℝ)⁻¹) • operatorInformationCurvaturePart (E := E) X X
            (modular_j (E := E)))
      ∧
    (quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX)
      ∧
    (operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 →
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
        ≠ 0) := by
  rcases root_gap_hessian_centralCharge_closure
      (A := A) (B := B) (E := E) V X hX hEven t with ⟨hRoot, hIdx, hNz⟩
  rcases hRoot with ⟨_, _, _, hLich⟩
  exact ⟨hLich, hIdx, hNz⟩

/--
Operator-valued central element induced by the operatorial central charge:
a scalar multiple of the identity on the doubled carrier.
-/
@[rep_depth transport]
noncomputable def operatorialCentralChargeOperator
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) : EndH :=
  (((operatorialCentralCharge (A := A) (B := B) (E := E) X hX : ℤ) : ℝ)) • (1 : EndH)

/--
Kinetic even part for the CPT supercharge square after extracting the
operator-valued central element.
-/
@[rep_depth transport]
noncomputable def cptSuperchargeKineticPart
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) : EndH :=
  -(ContinuousLinearMap.id ℝ H₂) - operatorialCentralChargeOperator (A := A) (B := B) (E := E) X hX

/--
The operator-valued central charge commutes with every doubled-carrier
endomorphism.
-/
@[rep_depth transport]
theorem operatorialCentralChargeOperator_commute
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (Y : EndH) :
    Commute (operatorialCentralChargeOperator (A := A) (B := B) (E := E) X hX) Y := by
  unfold operatorialCentralChargeOperator
  simpa using
    (Commute.one_left Y).smul_left
      ((((operatorialCentralCharge (A := A) (B := B) (E := E) X hX : ℤ) : ℝ)))

/--
CPT supercharge square decomposition on the doubled carrier:
`Q² = H + Z`, where `Z` is the operator-valued central charge element.
-/
@[rep_depth transport]
theorem cptSupercharge_sq_eq_kinetic_plus_centralChargeOperator
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) :
    (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E))
      =
    cptSuperchargeKineticPart (A := A) (B := B) (E := E) X hX
      + operatorialCentralChargeOperator (A := A) (B := B) (E := E) X hX := by
  unfold cptSuperchargeKineticPart
  rw [cptSuperchargeOp_sq]
  simp [operatorialCentralChargeOperator, sub_eq_add_neg]

/--
Central supercharge theorem on the root lane:

1. an explicit operator-valued central element `Z` is extracted from the
   operatorial central charge,
2. the CPT supercharge square decomposes as `Q² = H + Z` with `Z` central,
3. the transported root supercharge keeps the Lichnerowicz metric-plus-curvature
   closure,
4. the transported analytical index equals the operatorial central charge,
5. nonzero operatorial central charge forces nonvanishing transported index.
-/
@[rep_depth transport]
theorem root_central_supercharge_theorem
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    (let Z := operatorialCentralChargeOperator (A := A) (B := B) (E := E) X hX
     let H := cptSuperchargeKineticPart (A := A) (B := B) (E := E) X hX
     (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E)) = H + Z
       ∧ (∀ Y : EndH, Commute Z Y))
      ∧
    (let Xv := V.connectionGenerator;
      deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
        =
      operatorInformationMetricPart (E := E) Xv Xv (modular_j (E := E))
        + ((2 : ℝ)⁻¹) • operatorInformationCurvaturePart (E := E) Xv Xv
            (modular_j (E := E)))
      ∧
    (quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX)
      ∧
    (operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 →
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
        ≠ 0) := by
  rcases root_supercharge_lichnerowicz_centralCharge_closure
      (A := A) (B := B) (E := E) V X hX hEven t with ⟨hLich, hIdx, hNz⟩
  refine ⟨?_, hLich, hIdx, hNz⟩
  refine ⟨?_, ?_⟩
  · simpa using
      cptSupercharge_sq_eq_kinetic_plus_centralChargeOperator
        (A := A) (B := B) (E := E) X hX
  · intro Y
    simpa using
      operatorialCentralChargeOperator_commute (A := A) (B := B) (E := E) X hX Y

/--
Unified supercharge closure surface:

- supergraded CAR/CCR primitive algebra with CPT square law,
- central split `Q² = H + Z` with operator-valued central element,
- root transported supercharge parity/KKT odd split package,
- root Lichnerowicz closure,
- and operatorial central-charge/topological-index transport closure.
-/
@[rep_depth transport]
theorem unified_supercharge_central_supergeometry_topological_closure
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ)
    (hParity :
      operatorialCentralChargeParity (A := A) (B := B) X hX ≠ 0)
    (hGrade : KreinGradedModule.gradeCLM (H := H₂) = X.cl11.eps) :
    (CARBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E))
      = 0
      ∧
      CCRBracket (E := E)
          (paritySuperchargeOp (E := E))
          (modularSuperchargeOp (E := E))
        = (2 : ℝ) • cptSuperchargeOp (E := E)
      ∧
      (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E))
        = -(ContinuousLinearMap.id ℝ (DoubledSpace E)))
      ∧
    (let Z := operatorialCentralChargeOperator (A := A) (B := B) (E := E) X hX
     let H := cptSuperchargeKineticPart (A := A) (B := B) (E := E) X hX
     (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E)) = H + Z
       ∧ (∀ Y : EndH, Commute Z Y))
      ∧
    rootGapHessianClosure (E := E) V
      ∧
    TransportedChiralKernelDimMismatch (A := A) (B := B) (E := E)
      V X t (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ∧
    X.F = gOnePart X.cl11 X.F + gNegOnePart X.cl11 X.F
      ∧
    IsGZero X.cl11 (commutator (gOnePart X.cl11 X.F) (gNegOnePart X.cl11 X.F))
      ∧
    (let Xv := V.connectionGenerator;
      deriv (fun t => deriv (fun s => transportedParitySupercharge (E := E) V s) t) 0
        =
      operatorInformationMetricPart (E := E) Xv Xv (modular_j (E := E))
        + ((2 : ℝ)⁻¹) • operatorInformationCurvaturePart (E := E) Xv Xv
            (modular_j (E := E)))
      ∧
    (quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      =
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX)
      ∧
    (operatorialCentralCharge (A := A) (B := B) (E := E) X hX ≠ 0 →
      quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
        ≠ 0) := by
  rcases harmonic_oscillator_spine (E := E) with
    ⟨hCAR, hCCR, hSq, _, _, _⟩
  rcases root_gap_hessian_parity_kkt_closure
      (A := A) (B := B) (E := E) V X hX hEven t hParity hGrade with
    ⟨hRoot, hMismatch, hSplit, hGZero⟩
  rcases root_central_supercharge_theorem
      (A := A) (B := B) (E := E) V X hX hEven t with
    ⟨hCentralSplit, hLich, hIdx, hNz⟩
  exact ⟨⟨hCAR, hCCR, hSq⟩, hCentralSplit, hRoot, hMismatch, hSplit, hGZero, hLich, hIdx, hNz⟩

end Core

end InfoGeometry.Canonical.SuperchargeCentralChargeClosure
