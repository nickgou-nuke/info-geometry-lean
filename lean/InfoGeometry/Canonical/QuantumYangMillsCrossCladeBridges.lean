/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationGaugeTransport
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.OperatorAlgebra.YangMillsOrbitGramian
import InfoGeometry.Canonical.DrazinEpistemicSolveEtCoagula
import InfoGeometry.Canonical.KreinSpaceBRSTUnitarityBridge
import InfoGeometry.Superalgebra.FaradayYangMillsMonopoleChernSimons
import InfoGeometry.Superalgebra.GunaydinGurseyOctonionConfinement
import InfoGeometry.Superalgebra.SeibergWittenMonopoleDuality
import InfoGeometry.Canonical.AnomalyHigherGradeTDualityExtension

/-!
# Cross-Lane Algebraic Bridges: Derivations, Peirce Operators, Drazin Cohomology, and Coordinate Carriers

This module records explicit connections between existing repository owners. It does
not identify different carriers without a map, or derive geometric and physical
interpretations from the algebraic identities:

1. **Bridge A (inner derivations, Peirce curvature, and orbit commutator quadratic)**:
   - Bundles `AssociativeGaugeConnection.innerDerivative` into `NonAssocDerivation.derivations R A`
     (`innerNonAssocDerivation`).
   - Identifies the Clade I inner derivation `innerDerivative P` with the Clade II Peirce inner
     grading derivation `peirceGradingDeriv P` and orbit commutator `orbitCommutator P`.
   - Identifies `peirceCovariantDeriv P B C` with the sum of inner derivations
     `innerDerivative P + innerDerivative (genPhi P B C)`.
   - Distinguishes the right-module left-multiplication connection
     `peirceFundamentalConnection P B C` from the commutator covariant derivative and proves
     their exact difference by right multiplication. It also proves the second-order identity:
     $$\nabla_{P,\Phi}(\nabla_{P,\Phi}(X)) = \mathrm{peirceAdSq}\,P\,X + 2\,\Phi\,[P,X] + F_{\mathrm{MC}}(P,B,C)\,X,$$
     whose evaluation on `1 : A` recovers `peirceMaurerCartanCurvature P B C = genJ P B C + genV P B C`.
   - Under the stated self-adjoint idempotent hypotheses, identifies the orbit commutator
     quadratic with the Peirce boundary quadratic `genV P a a`. Related curvature and corner
     identities remain algebraic statements in the same ring carrier.

2. **Bridge B (Drazin decomposition of cycles modulo boundaries)**:
   - For any square-zero endomorphism `q` and endomorphism `b`, defines `L = q*b + b*q`
     and proves that `L` commutes with `q`.
   - Given a Drazin-inverse witness `G` for `L`, proves commutation with its regular and
     complementary projections and the homotopy identity `{q, b*G} = projection L G`.
   - For each `ψ ∈ ker q`, proves that its regular projection is a boundary, both projected
     terms are cycles, and their sum reconstructs `ψ`. Therefore the complementary Drazin
     component represents `[ψ]` in the explicitly defined quotient `ker q / range q`.
   - Separately proves pairing identities under the precise laws listed in each theorem.
     No inner-product data or Drazin-inverse existence theorem is assumed.

3. **Bridge C (coordinate equivalences between duplicated algebraic carriers)**:
   - Gives explicit coordinate equivalences between duplicated carriers. The proved laws
     preserve exactly the operations named in their theorem statements; an `Equiv` alone does
     not assert an algebra equivalence.
   - Relates the declared Faraday curvature expression to the Günaydin–Gürsey associator formula
     and proves a separate coordinate identity after applying the Seiberg–Witten map `J`.
     These are identities between the declared algebraic operations, not physical duality claims.
-/

noncomputable section

namespace InfoGeometry.Canonical.QuantumYangMillsCrossCladeBridges

open InfoGeometry.Algebra
open InfoGeometry.Geometry.AssociativeGaugeConnection
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.YangMillsOrbitGramian
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.DrazinCommutant
open InfoGeometry.Canonical.DrazinEpistemicSolveEtCoagula
open InfoGeometry.Canonical.BRSTExactClassZeroBridge
open InfoGeometry.Canonical.KreinSpaceBRSTUnitarityBridge
open InfoGeometry.Superalgebra

/-! ## 1. Inner Derivations, Peirce Curvature, and Orbit Quadratics -/

section BridgeA

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Bundled inner derivation `X ↦ a * X - X * a` as a member of the native Lie subalgebra
`NonAssocDerivation.derivations R A`. -/
def innerNonAssocDerivation (R : Type*) [CommRing R] [Algebra R A] (a : A) :
    NonAssocDerivation.derivations R A :=
  ⟨innerDerivative (R := R) a, innerDerivative_isLeibniz a⟩

@[simp] theorem innerNonAssocDerivation_apply (a x : A) :
    (innerNonAssocDerivation R a : Module.End R A) x = a * x - x * a := rfl

@[simp] theorem innerDerivative_apply (a x : A) :
    innerDerivative (R := R) a x = a * x - x * a := rfl

/-- Exact equational identification of the Clade I inner derivation `innerDerivative P`,
the Clade II-A Peirce grading derivation `peirceGradingDeriv P`, and the Clade II-B
Yang–Mills orbit commutator `orbitCommutator P`. -/
theorem innerDerivative_eq_peirceGradingDeriv_and_orbitCommutator (P X : A) :
    innerDerivative (R := R) P X = peirceGradingDeriv P X ∧
    peirceGradingDeriv P X = orbitCommutator P X :=
  ⟨rfl, rfl⟩

/-- The Clade II Peirce covariant derivative `peirceCovariantDeriv P B C` is the sum of the
Clade I inner derivation along `P` and the inner derivation along the off-diagonal connection
`genPhi P B C`. -/
theorem peirceCovariantDeriv_eq_innerDerivative_sum (P B C X : A) :
    peirceCovariantDeriv P B C X =
      innerDerivative (R := R) P X + innerDerivative (R := R) (genPhi P B C) X := rfl

/-- The fundamental right-module Peirce gauge connection
`∇_{P, Φ}(X) = [P, X] + (genPhi P B C) * X`, constructed via
`AssociativeGaugeConnection.covariantDerivative`. -/
def peirceFundamentalConnection (R : Type*) [CommRing R] [Algebra R A] (P B C : A) :
    Module.End R A :=
  covariantDerivative (innerDerivative (R := R) P) (genPhi P B C)

@[simp] theorem peirceFundamentalConnection_apply (P B C X : A) :
    peirceFundamentalConnection R P B C X =
      peirceGradingDeriv P X + genPhi P B C * X := rfl

/-- The left-multiplication connection differs from the commutator covariant derivative
by right multiplication by the same coefficient. This distinguishes the two actions in
the noncommutative coefficient ring. -/
theorem peirceFundamentalConnection_eq_covariantDeriv_add_right_mul
    (P B C X : A) :
    peirceFundamentalConnection R P B C X =
      peirceCovariantDeriv P B C X + X * genPhi P B C := by
  simp only [peirceFundamentalConnection_apply, peirceCovariantDeriv,
    peirceGradingDeriv, InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
    sub_eq_add_neg]
  abel

/-- `peirceFundamentalConnection` obeys the right-module Leibniz connection law with respect
to `peirceGradingDeriv P`. -/
theorem peirceFundamentalConnection_leibniz (P B C X Y : A) :
    peirceFundamentalConnection R P B C (X * Y) =
      peirceFundamentalConnection R P B C X * Y + X * peirceGradingDeriv P Y :=
  connection_leibniz (innerDerivative (R := R) P) (innerDerivative_isLeibniz P)
    (genPhi P B C) X Y

/-- **Universal Second-Order Iterated Peirce Connection Identity**:
Applying the fundamental Peirce connection `∇_{P, Φ}` twice decomposes into the second-order
Peirce superoperator `peirceAdSq P X`, the first-order cross-term `2 • (genPhi P B C * peirceGradingDeriv P X)`,
and left multiplication by the Peirce Maurer–Cartan curvature `peirceMaurerCartanCurvature P B C`. -/
theorem peirceFundamentalConnection_sq_apply (P B C X : A) :
    peirceFundamentalConnection R P B C (peirceFundamentalConnection R P B C X) =
      peirceAdSq P X +
        (2 : ℤ) • (genPhi P B C * peirceGradingDeriv P X) +
        peirceMaurerCartanCurvature P B C * X := by
  simp only [peirceFundamentalConnection_apply, peirceMaurerCartanCurvature,
    peirceGradingDeriv, peirceAdSq, InfoGeometry.OperatorAlgebra.PeirceSpine.comm, two_zsmul]
  noncomm_ring

/-- **Vacuum Section Curvature Readout**:
Evaluating the iterated fundamental Peirce connection on the unit section `1 : A` recovers the
exact Peirce Maurer–Cartan curvature `peirceMaurerCartanCurvature P B C = genJ P B C + genV P B C`. -/
theorem peirceFundamentalConnection_sq_one {P : A} (hP : P * P = P) (B C : A) :
    peirceFundamentalConnection R P B C (peirceFundamentalConnection R P B C 1) =
      peirceMaurerCartanCurvature P B C ∧
    peirceMaurerCartanCurvature P B C = genJ P B C + genV P B C := by
  refine ⟨?_, (peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills hP B C 1 1).2.2.1⟩
  rw [peirceFundamentalConnection_sq_apply]
  have h1 : peirceGradingDeriv P (1 : A) = 0 := by
    unfold peirceGradingDeriv InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    noncomm_ring
  have h2 : peirceAdSq P (1 : A) = 0 := by
    unfold peirceAdSq InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    noncomm_ring
  rw [h1, h2, mul_zero, smul_zero, add_zero, zero_add, mul_one]

/-- **Even-Grade Section Curvature Readout**:
On any section `X : A` annihilated by `peirceGradingDeriv P` (in particular any even-grade
element `evenGrade P Y`), the square of `peirceFundamentalConnection` acts purely by left
multiplication by `peirceMaurerCartanCurvature P B C`. -/
theorem peirceFundamentalConnection_sq_of_gradingDeriv_zero
    (P B C X : A) (hX : peirceGradingDeriv P X = 0) :
    peirceFundamentalConnection R P B C (peirceFundamentalConnection R P B C X) =
      peirceMaurerCartanCurvature P B C * X := by
  rw [peirceFundamentalConnection_sq_apply]
  have hAdSq : peirceAdSq P X = 0 := by
    change peirceGradingDeriv P (peirceGradingDeriv P X) = 0
    rw [hX]
    unfold peirceGradingDeriv InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    noncomm_ring
  rw [hX, hAdSq, mul_zero, smul_zero, add_zero, zero_add]

/-- For any `P a : A`, `peirceGradingDeriv P a` is the odd Peirce rotor `genJ P a a`. -/
theorem peirceGradingDeriv_eq_genJ (P a : A) :
    peirceGradingDeriv P a = genJ P a a := by
  unfold peirceGradingDeriv InfoGeometry.OperatorAlgebra.PeirceSpine.comm genJ conePlus coneMinus
  noncomm_ring

/-- Under the stated self-adjoint idempotent hypotheses, identifies the orbit commutator
quadratic with the Peirce boundary quadratic in the same star-ring carrier. -/
theorem orbitMassMode_eq_genV
    [StarRing A] {P a : A}
    (hP : P * P = P) (hPs : star P = P) (has : star a = a) :
    orbitMassMode P a = genV P a a := by
  have hNegSq : orbitMassMode P a = -(peirceGradingDeriv P a * peirceGradingDeriv P a) :=
    orbitMassMode_eq_neg_commutator_sq hPs has
  have hGenV : orbitMassMode P a = genV P a a := by
    rw [hNegSq]
    unfold peirceGradingDeriv InfoGeometry.OperatorAlgebra.PeirceSpine.comm genV conePlus coneMinus
    peirce_nf hP
  exact hGenV

/-- Under the stated self-adjoint idempotent hypotheses, `orbitMassMode P a` equals the even-grade
sector of `peirceMaurerCartanCurvature P a a`, is parity-even, is covariantly constant under
`peirceCovariantDeriv P a a`, and has physical Peirce corner equal to the forward-block Gramian
`orbitPeirce10 P a * star (orbitPeirce10 P a)`. -/
theorem orbitMassMode_bianchi_and_corner_gramians
    [StarRing A] {P a : A}
    (hP : P * P = P) (hPs : star P = P) (has : star a = a) :
    evenGrade P (peirceMaurerCartanCurvature P a a) = orbitMassMode P a ∧
    parityConj P (orbitMassMode P a) = orbitMassMode P a ∧
    peirceCovariantDeriv P a a (orbitMassMode P a) = 0 ∧
    P * orbitMassMode P a * P =
      orbitPeirce10 P a * star (orbitPeirce10 P a) := by
  have hGenV : orbitMassMode P a = genV P a a := orbitMassMode_eq_genV hP hPs has
  have hMC := peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills hP a a 1 1
  refine ⟨?_, ?_, ?_, orbitMassMode_core_eq_peirce_gram hP hPs has⟩
  · rw [hGenV]
    exact hMC.2.2.2.1
  · rw [hGenV]
    exact hMC.2.2.2.2.2.1
  · rw [hGenV]
    exact hMC.2.2.2.2.2.2.2.2.2.1

end BridgeA

/-! ## 2. Drazin Decomposition of Cycles Modulo Boundaries -/

section BridgeB

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The anticommutator endomorphism `L = q * b + b * q`. -/
def brstFaddeevPopovLaplacian (q b_fermion : Module.End R M) : Module.End R M :=
  q * b_fermion + b_fermion * q

/-- The composite endomorphism `K = b * G`. -/
def drazinBRSTHomotopy (b_fermion G_fp : Module.End R M) : Module.End R M :=
  b_fermion * G_fp

/-- `q.comp q = 0` is equivalent to `q * q = 0` in `Module.End R M`. -/
theorem brst_mul_self_eq_zero_of_comp_eq_zero
    {q : Module.End R M} (hq2 : q.comp q = 0) :
    q * q = 0 := hq2

/-- The anticommutator `L = q * b + b * q` commutes with `q` when `q² = 0`. -/
theorem brstFaddeevPopovLaplacian_comm_brst
    {q : Module.End R M} (hq2 : q.comp q = 0) (b_fermion : Module.End R M) :
    brstFaddeevPopovLaplacian q b_fermion * q =
      q * brstFaddeevPopovLaplacian q b_fermion := by
  have hq : q * q = 0 := hq2
  unfold brstFaddeevPopovLaplacian
  calc
    (q * b_fermion + b_fermion * q) * q
        = q * b_fermion * q + b_fermion * (q * q) := by noncomm_ring
    _ = q * b_fermion * q + b_fermion * 0 := by rw [hq]
    _ = (q * q) * b_fermion + q * b_fermion * q := by rw [hq]; noncomm_ring
    _ = q * (q * b_fermion + b_fermion * q) := by noncomm_ring

/-- If `q` commutes with `L` and `G` is a Drazin inverse of `L`, then `q` commutes with `G`
and its regular and complementary Drazin projections. The Drazin witness is an assumption. -/
theorem drazin_propagator_and_projections_commute_with_q
    {q b_fermion G_fp : Module.End R M} {k : ℕ}
    (hq2 : q.comp q = 0)
    (hD : IsDrazinInverse (brstFaddeevPopovLaplacian q b_fermion) G_fp k) :
    G_fp * q = q * G_fp ∧
    projection (brstFaddeevPopovLaplacian q b_fermion) G_fp * q =
      q * projection (brstFaddeevPopovLaplacian q b_fermion) G_fp ∧
    complementaryProjection (brstFaddeevPopovLaplacian q b_fermion) G_fp * q =
      q * complementaryProjection (brstFaddeevPopovLaplacian q b_fermion) G_fp := by
  have hLq := brstFaddeevPopovLaplacian_comm_brst hq2 b_fermion
  have hGq := inverse_commutes_of_commutes hD q hLq
  have hProj := projection_commutes_of_commutes hD hLq
  exact ⟨hGq, hProj.1, hProj.2⟩

/-- The anticommutator `{q, b * G}` equals the regular Drazin projection of `q * b + b * q`. -/
theorem drazinBRSTHomotopy_anticomm_eq_projection
    {q b_fermion G_fp : Module.End R M} {k : ℕ}
    (hq2 : q.comp q = 0)
    (hD : IsDrazinInverse (brstFaddeevPopovLaplacian q b_fermion) G_fp k) :
    q * drazinBRSTHomotopy b_fermion G_fp + drazinBRSTHomotopy b_fermion G_fp * q =
      projection (brstFaddeevPopovLaplacian q b_fermion) G_fp := by
  have hGq : G_fp * q = q * G_fp := (drazin_propagator_and_projections_commute_with_q hq2 hD).1
  unfold drazinBRSTHomotopy projection brstFaddeevPopovLaplacian
  calc
    q * (b_fermion * G_fp) + (b_fermion * G_fp) * q
        = q * b_fermion * G_fp + b_fermion * (G_fp * q) := by noncomm_ring
    _ = q * b_fermion * G_fp + b_fermion * (q * G_fp) := by rw [hGq]
    _ = (q * b_fermion + b_fermion * q) * G_fp := by noncomm_ring

/-- **Exactness of the Regular Drazin Component on Physical States**:
For any BRST-closed state `ψ : M` (`isPhysicalState q ψ`, i.e., `q ψ = 0`):
1. `(projection L_fp G_fp) ψ = q (drazinBRSTHomotopy b_fermion G_fp ψ)` (the regular Drazin
   component is BRST-exact),
2. both `(projection L_fp G_fp) ψ` and `(complementaryProjection L_fp G_fp) ψ` are BRST-closed,
3. `ψ = (complementaryProjection L_fp G_fp) ψ + q (drazinBRSTHomotopy b_fermion G_fp ψ)`. -/
theorem drazin_regular_component_exact_on_physical_state
    {q b_fermion G_fp : Module.End R M} {k : ℕ}
    (hq2 : q.comp q = 0)
    (hD : IsDrazinInverse (brstFaddeevPopovLaplacian q b_fermion) G_fp k)
    {ψ : M} (hψ : isPhysicalState q ψ) :
    projection (brstFaddeevPopovLaplacian q b_fermion) G_fp ψ =
      q (drazinBRSTHomotopy b_fermion G_fp ψ) ∧
    isPhysicalState q (projection (brstFaddeevPopovLaplacian q b_fermion) G_fp ψ) ∧
    isPhysicalState q (complementaryProjection (brstFaddeevPopovLaplacian q b_fermion) G_fp ψ) ∧
    ψ = complementaryProjection (brstFaddeevPopovLaplacian q b_fermion) G_fp ψ +
          q (drazinBRSTHomotopy b_fermion G_fp ψ) := by
  have hHom := drazinBRSTHomotopy_anticomm_eq_projection hq2 hD
  have hComm := drazin_propagator_and_projections_commute_with_q hq2 hD
  have hqψ : q ψ = 0 := hψ
  have hExact : projection (brstFaddeevPopovLaplacian q b_fermion) G_fp ψ =
      q (drazinBRSTHomotopy b_fermion G_fp ψ) := by
    have hApp := congrArg (fun T : Module.End R M => T ψ) hHom.symm
    simpa [LinearMap.add_apply, Module.End.mul_apply, hqψ] using hApp
  have hPhysReg : isPhysicalState q
      (projection (brstFaddeevPopovLaplacian q b_fermion) G_fp ψ) := by
    unfold isPhysicalState
    rw [hExact]
    exact LinearMap.congr_fun hq2 (drazinBRSTHomotopy b_fermion G_fp ψ)
  have hPhysComplement : isPhysicalState q
      (complementaryProjection (brstFaddeevPopovLaplacian q b_fermion) G_fp ψ) := by
    unfold isPhysicalState
    have hQcomm := congrArg (fun T : Module.End R M => T ψ) hComm.2.2.symm
    simpa [Module.End.mul_apply, hqψ] using hQcomm
  have hDecomp : ψ =
      complementaryProjection (brstFaddeevPopovLaplacian q b_fermion) G_fp ψ +
        q (drazinBRSTHomotopy b_fermion G_fp ψ) := by
    rw [← hExact]
    have hSum := congrArg (fun T : Module.End R M => T ψ)
      (projection_add_complementaryProjection
        (a := brstFaddeevPopovLaplacian q b_fermion) (b := G_fp)).symm
    simpa [LinearMap.add_apply, add_comm] using hSum
  exact ⟨hExact, hPhysReg, hPhysComplement, hDecomp⟩

/-- **Cohomology Decomposition by Complementary Drazin Projection**:
For every `ψ : LinearMap.ker q`, its regular Drazin component is zero in the quotient
`ker q / range q`, while the complementary Drazin component represents the same quotient
quotient element represented by `ψ`. The Drazin inverse is an explicit hypothesis; no spectral or horizon
interpretation is asserted. -/
theorem brstCohomology_decomposes_via_complementary_drazin_projection
    {q b_fermion G_fp : Module.End R M} {k : ℕ}
    (hq2 : q.comp q = 0)
    (hD : IsDrazinInverse (brstFaddeevPopovLaplacian q b_fermion) G_fp k)
    (ψ : LinearMap.ker q) :
    let L_fp := brstFaddeevPopovLaplacian q b_fermion
    let hClosed := drazin_regular_component_exact_on_physical_state hq2 hD ψ.2
    Submodule.Quotient.mk (p := LinearMap.range (brstExactToClosed q hq2))
      ⟨projection L_fp G_fp ψ.1, hClosed.2.1⟩ =
      (Submodule.Quotient.mk 0 : brstCohomologyModule q hq2) ∧
    Submodule.Quotient.mk (p := LinearMap.range (brstExactToClosed q hq2))
      ⟨complementaryProjection L_fp G_fp ψ.1, hClosed.2.2.1⟩ =
      (Submodule.Quotient.mk (p := LinearMap.range (brstExactToClosed q hq2)) ψ :
        brstCohomologyModule q hq2) := by
  intro L_fp hClosed
  constructor
  · change Submodule.Quotient.mk (p := LinearMap.range (brstExactToClosed q hq2))
        ⟨projection L_fp G_fp ψ.1, hClosed.2.1⟩ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨q (drazinBRSTHomotopy b_fermion G_fp ψ.1),
      LinearMap.mem_range_self q (drazinBRSTHomotopy b_fermion G_fp ψ.1)⟩, ?_⟩
    ext
    exact hClosed.1.symm
  · rw [Submodule.Quotient.eq]
    refine ⟨⟨-q (drazinBRSTHomotopy b_fermion G_fp ψ.1),
      ⟨-drazinBRSTHomotopy b_fermion G_fp ψ.1, map_neg q _⟩⟩, ?_⟩
    ext
    dsimp [brstExactToClosed]
    have hDecomp := hClosed.2.2.2
    calc
      -q (drazinBRSTHomotopy b_fermion G_fp ψ.1)
          = (complementaryProjection L_fp G_fp ψ.1 +
              q (drazinBRSTHomotopy b_fermion G_fp ψ.1)) -
            (complementaryProjection L_fp G_fp ψ.1 +
              q (drazinBRSTHomotopy b_fermion G_fp ψ.1)) -
            q (drazinBRSTHomotopy b_fermion G_fp ψ.1) := by abel
      _ = complementaryProjection L_fp G_fp ψ.1 - ψ.1 := by
        nth_rw 2 [← hDecomp]
        abel

/-- For a supplied pairing satisfying the displayed adjointness and zero laws, the regular
Drazin component pairs to zero with a `q`-closed state. No inner-product or Krein-space
data is assumed. -/
theorem pairing_vanishes_on_regular_drazin_component
    {q b_fermion G_fp : Module.End R M} {k : ℕ}
    (hq2 : q.comp q = 0)
    (hD : IsDrazinInverse (brstFaddeevPopovLaplacian q b_fermion) G_fp k)
    (inner : M → M → R)
    (h_adj : ∀ x y, inner (q x) y = inner x (q y))
    (h_zero1 : ∀ y, inner 0 y = 0)
    {φ ψ : M} (hφ : isPhysicalState q φ) (hψ : isPhysicalState q ψ) :
    inner φ (projection (brstFaddeevPopovLaplacian q b_fermion) G_fp ψ) = 0 := by
  have hClosed := drazin_regular_component_exact_on_physical_state hq2 hD hψ
  have hOrtho : inner φ (projection (brstFaddeevPopovLaplacian q b_fermion) G_fp ψ) = 0 := by
    rw [hClosed.1]
    exact physical_state_exact_decoupling_orthogonality inner q h_adj h_zero1
      φ (drazinBRSTHomotopy b_fermion G_fp ψ) hφ
  exact hOrtho

/-- Right-additivity of a supplied pairing reduces its value on a `q`-closed vector to the
complementary Drazin component, since the regular component is exact. -/
theorem pairing_eq_complementary_drazin_component
    {q b_fermion G_fp : Module.End R M} {k : ℕ}
    (hq2 : q.comp q = 0)
    (hD : IsDrazinInverse (brstFaddeevPopovLaplacian q b_fermion) G_fp k)
    (inner : M → M → R)
    (h_adj : ∀ x y, inner (q x) y = inner x (q y))
    (h_zero1 : ∀ y, inner 0 y = 0)
    (h_add_right : ∀ x y z, inner x (y + z) = inner x y + inner x z)
    {φ ψ : M} (hφ : isPhysicalState q φ) (hψ : isPhysicalState q ψ) :
    inner φ ψ =
      inner φ (complementaryProjection (brstFaddeevPopovLaplacian q b_fermion) G_fp ψ) := by
  have hClosed := drazin_regular_component_exact_on_physical_state hq2 hD hψ
  have hOrtho := pairing_vanishes_on_regular_drazin_component
    hq2 hD inner h_adj h_zero1 hφ hψ
  conv_lhs => rw [hClosed.2.2.2]
  rw [h_add_right, ← hClosed.1, hOrtho, add_zero]

end BridgeB

/-! ## 3. Coordinate Equivalences Between Split-Octonion Carriers -/

section BridgeC

variable {R : Type*} [CommRing R]

/-- Canonical equivalence between `FaradayYangMillsChernSimons.ColorVec3 R` and
`GunaydinGursey.ColorVec3 R`. -/
def colorVec3FaradayToGGEquiv :
    FaradayYangMillsChernSimons.ColorVec3 R ≃ GunaydinGursey.ColorVec3 R where
  toFun u := ⟨u.c1, u.c2, u.c3⟩
  invFun u := ⟨u.c1, u.c2, u.c3⟩
  left_inv u := by cases u; rfl
  right_inv u := by cases u; rfl

/-- Canonical equivalence between `FaradayYangMillsChernSimons.ColorVec3 R` and
`SeibergWitten.ColorVec3 R`. -/
def colorVec3FaradayToSWEquiv :
    FaradayYangMillsChernSimons.ColorVec3 R ≃ SeibergWitten.ColorVec3 R where
  toFun u := ⟨u.c1, u.c2, u.c3⟩
  invFun u := ⟨u.c1, u.c2, u.c3⟩
  left_inv u := by cases u; rfl
  right_inv u := by cases u; rfl

/-- Canonical equivalence between `FaradayYangMillsChernSimons.SplitOctonion R` and
`GunaydinGursey.SplitOctonion R`. -/
def splitOctonionFaradayToGGEquiv :
    FaradayYangMillsChernSimons.SplitOctonion R ≃ GunaydinGursey.SplitOctonion R where
  toFun X := ⟨X.a, colorVec3FaradayToGGEquiv X.u, colorVec3FaradayToGGEquiv X.v, X.b⟩
  invFun X := ⟨X.a, colorVec3FaradayToGGEquiv.symm X.u, colorVec3FaradayToGGEquiv.symm X.v, X.b⟩
  left_inv X := by
    rcases X with ⟨a, ⟨u1, u2, u3⟩, ⟨v1, v2, v3⟩, b⟩
    rfl
  right_inv X := by
    rcases X with ⟨a, ⟨u1, u2, u3⟩, ⟨v1, v2, v3⟩, b⟩
    rfl

/-- Canonical equivalence between `FaradayYangMillsChernSimons.SplitOctonion R` and
`SeibergWitten.SplitOctonion R`. -/
def splitOctonionFaradayToSWEquiv :
    FaradayYangMillsChernSimons.SplitOctonion R ≃ SeibergWitten.SplitOctonion R where
  toFun X := ⟨X.a, colorVec3FaradayToSWEquiv X.u, colorVec3FaradayToSWEquiv X.v, X.b⟩
  invFun X := ⟨X.a, colorVec3FaradayToSWEquiv.symm X.u, colorVec3FaradayToSWEquiv.symm X.v, X.b⟩
  left_inv X := by
    rcases X with ⟨a, ⟨u1, u2, u3⟩, ⟨v1, v2, v3⟩, b⟩
    rfl
  right_inv X := by
    rcases X with ⟨a, ⟨u1, u2, u3⟩, ⟨v1, v2, v3⟩, b⟩
    rfl

/-- The coordinate equivalence preserves the declared multiplication, addition, and scaling. -/
theorem splitOctonionFaradayToGGEquiv_hom
    (k : R) (u v : FaradayYangMillsChernSimons.ColorVec3 R)
    (X Y : FaradayYangMillsChernSimons.SplitOctonion R) :
    splitOctonionFaradayToGGEquiv (FaradayYangMillsChernSimons.SplitOctonion.mul X Y) =
      GunaydinGursey.SplitOctonion.mul
        (splitOctonionFaradayToGGEquiv X) (splitOctonionFaradayToGGEquiv Y) ∧
    splitOctonionFaradayToGGEquiv (FaradayYangMillsChernSimons.SplitOctonion.add X Y) =
      GunaydinGursey.SplitOctonion.add
        (splitOctonionFaradayToGGEquiv X) (splitOctonionFaradayToGGEquiv Y) ∧
    splitOctonionFaradayToGGEquiv (FaradayYangMillsChernSimons.SplitOctonion.scale k X) =
      GunaydinGursey.SplitOctonion.scale k (splitOctonionFaradayToGGEquiv X) ∧
    splitOctonionFaradayToGGEquiv
        (FaradayYangMillsChernSimons.SplitOctonion.paraSymplecticK0 (R := R)) =
      GunaydinGursey.SplitOctonion.paraSymplecticK0 ∧
    splitOctonionFaradayToGGEquiv (FaradayYangMillsChernSimons.SplitOctonion.quark u) =
      GunaydinGursey.SplitOctonion.quark (colorVec3FaradayToGGEquiv u) ∧
    splitOctonionFaradayToGGEquiv (FaradayYangMillsChernSimons.SplitOctonion.antiquark v) =
      GunaydinGursey.SplitOctonion.antiquark (colorVec3FaradayToGGEquiv v) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The coordinate equivalence preserves the declared multiplication, addition, and scaling. -/
theorem splitOctonionFaradayToSWEquiv_hom
    (k : R) (u v : FaradayYangMillsChernSimons.ColorVec3 R)
    (X Y : FaradayYangMillsChernSimons.SplitOctonion R) :
    splitOctonionFaradayToSWEquiv (FaradayYangMillsChernSimons.SplitOctonion.mul X Y) =
      SeibergWitten.SplitOctonion.mul
        (splitOctonionFaradayToSWEquiv X) (splitOctonionFaradayToSWEquiv Y) ∧
    splitOctonionFaradayToSWEquiv (FaradayYangMillsChernSimons.SplitOctonion.add X Y) =
      SeibergWitten.SplitOctonion.add
        (splitOctonionFaradayToSWEquiv X) (splitOctonionFaradayToSWEquiv Y) ∧
    splitOctonionFaradayToSWEquiv (FaradayYangMillsChernSimons.SplitOctonion.scale k X) =
      SeibergWitten.SplitOctonion.scale k (splitOctonionFaradayToSWEquiv X) ∧
    splitOctonionFaradayToSWEquiv
        (FaradayYangMillsChernSimons.SplitOctonion.paraSymplecticK0 (R := R)) =
      SeibergWitten.SplitOctonion.paraSymplecticK0 ∧
    splitOctonionFaradayToSWEquiv (FaradayYangMillsChernSimons.SplitOctonion.quark u) =
      SeibergWitten.SplitOctonion.quark (colorVec3FaradayToSWEquiv u) ∧
    splitOctonionFaradayToSWEquiv (FaradayYangMillsChernSimons.SplitOctonion.antiquark v) =
      SeibergWitten.SplitOctonion.antiquark (colorVec3FaradayToSWEquiv v) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [CommRing R] in
@[simp] theorem colorVec3FaradayToGGEquiv_apply
    (u : FaradayYangMillsChernSimons.ColorVec3 R) :
    colorVec3FaradayToGGEquiv u = ⟨u.c1, u.c2, u.c3⟩ := rfl

omit [CommRing R] in
@[simp] theorem colorVec3FaradayToGGEquiv_symm_apply
    (u : GunaydinGursey.ColorVec3 R) :
    colorVec3FaradayToGGEquiv.symm u = ⟨u.c1, u.c2, u.c3⟩ := rfl

omit [CommRing R] in
@[simp] theorem colorVec3FaradayToSWEquiv_apply
    (u : FaradayYangMillsChernSimons.ColorVec3 R) :
    colorVec3FaradayToSWEquiv u = ⟨u.c1, u.c2, u.c3⟩ := rfl

omit [CommRing R] in
@[simp] theorem splitOctonionFaradayToGGEquiv_symm_apply
    (X : GunaydinGursey.SplitOctonion R) :
    splitOctonionFaradayToGGEquiv.symm X =
      ⟨X.a, colorVec3FaradayToGGEquiv.symm X.u, colorVec3FaradayToGGEquiv.symm X.v, X.b⟩ := rfl

omit [CommRing R] in
@[simp] theorem splitOctonionFaradayToSWEquiv_apply
    (X : FaradayYangMillsChernSimons.SplitOctonion R) :
    splitOctonionFaradayToSWEquiv X =
      ⟨X.a, colorVec3FaradayToSWEquiv X.u, colorVec3FaradayToSWEquiv X.v, X.b⟩ := rfl

/-- Relates the declared Faraday curvature expression to a transported associator formula and
proves a second coordinate identity after applying the explicitly defined map `J`. -/
theorem faraday_monopole_baryon_associator_seiberg_witten_bridge
    (u da db : FaradayYangMillsChernSimons.ColorVec3 R) :
    FaradayYangMillsChernSimons.SplitOctonion.faradayYangMillsCurvature u da db =
      FaradayYangMillsChernSimons.SplitOctonion.add
        (FaradayYangMillsChernSimons.SplitOctonion.scale 2
          (splitOctonionFaradayToGGEquiv.symm
            (GunaydinGursey.SplitOctonion.associator
              (GunaydinGursey.SplitOctonion.quark (colorVec3FaradayToGGEquiv u))
              (GunaydinGursey.SplitOctonion.quark (colorVec3FaradayToGGEquiv da))
              (GunaydinGursey.SplitOctonion.quark (colorVec3FaradayToGGEquiv db)))))
        (FaradayYangMillsChernSimons.SplitOctonion.scale
          (-2 * FaradayYangMillsChernSimons.ColorVec3.det3 u da db)
          (FaradayYangMillsChernSimons.SplitOctonion.quark u)) ∧
    SeibergWitten.SplitOctonion.J
        (splitOctonionFaradayToSWEquiv
          (FaradayYangMillsChernSimons.SplitOctonion.faradayYangMillsCurvature u da db)) =
      SeibergWitten.SplitOctonion.scale
        (2 * FaradayYangMillsChernSimons.ColorVec3.det3 u da db)
        (SeibergWitten.SplitOctonion.add SeibergWitten.SplitOctonion.paraSymplecticK0
          (SeibergWitten.SplitOctonion.antiquark (colorVec3FaradayToSWEquiv u))) := by
  rw [FaradayYangMillsChernSimons.SplitOctonion.faraday_yang_mills_monopole_reduction u da db]
  rw [GunaydinGursey.SplitOctonion.baryon_associator_eq_neg_det_k0]
  constructor
  · simp only [splitOctonionFaradayToGGEquiv_symm_apply,
      colorVec3FaradayToGGEquiv_apply, colorVec3FaradayToGGEquiv_symm_apply,
      FaradayYangMillsChernSimons.SplitOctonion.add,
      FaradayYangMillsChernSimons.SplitOctonion.scale,
      FaradayYangMillsChernSimons.SplitOctonion.paraSymplecticK0,
      FaradayYangMillsChernSimons.SplitOctonion.quark,
      GunaydinGursey.SplitOctonion.scale,
      GunaydinGursey.SplitOctonion.paraSymplecticK0,
      FaradayYangMillsChernSimons.ColorVec3.det3,
      GunaydinGursey.ColorVec3.det3,
      FaradayYangMillsChernSimons.ColorVec3.dot,
      GunaydinGursey.ColorVec3.dot,
      FaradayYangMillsChernSimons.ColorVec3.cross,
      GunaydinGursey.ColorVec3.cross,
      FaradayYangMillsChernSimons.ColorVec3.add,
      FaradayYangMillsChernSimons.ColorVec3.smul,
      GunaydinGursey.ColorVec3.smul,
      FaradayYangMillsChernSimons.ColorVec3.zero,
      GunaydinGursey.ColorVec3.zero]
    ext <;> ring
  · simp only [splitOctonionFaradayToSWEquiv_apply,
      colorVec3FaradayToSWEquiv_apply,
      FaradayYangMillsChernSimons.SplitOctonion.add,
      FaradayYangMillsChernSimons.SplitOctonion.scale,
      FaradayYangMillsChernSimons.SplitOctonion.paraSymplecticK0,
      FaradayYangMillsChernSimons.SplitOctonion.quark,
      SeibergWitten.SplitOctonion.J,
      SeibergWitten.SplitOctonion.scale,
      SeibergWitten.SplitOctonion.add,
      SeibergWitten.SplitOctonion.paraSymplecticK0,
      SeibergWitten.SplitOctonion.antiquark,
      FaradayYangMillsChernSimons.ColorVec3.det3,
      FaradayYangMillsChernSimons.ColorVec3.dot,
      FaradayYangMillsChernSimons.ColorVec3.cross,
      FaradayYangMillsChernSimons.ColorVec3.add,
      FaradayYangMillsChernSimons.ColorVec3.smul,
      FaradayYangMillsChernSimons.ColorVec3.zero,
      SeibergWitten.ColorVec3.neg,
      SeibergWitten.ColorVec3.add,
      SeibergWitten.ColorVec3.smul,
      SeibergWitten.ColorVec3.zero]
    ext <;> ring

end BridgeC

/-! ## 4. Bridge D: Anomaly Counterexamples, 5-Graded Contact Extension & O(5,5) T-Duality -/

section BridgeD

open InfoGeometry.Canonical.AnomalyHigherGradeTDualityExtension

/-- **Bridge D (Higher-Grade Anomaly Extension to $O(5,5)$ T-Duality)**:
1. The non-zero grade-$\pm 2$ anomaly generators `anomalyGeneratorMinusTwo` and
   `anomalyGeneratorPlusTwo` in `O55Lie` have Lie bracket equal to the
   5-graded contact Euler element `Orthogonal.O55Contact.contactEuler`.
2. The $O(5,5)$ T-duality involution `tDualityLie` exchanges `anomalyGeneratorPlusTwo`
   and `anomalyGeneratorMinusTwo` while negating the 5-graded contact Euler grading
   `tDualityLie Orthogonal.O55Contact.contactEuler = -Orthogonal.O55Contact.contactEuler`. -/
theorem anomaly_higher_grade_to_tduality_bridge :
    ⁅anomalyGeneratorMinusTwo, anomalyGeneratorPlusTwo⁆ =
      InfoGeometry.Orthogonal.O55Contact.contactEuler ∧
    tDualityLie anomalyGeneratorPlusTwo = anomalyGeneratorMinusTwo ∧
    tDualityLie anomalyGeneratorMinusTwo = anomalyGeneratorPlusTwo ∧
    tDualityLie InfoGeometry.Orthogonal.O55Contact.contactEuler =
      -InfoGeometry.Orthogonal.O55Contact.contactEuler :=
  ⟨anomaly_minusTwo_bracket_plusTwo_eq_contactEuler,
   tDualityLie_swaps_anomaly_generators.1,
   tDualityLie_swaps_anomaly_generators.2,
   tDualityLie_contactEuler⟩

end BridgeD

/-! ## 5. Master Cross-Clade Quantum Yang–Mills Synthesis -/

section MasterCrossCladeSynthesis

open InfoGeometry.Geometry.AssociativeGaugeConnection
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.YangMillsOrbitGramian
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.KreinSpaceBRSTUnitarityBridge
open InfoGeometry.Canonical.AnomalyHigherGradeTDualityExtension

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [StarRing A] [Algebra R A]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- **Master Cross-Clade Quantum Yang–Mills Bridge Theorem**:
Coagulates all four cross-clade bridges (Bridges A, B, C, and D) into one theorem. -/
theorem quantum_yang_mills_cross_clade_master_synthesis
    {P a : A} (hP : P * P = P) (hPs : star P = P) (has : star a = a)
    {q b_fermion G_fp : Module.End R M} {k : ℕ}
    (hq2 : q.comp q = 0)
    (hD : IsDrazinInverse (brstFaddeevPopovLaplacian q b_fermion) G_fp k)
    (u da db : FaradayYangMillsChernSimons.ColorVec3 R) :
    ((∀ X : A,
       peirceCovariantDeriv P a a X =
         innerDerivative (R := R) P X + innerDerivative (R := R) (genPhi P a a) X) ∧
     peirceFundamentalConnection R P a a (peirceFundamentalConnection R P a a 1) =
       peirceMaurerCartanCurvature P a a ∧
     orbitMassMode P a = genV P a a ∧
     peirceCovariantDeriv P a a (orbitMassMode P a) = 0) ∧
    (G_fp * q = q * G_fp ∧
     q * drazinBRSTHomotopy b_fermion G_fp + drazinBRSTHomotopy b_fermion G_fp * q =
       projection (brstFaddeevPopovLaplacian q b_fermion) G_fp ∧
     ∀ ψ : LinearMap.ker q,
       let L_fp := brstFaddeevPopovLaplacian q b_fermion
       let hClosed := drazin_regular_component_exact_on_physical_state hq2 hD ψ.2
       Submodule.Quotient.mk (p := LinearMap.range (brstExactToClosed q hq2))
         ⟨projection L_fp G_fp ψ.1, hClosed.2.1⟩ =
         (Submodule.Quotient.mk 0 : brstCohomologyModule q hq2) ∧
       Submodule.Quotient.mk (p := LinearMap.range (brstExactToClosed q hq2))
         ⟨complementaryProjection L_fp G_fp ψ.1, hClosed.2.2.1⟩ =
         (Submodule.Quotient.mk (p := LinearMap.range (brstExactToClosed q hq2)) ψ :
           brstCohomologyModule q hq2)) ∧
    (FaradayYangMillsChernSimons.SplitOctonion.faradayYangMillsCurvature u da db =
       FaradayYangMillsChernSimons.SplitOctonion.add
         (FaradayYangMillsChernSimons.SplitOctonion.scale 2
           (splitOctonionFaradayToGGEquiv.symm
             (GunaydinGursey.SplitOctonion.associator
               (GunaydinGursey.SplitOctonion.quark (colorVec3FaradayToGGEquiv u))
               (GunaydinGursey.SplitOctonion.quark (colorVec3FaradayToGGEquiv da))
               (GunaydinGursey.SplitOctonion.quark (colorVec3FaradayToGGEquiv db)))))
         (FaradayYangMillsChernSimons.SplitOctonion.scale
           (-2 * FaradayYangMillsChernSimons.ColorVec3.det3 u da db)
           (FaradayYangMillsChernSimons.SplitOctonion.quark u)) ∧
     SeibergWitten.SplitOctonion.J
         (splitOctonionFaradayToSWEquiv
           (FaradayYangMillsChernSimons.SplitOctonion.faradayYangMillsCurvature u da db)) =
       SeibergWitten.SplitOctonion.scale
         (2 * FaradayYangMillsChernSimons.ColorVec3.det3 u da db)
         (SeibergWitten.SplitOctonion.add SeibergWitten.SplitOctonion.paraSymplecticK0
           (SeibergWitten.SplitOctonion.antiquark (colorVec3FaradayToSWEquiv u)))) ∧
    (⁅anomalyGeneratorMinusTwo, anomalyGeneratorPlusTwo⁆ =
       InfoGeometry.Orthogonal.O55Contact.contactEuler ∧
     tDualityLie anomalyGeneratorPlusTwo = anomalyGeneratorMinusTwo ∧
     tDualityLie anomalyGeneratorMinusTwo = anomalyGeneratorPlusTwo ∧
     tDualityLie InfoGeometry.Orthogonal.O55Contact.contactEuler =
       -InfoGeometry.Orthogonal.O55Contact.contactEuler) := by
  have hA := orbitMassMode_bianchi_and_corner_gramians hP hPs has
  have hB_comm := (drazin_propagator_and_projections_commute_with_q hq2 hD).1
  have hB_hom := drazinBRSTHomotopy_anticomm_eq_projection hq2 hD
  have hC := faraday_monopole_baryon_associator_seiberg_witten_bridge u da db
  refine ⟨⟨fun X => peirceCovariantDeriv_eq_innerDerivative_sum P a a X,
           (peirceFundamentalConnection_sq_one (R := R) hP a a).1,
           orbitMassMode_eq_genV hP hPs has,
           hA.2.2.1⟩,
          ⟨hB_comm, hB_hom, fun ψ =>
            brstCohomology_decomposes_via_complementary_drazin_projection hq2 hD ψ⟩,
          hC,
          anomaly_higher_grade_to_tduality_bridge⟩

end MasterCrossCladeSynthesis

end InfoGeometry.Canonical.QuantumYangMillsCrossCladeBridges

end
