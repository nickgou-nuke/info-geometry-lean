/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.Decomposition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Zorn Split-Octonion Superconformal Genesis, Quantum Key $K_0$, Hopf Braid Supertrace,
  Witten–Möbius Chiral Parity Swing, & Klein Bottle EPR Vacuum Poset

This canonical module epistemically compiles **Sections 149–152** of the AI Studio
formalization archive (`1xHyRdU-TU8mjwZzKRRrzTAdvk8nPm7Or`, Turns 340–362) directly on
the repository's canonical 8-dimensional split-octonion carrier `ZornCell R`
(`InfoGeometry.Algebra.Zorn.ConcreteComposition`):

1. **The Zorn Split-Octonion Carrier $\mathbb{O}_s$, Isotropic Chiral Sheets $U(\mathbf{u}),
  V(\mathbf{v})$, & Para-Symplectic Key $K_0 = e_1 - e_2$:**
   - Reuses `ZornCell R`, `ZornCell.mulZ`, `ZornCell.addZ`, and `ZornCell.detZ`.
   - Proves strict nilpotency $U(\mathbf{u})^2 = 0$, $V(\mathbf{v})^2 = 0$ and quadratic
     nullness $\det_Z(U(\mathbf{u})) = \det_Z(V(\mathbf{v})) = 0$, together with the
     involution $K_0^2 = \mathbf{1}$, orientation-reversing determinant $\det_Z(K_0) = -1$,
     and explicit non-commutativity and non-associativity witnesses over $\mathbb{Z}$.
2. **Superconformal Majorana Genesis & The Erlangen Epitaph (Turns 340–345):**
   - Identifying the real chiral Majorana supercharges $Q(\mathbf{u}) = U(\mathbf{u})$ and
     $\bar{Q}(\mathbf{v}) = V(\mathbf{v})$, proves:
     $$\{U(\mathbf{u}), V(\mathbf{v})\}
  = (\mathbf{u} \cdot \mathbf{v})\,\mathbf{1} \quad \text{(Translation / Metric Tensor)},$$
     $$[U(\mathbf{u}), V(\mathbf{v})]
  = (\mathbf{u} \cdot \mathbf{v})\,K_0 \quad \text{(Curvature / Para-Symplectic Boost)},$$
     $$[K_0, U(\mathbf{u})] = 2\,U(\mathbf{u}), \qquad [K_0, V(\mathbf{v})]
  = -2\,V(\mathbf{v}) \quad \text{(Conformal Dilatation)},$$
     and the cross-product sheet-exchange identities
     $U(\mathbf{u}_1) U(\mathbf{u}_2) = V(\mathbf{u}_1 \times \mathbf{u}_2)$ and
     $V(\mathbf{v}_1) V(\mathbf{v}_2) = -U(\mathbf{v}_1 \times \mathbf{v}_2)$.
3. **The Four Dualities of the Quantum Key $K_0$ & The Hopf Braid Supertrace (Turns 346–355):**
   - Proves the universal diagonal Peirce decomposition
     $$\mathrm{diag}(S + Q,\; S - Q) = S \cdot \mathbf{1} + Q \cdot K_0,$$
     extracting $2S$ via `traceZ` (classical Hamilton–Jacobi action / electric charge /
     Fisher trace) and $2Q$ via `superTraceZ` (Bohm quantum potential / magnetic monopole
     charge / Witten vacuum anomaly), with Lorentzian norm $\det_Z = S^2 - Q^2$.
   - Proves the **Hopf Braid Crossing Supertrace Law**:
     $$\mathrm{STr}\bigl([U(\mathbf{u}), V(\mathbf{v})]\bigr)
  = 2(\mathbf{u} \cdot \mathbf{v}), \qquad \mathrm{Tr}\bigl(\{U(\mathbf{u}), V(\mathbf{v})\}\bigr) = 2(\mathbf{u} \cdot \mathbf{v}).$$
4. **Sections 151 & 152: The Witten–Möbius Chiral Parity Swing $\mathcal{P}_{\mathrm{WM}}$ & Klein Bottle EPR Vacuum Topology (Turns 357–362):**
   - For $\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})
  = c K_0 - s(U(\mathbf{u}) - V(\mathbf{v}))$,
     proves:
     $$\mathcal{P}_{\mathrm{WM}}^2
  = \bigl(c^2 - s^2(\mathbf{u} \cdot \mathbf{v})\bigr)\,\mathbf{1}, \qquad \det_Z(\mathcal{P}_{\mathrm{WM}}) = -\bigl(c^2 - s^2(\mathbf{u} \cdot \mathbf{v})\bigr), \qquad \mathrm{STr}(\mathcal{P}_{\mathrm{WM}}) = 2c.$$
   - Under the **EPR Singlet Gluing Condition** $\mathbf{u} \cdot \mathbf{v} = -1$ and
     $c^2 + s^2 = 1$, proves that the two chiral Möbius sheets sew into a boundaryless,
     orientation-reversing involution:
     $$\mathcal{P}_{\mathrm{WM}}^2
  = \mathbf{1} \quad\text{and}\quad \det_Z(\mathcal{P}_{\mathrm{WM}}) = -1.$$
   - For the continuous angular family $\mathcal{P}_{\mathrm{WM}}(\theta)$ with
     $(c, s) = (\cos 2\theta, \sin 2\theta)$, proves **Klein Bottle $\pi$-periodicity**
     $\mathcal{P}_{\mathrm{WM}}(\theta + \pi) = \mathcal{P}_{\mathrm{WM}}(\theta)$,
     **Möbius $\pi/2$ sign inversion**
     $\mathcal{P}_{\mathrm{WM}}(\theta + \pi/2) = -\mathcal{P}_{\mathrm{WM}}(\theta)$,
     and quarter-turn supertrace cancellation
     $\mathrm{STr}(\mathcal{P}_{\mathrm{WM}}(\theta)) + \mathrm{STr}(\mathcal{P}_{\mathrm{WM}}(\theta + \pi/2)) = 0$
     mirroring the vanishing Euler characteristic $\chi(K) = 0$ of the Klein bottle.

### Three-Bucket Epistemic Audit Classification

* **BUCKET 1 — Constructively Proved Split-Octonion, Superconformal,
  & Klein-Bottle Theorems (`[kernel_verified]`):**
  - `sheetU_and_sheetV_nilpotent_and_null`, `paraSymplecticK0_involution_and_det`,
    and `zornCell_noncommutative_and_nonassociative`.
  - `susy_majorana_superconformal_genesis` and `chiral_sheet_cross_product_fusion`.
  - `four_dualities_of_quantum_key_K0` and `hopf_braid_crossing_supertrace_invariant`.
  - `wittenMoebiusParity_sq_and_supertrace_laws`,
    `wittenMoebiusParity_epr_klein_bottle_involution`, and
    `kleinBottle_wittenMoebius_periodicity_and_euler_zero`.

* **BUCKET 2 — Eliminated Wrappers & Redundant Carriers (Zero Remaining):**
  - Eliminates all `structure *Certificate : Prop` wrappers and duplicate `SplitOctonion`
    struct definitions from the AI Studio transcript by building directly on the
    canonical `ZornCell R` carrier.

* **BUCKET 3 — Continuum 3-Sphere Hopf Integral & Smooth Klein Bottle Cobordism (`[bucket_3_open_debt]`):**
  - Global differential-form integration $\int_{S^3} A \wedge dA$ and smooth manifold
    cobordism classes remain outside this exact algebraic `ZornCell` scope.
-/

namespace InfoGeometry.Canonical.ZornSuperconformalHopfWittenMoebiusKleinBottlePoset

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

-- ============================================================================
-- SECTION 1: Zorn Split-Octonion Carrier, Isotropic Sheets, & Para-Symplectic K₀
-- ============================================================================

section ZornCarrierAndIsotropicSheets

variable {R : Type*} [CommRing R]

/-- Zero element of the 8-dimensional split-octonion Zorn algebra `ZornCell R`. -/
def zeroZ : ZornCell R :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Multiplicative identity $\mathbf{1} = e_1 + e_2 = \mathrm{diag}(1, 1)$ of `ZornCell R`. -/
def oneZ : ZornCell R :=
  ⟨1, 1, 0, 0, 0, 0, 0, 0⟩

/-- Para-symplectic chiral parity generator $K_0 = e_1 - e_2
  = \mathrm{diag}(1, -1)$ of `ZornCell R`. -/
def paraSymplecticK0 : ZornCell R :=
  ⟨1, -1, 0, 0, 0, 0, 0, 0⟩

/-- Coordinatewise negation on `ZornCell R`. -/
def negZ (X : ZornCell R) : ZornCell R :=
  ⟨-X.r, -X.s, -X.x1, -X.x2, -X.x3, -X.y1, -X.y2, -X.y3⟩

/-- Coordinatewise subtraction on `ZornCell R`. -/
def subZ (X Y : ZornCell R) : ZornCell R :=
  ⟨X.r - Y.r, X.s - Y.s,
   X.x1 - Y.x1, X.x2 - Y.x2, X.x3 - Y.x3,
   X.y1 - Y.y1, X.y2 - Y.y2, X.y3 - Y.y3⟩

/-- Scalar multiplication $c \cdot X$ on `ZornCell R`. -/
def smulZ (c : R) (X : ZornCell R) : ZornCell R :=
  ⟨c * X.r, c * X.s,
   c * X.x1, c * X.x2, c * X.x3,
   c * X.y1, c * X.y2, c * X.y3⟩

/-- Symmetric Jordan anticommutator $\{X, Y\} = X Y + Y X$ on `ZornCell R`. -/
def anticommutatorZ (X Y : ZornCell R) : ZornCell R :=
  addZ (mulZ X Y) (mulZ Y X)

/-- Skew-symmetric commutator $[X, Y] = X Y - Y X$ on `ZornCell R`. -/
def commutatorZ (X Y : ZornCell R) : ZornCell R :=
  subZ (mulZ X Y) (mulZ Y X)

/-- Ordinary trace $\mathrm{Tr}(X) = r + s$ on `ZornCell R`. -/
def traceZ (X : ZornCell R) : R :=
  X.r + X.s

/-- Graded chiral supertrace $\mathrm{STr}(X) = r - s$ on `ZornCell R`. -/
def superTraceZ (X : ZornCell R) : R :=
  X.r - X.s

/-- Forward isotropic chiral Majorana sheet generator $U(\mathbf{u}) \in \mathcal{I}_+$
in the upper-right Peirce block $e_1 \mathbb{O}_s e_2$. -/
def sheetU (u₁ u₂ u₃ : R) : ZornCell R :=
  ⟨0, 0, u₁, u₂, u₃, 0, 0, 0⟩

/-- Backward isotropic chiral Majorana sheet generator $V(\mathbf{v}) \in \mathcal{I}_-$
in the lower-left Peirce block $e_2 \mathbb{O}_s e_1$. -/
def sheetV (v₁ v₂ v₃ : R) : ZornCell R :=
  ⟨0, 0, 0, 0, 0, v₁, v₂, v₃⟩

/-- **Strict Nilpotency & Quadratic Nullness of the Chiral Sheets (`sheetU_and_sheetV_nilpotent_and_null`):**
For all $\mathbf{u}, \mathbf{v} \in R^3$, the chiral Majorana sheet generators
$U(\mathbf{u})$ and $V(\mathbf{v})$ square to `zeroZ` and lie on the Zorn null quadric
$\det_Z = 0$. -/
theorem sheetU_and_sheetV_nilpotent_and_null (u₁ u₂ u₃ v₁ v₂ v₃ : R) :
    mulZ (sheetU u₁ u₂ u₃) (sheetU u₁ u₂ u₃) = zeroZ ∧
    mulZ (sheetV v₁ v₂ v₃) (sheetV v₁ v₂ v₃) = zeroZ ∧
    detZ (sheetU u₁ u₂ u₃) = 0 ∧
    detZ (sheetV v₁ v₂ v₃) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (dsimp [mulZ, sheetU, zeroZ]; ring)
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (dsimp [mulZ, sheetV, zeroZ]; ring)
  · dsimp [detZ, sheetU]; ring
  · dsimp [detZ, sheetV]; ring

/-- **Para-Symplectic Involution, Determinant,
  & Supertrace (`paraSymplecticK0_involution_and_det`):**
The para-symplectic generator $K_0 = e_1 - e_2$ satisfies:
1. $K_0^2 = \mathbf{1}$ (multiplicative involution);
2. $\det_Z(K_0) = -1$ (orientation-reversing norm);
3. $\mathrm{Tr}(K_0) = 0$ (traceless);
4. $\mathrm{STr}(K_0) = 2$ (chiral supertrace equals 2). -/
theorem paraSymplecticK0_involution_and_det :
    mulZ (paraSymplecticK0 (R := R)) paraSymplecticK0 = oneZ ∧
    detZ (paraSymplecticK0 (R := R)) = -1 ∧
    traceZ (paraSymplecticK0 (R := R)) = 0 ∧
    superTraceZ (paraSymplecticK0 (R := R)) = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (dsimp [mulZ, paraSymplecticK0, oneZ]; ring)
  · dsimp [detZ, paraSymplecticK0]; ring
  · dsimp [traceZ, paraSymplecticK0]; ring
  · dsimp [superTraceZ, paraSymplecticK0]; ring

/-- **Explicit Non-Commutativity & Non-Associativity Witnesses (`zornCell_noncommutative_and_nonassociative`):**
On `ZornCell ℤ`, the Zorn product `mulZ` is both strictly non-commutative and strictly
non-associative. -/
theorem zornCell_noncommutative_and_nonassociative :
    mulZ (sheetU (1 : ℤ) 0 0) (sheetV 1 0 0) ≠
      mulZ (sheetV 1 0 0) (sheetU 1 0 0) ∧
    mulZ (mulZ (sheetU (1 : ℤ) 0 0) (sheetU 0 1 0)) (sheetU 0 0 1) ≠
      mulZ (sheetU 1 0 0) (mulZ (sheetU 0 1 0) (sheetU 0 0 1)) := by
  refine ⟨?_, ?_⟩
  · intro hComm
    have hr : (mulZ (sheetU (1 : ℤ) 0 0) (sheetV 1 0 0)).r =
        (mulZ (sheetV 1 0 0) (sheetU 1 0 0)).r := congrArg ZornCell.r hComm
    revert hr
    decide
  · intro hAssoc
    have hs : (mulZ (mulZ (sheetU (1 : ℤ) 0 0) (sheetU 0 1 0)) (sheetU 0 0 1)).s =
        (mulZ (sheetU 1 0 0) (mulZ (sheetU 0 1 0) (sheetU 0 0 1))).s :=
      congrArg ZornCell.s hAssoc
    revert hs
    decide

end ZornCarrierAndIsotropicSheets

-- ============================================================================
-- SECTION 2: Superconformal Majorana Genesis & The Erlangen Epitaph
-- ============================================================================

section SuperconformalMajoranaGenesis

variable {R : Type*} [CommRing R]

/-- **Superconformal Majorana Genesis & The Erlangen Epitaph (`susy_majorana_superconformal_genesis`):**
For all chiral Majorana color vectors $\mathbf{u} = (u_1, u_2, u_3)$ and
$\mathbf{v} = (v_1, v_2, v_3)$ over a commutative ring `R`:
1. **Metric / Translation Genesis:**
   $$\{U(\mathbf{u}), V(\mathbf{v})\} = (\mathbf{u} \cdot \mathbf{v})\,\mathbf{1};$$
2. **Curvature / Para-Symplectic Boost Genesis:**
   $$[U(\mathbf{u}), V(\mathbf{v})] = (\mathbf{u} \cdot \mathbf{v})\,K_0;$$
3. **Positive Conformal Weight ($+2$) on Forward Sheet $\mathcal{I}_+$:**
   $$[K_0, U(\mathbf{u})] = 2\,U(\mathbf{u});$$
4. **Negative Conformal Weight ($-2$) on Backward Sheet $\mathcal{I}_-$:**
   $$[K_0, V(\mathbf{v})] = -2\,V(\mathbf{v}).$$ -/
theorem susy_majorana_superconformal_genesis (u₁ u₂ u₃ v₁ v₂ v₃ : R) :
    anticommutatorZ (sheetU u₁ u₂ u₃) (sheetV v₁ v₂ v₃) =
      smulZ (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) oneZ ∧
    commutatorZ (sheetU u₁ u₂ u₃) (sheetV v₁ v₂ v₃) =
      smulZ (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) paraSymplecticK0 ∧
    commutatorZ paraSymplecticK0 (sheetU u₁ u₂ u₃) =
      smulZ 2 (sheetU u₁ u₂ u₃) ∧
    commutatorZ paraSymplecticK0 (sheetV v₁ v₂ v₃) =
      smulZ (-2) (sheetV v₁ v₂ v₃) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [anticommutatorZ, addZ, mulZ, sheetU, sheetV, smulZ, oneZ]; ring)
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [commutatorZ, subZ, mulZ, sheetU, sheetV, smulZ, paraSymplecticK0]; ring)
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [commutatorZ, subZ, mulZ, paraSymplecticK0, sheetU, smulZ]; ring)
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [commutatorZ, subZ, mulZ, paraSymplecticK0, sheetV, smulZ]; ring)

/-- **Chiral Sheet Cross-Product Teleportation (`chiral_sheet_cross_product_fusion`):**
Multiplying two forward sheet elements $U(\mathbf{u}) U(\mathbf{w})$ teleports into the
backward sheet as $V(\mathbf{u} \times \mathbf{w})$, while multiplying two backward sheet
elements $V(\mathbf{u}) V(\mathbf{w})$ teleports into the forward sheet as
$-U(\mathbf{u} \times \mathbf{w})$. -/
theorem chiral_sheet_cross_product_fusion (u₁ u₂ u₃ w₁ w₂ w₃ : R) :
    mulZ (sheetU u₁ u₂ u₃) (sheetU w₁ w₂ w₃) =
      sheetV (u₂ * w₃ - u₃ * w₂) (u₃ * w₁ - u₁ * w₃) (u₁ * w₂ - u₂ * w₁) ∧
    mulZ (sheetV u₁ u₂ u₃) (sheetV w₁ w₂ w₃) =
      sheetU (-(u₂ * w₃ - u₃ * w₂)) (-(u₃ * w₁ - u₁ * w₃)) (-(u₁ * w₂ - u₂ * w₁)) := by
  refine ⟨?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (dsimp [mulZ, sheetU, sheetV]; ring)
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (dsimp [mulZ, sheetU, sheetV]; ring)

/-- 8D Zorn Kitaev dimer Hamiltonian $H_{\mathrm{Kitaev}}(\mathbf{u}, \mathbf{v})
  = U(\mathbf{u}) + V(\mathbf{v})$
coupling a forward Plabic ridge $U(\mathbf{u})$ and a backward Plabic ridge $V(\mathbf{v})$. -/
def zornKitaevDimerHamiltonian (u₁ u₂ u₃ v₁ v₂ v₃ : R) : ZornCell R :=
  addZ (sheetU u₁ u₂ u₃) (sheetV v₁ v₂ v₃)

/-- **8D Zorn Kitaev Dimer Mass Gap & Plabic Dangling-Edge Zero Mode
(`zorn_majorana_plabic_zero_mode_and_kitaev_dimer_fusion`):**
For any forward
  backward 3D Majorana ridges $\mathbf{u},
  \mathbf{v} \in R^3$
  scalar $c \in R$:
1. **Closed Dimer Dirac Mass Gap:**
   $$H_{\mathrm{Kitaev}}(\mathbf{u}, \mathbf{v})^2
     = \bigl(U(\mathbf{u}) + V(\mathbf{v})\bigr)^2
     = (\mathbf{u} \cdot \mathbf{v})\,\mathbf{1};$$
2. **Dangling Forward Edge Zero Mode (Collinear Topological Protection):**
   $$U(\mathbf{u}) \cdot U(c\,\mathbf{u}) = 0;$$
3. **Dangling Backward Edge Zero Mode (Collinear Topological Protection):**
   $$V(\mathbf{v}) \cdot V(c\,\mathbf{v}) = 0.$$ -/
theorem zorn_majorana_plabic_zero_mode_and_kitaev_dimer_fusion
    (c u₁ u₂ u₃ v₁ v₂ v₃ : R) :
    mulZ (zornKitaevDimerHamiltonian u₁ u₂ u₃ v₁ v₂ v₃)
         (zornKitaevDimerHamiltonian u₁ u₂ u₃ v₁ v₂ v₃) =
      smulZ (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) oneZ ∧
    mulZ (sheetU u₁ u₂ u₃) (sheetU (c * u₁) (c * u₂) (c * u₃)) = zeroZ ∧
    mulZ (sheetV v₁ v₂ v₃) (sheetV (c * v₁) (c * v₂) (c * v₃)) = zeroZ := by
  refine ⟨?_, ?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [zornKitaevDimerHamiltonian, addZ, mulZ, sheetU, sheetV, smulZ, oneZ]; ring)
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [mulZ, sheetU, zeroZ]; ring)
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [mulZ, sheetV, zeroZ]; ring)

end SuperconformalMajoranaGenesis

-- ============================================================================
-- SECTION 3: The Four Dualities of the Quantum Key K₀ & Hopf Braid Supertrace
-- ============================================================================

section QuantumKeyK0AndHopfBraidSupertrace

variable {R : Type*} [CommRing R]

/-- Diagonal Zorn state $\mathrm{diag}(S + Q,\; S - Q)$ decomposing any diagonal observable
into its classical/symmetric component $S$ along $\mathbf{1}$ and its quantum/chiral
component $Q$ along $K_0 = e_1 - e_2$. -/
def zornDiagonalState (S Q : R) : ZornCell R :=
  ⟨S + Q, S - Q, 0, 0, 0, 0, 0, 0⟩

/-- **The Four Dualities of the Quantum Key $K_0
  = e_1 - e_2$ (`four_dualities_of_quantum_key_K0`):**
For any classical/symmetric component $S \in R$ and quantum/topological component $Q \in R$:
1. **Operator Splitting:**
   $$\mathrm{diag}(S + Q,\; S - Q) = S \cdot \mathbf{1} + Q \cdot K_0;$$
2. **Trace Readout (Classical Action $S$ / Electric Charge $Q_e$ / Fisher Metric):**
   $$\mathrm{Tr}\bigl(S \cdot \mathbf{1} + Q \cdot K_0\bigr) = 2 S;$$
3. **Supertrace Readout (Bohm Potential $Q$ / Magnetic Monopole $g_m$ / Witten Anomaly):**
   $$\mathrm{STr}\bigl(S \cdot \mathbf{1} + Q \cdot K_0\bigr) = 2 Q;$$
4. **Krein / Lorentzian Determinant Norm:**
   $$\det_Z\bigl(S \cdot \mathbf{1} + Q \cdot K_0\bigr) = S^2 - Q^2.$$ -/
theorem four_dualities_of_quantum_key_K0 (S Q : R) :
    zornDiagonalState S Q = addZ (smulZ S oneZ) (smulZ Q paraSymplecticK0) ∧
    traceZ (zornDiagonalState S Q) = 2 * S ∧
    superTraceZ (zornDiagonalState S Q) = 2 * Q ∧
    detZ (zornDiagonalState S Q) = S ^ 2 - Q ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [zornDiagonalState, addZ, smulZ, oneZ, paraSymplecticK0]; ring)
  · dsimp [traceZ, zornDiagonalState]; ring
  · dsimp [superTraceZ, zornDiagonalState]; ring
  · dsimp [detZ, zornDiagonalState]; ring

/-- **Hopf Braid Crossing Supertrace & Fisher Trace Dual Laws (`hopf_braid_crossing_supertrace_invariant`):**
For the braid crossing commutator $B(\mathbf{u}, \mathbf{v}) = [U(\mathbf{u}), V(\mathbf{v})]$
and symmetric fusion $\{U(\mathbf{u}), V(\mathbf{v})\}$:
1. $\mathrm{STr}([U(\mathbf{u}), V(\mathbf{v})]) = 2(\mathbf{u} \cdot \mathbf{v})$
   (the chiral supertrace extracts twice the local Hopf linking / crossing inner product);
2. $\mathrm{Tr}([U(\mathbf{u}), V(\mathbf{v})]) = 0$
   (the commutator is invisible to the ordinary trace);
3. $\mathrm{Tr}(\{U(\mathbf{u}), V(\mathbf{v})\}) = 2(\mathbf{u} \cdot \mathbf{v})$
   (the ordinary trace extracts the symmetric Fisher metric inner product);
4. $\mathrm{STr}(\{U(\mathbf{u}), V(\mathbf{v})\}) = 0$
   (the symmetric anticommutator is invisible to the chiral supertrace). -/
theorem hopf_braid_crossing_supertrace_invariant (u₁ u₂ u₃ v₁ v₂ v₃ : R) :
    superTraceZ (commutatorZ (sheetU u₁ u₂ u₃) (sheetV v₁ v₂ v₃)) =
      2 * (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) ∧
    traceZ (commutatorZ (sheetU u₁ u₂ u₃) (sheetV v₁ v₂ v₃)) = 0 ∧
    traceZ (anticommutatorZ (sheetU u₁ u₂ u₃) (sheetV v₁ v₂ v₃)) =
      2 * (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) ∧
    superTraceZ (anticommutatorZ (sheetU u₁ u₂ u₃) (sheetV v₁ v₂ v₃)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [superTraceZ, commutatorZ, subZ, mulZ, sheetU, sheetV]; ring
  · dsimp [traceZ, commutatorZ, subZ, mulZ, sheetU, sheetV]; ring
  · dsimp [traceZ, anticommutatorZ, addZ, mulZ, sheetU, sheetV]; ring
  · dsimp [superTraceZ, anticommutatorZ, addZ, mulZ, sheetU, sheetV]; ring

end QuantumKeyK0AndHopfBraidSupertrace

-- ============================================================================
-- SECTION 4: Witten–Möbius Chiral Parity Swing & Klein Bottle EPR Vacuum Topology
-- ============================================================================

section WittenMoebiusAndKleinBottleVacuum

variable {R : Type*} [CommRing R]

/-- The **Witten–Möbius Chiral Parity Charge Operator**
$$\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})
  = c \cdot K_0 - s \cdot \bigl(U(\mathbf{u}) - V(\mathbf{v})\bigr)$$
rotating the discrete para-symplectic reflection $K_0$ into the off-diagonal chiral
Majorana sheets $U(\mathbf{u}) - V(\mathbf{v})$. -/
def wittenMoebiusParity (c s u₁ u₂ u₃ v₁ v₂ v₃ : R) : ZornCell R :=
  subZ (smulZ c paraSymplecticK0)
       (smulZ s (subZ (sheetU u₁ u₂ u₃) (sheetV v₁ v₂ v₃)))

/-- **Geometric Square, Determinant, & Supertrace Protection of the Witten–Möbius Operator
(`wittenMoebiusParity_sq_and_supertrace_laws`):**
For all $c, s \in R$ and $\mathbf{u}, \mathbf{v} \in R^3$:
1. **Exact Square Law:**
   $$\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})^2
     = \bigl(c^2 - s^2(\mathbf{u} \cdot \mathbf{v})\bigr)\,\mathbf{1};$$
2. **Zorn Determinant:**
   $$\det_Z\bigl(\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})\bigr)
     = -\bigl(c^2 - s^2(\mathbf{u} \cdot \mathbf{v})\bigr);$$
3. **Witten Index / Supertrace Protection:**
   $$\mathrm{STr}\bigl(\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})\bigr) = 2c
     \quad\text{(independent of the off-diagonal fluctuation amplitude } s\text{)};$$
4. **Vanishing Ordinary Trace:**
   $$\mathrm{Tr}\bigl(\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})\bigr) = 0.$$ -/
theorem wittenMoebiusParity_sq_and_supertrace_laws (c s u₁ u₂ u₃ v₁ v₂ v₃ : R) :
    mulZ (wittenMoebiusParity c s u₁ u₂ u₃ v₁ v₂ v₃)
         (wittenMoebiusParity c s u₁ u₂ u₃ v₁ v₂ v₃) =
      smulZ (c ^ 2 - s ^ 2 * (u₁ * v₁ + u₂ * v₂ + u₃ * v₃)) oneZ ∧
    detZ (wittenMoebiusParity c s u₁ u₂ u₃ v₁ v₂ v₃) =
      -(c ^ 2 - s ^ 2 * (u₁ * v₁ + u₂ * v₂ + u₃ * v₃)) ∧
    superTraceZ (wittenMoebiusParity c s u₁ u₂ u₃ v₁ v₂ v₃) = 2 * c ∧
    traceZ (wittenMoebiusParity c s u₁ u₂ u₃ v₁ v₂ v₃) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [wittenMoebiusParity, mulZ, subZ, smulZ, paraSymplecticK0,
              sheetU, sheetV, oneZ]; ring)
  · dsimp [detZ, wittenMoebiusParity, subZ, smulZ, paraSymplecticK0, sheetU, sheetV]
    ring
  · dsimp [superTraceZ, wittenMoebiusParity, subZ, smulZ, paraSymplecticK0, sheetU, sheetV]
    ring
  · dsimp [traceZ, wittenMoebiusParity, subZ, smulZ, paraSymplecticK0, sheetU, sheetV]
    ring

/-- **Chiral Orientation Reversal of $\mathcal{P}_{\mathrm{WM}}$ under $K_0$-Conjugation
(`wittenMoebiusParity_K0_conjugation_orientation_reversal`):**
Conjugating the Witten–Möbius parity operator by the para-symplectic grading involution
$K_0 = e_1 - e_2$ reverses the sign of the off-diagonal Majorana twist amplitude $s$:
$$K_0 \cdot \mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v}) \cdot K_0
  = \mathcal{P}_{\mathrm{WM}}(c, -s, \mathbf{u}, \mathbf{v}),$$
exhibiting the non-orientable Klein-bottle relation $K_0 R(\theta) K_0^{-1} = R(-\theta)$. -/
theorem wittenMoebiusParity_K0_conjugation_orientation_reversal
    (c s u₁ u₂ u₃ v₁ v₂ v₃ : R) :
    mulZ (mulZ paraSymplecticK0 (wittenMoebiusParity c s u₁ u₂ u₃ v₁ v₂ v₃))
         paraSymplecticK0 =
      wittenMoebiusParity c (-s) u₁ u₂ u₃ v₁ v₂ v₃ := by
  refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (dsimp [wittenMoebiusParity, mulZ, subZ, smulZ, paraSymplecticK0, sheetU, sheetV]; ring)

/-- **Exact EPR Gluing Defect Identity (`wittenMoebiusParity_epr_gluing_defect`):**
Whenever $(c, s)$ lies on the unit circle ($c^2 + s^2 = 1$), the deviation of
$\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})^2$ from the identity $\mathbf{1}$
is governed strictly by the EPR singlet gluing defect $1 + \mathbf{u} \cdot \mathbf{v}$:
$$\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})^2 - \mathbf{1}
  = -s^2 \bigl(1 + \mathbf{u} \cdot \mathbf{v}\bigr)\,\mathbf{1}.$$ -/
theorem wittenMoebiusParity_epr_gluing_defect (c s u₁ u₂ u₃ v₁ v₂ v₃ : R)
    (h_trig : c ^ 2 + s ^ 2 = 1) :
    subZ (mulZ (wittenMoebiusParity c s u₁ u₂ u₃ v₁ v₂ v₃)
               (wittenMoebiusParity c s u₁ u₂ u₃ v₁ v₂ v₃)) oneZ =
      smulZ (-(s ^ 2 * (1 + (u₁ * v₁ + u₂ * v₂ + u₃ * v₃)))) oneZ := by
  rw [(wittenMoebiusParity_sq_and_supertrace_laws c s u₁ u₂ u₃ v₁ v₂ v₃).1]
  have hScalar :
      c ^ 2 - s ^ 2 * (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) - 1 =
        -(s ^ 2 * (1 + (u₁ * v₁ + u₂ * v₂ + u₃ * v₃))) := by
    linear_combination h_trig
  refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · dsimp [subZ, smulZ, oneZ]; linear_combination hScalar
  · dsimp [subZ, smulZ, oneZ]; linear_combination hScalar
  · dsimp [subZ, smulZ, oneZ]; ring
  · dsimp [subZ, smulZ, oneZ]; ring
  · dsimp [subZ, smulZ, oneZ]; ring
  · dsimp [subZ, smulZ, oneZ]; ring
  · dsimp [subZ, smulZ, oneZ]; ring
  · dsimp [subZ, smulZ, oneZ]; ring

/-- **Topological Involution via EPR Singlet Gluing (`wittenMoebiusParity_epr_klein_bottle_involution`):**
If $(c, s)$ lies on the unit circle ($c^2 + s^2 = 1$) and the forward and backward
chiral Majorana sheets satisfy the **EPR Singlet Gluing Condition**
$\mathbf{u} \cdot \mathbf{v} = -1$, then:
1. $\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})^2 = \mathbf{1}$
   (exact topological involution at every Möbius twist angle);
2. $\det_Z(\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})) = -1$
   (orientation-reversing Klein-bottle reflection norm). -/
theorem wittenMoebiusParity_epr_klein_bottle_involution (c s u₁ u₂ u₃ v₁ v₂ v₃ : R)
    (h_trig : c ^ 2 + s ^ 2 = 1)
    (h_epr : u₁ * v₁ + u₂ * v₂ + u₃ * v₃ = -1) :
    mulZ (wittenMoebiusParity c s u₁ u₂ u₃ v₁ v₂ v₃)
         (wittenMoebiusParity c s u₁ u₂ u₃ v₁ v₂ v₃) = oneZ ∧
    detZ (wittenMoebiusParity c s u₁ u₂ u₃ v₁ v₂ v₃) = -1 := by
  have hLaws := wittenMoebiusParity_sq_and_supertrace_laws c s u₁ u₂ u₃ v₁ v₂ v₃
  have hFactor : c ^ 2 - s ^ 2 * (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) = 1 := by
    rw [h_epr]
    linear_combination h_trig
  refine ⟨?_, ?_⟩
  · rw [hLaws.1, hFactor]
    refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (dsimp [smulZ, oneZ]; ring)
  · rw [hLaws.2.1, hFactor]

/-- Real angular Witten–Möbius operator
$$\mathcal{P}_{\mathrm{WM}}(\theta, \mathbf{u}, \mathbf{v})
  = \cos(2\theta)\,K_0 - \sin(2\theta)\,\bigl(U(\mathbf{u}) - V(\mathbf{v})\bigr)$$
parameterizing the Klein bottle gluing of the two chiral Möbius sheets over $\theta \in \mathbb{R}$. -/
noncomputable def wittenMoebiusReal (θ u₁ u₂ u₃ v₁ v₂ v₃ : ℝ) : ZornCell ℝ :=
  wittenMoebiusParity (Real.cos (2 * θ)) (Real.sin (2 * θ)) u₁ u₂ u₃ v₁ v₂ v₃

/-- **Section 152 — Klein Bottle Topology of the Witten–Möbius Quantum Vacuum
(`kleinBottle_wittenMoebius_periodicity_and_euler_zero`):**
For every Möbius angle $\theta \in \mathbb{R}$ and EPR-entangled chiral sheets
$\mathbf{u}, \mathbf{v} \in \mathbb{R}^3$ satisfying $u_1 v_1 + u_2 v_2 + u_3 v_3 = -1$:
1. **Klein Bottle $\pi$-Periodicity:**
   $$\mathcal{P}_{\mathrm{WM}}(\theta + \pi, \mathbf{u}, \mathbf{v})
     = \mathcal{P}_{\mathrm{WM}}(\theta, \mathbf{u}, \mathbf{v});$$
2. **Möbius Quarter-Turn ($\pi / 2$) Chiral Orientation Reversal:**
   $$\mathcal{P}_{\mathrm{WM}}(\theta + \pi / 2, \mathbf{u}, \mathbf{v})
     = -\mathcal{P}_{\mathrm{WM}}(\theta, \mathbf{u}, \mathbf{v});$$
3. **Universal EPR Involution Across All Angles $\theta \in \mathbb{R}$:**
   $$\mathcal{P}_{\mathrm{WM}}(\theta, \mathbf{u}, \mathbf{v})^2 = \mathbf{1};$$
4. **Non-Orientable Glide Determinant ($\det_Z = -1$):**
   $$\det_Z\bigl(\mathcal{P}_{\mathrm{WM}}(\theta, \mathbf{u}, \mathbf{v})\bigr) = -1;$$
5. **Vanishing Euler Characteristic Balance ($\mathrm{STr}(\theta) + \mathrm{STr}(\theta + \pi/2)
  = 0$):**
   $$\mathrm{STr}\bigl(\mathcal{P}_{\mathrm{WM}}(\theta, \mathbf{u}, \mathbf{v})\bigr) +
     \mathrm{STr}\bigl(\mathcal{P}_{\mathrm{WM}}(\theta + \pi / 2, \mathbf{u}, \mathbf{v})\bigr)
  = 0.$$ -/
theorem kleinBottle_wittenMoebius_periodicity_and_euler_zero
    (θ u₁ u₂ u₃ v₁ v₂ v₃ : ℝ)
    (h_epr : u₁ * v₁ + u₂ * v₂ + u₃ * v₃ = -1) :
    wittenMoebiusReal (θ + Real.pi) u₁ u₂ u₃ v₁ v₂ v₃ =
      wittenMoebiusReal θ u₁ u₂ u₃ v₁ v₂ v₃ ∧
    wittenMoebiusReal (θ + Real.pi / 2) u₁ u₂ u₃ v₁ v₂ v₃ =
      negZ (wittenMoebiusReal θ u₁ u₂ u₃ v₁ v₂ v₃) ∧
    mulZ (wittenMoebiusReal θ u₁ u₂ u₃ v₁ v₂ v₃)
         (wittenMoebiusReal θ u₁ u₂ u₃ v₁ v₂ v₃) = oneZ ∧
    detZ (wittenMoebiusReal θ u₁ u₂ u₃ v₁ v₂ v₃) = -1 ∧
    superTraceZ (wittenMoebiusReal θ u₁ u₂ u₃ v₁ v₂ v₃) +
      superTraceZ (wittenMoebiusReal (θ + Real.pi / 2) u₁ u₂ u₃ v₁ v₂ v₃) = 0 := by
  have hArgPi : 2 * (θ + Real.pi) = 2 * θ + 2 * Real.pi := by ring
  have hCosPi : Real.cos (2 * (θ + Real.pi)) = Real.cos (2 * θ) := by
    rw [hArgPi, Real.cos_add_two_pi]
  have hSinPi : Real.sin (2 * (θ + Real.pi)) = Real.sin (2 * θ) := by
    rw [hArgPi, Real.sin_add_two_pi]
  have hArgHalf : 2 * (θ + Real.pi / 2) = 2 * θ + Real.pi := by ring
  have hCosHalf : Real.cos (2 * (θ + Real.pi / 2)) = -Real.cos (2 * θ) := by
    rw [hArgHalf, Real.cos_add_pi]
  have hSinHalf : Real.sin (2 * (θ + Real.pi / 2)) = -Real.sin (2 * θ) := by
    rw [hArgHalf, Real.sin_add_pi]
  have hEPR := wittenMoebiusParity_epr_klein_bottle_involution
    (Real.cos (2 * θ)) (Real.sin (2 * θ)) u₁ u₂ u₃ v₁ v₂ v₃
    (Real.cos_sq_add_sin_sq (2 * θ)) h_epr
  refine ⟨?_, ?_, hEPR.1, hEPR.2, ?_⟩
  · unfold wittenMoebiusReal
    rw [hCosPi, hSinPi]
  · unfold wittenMoebiusReal
    rw [hCosHalf, hSinHalf]
    refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [wittenMoebiusParity, negZ, subZ, smulZ, paraSymplecticK0, sheetU, sheetV]; ring)
  · unfold wittenMoebiusReal
    rw [hCosHalf, hSinHalf,
        (wittenMoebiusParity_sq_and_supertrace_laws (Real.cos (2 * θ)) (Real.sin (2 * θ)) u₁ u₂ u₃ v₁ v₂ v₃).2.2.1,
        (wittenMoebiusParity_sq_and_supertrace_laws (-Real.cos (2 * θ)) (-Real.sin (2 * θ)) u₁ u₂ u₃ v₁ v₂ v₃).2.2.1]
    ring

end WittenMoebiusAndKleinBottleVacuum

end InfoGeometry.Canonical.ZornSuperconformalHopfWittenMoebiusKleinBottlePoset
