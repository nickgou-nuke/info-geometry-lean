/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.Decomposition
import Mathlib.Tactic.Ring

/-!
# Faraday–Yang–Mills Monopole Curvature & Chern–Simons Hopf Fiber Invariant

Target: `InfoGeometry/Superalgebra/FaradayYangMillsChernSimonsHopf.lean`

Epistemically compiled from AI Studio archive `1xHyRdU-TU8mjwZzKRRrzTAdvk8nPm7Or`
(Section 135, Turn 274) directly on the canonical 8-dimensional split-octonion carrier
`ZornCell R` (`InfoGeometry.Algebra.Zorn.ConcreteComposition`):

1. **Double Vector Cross-Product Identity for Hopf Torsion:**
   $$(\mathbf{u} \times \mathbf{a}) \times (\mathbf{u} \times \mathbf{b})
     = \det_3(\mathbf{u}, \mathbf{a}, \mathbf{b})\,\mathbf{u}.$$
2. **Maurer–Cartan Form $\omega_L(\mathbf{u}, \mathbf{a}) = U(\mathbf{a}) - V(\mathbf{u}\times\mathbf{a})$
   & Faraday–Yang–Mills Monopole Reduction:**
   - The commutator $[\omega_L(\mathbf{u}, \mathbf{a}), \omega_L(\mathbf{u}, \mathbf{b})]$
     splits into $+2\,V(\mathbf{a}\times\mathbf{b})$ plus the radial monopole term
     $-2\det_3(\mathbf{u}, \mathbf{a}, \mathbf{b})\,(K_0 + U(\mathbf{u}))$.
   - Combining with $d\omega_L(\mathbf{a}, \mathbf{b}) = -2\,V(\mathbf{a}\times\mathbf{b})$
     cancels the flat backward-sheet torsion and leaves the pure radial monopole curvature:
     $$\mathcal{F}_{\mathrm{YM}}(\mathbf{u}, \mathbf{a}, \mathbf{b})
       = -2\det_3(\mathbf{u}, \mathbf{a}, \mathbf{b})\,(K_0 + U(\mathbf{u})).$$
3. **Berry–Faraday Supertrace Charge & Chern–Simons 3-Form Conservation:**
   - $\mathrm{Tr}(\mathcal{F}_{\mathrm{YM}}) = 0$ and
     $\mathrm{STr}(\mathcal{F}_{\mathrm{YM}}) = -4\det_3(\mathbf{u}, \mathbf{a}, \mathbf{b})$.
   - $\mathrm{CS}_3(\mathbf{u}, \mathbf{a}, \mathbf{b}, \mathbf{c})
     := \mathrm{Tr}(\mathcal{F}_{\mathrm{YM}}\,\omega_L(\mathbf{u}, \mathbf{c})^\dagger)
     = -2\det_3(\mathbf{u}, \mathbf{a}, \mathbf{b})\,(\mathbf{u}\cdot\mathbf{c})$,
     which vanishes identically for every tangential displacement $\mathbf{u}\cdot\mathbf{c} = 0$.

### Three-Bucket Epistemic Audit Classification

* **BUCKET 1 — Constructively Proved Monopole & Chern–Simons Theorems (`[kernel_verified]`):**
  - `maurer_cartan_commutator_and_faraday_monopole_reduction`.
  - `faraday_yang_mills_traces_and_sq`.
  - `chern_simons_explicit_formula_and_sphere_conservation` and
    `faradayYangMills_zorn_noncommutative`.

* **BUCKET 2 — Eliminated Duplicate Carriers & Certificate Wrappers (Zero Remaining):**
  - Eliminates the raw transcript's duplicate `SplitOctonion` carrier and
    `FaradayYangMillsChernSimonsCertificate : Prop` wrapper in favor of `ZornCell R`.

* **BUCKET 3 — Global Principal Bundle Cohomology (`[bucket_3_open_debt]`):**
  - Global Čech/de Rham cohomology classes on principal $SU(2)$-bundles over $S^4$
    remain outside this algebraic `ZornCell R` scope.
-/

namespace InfoGeometry.Superalgebra.FaradayYangMillsChernSimons

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

variable {R : Type*} [CommRing R]

/-- Multiplicative identity $\mathbf{1} = \mathrm{diag}(1, 1)$ in `ZornCell R`. -/
def oneZ : ZornCell R :=
  ⟨1, 1, 0, 0, 0, 0, 0, 0⟩

/-- Para-symplectic chiral parity generator $K_0 = \mathrm{diag}(1, -1)$ in `ZornCell R`. -/
def paraSymplecticK0 : ZornCell R :=
  ⟨1, -1, 0, 0, 0, 0, 0, 0⟩

/-- Coordinatewise subtraction on `ZornCell R`. -/
def subZ (X Y : ZornCell R) : ZornCell R :=
  ⟨X.r - Y.r, X.s - Y.s,
   X.x1 - Y.x1, X.x2 - Y.x2, X.x3 - Y.x3,
   X.y1 - Y.y1, X.y2 - Y.y2, X.y3 - Y.y3⟩

/-- Scalar multiplication $k \cdot X$ on `ZornCell R`. -/
def smulZ (k : R) (X : ZornCell R) : ZornCell R :=
  ⟨k * X.r, k * X.s,
   k * X.x1, k * X.x2, k * X.x3,
   k * X.y1, k * X.y2, k * X.y3⟩

/-- Sheet-exchange involution $X^\dagger$ on `ZornCell R`. -/
def daggerZ (X : ZornCell R) : ZornCell R :=
  ⟨X.r, X.s, X.y1, X.y2, X.y3, X.x1, X.x2, X.x3⟩

/-- Skew-symmetric commutator $[X, Y] = X Y - Y X$ on `ZornCell R`. -/
def commutatorZ (X Y : ZornCell R) : ZornCell R :=
  subZ (mulZ X Y) (mulZ Y X)

/-- Ordinary trace $\mathrm{Tr}(X) = r + s$ on `ZornCell R`. -/
def traceZ (X : ZornCell R) : R :=
  X.r + X.s

/-- Graded chiral supertrace $\mathrm{STr}(X) = r - s$ on `ZornCell R`. -/
def superTraceZ (X : ZornCell R) : R :=
  X.r - X.s

/-- Forward isotropic chiral sheet $U(\mathbf{u})$ in `ZornCell R`. -/
def sheetU (u₁ u₂ u₃ : R) : ZornCell R :=
  ⟨0, 0, u₁, u₂, u₃, 0, 0, 0⟩

/-- Backward isotropic chiral sheet $V(\mathbf{v})$ in `ZornCell R`. -/
def sheetV (v₁ v₂ v₃ : R) : ZornCell R :=
  ⟨0, 0, 0, 0, 0, v₁, v₂, v₃⟩

/-- Oriented scalar triple product $\det_3(\mathbf{u}, \mathbf{a}, \mathbf{b}) = \mathbf{u}\cdot(\mathbf{a}\times\mathbf{b})$. -/
def det3R (u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ : R) : R :=
  u₁ * (a₂ * b₃ - a₃ * b₂) + u₂ * (a₃ * b₁ - a₁ * b₃) + u₃ * (a₁ * b₂ - a₂ * b₁)

/-- Maurer–Cartan 1-form $\omega_L(\mathbf{u}, \mathbf{a}) = U(\mathbf{a}) - V(\mathbf{u}\times\mathbf{a})$. -/
def maurerCartanForm (u₁ u₂ u₃ a₁ a₂ a₃ : R) : ZornCell R :=
  ⟨0, 0, a₁, a₂, a₃,
   -(u₂ * a₃ - u₃ * a₂), -(u₃ * a₁ - u₁ * a₃), -(u₁ * a₂ - u₂ * a₁)⟩

/-- Exterior differential $d\omega_L(\mathbf{a}, \mathbf{b}) = -2\,V(\mathbf{a}\times\mathbf{b})$. -/
def exteriorDiffMaurerCartan (a₁ a₂ a₃ b₁ b₂ b₃ : R) : ZornCell R :=
  smulZ (-2) (sheetV (a₂ * b₃ - a₃ * b₂) (a₃ * b₁ - a₁ * b₃) (a₁ * b₂ - a₂ * b₁))

/-- Full 2-form Faraday–Yang–Mills field strength
$\mathcal{F}_{\mathrm{YM}}(\mathbf{u}, \mathbf{a}, \mathbf{b}) = d\omega_L(\mathbf{a}, \mathbf{b}) + [\omega_L(\mathbf{u}, \mathbf{a}), \omega_L(\mathbf{u}, \mathbf{b})]$. -/
def faradayYangMillsCurvature (u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ : R) : ZornCell R :=
  addZ (exteriorDiffMaurerCartan a₁ a₂ a₃ b₁ b₂ b₃)
       (commutatorZ (maurerCartanForm u₁ u₂ u₃ a₁ a₂ a₃)
                    (maurerCartanForm u₁ u₂ u₃ b₁ b₂ b₃))

/-- Chern–Simons 3-form $\mathrm{CS}_3(\mathbf{u}, \mathbf{a}, \mathbf{b}, \mathbf{c}) = \mathrm{Tr}(\mathcal{F}_{\mathrm{YM}}\,\omega_L(\mathbf{u}, \mathbf{c})^\dagger)$. -/
def chernSimons3Form (u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ : R) : R :=
  traceZ (mulZ (faradayYangMillsCurvature u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃)
               (daggerZ (maurerCartanForm u₁ u₂ u₃ c₁ c₂ c₃)))

/-- **Maurer–Cartan Commutator & Faraday–Yang–Mills Monopole Reduction
(`maurer_cartan_commutator_and_faraday_monopole_reduction`):**
1. $[\omega_L(\mathbf{u}, \mathbf{a}), \omega_L(\mathbf{u}, \mathbf{b})]
   = 2\,V(\mathbf{a}\times\mathbf{b}) - 2\det_3(\mathbf{u}, \mathbf{a}, \mathbf{b})\,(K_0 + U(\mathbf{u}))$;
2. $\mathcal{F}_{\mathrm{YM}}(\mathbf{u}, \mathbf{a}, \mathbf{b})
   = -2\det_3(\mathbf{u}, \mathbf{a}, \mathbf{b})\,(K_0 + U(\mathbf{u}))$. -/
theorem maurer_cartan_commutator_and_faraday_monopole_reduction
    (u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ : R) :
    commutatorZ (maurerCartanForm u₁ u₂ u₃ a₁ a₂ a₃)
                (maurerCartanForm u₁ u₂ u₃ b₁ b₂ b₃) =
      addZ (smulZ 2 (sheetV (a₂ * b₃ - a₃ * b₂) (a₃ * b₁ - a₁ * b₃) (a₁ * b₂ - a₂ * b₁)))
           (smulZ (-2 * det3R u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃)
                  (addZ paraSymplecticK0 (sheetU u₁ u₂ u₃))) ∧
    faradayYangMillsCurvature u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ =
      smulZ (-2 * det3R u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃)
            (addZ paraSymplecticK0 (sheetU u₁ u₂ u₃)) := by
  refine ⟨?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [commutatorZ, subZ, mulZ, maurerCartanForm, addZ, smulZ, sheetU, sheetV,
              paraSymplecticK0, det3R]; ring)
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [faradayYangMillsCurvature, exteriorDiffMaurerCartan, commutatorZ, subZ, mulZ,
              maurerCartanForm, addZ, smulZ, sheetU, sheetV, paraSymplecticK0, det3R]; ring)

/-- **Berry–Faraday Supertrace Charge & Quadratic Law (`faraday_yang_mills_traces_and_sq`):**
1. $\mathrm{Tr}(\mathcal{F}_{\mathrm{YM}}) = 0$;
2. $\mathrm{STr}(\mathcal{F}_{\mathrm{YM}}) = -4\det_3(\mathbf{u}, \mathbf{a}, \mathbf{b})$;
3. $\mathcal{F}_{\mathrm{YM}}^2 = 4\det_3(\mathbf{u}, \mathbf{a}, \mathbf{b})^2\,(\mathbf{1} + U(\mathbf{u}))$. -/
theorem faraday_yang_mills_traces_and_sq
    (u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ : R) :
    traceZ (faradayYangMillsCurvature u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃) = 0 ∧
    superTraceZ (faradayYangMillsCurvature u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃) =
      -4 * det3R u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ ∧
    mulZ (faradayYangMillsCurvature u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃)
         (faradayYangMillsCurvature u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃) =
      smulZ (4 * det3R u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ * det3R u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃)
            (addZ oneZ (sheetU u₁ u₂ u₃)) := by
  rw [(maurer_cartan_commutator_and_faraday_monopole_reduction u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃).2]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [traceZ, smulZ, addZ, paraSymplecticK0, sheetU]; ring
  · dsimp [superTraceZ, smulZ, addZ, paraSymplecticK0, sheetU]; ring
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [mulZ, smulZ, addZ, paraSymplecticK0, sheetU, oneZ]; ring)

/-- **Chern–Simons 3-Form Formula & Hopf Sphere Conservation
(`chern_simons_explicit_formula_and_sphere_conservation`):**
1. $\mathrm{CS}_3(\mathbf{u}, \mathbf{a}, \mathbf{b}, \mathbf{c})
   = -2\det_3(\mathbf{u}, \mathbf{a}, \mathbf{b})\,(\mathbf{u}\cdot\mathbf{c})$;
2. Whenever $\mathbf{u}\cdot\mathbf{c} = 0$ (tangential displacement along $S^2$),
   $\mathrm{CS}_3(\mathbf{u}, \mathbf{a}, \mathbf{b}, \mathbf{c}) = 0$. -/
theorem chern_simons_explicit_formula_and_sphere_conservation
    (u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ : R) :
    chernSimons3Form u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ =
      -2 * det3R u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ * (u₁ * c₁ + u₂ * c₂ + u₃ * c₃) ∧
    (u₁ * c₁ + u₂ * c₂ + u₃ * c₃ = 0 →
      chernSimons3Form u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ = 0) := by
  have h_cs :
      chernSimons3Form u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ =
        -2 * det3R u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃ * (u₁ * c₁ + u₂ * c₂ + u₃ * c₃) := by
    dsimp [chernSimons3Form]
    rw [(maurer_cartan_commutator_and_faraday_monopole_reduction u₁ u₂ u₃ a₁ a₂ a₃ b₁ b₂ b₃).2]
    dsimp [traceZ, mulZ, smulZ, addZ, paraSymplecticK0, sheetU, daggerZ, maurerCartanForm]
    ring
  refine ⟨h_cs, ?_⟩
  intro h_tan
  rw [h_cs, h_tan, mul_zero]

/-- Explicit non-commutativity witness on `ZornCell ℤ` for Maurer–Cartan forms. -/
theorem faradayYangMills_zorn_noncommutative :
    mulZ (maurerCartanForm (1 : ℤ) 0 0 0 1 0) (maurerCartanForm 1 0 0 0 0 1) ≠
      mulZ (maurerCartanForm (1 : ℤ) 0 0 0 0 1) (maurerCartanForm 1 0 0 0 1 0) := by
  intro h
  have hr := congrArg ZornCell.r h
  revert hr
  decide

end InfoGeometry.Superalgebra.FaradayYangMillsChernSimons
