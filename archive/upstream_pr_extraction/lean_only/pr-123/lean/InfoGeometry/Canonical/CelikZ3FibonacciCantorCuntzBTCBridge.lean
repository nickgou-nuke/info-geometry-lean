import InfoGeometry.Canonical.CantorCuntzBasis
import InfoGeometry.Canonical.FibonacciParafermionAtoms
import InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
import InfoGeometry.Canonical.Z3GrassmannDifferentialCalculus
import InfoGeometry.Categorical.FibonacciBraiding

open InfoGeometry.Topology

/-!
# Çelik Z3 / Fibonacci / Cantor-Cuntz BTC bridge

This module is a theorem-safe bridge interface.

It does not identify Salih Çelik's `Z3`-graded Cartan/differential calculus
with Fibonacci anyons by definitional equality.  Instead it records the exact
data needed for such an identification:

* a `Z3` quantum-plane and cubic differential calculus;
* Cartan readback data, stated as explicit operators and a formula;
* a local two-channel Yang--Baxter matrix owner;
* a finite Fibonacci braided-tensor-category shadow with fusion and `F/R/B`
  matrices;
* a multiplicative transport from the local `Z3` matrix owner into the
  Fibonacci matrix shadow;
* a Cantor/Cuntz null-boundary crystal readout.

The main closed theorem is `fibonacci_yang_baxter_from_celik`: once the
transport maps the local Çelik `R/B` pair to the Fibonacci `R/B` pair, the
Fibonacci Artin/Yang--Baxter relation follows by multiplicative transport.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Canonical.CelikZ3FibonacciCantorCuntzBTCBridge

open Matrix
open InfoGeometry.Canonical.Z3GrassmannDifferentialCalculus
open InfoGeometry.Canonical.FibonacciParafermionAtoms
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding

/-! ## 1. Çelik Z3 Cartan/Yang--Baxter theorems -/

theorem cartan_formula
    {A : Type*} [Ring A]
    (calculus : Z3DifferentialCalculus A)
    (contraction lieDerivative : A → A)
    (hCartan :
      ∀ x : A, lieDerivative x = calculus.d (contraction x) + contraction (calculus.d x))
    (x : A) :
    lieDerivative x = calculus.d (contraction x) + contraction (calculus.d x) :=
  hCartan x

theorem concreteZ3_yang_baxter :
    z3RMatrix * z3BMatrix * z3RMatrix = z3BMatrix * z3RMatrix * z3BMatrix :=
  z3_R_B_R_eq_B_R_B

/-! ## 2. Finite Fibonacci braided tensor matrix theorems -/

/- The finite Fibonacci data is kept as direct theorem arguments.  The
categorical owner in `InfoGeometry.Categorical.FibonacciBraiding` supplies the
matrix identities; this file adds only the bridge hypotheses and conclusions.
-/

theorem fibonacci_self_fusion_rule :
    FibonacciCharge.fusion FibonacciCharge.eps FibonacciCharge.eps =
      {FibonacciCharge.one, FibonacciCharge.eps} := by
  rfl

/-- The finite Fibonacci fusion matrix squares to the identity. -/
theorem fibonacci_fusion_matrix_sq
    (tau sqrtTau : ℂ)
    (sqrt_sq : sqrtTau ^ 2 = tau)
    (tau_sq_add_tau : tau ^ 2 + tau = 1) :
    fibonacciFusionMatrix tau sqrtTau * fibonacciFusionMatrix tau sqrtTau = 1 :=
  InfoGeometry.Categorical.FibonacciBraiding.F_sq tau sqrtTau sqrt_sq tau_sq_add_tau

/-- The finite Fibonacci fusion matrix has determinant `-1`. -/
theorem fibonacci_fusion_matrix_det
    (tau sqrtTau : ℂ)
    (sqrt_sq : sqrtTau ^ 2 = tau)
    (tau_sq_add_tau : tau ^ 2 + tau = 1) :
    (fibonacciFusionMatrix tau sqrtTau).det = -1 :=
  InfoGeometry.Categorical.FibonacciBraiding.det_F tau sqrtTau sqrt_sq tau_sq_add_tau

/-- The middle braid generator is the `F R F` conjugate in the supplied shadow. -/
theorem fibonacci_B_eq_FRF (q : Units ℂ) (tau sqrtTau : ℂ) :
    fibonacciBMatrix q tau sqrtTau =
      fibonacciFusionMatrix tau sqrtTau * fibonacciRMatrix q *
        fibonacciFusionMatrix tau sqrtTau :=
  InfoGeometry.Categorical.FibonacciBraiding.B_eq_FRF q tau sqrtTau

/-! ## 3. Multiplicative braid-matrix transport -/

/--
Transport of the local Çelik `Z3` Yang--Baxter relation to the Fibonacci
braided-tensor shadow.
-/
theorem transports_yang_baxter
    (localR localB : Matrix (Fin 2) (Fin 2) ℝ)
    (local_yang_baxter : localR * localB * localR = localB * localR * localB)
    (q : Units ℂ) (tau sqrtTau : ℂ)
    (map : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (map_mul :
      ∀ X Y : Matrix (Fin 2) (Fin 2) ℝ, map (X * Y) = map X * map Y)
    (maps_R : map localR = fibonacciRMatrix q)
    (maps_B : map localB = fibonacciBMatrix q tau sqrtTau) :
    fibonacciRMatrix q * fibonacciBMatrix q tau sqrtTau * fibonacciRMatrix q =
      fibonacciBMatrix q tau sqrtTau * fibonacciRMatrix q * fibonacciBMatrix q tau sqrtTau := by
  calc
    fibonacciRMatrix q * fibonacciBMatrix q tau sqrtTau * fibonacciRMatrix q
        = map localR * map localB * map localR := by
            rw [← maps_R, ← maps_B]
    _ = map (localR * localB * localR) := by
            rw [← map_mul localR localB,
              ← map_mul (localR * localB) localR]
    _ = map (localB * localR * localB) := by
            rw [local_yang_baxter]
    _ = map localB * map localR * map localB := by
            rw [map_mul (localB * localR) localB,
              map_mul localB localR]
    _ = fibonacciBMatrix q tau sqrtTau * fibonacciRMatrix q * fibonacciBMatrix q tau sqrtTau := by
            rw [maps_R, maps_B]

/-! ## 4. Direct BTC transport theorems -/

/-- Fibonacci Artin/Yang--Baxter follows from direct multiplicative transport. -/
theorem fibonacci_yang_baxter_from_celik
    (localR localB : Matrix (Fin 2) (Fin 2) ℝ)
    (local_yang_baxter : localR * localB * localR = localB * localR * localB)
    (q : Units ℂ) (tau sqrtTau : ℂ)
    (map : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (map_mul :
      ∀ X Y : Matrix (Fin 2) (Fin 2) ℝ, map (X * Y) = map X * map Y)
    (maps_R : map localR = fibonacciRMatrix q)
    (maps_B : map localB = fibonacciBMatrix q tau sqrtTau) :
    fibonacciRMatrix q * fibonacciBMatrix q tau sqrtTau * fibonacciRMatrix q =
      fibonacciBMatrix q tau sqrtTau * fibonacciRMatrix q * fibonacciBMatrix q tau sqrtTau :=
  transports_yang_baxter localR localB local_yang_baxter q tau sqrtTau
    map map_mul maps_R maps_B

/--
The finite Fibonacci hexagon/Yang--Baxter matrix shadow obtained from the
transported Çelik `Z3` Yang--Baxter owner.
-/
theorem finite_hexagon_shadow_from_celik
    (localR localB : Matrix (Fin 2) (Fin 2) ℝ)
    (local_yang_baxter : localR * localB * localR = localB * localR * localB)
    (q : Units ℂ) (tau sqrtTau : ℂ)
    (sqrt_sq : sqrtTau ^ 2 = tau)
    (tau_sq_add_tau : tau ^ 2 + tau = 1)
    (map : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (map_mul :
      ∀ X Y : Matrix (Fin 2) (Fin 2) ℝ, map (X * Y) = map X * map Y)
    (maps_R : map localR = fibonacciRMatrix q)
    (maps_B : map localB = fibonacciBMatrix q tau sqrtTau) :
    fibonacciFusionMatrix tau sqrtTau * fibonacciFusionMatrix tau sqrtTau = 1
      ∧ (fibonacciFusionMatrix tau sqrtTau).det = -1
      ∧ fibonacciBMatrix q tau sqrtTau =
          fibonacciFusionMatrix tau sqrtTau * fibonacciRMatrix q *
            fibonacciFusionMatrix tau sqrtTau
      ∧ fibonacciRMatrix q * fibonacciBMatrix q tau sqrtTau * fibonacciRMatrix q =
          fibonacciBMatrix q tau sqrtTau * fibonacciRMatrix q *
            fibonacciBMatrix q tau sqrtTau := by
  have hArtin :
      fibonacciRMatrix q * fibonacciBMatrix q tau sqrtTau * fibonacciRMatrix q =
          fibonacciBMatrix q tau sqrtTau * fibonacciRMatrix q * fibonacciBMatrix q tau sqrtTau := by
    exact fibonacci_yang_baxter_from_celik localR localB local_yang_baxter
      q tau sqrtTau map map_mul maps_R maps_B
  exact ⟨
    InfoGeometry.Categorical.FibonacciBraiding.F_sq tau sqrtTau sqrt_sq tau_sq_add_tau,
    InfoGeometry.Categorical.FibonacciBraiding.det_F tau sqrtTau sqrt_sq tau_sq_add_tau,
    InfoGeometry.Categorical.FibonacciBraiding.B_eq_FRF q tau sqrtTau,
    hArtin⟩

/-! ## 5. Cantor/Cuntz crystal at the null boundary -/

variable {Op : Type*} [Ring Op] [StarRing Op]

/-- The null-boundary orbit is the Cuntz/Cantor seed. -/
theorem orbit_null_eq_seed
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (seed : Op)
    (nullBoundary : List Bool)
    (nullBoundary_eq_root : nullBoundary = []) :
    InfoGeometry.Canonical.CantorCuntzBasis.orbit
        C seed nullBoundary = seed := by
  rw [nullBoundary_eq_root]
  exact CantorCuntzBasis.orbit_root_eq_seed C seed

/-! ## 6. Combined Çelik--Fibonacci--Cantor/Cuntz bridge -/

variable {Op : Type*} [Ring Op] [StarRing Op]

/-- The combined bridge inherits the transported Fibonacci Yang--Baxter relation. -/
theorem fibonacci_yang_baxter
    (localR localB : Matrix (Fin 2) (Fin 2) ℝ)
    (local_yang_baxter : localR * localB * localR = localB * localR * localB)
    (q : Units ℂ) (tau sqrtTau : ℂ)
    (map : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (map_mul :
      ∀ X Y : Matrix (Fin 2) (Fin 2) ℝ, map (X * Y) = map X * map Y)
    (maps_R : map localR = fibonacciRMatrix q)
    (maps_B : map localB = fibonacciBMatrix q tau sqrtTau) :
    fibonacciRMatrix q * fibonacciBMatrix q tau sqrtTau * fibonacciRMatrix q =
      fibonacciBMatrix q tau sqrtTau * fibonacciRMatrix q * fibonacciBMatrix q tau sqrtTau :=
  fibonacci_yang_baxter_from_celik localR localB local_yang_baxter
    q tau sqrtTau map map_mul maps_R maps_B

/-- The combined bridge reads the null Cantor/Cuntz boundary as the seed crystal. -/
theorem null_boundary_orbit_eq_seed
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (seed : Op)
    (nullBoundary : List Bool)
    (nullBoundary_eq_root : nullBoundary = []) :
    InfoGeometry.Canonical.CantorCuntzBasis.orbit
        C seed nullBoundary = seed :=
  orbit_null_eq_seed C seed nullBoundary nullBoundary_eq_root

end InfoGeometry.Canonical.CelikZ3FibonacciCantorCuntzBTCBridge
