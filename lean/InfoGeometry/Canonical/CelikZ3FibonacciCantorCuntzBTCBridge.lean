import InfoGeometry.Canonical.CantorCuntzBasis
import InfoGeometry.Canonical.FibonacciParafermionAtoms
import InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
import InfoGeometry.Canonical.Z3GrassmannDifferentialCalculus
import InfoGeometry.Categorical.FibonacciBraiding

/-!
# Çelik Z3 / Fibonacci / Cantor-Cuntz BTC bridge

This module is a theorem-safe bridge socket.

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

/-! ## 1. Çelik Z3 Cartan/Yang--Baxter socket -/

/--
A theorem-safe socket for Salih Çelik-style `Z3` Cartan/Yang--Baxter data.

The `plane` and `calculus` fields come from
`Z3GrassmannDifferentialCalculus`.  The Cartan layer is deliberately explicit:
a contraction, a Lie derivative, and the formula connecting them.  The
Yang--Baxter layer is the local two-channel matrix pair whose braid relation is
proved or supplied by an owner theorem.
-/
structure CelikZ3CartanYangBaxterCalculus (A : Type*) [Ring A] where
  plane : Z3QuantumPlane A
  calculus : Z3DifferentialCalculus A
  contraction : A → A
  lieDerivative : A → A
  cartan_formula :
    ∀ x : A, lieDerivative x = calculus.d (contraction x) + contraction (calculus.d x)
  localR : Matrix (Fin 2) (Fin 2) ℝ
  localB : Matrix (Fin 2) (Fin 2) ℝ
  local_yang_baxter : localR * localB * localR = localB * localR * localB

namespace CelikZ3CartanYangBaxterCalculus

variable {A : Type*} [Ring A]

/--
Concrete `Z3` matrix owner socket.

This constructor uses the no-premise real `Z3` Artin/Yang--Baxter owner from
`FibonacciParafermionAtoms`, while keeping the Cartan/differential calculus as
explicit input data.
-/
def concreteZ3
    (plane : Z3QuantumPlane A)
    (calculus : Z3DifferentialCalculus A)
    (contraction lieDerivative : A → A)
    (hCartan :
      ∀ x : A, lieDerivative x = calculus.d (contraction x) + contraction (calculus.d x)) :
    CelikZ3CartanYangBaxterCalculus A where
  plane := plane
  calculus := calculus
  contraction := contraction
  lieDerivative := lieDerivative
  cartan_formula := hCartan
  localR := z3RMatrix
  localB := z3BMatrix
  local_yang_baxter := z3_R_B_R_eq_B_R_B

@[simp]
theorem concreteZ3_localR
    (plane : Z3QuantumPlane A)
    (calculus : Z3DifferentialCalculus A)
    (contraction lieDerivative : A → A)
    (hCartan :
      ∀ x : A, lieDerivative x = calculus.d (contraction x) + contraction (calculus.d x)) :
    (concreteZ3 plane calculus contraction lieDerivative hCartan).localR = z3RMatrix :=
  rfl

@[simp]
theorem concreteZ3_localB
    (plane : Z3QuantumPlane A)
    (calculus : Z3DifferentialCalculus A)
    (contraction lieDerivative : A → A)
    (hCartan :
      ∀ x : A, lieDerivative x = calculus.d (contraction x) + contraction (calculus.d x)) :
    (concreteZ3 plane calculus contraction lieDerivative hCartan).localB = z3BMatrix :=
  rfl

end CelikZ3CartanYangBaxterCalculus

/-! ## 2. Finite Fibonacci braided tensor category shadow -/

/--
Finite braided-tensor-category shadow for Fibonacci anyon braiding.

The tensor product is represented by the finite fusion-output function on
`FibonacciCharge`; the associator/braiding readout is represented by the
two-channel `F/R/B` matrix surface.  This is intentionally not a
`BraidedCategory` instance.
-/
structure FibonacciBraidedTensorCategoryShadow where
  q : Units ℂ
  tau : ℂ
  sqrtTau : ℂ
  sqrt_sq : sqrtTau ^ 2 = tau
  tau_sq_add_tau : tau ^ 2 + tau = 1
  R : Matrix (Fin 2) (Fin 2) ℂ
  B : Matrix (Fin 2) (Fin 2) ℂ
  R_eq : R = fibonacciRMatrix q
  B_eq : B = fibonacciBMatrix q tau sqrtTau
  fusion_rule :
    FibonacciCharge.fusion FibonacciCharge.eps FibonacciCharge.eps =
      {FibonacciCharge.one, FibonacciCharge.eps}

namespace FibonacciBraidedTensorCategoryShadow

/-- The intrinsic finite Fibonacci self-fusion rule. -/
theorem self_fusion_rule (F : FibonacciBraidedTensorCategoryShadow) :
    FibonacciCharge.fusion FibonacciCharge.eps FibonacciCharge.eps =
      {FibonacciCharge.one, FibonacciCharge.eps} :=
  F.fusion_rule

/-- The finite Fibonacci fusion matrix squares to the identity. -/
theorem fusion_matrix_sq (F : FibonacciBraidedTensorCategoryShadow) :
    fibonacciFusionMatrix F.tau F.sqrtTau * fibonacciFusionMatrix F.tau F.sqrtTau = 1 :=
  fibonacciFusionMatrix_sq F.sqrt_sq F.tau_sq_add_tau

/-- The finite Fibonacci fusion matrix has determinant `-1`. -/
theorem fusion_matrix_det (F : FibonacciBraidedTensorCategoryShadow) :
    (fibonacciFusionMatrix F.tau F.sqrtTau).det = -1 :=
  det_fibonacciFusionMatrix F.sqrt_sq F.tau_sq_add_tau

/-- The middle braid generator is the `F R F` conjugate in the supplied shadow. -/
theorem B_eq_FRF (F : FibonacciBraidedTensorCategoryShadow) :
    F.B =
      fibonacciFusionMatrix F.tau F.sqrtTau * F.R *
        fibonacciFusionMatrix F.tau F.sqrtTau := by
  calc
    F.B = fibonacciBMatrix F.q F.tau F.sqrtTau := F.B_eq
    _ = fibonacciFusionMatrix F.tau F.sqrtTau * fibonacciRMatrix F.q *
          fibonacciFusionMatrix F.tau F.sqrtTau := rfl
    _ = fibonacciFusionMatrix F.tau F.sqrtTau * F.R *
          fibonacciFusionMatrix F.tau F.sqrtTau := by
            rw [← F.R_eq]

end FibonacciBraidedTensorCategoryShadow

/-! ## 3. Multiplicative braid-matrix transport -/

/--
A multiplicative transport from the local real `Z3` Yang--Baxter matrix owner to
the complex Fibonacci braided tensor shadow.

This is the exact bridge datum that must exist before one may identify the
local `Z3` calculus lane with a Fibonacci braid lane.
-/
structure RealToComplexBraidTransport
    {A : Type*} [Ring A]
    (C : CelikZ3CartanYangBaxterCalculus A)
    (F : FibonacciBraidedTensorCategoryShadow) where
  map : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℂ
  map_mul :
    ∀ X Y : Matrix (Fin 2) (Fin 2) ℝ, map (X * Y) = map X * map Y
  maps_R : map C.localR = F.R
  maps_B : map C.localB = F.B

namespace RealToComplexBraidTransport

variable {A : Type*} [Ring A]
variable {C : CelikZ3CartanYangBaxterCalculus A}
variable {F : FibonacciBraidedTensorCategoryShadow}

/--
Transport of the local Çelik `Z3` Yang--Baxter relation to the Fibonacci
braided-tensor shadow.
-/
theorem transports_yang_baxter (T : RealToComplexBraidTransport C F) :
    F.R * F.B * F.R = F.B * F.R * F.B := by
  calc
    F.R * F.B * F.R
        = T.map C.localR * T.map C.localB * T.map C.localR := by
            rw [← T.maps_R, ← T.maps_B]
    _ = T.map (C.localR * C.localB * C.localR) := by
            rw [← T.map_mul C.localR C.localB,
              ← T.map_mul (C.localR * C.localB) C.localR]
    _ = T.map (C.localB * C.localR * C.localB) := by
            rw [C.local_yang_baxter]
    _ = T.map C.localB * T.map C.localR * T.map C.localB := by
            rw [T.map_mul (C.localB * C.localR) C.localB,
              T.map_mul C.localB C.localR]
    _ = F.B * F.R * F.B := by
            rw [T.maps_R, T.maps_B]

end RealToComplexBraidTransport

/-! ## 4. Explicit BTC bridge -/

/--
Explicit bridge from a Çelik `Z3` Cartan/Yang--Baxter socket to a finite
Fibonacci braided-tensor-category shadow.
-/
structure ExplicitZ3FibonacciBTCBridge (A : Type*) [Ring A] where
  celik : CelikZ3CartanYangBaxterCalculus A
  fibonacci : FibonacciBraidedTensorCategoryShadow
  transport : RealToComplexBraidTransport celik fibonacci

namespace ExplicitZ3FibonacciBTCBridge

variable {A : Type*} [Ring A]

/-- Main bridge theorem: Fibonacci Artin/Yang--Baxter follows from local `Z3` transport. -/
theorem fibonacci_yang_baxter_from_celik (G : ExplicitZ3FibonacciBTCBridge A) :
    G.fibonacci.R * G.fibonacci.B * G.fibonacci.R =
      G.fibonacci.B * G.fibonacci.R * G.fibonacci.B :=
  RealToComplexBraidTransport.transports_yang_baxter G.transport

/--
The finite Fibonacci hexagon/Yang--Baxter matrix shadow obtained from the
transported Çelik `Z3` Yang--Baxter owner.
-/
theorem finite_hexagon_shadow_from_celik (G : ExplicitZ3FibonacciBTCBridge A) :
    fibonacciFusionMatrix G.fibonacci.tau G.fibonacci.sqrtTau *
        fibonacciFusionMatrix G.fibonacci.tau G.fibonacci.sqrtTau = 1
      ∧ (fibonacciFusionMatrix G.fibonacci.tau G.fibonacci.sqrtTau).det = -1
      ∧ fibonacciBMatrix G.fibonacci.q G.fibonacci.tau G.fibonacci.sqrtTau =
          fibonacciFusionMatrix G.fibonacci.tau G.fibonacci.sqrtTau *
            fibonacciRMatrix G.fibonacci.q *
            fibonacciFusionMatrix G.fibonacci.tau G.fibonacci.sqrtTau
      ∧ fibonacciRMatrix G.fibonacci.q *
            fibonacciBMatrix G.fibonacci.q G.fibonacci.tau G.fibonacci.sqrtTau *
            fibonacciRMatrix G.fibonacci.q =
          fibonacciBMatrix G.fibonacci.q G.fibonacci.tau G.fibonacci.sqrtTau *
            fibonacciRMatrix G.fibonacci.q *
            fibonacciBMatrix G.fibonacci.q G.fibonacci.tau G.fibonacci.sqrtTau := by
  have hArtin :
      fibonacciRMatrix G.fibonacci.q *
            fibonacciBMatrix G.fibonacci.q G.fibonacci.tau G.fibonacci.sqrtTau *
            fibonacciRMatrix G.fibonacci.q =
          fibonacciBMatrix G.fibonacci.q G.fibonacci.tau G.fibonacci.sqrtTau *
            fibonacciRMatrix G.fibonacci.q *
            fibonacciBMatrix G.fibonacci.q G.fibonacci.tau G.fibonacci.sqrtTau := by
    have h := fibonacci_yang_baxter_from_celik G
    simpa [G.fibonacci.R_eq, G.fibonacci.B_eq] using h
  exact ⟨
    InfoGeometry.Categorical.FibonacciBraiding.F_sq G.fibonacci.tau G.fibonacci.sqrtTau G.fibonacci.sqrt_sq G.fibonacci.tau_sq_add_tau,
    InfoGeometry.Categorical.FibonacciBraiding.det_F G.fibonacci.tau G.fibonacci.sqrtTau G.fibonacci.sqrt_sq G.fibonacci.tau_sq_add_tau,
    InfoGeometry.Categorical.FibonacciBraiding.B_eq_FRF G.fibonacci.q G.fibonacci.tau G.fibonacci.sqrtTau,
    hArtin⟩

end ExplicitZ3FibonacciBTCBridge

/-! ## 5. Cantor/Cuntz crystal at the null boundary -/

/--
Cantor/Cuntz crystal data at the null topological boundary.

The null boundary is represented by the empty binary word, i.e. the root
cylinder of the Cantor/Cuntz recursion.
-/
structure CantorCuntzNullBoundaryCrystal (Op : Type*) [Ring Op] [StarRing Op] where
  basis : InfoGeometry.Canonical.CantorCuntzBasis.CantorCuntzBasisPacket Op
  nullBoundary : InfoGeometry.Canonical.CantorCuntzBasis.BinaryWord
  nullBoundary_eq_root : nullBoundary = []

namespace CantorCuntzNullBoundaryCrystal

variable {Op : Type*} [Ring Op] [StarRing Op]

/-- The null-boundary orbit is the Cuntz/Cantor seed. -/
theorem orbit_null_eq_seed (X : CantorCuntzNullBoundaryCrystal Op) :
    InfoGeometry.Canonical.CantorCuntzBasis.CantorCuntzBasisPacket.orbit
        X.basis X.nullBoundary = X.basis.seed := by
  rw [X.nullBoundary_eq_root]
  exact InfoGeometry.Canonical.CantorCuntzBasis.CantorCuntzBasisPacket.orbit_root_eq_seed X.basis

end CantorCuntzNullBoundaryCrystal

/-! ## 6. Combined Çelik--Fibonacci--Cantor/Cuntz bridge -/

/--
Combined bridge: local `Z3` Cartan/Yang--Baxter calculus, finite Fibonacci
braided tensor shadow, and Cantor/Cuntz null-boundary crystal.
-/
structure CelikZ3FibonacciCantorCuntzBridge
    (A Op : Type*) [Ring A] [Ring Op] [StarRing Op] where
  btc : ExplicitZ3FibonacciBTCBridge A
  crystal : CantorCuntzNullBoundaryCrystal Op

namespace CelikZ3FibonacciCantorCuntzBridge

variable {A Op : Type*} [Ring A] [Ring Op] [StarRing Op]

/-- The combined bridge inherits the transported Fibonacci Yang--Baxter relation. -/
theorem fibonacci_yang_baxter (G : CelikZ3FibonacciCantorCuntzBridge A Op) :
    G.btc.fibonacci.R * G.btc.fibonacci.B * G.btc.fibonacci.R =
      G.btc.fibonacci.B * G.btc.fibonacci.R * G.btc.fibonacci.B :=
  ExplicitZ3FibonacciBTCBridge.fibonacci_yang_baxter_from_celik G.btc

/-- The combined bridge reads the null Cantor/Cuntz boundary as the seed crystal. -/
theorem null_boundary_orbit_eq_seed (G : CelikZ3FibonacciCantorCuntzBridge A Op) :
    InfoGeometry.Canonical.CantorCuntzBasis.CantorCuntzBasisPacket.orbit
        G.crystal.basis G.crystal.nullBoundary = G.crystal.basis.seed :=
  CantorCuntzNullBoundaryCrystal.orbit_null_eq_seed G.crystal

end CelikZ3FibonacciCantorCuntzBridge

end InfoGeometry.Canonical.CelikZ3FibonacciCantorCuntzBTCBridge
