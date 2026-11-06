/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.ModularFlowIsometry
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra
import InfoGeometry.OperatorAlgebra.NoetherModularFlow
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTitsFiveGradedClosurePoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetKKTRealization
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetZornGradingBridge

/-!
# Modular transport of operator-valued forms and charges

An implemented modular automorphism transports operator-valued forms by its
induced algebra map. It preserves wedge products. Central Cartan/Casimir
operators are fixed by inner modular transport, and therefore so are forms
whose values are central. The module states covariance and fixed-point
conditions explicitly: arbitrary observables and forms need not be fixed.

The unitary implementer is supplied as data. No claim that it is an
exponential, or that a general unbounded Tomita generator has been constructed,
is made here.

Erlangen reading: the represented operator algebra is the carrier, the
implemented modular star-algebra equivalence is an admissible transformation,
and fixed operators/forms (or invariant readouts) are the geometric data.
This is an action-relative definition of geometry; covariance does not imply
that every observable is pointwise fixed.
-/

noncomputable section

namespace InfoGeometry.Canonical.ModularFlowOperatorForms

open InfoGeometry.Canonical.ModularFlowIsometry
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.OperatorAlgebra.NoetherModularFlow
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion

variable {A B V : Type*}
variable [Ring A] [Algebra ℂ A] [StarRing A]
variable [NormedRing B] [NormOneClass B] [NormedAlgebra ℂ B] [StarRing B]
variable [CStarRing B]
variable [AddCommGroup V] [Module ℂ V]

/-- The inner modular automorphism acting on the represented operator algebra. -/
def modularOperatorMap (d : Data (A := A) (B := B)) : B →ₐ[ℂ] B :=
  unitaryConjugationAlgHom d

/-- Transport an operator-valued one-form through modular conjugation. -/
def modularTransport1 (d : Data (A := A) (B := B))
    (α : Op1Form ℂ V B) : Op1Form ℂ V B :=
  map1 (modularOperatorMap d) α

/-- Transport an operator-valued alternating two-form through modular conjugation. -/
def modularTransport2 (d : Data (A := A) (B := B))
    (ω : Op2Form ℂ V B) : Op2Form ℂ V B :=
  map2 (modularOperatorMap d) ω

/-- An operator is modular-geometric (fixed by the chosen implemented flow)
when the modular automorphism fixes it. -/
def ModularFixed (d : Data (A := A) (B := B)) (x : B) : Prop :=
  modularOperatorMap d x = x

/-- Every operator is transported by the modular algebra map; this is the
Erlangen covariance law for the operator carrier. -/
theorem modularOperatorMap_mul (d : Data (A := A) (B := B)) (x y : B) :
    modularOperatorMap d (x * y) = modularOperatorMap d x * modularOperatorMap d y :=
  (modularOperatorMap d).map_mul x y

/-- Modular transport preserves every power equation, including nilpotency
`x^n = 0` and finite-order/idempotence equations `x^n = 1`. -/
theorem modularOperatorMap_pow (d : Data (A := A) (B := B)) (x : B) (n : ℕ) :
    modularOperatorMap d (x ^ n) = modularOperatorMap d x ^ n :=
  (modularOperatorMap d).map_pow x n

omit [NormOneClass B] [CStarRing B] in
/-- The implemented inner modular action is compatible with the involution. -/
theorem modularOperatorMap_star (d : Data (A := A) (B := B)) (x : B) :
    modularOperatorMap d (star x) = star (modularOperatorMap d x) := by
  change unitaryConjugationStarAlgHom d (star x) =
    star (unitaryConjugationStarAlgHom d x)
  exact (unitaryConjugationStarAlgHom d).map_star' x

omit [NormOneClass B] [CStarRing B] in
/-- Inner modular transport intertwines the noncommutative commutator.  Thus
the order-sensitive anomaly of a paired operator is transported as the anomaly
of the transported pair. -/
theorem modularOperatorMap_comm (d : Data (A := A) (B := B)) (x y : B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (modularOperatorMap d x) (modularOperatorMap d y) =
      modularOperatorMap d
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y) := by
  simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
    map_sub, map_mul, modularOperatorMap]

omit [NormOneClass B] [CStarRing B] in
/-- Inner modular transport intertwines the anticommutator, carrying the
operator-valued support/gap of a chiral pair to the support/gap of its image. -/
theorem modularOperatorMap_anticomm (d : Data (A := A) (B := B)) (x y : B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm
        (modularOperatorMap d x) (modularOperatorMap d y) =
      modularOperatorMap d
        (InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm x y) := by
  simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm,
    map_add, map_mul, modularOperatorMap]

omit [NormOneClass B] [CStarRing B] in
/-- Modular fixed points are closed under addition. -/
theorem ModularFixed.add (d : Data (A := A) (B := B)) {x y : B}
    (hx : ModularFixed d x) (hy : ModularFixed d y) :
    ModularFixed d (x + y) := by
  change modularOperatorMap d (x + y) = x + y
  rw [map_add, hx, hy]

omit [NormOneClass B] [CStarRing B] in
/-- Modular fixed points are closed under the star involution. -/
theorem ModularFixed.star_closed (d : Data (A := A) (B := B)) {x : B}
    (hx : ModularFixed d x) : ModularFixed d (star x) := by
  change modularOperatorMap d (star x) = star x
  rw [modularOperatorMap_star, hx]

omit [NormOneClass B] [CStarRing B] in
/-- Modular fixed points are closed under the commutator Lie product. -/
theorem ModularFixed.comm (d : Data (A := A) (B := B)) {x y : B}
    (hx : ModularFixed d x) (hy : ModularFixed d y) :
    ModularFixed d
      (InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y) := by
  change modularOperatorMap d
      (InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y) = _
  rw [← modularOperatorMap_comm, hx, hy]

omit [NormOneClass B] [CStarRing B] in
/-- Modular fixed points are closed under the Jordan anticommutator product. -/
theorem ModularFixed.anticomm (d : Data (A := A) (B := B)) {x y : B}
    (hx : ModularFixed d x) (hy : ModularFixed d y) :
    ModularFixed d
      (InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm x y) := by
  change modularOperatorMap d
      (InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm x y) = _
  rw [← modularOperatorMap_anticomm, hx, hy]

omit [NormOneClass B] [CStarRing B] in
/-- The full Peirce tetraktys `(Φ, J, V, Σ)` is equivariant under inner
modular transport, with the commutator-defined anomaly and anticommutator
support both preserving their multiplication order.  No fixed-point condition
on the cut or generators is assumed. -/
theorem modularOperatorMap_peirce_tetraktys (d : Data (A := A) (B := B))
    (P A C : B) :
    modularOperatorMap d
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi
        (modularOperatorMap d P) (modularOperatorMap d A) (modularOperatorMap d C) ∧
    modularOperatorMap d
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A C) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.genJ
        (modularOperatorMap d P) (modularOperatorMap d A) (modularOperatorMap d C) ∧
    modularOperatorMap d
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genV P A C) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.genV
        (modularOperatorMap d P) (modularOperatorMap d A) (modularOperatorMap d C) ∧
    modularOperatorMap d
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P A C) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.genSig
        (modularOperatorMap d P) (modularOperatorMap d A) (modularOperatorMap d C) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi,
      InfoGeometry.OperatorAlgebra.PeirceSpine.genJ,
      InfoGeometry.OperatorAlgebra.PeirceSpine.genV,
      InfoGeometry.OperatorAlgebra.PeirceSpine.genSig,
      InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm,
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
      modularOperatorMap]

omit [NormOneClass B] [CStarRing B] in
/-- Modular transport preserves an `ad(s)` integer eigenspace whenever it fixes
the grading operator `s`. This is the operator-level compatibility between
the Erlangen action and an inner-commutator grading: if `s` is a fixed Cartan
generator and `[s,x] = m • x`, then the transported operator has the same
grade. -/
theorem modular_preserves_ad_eigenspace (d : Data (A := A) (B := B))
    (s x : B) (m : ℤ) (hs : modularOperatorMap d s = s)
    (hx : s * x - x * s = m • x) :
    s * modularOperatorMap d x - modularOperatorMap d x * s =
      m • modularOperatorMap d x := by
  have hmap := congrArg (modularOperatorMap d) hx
  simpa only [map_sub, map_mul, map_zsmul, hs] using hmap

omit [NormOneClass B] [CStarRing B] in
/-- Modular transport intertwines the grade `+2` Jordan-associator/Kantor
generator with the same construction on the transported operators. This
connects the implemented operator-algebra action to the owned five-grade KKT
construction without assuming that the original generators are fixed. -/
theorem modularOperatorMap_transports_K_plus2
    (d : Data (A := A) (B := B)) (N X : B) :
    modularOperatorMap d
        (InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTits.K_plus2 N X) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTits.K_plus2
        (modularOperatorMap d N) (modularOperatorMap d X) := by
  simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTits.K_plus2,
    InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTits.JordanAssoc,
    map_sub, map_add, map_mul, modularOperatorMap]

/-- Apply the implemented modular algebra automorphism entrywise to the
three-sheet matrix carrier. -/
def modularMatrixTransport (d : Data (A := A) (B := B)) :
    Matrix (Fin 3) (Fin 3) B →+* Matrix (Fin 3) (Fin 3) B :=
  (unitaryConjugationAlgHom d).toRingHom.mapMatrix

omit [NormOneClass B] [CStarRing B] in
/-- The entrywise modular transport preserves the concrete Euler five-grading
on `Matrix (Fin 3) (Fin 3) B`. Thus the implemented operator-algebra action
from this file acts on the same five graded matrix sectors as the
three-sheet KKT realization. The coefficients of the grading are integer
scalars, so no commutation assumption on matrix entries is used. -/
theorem modularMatrixTransport_eulerFiveGrading3
    (d : Data (A := A) (B := B)) (X : Matrix (Fin 3) (Fin 3) B) :
    modularMatrixTransport d
        (InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetKKTRealization.eulerFiveGrading3 X) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetKKTRealization.eulerFiveGrading3
        (modularMatrixTransport d X) := by
  ext i j
  simp [modularMatrixTransport,
    InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetKKTRealization.eulerFiveGrading3,
    InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetKKTRealization.grade3Matrix,
    RingHom.mapMatrix_apply, map_mul]

/-- The modular algebra automorphism acts coordinatewise on the noncommutative
operator-valued Zorn carrier. -/
def modularOpZornTransport (d : Data (A := A) (B := B))
    (X : OpZornMatrix B) : OpZornMatrix B :=
  ⟨modularOperatorMap d X.a,
   ⟨modularOperatorMap d X.v.x, modularOperatorMap d X.v.y,
     modularOperatorMap d X.v.z⟩,
   ⟨modularOperatorMap d X.w.x, modularOperatorMap d X.w.y,
     modularOperatorMap d X.w.z⟩,
   modularOperatorMap d X.b⟩

omit [NormOneClass B] [CStarRing B] in
/-- The three-sheet-to-Zorn projection is equivariant for entrywise modular
transport. This is a commuting-square theorem for the grading projection; it
does not assert that the projection preserves matrix multiplication. -/
theorem modularOpZornTransport_matrix3ToOpZorn
    (d : Data (A := A) (B := B)) (X : Matrix (Fin 3) (Fin 3) B) :
    modularOpZornTransport d
        (InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetZornGradingBridge.matrix3ToOpZorn X) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetZornGradingBridge.matrix3ToOpZorn
        (modularMatrixTransport d X) := by
  ext <;>
    simp [modularOpZornTransport, modularOperatorMap,
      InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetZornGradingBridge.matrix3ToOpZorn,
      modularMatrixTransport, RingHom.mapMatrix_apply]

omit [NormOneClass B] [CStarRing B] in
/-- Modular transport preserves the five-grade Euler action on the
operator-valued Zorn model. -/
theorem modularOpZornTransport_eulerFiveGrading
    (d : Data (A := A) (B := B)) (X : OpZornMatrix B) :
    modularOpZornTransport d (opEulerFiveGrading X) =
      opEulerFiveGrading (modularOpZornTransport d X) := by
  ext <;>
    simp [modularOpZornTransport, modularOperatorMap, opEulerFiveGrading]

omit [NormOneClass B] [CStarRing B] in
/-- The matrix-to-Zorn grading projection intertwines modular transport and
the Euler five-grading in the same commuting square. -/
theorem modularOpZornTransport_euler_projection_square
    (d : Data (A := A) (B := B)) (X : Matrix (Fin 3) (Fin 3) B) :
    modularOpZornTransport d
        (opEulerFiveGrading
          (InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetZornGradingBridge.matrix3ToOpZorn X)) =
      opEulerFiveGrading
        (InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetZornGradingBridge.matrix3ToOpZorn
          (modularMatrixTransport d X)) := by
  calc
    modularOpZornTransport d
        (opEulerFiveGrading
          (InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetZornGradingBridge.matrix3ToOpZorn X)) =
      opEulerFiveGrading
        (modularOpZornTransport d
          (InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetZornGradingBridge.matrix3ToOpZorn X)) :=
            modularOpZornTransport_eulerFiveGrading d _
    _ = opEulerFiveGrading
        (InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetZornGradingBridge.matrix3ToOpZorn
          (modularMatrixTransport d X)) := by
            rw [modularOpZornTransport_matrix3ToOpZorn]

theorem modular_preserves_nilpotence (d : Data (A := A) (B := B))
    (x : B) (n : ℕ) (h : x ^ n = 0) :
    modularOperatorMap d x ^ n = 0 := by
  rw [← modularOperatorMap_pow, h]
  exact (modularOperatorMap d).map_zero

theorem modular_preserves_finite_order (d : Data (A := A) (B := B))
    (x : B) (n : ℕ) (h : x ^ n = 1) :
    modularOperatorMap d x ^ n = 1 := by
  rw [← modularOperatorMap_pow, h]
  exact (modularOperatorMap d).map_one

/-- The order-six cyclotomic operator equation is preserved by modular
transport. This formulation keeps the operator multiplication order explicit. -/
theorem modular_preserves_cyclotomic6 (d : Data (A := A) (B := B))
    (u : B) (h : u * u - u + 1 = 0) :
    modularOperatorMap d u * modularOperatorMap d u -
        modularOperatorMap d u + 1 = 0 := by
  have hm := congrArg (modularOperatorMap d) h
  simpa only [map_sub, map_add, map_mul, map_one, map_zero] using hm

/-- An explicit coefficient-fixing operator-algebra equivalence preserves
nilpotence. Applying this theorem to elements of a Galois group requires an
owned realization of those elements as `AlgEquiv`s. -/
theorem operatorAlgEquiv_preserves_nilpotence
    {R B : Type*} [CommSemiring R] [Ring B] [Algebra R B]
    (f : B ≃ₐ[R] B) (x : B) (n : ℕ)
    (hx : x ^ n = 0) : (f x) ^ n = 0 := by
  have hm := congrArg f hx
  simpa only [map_pow, map_zero] using hm

/-- An explicit coefficient-fixing operator-algebra equivalence preserves
finite-order and idempotence equations. -/
theorem operatorAlgEquiv_preserves_finite_order
    {R B : Type*} [CommSemiring R] [Ring B] [Algebra R B]
    (f : B ≃ₐ[R] B) (x : B) (n : ℕ)
    (hx : x ^ n = 1) : (f x) ^ n = 1 := by
  have hm := congrArg f hx
  simpa only [map_pow, map_one] using hm

/-- An explicit coefficient-fixing operator-algebra equivalence preserves
cyclotomic polynomial equations, including the order-six relation. -/
theorem operatorAlgEquiv_preserves_cyclotomic6
    {R B : Type*} [CommSemiring R] [Ring B] [Algebra R B]
    (f : B ≃ₐ[R] B) (u : B)
    (hu : u * u - u + 1 = 0) :
    f u * f u - f u + 1 = 0 := by
  have hm := congrArg f hu
  simpa only [map_sub, map_add, map_mul, map_one, map_zero] using hm

/-- The fixed-point operators form a multiplicatively closed sector. -/
theorem ModularFixed.mul (d : Data (A := A) (B := B)) {x y : B}
    (hx : ModularFixed d x) (hy : ModularFixed d y) : ModularFixed d (x * y) := by
  unfold ModularFixed at *
  rw [modularOperatorMap_mul, hx, hy]

/-- Modular transport preserves the noncommutative wedge product. -/
theorem modularTransport_wedge (d : Data (A := A) (B := B))
    (α β : Op1Form ℂ V B) :
    modularTransport2 d (wedge α β) =
      wedge (modularTransport1 d α) (modularTransport1 d β) := by
  exact map2_wedge (modularOperatorMap d) α β

/-- A central operator is fixed by the implemented modular automorphism. -/
theorem modularOperatorMap_fixes_central (d : Data (A := A) (B := B))
    (z : B) (hz : ∀ x : B, z * x = x * z) :
    modularOperatorMap d z = z := by
  change d.implementer * z * star d.implementer = z
  calc
    d.implementer * z * star d.implementer =
        z * d.implementer * star d.implementer := by rw [hz d.implementer]
    _ = z * (d.implementer * star d.implementer) := by rw [mul_assoc]
    _ = z := by rw [d.implementer_right, mul_one]

/-- Any two operators in Mathlib's center of the represented algebra commute.
This is the operator-algebra statement for a family of Cartan/Casimir
observables once each observable has been shown central. -/
theorem centralObservables_commute (c₁ c₂ : Subalgebra.center ℂ B) :
    (c₁ : B) * (c₂ : B) = (c₂ : B) * (c₁ : B) := by
  exact ((Subalgebra.mem_center_iff.mp c₁.2) (c₂ : B)).symm

/-- Central operators are modular-geometric fixed points. -/
theorem central_is_modularFixed (d : Data (A := A) (B := B)) (z : B)
    (hz : ∀ x : B, z * x = x * z) : ModularFixed d z :=
  modularOperatorMap_fixes_central d z hz

/-- If every value of a one-form is a central operator, modular transport fixes it. -/
theorem modularTransport1_fixes_centralValues (d : Data (A := A) (B := B))
    (α : Op1Form ℂ V B)
    (hcentral : ∀ v x, α v * x = x * α v) :
    modularTransport1 d α = α := by
  ext v
  exact modularOperatorMap_fixes_central d (α v) (hcentral v)

/-- If every value of a two-form is a central operator, modular transport fixes it. -/
theorem modularTransport2_fixes_centralValues (d : Data (A := A) (B := B))
    (ω : Op2Form ℂ V B)
    (hcentral : ∀ u v x, ω u v * x = x * ω u v) :
    modularTransport2 d ω = ω := by
  apply Op2Form.ext
  intro u v
  exact modularOperatorMap_fixes_central d (ω u v) (hcentral u v)

/-- Transport an operator-valued Killing derivation by modular conjugation. -/
def modularTransportKillingField (d : Data (A := A) (B := B))
    (K : OperatorKillingField B) : OperatorKillingField B where
  derivation := fun x =>
    unitaryConjugationStarAlgEquiv d
      (K.derivation ((unitaryConjugationStarAlgEquiv d).symm x))

/-- The transported Killing derivation is equivariant under the modular
automorphism: transport after applying the modular map equals applying the
modular map after the original derivation. -/
theorem modularTransportKillingField_equivariant
    (d : Data (A := A) (B := B)) (K : OperatorKillingField B) (x : B) :
    (modularTransportKillingField d K).derivation
        (unitaryConjugationStarAlgEquiv d x) =
      unitaryConjugationStarAlgEquiv d (K.derivation x) := by
  change unitaryConjugationStarAlgEquiv d
      (K.derivation ((unitaryConjugationStarAlgEquiv d).symm
        (unitaryConjugationStarAlgEquiv d x))) =
      unitaryConjugationStarAlgEquiv d (K.derivation x)
  rw [(unitaryConjugationStarAlgEquiv d).symm_apply_apply]

/-- A Noether charge is modular-invariant when its operator observable is a
fixed point of the implemented modular automorphism. -/
def IsModularInvariantNoetherCharge (d : Data (A := A) (B := B))
    {Readout : Type*} (Q : OperatorNoetherCharge B Readout) : Prop :=
  ModularFixed d Q.chargeObservable

/-- Central Noether observables are modular-invariant charges. -/
theorem centralNoetherCharge_is_modularInvariant
    (d : Data (A := A) (B := B)) {Readout : Type*}
    (Q : OperatorNoetherCharge B Readout)
    (hcentral : ∀ x : B, Q.chargeObservable * x = x * Q.chargeObservable) :
    IsModularInvariantNoetherCharge d Q :=
  central_is_modularFixed d Q.chargeObservable hcentral

/-- The modular automorphism fixes the Cartan/Casimir-generated operator when
that operator is central in the represented algebra. -/
theorem modularOperatorMap_fixes_casimir
    (d : Data (A := A) (B := B)) (casimir : B)
    (hcentral : ∀ x : B, casimir * x = x * casimir) :
    modularOperatorMap d casimir = casimir :=
  modularOperatorMap_fixes_central d casimir hcentral

/-- A Cartan/Casimir observable contributes a fixed geometric datum precisely
when its centrality (or another fixed-point proof) is established. -/
theorem casimir_is_modularFixed (d : Data (A := A) (B := B)) (casimir : B)
    (hcentral : ∀ x : B, casimir * x = x * casimir) : ModularFixed d casimir :=
  central_is_modularFixed d casimir hcentral

/-- Central charges act compatibly with every operator on a left operator module.
This is the precise module-level meaning of a central Cartan/Casimir action. -/
theorem centralOperatorAction_commutes
    {M : Type*} [AddCommMonoid M] [Module B M]
    (c x : B) (hc : c * x = x * c) (v : M) :
    c • (x • v) = x • (c • v) := by
  rw [← mul_smul, hc, mul_smul]

/-- The sheet grading acts on the Peirce frame/current pair as the two-step
modular harmonic oscillator.  The parameter `c` is an arbitrary central
coefficient (in particular `c = -log(p/q)/2` when an analytic sheet
surprisal has been constructed); this theorem formalizes the algebraic
commutator identities and makes no claim to construct an operator logarithm.
-/
theorem peirce_sheet_generator_harmonic
    {B : Type*} [Ring B] [Algebra ℂ B]
    (P A C : B) (hP : P * P = P) (c : ℂ) :
    let Φ := InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C
    let J := InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A C
    let S := InfoGeometry.OperatorAlgebra.PeirceSpine.invS P
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (c • S) Φ =
        (2 * c) • J ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (c • S) J =
        (2 * c) • Φ ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (c • S)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (c • S) Φ) =
        (4 * c * c) • Φ := by
  dsimp
  have hSΦ : InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C) =
      (2 : ℂ) • InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A C := by
    simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
      InfoGeometry.OperatorAlgebra.PeirceSpine.invS,
      InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi,
      InfoGeometry.OperatorAlgebra.PeirceSpine.genJ,
      InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus]
    peirce_nf hP
    module
  have hSJ : InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A C) =
      (2 : ℂ) • InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C := by
    simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
      InfoGeometry.OperatorAlgebra.PeirceSpine.invS,
      InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi,
      InfoGeometry.OperatorAlgebra.PeirceSpine.genJ,
      InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus]
    peirce_nf hP
    module
  have hscale : ∀ (X Y : B),
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (c • X) Y =
        c • InfoGeometry.OperatorAlgebra.PeirceSpine.comm X Y := by
    intro X Y
    simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
      smul_mul_assoc, mul_smul_comm, smul_sub]
  have hscaleRight : ∀ (X Y : B),
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm X (c • Y) =
        c • InfoGeometry.OperatorAlgebra.PeirceSpine.comm X Y := by
    intro X Y
    simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
      mul_smul_comm, smul_mul_assoc, smul_sub]
  have hscaleRightScalar : ∀ (d : ℂ) (X Y : B),
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm X (d • Y) =
        d • InfoGeometry.OperatorAlgebra.PeirceSpine.comm X Y := by
    intro d X Y
    simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
      mul_smul_comm, smul_mul_assoc, smul_sub]
  refine ⟨?_, ?_, ?_⟩
  · rw [hscale, hSΦ, smul_smul]
    congr 1
    ring
  · rw [hscale, hSJ, smul_smul]
    congr 1
    ring
  · calc
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (c • InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (c • InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
            (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C))
          = c • InfoGeometry.OperatorAlgebra.PeirceSpine.comm
              (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
              (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (c • InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
                (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C)) := hscale _ _
      _ = c • InfoGeometry.OperatorAlgebra.PeirceSpine.comm
              (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
              (c • InfoGeometry.OperatorAlgebra.PeirceSpine.comm
                (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
                (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C)) := by
          rw [hscale]
      _ = c • (c • InfoGeometry.OperatorAlgebra.PeirceSpine.comm
              (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
              (InfoGeometry.OperatorAlgebra.PeirceSpine.comm
                (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
                (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C))) := by
          rw [hscaleRight]
      _ = (c * c) • InfoGeometry.OperatorAlgebra.PeirceSpine.comm
              (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
              (InfoGeometry.OperatorAlgebra.PeirceSpine.comm
                (InfoGeometry.OperatorAlgebra.PeirceSpine.invS P)
                (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C)) := by
          rw [smul_smul]
      _ = (c * c) • ((2 : ℂ) • ((2 : ℂ) •
              InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C)) := by
          rw [hSΦ, hscaleRightScalar, hSJ]
      _ = (4 * c * c) • InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A C := by
          rw [smul_smul, smul_smul]
          congr 1
          ring

end InfoGeometry.Canonical.ModularFlowOperatorForms

end noncomputable section
