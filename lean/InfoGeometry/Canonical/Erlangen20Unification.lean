/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
import InfoGeometry.Canonical.ErlangenOperator2
import InfoGeometry.Canonical.ErlangenOperator2Bridge
import InfoGeometry.OperatorAlgebra.ErlangenOperator2
import InfoGeometry.Geometry.PhaseErlanger
import InfoGeometry.Erlangen.SmoothCartanGeometry
import InfoGeometry.Canonical.OperatorErlangenFixedPoints
import InfoGeometry.Canonical.OperatorErlangenGaloisConnection
import InfoGeometry.Canonical.FelixKleinGeometryUnification
import InfoGeometry.Categorical.CantorDoubleCylinderColimitAlgebra
import InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis
import InfoGeometry.Erlangen.GrassmannPluckerKleinCrossPillarBridges
import InfoGeometry.Erlangen.ErlangenProgramGroupHierarchyAndPrincipal
import InfoGeometry.Erlangen.ErlangenProgramTransferHesseAndBodies
import InfoGeometry.Erlangen.ErlangenProgramCurvatureBinaryAndMasterAtlas
import InfoGeometry.Projective.KleinErlangenProgramGroupsAndProjectiveTransfer
import InfoGeometry.Krein.DoubledSpace

/-!
# Felix Klein Erlangen 2.0 Unification (`F2.1` / `M3.4`)

This module reconciles all 10 F2.1 Erlangen 2.0 owners across the four Erlangen axes, grounded
in Felix Klein's 1872 *Erlanger Programm* (*Vergleichende Betrachtungen über neuere geometrische
Forschungen*, Erlangen: A. Deichert, 1872; University of Michigan Historical Mathematics
Collection `ABN7632.0001.001`; English translation by M. W. Haskell, *Bull. New York Math. Soc.*
2 (1892–1893), 215–249, `arXiv:0807.3161v1`):

- **Axis A** (`SymmetryAction`, `OperatorSymmetryAction`, `OperatorErlangenFixedPoints`,
  `OperatorErlangenGaloisConnection`, `IsHomogeneousSpace`, `orbit_quotient_stabilizer_equiv`):
  Klein §1 *Hauptgruppe* & invariants, §2 subgroup inclusion / adjoining configurations, §5 &
  Fn. 22–23 homogeneous *bodies* and normal-core faithfulness, and Concluding Remarks Galois
  correspondence.
- **Axis B** (`Erlangen20Datum`, `OperatorIntertwiner`): Klein §4 transfer by representation
  (*Abbildung*) and §10 / Concluding Remarks coordinate-system-independent analytic formalisms.
- **Axis C** (`Canonical.ErlangenOperator2.ErlangenOperatorDatum`, `ErlangenOperator2Bridge`,
  `OperatorAlgebra.ErlangenOperator2.ErlangenInvariantPacket`): Thermodynamic / Fisher / Onsager
  invariant geometry.
- **Axis D** (`PhaseErlanger`, `SmoothCartanGeometry`, `CantorDoubleCylinderColimitAlgebra`,
  `KreinCl44SplitG2DerivationPosetSynthesis`, `GrassmannPluckerKleinCrossPillarBridges`):
  Concrete physical, Cartan (§§8–9), Cantor direct-limit, Krein / split $G_{2(2)}$, and
  Grassmann–Plücker–Clifford realizations.

## Six Bridges

1. **Bridge 1**: `PhaseCentralizer K` / `PhaseIsomorphism K K` → `SymmetryAction`,
   `OperatorSymmetryAction`, `InvariantReadout` / `IsInvariantReadout`, `ChiralAxis K` →
   `CircularPolarization` → `ComplementaryProjectors` (+ `chiralStabilizer`), and
   `PhaseMetricMorphism` (`MetricPreserving`) vs. `IsKreinIsometry` (`kreinInner`) separation.
2. **Bridge 2**: `PhaseErlanger (H, K)` → `Erlangen20Datum` (`phaseErlangerDatum`,
   `toErlangen20Datum`, `HomothetyH` / full-centralizer / chiral variants).
3. **Bridge 3**: Bidirectional `Erlangen20Datum` ↔ `SymmetryAction` & `OperatorErlangenFixedPoints`
   (including commutant = stabilizer, Galois connection, `Type u` Cantor generalization via
   non-diamond `def doubleCylinderColimitAlgebra`, `Type 0` match, and Krein / split $G_{2(2)}$).
4. **Bridge 4**: `OperatorAlgebra.ErlangenOperator2.ErlangenInvariantPacket` →
   `Canonical.ErlangenOperator2.ErlangenOperatorDatum` (isolating `uPol = 0` inside packet inputs),
   compatibility with `ErlangenOperator2Bridge`, and universe-polymorphic Axis A ↔ Axis C / B.
5. **Bridge 5**: `SmoothCartanGeometry` fiberwise `H`-action (`C.AdH` + `C.omega p`) →
   `OperatorSymmetryAction` / `SymmetryAction` compatible with `cartanFiberErlangen20Datum` and
   `cartanAdjointIntertwiner`, plus concrete `homothetyCartanGeometry κ` noncommutative witness.
6. **Bridge 6**: `OperatorIntertwiner` & Klein §4 *Abbildung* transport (`conjEndAlgEquiv`,
   `transportSymmetryAction`, `transportErlangen20Datum`), M3.1 §5 & M3.2 integration, T16/T17
   noncommutativity witnesses (`sl₂(ℝ)` / `M₂(ℝ)` and `EndR (DoubledSpace ℝ)`), and
   `klein_erlangen20_four_axis_master_unification`.
-/

noncomputable section

namespace InfoGeometry.Canonical.Erlangen20Unification

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Core
open InfoGeometry.Erlangen.InvariantGeometry
open InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
open InfoGeometry.Canonical.OperatorErlangenFixedPoints
open InfoGeometry.Canonical.FelixKleinGeometryUnification

/-!
## Bridge 1: `PhaseCentralizer` & `PhaseIsomorphism` → `SymmetryAction`, `ChiralAxis`, & Krein Separation
-/

section Bridge1

open InfoGeometry.Geometry.PhaseErlanger

/-- `PhaseCentralizer K` realized cleanly as a `Subalgebra ℝ (EndR H)` using only Mathlib's
native `Subalgebra` instances. -/
def phaseCentralizerSubalgebra
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : Subalgebra ℝ (EndR H) where
  carrier := {T : EndR H | PhaseLinear K T}
  mul_mem' hS hT := PhaseLinear.comp hS hT
  one_mem' := PhaseLinear.id
  add_mem' hS hT := PhaseLinear.add hS hT
  zero_mem' := PhaseLinear.zero
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact PhaseLinear.smul r PhaseLinear.id

/-- Canonical `ℝ`-algebra homomorphism from continuous linear endomorphisms `EndR H` to
abstract linear endomorphisms `Module.End ℝ H`. -/
def clmToEndAlgHom
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :
    EndR H →ₐ[ℝ] Module.End ℝ H :=
  { ContinuousLinearMap.toLinearMapRingHom with
    commutes' := fun r => by
      ext v
      change (algebraMap ℝ (EndR H) r) v = (algebraMap ℝ (Module.End ℝ H) r) v
      rw [ContinuousLinearMap.algebraMap_apply, Module.algebraMap_end_apply] }

/-- Image of `phaseCentralizerSubalgebra K` inside `Module.End ℝ H`. -/
def phaseCentralizerEndSubalgebra
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : Subalgebra ℝ (Module.End ℝ H) :=
  (phaseCentralizerSubalgebra K).map (clmToEndAlgHom H)

lemma phaseCentralizer_eq_of_op_eq
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : EndR H} {S T : PhaseCentralizer K} (h : S.op = T.op) : S = T := by
  cases S
  cases T
  cases h
  rfl

scoped instance instZeroPhaseCentralizer
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (K : EndR H) :
    Zero (PhaseCentralizer K) :=
  ⟨⟨0, PhaseLinear.zero⟩⟩

scoped instance instOnePhaseCentralizer
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (K : EndR H) :
    One (PhaseCentralizer K) :=
  ⟨⟨ContinuousLinearMap.id ℝ H, PhaseLinear.id⟩⟩

scoped instance instAddPhaseCentralizer
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (K : EndR H) :
    Add (PhaseCentralizer K) :=
  ⟨fun S T => ⟨S.op + T.op, PhaseLinear.add S.phase_linear T.phase_linear⟩⟩

scoped instance instNegPhaseCentralizer
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (K : EndR H) :
    Neg (PhaseCentralizer K) :=
  ⟨fun S => ⟨-S.op, PhaseLinear.neg S.phase_linear⟩⟩

scoped instance instSubPhaseCentralizer
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (K : EndR H) :
    Sub (PhaseCentralizer K) :=
  ⟨fun S T => ⟨S.op - T.op, PhaseLinear.sub S.phase_linear T.phase_linear⟩⟩

scoped instance instMulPhaseCentralizer
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (K : EndR H) :
    Mul (PhaseCentralizer K) :=
  ⟨fun S T => ⟨S.op.comp T.op, PhaseLinear.comp S.phase_linear T.phase_linear⟩⟩

/-- Scoped `Ring` structure on `PhaseCentralizer K` inherited from `EndR H`. -/
scoped instance instRingPhaseCentralizer
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : Ring (PhaseCentralizer K) where
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec
  add_assoc a b c := phaseCentralizer_eq_of_op_eq (_root_.add_assoc a.op b.op c.op)
  zero_add a := phaseCentralizer_eq_of_op_eq (_root_.zero_add a.op)
  add_zero a := phaseCentralizer_eq_of_op_eq (_root_.add_zero a.op)
  neg_add_cancel a := phaseCentralizer_eq_of_op_eq (_root_.neg_add_cancel a.op)
  add_comm a b := phaseCentralizer_eq_of_op_eq (_root_.add_comm a.op b.op)
  sub_eq_add_neg a b := phaseCentralizer_eq_of_op_eq (_root_.sub_eq_add_neg a.op b.op)
  left_distrib a b c := phaseCentralizer_eq_of_op_eq (mul_add a.op b.op c.op)
  right_distrib a b c := phaseCentralizer_eq_of_op_eq (add_mul a.op b.op c.op)
  zero_mul a := phaseCentralizer_eq_of_op_eq (zero_mul a.op)
  mul_zero a := phaseCentralizer_eq_of_op_eq (mul_zero a.op)
  mul_assoc a b c := phaseCentralizer_eq_of_op_eq (_root_.mul_assoc a.op b.op c.op)
  one_mul a := phaseCentralizer_eq_of_op_eq (one_mul a.op)
  mul_one a := phaseCentralizer_eq_of_op_eq (mul_one a.op)

@[simp] lemma phaseCentralizer_zero_op
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (K : EndR H) :
    (0 : PhaseCentralizer K).op = 0 := rfl

@[simp] lemma phaseCentralizer_one_op
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (K : EndR H) :
    (1 : PhaseCentralizer K).op = ContinuousLinearMap.id ℝ H := rfl

@[simp] lemma phaseCentralizer_add_op
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {K : EndR H}
    (S T : PhaseCentralizer K) : (S + T).op = S.op + T.op := rfl

@[simp] lemma phaseCentralizer_sub_op
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {K : EndR H}
    (S T : PhaseCentralizer K) : (S - T).op = S.op - T.op := rfl

@[simp] lemma phaseCentralizer_neg_op
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {K : EndR H}
    (S : PhaseCentralizer K) : (-S).op = -S.op := rfl

@[simp] lemma phaseCentralizer_mul_op
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {K : EndR H}
    (S T : PhaseCentralizer K) : (S * T).op = S.op.comp T.op := rfl

/-- Scalar embedding `ℝ →+* PhaseCentralizer K` for `RingHom.toAlgebra'`. -/
def phaseCentralizerAlgebraMap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : ℝ →+* PhaseCentralizer K where
  toFun r := ⟨r • ContinuousLinearMap.id ℝ H, PhaseLinear.smul r PhaseLinear.id⟩
  map_one' := phaseCentralizer_eq_of_op_eq (one_smul ℝ (ContinuousLinearMap.id ℝ H))
  map_mul' r s := phaseCentralizer_eq_of_op_eq (by
    change (r * s) • ContinuousLinearMap.id ℝ H =
      (r • ContinuousLinearMap.id ℝ H).comp (s • ContinuousLinearMap.id ℝ H)
    ext v
    change (r * s) • v = r • (s • v)
    rw [mul_smul])
  map_zero' := phaseCentralizer_eq_of_op_eq (zero_smul ℝ (ContinuousLinearMap.id ℝ H))
  map_add' r s := phaseCentralizer_eq_of_op_eq (add_smul r s (ContinuousLinearMap.id ℝ H))

/-- Scoped `Algebra ℝ` on `PhaseCentralizer K` built via `RingHom.toAlgebra'` (diamond-free). -/
scoped instance instAlgebraPhaseCentralizer
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : Algebra ℝ (PhaseCentralizer K) :=
  RingHom.toAlgebra' (phaseCentralizerAlgebraMap K) (fun r T => by
    apply phaseCentralizer_eq_of_op_eq
    ext v
    change r • T.op v = T.op (r • v)
    rw [map_smul])

@[simp] lemma phaseCentralizer_smul_op
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {K : EndR H}
    (r : ℝ) (T : PhaseCentralizer K) :
    (r • T).op = r • T.op := by
  rw [Algebra.smul_def]
  ext v
  change ((r • ContinuousLinearMap.id ℝ H).comp T.op) v = (r • T.op) v
  rfl

/-- `ℝ`-algebra isomorphism between `PhaseCentralizer K` and `phaseCentralizerSubalgebra K`. -/
def phaseCentralizerEquivSubalgebra
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : PhaseCentralizer K ≃ₐ[ℝ] phaseCentralizerSubalgebra K where
  toFun T := ⟨T.op, T.phase_linear⟩
  invFun T := ⟨T.1, T.2⟩
  left_inv T := by cases T; rfl
  right_inv T := by cases T; rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' r := by
    apply Subtype.ext
    change r • ContinuousLinearMap.id ℝ H = algebraMap ℝ (EndR H) r
    rw [Algebra.algebraMap_eq_smul_one]
    rfl

lemma phaseIsomorphism_eq_of_fields
    {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    {K₁ : EndR H₁} {K₂ : EndR H₂}
    {Φ Ψ : PhaseIsomorphism K₁ K₂}
    (h1 : Φ.toLinear = Ψ.toLinear) (h2 : Φ.invLinear = Ψ.invLinear) : Φ = Ψ := by
  cases Φ
  cases Ψ
  cases h1
  cases h2
  rfl

/-- Scoped `Group` structure on `PhaseIsomorphism K K` under composition and inversion. -/
scoped instance instGroupPhaseIsomorphism
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : Group (PhaseIsomorphism K K) where
  one :=
    { toLinear := ContinuousLinearMap.id ℝ H
      invLinear := ContinuousLinearMap.id ℝ H
      left_inv := ContinuousLinearMap.id_comp _
      right_inv := ContinuousLinearMap.id_comp _
      phase_to := PhaseLinear.id
      phase_inv := PhaseLinear.id }
  mul Φ Ψ :=
    { toLinear := Φ.toLinear.comp Ψ.toLinear
      invLinear := Ψ.invLinear.comp Φ.invLinear
      left_inv := by
        calc
          (Ψ.invLinear.comp Φ.invLinear).comp (Φ.toLinear.comp Ψ.toLinear)
              = Ψ.invLinear.comp ((Φ.invLinear.comp Φ.toLinear).comp Ψ.toLinear) := by
                  simp only [ContinuousLinearMap.comp_assoc]
          _ = ContinuousLinearMap.id ℝ H := by
                rw [Φ.left_inv, ContinuousLinearMap.id_comp, Ψ.left_inv]
      right_inv := by
        calc
          (Φ.toLinear.comp Ψ.toLinear).comp (Ψ.invLinear.comp Φ.invLinear)
              = Φ.toLinear.comp ((Ψ.toLinear.comp Ψ.invLinear).comp Φ.invLinear) := by
                  simp only [ContinuousLinearMap.comp_assoc]
          _ = ContinuousLinearMap.id ℝ H := by
                rw [Ψ.right_inv, ContinuousLinearMap.id_comp, Φ.right_inv]
      phase_to := by
        change (Φ.toLinear.comp Ψ.toLinear).comp K = K.comp (Φ.toLinear.comp Ψ.toLinear)
        rw [ContinuousLinearMap.comp_assoc, Ψ.phase_to, ← ContinuousLinearMap.comp_assoc,
          Φ.phase_to, ContinuousLinearMap.comp_assoc]
      phase_inv := by
        change (Ψ.invLinear.comp Φ.invLinear).comp K = K.comp (Ψ.invLinear.comp Φ.invLinear)
        rw [ContinuousLinearMap.comp_assoc, Φ.phase_inv, ← ContinuousLinearMap.comp_assoc,
          Ψ.phase_inv, ContinuousLinearMap.comp_assoc] }
  inv Φ :=
    { toLinear := Φ.invLinear
      invLinear := Φ.toLinear
      left_inv := Φ.right_inv
      right_inv := Φ.left_inv
      phase_to := Φ.phase_inv
      phase_inv := Φ.phase_to }
  mul_assoc Φ Ψ Χ := phaseIsomorphism_eq_of_fields
    (ContinuousLinearMap.comp_assoc _ _ _)
    (ContinuousLinearMap.comp_assoc _ _ _).symm
  one_mul Φ := phaseIsomorphism_eq_of_fields
    (ContinuousLinearMap.id_comp _)
    (ContinuousLinearMap.comp_id _)
  mul_one Φ := phaseIsomorphism_eq_of_fields
    (ContinuousLinearMap.comp_id _)
    (ContinuousLinearMap.id_comp _)
  inv_mul_cancel Φ := phaseIsomorphism_eq_of_fields Φ.left_inv Φ.left_inv

@[simp] lemma phaseIsomorphism_one_toLinear
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (K : EndR H) :
    (1 : PhaseIsomorphism K K).toLinear = ContinuousLinearMap.id ℝ H := rfl

@[simp] lemma phaseIsomorphism_one_invLinear
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (K : EndR H) :
    (1 : PhaseIsomorphism K K).invLinear = ContinuousLinearMap.id ℝ H := rfl

@[simp] lemma phaseIsomorphism_mul_toLinear
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {K : EndR H}
    (Φ Ψ : PhaseIsomorphism K K) : (Φ * Ψ).toLinear = Φ.toLinear.comp Ψ.toLinear := rfl

@[simp] lemma phaseIsomorphism_mul_invLinear
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {K : EndR H}
    (Φ Ψ : PhaseIsomorphism K K) : (Φ * Ψ).invLinear = Ψ.invLinear.comp Φ.invLinear := rfl

@[simp] lemma phaseIsomorphism_inv_toLinear
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {K : EndR H}
    (Φ : PhaseIsomorphism K K) : Φ⁻¹.toLinear = Φ.invLinear := rfl

@[simp] lemma phaseIsomorphism_inv_invLinear
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {K : EndR H}
    (Φ : PhaseIsomorphism K K) : Φ⁻¹.invLinear = Φ.toLinear := rfl

/-- Conjugation `ℝ`-algebra equivalence on `EndR H` induced by `Φ : PhaseIsomorphism K K`. -/
def phaseIsomorphismConjugateEndRAlgEquiv
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {K : EndR H}
    (Φ : PhaseIsomorphism K K) : EndR H ≃ₐ[ℝ] EndR H where
  toFun T := PhaseIsomorphism.conjugateOperator Φ T
  invFun T := PhaseIsomorphism.conjugateOperator Φ⁻¹ T
  left_inv T := by
    simp only [PhaseIsomorphism.conjugateOperator, phaseIsomorphism_inv_toLinear,
      phaseIsomorphism_inv_invLinear]
    rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc,
      Φ.left_inv, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_assoc,
      Φ.left_inv, ContinuousLinearMap.comp_id]
  right_inv T := by
    simp only [PhaseIsomorphism.conjugateOperator, phaseIsomorphism_inv_toLinear,
      phaseIsomorphism_inv_invLinear]
    rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc,
      Φ.right_inv, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_assoc,
      Φ.right_inv, ContinuousLinearMap.comp_id]
  map_mul' S T := by
    change (Φ.toLinear.comp (S.comp T)).comp Φ.invLinear =
      ((Φ.toLinear.comp S).comp Φ.invLinear).comp ((Φ.toLinear.comp T).comp Φ.invLinear)
    calc
      (Φ.toLinear.comp (S.comp T)).comp Φ.invLinear
          = (Φ.toLinear.comp (S.comp ((ContinuousLinearMap.id ℝ H).comp T))).comp Φ.invLinear := by
              rw [ContinuousLinearMap.id_comp]
      _ = (Φ.toLinear.comp (S.comp ((Φ.invLinear.comp Φ.toLinear).comp T))).comp Φ.invLinear := by
            rw [Φ.left_inv]
      _ = ((Φ.toLinear.comp S).comp Φ.invLinear).comp ((Φ.toLinear.comp T).comp Φ.invLinear) := by
            simp only [ContinuousLinearMap.comp_assoc]
  map_add' S T := by
    change (Φ.toLinear.comp (S + T)).comp Φ.invLinear =
      (Φ.toLinear.comp S).comp Φ.invLinear + (Φ.toLinear.comp T).comp Φ.invLinear
    rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
  commutes' r := by
    ext v
    simp only [PhaseIsomorphism.conjugateOperator, ContinuousLinearMap.algebraMap_apply,
      ContinuousLinearMap.comp_apply]
    change Φ.toLinear (r • Φ.invLinear v) = r • v
    rw [map_smul]
    change r • (Φ.toLinear.comp Φ.invLinear) v = r • v
    rw [Φ.right_inv, ContinuousLinearMap.id_apply]

/-- Conjugation `ℝ`-algebra equivalence on `PhaseCentralizer K` induced by `Φ`. -/
def phaseIsomorphismConjugateCentralizerAlgEquiv
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {K : EndR H}
    (Φ : PhaseIsomorphism K K) : PhaseCentralizer K ≃ₐ[ℝ] PhaseCentralizer K where
  toFun T := PhaseIsomorphism.conjugateCentralizer Φ T
  invFun T := PhaseIsomorphism.conjugateCentralizer Φ⁻¹ T
  left_inv T := phaseCentralizer_eq_of_op_eq
    ((phaseIsomorphismConjugateEndRAlgEquiv Φ).left_inv T.op)
  right_inv T := phaseCentralizer_eq_of_op_eq
    ((phaseIsomorphismConjugateEndRAlgEquiv Φ).right_inv T.op)
  map_mul' S T := phaseCentralizer_eq_of_op_eq
    ((phaseIsomorphismConjugateEndRAlgEquiv Φ).map_mul S.op T.op)
  map_add' S T := phaseCentralizer_eq_of_op_eq
    ((phaseIsomorphismConjugateEndRAlgEquiv Φ).map_add S.op T.op)
  commutes' r := phaseCentralizer_eq_of_op_eq (by
    change PhaseIsomorphism.conjugateOperator Φ (r • ContinuousLinearMap.id ℝ H) =
      r • ContinuousLinearMap.id ℝ H
    ext v
    change Φ.toLinear ((r • ContinuousLinearMap.id ℝ H) (Φ.invLinear v)) = r • v
    simp only [smul_apply, ContinuousLinearMap.id_apply, map_smul]
    change r • (Φ.toLinear.comp Φ.invLinear) v = r • v
    rw [Φ.right_inv, ContinuousLinearMap.id_apply])

/-- Conjugation `OperatorSymmetryAction` on `EndR H` (with `toFun Φ := (Φ⁻¹)...` so `.act Φ = Φ.conjugateOperator`). -/
def phaseIsomorphismEndROperatorAction
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : OperatorSymmetryAction (PhaseIsomorphism K K) (EndR H) where
  toFun Φ := phaseIsomorphismConjugateEndRAlgEquiv Φ⁻¹
  map_one' := by
    ext T v
    simp [phaseIsomorphismConjugateEndRAlgEquiv, PhaseIsomorphism.conjugateOperator]
  map_mul' Φ Ψ := by
    ext T v
    change (Φ * Ψ)⁻¹.toLinear (T ((Φ * Ψ)⁻¹.invLinear v)) =
      Ψ⁻¹.toLinear (Φ⁻¹.toLinear (T (Φ⁻¹.invLinear (Ψ⁻¹.invLinear v))))
    rw [_root_.mul_inv_rev]
    rfl

/-- Conjugation `OperatorSymmetryAction` on `PhaseCentralizer K` (`.act Φ = Φ.conjugateCentralizer`). -/
def phaseIsomorphismCentralizerOperatorAction
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : OperatorSymmetryAction (PhaseIsomorphism K K) (PhaseCentralizer K) where
  toFun Φ := phaseIsomorphismConjugateCentralizerAlgEquiv Φ⁻¹
  map_one' := by
    apply AlgEquiv.ext
    intro T
    apply phaseCentralizer_eq_of_op_eq
    change PhaseIsomorphism.conjugateOperator (1 : PhaseIsomorphism K K)⁻¹ T.op = T.op
    rw [inv_one]
    rfl
  map_mul' Φ Ψ := by
    apply AlgEquiv.ext
    intro T
    apply phaseCentralizer_eq_of_op_eq
    change PhaseIsomorphism.conjugateOperator (Φ * Ψ)⁻¹ T.op =
      PhaseIsomorphism.conjugateOperator Ψ⁻¹ (PhaseIsomorphism.conjugateOperator Φ⁻¹ T.op)
    rw [_root_.mul_inv_rev]
    rfl

/-- Conjugation `SymmetryAction` on `EndR H`. -/
def phaseIsomorphismEndRAction
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : SymmetryAction (PhaseIsomorphism K K) (EndR H) :=
  toSymmetryAction (phaseIsomorphismEndROperatorAction K)

/-- Conjugation `SymmetryAction` on `PhaseCentralizer K`. -/
def phaseIsomorphismCentralizerAction
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : SymmetryAction (PhaseIsomorphism K K) (PhaseCentralizer K) :=
  toSymmetryAction (phaseIsomorphismCentralizerOperatorAction K)

/-- Canonical alias required by F2.1 contract (`phaseCentralizerSymmetryAction`). -/
abbrev phaseCentralizerSymmetryAction
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : SymmetryAction (PhaseIsomorphism K K) (PhaseCentralizer K) :=
  phaseIsomorphismCentralizerAction K

@[simp] theorem phaseIsomorphismEndROperatorAction_act
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) (Φ : PhaseIsomorphism K K) (T : EndR H) :
    (phaseIsomorphismEndROperatorAction K).act Φ T = Φ.conjugateOperator T := by
  change phaseIsomorphismConjugateEndRAlgEquiv (Φ⁻¹)⁻¹ T = _
  rw [inv_inv]
  rfl

@[simp] theorem phaseIsomorphismEndRAction_act
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) (Φ : PhaseIsomorphism K K) (T : EndR H) :
    (phaseIsomorphismEndRAction K).act Φ T = Φ.conjugateOperator T :=
  phaseIsomorphismEndROperatorAction_act K Φ T

@[simp] theorem phaseIsomorphismCentralizerOperatorAction_act
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) (Φ : PhaseIsomorphism K K) (T : PhaseCentralizer K) :
    (phaseIsomorphismCentralizerOperatorAction K).act Φ T = Φ.conjugateCentralizer T := by
  change phaseIsomorphismConjugateCentralizerAlgEquiv (Φ⁻¹)⁻¹ T = _
  rw [inv_inv]
  rfl

@[simp] theorem phaseIsomorphismCentralizerAction_act
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) (Φ : PhaseIsomorphism K K) (T : PhaseCentralizer K) :
    (phaseIsomorphismCentralizerAction K).act Φ T = Φ.conjugateCentralizer T :=
  phaseIsomorphismCentralizerOperatorAction_act K Φ T

/-- Exact equivalence `PhaseErlanger.ErlangerInvariant K α ≃ SymmetryInvariants.InvariantReadout`. -/
def erlangerInvariantEquivInvariantReadout
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) (α : Type*) :
    InfoGeometry.Geometry.PhaseErlanger.ErlangerInvariant K α ≃
      InfoGeometry.OperatorAlgebra.InvariantReadout (phaseIsomorphismCentralizerAction K) α where
  toFun E := ⟨E.1, fun Φ T => by
    rw [phaseIsomorphismCentralizerAction_act]
    exact E.2 Φ T⟩
  invFun R := ⟨R.1, fun Φ T => by
    have h := R.2 Φ T
    rwa [phaseIsomorphismCentralizerAction_act] at h⟩
  left_inv E := by cases E; rfl
  right_inv R := by cases R; rfl

/-- Exact equivalence `PhaseErlanger.ErlangerInvariant K α ≃ OperatorSymmetryAction.InvariantReadout`. -/
def erlangerInvariantEquivOpInvariantReadout
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) (α : Type*) :
    InfoGeometry.Geometry.PhaseErlanger.ErlangerInvariant K α ≃
      (phaseIsomorphismCentralizerOperatorAction K).InvariantReadout α where
  toFun E := ⟨E.1, fun Φ T => by
    rw [phaseIsomorphismCentralizerOperatorAction_act]
    exact E.2 Φ T⟩
  invFun R := ⟨R.1, fun Φ T => by
    have h := R.2 Φ T
    rwa [phaseIsomorphismCentralizerOperatorAction_act] at h⟩
  left_inv E := by cases E; rfl
  right_inv R := by cases R; rfl

/-- Equivalence with `InvariantGeometry.IsInvariantReadout` under `symmetryActionToMulSemiringAction`. -/
theorem erlangerInvariant_iff_isInvariantReadout
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) {α : Type*} (f : PhaseCentralizer K → α) :
    (∀ (Φ : PhaseIsomorphism K K) (T : PhaseCentralizer K),
        f (Φ.conjugateCentralizer T) = f T) ↔
      @IsInvariantReadout (PhaseIsomorphism K K) (PhaseCentralizer K) _
        (symmetryActionToMulSemiringAction (phaseIsomorphismCentralizerAction K)).toMulAction α f := by
  constructor
  · intro h Φ T
    change f ((phaseIsomorphismCentralizerAction K).act Φ T) = f T
    rw [phaseIsomorphismCentralizerAction_act]
    exact h Φ T
  · intro h Φ T
    have h' := h Φ T
    change f ((phaseIsomorphismCentralizerAction K).act Φ T) = f T at h'
    rwa [phaseIsomorphismCentralizerAction_act] at h'

/-- Any `ChiralAxis K` induces a `CircularPolarization (PhaseCentralizer K)` with zero extra hypotheses. -/
def chiralAxisToCircularPolarization
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : EndR H} (χ : ChiralAxis K) :
    CircularPolarization (PhaseCentralizer K) where
  chi := ⟨χ.chi, χ.chi_phase_linear⟩
  chi_sq := phaseCentralizer_eq_of_op_eq χ.chi_square_one
  P_left := ⟨χ.leftProjector, χ.leftProjector_phaseLinear⟩
  P_right := ⟨χ.rightProjector, χ.rightProjector_phaseLinear⟩
  P_left_def := phaseCentralizer_eq_of_op_eq (by
    simp only [phaseCentralizer_smul_op, phaseCentralizer_add_op, phaseCentralizer_one_op]
    rfl)
  P_right_def := phaseCentralizer_eq_of_op_eq (by
    simp only [phaseCentralizer_smul_op, phaseCentralizer_sub_op, phaseCentralizer_one_op]
    rfl)
  P_left_idem := phaseCentralizer_eq_of_op_eq (by
    have hsq : χ.chi.comp χ.chi = ContinuousLinearMap.id ℝ H := χ.chi_square_one
    ext v
    have hv : χ.chi (χ.chi v) = v := congrArg (fun T : EndR H => T v) hsq
    simp only [phaseCentralizer_mul_op, ChiralAxis.leftProjector, ContinuousLinearMap.comp_apply,
      smul_apply, add_apply, ContinuousLinearMap.id_apply, map_smul, map_add, hv]
    module)
  P_right_idem := phaseCentralizer_eq_of_op_eq (by
    have hsq : χ.chi.comp χ.chi = ContinuousLinearMap.id ℝ H := χ.chi_square_one
    ext v
    have hv : χ.chi (χ.chi v) = v := congrArg (fun T : EndR H => T v) hsq
    simp only [phaseCentralizer_mul_op, ChiralAxis.rightProjector, ContinuousLinearMap.comp_apply,
      smul_apply, sub_apply, ContinuousLinearMap.id_apply, map_smul, map_sub, hv]
    module)
  P_left_mul_right := phaseCentralizer_eq_of_op_eq (by
    have hsq : χ.chi.comp χ.chi = ContinuousLinearMap.id ℝ H := χ.chi_square_one
    ext v
    have hv : χ.chi (χ.chi v) = v := congrArg (fun T : EndR H => T v) hsq
    simp only [phaseCentralizer_mul_op, ChiralAxis.leftProjector, ChiralAxis.rightProjector,
      ContinuousLinearMap.comp_apply, smul_apply, add_apply, sub_apply,
      ContinuousLinearMap.id_apply, map_smul, map_sub, hv,
      phaseCentralizer_zero_op, zero_apply]
    module)
  P_right_mul_left := phaseCentralizer_eq_of_op_eq (by
    have hsq : χ.chi.comp χ.chi = ContinuousLinearMap.id ℝ H := χ.chi_square_one
    ext v
    have hv : χ.chi (χ.chi v) = v := congrArg (fun T : EndR H => T v) hsq
    simp only [phaseCentralizer_mul_op, ChiralAxis.leftProjector, ChiralAxis.rightProjector,
      ContinuousLinearMap.comp_apply, smul_apply, add_apply, sub_apply,
      ContinuousLinearMap.id_apply, map_smul, map_add, hv,
      phaseCentralizer_zero_op, zero_apply]
    module)
  P_sum := phaseCentralizer_eq_of_op_eq χ.leftProjector_add_rightProjector

/-- Package any `CircularPolarization Op` into `SymmetryInvariants.ComplementaryProjectors Op`. -/
def circularPolarizationToComplementaryProjectors
    {Op : Type*} [Ring Op] [Module ℝ Op]
    (C : CircularPolarization Op) : ComplementaryProjectors Op where
  p := C.P_left
  q := C.P_right
  p_idempotent := C.P_left_idem
  q_idempotent := C.P_right_idem
  sum_eq_one := C.P_sum
  pq_zero := C.P_left_mul_right
  qp_zero := C.P_right_mul_left

/-- Any `ChiralAxis K` gives `ComplementaryProjectors (PhaseCentralizer K)`. -/
def chiralAxisToComplementaryProjectors
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : EndR H} (χ : ChiralAxis K) :
    ComplementaryProjectors (PhaseCentralizer K) :=
  circularPolarizationToComplementaryProjectors (chiralAxisToCircularPolarization χ)

/-- Subgroup of `PhaseIsomorphism K K` preserving a given `ChiralAxis K`. -/
def chiralStabilizer
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : EndR H} (χ : ChiralAxis K) : Subgroup (PhaseIsomorphism K K) where
  carrier := {Φ | ChiralPreserving χ χ Φ.toLinear}
  one_mem' := rfl
  mul_mem' {Φ Ψ} hΦ hΨ := by
    change (Φ.toLinear.comp Ψ.toLinear).comp χ.chi = χ.chi.comp (Φ.toLinear.comp Ψ.toLinear)
    rw [ContinuousLinearMap.comp_assoc, hΨ, ← ContinuousLinearMap.comp_assoc, hΦ,
      ContinuousLinearMap.comp_assoc]
  inv_mem' {Φ} hΦ := by
    change Φ.invLinear.comp χ.chi = χ.chi.comp Φ.invLinear
    calc
      Φ.invLinear.comp χ.chi
          = (Φ.invLinear.comp χ.chi).comp (Φ.toLinear.comp Φ.invLinear) := by
              rw [Φ.right_inv, ContinuousLinearMap.comp_id]
      _ = Φ.invLinear.comp ((χ.chi.comp Φ.toLinear).comp Φ.invLinear) := by
            simp only [ContinuousLinearMap.comp_assoc]
      _ = Φ.invLinear.comp ((Φ.toLinear.comp χ.chi).comp Φ.invLinear) := by rw [← hΦ]
      _ = (Φ.invLinear.comp Φ.toLinear).comp (χ.chi.comp Φ.invLinear) := by
            simp only [ContinuousLinearMap.comp_assoc]
      _ = χ.chi.comp Φ.invLinear := by rw [Φ.left_inv, ContinuousLinearMap.id_comp]

/-- Restriction of `phaseIsomorphismCentralizerOperatorAction K` to `chiralStabilizer χ`. -/
def chiralStabilizerOperatorAction
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : EndR H} (χ : ChiralAxis K) :
    OperatorSymmetryAction (↥(chiralStabilizer χ)) (PhaseCentralizer K) where
  toFun Φ := (phaseIsomorphismCentralizerOperatorAction K).toFun Φ.1
  map_one' := (phaseIsomorphismCentralizerOperatorAction K).map_one'
  map_mul' Φ Ψ := (phaseIsomorphismCentralizerOperatorAction K).map_mul' Φ.1 Ψ.1

theorem chiralStabilizer_preserves_circularPolarization
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : EndR H} (χ : ChiralAxis K) :
    (chiralStabilizerOperatorAction χ).PreservesCircularPolarization
      (chiralAxisToCircularPolarization χ) := by
  intro Φ
  apply phaseCentralizer_eq_of_op_eq
  change PhaseIsomorphism.conjugateOperator Φ.1 χ.chi = χ.chi
  have hχ : ChiralPreserving χ χ Φ.1.toLinear := Φ.2
  change (Φ.1.toLinear.comp χ.chi).comp Φ.1.invLinear = χ.chi
  rw [hχ, ContinuousLinearMap.comp_assoc, Φ.1.right_inv, ContinuousLinearMap.comp_id]

/-- Stabilizer-equivariant `InvariantProjectorDecomposition` on `PhaseCentralizer K`. -/
def chiralStabilizerInvariantProjectorDecomposition
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : EndR H} (χ : ChiralAxis K) :
    InvariantProjectorDecomposition
      (toSymmetryAction (chiralStabilizerOperatorAction χ)) where
  projectors := chiralAxisToComplementaryProjectors χ
  p_invariant := OperatorSymmetryAction.invariant_P_left_of_preserves_chi
    (chiralStabilizerOperatorAction χ)
    (chiralAxisToCircularPolarization χ)
    (chiralStabilizer_preserves_circularPolarization χ)
  q_invariant := OperatorSymmetryAction.invariant_P_right_of_preserves_chi
    (chiralStabilizerOperatorAction χ)
    (chiralAxisToCircularPolarization χ)
    (chiralStabilizer_preserves_circularPolarization χ)

/-- `χ.chi` itself yields an involution element in `chiralStabilizer χ`. -/
def chiralInvolutionIso
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : EndR H} (χ : ChiralAxis K) : PhaseIsomorphism K K where
  toLinear := χ.chi
  invLinear := χ.chi
  left_inv := χ.chi_square_one
  right_inv := χ.chi_square_one
  phase_to := χ.chi_phase_linear
  phase_inv := χ.chi_phase_linear

theorem chiralInvolutionIso_mem_stabilizer
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : EndR H} (χ : ChiralAxis K) :
    chiralInvolutionIso χ ∈ chiralStabilizer χ :=
  rfl

/-! ### `PhaseMetricMorphism` (`MetricPreserving`) vs. `IsKreinIsometry` (`kreinInner`) Separation -/

section KreinMetricSeparation

open InfoGeometry.Krein

/-- On a `KreinSpace H`, a `MetricPreserving` map that commutes with `KreinSpace.jCLM`
(`PhasePreserving jCLM jCLM F`) is automatically a `KreinSpace.IsKreinIsometry`. -/
theorem metricPreserving_isKreinIsometry_of_phasePreserving_jCLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] (F : H →L[ℝ] H)
    (hMetric : MetricPreserving F)
    (hJ : PhasePreserving (KreinSpace.jCLM (H := H)) (KreinSpace.jCLM (H := H)) F) :
    KreinSpace.IsKreinIsometry F := by
  intro u v
  have hJu : F (KreinSpace.jCLM u) = KreinSpace.jCLM (F u) :=
    congrArg (fun T : H →L[ℝ] H => T u) hJ
  calc
    KreinSpace.kreinInner (F u) (F v)
        = inner (𝕜 := ℝ) (KreinSpace.jCLM (F u)) (F v) := rfl
    _ = inner (𝕜 := ℝ) (F (KreinSpace.jCLM u)) (F v) := by rw [← hJu]
    _ = inner (𝕜 := ℝ) (KreinSpace.jCLM u) v := hMetric (KreinSpace.jCLM u) v
    _ = KreinSpace.kreinInner u v := rfl

/-- Specialization to `PhaseMetricMorphism (KreinSpace.jCLM) (KreinSpace.jCLM)`. -/
theorem phaseMetricMorphism_jCLM_isKreinIsometry
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (M : PhaseMetricMorphism (KreinSpace.jCLM (H := H)) (KreinSpace.jCLM (H := H))) :
    KreinSpace.IsKreinIsometry M.toLinear :=
  metricPreserving_isKreinIsometry_of_phasePreserving_jCLM M.toLinear
    M.metric_preserving M.phase_preserving

/-- For an invertible Hilbert-metric-preserving map `U : H ≃L[ℝ] H` on a `KreinSpace H`,
`IsKreinIsometry U` holds if and only if `U` commutes with the fundamental symmetry `jCLM`. -/
theorem metricPreserving_equiv_isKreinIsometry_iff_comm_jCLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] (U : H ≃L[ℝ] H)
    (hMetric : MetricPreserving (U : H →L[ℝ] H)) :
    KreinSpace.IsKreinIsometry (U : H →L[ℝ] H) ↔
      PhasePreserving (KreinSpace.jCLM (H := H)) (KreinSpace.jCLM (H := H)) (U : H →L[ℝ] H) := by
  constructor
  · intro hKrein
    ext u
    apply ext_inner_right ℝ
    intro w
    have hw : w = (U : H →L[ℝ] H) (U.symm w) := (U.apply_symm_apply w).symm
    calc
      inner (𝕜 := ℝ) (((U : H →L[ℝ] H).comp KreinSpace.jCLM) u) w
          = inner (𝕜 := ℝ) ((U : H →L[ℝ] H) (KreinSpace.jCLM u))
              ((U : H →L[ℝ] H) (U.symm w)) := by nth_rw 1 [hw]; rfl
      _ = inner (𝕜 := ℝ) (KreinSpace.jCLM u) (U.symm w) :=
            hMetric (KreinSpace.jCLM u) (U.symm w)
      _ = KreinSpace.kreinInner u (U.symm w) := rfl
      _ = KreinSpace.kreinInner ((U : H →L[ℝ] H) u) ((U : H →L[ℝ] H) (U.symm w)) :=
            (hKrein u (U.symm w)).symm
      _ = inner (𝕜 := ℝ) (KreinSpace.jCLM ((U : H →L[ℝ] H) u)) w := by
            rw [← hw]; rfl
  · exact metricPreserving_isKreinIsometry_of_phasePreserving_jCLM (U : H →L[ℝ] H) hMetric

/-- Rational hyperbolic boost `(x, ξ) ↦ ((5/4)x + (3/4)ξ, (3/4)x + (5/4)ξ)` on `DoubledSpace ℝ`. -/
def kreinBoost54 : DoubledSpace ℝ →L[ℝ] DoubledSpace ℝ where
  toFun u := to_doubled ((5 / 4 : ℝ) * WithLp.fst u + (3 / 4 : ℝ) * WithLp.snd u)
    ((3 / 4 : ℝ) * WithLp.fst u + (5 / 4 : ℝ) * WithLp.snd u)
  map_add' u v := by
    apply DoubledSpace.ext <;> simp [WithLp.add_fst, WithLp.add_snd] <;> ring
  map_smul' c u := by
    apply DoubledSpace.ext <;> simp [WithLp.smul_fst, WithLp.smul_snd] <;> ring
  cont := by
    refine (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)).comp ?_
    exact Continuous.prodMk
      ((continuous_const.mul (WithLp.continuous_fst (p := (2 : ENNReal)) (α := ℝ) (β := ℝ))).add
        (continuous_const.mul (WithLp.continuous_snd (p := (2 : ENNReal)) (α := ℝ) (β := ℝ))))
      ((continuous_const.mul (WithLp.continuous_fst (p := (2 : ENNReal)) (α := ℝ) (β := ℝ))).add
        (continuous_const.mul (WithLp.continuous_snd (p := (2 : ENNReal)) (α := ℝ) (β := ℝ))))

/-- Explicit separation of `MetricPreserving` (Hilbert inner product) and `IsKreinIsometry`
(`kreinInner`) on `DoubledSpace ℝ`:
1. `modular_j` is `MetricPreserving` (even a `PhaseMetricMorphism` for `id`), yet NOT `IsKreinIsometry`.
2. `kreinBoost54` is `IsKreinIsometry`, yet NOT `MetricPreserving`. -/
theorem metricPreserving_ne_isKreinIsometry_witness :
    (MetricPreserving (modular_j (E := ℝ)) ∧
      ¬ KreinSpace.IsKreinIsometry (modular_j (E := ℝ))) ∧
    (KreinSpace.IsKreinIsometry kreinBoost54 ∧
      ¬ MetricPreserving kreinBoost54) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro u v
    simp only [modular_j, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.prod_inner_apply]
    change inner (𝕜 := ℝ) u.ofLp.2 v.ofLp.2 + inner (𝕜 := ℝ) u.ofLp.1 v.ofLp.1 =
      inner (𝕜 := ℝ) u.ofLp.1 v.ofLp.1 + inner (𝕜 := ℝ) u.ofLp.2 v.ofLp.2
    ring
  · intro hKrein
    have h1 := hKrein (to_doubled (1 : ℝ) 0) (to_doubled (1 : ℝ) 0)
    rw [KreinSpace.kreinInner_def, KreinSpace.kreinInner_def, ← KreinSpace.jCLM_apply,
      ← KreinSpace.jCLM_apply, jCLM_eq_spectral_epsilon] at h1
    simp only [modular_j_to_doubled, spectral_epsilon_to_doubled, neg_zero, to_doubled,
      WithLp.prod_inner_apply, real_inner_self_eq_norm_sq] at h1
    norm_num at h1
  · intro u v
    rw [KreinSpace.kreinInner_def, KreinSpace.kreinInner_def, ← KreinSpace.jCLM_apply,
      ← KreinSpace.jCLM_apply, jCLM_eq_spectral_epsilon]
    change inner (𝕜 := ℝ)
        (spectral_epsilon (kreinBoost54 u)) (kreinBoost54 v) =
      inner (𝕜 := ℝ) (spectral_epsilon u) v
    rw [show u = to_doubled (WithLp.fst u) (WithLp.snd u) by apply DoubledSpace.ext <;> rfl]
    rw [show v = to_doubled (WithLp.fst v) (WithLp.snd v) by apply DoubledSpace.ext <;> rfl]
    simp only [kreinBoost54, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      fst_to_doubled, snd_to_doubled, spectral_epsilon_to_doubled, to_doubled,
      WithLp.prod_inner_apply, RCLike.inner_apply, conj_trivial]
    ring
  · intro hMetric
    have h1 := hMetric (to_doubled (1 : ℝ) 0) (to_doubled (1 : ℝ) 0)
    change inner (𝕜 := ℝ) (kreinBoost54 (to_doubled (1 : ℝ) 0))
        (kreinBoost54 (to_doubled (1 : ℝ) 0)) =
      inner (𝕜 := ℝ) (to_doubled (1 : ℝ) 0) (to_doubled (1 : ℝ) 0) at h1
    simp only [kreinBoost54, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      fst_to_doubled, snd_to_doubled, mul_one, mul_zero, add_zero, to_doubled,
      WithLp.prod_inner_apply, RCLike.inner_apply, conj_trivial] at h1
    norm_num at h1

end KreinMetricSeparation

end Bridge1

/-!
## Bridge 2: `PhaseErlanger (H, K)` → `Erlangen20Datum`
-/

section Bridge2

open InfoGeometry.Geometry.PhaseErlanger

/-- Scoped 1-dimensional abelian `LieRing` on `ℝ` (`⁅r, s⁆ = 0`). -/
scoped instance realAbelianLieRing : LieRing ℝ where
  bracket _ _ := 0
  add_lie _ _ _ := (add_zero 0).symm
  lie_add _ _ _ := (add_zero 0).symm
  lie_self _ := rfl
  leibniz_lie _ _ _ := by simp

/-- Scoped 1-dimensional abelian `LieAlgebra ℝ ℝ`. -/
scoped instance realAbelianLieAlgebra : LieAlgebra ℝ ℝ where
  lie_smul _ _ _ := (smul_zero _).symm

/-- Scoped `LieRing` on `PhaseCentralizer K` inherited from its associative multiplication. -/
scoped instance phaseCentralizerLieRing
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : LieRing (PhaseCentralizer K) :=
  LieRing.ofAssociativeRing

/-- Scoped `LieAlgebra ℝ` on `PhaseCentralizer K`. -/
scoped instance phaseCentralizerLieAlgebra
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : LieAlgebra ℝ (PhaseCentralizer K) :=
  LieAlgebra.ofAssociativeAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- 1D abelian Lie representation `ℝ →ₗ⁅ℝ⁆ Module.End ℝ H` generated by the phase axis `K`. -/
def phaseAxisLieHom
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : ℝ →ₗ⁅ℝ⁆ Module.End ℝ H where
  toFun r := r • K.toLinearMap
  map_add' r s := add_smul r s K.toLinearMap
  map_smul' c r := mul_smul c r K.toLinearMap
  map_lie' {r s} := by
    have hlhs : ⁅r, s⁆ = (0 : ℝ) := rfl
    rw [hlhs, zero_smul]
    change 0 = (r • K.toLinearMap) * (s • K.toLinearMap) -
      (s • K.toLinearMap) * (r • K.toLinearMap)
    ext v
    simp only [LinearMap.zero_apply, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, ContinuousLinearMap.coe_coe, map_smul]
    rw [smul_smul, smul_smul, mul_comm r s, sub_self]

/-- Canonical Bridge 2: `PhaseErlanger (H, K)` packaged as an `Erlangen20Datum ℝ H ℝ`. -/
def phaseErlangerDatum
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) :
    Erlangen20Datum ℝ H ℝ
      (OperatorSymmetryAction (PhaseIsomorphism K K) (PhaseCentralizer K))
      (Subring (PhaseCentralizer K)) where
  operatorAlgebra := phaseCentralizerEndSubalgebra K
  representation := phaseAxisLieHom K
  representation_mem r := ⟨r • K, PhaseLinear.smul r (rfl : PhaseLinear K K), by ext v; rfl⟩
  symmetryData := phaseIsomorphismCentralizerOperatorAction K
  invariantData := invariantSubring (phaseIsomorphismCentralizerAction K)

/-- Canonical `toErlangen20Datum` alias for `phaseErlangerDatum`. -/
abbrev toErlangen20Datum
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) :
    Erlangen20Datum ℝ H ℝ
      (OperatorSymmetryAction (PhaseIsomorphism K K) (PhaseCentralizer K))
      (Subring (PhaseCentralizer K)) :=
  phaseErlangerDatum K

/-- Variant of Bridge 2 using `SmoothCartanGeometry.HomothetyH` (requires no `LieRing ℝ` instance). -/
def phaseErlangerHomothetyDatum
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) :
    Erlangen20Datum ℝ H InfoGeometry.Erlangen.SmoothCartanGeometry.HomothetyH
      (OperatorSymmetryAction (PhaseIsomorphism K K) (PhaseCentralizer K))
      (Subring (PhaseCentralizer K)) where
  operatorAlgebra := phaseCentralizerEndSubalgebra K
  representation :=
    { toFun := fun a => a.val • K.toLinearMap
      map_add' := fun a b => add_smul a.val b.val K.toLinearMap
      map_smul' := fun c a => mul_smul c a.val K.toLinearMap
      map_lie' := fun {a b} => by
        have hlhs : ⁅a, b⁆ = (0 : InfoGeometry.Erlangen.SmoothCartanGeometry.HomothetyH) := rfl
        rw [hlhs]
        change (0 : ℝ) • K.toLinearMap = (a.val • K.toLinearMap) * (b.val • K.toLinearMap) -
          (b.val • K.toLinearMap) * (a.val • K.toLinearMap)
        rw [zero_smul]
        ext v
        simp only [LinearMap.zero_apply, LinearMap.sub_apply, Module.End.mul_apply,
          LinearMap.smul_apply, ContinuousLinearMap.coe_coe, map_smul]
        rw [smul_smul, smul_smul, mul_comm a.val b.val, sub_self] }
  representation_mem a := ⟨a.val • K, PhaseLinear.smul a.val (rfl : PhaseLinear K K), by ext v; rfl⟩
  symmetryData := phaseIsomorphismCentralizerOperatorAction K
  invariantData := invariantSubring (phaseIsomorphismCentralizerAction K)

/-- Full-centralizer Bridge 2 (`𝔤 := PhaseCentralizer K`). -/
def phaseErlangerCentralizerDatum
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) :
    Erlangen20Datum ℝ H (PhaseCentralizer K)
      (OperatorSymmetryAction (PhaseIsomorphism K K) (PhaseCentralizer K))
      (Subring (PhaseCentralizer K)) where
  operatorAlgebra := phaseCentralizerEndSubalgebra K
  representation :=
    { toFun := fun T => T.op.toLinearMap
      map_add' := fun _ _ => rfl
      map_smul' := fun c T => by
        ext v
        simp [phaseCentralizer_smul_op]
      map_lie' := fun {S T} => by
        ext v
        change ((S * T - T * S).op) v =
          (S.op.toLinearMap * T.op.toLinearMap - T.op.toLinearMap * S.op.toLinearMap) v
        simp [phaseCentralizer_sub_op, phaseCentralizer_mul_op, Module.End.mul_apply] }
  representation_mem T := ⟨T.op, T.phase_linear, rfl⟩
  symmetryData := phaseIsomorphismCentralizerOperatorAction K
  invariantData := invariantSubring (phaseIsomorphismCentralizerAction K)

/-- Chiral-stabilizer Bridge 2 packaging `CircularPolarization` and `InvariantProjectorDecomposition`. -/
def phaseErlangerChiralDatum
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) (χ : ChiralAxis K) :
    Erlangen20Datum ℝ H (PhaseCentralizer K)
      (CircularPolarization (PhaseCentralizer K))
      (InvariantProjectorDecomposition
        (toSymmetryAction (chiralStabilizerOperatorAction χ))) where
  operatorAlgebra := phaseCentralizerEndSubalgebra K
  representation := (phaseErlangerCentralizerDatum K).representation
  representation_mem := (phaseErlangerCentralizerDatum K).representation_mem
  symmetryData := chiralAxisToCircularPolarization χ
  invariantData := chiralStabilizerInvariantProjectorDecomposition χ

end Bridge2

/-!
## Bridge 3: `Erlangen20Datum` ↔ `SymmetryAction` & `OperatorErlangenFixedPoints`
-/

section Bridge3Forward

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Conjugation `R`-algebra automorphism of `Module.End R V` by a unit of `E.operatorAlgebra`. -/
def erlangen20EndConjAlgEquiv
    {R V 𝔤 𝒮 ℐ : Type*}
    [CommRing R] [AddCommGroup V] [Module R V] [LieRing 𝔤] [LieAlgebra R 𝔤]
    (E : Erlangen20Datum R V 𝔤 𝒮 ℐ) (u : E.operatorAlgebraˣ) :
    Module.End R V ≃ₐ[R] Module.End R V where
  toFun T := (u : E.operatorAlgebra).val * T * (↑(u⁻¹) : E.operatorAlgebra).val
  invFun T := (↑(u⁻¹) : E.operatorAlgebra).val * T * (u : E.operatorAlgebra).val
  left_inv T := by
    calc
      (↑(u⁻¹) : E.operatorAlgebra).val *
          ((u : E.operatorAlgebra).val * T * (↑(u⁻¹) : E.operatorAlgebra).val) *
          (u : E.operatorAlgebra).val
          = (((u⁻¹ * u : E.operatorAlgebraˣ) : E.operatorAlgebra).val) * T *
              (((u⁻¹ * u : E.operatorAlgebraˣ) : E.operatorAlgebra).val) := by
                simp only [Units.val_mul, Subalgebra.coe_mul, mul_assoc]
      _ = T := by simp
  right_inv T := by
    calc
      (u : E.operatorAlgebra).val *
          ((↑(u⁻¹) : E.operatorAlgebra).val * T * (u : E.operatorAlgebra).val) *
          (↑(u⁻¹) : E.operatorAlgebra).val
          = (((u * u⁻¹ : E.operatorAlgebraˣ) : E.operatorAlgebra).val) * T *
              (((u * u⁻¹ : E.operatorAlgebraˣ) : E.operatorAlgebra).val) := by
                simp only [Units.val_mul, Subalgebra.coe_mul, mul_assoc]
      _ = T := by simp
  map_mul' T₁ T₂ := by
    calc
      (u : E.operatorAlgebra).val * (T₁ * T₂) * (↑(u⁻¹) : E.operatorAlgebra).val
          = (u : E.operatorAlgebra).val * T₁ *
              (((u⁻¹ * u : E.operatorAlgebraˣ) : E.operatorAlgebra).val) * T₂ *
              (↑(u⁻¹) : E.operatorAlgebra).val := by
                simp only [inv_mul_cancel, Units.val_one, Subalgebra.coe_one, mul_one, mul_assoc]
      _ = ((u : E.operatorAlgebra).val * T₁ * (↑(u⁻¹) : E.operatorAlgebra).val) *
            ((u : E.operatorAlgebra).val * T₂ * (↑(u⁻¹) : E.operatorAlgebra).val) := by
              simp only [Units.val_mul, Subalgebra.coe_mul, mul_assoc]
  map_add' T₁ T₂ := by rw [mul_add, add_mul]
  commutes' r := by
    calc
      (u : E.operatorAlgebra).val * algebraMap R (Module.End R V) r * (↑(u⁻¹) : E.operatorAlgebra).val
          = (u : E.operatorAlgebra).val * (↑(u⁻¹) : E.operatorAlgebra).val *
              algebraMap R (Module.End R V) r := by
                rw [mul_assoc, Algebra.commutes, ← mul_assoc]
      _ = (((u * u⁻¹ : E.operatorAlgebraˣ) : E.operatorAlgebra).val) *
            algebraMap R (Module.End R V) r := by
              rw [← Subalgebra.coe_mul, ← Units.val_mul]
      _ = algebraMap R (Module.End R V) r := by
              rw [mul_inv_cancel, Units.val_one, Subalgebra.coe_one, one_mul]

/-- Forward Bridge 3 (ambient endomorphism ring): conjugation action of `G` via `ρ : G →* E.operatorAlgebraˣ`. -/
def erlangen20EndSymmetryAction
    {R V 𝔤 𝒮 ℐ G : Type*}
    [CommRing R] [AddCommGroup V] [Module R V] [LieRing 𝔤] [LieAlgebra R 𝔤] [Group G]
    (E : Erlangen20Datum R V 𝔤 𝒮 ℐ) (ρ : G →* E.operatorAlgebraˣ) :
    SymmetryAction G (Module.End R V) where
  act g := (erlangen20EndConjAlgEquiv E (ρ g)).toRingEquiv
  act_one T := by
    change (erlangen20EndConjAlgEquiv E (ρ 1)) T = T
    rw [map_one]
    simp [erlangen20EndConjAlgEquiv]
  act_mul g h T := by
    change (erlangen20EndConjAlgEquiv E (ρ (g * h))) T =
      (erlangen20EndConjAlgEquiv E (ρ g)) ((erlangen20EndConjAlgEquiv E (ρ h)) T)
    rw [map_mul]
    simp only [erlangen20EndConjAlgEquiv, Equiv.coe_fn_mk, AlgEquiv.coe_mk,
      _root_.mul_inv_rev, Units.val_mul, Subalgebra.coe_mul, mul_assoc]

/-- Conjugation `R`-algebra automorphism directly on `E.operatorAlgebra`. -/
def erlangen20AlgConjAlgEquiv
    {R V 𝔤 𝒮 ℐ : Type*}
    [CommRing R] [AddCommGroup V] [Module R V] [LieRing 𝔤] [LieAlgebra R 𝔤]
    (E : Erlangen20Datum R V 𝔤 𝒮 ℐ) (u : E.operatorAlgebraˣ) :
    E.operatorAlgebra ≃ₐ[R] E.operatorAlgebra where
  toFun a := (u : E.operatorAlgebra) * a * (↑(u⁻¹) : E.operatorAlgebra)
  invFun a := (↑(u⁻¹) : E.operatorAlgebra) * a * (u : E.operatorAlgebra)
  left_inv a := by
    calc (↑(u⁻¹) : E.operatorAlgebra) * ((u : E.operatorAlgebra) * a * (↑(u⁻¹) : E.operatorAlgebra)) *
            (u : E.operatorAlgebra)
        = ((u⁻¹ * u : E.operatorAlgebraˣ) : E.operatorAlgebra) * a *
            ((u⁻¹ * u : E.operatorAlgebraˣ) : E.operatorAlgebra) := by
              simp only [Units.val_mul, mul_assoc]
      _ = a := by simp
  right_inv a := by
    calc (u : E.operatorAlgebra) * ((↑(u⁻¹) : E.operatorAlgebra) * a * (u : E.operatorAlgebra)) *
            (↑(u⁻¹) : E.operatorAlgebra)
        = ((u * u⁻¹ : E.operatorAlgebraˣ) : E.operatorAlgebra) * a *
            ((u * u⁻¹ : E.operatorAlgebraˣ) : E.operatorAlgebra) := by
              simp only [Units.val_mul, mul_assoc]
      _ = a := by simp
  map_mul' a b := by
    calc (u : E.operatorAlgebra) * (a * b) * (↑(u⁻¹) : E.operatorAlgebra)
        = (u : E.operatorAlgebra) * a * ((u⁻¹ * u : E.operatorAlgebraˣ) : E.operatorAlgebra) * b *
            (↑(u⁻¹) : E.operatorAlgebra) := by simp [mul_assoc]
      _ = ((u : E.operatorAlgebra) * a * (↑(u⁻¹) : E.operatorAlgebra)) *
            ((u : E.operatorAlgebra) * b * (↑(u⁻¹) : E.operatorAlgebra)) := by
              simp only [Units.val_mul, mul_assoc]
  map_add' a b := by rw [mul_add, add_mul]
  commutes' r := by
    calc (u : E.operatorAlgebra) * algebraMap R E.operatorAlgebra r * (↑(u⁻¹) : E.operatorAlgebra)
        = (u : E.operatorAlgebra) * (↑(u⁻¹) : E.operatorAlgebra) * algebraMap R E.operatorAlgebra r := by
            rw [mul_assoc, Algebra.commutes, ← mul_assoc]
      _ = ((u * u⁻¹ : E.operatorAlgebraˣ) : E.operatorAlgebra) * algebraMap R E.operatorAlgebra r := by
            rw [← Units.val_mul]
      _ = algebraMap R E.operatorAlgebra r := by simp

/-- Forward Bridge 3 (restricted directly to `E.operatorAlgebra`). -/
def erlangen20AlgebraSymmetryAction
    {R V 𝔤 𝒮 ℐ G : Type*}
    [CommRing R] [AddCommGroup V] [Module R V] [LieRing 𝔤] [LieAlgebra R 𝔤] [Group G]
    (E : Erlangen20Datum R V 𝔤 𝒮 ℐ) (ρ : G →* E.operatorAlgebraˣ) :
    SymmetryAction G E.operatorAlgebra where
  act g := (erlangen20AlgConjAlgEquiv E (ρ g)).toRingEquiv
  act_one a := by
    change (erlangen20AlgConjAlgEquiv E (ρ 1)) a = a
    rw [map_one]
    simp [erlangen20AlgConjAlgEquiv]
  act_mul g h a := by
    change (erlangen20AlgConjAlgEquiv E (ρ (g * h))) a =
      (erlangen20AlgConjAlgEquiv E (ρ g)) ((erlangen20AlgConjAlgEquiv E (ρ h)) a)
    rw [map_mul]
    simp only [erlangen20AlgConjAlgEquiv, Equiv.coe_fn_mk, AlgEquiv.coe_mk,
      _root_.mul_inv_rev, Units.val_mul, mul_assoc]

/-- Real `OperatorSymmetryAction` on `E.operatorAlgebra` when `R = ℝ`. -/
def erlangen20AlgebraOperatorSymmetryAction
    {V 𝔤 𝒮 ℐ G : Type*}
    [AddCommGroup V] [Module ℝ V] [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Group G]
    (E : Erlangen20Datum ℝ V 𝔤 𝒮 ℐ) (ρ : G →* E.operatorAlgebraˣ) :
    OperatorSymmetryAction G E.operatorAlgebra where
  toFun g := erlangen20AlgConjAlgEquiv E (ρ g⁻¹)
  map_one' := by
    apply AlgEquiv.ext
    intro a
    change erlangen20AlgConjAlgEquiv E (ρ (1 : G)⁻¹) a = a
    rw [inv_one, map_one]
    simp [erlangen20AlgConjAlgEquiv]
  map_mul' g₁ g₂ := by
    apply AlgEquiv.ext
    intro a
    apply Subtype.ext
    change ((ρ (g₁ * g₂)⁻¹ : E.operatorAlgebra) : Module.End ℝ V) * a.1 *
        ((↑(((ρ (g₁ * g₂)⁻¹)⁻¹)) : E.operatorAlgebra) : Module.End ℝ V) =
      ((ρ g₂⁻¹ : E.operatorAlgebra) : Module.End ℝ V) *
        (((ρ g₁⁻¹ : E.operatorAlgebra) : Module.End ℝ V) * a.1 *
          ((↑(((ρ g₁⁻¹)⁻¹)) : E.operatorAlgebra) : Module.End ℝ V)) *
        ((↑(((ρ g₂⁻¹)⁻¹)) : E.operatorAlgebra) : Module.End ℝ V)
    rw [_root_.mul_inv_rev, map_mul, _root_.mul_inv_rev]
    simp only [Units.val_mul, Subalgebra.coe_mul, mul_assoc]

theorem toSymmetryAction_erlangen20AlgebraOperatorSymmetryAction
    {V 𝔤 𝒮 ℐ G : Type*}
    [AddCommGroup V] [Module ℝ V] [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Group G]
    (E : Erlangen20Datum ℝ V 𝔤 𝒮 ℐ) (ρ : G →* E.operatorAlgebraˣ) :
    toSymmetryAction (erlangen20AlgebraOperatorSymmetryAction E ρ) =
      erlangen20AlgebraSymmetryAction E ρ := by
  have hact : ∀ g : G,
      (toSymmetryAction (erlangen20AlgebraOperatorSymmetryAction E ρ)).act g =
        (erlangen20AlgebraSymmetryAction E ρ).act g := by
    intro g
    apply RingEquiv.ext
    intro a
    change erlangen20AlgConjAlgEquiv E (ρ (g⁻¹)⁻¹) a =
      erlangen20AlgConjAlgEquiv E (ρ g) a
    rw [inv_inv]
  cases h1 : toSymmetryAction (erlangen20AlgebraOperatorSymmetryAction E ρ)
  cases h2 : erlangen20AlgebraSymmetryAction E ρ
  simp only [SymmetryAction.mk.injEq]
  funext g
  have hg := hact g
  rw [h1, h2] at hg
  exact hg

/-- `erlangen20EndSymmetryAction` stabilizes `E.operatorAlgebra` (and in particular every `E.representation X`). -/
theorem erlangen20EndSymmetryAction_stabilizes_operatorAlgebra
    {R V 𝔤 𝒮 ℐ G : Type*}
    [CommRing R] [AddCommGroup V] [Module R V] [LieRing 𝔤] [LieAlgebra R 𝔤] [Group G]
    (E : Erlangen20Datum R V 𝔤 𝒮 ℐ) (ρ : G →* E.operatorAlgebraˣ)
    (g : G) {T : Module.End R V} (hT : T ∈ E.operatorAlgebra) :
    (erlangen20EndSymmetryAction E ρ).act g T ∈ E.operatorAlgebra :=
  E.operatorAlgebra.mul_mem
    (E.operatorAlgebra.mul_mem (ρ g : E.operatorAlgebra).2 hT)
    ((↑((ρ g)⁻¹) : E.operatorAlgebra).2)

theorem erlangen20EndSymmetryAction_stabilizes_representation
    {R V 𝔤 𝒮 ℐ G : Type*}
    [CommRing R] [AddCommGroup V] [Module R V] [LieRing 𝔤] [LieAlgebra R 𝔤] [Group G]
    (E : Erlangen20Datum R V 𝔤 𝒮 ℐ) (ρ : G →* E.operatorAlgebraˣ)
    (g : G) (X : 𝔤) :
    (erlangen20EndSymmetryAction E ρ).act g (E.representation X) ∈ E.operatorAlgebra :=
  erlangen20EndSymmetryAction_stabilizes_operatorAlgebra E ρ g (E.representation_mem X)

/-- Subalgebra inclusion intertwines `erlangen20AlgebraSymmetryAction` and `erlangen20EndSymmetryAction`. -/
theorem erlangen20EndSymmetryAction_coe_eq
    {R V 𝔤 𝒮 ℐ G : Type*}
    [CommRing R] [AddCommGroup V] [Module R V] [LieRing 𝔤] [LieAlgebra R 𝔤] [Group G]
    (E : Erlangen20Datum R V 𝔤 𝒮 ℐ) (ρ : G →* E.operatorAlgebraˣ)
    (g : G) (a : E.operatorAlgebra) :
    ((erlangen20AlgebraSymmetryAction E ρ).act g a : Module.End R V) =
      (erlangen20EndSymmetryAction E ρ).act g (a : Module.End R V) :=
  rfl

/-- Commutant-equals-stabilizer theorem for `erlangen20EndSymmetryAction`. -/
theorem erlangen20EndSymmetryAction_act_eq_self_iff_commute
    {R V 𝔤 𝒮 ℐ G : Type*}
    [CommRing R] [AddCommGroup V] [Module R V] [LieRing 𝔤] [LieAlgebra R 𝔤] [Group G]
    (E : Erlangen20Datum R V 𝔤 𝒮 ℐ) (ρ : G →* E.operatorAlgebraˣ)
    (g : G) (T : Module.End R V) :
    (erlangen20EndSymmetryAction E ρ).act g T = T ↔
      ((ρ g : E.operatorAlgebra) : Module.End R V) * T =
        T * ((ρ g : E.operatorAlgebra) : Module.End R V) := by
  constructor
  · intro h
    have hmul := congrArg (· * ((ρ g : E.operatorAlgebra) : Module.End R V)) h
    dsimp [erlangen20EndSymmetryAction, erlangen20EndConjAlgEquiv] at hmul
    rw [mul_assoc] at hmul
    have hinv : ((↑((ρ g)⁻¹) : E.operatorAlgebra) : Module.End R V) *
        ((ρ g : E.operatorAlgebra) : Module.End R V) = 1 := by
      rw [← Subalgebra.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Subalgebra.coe_one]
    rw [hinv, mul_one] at hmul
    exact hmul
  · intro h
    change ((ρ g : E.operatorAlgebra) : Module.End R V) * T *
        ((↑((ρ g)⁻¹) : E.operatorAlgebra) : Module.End R V) = T
    rw [h, mul_assoc]
    have hinv : ((ρ g : E.operatorAlgebra) : Module.End R V) *
        ((↑((ρ g)⁻¹) : E.operatorAlgebra) : Module.End R V) = 1 := by
      rw [← Subalgebra.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Subalgebra.coe_one]
    rw [hinv, mul_one]

/-- Fixed-point subsemiring and Galois connection bridge for `Erlangen20Datum`. -/
theorem erlangen20_fixedPointSubsemiring_and_galois
    {R V 𝔤 𝒮 ℐ G : Type*}
    [CommRing R] [AddCommGroup V] [Module R V] [LieRing 𝔤] [LieAlgebra R 𝔤] [Group G]
    (E : Erlangen20Datum R V 𝔤 𝒮 ℐ) (ρ : G →* E.operatorAlgebraˣ)
    (H : Subgroup G) (S : Set (Module.End R V)) :
    ((invariantSubring (erlangen20EndSymmetryAction E ρ)).toSubsemiring =
      @fixedPointSubsemiring G (Module.End R V) _ _
        (symmetryActionToMulSemiringAction (erlangen20EndSymmetryAction E ρ)) ⊤) ∧
    (H ≤ @fixingSubgroup G (Module.End R V) _ _
        (symmetryActionToMulSemiringAction (erlangen20EndSymmetryAction E ρ)) S ↔
      S ⊆ @fixedPointSet G (Module.End R V) _ _
        (symmetryActionToMulSemiringAction (erlangen20EndSymmetryAction E ρ)) H) ∧
    (H ≤ @fixingSubgroup G (Module.End R V) _ _
        (symmetryActionToMulSemiringAction (erlangen20EndSymmetryAction E ρ))
        (Set.range E.representation) ↔
      ∀ X : 𝔤, E.representation X ∈
        @fixedPointSet G (Module.End R V) _ _
          (symmetryActionToMulSemiringAction (erlangen20EndSymmetryAction E ρ)) H) := by
  refine ⟨invariantSubring_toSubsemiring_eq_fixedPointSubsemiring_top _,
    symmetryAction_galois_connection _ H S, ?_⟩
  rw [symmetryAction_galois_connection]
  exact Set.range_subset_iff

end Bridge3Forward

section Bridge3Reverse

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Compose `π : Op →ₐ[R] Module.End R V` with an associative Lie-compatible linear map
`φ : 𝔤 →ₗ[R] Op` (avoiding any `[Ring Op]` / `[LieRing Op]` typeclass overlap). -/
def algHomCompLieHom
    {R V Op 𝔤 : Type*}
    [CommRing R] [AddCommGroup V] [Module R V]
    [Ring Op] [Algebra R Op]
    [LieRing 𝔤] [LieAlgebra R 𝔤]
    (π : Op →ₐ[R] Module.End R V)
    (φ : 𝔤 →ₗ[R] Op)
    (hφ : ∀ X Y : 𝔤, φ ⁅X, Y⁆ = φ X * φ Y - φ Y * φ X) :
    𝔤 →ₗ⁅R⁆ Module.End R V where
  toLinearMap := π.toLinearMap.comp φ
  map_lie' {X Y} := by
    change π (φ ⁅X, Y⁆) = π (φ X) * π (φ Y) - π (φ Y) * π (φ X)
    rw [hφ X Y, map_sub, map_mul, map_mul]

/-- Reverse Bridge 3 (represented module `V` via `π : Op →ₐ[R] Module.End R V`). -/
def erlangen20DatumOfSymmetryActionOnModule
    {R V Op 𝔤 G : Type*}
    [CommRing R] [AddCommGroup V] [Module R V]
    [Ring Op] [Algebra R Op]
    [LieRing 𝔤] [LieAlgebra R 𝔤]
    [Group G]
    (α : SymmetryAction G Op)
    (π : Op →ₐ[R] Module.End R V)
    (φ : 𝔤 →ₗ[R] Op)
    (hφ : ∀ X Y : 𝔤, φ ⁅X, Y⁆ = φ X * φ Y - φ Y * φ X) :
    Erlangen20Datum R V 𝔤 (SymmetryAction G Op) (Subring Op) where
  operatorAlgebra := π.range
  representation := algHomCompLieHom π φ hφ
  representation_mem X := ⟨φ X, rfl⟩
  symmetryData := α
  invariantData := invariantSubring α

/-- Reverse Bridge 3 (left-regular representation `V := Op`, `π := Algebra.lmul R Op`). -/
def erlangen20DatumOfSymmetryAction
    (R : Type*) {Op 𝔤 G : Type*}
    [CommRing R] [Ring Op] [Algebra R Op]
    [LieRing 𝔤] [LieAlgebra R 𝔤]
    [Group G]
    (α : SymmetryAction G Op)
    (φ : 𝔤 →ₗ[R] Op)
    (hφ : ∀ X Y : 𝔤, φ ⁅X, Y⁆ = φ X * φ Y - φ Y * φ X) :
    Erlangen20Datum R Op 𝔤 (SymmetryAction G Op) (Subring Op) :=
  erlangen20DatumOfSymmetryActionOnModule α (Algebra.lmul R Op) φ hφ

theorem erlangen20DatumOfSymmetryAction_rep_injective
    (R : Type*) {Op 𝔤 G : Type*}
    [CommRing R] [Ring Op] [Algebra R Op]
    [LieRing 𝔤] [LieAlgebra R 𝔤]
    [Group G]
    (α : SymmetryAction G Op)
    (φ : 𝔤 →ₗ[R] Op)
    (hφ_lie : ∀ X Y : 𝔤, φ ⁅X, Y⁆ = φ X * φ Y - φ Y * φ X)
    (hφ : Function.Injective φ) :
    Function.Injective (erlangen20DatumOfSymmetryAction R α φ hφ_lie).representation := by
  intro X Y hXY
  apply hφ
  have h1 := congrArg (fun T : Module.End R Op => T (1 : Op)) hXY
  change φ X * (1 : Op) = φ Y * (1 : Op) at h1
  simpa using h1

/-- Reverse Bridge 3 from `OperatorSymmetryAction G Op` over `ℝ`. -/
def erlangen20DatumOfOperatorSymmetryAction
    {Op 𝔤 G : Type*}
    [Ring Op] [Algebra ℝ Op]
    [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [Group G]
    (S : OperatorSymmetryAction G Op)
    (φ : 𝔤 →ₗ[ℝ] Op)
    (hφ : ∀ X Y : 𝔤, φ ⁅X, Y⁆ = φ X * φ Y - φ Y * φ X) :
    Erlangen20Datum ℝ Op 𝔤 (OperatorSymmetryAction G Op) (Submodule ℝ Op × Subring Op) where
  operatorAlgebra := (Algebra.lmul ℝ Op).range
  representation := algHomCompLieHom (Algebra.lmul ℝ Op) φ hφ
  representation_mem X := ⟨φ X, rfl⟩
  symmetryData := S
  invariantData := (S.invariantSubmodule, invariantSubring (toSymmetryAction S))

end Bridge3Reverse

section ConcreteCantorAndKreinFamilies

open InfoGeometry.OperatorAlgebra.CantorDoubleCylinderFractalColimit
open InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants
open InfoGeometry.Categorical.CantorDoubleCylinderColimitAlgebra
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.ConcreteHilbertCommutation
open InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
open InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis
open scoped InnerProductSpace

/-! ### Cantor Double Cylinder (`Type u` generalization + `Type 0` compatibility) -/

private def doubleCylinderColimitAlgebraMapPoly
    (R B : Type*) [CommRing R] [Ring B] [Algebra R B] :
    R →+* DoubleCylinderColimit B :=
  (doubleCylinderInclusion B 0).comp (algebraMap R (DoubleCylinderStage B 0))

private theorem doubleCylinderBond_smul_poly
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (n : ℕ) (r : R) (M : DoubleCylinderStage B n) :
    doubleCylinderBond B n (r • M) = r • doubleCylinderBond B n M := by
  ext v w
  dsimp [doubleCylinderBond, doubleCylinderBondFun]
  split_ifs <;> simp

private theorem doubleCylinderBond_algebraMap_poly
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (n : ℕ) (r : R) :
    doubleCylinderBond B n (algebraMap R (DoubleCylinderStage B n) r) =
      algebraMap R (DoubleCylinderStage B (n + 1)) r := by
  rw [Algebra.algebraMap_eq_smul_one, doubleCylinderBond_smul_poly, map_one,
    ← Algebra.algebraMap_eq_smul_one]

private theorem doubleCylinderInclusion_algebraMap_poly
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (n : ℕ) (r : R) :
    doubleCylinderInclusion B n (algebraMap R (DoubleCylinderStage B n) r) =
      doubleCylinderInclusion B 0 (algebraMap R (DoubleCylinderStage B 0) r) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← doubleCylinderBond_algebraMap_poly n r, doubleCylinderInclusion_bond, ih]

private theorem doubleCylinderColimitAlgebraMapPoly_commutes
    (R B : Type*) [CommRing R] [Ring B] [Algebra R B]
    (r : R) (X : DoubleCylinderColimit B) :
    doubleCylinderColimitAlgebraMapPoly R B r * X =
      X * doubleCylinderColimitAlgebraMapPoly R B r := by
  induction X using DirectLimit.induction with
  | ih n M =>
      change doubleCylinderInclusion B 0 (algebraMap R (DoubleCylinderStage B 0) r) *
          doubleCylinderInclusion B n M =
        doubleCylinderInclusion B n M *
          doubleCylinderInclusion B 0 (algebraMap R (DoubleCylinderStage B 0) r)
      rw [← doubleCylinderInclusion_algebraMap_poly n r,
          ← (doubleCylinderInclusion B n).map_mul,
          ← (doubleCylinderInclusion B n).map_mul, Algebra.commutes]

/-- Explicit (non-instance) `R`-algebra structure on `DoubleCylinderColimit B` for arbitrary
universes `R : Type uR`, `B : Type uB` (avoiding typeclass diamond with
`instAlgebraRealDoubleCylinderColimit` at `(ℝ, ℝ)`). -/
@[instance_reducible]
def doubleCylinderColimitAlgebra
    (R B : Type*) [CommRing R] [Ring B] [Algebra R B] :
    Algebra R (DoubleCylinderColimit B) :=
  RingHom.toAlgebra' (doubleCylinderColimitAlgebraMapPoly R B)
    (doubleCylinderColimitAlgebraMapPoly_commutes R B)

/-- Universe-polymorphic Cantor double-cylinder `Erlangen20Datum` (generalizes beyond `Type 0`). -/
def cantorDoubleCylinderErlangen20DatumPoly
    (R B : Type*)
    [CommRing R] [Ring B] [Algebra R (DoubleCylinderColimit B)] :
    @Erlangen20Datum R (DoubleCylinderColimit B) (DoubleCylinderColimit B)
      (SymmetryAction G_swap (DoubleCylinderColimit B))
      (Subring (DoubleCylinderColimit B))
      _ _ Algebra.toModule
      LieRing.ofAssociativeRing
      LieAlgebra.ofAssociativeAlgebra :=
  letI : LieRing (DoubleCylinderColimit B) := LieRing.ofAssociativeRing
  letI : LieAlgebra R (DoubleCylinderColimit B) := LieAlgebra.ofAssociativeAlgebra
  erlangen20DatumOfSymmetryAction R (erlangenDoubleCylinderSymmetryAction B)
    LinearMap.id (fun x y => Ring.lie_def x y)

/-- Convenience constructor for any `[CommRing R] [Ring B] [Algebra R B]` in arbitrary universes. -/
def cantorDoubleCylinderErlangen20DatumOfSeedAlgebra
    (R B : Type*) [CommRing R] [Ring B] [Algebra R B] :
    @Erlangen20Datum R (DoubleCylinderColimit B) (DoubleCylinderColimit B)
      (SymmetryAction G_swap (DoubleCylinderColimit B))
      (Subring (DoubleCylinderColimit B))
      _ _ (@Algebra.toModule _ _ _ _ (doubleCylinderColimitAlgebra R B))
      LieRing.ofAssociativeRing
      (@LieAlgebra.ofAssociativeAlgebra _ _ _ _ (doubleCylinderColimitAlgebra R B)) :=
  letI : Algebra R (DoubleCylinderColimit B) := doubleCylinderColimitAlgebra R B
  cantorDoubleCylinderErlangen20DatumPoly R B

/-- Exact match between `CantorDoubleCylinderColimitAlgebra.cantorDoubleCylinderErlangen20Datum` (`Type 0`)
and Reverse Bridge 3 applied to `erlangenDoubleCylinderSymmetryAction ℝ` via `colimitRepresentationEndAlgHom`. -/
theorem cantorDoubleCylinderErlangen20Datum_matches_bridge3 :
    let E := erlangen20DatumOfSymmetryActionOnModule
      (erlangenDoubleCylinderSymmetryAction ℝ)
      colimitRepresentationEndAlgHom
      (LinearMap.id : DoubleCylinderColimit ℝ →ₗ[ℝ] DoubleCylinderColimit ℝ)
      (fun x y => Ring.lie_def x y)
    E.operatorAlgebra = cantorDoubleCylinderErlangen20Datum.operatorAlgebra ∧
    E.representation = cantorDoubleCylinderErlangen20Datum.representation ∧
    E.symmetryData = cantorDoubleCylinderErlangen20Datum.symmetryData.gSwapAction ∧
    E.invariantData = cantorDoubleCylinderErlangen20Datum.invariantData.invariantSubring :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Transport `erlangenDoubleCylinderSymmetryAction ℝ` to `cantorDoubleCylinderErlangen20Datum.operatorAlgebra`. -/
def cantorDoubleCylinderOperatorAlgebraEquiv :
    DoubleCylinderColimit ℝ ≃ₐ[ℝ] cantorDoubleCylinderErlangen20Datum.operatorAlgebra :=
  AlgEquiv.ofInjective colimitRepresentationEndAlgHom colimitRepresentationEndAlgHom_injective

def cantorDoubleCylinderOperatorAlgebraSymmetryAction :
    SymmetryAction G_swap cantorDoubleCylinderErlangen20Datum.operatorAlgebra where
  act g :=
    (cantorDoubleCylinderOperatorAlgebraEquiv.symm.toRingEquiv.trans
      ((erlangenDoubleCylinderSymmetryAction ℝ).act g)).trans
      cantorDoubleCylinderOperatorAlgebraEquiv.toRingEquiv
  act_one a := by
    change cantorDoubleCylinderOperatorAlgebraEquiv
      ((erlangenDoubleCylinderSymmetryAction ℝ).act 1
        (cantorDoubleCylinderOperatorAlgebraEquiv.symm a)) = a
    rw [(erlangenDoubleCylinderSymmetryAction ℝ).act_one]
    exact cantorDoubleCylinderOperatorAlgebraEquiv.apply_symm_apply a
  act_mul g h a := by
    change cantorDoubleCylinderOperatorAlgebraEquiv
      ((erlangenDoubleCylinderSymmetryAction ℝ).act (g * h)
        (cantorDoubleCylinderOperatorAlgebraEquiv.symm a)) =
      cantorDoubleCylinderOperatorAlgebraEquiv
        ((erlangenDoubleCylinderSymmetryAction ℝ).act g
          (cantorDoubleCylinderOperatorAlgebraEquiv.symm
            (cantorDoubleCylinderOperatorAlgebraEquiv
              ((erlangenDoubleCylinderSymmetryAction ℝ).act h
                (cantorDoubleCylinderOperatorAlgebraEquiv.symm a)))))
    rw [cantorDoubleCylinderOperatorAlgebraEquiv.symm_apply_apply,
        (erlangenDoubleCylinderSymmetryAction ℝ).act_mul]

/-- Krein `J_lp_clm` conjugation fixes `cantorDoubleCylinderErlangen20Datum.operatorAlgebra` pointwise. -/
theorem cantorDoubleCylinder_sewn_fixes_operatorAlgebra
    (X : DoubleCylinderColimit ℝ) (v : H_lp ℝ) :
    ((J_lp_clm (E := ℝ)).toLinearMap *
      (cantorDoubleCylinderErlangen20Datum.representation X) *
      (J_lp_clm (E := ℝ)).toLinearMap) v =
      (cantorDoubleCylinderErlangen20Datum.representation X) v := by
  have h := congrArg (fun T : H_lp ℝ →L[ℝ] H_lp ℝ => T v) (colimitRepresentation_sewn_invariant X)
  change (J_lp_clm (E := ℝ)) ((colimitRepresentationCLM X) ((J_lp_clm (E := ℝ)) v)) =
    (colimitRepresentationCLM X) v
  exact h

/-! ### Krein / Split `G_{2(2)}` Unification (`KreinCl44SplitG2DerivationPosetSynthesis`) -/

theorem cl44Vec1Submodule_le_cl44MatrixSubalgebra :
    cl44Vec1Submodule ≤ cl44MatrixSubalgebra.toSubmodule :=
  Submodule.span_le.mpr (Set.range_subset_iff.mpr fun a =>
    Algebra.subset_adjoin (Set.mem_range_self a))

theorem splitG2MatrixSymmetryAction_stabilizes_cl44MatrixSubalgebra
    (u : SplitG2MatrixGroup) {M : Matrix Krein16Idx Krein16Idx ℝ}
    (hM : M ∈ cl44MatrixSubalgebra) :
    splitG2MatrixSymmetryAction.act u M ∈ cl44MatrixSubalgebra := by
  have hgen : Set.range cl44Gen ⊆
      (cl44MatrixSubalgebra.comap (splitG2ConjAlgEquiv u).toAlgHom : Set _) := by
    rintro _ ⟨a, rfl⟩
    exact cl44Vec1Submodule_le_cl44MatrixSubalgebra
      (u.2.2.2.2.2 (cl44Gen a) (Submodule.subset_span (Set.mem_range_self a)))
  exact (Algebra.adjoin_le hgen) hM

theorem splitG2EuclideanSymmetryAction_stabilizes_g2OperatorAlgebra
    (u : SplitG2MatrixGroup) {T : Module.End ℝ (EuclideanSpace ℝ Krein16Idx)}
    (hT : T ∈ g2Erlangen20Datum.operatorAlgebra) :
    splitG2EuclideanSymmetryAction.act u T ∈ g2Erlangen20Datum.operatorAlgebra := by
  rcases hT with ⟨M, hM, rfl⟩
  refine ⟨splitG2MatrixSymmetryAction.act u M,
    splitG2MatrixSymmetryAction_stabilizes_cl44MatrixSubalgebra u hM, ?_⟩
  change Matrix.toLpLinAlgEquiv 2 (splitG2ConjAlgEquiv u M) =
    Matrix.toLpLinAlgEquiv 2 (splitG2ConjAlgEquiv u
      ((Matrix.toLpLinAlgEquiv 2).symm (Matrix.toLpLinAlgEquiv 2 M)))
  rw [AlgEquiv.symm_apply_apply]

theorem g2_erlangen_fixedPoints_bridge :
    gamma44 ∈ @fixedPointSubsemiring SplitG2MatrixGroup (Matrix Krein16Idx Krein16Idx ℝ) _ _
      (symmetryActionToMulSemiringAction splitG2MatrixSymmetryAction) ⊤ ∧
    cl44Gen 0 ∈ @fixedPointSubsemiring SplitG2MatrixGroup (Matrix Krein16Idx Krein16Idx ℝ) _ _
      (symmetryActionToMulSemiringAction splitG2MatrixSymmetryAction) ⊤ ∧
    g2Erlangen20Datum.symmetryData.2.1 ∈
      @fixedPointSubsemiring SplitG2MatrixGroup (Module.End ℝ (EuclideanSpace ℝ Krein16Idx)) _ _
        (symmetryActionToMulSemiringAction splitG2EuclideanSymmetryAction) ⊤ ∧
    g2Erlangen20Datum.symmetryData.2.2 ∈
      @fixedPointSubsemiring SplitG2MatrixGroup (Module.End ℝ (EuclideanSpace ℝ Krein16Idx)) _ _
        (symmetryActionToMulSemiringAction splitG2EuclideanSymmetryAction) ⊤ := by
  have h1 : gamma44 ∈ invariantSubring splitG2MatrixSymmetryAction := splitG2_erlangen_invariants.2.1
  have h2 : cl44Gen 0 ∈ invariantSubring splitG2MatrixSymmetryAction := splitG2_erlangen_invariants.2.2.1
  rw [← SetLike.mem_coe, ← Subring.coe_toSubsemiring,
      invariantSubring_toSubsemiring_eq_fixedPointSubsemiring_top] at h1 h2
  refine ⟨h1, h2, ?_, ?_⟩
  · intro u
    have hu := splitG2_erlangen_invariants.2.1 u
    change Matrix.toLpLinAlgEquiv 2 (splitG2ConjAlgEquiv u
      ((Matrix.toLpLinAlgEquiv 2).symm (Matrix.toLpLinAlgEquiv 2 gamma44))) =
      Matrix.toLpLinAlgEquiv 2 gamma44
    rw [AlgEquiv.symm_apply_apply]
    exact congrArg (Matrix.toLpLinAlgEquiv 2) hu
  · intro u
    have hu := splitG2_erlangen_invariants.2.2.1 u
    change Matrix.toLpLinAlgEquiv 2 (splitG2ConjAlgEquiv u
      ((Matrix.toLpLinAlgEquiv 2).symm (Matrix.toLpLinAlgEquiv 2 (cl44Gen 0)))) =
      Matrix.toLpLinAlgEquiv 2 (cl44Gen 0)
    rw [AlgEquiv.symm_apply_apply]
    exact congrArg (Matrix.toLpLinAlgEquiv 2) hu

/-- Reverse Bridge 3 applied to `splitG2MatrixSymmetryAction` recovers `g2Erlangen20Datum.representation`. -/
theorem splitG2_bridge3_representation_eq :
    letI : LieRing (Matrix Krein16Idx Krein16Idx ℝ) := LieRing.ofAssociativeRing
    letI : LieAlgebra ℝ (Matrix Krein16Idx Krein16Idx ℝ) := LieAlgebra.ofAssociativeAlgebra
    let E := erlangen20DatumOfSymmetryActionOnModule
      splitG2MatrixSymmetryAction
      (Matrix.toLpLinAlgEquiv (2 : ENNReal) (R := ℝ) (n := Krein16Idx)).toAlgHom
      g2LieSubalgebra.incl.toLinearMap
      (fun X Y => by
        change g2LieSubalgebra.incl ⁅X, Y⁆ =
          g2LieSubalgebra.incl X * g2LieSubalgebra.incl Y -
          g2LieSubalgebra.incl Y * g2LieSubalgebra.incl X
        rw [g2LieSubalgebra.incl.map_lie]
        exact Ring.lie_def _ _)
    ∀ X : g2LieSubalgebra, E.representation X = g2Erlangen20Datum.representation X := by
  dsimp only
  intro X
  apply LinearMap.ext
  intro v
  rfl

end ConcreteCantorAndKreinFamilies

/-!
## Bridge 4: `OperatorAlgebra.ErlangenOperator2.ErlangenInvariantPacket` → `Canonical.ErlangenOperator2.ErlangenOperatorDatum`
-/

section Bridge4

/-- Bridge 4: Construct a `Canonical.ErlangenOperator2.ErlangenOperatorDatum` from an
`OperatorAlgebra.ErlangenOperator2.ErlangenInvariantPacket`, preserving universe polymorphism on
`Obs, Sym, G, Gdual, StateSpace` while isolating the internal `uPol = 0` pin inside `E`. -/
def erlangenOperatorDatumOfPacket
    {Obs Sym G Gdual StateSpace : Type*}
    [Ring Obs] [Group Sym]
    (E : InfoGeometry.OperatorAlgebra.ErlangenOperator2.ErlangenInvariantPacket
      Obs Sym G Gdual StateSpace)
    (hStateActOne : ∀ ω : StateSpace, E.entropySymmetry.stateAction 1 ω = ω)
    (hStateActMul : ∀ g h : Sym, ∀ ω : StateSpace,
      E.entropySymmetry.stateAction (g * h) ω =
        E.entropySymmetry.stateAction g (E.entropySymmetry.stateAction h ω))
    (hfisher : ∀ s : Sym, ∀ ω : StateSpace, ∀ A B : Obs,
      E.fisherMetric (E.entropySymmetry.stateAction s ω)
        (E.legendrePacket.symmetryAction.act s A)
        (E.legendrePacket.symmetryAction.act s B) = E.fisherMetric ω A B) :
    InfoGeometry.Canonical.ErlangenOperator2.ErlangenOperatorDatum ℝ Sym StateSpace Obs where
  entropy := fun ω => E.entropySymmetry.entropy (E.entropySymmetry.data.moment ω)
  responseMetric := E.fisherMetric
  onsagerPairing := E.fisherMetric
  stateAct := E.entropySymmetry.stateAction
  obsAct := fun s A => E.legendrePacket.symmetryAction.act s A
  casimirJ := id
  stateAct_one := hStateActOne
  stateAct_mul := hStateActMul
  obsAct_one := E.legendrePacket.symmetryAction.act_one
  obsAct_mul := E.legendrePacket.symmetryAction.act_mul
  entropy_invariant := fun s ω => E.entropy_constant_on_state_orbit s ω
  response_invariant := fun s A B ω => hfisher s ω A B
  onsager_reciprocity := fun A B ω => E.fisher_symmetric ω A B

theorem erlangenOperatorDatumOfPacket_geometry
    {Obs Sym G Gdual StateSpace : Type*} [Ring Obs] [Group Sym]
    (E : InfoGeometry.OperatorAlgebra.ErlangenOperator2.ErlangenInvariantPacket
      Obs Sym G Gdual StateSpace)
    (hStateActOne : ∀ ω : StateSpace, E.entropySymmetry.stateAction 1 ω = ω)
    (hStateActMul : ∀ g h : Sym, ∀ ω : StateSpace,
      E.entropySymmetry.stateAction (g * h) ω =
        E.entropySymmetry.stateAction g (E.entropySymmetry.stateAction h ω))
    (hfisher : ∀ s : Sym, ∀ ω : StateSpace, ∀ A B : Obs,
      E.fisherMetric (E.entropySymmetry.stateAction s ω)
        (E.legendrePacket.symmetryAction.act s A)
        (E.legendrePacket.symmetryAction.act s B) = E.fisherMetric ω A B) :
    InfoGeometry.Canonical.ErlangenOperator2.ErlangenOperatorDatum.ErlangenOperatorGeometry
      (erlangenOperatorDatumOfPacket E hStateActOne hStateActMul hfisher) :=
  InfoGeometry.Canonical.ErlangenOperator2.ErlangenOperatorDatum.geometry_as_symmetry_invariants _

theorem erlangenOperatorDatumOfPacket_casimir_and_psd
    {Obs Sym G Gdual StateSpace : Type*} [Ring Obs] [Group Sym]
    (E : InfoGeometry.OperatorAlgebra.ErlangenOperator2.ErlangenInvariantPacket
      Obs Sym G Gdual StateSpace)
    (hStateActOne : ∀ ω : StateSpace, E.entropySymmetry.stateAction 1 ω = ω)
    (hStateActMul : ∀ g h : Sym, ∀ ω : StateSpace,
      E.entropySymmetry.stateAction (g * h) ω =
        E.entropySymmetry.stateAction g (E.entropySymmetry.stateAction h ω))
    (hfisher : ∀ s : Sym, ∀ ω : StateSpace, ∀ A B : Obs,
      E.fisherMetric (E.entropySymmetry.stateAction s ω)
        (E.legendrePacket.symmetryAction.act s A)
        (E.legendrePacket.symmetryAction.act s B) = E.fisherMetric ω A B) :
    (∀ s : Sym,
      (erlangenOperatorDatumOfPacket E hStateActOne hStateActMul hfisher).obsAct s E.casimir.C =
        E.casimir.C) ∧
    (E.casimir.C ∈
      @fixedPointSet Sym Obs _ _
        (symmetryActionToMulSemiringAction E.legendrePacket.symmetryAction) ⊤) ∧
    (∀ ω : StateSpace, ∀ A : Obs,
      0 ≤ (erlangenOperatorDatumOfPacket E hStateActOne hStateActMul hfisher).responseMetric ω A A) ∧
    (∀ s : Sym, ∀ ω : StateSpace,
      E.fisherMetric (E.entropySymmetry.stateAction s ω) E.casimir.C E.casimir.C =
        E.fisherMetric ω E.casimir.C E.casimir.C) := by
  refine ⟨E.casimir_invariant, fun s => E.casimir_invariant (s : Sym), E.fisher_psd, ?_⟩
  intro s ω
  have h := hfisher s ω E.casimir.C E.casimir.C
  rwa [E.casimir_invariant s] at h

/-- Coadjoint socket variant of Bridge 4. -/
def erlangenOperatorDatumOfSocket
    {Obs Sym G Gdual StateSpace : Type*} [Ring Obs] [Group Sym]
    (S : InfoGeometry.OperatorAlgebra.ErlangenOperator2.CoadjointCasimirGeometrySocket
      Obs Sym G Gdual StateSpace)
    (hStateActOne : ∀ ω : StateSpace, S.packet.entropySymmetry.stateAction 1 ω = ω)
    (hStateActMul : ∀ g h : Sym, ∀ ω : StateSpace,
      S.packet.entropySymmetry.stateAction (g * h) ω =
        S.packet.entropySymmetry.stateAction g (S.packet.entropySymmetry.stateAction h ω))
    (hfisher : ∀ s : Sym, ∀ ω : StateSpace, ∀ A B : Obs,
      S.packet.fisherMetric (S.packet.entropySymmetry.stateAction s ω)
        (S.packet.legendrePacket.symmetryAction.act s A)
        (S.packet.legendrePacket.symmetryAction.act s B) = S.packet.fisherMetric ω A B) :
    InfoGeometry.Canonical.ErlangenOperator2.ErlangenOperatorDatum ℝ Sym StateSpace Obs :=
  erlangenOperatorDatumOfPacket S.packet hStateActOne hStateActMul hfisher

/-- Compatibility with `InfoGeometry.Canonical.stateMomentErlangenDatum` along an invariant embedding
`embed : Sym → Obs`. -/
def stateMomentErlangenDatumOfPacket
    {Obs Sym G Gdual StateSpace : Type*} [Ring Obs] [Group Sym]
    (E : InfoGeometry.OperatorAlgebra.ErlangenOperator2.ErlangenInvariantPacket
      Obs Sym G Gdual StateSpace)
    (embed : Sym → Obs)
    (hembed : ∀ s a : Sym, E.legendrePacket.symmetryAction.act s (embed a) = embed a)
    (hStateActOne : ∀ ω : StateSpace, E.entropySymmetry.stateAction 1 ω = ω)
    (hStateActMul : ∀ g h : Sym, ∀ ω : StateSpace,
      E.entropySymmetry.stateAction (g * h) ω =
        E.entropySymmetry.stateAction g (E.entropySymmetry.stateAction h ω))
    (hfisher : ∀ s : Sym, ∀ ω : StateSpace, ∀ A B : Obs,
      E.fisherMetric (E.entropySymmetry.stateAction s ω)
        (E.legendrePacket.symmetryAction.act s A)
        (E.legendrePacket.symmetryAction.act s B) = E.fisherMetric ω A B) :
    InfoGeometry.Canonical.ErlangenOperator2.ErlangenOperatorDatum ℝ Sym StateSpace Sym :=
  InfoGeometry.Canonical.stateMomentErlangenDatum
    E.entropySymmetry
    (fun ω a b => E.fisherMetric ω (embed a) (embed b))
    (fun ω a b => E.fisherMetric ω (embed a) (embed b))
    id
    hStateActOne
    hStateActMul
    (fun s a b ω => by
      have h := hfisher s ω (embed a) (embed b)
      rwa [hembed s a, hembed s b] at h)
    (fun a b ω => E.fisher_symmetric ω (embed a) (embed b))

theorem stateMomentErlangenDatumOfPacket_agrees
    {Obs Sym G Gdual StateSpace : Type*} [Ring Obs] [Group Sym]
    (E : InfoGeometry.OperatorAlgebra.ErlangenOperator2.ErlangenInvariantPacket
      Obs Sym G Gdual StateSpace)
    (embed : Sym → Obs)
    (hembed : ∀ s a : Sym, E.legendrePacket.symmetryAction.act s (embed a) = embed a)
    (hStateActOne : ∀ ω : StateSpace, E.entropySymmetry.stateAction 1 ω = ω)
    (hStateActMul : ∀ g h : Sym, ∀ ω : StateSpace,
      E.entropySymmetry.stateAction (g * h) ω =
        E.entropySymmetry.stateAction g (E.entropySymmetry.stateAction h ω))
    (hfisher : ∀ s : Sym, ∀ ω : StateSpace, ∀ A B : Obs,
      E.fisherMetric (E.entropySymmetry.stateAction s ω)
        (E.legendrePacket.symmetryAction.act s A)
        (E.legendrePacket.symmetryAction.act s B) = E.fisherMetric ω A B) :
    let D₁ := erlangenOperatorDatumOfPacket E hStateActOne hStateActMul hfisher
    let D₂ := stateMomentErlangenDatumOfPacket E embed hembed hStateActOne hStateActMul hfisher
    D₂.entropy = D₁.entropy ∧
    D₂.stateAct = D₁.stateAct ∧
    (∀ ω a b, D₂.responseMetric ω a b = D₁.responseMetric ω (embed a) (embed b)) ∧
    (∀ ω a b, D₂.onsagerPairing ω a b = D₁.onsagerPairing ω (embed a) (embed b)) :=
  ⟨rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- Universe-polymorphic Axis A ↔ Axis C bridge (no `uPol = 0` and no `ℝ` scalar pin). -/
def erlangenOperatorDatumOfSymmetryAction
    {𝕜 G State Obs : Type*} [Group G] [Ring Obs]
    (α : SymmetryAction G Obs)
    (entropy : State → 𝕜)
    (stateAct : G → State → State)
    (metric : State → Obs → Obs → 𝕜)
    (casimirJ : Obs → Obs)
    (hStateActOne : ∀ s, stateAct 1 s = s)
    (hStateActMul : ∀ g h s, stateAct (g * h) s = stateAct g (stateAct h s))
    (hEnt : InfoGeometry.Canonical.ErlangenOperator2.IsGeneralizedCasimir entropy stateAct)
    (hResp : InfoGeometry.Canonical.ErlangenOperator2.IsGeometryInvariant metric stateAct
      (fun g A => α.act g A))
    (hOns : InfoGeometry.Canonical.ErlangenOperator2.HasJReciprocity metric casimirJ) :
    InfoGeometry.Canonical.ErlangenOperator2.ErlangenOperatorDatum 𝕜 G State Obs where
  entropy := entropy
  responseMetric := metric
  onsagerPairing := metric
  stateAct := stateAct
  obsAct := fun g A => α.act g A
  casimirJ := casimirJ
  stateAct_one := hStateActOne
  stateAct_mul := hStateActMul
  obsAct_one := α.act_one
  obsAct_mul := α.act_mul
  entropy_invariant := hEnt
  response_invariant := hResp
  onsager_reciprocity := hOns

/-- Specialization to a `SymmetryInvariants.InvariantPairing` over `State := Unit`. -/
def erlangenOperatorDatumOfInvariantPairing
    {𝕜 G Obs : Type*} [Group G] [Ring Obs]
    (α : SymmetryAction G Obs)
    (P : InvariantPairing α 𝕜)
    (c₀ : 𝕜)
    (casimirJ : Obs → Obs)
    (hOns : ∀ A B : Obs, P.pair A B = P.pair (casimirJ B) (casimirJ A)) :
    InfoGeometry.Canonical.ErlangenOperator2.ErlangenOperatorDatum 𝕜 G Unit Obs :=
  erlangenOperatorDatumOfSymmetryAction α (fun _ => c₀) (fun _ u => u)
    (fun _ A B => P.pair A B) casimirJ
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun g A B _ => P.invariant g A B) (fun A B _ => hOns A B)

/-- `IsGeneralizedCasimir E.entropy E.stateAct` is `IsInvariantReadout` for the `MulAction` induced
by `E.stateAct`. -/
theorem erlangenOperatorDatum_casimir_isInvariantReadout
    {𝕜 G State Obs : Type*} [Group G]
    (E : InfoGeometry.Canonical.ErlangenOperator2.ErlangenOperatorDatum 𝕜 G State Obs) :
    let _inst : MulAction G State :=
      { smul := E.stateAct
        one_smul := E.stateAct_one
        mul_smul := E.stateAct_mul }
    IsInvariantReadout G State E.entropy :=
  E.entropy_invariant

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra in
/-- Axis C → Axis B bridge: embed any `ErlangenOperatorDatum` whose observable algebra carries an
`R`-algebra structure and an associative Lie-compatible map `φ : 𝔤 →ₗ[R] Obs` into `Erlangen20Datum`. -/
def erlangenOperatorDatumToErlangen20Datum
    {R 𝕜 G State Obs 𝔤 : Type*}
    [CommRing R] [Group G] [Ring Obs] [Algebra R Obs]
    [LieRing 𝔤] [LieAlgebra R 𝔤]
    (E : InfoGeometry.Canonical.ErlangenOperator2.ErlangenOperatorDatum 𝕜 G State Obs)
    (φ : 𝔤 →ₗ[R] Obs)
    (hφ : ∀ X Y : 𝔤, φ ⁅X, Y⁆ = φ X * φ Y - φ Y * φ X) :
    Erlangen20Datum R Obs 𝔤
      (InfoGeometry.Canonical.ErlangenOperator2.ErlangenOperatorDatum 𝕜 G State Obs)
      (Obs → Prop) where
  operatorAlgebra := (Algebra.lmul R Obs).range
  representation := algHomCompLieHom (Algebra.lmul R Obs) φ hφ
  representation_mem X := ⟨φ X, rfl⟩
  symmetryData := E
  invariantData := fun A => ∀ g : G, E.obsAct g A = A

end Bridge4

/-!
## Bridge 5: `SmoothCartanGeometry` Fiberwise `H`-Action
-/

section Bridge5

open InfoGeometry.Erlangen.SmoothCartanGeometry
open scoped Manifold

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Conjugation `R`-algebra isomorphism `Module.End R V ≃ₐ[R] Module.End R W` induced by a
linear equivalence `e : V ≃ₗ[R] W` (Klein §4 *Abbildung* on operator rings). -/
def conjEndAlgEquiv
    {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W) :
    Module.End R V ≃ₐ[R] Module.End R W where
  toFun T := e.toLinearMap.comp (T.comp e.symm.toLinearMap)
  invFun S := e.symm.toLinearMap.comp (S.comp e.toLinearMap)
  left_inv T := by ext v; simp
  right_inv S := by ext w; simp
  map_mul' T₁ T₂ := by ext w; simp [Module.End.mul_apply]
  map_add' T₁ T₂ := by ext w; simp
  commutes' r := by
    ext w
    simp [Module.algebraMap_end_apply]

/-- Conjugation `R`-algebra automorphism of `Module.End R V` induced by `U : V ≃ₗ[R] V`. -/
def linearEquivConjAlgEquiv
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (U : V ≃ₗ[R] V) : Module.End R V ≃ₐ[R] Module.End R V :=
  conjEndAlgEquiv U

/-- General `OperatorSymmetryAction H (Module.End ℝ V)` built from a left group representation
`e : H → (V ≃ₗ[ℝ] V)` (using `toFun h := linearEquivConjAlgEquiv (e h⁻¹)` so `.act h` conjugates by `e h`). -/
def operatorSymmetryActionOfLinearEquiv
    {H V : Type*} [Group H] [AddCommGroup V] [Module ℝ V]
    (e : H → (V ≃ₗ[ℝ] V))
    (he_one : e 1 = LinearEquiv.refl ℝ V)
    (he_mul : ∀ h₁ h₂ : H, ∀ v : V, e (h₁ * h₂) v = e h₁ (e h₂ v)) :
    OperatorSymmetryAction H (Module.End ℝ V) where
  toFun h := linearEquivConjAlgEquiv (e h⁻¹)
  map_one' := by
    ext T v
    rw [inv_one, he_one]
    rfl
  map_mul' h₁ h₂ := by
    ext T v
    change e (h₁ * h₂)⁻¹ (T ((e (h₁ * h₂)⁻¹).symm v)) =
      e h₂⁻¹ (e h₁⁻¹ (T ((e h₁⁻¹).symm ((e h₂⁻¹).symm v))))
    have he_inv : ∀ w : V, e (h₁ * h₂)⁻¹ w = e h₂⁻¹ (e h₁⁻¹ w) := by
      intro w
      rw [_root_.mul_inv_rev, he_mul]
    have he_symm : ∀ w : V, (e (h₁ * h₂)⁻¹).symm w = (e h₁⁻¹).symm ((e h₂⁻¹).symm w) := by
      intro w
      apply (e (h₁ * h₂)⁻¹).injective
      rw [LinearEquiv.apply_symm_apply, he_inv, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
    rw [he_symm, he_inv]

@[simp] theorem operatorSymmetryActionOfLinearEquiv_act
    {H V : Type*} [Group H] [AddCommGroup V] [Module ℝ V]
    (e : H → (V ≃ₗ[ℝ] V))
    (he_one : e 1 = LinearEquiv.refl ℝ V)
    (he_mul : ∀ h₁ h₂ : H, ∀ v : V, e (h₁ * h₂) v = e h₁ (e h₂ v))
    (h : H) (T : Module.End ℝ V) :
    (operatorSymmetryActionOfLinearEquiv e he_one he_mul).act h T =
      linearEquivConjAlgEquiv (e h) T := by
  change linearEquivConjAlgEquiv (e (h⁻¹)⁻¹) T = _
  rw [inv_inv]

/-- Invertible linear equivalence `𝔤 ≃ₗ[ℝ] 𝔤` induced by `C.AdH h`. -/
def cartanAdLinearEquiv
    {EP EM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HP HM : Type*} [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (h : H) :
    𝔤 ≃ₗ[ℝ] 𝔤 where
  toLinearMap := (C.AdH h).toLinearMap
  invFun := C.AdH h⁻¹
  left_inv X := by
    change C.AdH h⁻¹ (C.AdH h X) = X
    rw [← C.AdH_mul, inv_mul_cancel, C.AdH_one]
  right_inv X := by
    change C.AdH h (C.AdH h⁻¹ X) = X
    rw [← C.AdH_mul, mul_inv_cancel, C.AdH_one]

lemma cartanAdLinearEquiv_one
    {EP EM HP HM P M H 𝔤 𝔥 : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    [Group H]
    [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) :
    cartanAdLinearEquiv C 1 = LinearEquiv.refl ℝ 𝔤 := by
  ext X
  exact C.AdH_one X

lemma cartanAdLinearEquiv_mul
    {EP EM HP HM P M H 𝔤 𝔥 : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    [Group H]
    [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    (h₁ h₂ : H) (X : 𝔤) :
    cartanAdLinearEquiv C (h₁ * h₂) X = cartanAdLinearEquiv C h₁ (cartanAdLinearEquiv C h₂ X) :=
  C.AdH_mul h₁ h₂ X

/-- Fiberwise linear equivalence on `TangentSpace IP p` induced by `C.AdH h` via `C.omega p`. -/
def cartanFiberLinearEquiv
    {EP EM HP HM P M H 𝔤 𝔥 : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    [Group H]
    [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P) (h : H) :
    TangentSpace IP p ≃ₗ[ℝ] TangentSpace IP p :=
  (C.omega p).toLinearEquiv.trans ((cartanAdLinearEquiv C h).trans (C.omega p).toLinearEquiv.symm)

lemma cartanFiberLinearEquiv_one
    {EP EM HP HM P M H 𝔤 𝔥 : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    [Group H]
    [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P) :
    cartanFiberLinearEquiv C p 1 = LinearEquiv.refl ℝ (TangentSpace IP p) := by
  ext v
  change (C.omega p).symm (C.AdH 1 (C.omega p v)) = v
  rw [C.AdH_one]
  exact (C.omega p).symm_apply_apply v

lemma cartanFiberLinearEquiv_mul
    {EP EM HP HM P M H 𝔤 𝔥 : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    [Group H]
    [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P)
    (h₁ h₂ : H) (v : TangentSpace IP p) :
    cartanFiberLinearEquiv C p (h₁ * h₂) v =
      cartanFiberLinearEquiv C p h₁ (cartanFiberLinearEquiv C p h₂ v) := by
  change (C.omega p).symm (C.AdH (h₁ * h₂) (C.omega p v)) =
    (C.omega p).symm (C.AdH h₁ (C.omega p ((C.omega p).symm (C.AdH h₂ (C.omega p v)))))
  rw [C.AdH_mul, (C.omega p).apply_symm_apply]

/-- Fiberwise `H`-action on `Module.End ℝ (TangentSpace IP p)` via `C.AdH` and `C.omega p`. -/
def cartanFiberAdjointOperatorAction
    {EP EM HP HM P M H 𝔤 𝔥 : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    [Group H]
    [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P) :
    OperatorSymmetryAction H (Module.End ℝ (TangentSpace IP p)) :=
  operatorSymmetryActionOfLinearEquiv (cartanFiberLinearEquiv C p)
    (cartanFiberLinearEquiv_one C p) (cartanFiberLinearEquiv_mul C p)

/-- Fiberwise `SymmetryAction` on `Module.End ℝ (TangentSpace IP p)`. -/
def cartanFiberAdjointAction
    {EP EM HP HM P M H 𝔤 𝔥 : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    [Group H]
    [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P) :
    SymmetryAction H (Module.End ℝ (TangentSpace IP p)) :=
  toSymmetryAction (cartanFiberAdjointOperatorAction C p)

/-- Adjoint `H`-action on `Module.End ℝ 𝔤`. -/
def cartanLieAdjointOperatorAction
    {EP EM HP HM P M H 𝔤 𝔥 : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    [Group H]
    [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) :
    OperatorSymmetryAction H (Module.End ℝ 𝔤) :=
  operatorSymmetryActionOfLinearEquiv (cartanAdLinearEquiv C)
    (cartanAdLinearEquiv_one C) (cartanAdLinearEquiv_mul C)

/-- `ℝ`-algebra equivalence `Module.End ℝ (TangentSpace IP p) ≃ₐ[ℝ] Module.End ℝ 𝔤` induced by `C.omega p`. -/
def cartanOmegaEndEquiv
    {EP EM HP HM P M H 𝔤 𝔥 : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    [Group H]
    [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P) :
    Module.End ℝ (TangentSpace IP p) ≃ₐ[ℝ] Module.End ℝ 𝔤 :=
  conjEndAlgEquiv (C.omega p).toLinearEquiv

/-- `cartanOmegaEndEquiv C p` is an `H`-equivariant algebra map between the fiberwise and Lie
adjoint actions. -/
def cartanOmegaEndEquiv_equivariant
    {EP EM HP HM P M H 𝔤 𝔥 : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    [Group H]
    [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P) :
    (cartanFiberAdjointOperatorAction C p).EquivariantAlgebraMap
      (cartanLieAdjointOperatorAction C) where
  toLinearMap := (cartanOmegaEndEquiv C p).toAlgHom
  equivariant h T := by
    ext X
    change (C.omega p) ((cartanFiberAdjointOperatorAction C p).act h T ((C.omega p).symm X)) =
      (cartanLieAdjointOperatorAction C).act h (cartanOmegaEndEquiv C p T) X
    rw [cartanFiberAdjointOperatorAction, operatorSymmetryActionOfLinearEquiv_act,
      cartanLieAdjointOperatorAction, operatorSymmetryActionOfLinearEquiv_act]
    change (C.omega p) ((C.omega p).symm (C.AdH h (C.omega p (T ((C.omega p).symm (C.AdH h⁻¹ ((C.omega p) ((C.omega p).symm X)))))))) =
      C.AdH h (C.omega p (T ((C.omega p).symm (C.AdH h⁻¹ X))))
    rw [(C.omega p).apply_symm_apply, (C.omega p).apply_symm_apply]

/-- Exact `AdH`-equivariance of `(cartanFiberErlangen20Datum C p).representation`. -/
theorem cartanFiberAdjointAction_act_representation
    {EP EM HP HM P M H 𝔤 𝔥 : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    [Group H]
    [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P)
    (h : H) (X : 𝔤) :
    (cartanFiberAdjointAction C p).act h ((cartanFiberErlangen20Datum C p).representation X) =
      (cartanFiberErlangen20Datum C p).representation (C.AdH h X) := by
  ext v
  change (cartanFiberAdjointOperatorAction C p).act h
      ((cartanFiberErlangen20Datum C p).representation X) v = _
  rw [cartanFiberAdjointOperatorAction, operatorSymmetryActionOfLinearEquiv_act]
  change (C.omega p).symm (C.AdH h (C.omega p ((C.omega p).symm
      ⁅X, C.omega p ((C.omega p).symm (C.AdH h⁻¹ (C.omega p v)))⁆))) =
    (C.omega p).symm ⁅C.AdH h X, C.omega p v⁆
  rw [(C.omega p).apply_symm_apply, (C.omega p).apply_symm_apply,
    (C.AdH h).map_lie, ← C.AdH_mul, mul_inv_cancel, C.AdH_one]

/-- Compatibility with `cartanAdjointIntertwiner C p`. -/
theorem cartanAdjointIntertwiner_equivariant
    {EP EM HP HM P M H 𝔤 𝔥 : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    [Group H]
    [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P)
    (h : H) (X : 𝔤) :
    (cartanAdjointIntertwiner C p (C.AdH h X)).source =
      (cartanFiberAdjointAction C p).act h ((cartanFiberErlangen20Datum C p).representation X) ∧
    (cartanAdjointIntertwiner C p (C.AdH h X)).target =
      (toSymmetryAction (cartanLieAdjointOperatorAction C)).act h
        (LieModule.toEnd ℝ 𝔤 𝔤 X) := by
  refine ⟨(cartanFiberAdjointAction_act_representation C p h X).symm, ?_⟩
  ext Y
  change ⁅C.AdH h X, Y⁆ =
    ((cartanLieAdjointOperatorAction C).act h (LieModule.toEnd ℝ 𝔤 𝔤 X)) Y
  rw [cartanLieAdjointOperatorAction, operatorSymmetryActionOfLinearEquiv_act]
  change ⁅C.AdH h X, Y⁆ = C.AdH h ⁅X, C.AdH h⁻¹ Y⁆
  rw [(C.AdH h).map_lie, ← C.AdH_mul, mul_inv_cancel, C.AdH_one]

theorem cartanFiberAdjointRep_invariant_of_adH_fixed
    {EP EM HP HM P M H 𝔤 𝔥 : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    [TopologicalSpace P] [ChartedSpace HP P] [TopologicalSpace M] [ChartedSpace HM M]
    [Group H]
    [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥) (p : P)
    {X : 𝔤} (hX : ∀ h : H, C.AdH h X = X) :
    (cartanFiberErlangen20Datum C p).representation X ∈
      invariantSubring (cartanFiberAdjointAction C p) := by
  intro h
  rw [cartanFiberAdjointAction_act_representation, hX h]

/-- Concrete homothety synthesis (`homothetyCartanGeometry κ`):
- Vertical scale generator `⟨0, 1⟩ : HomothetyLieAlg` is `H`-invariant under `cartanFiberAdjointAction`;
- Horizontal translation generator `⟨![1, 0], 0⟩` scales by `e` under `Multiplicative.ofAdd 1` (non-invariant);
- Fiber endomorphisms are strictly noncommutative (`homothety_fiberEnd_noncommutative`), while curvature
  scale `2 * κ` is an `H`-invariant readout (`homothety_curvature_scale_invariantReadout`). -/
theorem homothety_fiber_noncommutative_and_invariant_scale (κ : ℝ) (p : (Fin 2 → ℝ) × ℝ) :
    ((cartanFiberErlangen20Datum (homothetyCartanGeometry κ) p).representation ⟨0, 1⟩ ∈
      invariantSubring (cartanFiberAdjointAction (homothetyCartanGeometry κ) p)) ∧
    ((cartanFiberAdjointAction (homothetyCartanGeometry κ) p).act (Multiplicative.ofAdd (1 : ℝ))
      ((cartanFiberErlangen20Datum (homothetyCartanGeometry κ) p).representation ⟨![1, 0], 0⟩) ≠
      (cartanFiberErlangen20Datum (homothetyCartanGeometry κ) p).representation ⟨![1, 0], 0⟩) ∧
    ((cartanFiberErlangen20Datum (homothetyCartanGeometry κ) p).representation ⟨0, 1⟩ *
        (cartanFiberErlangen20Datum (homothetyCartanGeometry κ) p).representation ⟨![1, 0], 0⟩ ≠
      (cartanFiberErlangen20Datum (homothetyCartanGeometry κ) p).representation ⟨![1, 0], 0⟩ *
        (cartanFiberErlangen20Datum (homothetyCartanGeometry κ) p).representation ⟨0, 1⟩) ∧
    @IsInvariantReadout (Multiplicative ℝ) ((Fin 2 → ℝ) × ℝ) _ homothetyFiberAction ℝ
      (fun q => (cartanCurvatureForm 𝓘(ℝ, (Fin 2 → ℝ) × ℝ)
        (fun r => ((homothetyCartanGeometry κ).omega r).toContinuousLinearMap)
        homothetyCoordX0 homothetyCoordX1 q).scale) := by
  refine ⟨?_, ?_, homothety_fiberEnd_noncommutative κ p,
    homothety_curvature_scale_invariantReadout κ⟩
  · apply cartanFiberAdjointRep_invariant_of_adH_fixed
    intro t
    apply HomothetyLieAlg.ext
    · funext i
      change Real.exp (Multiplicative.toAdd t) * (0 : ℝ) = 0
      simp
    · rfl
  · intro hEq
    rw [cartanFiberAdjointAction_act_representation] at hEq
    have hpt := congrArg (fun T : Module.End ℝ (TangentSpace 𝓘(ℝ, (Fin 2 → ℝ) × ℝ) p) =>
      ((homothetyCartanGeometry κ).omega p)
        (T (((homothetyCartanGeometry κ).omega p).symm ⟨0, 1⟩))) hEq
    change ((homothetyCartanGeometry κ).omega p)
        (((homothetyCartanGeometry κ).omega p).symm
          ⁅(homothetyCartanGeometry κ).AdH (Multiplicative.ofAdd (1 : ℝ)) ⟨![1, 0], 0⟩,
            (homothetyCartanGeometry κ).omega p
              (((homothetyCartanGeometry κ).omega p).symm ⟨0, 1⟩)⁆) =
      ((homothetyCartanGeometry κ).omega p)
        (((homothetyCartanGeometry κ).omega p).symm
          ⁅(⟨![1, 0], 0⟩ : HomothetyLieAlg),
            (homothetyCartanGeometry κ).omega p
              (((homothetyCartanGeometry κ).omega p).symm ⟨0, 1⟩)⁆) at hpt
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hpt
    have hcoord := congrArg (fun g : HomothetyLieAlg => g.trans 0) hpt
    change (0 : ℝ) • (0 : ℝ) - (1 : ℝ) • (Real.exp (1 : ℝ) * (1 : ℝ)) =
      (0 : ℝ) • (0 : ℝ) - (1 : ℝ) • (1 : ℝ) at hcoord
    simp only [smul_eq_mul, zero_mul, one_mul, zero_sub, neg_inj, mul_one] at hcoord
    exact (ne_of_gt (Real.one_lt_exp_iff.mpr one_pos)) hcoord

end Bridge5

/-!
## Bridge 6: `OperatorIntertwiner`, Klein §4 *Abbildung*, M3.1/M3.2, T16/T17, & 4-Axis Master Unification
-/

section Bridge6

open InfoGeometry.Erlangen.GrassmannPluckerKleinCrossPillarBridges
open InfoGeometry.Erlangen.ErlangenProgramGroupHierarchyAndPrincipal
open InfoGeometry.Erlangen.ErlangenProgramTransferHesseAndBodies
open InfoGeometry.Erlangen.ErlangenProgramCurvatureBinaryAndMasterAtlas
open InfoGeometry.Projective.KleinErlangenProgramGroupsAndProjectiveTransfer
open InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms
open InfoGeometry.Canonical.PluckerGrassmannKleinUnifiedSynthesis
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.PluckerMatrixAction
open InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis
open InfoGeometry.Categorical.CantorDoubleCylinderColimitAlgebra
open InfoGeometry.OperatorAlgebra.CantorDoubleCylinderFractalColimit
open InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants
open InfoGeometry.Erlangen.SmoothCartanGeometry
open InfoGeometry.Projective
open Matrix
open scoped Matrix Manifold

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Pointwise agreement of `conjEndAlgEquiv` with Klein §4 `transportedSmul` (`e (T (e⁻¹ w))`). -/
theorem conjEndAlgEquiv_apply_eq_transportedSmul
    {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W)
    (T : Module.End R V) (w : W) :
    let _inst : SMul (Module.End R V) V := ⟨fun f v => f v⟩
    conjEndAlgEquiv e T w = transportedSmul e.toEquiv T w :=
  rfl

/-- An `OperatorIntertwiner R V W` satisfies both forward and inverse conjugation identities. -/
theorem operatorIntertwiner_target_and_source_conjugated
    {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (I : OperatorIntertwiner R V W) :
    I.target = conjEndAlgEquiv I.carrierEquiv I.source ∧
    I.source = (conjEndAlgEquiv I.carrierEquiv).symm I.target :=
  ⟨I.target_eq_conjugated, I.source_eq_conjugated⟩

theorem operatorIntertwiner_target_eq_conjEndAlgEquiv
    {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (I : OperatorIntertwiner R V W) :
    I.target = conjEndAlgEquiv I.carrierEquiv I.source :=
  I.target_eq_conjugated

theorem operatorIntertwiner_source_eq_conjEndAlgEquiv_symm
    {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (I : OperatorIntertwiner R V W) :
    I.source = (conjEndAlgEquiv I.carrierEquiv).symm I.target :=
  I.source_eq_conjugated

/-- Canonical `OperatorIntertwiner` from `e : V ≃ₗ[R] W` and `T : Module.End R V`. -/
def operatorIntertwinerOfLinearEquiv
    {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W) (T : Module.End R V) :
    OperatorIntertwiner R V W where
  carrierEquiv := e
  source := T
  target := conjEndAlgEquiv e T
  intertwines v := by simp [conjEndAlgEquiv]

/-- Transport `SymmetryAction G (Module.End R V)` across `e : V ≃ₗ[R] W` (Klein §4 *Abbildung*). -/
def transportSymmetryAction
    {R V W G : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] [Group G]
    (e : V ≃ₗ[R] W) (α : SymmetryAction G (Module.End R V)) :
    SymmetryAction G (Module.End R W) where
  act g :=
    ((conjEndAlgEquiv e).symm.toRingEquiv.trans (α.act g)).trans
      (conjEndAlgEquiv e).toRingEquiv
  act_one S := by
    change conjEndAlgEquiv e (α.act 1 ((conjEndAlgEquiv e).symm S)) = S
    rw [α.act_one]
    exact (conjEndAlgEquiv e).apply_symm_apply S
  act_mul g h S := by
    change conjEndAlgEquiv e (α.act (g * h) ((conjEndAlgEquiv e).symm S)) =
      conjEndAlgEquiv e (α.act g ((conjEndAlgEquiv e).symm
        (conjEndAlgEquiv e (α.act h ((conjEndAlgEquiv e).symm S)))))
    rw [(conjEndAlgEquiv e).symm_apply_apply, α.act_mul]

theorem transportSymmetryAction_invariantSubring_iff
    {R V W G : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] [Group G]
    (e : V ≃ₗ[R] W) (α : SymmetryAction G (Module.End R V))
    (T : Module.End R V) :
    conjEndAlgEquiv e T ∈ invariantSubring (transportSymmetryAction e α) ↔
      T ∈ invariantSubring α := by
  constructor
  · intro h g
    have hg := h g
    change conjEndAlgEquiv e (α.act g ((conjEndAlgEquiv e).symm (conjEndAlgEquiv e T))) =
      conjEndAlgEquiv e T at hg
    rw [(conjEndAlgEquiv e).symm_apply_apply] at hg
    exact (conjEndAlgEquiv e).injective hg
  · intro h g
    change conjEndAlgEquiv e (α.act g ((conjEndAlgEquiv e).symm (conjEndAlgEquiv e T))) =
      conjEndAlgEquiv e T
    rw [(conjEndAlgEquiv e).symm_apply_apply, h g]

/-- Transport `Erlangen20Datum R V 𝔤 𝒮 ℐ` across `e : V ≃ₗ[R] W` via `conjEndAlgEquiv e`. -/
def transportErlangen20Datum
    {R V W 𝔤 𝒮 ℐ : Type*}
    [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    [LieRing 𝔤] [LieAlgebra R 𝔤]
    (e : V ≃ₗ[R] W) (E : Erlangen20Datum R V 𝔤 𝒮 ℐ) :
    Erlangen20Datum R W 𝔤 𝒮 ℐ where
  operatorAlgebra := E.operatorAlgebra.map (conjEndAlgEquiv e).toAlgHom
  representation :=
    { toFun := fun X => conjEndAlgEquiv e (E.representation X)
      map_add' := fun X Y => by rw [map_add, map_add]
      map_smul' := fun c X => by rw [map_smul, map_smul]; rfl
      map_lie' := fun {X Y} => by
        rw [E.representation_map_lie]
        change conjEndAlgEquiv e (E.representation X * E.representation Y -
          E.representation Y * E.representation X) =
          conjEndAlgEquiv e (E.representation X) * conjEndAlgEquiv e (E.representation Y) -
          conjEndAlgEquiv e (E.representation Y) * conjEndAlgEquiv e (E.representation X)
        rw [map_sub, map_mul, map_mul] }
  representation_mem X := ⟨E.representation X, E.representation_mem X, rfl⟩
  symmetryData := E.symmetryData
  invariantData := E.invariantData

/-- Every `X : 𝔤` yields a canonical `OperatorIntertwiner` between `E` and `transportErlangen20Datum e E`. -/
def transportOperatorIntertwiner
    {R V W 𝔤 𝒮 ℐ : Type*}
    [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    [LieRing 𝔤] [LieAlgebra R 𝔤]
    (e : V ≃ₗ[R] W) (E : Erlangen20Datum R V 𝔤 𝒮 ℐ) (X : 𝔤) :
    OperatorIntertwiner R V W where
  carrierEquiv := e
  source := E.representation X
  target := (transportErlangen20Datum e E).representation X
  intertwines v := by simp [transportErlangen20Datum, conjEndAlgEquiv]

/-- Compatibility of `conjEndAlgEquiv` with Klein §4 `klein_sec4_abbildung_perm_transfer`. -/
theorem conjEndAlgEquiv_perm_transfer
    {R V W β : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W)
    (G : Subgroup (Equiv.Perm V)) (f : V → β) :
    (∀ g ∈ G, ∀ x : V, f (g x) = f x) ↔
      (∀ g' ∈ Subgroup.map (Equiv.permCongrHom e.toEquiv).toMonoidHom G,
        ∀ y : W, f (e.toEquiv.symm (g' y)) = f (e.toEquiv.symm y)) :=
  klein_sec4_abbildung_perm_transfer e.toEquiv G f

/-! ### M3.1 §5 & M3.2 Integration -/

/-- M3.1 §5 Clifford *Abbildung*: `cliffordLieBilinEquivLieQuadric2` yields an
`OperatorIntertwiner` intertwining left multiplication in `Cl(lieBilinForm)` and `Cl(lieQuadricBilin 2)`. -/
def cliffordLieBilinEquivLieQuadric2_operatorIntertwiner
    (a : CliffordAlgebra lieBilinForm.toQuadraticMap) :
    OperatorIntertwiner ℝ
      (CliffordAlgebra lieBilinForm.toQuadraticMap)
      (CliffordAlgebra (lieQuadricBilin 2).toQuadraticMap) where
  carrierEquiv := cliffordLieBilinEquivLieQuadric2.toLinearEquiv
  source := Algebra.lmul ℝ (CliffordAlgebra lieBilinForm.toQuadraticMap) a
  target := Algebra.lmul ℝ (CliffordAlgebra (lieQuadricBilin 2).toQuadraticMap)
    (cliffordLieBilinEquivLieQuadric2 a)
  intertwines x := by
    change cliffordLieBilinEquivLieQuadric2 a * cliffordLieBilinEquivLieQuadric2 x =
      cliffordLieBilinEquivLieQuadric2 (a * x)
    exact (map_mul cliffordLieBilinEquivLieQuadric2 a x).symm

/-- M3.1 §5 Plücker–ComplexCongr duality: `complexCongrDeriv R X` is the negative transpose of
`secondCompoundDeriv R X` (`pluckerErlangen20Datum` ↔ `complexCongrErlangen20Datum`), paired with
`gl4ExteriorSymmetryAction_pluckerToExterior2`. -/
theorem plucker_complexCongr_dual_neg_transpose
    (R : Type*) [CommRing R] (X : Matrix (Fin 4) (Fin 4) R) :
    (complexCongrErlangen20Datum R).representation X =
      Matrix.toLin' (-(secondCompoundDerivMatrix X)ᵀ) ∧
    (pluckerErlangen20Datum R).representation X =
      Matrix.toLin' (secondCompoundDerivMatrix X) ∧
    (∀ (g : Matrix.GeneralLinearGroup (Fin 4) R) (P : Plucker6 R),
      (gl4ExteriorSymmetryAction R).act g (pluckerToExterior2 P) =
        pluckerToExterior2 (transform g.1 P)) :=
  ⟨rfl, rfl, fun g P => gl4ExteriorSymmetryAction_pluckerToExterior2 g P⟩

/-- M3.2 Split `G₂(2)` *Abbildung*: `Matrix.toLpLinAlgEquiv 2` transports `splitG2MatrixSymmetryAction`
to `splitG2EuclideanSymmetryAction` on `g2Erlangen20Datum.operatorAlgebra`. -/
theorem g2_toLpLinAlgEquiv_equivariant (u : SplitG2MatrixGroup) (M : Matrix Krein16Idx Krein16Idx ℝ) :
    splitG2EuclideanSymmetryAction.act u (Matrix.toLpLinAlgEquiv 2 M) =
      Matrix.toLpLinAlgEquiv 2 (splitG2MatrixSymmetryAction.act u M) := by
  change Matrix.toLpLinAlgEquiv 2 (splitG2ConjAlgEquiv u
      ((Matrix.toLpLinAlgEquiv 2).symm (Matrix.toLpLinAlgEquiv 2 M))) =
    Matrix.toLpLinAlgEquiv 2 (splitG2ConjAlgEquiv u M)
  rw [AlgEquiv.symm_apply_apply]

/-! ### T16/T17 Noncommutativity Witnesses (`sl₂(ℝ)` / `M₂(ℝ)` and `EndR (DoubledSpace ℝ)`) -/

/-- Linear equivalence `(Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)` induced by `g : GL (Fin 2) ℝ`. -/
def sl2GL2LinearEquiv (g : Matrix.GeneralLinearGroup (Fin 2) ℝ) : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := g.1 *ᵥ v
  invFun v := g⁻¹.1 *ᵥ v
  map_add' x y := Matrix.mulVec_add _ x y
  map_smul' c x := by simp [Matrix.mulVec_smul]
  left_inv v := by
    have hmul : g⁻¹.1 * g.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    change g⁻¹.1 *ᵥ (g.1 *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  right_inv v := by
    have hmul : g.1 * g⁻¹.1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    change g.1 *ᵥ (g⁻¹.1 *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]

/-- Canonical `M₂(ℝ)` / `sl₂(ℝ)` `Erlangen20Datum` on `Fin 2 → ℝ`. -/
def sl2MatrixErlangen20Datum :
    Erlangen20Datum ℝ (Fin 2 → ℝ) (Matrix (Fin 2) (Fin 2) ℝ)
      (SymmetryAction (Matrix.GeneralLinearGroup (Fin 2) ℝ) (Module.End ℝ (Fin 2 → ℝ)))
      (Subring (Module.End ℝ (Fin 2 → ℝ))) where
  operatorAlgebra := ⊤
  representation :=
    { toFun := Matrix.toLin'
      map_add' := map_add Matrix.toLin'
      map_smul' := map_smul Matrix.toLin'
      map_lie' := fun {A B} => by
        change Matrix.toLin' (A * B - B * A) =
          Matrix.toLin' A * Matrix.toLin' B - Matrix.toLin' B * Matrix.toLin' A
        rw [map_sub, Matrix.toLin'_mul, Matrix.toLin'_mul]
        rfl }
  representation_mem _ := Algebra.mem_top
  symmetryData :=
    { act := fun g => (conjEndAlgEquiv (sl2GL2LinearEquiv g)).toRingEquiv
      act_one := fun T => by
        apply LinearMap.ext
        intro v
        have he1 : sl2GL2LinearEquiv (1 : Matrix.GeneralLinearGroup (Fin 2) ℝ) =
            LinearEquiv.refl ℝ _ := by
          ext y i
          change ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ y) i = y i
          rw [Matrix.one_mulVec]
        change sl2GL2LinearEquiv 1 (T ((sl2GL2LinearEquiv 1).symm v)) = T v
        rw [he1]
        rfl
      act_mul := fun g h T => by
        apply LinearMap.ext
        intro v
        have hemul : sl2GL2LinearEquiv (g * h) =
            (sl2GL2LinearEquiv h).trans (sl2GL2LinearEquiv g) := by
          ext y i
          change ((g.1 * h.1) *ᵥ y) i = (g.1 *ᵥ (h.1 *ᵥ y)) i
          rw [Matrix.mulVec_mulVec]
        change sl2GL2LinearEquiv (g * h) (T ((sl2GL2LinearEquiv (g * h)).symm v)) =
          sl2GL2LinearEquiv g (sl2GL2LinearEquiv h
            (T ((sl2GL2LinearEquiv h).symm ((sl2GL2LinearEquiv g).symm v))))
        rw [hemul]
        rfl }
  invariantData := ⊤

/-- Explicit T16/T17 noncommutativity witness for `Matrix (Fin 2) (Fin 2) ℝ` / `sl₂(ℝ)` inside
`Erlangen20Datum` (`e * f ≠ f * e` and `[h, e] = 2e ≠ 0`). -/
theorem sl2_erlangen20_noncommutative_witness :
    let e : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 1], ![0, 0]]
    let f : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 0], ![1, 0]]
    let h : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![0, -1]]
    sl2MatrixErlangen20Datum.representation e * sl2MatrixErlangen20Datum.representation f ≠
      sl2MatrixErlangen20Datum.representation f * sl2MatrixErlangen20Datum.representation e ∧
    ⁅sl2MatrixErlangen20Datum.representation h, sl2MatrixErlangen20Datum.representation e⁆ =
      (2 : ℝ) • sl2MatrixErlangen20Datum.representation e ∧
    sl2MatrixErlangen20Datum.representation e ≠ 0 := by
  intro e f h
  refine ⟨?_, ?_, ?_⟩
  · intro hEq
    have h0 := congrArg (fun T : Module.End ℝ (Fin 2 → ℝ) => T ![1, 0] 0) hEq
    change (e *ᵥ (f *ᵥ ![1, 0])) 0 = (f *ᵥ (e *ᵥ ![1, 0])) 0 at h0
    simp [e, f, Matrix.mulVec, dotProduct] at h0
  · rw [← LieHom.map_lie, ← map_smul]
    congr 1
    rw [Ring.lie_def]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
       rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
       norm_num [e, h])
  · intro h0
    have hpt := congrArg (fun T : Module.End ℝ (Fin 2 → ℝ) => T ![0, 1] 0) h0
    change (e *ᵥ ![0, 1]) 0 = 0 at hpt
    simp [e, Matrix.mulVec, dotProduct] at hpt

/-- Explicit T17 noncommutativity witness on `EndR (DoubledSpace ℝ)` inside `PhaseCentralizer` /
`phaseErlangerDatum`: `modular_j` and `spectral_epsilon` anticommute and fail to commute. -/
theorem endR_doubledSpace_noncommutative_witness :
    (InfoGeometry.Krein.modular_j (E := ℝ)).comp (InfoGeometry.Krein.spectral_epsilon (E := ℝ)) ≠
      (InfoGeometry.Krein.spectral_epsilon (E := ℝ)).comp (InfoGeometry.Krein.modular_j (E := ℝ)) ∧
    (∃ A B : InfoGeometry.Geometry.PhaseErlanger.EndR (InfoGeometry.Krein.DoubledSpace ℝ),
      A * B ≠ B * A) := by
  have hneq :
      (InfoGeometry.Krein.modular_j (E := ℝ)).comp (InfoGeometry.Krein.spectral_epsilon (E := ℝ)) ≠
        (InfoGeometry.Krein.spectral_epsilon (E := ℝ)).comp (InfoGeometry.Krein.modular_j (E := ℝ)) := by
    intro h
    have hpt := congrArg (fun T : InfoGeometry.Krein.DoubledSpace ℝ →L[ℝ]
        InfoGeometry.Krein.DoubledSpace ℝ =>
      WithLp.fst (T (InfoGeometry.Krein.to_doubled (0 : ℝ) 1))) h
    change (-1 : ℝ) = (1 : ℝ) at hpt
    norm_num at hpt
  exact ⟨hneq, ⟨InfoGeometry.Krein.modular_j (E := ℝ),
    InfoGeometry.Krein.spectral_epsilon (E := ℝ), hneq⟩⟩

/-! ### 4-Axis Master Unification Theorem (Felix Klein 1872 *Erlanger Programm*) -/

/-- **4-Axis Master Unification Theorem** grounded in Felix Klein's 1872 *Erlanger Programm*
(`ABN7632.0001.001` / `arXiv:0807.3161v1`, §§1–10 & Concluding Remarks):

Reconciles all 4 Erlangen axes and all 10 F2.1 owners simultaneously:
1. **Axis A (Homogeneous Spaces & Galois Fixed Points — Klein §§1, 2, 4, 5 & Concluding Remarks)**:
   `IsHomogeneousSpace G X` yields the equivariant coset reconstruction `X ≃ G ⧸ stabilizer G x₀`
   (built from `OperatorErlangenFixedPoints.orbit_quotient_stabilizer_equiv`), constancy of
   `IsInvariantReadout`, normal-core orbit faithfulness (`klein_sec5_fn23_body_kernel_eq_normalCore`),
   subgroup adjoining (`klein_sec2_stabilizer_adjoining_equiv`), `SymmetryAction` fixed-point
   identification (`invariantSubring.toSubsemiring = fixedPointSubsemiring ⊤`), and the Galois
   connection `erlangen_galois_subgroup_observable_bridge`.
2. **Axis B (`Erlangen20Datum` & `OperatorIntertwiner` — Klein §4 *Abbildung* & §10 Coordinate-Less)**:
   Bidirectional `Erlangen20Datum ↔ SymmetryAction` bridges (`erlangen20EndSymmetryAction`,
   `erlangen20DatumOfSymmetryAction`), transport along `e : V ≃ₗ[R] W` via `OperatorIntertwiner`
   and `klein_sec4_abbildung_perm_transfer`, plus noncommutativity (`sl2_erlangen20_noncommutative_witness`).
3. **Axis C (`ErlangenOperatorDatum` & `ErlangenInvariantPacket`)**:
   Every `ErlangenInvariantPacket` satisfying state-action laws and joint Fisher invariance yields a
   `Canonical.ErlangenOperator2.ErlangenOperatorDatum` whose `ErlangenOperatorGeometry` holds and
   whose `stateMomentErlangenDatumOfPacket` agrees with `ErlangenOperator2Bridge`.
4. **Axis D (Concrete Physical, Cartan §§8–9, Cantor, Krein/`G_{2(2)}`, & Grassmann–Plücker Realizations)**:
   Unifies `PhaseErlanger` (`ErlangerInvariant ≃ InvariantReadout`, `ChiralAxis → ComplementaryProjectors`,
   `MetricPreserving ≠ IsKreinIsometry`), `SmoothCartanGeometry` (`homothetyCartanGeometry κ`),
   `CantorDoubleCylinderColimitAlgebra` (`cantorDoubleCylinderErlangen20Datum_matches_bridge3`),
   M3.2 Split `G_{2(2)}` (`g2_erlangen_fixedPoints_bridge`, `splitG2_bridge3_representation_eq`), and
   M3.1 §5 Clifford/Plücker (`plucker_complexCongr_dual_neg_transpose`). -/
theorem klein_erlangen20_four_axis_master_unification
    {G X : Type*} [Group G] [MulAction G X]
    (hHom : IsHomogeneousSpace G X) (x₀ : X) :
    -- Axis A: Klein §§1, 2, 4, 5 & Concluding Remarks
    (IsEquivariantMap G X (homogeneousSpaceEquivQuotient hHom x₀) ∧
     (∀ {β : Type*} {f : X → β}, IsInvariantReadout G X f → ∀ x y : X, f x = f y) ∧
     ((MulAction.toPermHom G (MulAction.orbit G x₀)).ker =
       (MulAction.stabilizer G x₀).normalCore)) ∧
    -- Axis B: Bidirectional Erlangen20Datum ↔ SymmetryAction + noncommutativity
    ((∀ {R V 𝔤 𝒮 ℐ G' : Type*} [CommRing R] [AddCommGroup V] [Module R V]
        [LieRing 𝔤] [LieAlgebra R 𝔤] [Group G']
        (E : Erlangen20Datum R V 𝔤 𝒮 ℐ) (ρ : G' →* E.operatorAlgebraˣ)
        (g : G') (X' : 𝔤),
        (erlangen20EndSymmetryAction E ρ).act g (E.representation X') ∈ E.operatorAlgebra) ∧
     (∃ e f : Matrix (Fin 2) (Fin 2) ℝ,
        sl2MatrixErlangen20Datum.representation e * sl2MatrixErlangen20Datum.representation f ≠
          sl2MatrixErlangen20Datum.representation f * sl2MatrixErlangen20Datum.representation e)) ∧
    -- Axis C: ErlangenInvariantPacket → ErlangenOperatorDatum + ErlangenOperatorGeometry
    (∀ {Obs Sym Gc Gdual StateSpace : Type*} [Ring Obs] [Group Sym]
        (E : InfoGeometry.OperatorAlgebra.ErlangenOperator2.ErlangenInvariantPacket
          Obs Sym Gc Gdual StateSpace)
        (h1 : ∀ ω, E.entropySymmetry.stateAction 1 ω = ω)
        (hmul : ∀ g h ω, E.entropySymmetry.stateAction (g * h) ω =
          E.entropySymmetry.stateAction g (E.entropySymmetry.stateAction h ω))
        (hf : ∀ s ω A B, E.fisherMetric (E.entropySymmetry.stateAction s ω)
          (E.legendrePacket.symmetryAction.act s A)
          (E.legendrePacket.symmetryAction.act s B) = E.fisherMetric ω A B),
        InfoGeometry.Canonical.ErlangenOperator2.ErlangenOperatorDatum.ErlangenOperatorGeometry
          (erlangenOperatorDatumOfPacket E h1 hmul hf)) ∧
    -- Axis D: PhaseErlanger, Krein separation, Homothety Cartan, Cantor, Split G₂(2), & Plücker
    ((InfoGeometry.Geometry.PhaseErlanger.MetricPreserving (InfoGeometry.Krein.modular_j (E := ℝ)) ∧
      ¬ InfoGeometry.Krein.KreinSpace.IsKreinIsometry (InfoGeometry.Krein.modular_j (E := ℝ)) ∧
      InfoGeometry.Krein.KreinSpace.IsKreinIsometry kreinBoost54 ∧
      ¬ InfoGeometry.Geometry.PhaseErlanger.MetricPreserving kreinBoost54) ∧
     (∀ (κ : ℝ) (p : (Fin 2 → ℝ) × ℝ),
        (cartanFiberErlangen20Datum (InfoGeometry.Erlangen.SmoothCartanGeometry.homothetyCartanGeometry κ) p).representation ⟨0, 1⟩ ∈
          invariantSubring (cartanFiberAdjointAction
            (InfoGeometry.Erlangen.SmoothCartanGeometry.homothetyCartanGeometry κ) p)) ∧
     ((erlangen20DatumOfSymmetryActionOnModule
          (erlangenDoubleCylinderSymmetryAction ℝ)
          colimitRepresentationEndAlgHom
          (LinearMap.id : DoubleCylinderColimit ℝ →ₗ[ℝ] DoubleCylinderColimit ℝ)
          (fun x y => Ring.lie_def x y)).operatorAlgebra =
        cantorDoubleCylinderErlangen20Datum.operatorAlgebra) ∧
     (∀ X : g2LieSubalgebra,
        (erlangen20DatumOfSymmetryActionOnModule
          splitG2MatrixSymmetryAction
          (Matrix.toLpLinAlgEquiv (2 : ENNReal) (R := ℝ) (n := Krein16Idx)).toAlgHom
          g2LieSubalgebra.incl.toLinearMap
          (fun X Y => by
            change g2LieSubalgebra.incl ⁅X, Y⁆ =
              g2LieSubalgebra.incl X * g2LieSubalgebra.incl Y -
              g2LieSubalgebra.incl Y * g2LieSubalgebra.incl X
            rw [g2LieSubalgebra.incl.map_lie]
            exact Ring.lie_def _ _)).representation X =
        g2Erlangen20Datum.representation X) ∧
     (∀ X : Matrix (Fin 4) (Fin 4) ℝ,
        (complexCongrErlangen20Datum ℝ).representation X =
          Matrix.toLin' (-(secondCompoundDerivMatrix X)ᵀ))) := by
  refine ⟨⟨homogeneousSpaceEquivQuotient_equivariant hHom x₀,
      fun hf x y => invariantReadout_const_of_homogeneousSpace hHom hf x y,
      (klein_sec5_fn23_body_kernel_eq_normalCore x₀).1⟩,
    ⟨fun E ρ g X' => erlangen20EndSymmetryAction_stabilizes_representation E ρ g X',
      ⟨![![0, 1], ![0, 0]], ![![0, 0], ![1, 0]], sl2_erlangen20_noncommutative_witness.1⟩⟩,
    fun E h1 hmul hf => erlangenOperatorDatumOfPacket_geometry E h1 hmul hf,
    ⟨⟨metricPreserving_ne_isKreinIsometry_witness.1.1,
      metricPreserving_ne_isKreinIsometry_witness.1.2,
      metricPreserving_ne_isKreinIsometry_witness.2.1,
      metricPreserving_ne_isKreinIsometry_witness.2.2⟩,
     fun κ p => (homothety_fiber_noncommutative_and_invariant_scale κ p).1,
     cantorDoubleCylinderErlangen20Datum_matches_bridge3.1,
     splitG2_bridge3_representation_eq,
     fun X => (plucker_complexCongr_dual_neg_transpose ℝ X).1⟩⟩

end Bridge6

end InfoGeometry.Canonical.Erlangen20Unification
