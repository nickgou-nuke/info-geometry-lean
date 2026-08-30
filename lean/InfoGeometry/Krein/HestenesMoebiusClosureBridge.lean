import InfoGeometry.Krein.HestenesConnesWilsonBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace BigOperators

noncomputable section

/-!
# InfoGeometry.Krein.HestenesMoebiusClosureBridge

Möbius closure data for the Hestenes--Krein / Connes--Wilson lane.

This file deliberately does **not** construct a global conformal field theory,
a representation theorem for `SL(2,ℝ)`, or a compactification theorem for a
Cantor boundary.  Instead it provides a theorem-safe calibration interface:

* a determinant-one Möbius parameter record;
* a supplied projective action on the finite atom/face index set;
* a supplied bounded ring-automorphism action on operators;
* a supplied Krein-isometric vector action fixing the vacuum `Ω`;
* invariance readbacks for Ω-expectations and Connes--Wilson holonomies.

The mathematical doctrine is property-gated: a concrete CFT/Jones/Cantor backend
supplies the Möbius representation laws, while this bridge records the exact
consequences needed by the real Hestenes--Krein volume pipeline.
-/

namespace InfoGeometry.Krein.HestenesMoebiusClosureBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.HestenesModularKMSBridge
open InfoGeometry.Krein.HestenesKreinVacuumBridge
open InfoGeometry.Krein.HestenesConnesWilsonBridge
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Canonical.StandardFormOmegaVolumeBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance moebiusClosureNormedRing : NormedRing EndH := inferInstance
noncomputable local instance moebiusClosureNormedAlgebra : NormedAlgebra ℝ EndH :=
  inferInstance
noncomputable local instance moebiusClosureNormedAlgebraRat : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance moebiusClosureTopologicalRing : IsTopologicalRing EndH := inferInstance
local instance moebiusClosureCompleteSpace : CompleteSpace EndH := inferInstance
local instance moebiusClosureSMulCommClass : SMulCommClass ℝ EndH EndH := inferInstance
local instance moebiusClosureIsScalarTower : IsScalarTower ℝ EndH EndH := inferInstance

/--
A determinant-one real Möbius parameter, read as an `SL(2,ℝ)` matrix
`[[a,b],[c,d]]` at this data level.
-/
@[rep_depth projective]
structure MoebiusParameter where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  det_one : a * d - b * c = 1

def MoebiusParameter.toMatrix (g : MoebiusParameter) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![g.a, g.b; g.c, g.d]

@[ext]
theorem MoebiusParameter.ext {g h : MoebiusParameter}
    (ha : g.a = h.a) (hb : g.b = h.b) (hc : g.c = h.c) (hd : g.d = h.d) :
    g = h := by
  cases g
  cases h
  simp_all

@[simp]
theorem MoebiusParameter.toMatrix_det (g : MoebiusParameter) :
    g.toMatrix.det = 1 := by
  dsimp [MoebiusParameter.toMatrix]
  rw [Matrix.det_fin_two]
  exact g.det_one

def MoebiusParameter.mul (g h : MoebiusParameter) : MoebiusParameter where
  a := g.a * h.a + g.b * h.c
  b := g.a * h.b + g.b * h.d
  c := g.c * h.a + g.d * h.c
  d := g.c * h.b + g.d * h.d
  det_one := by
    calc
      (g.a * h.a + g.b * h.c) * (g.c * h.b + g.d * h.d) -
          (g.a * h.b + g.b * h.d) * (g.c * h.a + g.d * h.c) =
        (g.a * g.d - g.b * g.c) * (h.a * h.d - h.b * h.c) := by ring
      _ = 1 := by rw [g.det_one, h.det_one]; norm_num

theorem MoebiusParameter.toMatrix_mul (g h : MoebiusParameter) :
    (g.mul h).toMatrix = g.toMatrix * h.toMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MoebiusParameter.mul, MoebiusParameter.toMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]
  <;> ring

theorem MoebiusParameter.toMatrix_injective :
    Function.Injective MoebiusParameter.toMatrix := by
  intro g h hgh
  cases g with
  | mk ga gb gc gd hg =>
      cases h with
      | mk ha hb hc hd hh =>
          have haa := congrArg
            (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hgh
          have hab := congrArg
            (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hgh
          have hac := congrArg
            (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) hgh
          have had := congrArg
            (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) hgh
          simp [MoebiusParameter.toMatrix] at haa hab hac had
          subst ha
          subst hb
          subst hc
          subst hd
          rfl

def MoebiusParameter.one : MoebiusParameter where
  a := 1
  b := 0
  c := 0
  d := 1
  det_one := by norm_num

def MoebiusParameter.inv (g : MoebiusParameter) : MoebiusParameter where
  a := g.d
  b := -g.b
  c := -g.c
  d := g.a
  det_one := by
    rw [← g.det_one]
    ring

theorem MoebiusParameter.one_mul (g : MoebiusParameter) :
    MoebiusParameter.one.mul g = g := by
  cases g
  ext <;> simp [MoebiusParameter.one, MoebiusParameter.mul]

theorem MoebiusParameter.mul_one (g : MoebiusParameter) :
    g.mul MoebiusParameter.one = g := by
  cases g
  ext <;> simp [MoebiusParameter.one, MoebiusParameter.mul]

theorem MoebiusParameter.mul_inv (g : MoebiusParameter) :
    g.mul g.inv = MoebiusParameter.one := by
  apply MoebiusParameter.ext <;> simp [MoebiusParameter.one, MoebiusParameter.inv,
    MoebiusParameter.mul]
  · rw [← g.det_one]
    ring
  · ring
  · ring
  · rw [← g.det_one]
    ring

theorem MoebiusParameter.inv_mul (g : MoebiusParameter) :
    g.inv.mul g = MoebiusParameter.one := by
  apply MoebiusParameter.ext <;> simp [MoebiusParameter.one, MoebiusParameter.inv,
    MoebiusParameter.mul]
  · rw [← g.det_one]
    ring
  · ring
  · ring
  · rw [← g.det_one]
    ring

theorem MoebiusParameter.mul_assoc
    (g h k : MoebiusParameter) :
    (g.mul h).mul k = g.mul (h.mul k) := by
  cases g
  cases h
  cases k
  apply MoebiusParameter.ext <;> simp [MoebiusParameter.mul] <;> ring

theorem MoebiusParameter.toMatrix_isUnit (g : MoebiusParameter) :
    IsUnit g.toMatrix := by
  apply (Matrix.isUnit_iff_isUnit_det (A := g.toMatrix)).mpr
  rw [g.toMatrix_det]
  exact isUnit_one

theorem MoebiusParameter.toMatrix_ne_zero (g : MoebiusParameter) :
    g.toMatrix ≠ 0 := by
  intro hzero
  have ha : g.a = 0 := by
    simpa [MoebiusParameter.toMatrix] using congrFun (congrFun hzero 0) 0
  have hb : g.b = 0 := by
    simpa [MoebiusParameter.toMatrix] using congrFun (congrFun hzero 0) 1
  have hc : g.c = 0 := by
    simpa [MoebiusParameter.toMatrix] using congrFun (congrFun hzero 1) 0
  have hd : g.d = 0 := by
    simpa [MoebiusParameter.toMatrix] using congrFun (congrFun hzero 1) 1
  have hdet := g.det_one
  rw [ha, hb, hc, hd] at hdet
  norm_num at hdet

def MoebiusParameter.inverseMatrix (g : MoebiusParameter) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![g.d, -g.b; -g.c, g.a]

@[simp]
theorem MoebiusParameter.inv_toMatrix (g : MoebiusParameter) :
    g.inv.toMatrix = g.inverseMatrix :=
  rfl

@[simp]
theorem MoebiusParameter.one_toMatrix :
    MoebiusParameter.one.toMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MoebiusParameter.one, MoebiusParameter.toMatrix,
      Matrix.one_apply]

@[simp]
theorem MoebiusParameter.inverseMatrix_det (g : MoebiusParameter) :
    g.inverseMatrix.det = 1 := by
  dsimp [MoebiusParameter.inverseMatrix]
  rw [Matrix.det_fin_two]
  change (g.d * g.a - (-g.b) * (-g.c) : ℝ) = 1
  rw [← g.det_one]
  ring

theorem MoebiusParameter.toMatrix_mul_inverseMatrix (g : MoebiusParameter) :
    g.toMatrix * g.inverseMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MoebiusParameter.toMatrix, MoebiusParameter.inverseMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]
  · rw [← g.det_one]
    ring
  · ring
  · ring
  · rw [← g.det_one]
    ring

theorem MoebiusParameter.inverseMatrix_mul_toMatrix (g : MoebiusParameter) :
    g.inverseMatrix * g.toMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MoebiusParameter.toMatrix, MoebiusParameter.inverseMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]
  · rw [← g.det_one]
    ring
  · ring
  · ring
  · rw [← g.det_one]
    ring

def MoebiusParameter.toUnit (g : MoebiusParameter) :
    (Matrix (Fin 2) (Fin 2) ℝ)ˣ :=
  { val := g.toMatrix
    inv := g.inverseMatrix
    val_inv := g.toMatrix_mul_inverseMatrix
    inv_val := g.inverseMatrix_mul_toMatrix }

@[simp]
theorem MoebiusParameter.toUnit_val (g : MoebiusParameter) :
    (g.toUnit : Matrix (Fin 2) (Fin 2) ℝ) = g.toMatrix :=
  rfl

@[simp]
theorem MoebiusParameter.toUnit_inv_val (g : MoebiusParameter) :
    (↑(g.toUnit⁻¹) : Matrix (Fin 2) (Fin 2) ℝ) = g.inverseMatrix :=
  rfl

theorem MoebiusParameter.toUnit_mul
    (g h : MoebiusParameter) :
    (g.mul h).toUnit = g.toUnit * h.toUnit := by
  apply Units.ext
  exact MoebiusParameter.toMatrix_mul g h

theorem MoebiusParameter.toUnit_one :
    MoebiusParameter.one.toUnit = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MoebiusParameter.toUnit, MoebiusParameter.one,
      MoebiusParameter.toMatrix, Matrix.one_apply]

theorem MoebiusParameter.toUnit_inv (g : MoebiusParameter) :
    g.inv.toUnit = g.toUnit⁻¹ := by
  apply Units.ext
  rfl

theorem MoebiusParameter.toUnit_injective :
    Function.Injective MoebiusParameter.toUnit := by
  intro g h heq
  apply MoebiusParameter.toMatrix_injective
  exact congrArg (fun u : (Matrix (Fin 2) (Fin 2) ℝ)ˣ =>
    (u : Matrix (Fin 2) (Fin 2) ℝ)) heq


/-- Hestenes--Krein null cone associated to the Wilson/KMS carrier. -/
@[rep_depth krein]
def HestenesNullCone (_P : HestenesKreinKMSPacket (E := H₂)) : Set H₂ :=
  { ξ : H₂ | KreinSpace.kreinInner (H := H₂) ξ ξ = 0 }

/--
Final Möbius closure bridge.

`Word` is a finite face/atom layer.  A concrete backend may instantiate it by
binary words at a fixed depth, Jones tower atoms, or another finite boundary
slice.  The Möbius action on that finite layer is supplied as a permutation.
-/
@[rep_depth krein]
structure Bridge
    (Word : Type*) [Fintype Word] [DecidableEq Word] where
  /-- Previously installed Hestenes--Connes--Wilson detailed-balance bridge. -/
  wilson :
    _root_.InfoGeometry.Krein.HestenesConnesWilsonBridge.Bridge (E := E) Word

  /-- Möbius action on vectors in the real doubled carrier. -/
  vectorAction : MoebiusParameter → H₂ → H₂

  /-- The vector action is Krein-isometric. -/
  vectorAction_krein_isometry :
    ∀ (g : MoebiusParameter) (ξ η : H₂),
      KreinSpace.kreinInner (H := H₂) (vectorAction g ξ) (vectorAction g η) =
        KreinSpace.kreinInner (H := H₂) ξ η

  /-- The vacuum apex `Ω` is fixed by the Möbius vector action. -/
  vectorAction_fixes_omega :
    ∀ g : MoebiusParameter,
      vectorAction g wilson.vacuum.omega = wilson.vacuum.omega

  /-- Möbius action on bounded doubled-space operators. -/
  operatorAction : MoebiusParameter → EndH ≃+* EndH

  /-- The Möbius operator action fixes the Hestenes phase axis `K`. -/
  operatorAction_phaseAxis_fixed :
    ∀ g : MoebiusParameter,
      operatorAction g (clockAxis (E := E)) = clockAxis (E := E)

  /-- The Ω-volume state is invariant under the Möbius operator action. -/
  volumeState_operatorAction_invariant :
    ∀ (g : MoebiusParameter) (A : EndH),
      wilson.volume.volumeState (operatorAction g A) = wilson.volume.volumeState A

  /-- Möbius permutation of the finite atom/face layer. -/
  wordAction : MoebiusParameter → Equiv.Perm Word

  /-- Atom weights are invariant under the Möbius face permutation. -/
  atomExpectation_wordAction_invariant :
    ∀ (g : MoebiusParameter) (w : Word),
      wilson.volume.atomExpectation ((wordAction g) w) =
        wilson.volume.atomExpectation w

  /-- Connes--Wilson holonomy is invariant under Möbius reparameterization. -/
  wilsonHolonomy_wordAction_invariant :
    ∀ (g : MoebiusParameter) (parent child : Word),
      wilson.wilsonHolonomy ((wordAction g) parent) ((wordAction g) child) =
        wilson.wilsonHolonomy parent child

namespace Bridge

variable {Word : Type*}
variable [Fintype Word] [DecidableEq Word]
variable (M : Bridge (E := E) Word)


/-- Möbius transformations preserve the Hestenes natural cone shadow. -/
@[rep_depth krein]
theorem moebius_preserves_naturalCone
    (g : MoebiusParameter) {ξ : H₂}
    (hξ : ξ ∈ M.wilson.kmsPacket.HestenesNaturalCone) :
    M.vectorAction g ξ ∈ M.wilson.kmsPacket.HestenesNaturalCone := by
  change 0 ≤ KreinSpace.kreinInner (H := H₂) ξ ξ at hξ
  change 0 ≤
    KreinSpace.kreinInner (H := H₂) (M.vectorAction g ξ) (M.vectorAction g ξ)
  rw [M.vectorAction_krein_isometry]
  exact hξ

/-- Möbius transformations preserve the Krein null cone. -/
@[rep_depth krein]
theorem moebius_preserves_nullCone
    (g : MoebiusParameter) {ξ : H₂}
    (hξ : ξ ∈ HestenesNullCone M.wilson.kmsPacket) :
    M.vectorAction g ξ ∈ HestenesNullCone M.wilson.kmsPacket := by
  change KreinSpace.kreinInner (H := H₂) ξ ξ = 0 at hξ
  change KreinSpace.kreinInner (H := H₂)
      (M.vectorAction g ξ) (M.vectorAction g ξ) = 0
  rw [M.vectorAction_krein_isometry]
  exact hξ

/-- The Möbius action keeps the vacuum normalized. -/
@[rep_depth krein]
theorem moebius_vacuum_norm_invariant (g : MoebiusParameter) :
    KreinSpace.kreinInner (H := H₂)
        (M.vectorAction g M.wilson.vacuum.omega)
        (M.vectorAction g M.wilson.vacuum.omega) = 1 := by
  rw [M.vectorAction_krein_isometry]
  exact M.wilson.vacuum.omega_normalized

/--
The Möbius closure invariant: pairing the transformed vacuum with `Ω` still
returns unit volume.
-/
@[rep_depth krein]
theorem moebius_vacuum_closure_invariant (g : MoebiusParameter) :
    KreinSpace.kreinInner (H := H₂)
        (M.vectorAction g M.wilson.vacuum.omega)
        M.wilson.vacuum.omega = 1 := by
  rw [M.vectorAction_fixes_omega]
  exact M.wilson.vacuum.omega_normalized


/-- The Möbius operator action preserves Hestenes analytic/K-linear operators. -/
@[rep_depth krein]
theorem moebius_preserves_hestenesAnalyticSymmetry
    (g : MoebiusParameter) {A : EndH}
    (hA : IsHestenesAnalyticSymmetry (E := E) A) :
    IsHestenesAnalyticSymmetry (E := E) (M.operatorAction g A) := by
  let K : EndH := clockAxis (E := E)
  unfold IsHestenesAnalyticSymmetry at hA ⊢
  unfold IsHestenesHolomorphicDifferential at hA ⊢
  change A * K = K * A at hA
  change (M.operatorAction g A) * K = K * (M.operatorAction g A)
  have hK : M.operatorAction g K = K := M.operatorAction_phaseAxis_fixed g
  calc
    (M.operatorAction g A) * K
        = (M.operatorAction g A) * (M.operatorAction g K) := by rw [hK]
    _ = M.operatorAction g (A * K) := by
          rw [(M.operatorAction g).map_mul]
    _ = M.operatorAction g (K * A) := by
          rw [hA]
    _ = (M.operatorAction g K) * (M.operatorAction g A) := by
          rw [(M.operatorAction g).map_mul]
    _ = K * (M.operatorAction g A) := by rw [hK]


/-- Vacuum real state invariance under Möbius operator action. -/
@[rep_depth krein]
theorem vacuumRealState_moebius_invariant
    (g : MoebiusParameter) (A : EndH) :
    M.wilson.vacuum.vacuumRealState (M.operatorAction g A) =
      M.wilson.vacuum.vacuumRealState A := by
  calc
    M.wilson.vacuum.vacuumRealState (M.operatorAction g A)
        = M.wilson.volume.volumeState (M.operatorAction g A) := by
            exact (M.wilson.volumeState_eq_vacuumRealState (M.operatorAction g A)).symm
    _ = M.wilson.volume.volumeState A :=
            M.volumeState_operatorAction_invariant g A
    _ = M.wilson.vacuum.vacuumRealState A :=
            M.wilson.volumeState_eq_vacuumRealState A

/-- The Möbius transform of the operator unit still has unit vacuum expectation. -/
@[rep_depth krein]
theorem moebius_unit_vacuum_expectation (g : MoebiusParameter) :
    M.wilson.vacuum.vacuumRealState (M.operatorAction g (1 : EndH)) = 1 := by
  calc
    M.wilson.vacuum.vacuumRealState (M.operatorAction g (1 : EndH))
        = M.wilson.vacuum.vacuumRealState (1 : EndH) :=
            M.vacuumRealState_moebius_invariant g (1 : EndH)
    _ = 1 := by
          simpa using M.wilson.vacuum.vacuumRealState_id


/-- The finite total atom volume is invariant under Möbius reindexing. -/
@[rep_depth projective]
theorem total_atom_volume_moebius_invariant (g : MoebiusParameter) :
    (∑ w : Word,
      M.wilson.volume.atomExpectation ((M.wordAction g) w)) = 1 := by
  calc
    (∑ w : Word,
      M.wilson.volume.atomExpectation ((M.wordAction g) w))
        = ∑ w : Word, M.wilson.volume.atomExpectation w := by
            apply Finset.sum_congr rfl
            intro w _hw
            exact M.atomExpectation_wordAction_invariant g w
    _ = 1 := M.wilson.volume.total_expectation_is_unity


/-- Radon--Nikodym log increments are Möbius invariant. -/
@[rep_depth projective]
theorem radonNikodymLog_moebius_invariant
    (g : MoebiusParameter) (parent child : Word) :
    M.wilson.radonNikodymLog ((M.wordAction g) parent) ((M.wordAction g) child) =
      M.wilson.radonNikodymLog parent child := by
  calc
    M.wilson.radonNikodymLog ((M.wordAction g) parent) ((M.wordAction g) child)
        = M.wilson.wilsonHolonomy ((M.wordAction g) parent) ((M.wordAction g) child) :=
            (M.wilson.wilsonHolonomy_eq_radonNikodymLog
              ((M.wordAction g) parent) ((M.wordAction g) child)).symm
    _ = M.wilson.wilsonHolonomy parent child :=
            M.wilsonHolonomy_wordAction_invariant g parent child
    _ = M.wilson.radonNikodymLog parent child :=
            M.wilson.wilsonHolonomy_eq_radonNikodymLog parent child

/-- The Ω-volume modular logarithmic increment is Möbius invariant. -/
@[rep_depth projective]
theorem modularVolumeIncrement_moebius_invariant
    (g : MoebiusParameter) (parent child : Word) :
    M.wilson.volume.modularVolumeIncrement
        ((M.wordAction g) parent) ((M.wordAction g) child) =
      M.wilson.volume.modularVolumeIncrement parent child := by
  calc
    M.wilson.volume.modularVolumeIncrement
        ((M.wordAction g) parent) ((M.wordAction g) child)
        = M.wilson.radonNikodymLog ((M.wordAction g) parent) ((M.wordAction g) child) :=
            (M.wilson.radonNikodymLog_eq_modularVolumeIncrement
              ((M.wordAction g) parent) ((M.wordAction g) child)).symm
    _ = M.wilson.radonNikodymLog parent child :=
            M.radonNikodymLog_moebius_invariant g parent child
    _ = M.wilson.volume.modularVolumeIncrement parent child :=
            M.wilson.radonNikodymLog_eq_modularVolumeIncrement parent child

/--
Alias for the final finite-level projective closure readback.

This is the theorem-safe "closure of the universe" statement at this data level:
Möbius reindexing of the finite atom layer preserves the normalized total
Ω-volume.  No compactification theorem or global CFT representation theorem is
claimed here.
-/
@[rep_depth projective]
theorem universe_projective_closure
    (g : MoebiusParameter) :
    (∑ w : Word,
      M.wilson.volume.atomExpectation ((M.wordAction g) w)) = 1 :=
  M.total_atom_volume_moebius_invariant g

/--
Alias for Möbius invariance of the Connes--Weyl logarithmic scale.

This is the finite Connes--Wilson/Weyl readback: Möbius reparameterization of
faces preserves the calibrated logarithmic Radon--Nikodym increment.
-/
@[rep_depth projective]
theorem connes_weyl_scale_moebius_closed
    (g : MoebiusParameter) (parent child : Word) :
    M.wilson.radonNikodymLog ((M.wordAction g) parent) ((M.wordAction g) child) =
      M.wilson.radonNikodymLog parent child :=
  M.radonNikodymLog_moebius_invariant g parent child

end Bridge

end Core

instance : Mul MoebiusParameter := ⟨MoebiusParameter.mul⟩

instance : One MoebiusParameter := ⟨MoebiusParameter.one⟩

instance : Inv MoebiusParameter := ⟨MoebiusParameter.inv⟩

instance : Group MoebiusParameter :=
  Group.ofLeftAxioms
    MoebiusParameter.mul_assoc
    MoebiusParameter.one_mul
    MoebiusParameter.inv_mul

def MoebiusParameter.toUnitHom :
    MoebiusParameter →* (Matrix (Fin 2) (Fin 2) ℝ)ˣ where
  toFun := MoebiusParameter.toUnit
  map_one' := MoebiusParameter.toUnit_one
  map_mul' g h := MoebiusParameter.toUnit_mul g h

theorem MoebiusParameter.toUnitHom_injective :
    Function.Injective MoebiusParameter.toUnitHom := by
  intro g h heq
  exact MoebiusParameter.toUnit_injective heq

end InfoGeometry.Krein.HestenesMoebiusClosureBridge
