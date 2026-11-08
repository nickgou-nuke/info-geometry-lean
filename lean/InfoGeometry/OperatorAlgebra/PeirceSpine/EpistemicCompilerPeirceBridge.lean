/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import InfoGeometry.OperatorAlgebra.PeirceSpine.DirectedFlowMagneticResolvent
import InfoGeometry.OperatorAlgebra.PeirceSpine.TelegrapherTwoStateMasterPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import InfoGeometry.Core.IdempotentGraphGrassmannian

open InfoGeometry.OperatorAlgebra.ThreeCornerColumnAlgebra (third)

/-!
# D₄₆: Peirce dissolution, homogenized channels, golden square, and finite resolvent

This module composes existing Peirce corner, tetraktys, homogenized-channel,
all-mode defect, and three-idempotent resolvent owners. The homogenized channels
are additive operator-valued channels; this module does not promote them to
Galois automorphisms or claim ambient idempotency. The finite resolvent is the
polynomial inverse attached to a cube-zero three-layer path operator.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

/-! ## Causal order -/

inductive EpistemicCompilerStage where
  | peirceDissolution
  | tetraktysSynthesis
  | homogenizedChannels
  | goldenCoagulation
  | finitePosetResolvent
  | unipotentShear
  | matrixCoordinates
  deriving DecidableEq, Repr

def epistemicCompilerLe (a b : EpistemicCompilerStage) : Prop :=
  a = b ∨
    (a = .peirceDissolution ∧ b = .tetraktysSynthesis) ∨
    (a = .peirceDissolution ∧ b = .homogenizedChannels) ∨
    (a = .peirceDissolution ∧ b = .goldenCoagulation) ∨
    (a = .peirceDissolution ∧ b = .finitePosetResolvent) ∨
    (a = .peirceDissolution ∧ b = .unipotentShear) ∨
    (a = .peirceDissolution ∧ b = .matrixCoordinates) ∨
    (a = .tetraktysSynthesis ∧ b = .homogenizedChannels) ∨
    (a = .tetraktysSynthesis ∧ b = .goldenCoagulation) ∨
    (a = .tetraktysSynthesis ∧ b = .matrixCoordinates)

instance : PartialOrder EpistemicCompilerStage where
  le := epistemicCompilerLe
  le_refl a := Or.inl rfl
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all [epistemicCompilerLe]
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;> simp_all [epistemicCompilerLe]

instance : DecidableLE EpistemicCompilerStage := fun a b => by
  change Decidable (a = b ∨
    (a = .peirceDissolution ∧ b = .tetraktysSynthesis) ∨
    (a = .peirceDissolution ∧ b = .homogenizedChannels) ∨
    (a = .peirceDissolution ∧ b = .goldenCoagulation) ∨
    (a = .peirceDissolution ∧ b = .finitePosetResolvent) ∨
    (a = .peirceDissolution ∧ b = .unipotentShear) ∨
    (a = .peirceDissolution ∧ b = .matrixCoordinates) ∨
    (a = .tetraktysSynthesis ∧ b = .homogenizedChannels) ∨
    (a = .tetraktysSynthesis ∧ b = .goldenCoagulation) ∨
    (a = .tetraktysSynthesis ∧ b = .matrixCoordinates))
  infer_instance

theorem epistemicCompiler_causal_dependencies :
    EpistemicCompilerStage.peirceDissolution < EpistemicCompilerStage.tetraktysSynthesis ∧
    EpistemicCompilerStage.peirceDissolution < EpistemicCompilerStage.finitePosetResolvent ∧
    EpistemicCompilerStage.peirceDissolution < EpistemicCompilerStage.unipotentShear ∧
    EpistemicCompilerStage.peirceDissolution < EpistemicCompilerStage.matrixCoordinates ∧
    EpistemicCompilerStage.tetraktysSynthesis < EpistemicCompilerStage.homogenizedChannels ∧
    EpistemicCompilerStage.tetraktysSynthesis < EpistemicCompilerStage.goldenCoagulation ∧
    EpistemicCompilerStage.tetraktysSynthesis < EpistemicCompilerStage.matrixCoordinates ∧
    ¬ EpistemicCompilerStage.homogenizedChannels ≤ EpistemicCompilerStage.goldenCoagulation ∧
    ¬ EpistemicCompilerStage.goldenCoagulation ≤ EpistemicCompilerStage.homogenizedChannels ∧
    ¬ EpistemicCompilerStage.finitePosetResolvent ≤ EpistemicCompilerStage.tetraktysSynthesis ∧
    ¬ EpistemicCompilerStage.tetraktysSynthesis ≤ EpistemicCompilerStage.finitePosetResolvent := by
  simp only [lt_iff_le_not_ge]
  decide

variable {B : Type*} [Ring B]

/-! ## AL₁: exact four-corner Peirce dissolution -/

/-- The complement of an idempotent is an orthogonal idempotent. -/
theorem epistemic_idempotent_cut_orthogonality {P : B} (hP : P * P = P) :
    (1 - P) * (1 - P) = 1 - P ∧
    P * (1 - P) = 0 ∧
    (1 - P) * P = 0 ∧
    P + (1 - P) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · noncomm_ring [hP]
  · noncomm_ring [hP]
  · noncomm_ring [hP]
  · noncomm_ring

/-- The ring commutator is a Lie bracket: its cyclic Jacobi sum vanishes
without any commutativity or characteristic assumption. -/
theorem epistemic_commutator_jacobi (X Y Z : B) :
    comm X (comm Y Z) + comm Y (comm Z X) + comm Z (comm X Y) = 0 := by
  simp only [comm]
  noncomm_ring

/-- Skew/symmetric bracket normalization and their ordered product readout.
The formulas are valid in arbitrary characteristic because `2` is represented
by integer scalar multiplication, not divided out. -/
theorem epistemic_bracket_normalization (X Y : B) :
    comm X Y = -comm Y X ∧
    anticomm X Y = anticomm Y X ∧
    comm X Y + anticomm X Y = (2 : ℤ) • (X * Y) := by
  unfold comm anticomm
  constructor
  · noncomm_ring
  constructor
  · abel
  · noncomm_ring

/-- The idempotent cut determines an involutive parity element. The
integer-multiple presentation agrees with the Peirce sign `invS`. -/
theorem epistemic_parity_involution {P : B} (hP : P * P = P) :
    ((2 : ℤ) • P - 1) * ((2 : ℤ) • P - 1) = 1 ∧
    ((2 : ℤ) • P - 1) = invS P ∧
    ((2 : ℤ) • P - 1) * P = P ∧
    P * ((2 : ℤ) • P - 1) = P ∧
    ((2 : ℤ) • P - 1) * P * ((2 : ℤ) • P - 1) = P := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · noncomm_ring [hP]
  · dsimp [invS]; noncomm_ring
  · noncomm_ring [hP]
  · noncomm_ring [hP]
  · noncomm_ring [hP]

/-- Completing the square expresses the quadratic defect as a ring identity,
valid in arbitrary characteristic. -/
theorem epistemic_defect_completed_square (X : B) :
    ((2 : ℤ) • X - 1) * ((2 : ℤ) • X - 1) =
      1 + (4 : ℤ) • (X * X - X) := by
  noncomm_ring

theorem peirce_quartet_reconstruction {P : B} (_hP : P * P = P) (X : B) :
    peirce11 P X + conePlus P X + coneMinus P X + peirce00 P X = X := by
  unfold peirce11 peirce00 conePlus coneMinus
  peirce_nf _hP

theorem peirce_quartet_corner_laws {P : B} (hP : P * P = P) (X Y : B) :
    peirce11 P X * coneMinus P Y = 0 ∧
    conePlus P X * conePlus P Y = 0 ∧
    coneMinus P X * coneMinus P Y = 0 ∧
    (2 : ℤ) • conePlus P X = comm P (comm P X) + comm P X ∧
    (2 : ℤ) • coneMinus P X = comm P (comm P X) - comm P X := by
  refine ⟨?_, conePlus_mul_conePlus hP X Y, coneMinus_mul_coneMinus hP X Y, ?_, ?_⟩
  · unfold peirce11
    peirce_nf hP
  · unfold conePlus
    peirce_nf hP
  · unfold coneMinus
    peirce_nf hP

/-- A Boolean-indexed Peirce block, with `true` denoting the `P` corner and
`false` its complementary corner. -/
def peirceCorner (P : B) (i j : Bool) (X : B) : B :=
  (if i then P else 1 - P) * X * (if j then P else 1 - P)

/-- Peirce blocks multiply by matching their adjacent indices. This is the
full four-by-four matrix-block law, valid in any ring with an idempotent; it
does not assume that arbitrary elements of the ring commute. -/
theorem peirceCorner_mul {P : B} (hP : P * P = P) (i j k l : Bool) (X Y : B) :
    peirceCorner P i j X * peirceCorner P k l Y =
      if j = k then
        (if i then P else 1 - P) * X * (if j then P else 1 - P) * Y *
          (if l then P else 1 - P)
      else 0 := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp [peirceCorner] <;> peirce_nf hP

/-- Multiplication of two operators is recovered blockwise by summing over
the two intermediate Peirce sectors. This is the coordinate multiplication
law behind the matrix-block interpretation of the four-corner decomposition. -/
theorem peirceCorner_product_resolution {P : B} (hP : P * P = P)
    (i j : Bool) (X Y : B) :
    peirceCorner P i j (X * Y) =
      peirceCorner P i true X * peirceCorner P true j Y +
        peirceCorner P i false X * peirceCorner P false j Y := by
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; noncomm_ring
  have hSum : P + (1 - P) = 1 := by noncomm_ring
  have hGeneral (E F : B) :
      E * X * Y * F =
        (E * X * P) * (P * Y * F) + (E * X * (1 - P)) * ((1 - P) * Y * F) := by
    calc
      E * X * Y * F = E * X * (P + (1 - P)) * Y * F := by rw [hSum]; simp
      _ = E * X * (P * P + (1 - P) * (1 - P)) * Y * F := by rw [hP, hQ]
      _ = (E * X * P) * (P * Y * F) +
          (E * X * (1 - P)) * ((1 - P) * Y * F) := by noncomm_ring
  simpa [peirceCorner, mul_assoc] using hGeneral (if i then P else 1 - P)
    (if j then P else 1 - P)

/-- The four Peirce corners of an operator, arranged as a two-by-two matrix
with entries in the original ring. -/
def peirceCoordinateMatrix (P X : B) : Matrix Bool Bool B :=
  fun i j => peirceCorner P i j X

/-- Peirce coordinates turn multiplication in the original ring into ordinary
two-by-two matrix multiplication. The diagonal coordinate of the unit is
`P` or `1 - P`, so this is a multiplicative coordinate map, not a unital map
to the full matrix ring unless the corresponding corner is trivial. -/
theorem peirceCoordinateMatrix_mul {P : B} (hP : P * P = P) (X Y : B) :
    peirceCoordinateMatrix P (X * Y) =
      peirceCoordinateMatrix P X * peirceCoordinateMatrix P Y := by
  ext i j
  simp [peirceCoordinateMatrix, Matrix.mul_apply, Fintype.univ_bool,
    peirceCorner_product_resolution hP]

/-- The Peirce coordinate map preserves addition, so together with its
multiplication law it is an additive and multiplicative representation. -/
theorem peirceCoordinateMatrix_add (P X Y : B) :
    peirceCoordinateMatrix P (X + Y) =
      peirceCoordinateMatrix P X + peirceCoordinateMatrix P Y := by
  ext i j
  cases i <;> cases j <;>
    simp [peirceCoordinateMatrix, peirceCorner, mul_add, add_mul, mul_assoc]

/-- The coordinate image of the unit is the diagonal idempotent matrix
`diag(P, 1 - P)`, which explains why the representation is generally
non-unital as a map to the full matrix ring. -/
theorem peirceCoordinateMatrix_one {P : B} (hP : P * P = P) :
    peirceCoordinateMatrix P 1 =
      fun i j => if i = j then (if i then P else 1 - P) else 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [peirceCoordinateMatrix, peirceCorner] <;> peirce_nf hP

/-- The faithful non-unital ring homomorphism given by Peirce coordinates.
Its multiplicativity uses `hP`; its image of `1` is `diag(P, 1-P)`, not the
identity matrix of the ambient matrix ring in general. -/
def peirceCoordinateRingHom {P : B} (hP : P * P = P) :
    B →ₙ+* Matrix Bool Bool B where
  toFun := peirceCoordinateMatrix P
  map_mul' := peirceCoordinateMatrix_mul hP
  map_add' := peirceCoordinateMatrix_add P
  map_zero' := by
    ext i j
    simp [peirceCoordinateMatrix, peirceCorner]

/-- Reconstruction from the four coordinates makes the non-unital ring
homomorphism faithful. -/
theorem peirceCoordinateRingHom_injective {P : B} (hP : P * P = P) :
    Function.Injective (peirceCoordinateRingHom hP) := by
  intro X Y h
  change peirceCoordinateMatrix P X = peirceCoordinateMatrix P Y at h
  have h11 : peirceCorner P true true X = peirceCorner P true true Y :=
    congrFun (congrFun h true) true
  have h10 : peirceCorner P true false X = peirceCorner P true false Y :=
    congrFun (congrFun h true) false
  have h01 : peirceCorner P false true X = peirceCorner P false true Y :=
    congrFun (congrFun h false) true
  have h00 : peirceCorner P false false X = peirceCorner P false false Y :=
    congrFun (congrFun h false) false
  calc
    X = peirceCorner P true true X + peirceCorner P true false X +
        peirceCorner P false true X + peirceCorner P false false X := by
          simpa [peirceCorner, peirce11, peirce00, conePlus, coneMinus] using
            (peirce_quartet_reconstruction hP X).symm
    _ = peirceCorner P true true Y + peirceCorner P true false Y +
        peirceCorner P false true Y + peirceCorner P false false Y := by
          rw [h11, h10, h01, h00]
    _ = Y := by
          simpa [peirceCorner, peirce11, peirce00, conePlus, coneMinus] using
            peirce_quartet_reconstruction hP Y

/-- The image of the unit is an idempotent matrix and is a two-sided identity
on the image of the Peirce coordinate map. Thus the image is naturally a
unital ring with its own unit, even though the map to the ambient matrix ring
is non-unital. -/
theorem peirceCoordinateMatrix_image_unit {P : B} (hP : P * P = P) (X : B) :
    peirceCoordinateMatrix P 1 * peirceCoordinateMatrix P 1 =
      peirceCoordinateMatrix P 1 ∧
    peirceCoordinateMatrix P 1 * peirceCoordinateMatrix P X =
      peirceCoordinateMatrix P X ∧
    peirceCoordinateMatrix P X * peirceCoordinateMatrix P 1 =
      peirceCoordinateMatrix P X := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      peirceCoordinateMatrix P 1 * peirceCoordinateMatrix P 1 =
          peirceCoordinateMatrix P (1 * 1) :=
            (peirceCoordinateMatrix_mul hP 1 1).symm
      _ = peirceCoordinateMatrix P 1 := by simp
  · calc
      peirceCoordinateMatrix P 1 * peirceCoordinateMatrix P X =
          peirceCoordinateMatrix P (1 * X) :=
            (peirceCoordinateMatrix_mul hP 1 X).symm
      _ = peirceCoordinateMatrix P X := by simp
  · calc
      peirceCoordinateMatrix P X * peirceCoordinateMatrix P 1 =
          peirceCoordinateMatrix P (X * 1) :=
            (peirceCoordinateMatrix_mul hP X 1).symm
      _ = peirceCoordinateMatrix P X := by simp

/-- In faithful Peirce coordinates, the symmetric transition `Φ` has only
the two off-diagonal blocks. This is the concrete matrix form of the
two-source/two-sink decomposition. -/
theorem peirceCoordinateMatrix_genPhi {P : B} (hP : P * P = P) (A C : B) :
    peirceCoordinateMatrix P (genPhi P A C) =
      fun i j => if i = true ∧ j = false then conePlus P A
        else if i = false ∧ j = true then coneMinus P C else 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [peirceCoordinateMatrix, peirceCorner, genPhi, conePlus, coneMinus] <;>
    peirce_nf hP

/-- The skew transition `J` differs from `Φ` by the sign on its lower
off-diagonal block. -/
theorem peirceCoordinateMatrix_genJ {P : B} (hP : P * P = P) (A C : B) :
    peirceCoordinateMatrix P (genJ P A C) =
      fun i j => if i = true ∧ j = false then conePlus P A
        else if i = false ∧ j = true then -coneMinus P C else 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [peirceCoordinateMatrix, peirceCorner, genJ, conePlus, coneMinus] <;>
    peirce_nf hP

/-- The metric operator `V` is diagonal in Peirce coordinates, with the two
ordered transition products on its diagonal. -/
theorem peirceCoordinateMatrix_genV {P : B} (hP : P * P = P) (A C : B) :
    peirceCoordinateMatrix P (genV P A C) =
      fun i j => if i = true ∧ j = true then qgtPlus P A C
        else if i = false ∧ j = false then qgtMinus P A C else 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [peirceCoordinateMatrix, peirceCorner, genV, anticomm,
      qgtPlus, qgtMinus, conePlus, coneMinus] <;> peirce_nf hP

/-- The signed curvature `Σ` has the same diagonal blocks as `V`, with the
lower block negated. The ordered corner products remain visible. -/
theorem peirceCoordinateMatrix_genSig {P : B} (hP : P * P = P) (A C : B) :
    peirceCoordinateMatrix P (genSig P A C) =
      fun i j => if i = true ∧ j = true then qgtPlus P A C
        else if i = false ∧ j = false then -qgtMinus P A C else 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [peirceCoordinateMatrix, peirceCorner, genSig, comm,
      qgtPlus, qgtMinus, conePlus, coneMinus] <;> peirce_nf hP

/-- The even Peirce component is exactly the diagonal part of the coordinate
matrix. -/
theorem peirceCoordinateMatrix_evenGrade {P : B} (hP : P * P = P) (X : B) :
    peirceCoordinateMatrix P (evenGrade P X) =
      fun i j => if i = j then peirceCorner P i i X else 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [peirceCoordinateMatrix, peirceCorner, evenGrade] <;> peirce_nf hP

/-- The odd Peirce component is exactly the off-diagonal part of the
coordinate matrix. -/
theorem peirceCoordinateMatrix_oddGrade {P : B} (hP : P * P = P) (X : B) :
    peirceCoordinateMatrix P (oddGrade P X) =
      fun i j => if i = j then 0 else peirceCorner P i j X := by
  ext i j
  cases i <;> cases j <;>
    simp [peirceCoordinateMatrix, peirceCorner, oddGrade] <;> peirce_nf hP

/-! ## AL₂: Tetraktys and its metric-curvature split -/

theorem tetraktys_coniunctio (P : B) (hP : P * P = P) (A C : B) :
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    genJ P A C * genPhi P A C = genSig P A C ∧
    genSig P A C = invS P * genV P A C := by
  rcases archetype_A3_nilpotent_cones_and_tetraktys_table (P := P) hP A C with
    ⟨hNp, hNm, hPhiSq, hJSq, _, hJPhi, _, _, hSig, _, _, _, _, _, _⟩
  exact ⟨hNp, hNm, hPhiSq, hJSq, hJPhi, hSig⟩

/-- The faithful matrix coordinates preserve the tetraktys products: the
matrix product of the `Φ` blocks is the represented metric `V`, and the
ordered product `J Φ` is the represented curvature `Σ`. -/
theorem peirceCoordinateMatrix_tetraktys_products
    {P : B} (hP : P * P = P) (A C : B) :
    peirceCoordinateMatrix P (genPhi P A C) *
        peirceCoordinateMatrix P (genPhi P A C) =
      peirceCoordinateMatrix P (genV P A C) ∧
    peirceCoordinateMatrix P (genJ P A C) *
        peirceCoordinateMatrix P (genPhi P A C) =
      peirceCoordinateMatrix P (genSig P A C) := by
  rcases tetraktys_coniunctio P hP A C with ⟨_, _, hPhi, _, hJPhi, _⟩
  constructor
  · calc
      peirceCoordinateMatrix P (genPhi P A C) *
          peirceCoordinateMatrix P (genPhi P A C) =
          peirceCoordinateMatrix P (genPhi P A C * genPhi P A C) :=
            (peirceCoordinateMatrix_mul hP _ _).symm
      _ = peirceCoordinateMatrix P (genV P A C) := by rw [hPhi]
  · calc
      peirceCoordinateMatrix P (genJ P A C) *
          peirceCoordinateMatrix P (genPhi P A C) =
          peirceCoordinateMatrix P (genJ P A C * genPhi P A C) :=
            (peirceCoordinateMatrix_mul hP _ _).symm
      _ = peirceCoordinateMatrix P (genSig P A C) := by rw [hJPhi]

/-! ## AL₃: existing V-homogenized Klein-Hadamard channels -/

theorem homogenized_mandala_channel_laws (P : B) (hP : P * P = P) (A C X : B) :
    hProjV P A C X + hProjPhi P A C X + hProjJ P A C X + hProjSig P A C X =
      (8 : ℤ) • ((genV P A C * genV P A C) * X) ∧
    hProjV P A C (genV P A C) =
      (8 : ℤ) • ((genV P A C * genV P A C) * genV P A C) ∧
    hProjPhi P A C (genPhi P A C) =
      (8 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) ∧
    hProjJ P A C (genJ P A C) =
      (8 : ℤ) • ((genV P A C * genV P A C) * genJ P A C) ∧
    hProjSig P A C (genSig P A C) =
      (8 : ℤ) • ((genV P A C * genV P A C) * genSig P A C) := by
  rcases archetype_A13_homogenized_projectors (P := P) hP A C X with
    ⟨hSum, hV, _, _, _, hPhi, _, _, _, hJ, _, _, _, hSig, _, _⟩
  exact ⟨hSum, hV, hPhi, hJ, hSig⟩

/-! ## AL₄: golden defect and completed-square identity -/

theorem golden_coagulation_discriminant (P : B) (hP : P * P = P) (A C : B) :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (P + genPhi P A C) = genV P A C ∧
    ((2 : ℤ) • (P + genPhi P A C) - 1) *
        ((2 : ℤ) • (P + genPhi P A C) - 1) =
      1 + (4 : ℤ) • genV P A C := by
  rcases archetype_A121_nilpotent_idempotent_peirce_split_and_all_mode_virasoro_emergence
      (P := P) hP A C 0 with ⟨_, ⟨hDefect, _, _, _, _⟩⟩
  refine ⟨hDefect, ?_⟩
  calc
    ((2 : ℤ) • (P + genPhi P A C) - 1) *
        ((2 : ℤ) • (P + genPhi P A C) - 1) =
      1 + (4 : ℤ) • InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (P + genPhi P A C) := by
        unfold InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        noncomm_ring
    _ = 1 + (4 : ℤ) • genV P A C := by rw [hDefect]

/-- The full tetraktys defect readout retains the odd-generator anomalies as
well as the coupled-state defect. In particular, the `J` branch has its own
defect `δ(P + J) = -V`; it is not suppressed by the `Φ` branch. -/
theorem epistemic_aporia_defect_laws {P : B} (hP : P * P = P) (A C : B) :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (genPhi P A C) = genV P A C - genPhi P A C ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (genJ P A C) = -genV P A C - genJ P A C ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (P + genJ P A C) = -genV P A C := by
  rcases archetype_A3_nilpotent_cones_and_tetraktys_table (P := P) hP A C with
    ⟨_, _, hPhiSq, hJSq, _, _, _, _, _, _, _, _, _, _, _⟩
  constructor
  · change genPhi P A C * genPhi P A C - genPhi P A C = _
    rw [hPhiSq]
  · constructor
    · change genJ P A C * genJ P A C - genJ P A C = _
      rw [hJSq]
    · change (P + genJ P A C) * (P + genJ P A C) -
        (P + genJ P A C) = -genV P A C
      peirce_nf hP

/-! ## AL₄′: exact epistemic compiler synthesis -/

/-- The product of the two positive unipotent Peirce shears. -/
def epistemicCornerShear (P A C : B) : B :=
  (1 + conePlus P A) * (1 + coneMinus P C)

/-- The inverse has the factors in reverse order and negative cone signs. -/
def epistemicCornerShearInv (P A C : B) : B :=
  (1 - coneMinus P C) * (1 - conePlus P A)

/-- The complete algebraic compiler readout: Peirce reconstruction,
nilpotent boundary cones, the metric-curvature tetraktys and its defect
identities, an exact two-sided inverse for the ordered positive shear, and
faithful multiplicative Peirce coordinates. All assertions hold in an
arbitrary unital associative ring; the matrix map is generally non-unital
into the ambient matrix ring. -/
theorem master_epistemic_compiler_synthesis
    {P : B} (hP : P * P = P) (A C X Y Z : B) :
    peirce11 P X + conePlus P X + coneMinus P X + peirce00 P X = X ∧
    ((2 : ℤ) • P - 1) * ((2 : ℤ) • P - 1) = 1 ∧
    ((2 : ℤ) • P - 1) = invS P ∧
    ((2 : ℤ) • P - 1) * P * ((2 : ℤ) • P - 1) = P ∧
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    genJ P A C * genPhi P A C = genSig P A C ∧
    genSig P A C * genSig P A C = genV P A C * genV P A C ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect P = 0 ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect (1 - P) = 0 ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (conePlus P A) = -conePlus P A ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (coneMinus P C) = -coneMinus P C ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (P + genPhi P A C) = genV P A C ∧
    ((2 : ℤ) • (P + genPhi P A C) - 1) *
        ((2 : ℤ) • (P + genPhi P A C) - 1) =
      1 + (4 : ℤ) • genV P A C ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (genPhi P A C) = genV P A C - genPhi P A C ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (genJ P A C) = -genV P A C - genJ P A C ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (P + genJ P A C) = -genV P A C ∧
    (∀ n : ℕ,
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n]
          (genV P A C) =
        InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n]
            (qgtPlus P A C) +
          InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect^[n]
            (qgtMinus P A C)) ∧
    epistemicCornerShear P A C * epistemicCornerShearInv P A C = 1 ∧
    epistemicCornerShearInv P A C * epistemicCornerShear P A C = 1 ∧
    Function.Injective (peirceCoordinateRingHom hP) ∧
    (∀ W : B,
      peirceCoordinateMatrix P (X * W) =
        peirceCoordinateMatrix P X * peirceCoordinateMatrix P W) ∧
    (comm X Y = -comm Y X ∧
      anticomm X Y = anticomm Y X ∧
      comm X Y + anticomm X Y = (2 : ℤ) • (X * Y)) ∧
    comm X (comm Y Z) + comm Y (comm Z X) + comm Z (comm X Y) = 0 ∧
    (EpistemicCompilerStage.peirceDissolution < EpistemicCompilerStage.tetraktysSynthesis ∧
      EpistemicCompilerStage.peirceDissolution < EpistemicCompilerStage.finitePosetResolvent ∧
      EpistemicCompilerStage.peirceDissolution < EpistemicCompilerStage.unipotentShear ∧
      EpistemicCompilerStage.peirceDissolution < EpistemicCompilerStage.matrixCoordinates ∧
      EpistemicCompilerStage.tetraktysSynthesis < EpistemicCompilerStage.homogenizedChannels ∧
      EpistemicCompilerStage.tetraktysSynthesis < EpistemicCompilerStage.goldenCoagulation ∧
      EpistemicCompilerStage.tetraktysSynthesis < EpistemicCompilerStage.matrixCoordinates ∧
      ¬ EpistemicCompilerStage.homogenizedChannels ≤ EpistemicCompilerStage.goldenCoagulation ∧
      ¬ EpistemicCompilerStage.goldenCoagulation ≤ EpistemicCompilerStage.homogenizedChannels ∧
      ¬ EpistemicCompilerStage.finitePosetResolvent ≤ EpistemicCompilerStage.tetraktysSynthesis ∧
      ¬ EpistemicCompilerStage.tetraktysSynthesis ≤ EpistemicCompilerStage.finitePosetResolvent) := by
  rcases peirce_quartet_reconstruction hP X with hPeirce
  rcases archetype_A3_nilpotent_cones_and_tetraktys_table (P := P) hP A C with
    ⟨hNplus, hNminus, hPhi, hJ, _, hJPhi, _, _, _, _, hSigSq, _⟩
  rcases epistemic_idempotent_cut_orthogonality hP with
    ⟨hPerpSq, hPPerp, hPerpP, hCut⟩
  have hDefP :
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect P = 0 := by
    simp [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect, hP]
  have hDefPerp :
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect (1 - P) = 0 := by
    simp [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect, hPerpSq]
  have hDefNplus :
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (conePlus P A) = -conePlus P A := by
    simp [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect, hNplus]
  have hDefNminus :
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (coneMinus P C) = -coneMinus P C := by
    simp [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect, hNminus]
  have hDefCoupled :
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (P + genPhi P A C) = genV P A C :=
    (golden_coagulation_discriminant P hP A C).1
  have hCompletedSquare := (golden_coagulation_discriminant P hP A C).2
  have hDefectTower := genV_defect_iterates_cycle_split hP A C
  rcases epistemic_aporia_defect_laws hP A C with
    ⟨hDefPhi, hDefJ, hDefCoupledJ⟩
  have hShearLeft : epistemicCornerShear P A C * epistemicCornerShearInv P A C = 1 := by
    dsimp [epistemicCornerShear, epistemicCornerShearInv]
    calc
      (1 + conePlus P A) * (1 + coneMinus P C) *
          ((1 - coneMinus P C) * (1 - conePlus P A)) =
        (1 + conePlus P A) * ((1 + coneMinus P C) * (1 - coneMinus P C)) *
          (1 - conePlus P A) := by noncomm_ring
      _ = (1 + conePlus P A) * 1 * (1 - conePlus P A) := by
        rw [show (1 + coneMinus P C) * (1 - coneMinus P C) = 1 by
          noncomm_ring [hNminus]]
      _ = 1 := by noncomm_ring [hNplus]
  have hShearRight : epistemicCornerShearInv P A C * epistemicCornerShear P A C = 1 := by
    dsimp [epistemicCornerShear, epistemicCornerShearInv]
    calc
      (1 - coneMinus P C) * (1 - conePlus P A) *
          ((1 + conePlus P A) * (1 + coneMinus P C)) =
        (1 - coneMinus P C) * ((1 - conePlus P A) * (1 + conePlus P A)) *
          (1 + coneMinus P C) := by noncomm_ring
      _ = (1 - coneMinus P C) * 1 * (1 + coneMinus P C) := by
        rw [show (1 - conePlus P A) * (1 + conePlus P A) = 1 by
          noncomm_ring [hNplus]]
      _ = 1 := by noncomm_ring [hNminus]
  rcases epistemic_parity_involution hP with
    ⟨hParitySq, hParityEq, _, _, hParityConj⟩
  exact ⟨hPeirce, hParitySq, hParityEq, hParityConj,
    hNplus, hNminus, hPhi, hJ, hJPhi, hSigSq,
    hDefP, hDefPerp, hDefNplus, hDefNminus, hDefCoupled, hCompletedSquare,
    hDefPhi, hDefJ, hDefCoupledJ, hDefectTower,
    hShearLeft, hShearRight, peirceCoordinateRingHom_injective hP,
    (fun W => peirceCoordinateMatrix_mul hP X W),
    epistemic_bracket_normalization X Y,
    epistemic_commutator_jacobi X Y Z,
    epistemicCompiler_causal_dependencies⟩

/-! ## AL₅: three-layer path and exact finite resolvent -/

theorem three_layer_poset_resolvent
    {P₁ P₂ : B} (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0) (A C : B) :
    twoStepUpper P₁ P₂ A C * twoStepUpper P₁ P₂ A C =
      P₁ * A * P₂ * C * third P₁ P₂ ∧
    twoStepUpper P₁ P₂ A C * twoStepUpper P₁ P₂ A C * twoStepUpper P₁ P₂ A C = 0 ∧
    (1 - twoStepUpper P₁ P₂ A C) * twoStepResolvent P₁ P₂ A C = 1 ∧
    twoStepResolvent P₁ P₂ A C * (1 - twoStepUpper P₁ P₂ A C) = 1 := by
  exact ⟨twoStepUpper_sq h1 h2 h12 h21 A C,
    twoStepUpper_mul_sq_zero h1 h2 h12 h21 A C,
    twoStepResolvent_left_inv h1 h2 h12 h21 A C,
    twoStepResolvent_right_inv h1 h2 h12 h21 A C⟩

/-! ## D₄₆ synthesis -/

theorem stageD46_epistemic_compiler_solve_coagula
    {P P₁ P₂ : B} (hP : P * P = P)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (i j k l : Bool) (X Y A C : B) :
    peirce11 P X + conePlus P X + coneMinus P X + peirce00 P X = X ∧
    (peirceCorner P i j X * peirceCorner P k l Y =
      if j = k then
        (if i then P else 1 - P) * X * (if j then P else 1 - P) * Y *
          (if l then P else 1 - P)
      else 0) ∧
    (peirceCorner P i j (X * Y) =
      peirceCorner P i true X * peirceCorner P true j Y +
        peirceCorner P i false X * peirceCorner P false j Y) ∧
    peirceCoordinateMatrix P (X * Y) =
      peirceCoordinateMatrix P X * peirceCoordinateMatrix P Y ∧
    peirceCoordinateMatrix P (X + Y) =
      peirceCoordinateMatrix P X + peirceCoordinateMatrix P Y ∧
    peirceCoordinateMatrix P 1 =
      (fun a b => if a = b then (if a then P else 1 - P) else 0) ∧
    Function.Injective (peirceCoordinateRingHom hP) ∧
    (peirceCoordinateMatrix P 1 * peirceCoordinateMatrix P 1 =
      peirceCoordinateMatrix P 1 ∧
     peirceCoordinateMatrix P 1 * peirceCoordinateMatrix P X =
      peirceCoordinateMatrix P X ∧
     peirceCoordinateMatrix P X * peirceCoordinateMatrix P 1 =
      peirceCoordinateMatrix P X) ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genPhi P A C = genSig P A C ∧
    peirceCoordinateMatrix P (genPhi P A C) =
      (fun i j => if i = true ∧ j = false then conePlus P A
        else if i = false ∧ j = true then coneMinus P C else 0) ∧
    peirceCoordinateMatrix P (genJ P A C) =
      (fun i j => if i = true ∧ j = false then conePlus P A
        else if i = false ∧ j = true then -coneMinus P C else 0) ∧
    peirceCoordinateMatrix P (genV P A C) =
      (fun i j => if i = true ∧ j = true then qgtPlus P A C
        else if i = false ∧ j = false then qgtMinus P A C else 0) ∧
    peirceCoordinateMatrix P (genSig P A C) =
      (fun i j => if i = true ∧ j = true then qgtPlus P A C
        else if i = false ∧ j = false then -qgtMinus P A C else 0) ∧
    peirceCoordinateMatrix P (evenGrade P X) =
      (fun i j => if i = j then peirceCorner P i i X else 0) ∧
    peirceCoordinateMatrix P (oddGrade P X) =
      (fun i j => if i = j then 0 else peirceCorner P i j X) ∧
    (peirceCoordinateMatrix P (genPhi P A C) *
        peirceCoordinateMatrix P (genPhi P A C) =
      peirceCoordinateMatrix P (genV P A C) ∧
     peirceCoordinateMatrix P (genJ P A C) *
        peirceCoordinateMatrix P (genPhi P A C) =
      peirceCoordinateMatrix P (genSig P A C)) ∧
    hProjV P A C X + hProjPhi P A C X + hProjJ P A C X + hProjSig P A C X =
      (8 : ℤ) • ((genV P A C * genV P A C) * X) ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (P + genPhi P A C) = genV P A C ∧
    ((2 : ℤ) • (P + genPhi P A C) - 1) *
        ((2 : ℤ) • (P + genPhi P A C) - 1) =
      1 + (4 : ℤ) • genV P A C ∧
    (1 - twoStepUpper P₁ P₂ A C) * twoStepResolvent P₁ P₂ A C = 1 ∧
    twoStepResolvent P₁ P₂ A C * (1 - twoStepUpper P₁ P₂ A C) = 1 := by
  have hDiss := peirce_quartet_reconstruction hP X
  have hBlock := peirceCorner_mul hP i j k l X Y
  have hResolution := peirceCorner_product_resolution hP i j X Y
  have hMatrixMul := peirceCoordinateMatrix_mul hP X Y
  have hMatrixAdd := peirceCoordinateMatrix_add P X Y
  have hMatrixOne := peirceCoordinateMatrix_one hP
  have hMatrixInj := peirceCoordinateRingHom_injective hP
  have hImageUnit := peirceCoordinateMatrix_image_unit hP X
  have hCoordPhi := peirceCoordinateMatrix_genPhi hP A C
  have hCoordJ := peirceCoordinateMatrix_genJ hP A C
  have hCoordV := peirceCoordinateMatrix_genV hP A C
  have hCoordSig := peirceCoordinateMatrix_genSig hP A C
  have hEvenGrade := peirceCoordinateMatrix_evenGrade hP X
  have hOddGrade := peirceCoordinateMatrix_oddGrade hP X
  have hCoordProducts := peirceCoordinateMatrix_tetraktys_products hP A C
  rcases tetraktys_coniunctio P hP A C with ⟨_, _, hPhi, _, hJphi, _⟩
  have hChannels := homogenized_mandala_channel_laws P hP A C X
  rcases golden_coagulation_discriminant P hP A C with ⟨hDefect, hRoot⟩
  rcases three_layer_poset_resolvent h1 h2 h12 h21 A C with ⟨_, _, hLeft, hRight⟩
  exact ⟨hDiss, hBlock, hResolution, hMatrixMul, hMatrixAdd, hMatrixOne,
    hMatrixInj, hImageUnit, hPhi, hJphi, hCoordPhi, hCoordJ, hCoordV,
    hCoordSig, hEvenGrade, hOddGrade, hCoordProducts, hChannels.1,
    hDefect, hRoot, hLeft, hRight⟩

/-! ## D₄₆ continuation: the four-stage Magnum Opus -/

inductive MagnumOpusStage where
  | nigredo
  | albedo
  | citrinitas
  | rubedo
  | projectio
  deriving DecidableEq, Repr

def magnumOpusRank : MagnumOpusStage → ℕ
  | .nigredo => 0
  | .albedo => 1
  | .citrinitas => 2
  | .rubedo => 3
  | .projectio => 4

theorem magnumOpusRank_injective : Function.Injective magnumOpusRank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : PartialOrder MagnumOpusStage :=
  PartialOrder.lift magnumOpusRank magnumOpusRank_injective

theorem magnumOpus_causal_chain :
    MagnumOpusStage.nigredo < MagnumOpusStage.albedo ∧
    MagnumOpusStage.albedo < MagnumOpusStage.citrinitas ∧
    MagnumOpusStage.citrinitas < MagnumOpusStage.rubedo ∧
    MagnumOpusStage.rubedo < MagnumOpusStage.projectio := by
  change magnumOpusRank .nigredo < magnumOpusRank .albedo ∧
    magnumOpusRank .albedo < magnumOpusRank .citrinitas ∧
    magnumOpusRank .citrinitas < magnumOpusRank .rubedo ∧
    magnumOpusRank .rubedo < magnumOpusRank .projectio
  norm_num [magnumOpusRank]

def peirceAd (P X : B) : B := comm P X
def peirceAdSq (P X : B) : B := comm P (comm P X)
def peirceAdCube (P X : B) : B := comm P (comm P (comm P X))
def peirceAdFourth (P X : B) : B := comm P (comm P (comm P (comm P X)))

/-! ### AL₆: commutator sieve -/

theorem nigredo_commutator_sieve {P : B} (hP : P * P = P) (X : B) :
    conePlus P X + coneMinus P X = peirceAdSq P X ∧
    peirce11 P X + peirce00 P X = X - peirceAdSq P X ∧
    peirce11 P X - peirce00 P X = invS P * (X - peirceAdSq P X) ∧
    peirceAdCube P X = peirceAd P X ∧
    peirceAdFourth P X = peirceAdSq P X := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [peirceAd, peirceAdSq, peirceAdCube, peirceAdFourth,
      peirce11, peirce00, conePlus, coneMinus, invS, comm] <;> peirce_nf hP

/-! ### AL₇: split-quaternion multiplication table -/

theorem albedo_split_quaternion_table {P : B} (hP : P * P = P) (A C : B) :
    comm (genV P A C) (genPhi P A C) = 0 ∧
    comm (genV P A C) (genJ P A C) = 0 ∧
    comm (genV P A C) (genSig P A C) = 0 ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    genSig P A C * genSig P A C = genV P A C * genV P A C ∧
    genJ P A C * genPhi P A C = genSig P A C ∧
    genPhi P A C * genJ P A C = -genSig P A C ∧
    genPhi P A C * genSig P A C = -genV P A C * genJ P A C ∧
    genJ P A C * genSig P A C = -genV P A C * genPhi P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [genPhi, genJ, genV, genSig, anticomm, comm] <;> peirce_nf hP

/-! ### AL₈: all sixteen entries of the mandala matrix -/

theorem citrinitas_full_mandala_matrix {P : B} (hP : P * P = P) (A C : B) :
    hProjV P A C (genV P A C) =
      (8 : ℤ) • ((genV P A C * genV P A C) * genV P A C) ∧
    hProjV P A C (genPhi P A C) = 0 ∧
    hProjV P A C (genJ P A C) = 0 ∧
    hProjV P A C (genSig P A C) = 0 ∧
    hProjPhi P A C (genV P A C) = 0 ∧
    hProjPhi P A C (genPhi P A C) =
      (8 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) ∧
    hProjPhi P A C (genJ P A C) = 0 ∧
    hProjPhi P A C (genSig P A C) = 0 ∧
    hProjJ P A C (genV P A C) = 0 ∧
    hProjJ P A C (genPhi P A C) = 0 ∧
    hProjJ P A C (genJ P A C) =
      (8 : ℤ) • ((genV P A C * genV P A C) * genJ P A C) ∧
    hProjJ P A C (genSig P A C) = 0 ∧
    hProjSig P A C (genV P A C) = 0 ∧
    hProjSig P A C (genPhi P A C) = 0 ∧
    hProjSig P A C (genJ P A C) = 0 ∧
    hProjSig P A C (genSig P A C) =
      (8 : ℤ) • ((genV P A C * genV P A C) * genSig P A C) := by
  rcases archetype_A13_homogenized_projectors (P := P) hP A C (0 : B) with
    ⟨_, hV, hVΦ, hVJ, hVSig, hPhi, hPhiV, hPhiJ, hPhiSig, hJ, hJV, hJPhi, hJSig,
      hSig, hSigV, hSigPhi, hSigJ⟩
  exact ⟨hV, hVΦ, hVJ, hVSig, hPhiV, hPhi, hPhiJ, hPhiSig, hJV, hJPhi, hJ, hJSig,
    hSigV, hSigPhi, hSigJ, hSig⟩

/-! ### AL₉: logistic coagulation -/

theorem rubedo_logistic_stone {P : B} (hP : P * P = P) (A C : B) :
    logisticBitPlus P A C = P - genSig P A C ∧
    logisticBitPlus P A C = P - genJ P A C * genPhi P A C ∧
    logisticBitMinus P A C = (1 - P) + genJ P A C * genPhi P A C ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (P + genPhi P A C) = genV P A C ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (logisticBitPlus P A C) =
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
          (P + genPhi P A C)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [logisticBitPlus, genSig, comm, qgtPlus, qgtMinus] <;> peirce_nf hP
  · have hJPhi := (albedo_split_quaternion_table hP A C).2.2.2.2.2.2.1
    calc
      logisticBitPlus P A C = P - genSig P A C := by
        simp [logisticBitPlus, genSig, comm, qgtPlus, qgtMinus] <;> peirce_nf hP
      _ = P - genJ P A C * genPhi P A C := by rw [← hJPhi]
  · simp [logisticBitMinus, genJ, genPhi, qgtPlus, qgtMinus] <;> peirce_nf hP
  · exact (golden_coagulation_discriminant P hP A C).1
  · have hLog : InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (logisticBitPlus P A C) =
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect (genV P A C) := by
        simp [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect,
          logisticBitPlus, genV, anticomm, genSig, comm, qgtPlus, qgtMinus] <;>
          peirce_nf hP
    have hGold := (golden_coagulation_discriminant P hP A C).1
    rw [hLog, ← congrArg InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      hGold.symm]

/-! ### AL₁₀: unipotent conjugation transports the finite resolvent -/

def epistemicUnipotentDress (P A X : B) : B :=
  (1 + conePlus P A) * X * (1 - conePlus P A)

theorem projectio_dressed_resolvent
    {P P₁ P₂ : B} (hP : P * P = P)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0) (A C X Y : B) :
    epistemicUnipotentDress P A (X * Y) =
      epistemicUnipotentDress P A X * epistemicUnipotentDress P A Y ∧
    epistemicUnipotentDress P A (1 - twoStepUpper P₁ P₂ A C) *
      epistemicUnipotentDress P A (twoStepResolvent P₁ P₂ A C) = 1 ∧
    epistemicUnipotentDress P A (twoStepResolvent P₁ P₂ A C) *
      epistemicUnipotentDress P A (1 - twoStepUpper P₁ P₂ A C) = 1 := by
  have hNil : conePlus P A * conePlus P A = 0 := conePlus_mul_conePlus hP A A
  have hInv : (1 - conePlus P A) * (1 + conePlus P A) = 1 := by
    simp only [sub_mul, mul_add, one_mul, mul_one, hNil]
    noncomm_ring
  have hInv' : (1 + conePlus P A) * (1 - conePlus P A) = 1 := by
    simp only [add_mul, mul_sub, one_mul, mul_one, hNil]
    noncomm_ring
  have hMult : ∀ U V : B,
      epistemicUnipotentDress P A (U * V) =
        epistemicUnipotentDress P A U * epistemicUnipotentDress P A V := by
    intro U V
    unfold epistemicUnipotentDress
    calc
      (1 + conePlus P A) * (U * V) * (1 - conePlus P A) =
          (1 + conePlus P A) * U * (V * (1 - conePlus P A)) := by
            noncomm_ring
      _ = (1 + conePlus P A) * U *
          ((1 - conePlus P A) * (1 + conePlus P A) * V * (1 - conePlus P A)) := by
            rw [hInv]
            noncomm_ring
      _ = ((1 + conePlus P A) * U * (1 - conePlus P A)) *
          ((1 + conePlus P A) * V * (1 - conePlus P A)) := by
            noncomm_ring
  have hLeft := twoStepResolvent_left_inv h1 h2 h12 h21 A C
  have hRight := twoStepResolvent_right_inv h1 h2 h12 h21 A C
  refine ⟨hMult X Y, ?_, ?_⟩
  · calc
      epistemicUnipotentDress P A (1 - twoStepUpper P₁ P₂ A C) *
          epistemicUnipotentDress P A (twoStepResolvent P₁ P₂ A C) =
        epistemicUnipotentDress P A
          ((1 - twoStepUpper P₁ P₂ A C) * twoStepResolvent P₁ P₂ A C) :=
            (hMult _ _).symm
      _ = epistemicUnipotentDress P A 1 := by rw [hLeft]
      _ = 1 := by
        unfold epistemicUnipotentDress
        simp only [mul_one, hInv']
  · calc
      epistemicUnipotentDress P A (twoStepResolvent P₁ P₂ A C) *
          epistemicUnipotentDress P A (1 - twoStepUpper P₁ P₂ A C) =
        epistemicUnipotentDress P A
          (twoStepResolvent P₁ P₂ A C * (1 - twoStepUpper P₁ P₂ A C)) :=
            (hMult _ _).symm
      _ = epistemicUnipotentDress P A 1 := by rw [hRight]
      _ = 1 := by
        unfold epistemicUnipotentDress
        simp only [mul_one, hInv']

theorem stageD46_magnum_opus_completion
    {P P₁ P₂ : B} (hP : P * P = P)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0) (X A C : B) :
    conePlus P X + coneMinus P X = peirceAdSq P X ∧
    peirceAdCube P X = peirceAd P X ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genPhi P A C * genSig P A C = -genV P A C * genJ P A C ∧
    hProjV P A C (genPhi P A C) = 0 ∧
    hProjPhi P A C (genJ P A C) = 0 ∧
    logisticBitPlus P A C = P - genJ P A C * genPhi P A C ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (logisticBitPlus P A C) =
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
          (P + genPhi P A C)) ∧
    epistemicUnipotentDress P A (1 - twoStepUpper P₁ P₂ A C) *
      epistemicUnipotentDress P A (twoStepResolvent P₁ P₂ A C) = 1 ∧
    epistemicUnipotentDress P A (twoStepResolvent P₁ P₂ A C) *
      epistemicUnipotentDress P A (1 - twoStepUpper P₁ P₂ A C) = 1 := by
  rcases nigredo_commutator_sieve hP X with ⟨hN1, _, _, hN4, _⟩
  rcases albedo_split_quaternion_table hP A C with
    ⟨_, _, _, hA4, _, _, _, _, hA9, _⟩
  rcases citrinitas_full_mandala_matrix hP A C with
    ⟨_, hC2, _, _, _, _, hC7, _, _, _, _, _, _, _, _, _⟩
  rcases rubedo_logistic_stone hP A C with ⟨_, hR2, _, _, hR5⟩
  rcases projectio_dressed_resolvent hP h1 h2 h12 h21 A C X X with
    ⟨_, hDressedLeft, hDressedRight⟩
  exact ⟨hN1, hN4, hA4, hA9, hC2, hC7, hR2, hR5,
    hDressedLeft, hDressedRight⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine
