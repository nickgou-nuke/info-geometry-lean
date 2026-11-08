/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NoncommRing

/-!
# Peirce spine A₁₃, A₁₅: `V`-homogenized Klein–Hadamard projectors

The raw projectors of A₅/A₁₁ mix eigenvalues `V` and `V²`. Multiplying the
`ad_Φ²`, `ad_J²` channels by `V` makes all four channels have eigenvalue
`8 V²` on their own generator and `0` on the other three (A₁₃). The
second-order identities in A₁₅ are evaluated on those named generators, not
asserted as identities of endomorphisms on every input. These are additive
channels; the name `projector` does not assert ambient idempotence or
invertibility. No inverse of `V` is used.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def hProjV (P A C X : B) : B :=
  (8 : ℤ) • ((genV P A C * genV P A C) * X) +
    (genV P A C * derivSqPhi P A C X + genV P A C * derivSqJ P A C X + derivSqSig P A C X)
def hProjPhi (P A C X : B) : B :=
  genV P A C * derivSqPhi P A C X - genV P A C * derivSqJ P A C X - derivSqSig P A C X
def hProjJ (P A C X : B) : B :=
  genV P A C * derivSqJ P A C X - genV P A C * derivSqPhi P A C X - derivSqSig P A C X
def hProjSig (P A C X : B) : B :=
  derivSqSig P A C X - genV P A C * derivSqPhi P A C X - genV P A C * derivSqJ P A C X

/-- The connection obtained by compressing a seed to the upper Peirce sheet. -/
def sheetPlusConnection (P W : B) : B := P * W * P

/-- The connection obtained by compressing a seed to the lower Peirce sheet. -/
def sheetMinusConnection (P W : B) : B := (1 - P) * W * (1 - P)

/-- The even, sum connection of the two Peirce sheets. -/
def sheetConnectionSum (P W : B) : B :=
  sheetPlusConnection P W + sheetMinusConnection P W

/-- The even, difference connection of the two Peirce sheets. -/
def sheetConnectionDiff (P W : B) : B :=
  sheetPlusConnection P W - sheetMinusConnection P W

section SheetConnectionCrossover

variable {P : B} (hP : P * P = P)
include hP

/-- **Sum–difference crossover on the two Peirce sheets.** For an arbitrary
connection seed `W`, the compressed sum and difference act on the existing
Peirce throat `Φ,J` by exchanging commutators and anticommutators. This is a
ring identity; it does not assume a topology, a Klein-bottle quotient, or a
parallel-transport flow. -/
theorem sheetConnection_sum_difference_crossover (W A C : B) :
    comm (sheetConnectionDiff P W) (genPhi P A C) =
        anticomm (sheetConnectionSum P W) (genJ P A C) ∧
    anticomm (sheetConnectionDiff P W) (genPhi P A C) =
        comm (sheetConnectionSum P W) (genJ P A C) ∧
    comm (sheetConnectionDiff P W) (genJ P A C) =
        anticomm (sheetConnectionSum P W) (genPhi P A C) ∧
    anticomm (sheetConnectionDiff P W) (genJ P A C) =
        comm (sheetConnectionSum P W) (genPhi P A C) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (unfold comm anticomm sheetConnectionDiff sheetConnectionSum
      sheetPlusConnection sheetMinusConnection genPhi genJ;
     peirce_nf hP)

end SheetConnectionCrossover

/-! ### Unconditional commutator transport and its noncommutative defect -/

/-- Left scaling inside the first slot of a commutator has an exact
noncommutative correction. It vanishes when `v` commutes with `x`, and can
also vanish when the resulting commutator is annihilated by `a`; it is
retained here as an operator term. -/
theorem comm_left_scale_with_anomaly (v a x : B) :
    comm (v * a) x = v * comm a x + comm v x * a := by
  simp only [comm, mul_sub, sub_mul, mul_assoc]
  abel

/-- Left scaling inside the second slot likewise retains its commutator
defect, with no centralizer premise. -/
theorem comm_right_scale_with_anomaly (v a x : B) :
    comm a (v * x) = v * comm a x + comm a v * x := by
  simp only [comm, mul_sub, sub_mul, mul_assoc]
  abel

/-- The exact two-step transport law for a scaled commutator generator.
The terms involving `comm v` are the noncommutative correction; this law
does not impose a centralizer condition on the test operator. -/
theorem double_comm_left_scale_with_anomaly (v a x : B) :
    comm (v * a) (comm (v * a) x) =
      v * comm a (v * comm a x + comm v x * a) +
        comm v (v * comm a x + comm v x * a) * a := by
  calc
    comm (v * a) (comm (v * a) x) =
        comm (v * a) (v * comm a x + comm v x * a) := by
      rw [comm_left_scale_with_anomaly v a x]
    _ = v * comm a (v * comm a x + comm v x * a) +
          comm v (v * comm a x + comm v x * a) * a :=
      comm_left_scale_with_anomaly v a _

/-- Two independently scaled generators retain both scale-generator
commutators and the scale-scale commutator. This is the exact metric
transport law before imposing any centralizer condition. -/
theorem anticommutator_two_sided_scale_with_anomaly
    (u a v b : B) :
    anticomm (u * a) (v * b) =
      (u * v) * anticomm a b +
        u * comm a v * b + v * comm b u * a + comm v u * b * a := by
  simp only [anticomm, comm, mul_sub, sub_mul, mul_add, mul_assoc]
  abel

/-- The corresponding exact transport law for the chiral commutator.
Its correction terms record the same three noncommutative obstructions with
the signs dictated by the commutator. -/
theorem commutator_two_sided_scale_with_anomaly
    (u a v b : B) :
    comm (u * a) (v * b) =
      (u * v) * comm a b +
        u * comm a v * b - v * comm b u * a - comm v u * b * a := by
  simp only [comm, mul_sub, sub_mul, mul_assoc]
  abel

/-! ### Conditional covariance of inner double commutators

Scaling a generator inside an inner derivation is not automatically
homogeneous on the whole ring. The following ring-level lemmas state
sufficient commutation hypotheses before specializing to Peirce generators. -/

/-- If the scale commutes with the test element, it factors through a
commutator whose left entry is scaled. -/
theorem comm_left_scale (v a x : B) (hvx : v * x = x * v) :
    comm (v * a) x = v * comm a x := by
  unfold comm
  calc
    (v * a) * x - x * (v * a) = v * (a * x) - (x * v) * a := by
      congr 1
      · rw [mul_assoc]
      · rw [← mul_assoc]
    _ = v * (a * x) - (v * x) * a := by rw [hvx]
    _ = v * (a * x) - v * (x * a) := by
      congr 1
      exact mul_assoc v x a
    _ = v * (a * x - x * a) := by rw [← mul_sub]

/-- A scale commuting with `a` can be moved out of the right argument of
`ad a`. -/
theorem comm_right_scale (v a x : B) (hva : v * a = a * v) :
    comm a (v * x) = v * comm a x := by
  unfold comm
  calc
    a * (v * x) - (v * x) * a = (a * v) * x - (v * x) * a := by rw [← mul_assoc]
    _ = (v * a) * x - (v * x) * a := by rw [hva.symm]
    _ = v * (a * x) - (v * x) * a := by rw [mul_assoc]
    _ = v * (a * x) - v * (x * a) := by
      congr 1
      exact mul_assoc v x a
    _ = v * (a * x - x * a) := by rw [← mul_sub]

/-- Under the same centralizer conditions, a double inner commutator scales
quadratically. This is deliberately conditional on `v` commuting with the
test operator; it does not assert covariance on arbitrary `X : B`. -/
theorem double_comm_left_scale (v a x : B) (hva : v * a = a * v)
    (hvx : v * x = x * v) :
    comm (v * a) (comm (v * a) x) =
      (v * v) * comm a (comm a x) := by
  have hvInner : v * comm a x = comm a x * v := by
    unfold comm
    calc
      v * (a * x - x * a) = v * (a * x) - v * (x * a) := by rw [mul_sub]
      _ = (a * x) * v - (x * a) * v := by
        congr 1
        · calc
            v * (a * x) = (v * a) * x := by rw [mul_assoc]
            _ = (a * v) * x := by rw [hva]
            _ = a * (v * x) := by rw [← mul_assoc]
            _ = a * (x * v) := by rw [hvx]
            _ = (a * x) * v := by rw [mul_assoc]
        · calc
            v * (x * a) = (v * x) * a := by rw [mul_assoc]
            _ = (x * v) * a := by rw [hvx]
            _ = x * (v * a) := by rw [← mul_assoc]
            _ = x * (a * v) := by rw [hva]
            _ = (x * a) * v := by rw [mul_assoc]
      _ = (a * x - x * a) * v := by rw [← sub_mul]
  have hvInner' : v * (v * comm a x) = (v * comm a x) * v := by
    calc
      v * (v * comm a x) = v * (comm a x * v) := by rw [hvInner]
      _ = (v * comm a x) * v := by rw [← mul_assoc]
  calc
    comm (v * a) (comm (v * a) x) =
        comm (v * a) (v * comm a x) := by rw [comm_left_scale v a x hvx]
    _ = v * comm a (v * comm a x) := comm_left_scale v a _ hvInner'
    _ = v * (v * comm a (comm a x)) := by rw [comm_right_scale v a _ hva]
    _ = (v * v) * comm a (comm a x) := by rw [mul_assoc]

/-! ### A₁₇: group-sandwich character channels

These are additive polynomial maps on the ring. The names record their
formulas; they do not assert that the maps are group actions or automorphisms.
-/

def grpId (P A C X : B) : B := (genV P A C * genV P A C) * X
def grpPhi (P A C X : B) : B := genV P A C * (genPhi P A C * X * genPhi P A C)
def grpJ (P A C X : B) : B := -(genV P A C * (genJ P A C * X * genJ P A C))
def grpSig (P A C X : B) : B := genSig P A C * X * genSig P A C

def fourierV (P A C X : B) : B :=
  (2 : ℤ) • (grpId P A C X + grpPhi P A C X + grpJ P A C X + grpSig P A C X)
def fourierPhi (P A C X : B) : B :=
  (2 : ℤ) • (grpId P A C X + grpPhi P A C X - grpJ P A C X - grpSig P A C X)
def fourierJ (P A C X : B) : B :=
  (2 : ℤ) • (grpId P A C X - grpPhi P A C X + grpJ P A C X - grpSig P A C X)
def fourierSig (P A C X : B) : B :=
  (2 : ℤ) • (grpId P A C X - grpPhi P A C X - grpJ P A C X + grpSig P A C X)

/-! ### Degeneracy obstruction to interpreting the channels as automorphisms -/

/-- With both Peirce corners zero, each homogenized channel is the zero map.
Thus these operators, in general, are linear channels rather than elements of
a group of automorphisms. -/
theorem homogenized_channels_zero_at_zero_corners (P X : B) :
    hProjV P (0 : B) (0 : B) X = 0 ∧ hProjPhi P (0 : B) (0 : B) X = 0 ∧
      hProjJ P (0 : B) (0 : B) X = 0 ∧ hProjSig P (0 : B) (0 : B) X = 0 := by
  simp [hProjV, hProjPhi, hProjJ, hProjSig, derivSqPhi, derivSqJ, derivSqSig,
    genPhi, genJ, genV, genSig, anticomm, comm, conePlus, coneMinus]

/-- Any nonzero input witnesses failure of injectivity at the zero-corner
specialization. In particular, these homogenized channels cannot uniformly
be Galois automorphisms of the ambient ring. -/
theorem hProjV_not_injective_at_zero_corners (P X : B) (hX : X ≠ 0) :
    ¬ Function.Injective (hProjV P (0 : B) (0 : B)) := by
  intro hinj
  have hEq : hProjV P (0 : B) (0 : B) X = hProjV P (0 : B) (0 : B) 0 := by
    rw [(homogenized_channels_zero_at_zero_corners P X).1,
      (homogenized_channels_zero_at_zero_corners P 0).1]
  exact hX (hinj hEq)

/-- On every nontrivial ring, the zero-corner specialization is an explicit
counterexample to the claim that `hProjV` is an ambient ring automorphism. -/
theorem hProjV_not_injective_at_zero_corners_of_nontrivial [Nontrivial B] (P : B) :
    ¬ Function.Injective (hProjV P (0 : B) (0 : B)) :=
  hProjV_not_injective_at_zero_corners P 1 one_ne_zero

variable {P : B} (hP : P * P = P)
include hP

/-! The four sandwich channels act on the tetraktys generators with the
character table below. The Fourier combinations agree with the homogenized
channels on their matching generators, with common operator-valued scale
`8 V²` already established by A₁₃.
-/

theorem archetype_A17_group_sandwich_character_table (A C : B) :
    grpPhi P A C (genV P A C) = grpId P A C (genV P A C) ∧
    grpPhi P A C (genPhi P A C) = grpId P A C (genPhi P A C) ∧
    grpPhi P A C (genJ P A C) = -grpId P A C (genJ P A C) ∧
    grpPhi P A C (genSig P A C) = -grpId P A C (genSig P A C) ∧
    grpJ P A C (genV P A C) = grpId P A C (genV P A C) ∧
    grpJ P A C (genPhi P A C) = -grpId P A C (genPhi P A C) ∧
    grpJ P A C (genJ P A C) = grpId P A C (genJ P A C) ∧
    grpJ P A C (genSig P A C) = -grpId P A C (genSig P A C) ∧
    grpSig P A C (genV P A C) = grpId P A C (genV P A C) ∧
    grpSig P A C (genPhi P A C) = -grpId P A C (genPhi P A C) ∧
    grpSig P A C (genJ P A C) = -grpId P A C (genJ P A C) ∧
    grpSig P A C (genSig P A C) = grpId P A C (genSig P A C) ∧
    hProjV P A C (genV P A C) = fourierV P A C (genV P A C) ∧
    hProjPhi P A C (genPhi P A C) = fourierPhi P A C (genPhi P A C) ∧
    hProjJ P A C (genJ P A C) = fourierJ P A C (genJ P A C) ∧
    hProjSig P A C (genSig P A C) = fourierSig P A C (genSig P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [grpId, grpPhi, grpJ, grpSig, fourierV, fourierPhi, fourierJ, fourierSig,
      hProjV, hProjPhi, hProjJ, hProjSig, derivSqPhi, derivSqJ, derivSqSig]; peirce_nf hP)

/-! ### A₁₃ -/

theorem archetype_A13_homogenized_projectors (A C X : B) :
    hProjV P A C X + hProjPhi P A C X + hProjJ P A C X + hProjSig P A C X =
      (8 : ℤ) • ((genV P A C * genV P A C) * X) ∧
    hProjV P A C (genV P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genV P A C) ∧
    hProjV P A C (genPhi P A C) = 0 ∧
    hProjV P A C (genJ P A C) = 0 ∧
    hProjV P A C (genSig P A C) = 0 ∧
    hProjPhi P A C (genPhi P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) ∧
    hProjPhi P A C (genV P A C) = 0 ∧
    hProjPhi P A C (genJ P A C) = 0 ∧
    hProjPhi P A C (genSig P A C) = 0 ∧
    hProjJ P A C (genJ P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genJ P A C) ∧
    hProjJ P A C (genV P A C) = 0 ∧
    hProjJ P A C (genPhi P A C) = 0 ∧
    hProjJ P A C (genSig P A C) = 0 ∧
    hProjSig P A C (genSig P A C) = (8 : ℤ) • ((genV P A C * genV P A C) * genSig P A C) ∧
    hProjSig P A C (genV P A C) = 0 ∧
    hProjSig P A C (genPhi P A C) = 0 ∧
    hProjSig P A C (genJ P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [hProjV, hProjPhi, hProjJ, hProjSig, derivSqPhi, derivSqJ, derivSqSig]);
      peirce_nf hP)

/-! ### Defect-vielbein transport into the A₁₃ channel theorem

The scale is a change of the upper Peirce generator. Its metric is the
idempotency defect of the original metric, with no normalization imposed.
The channel conclusions below are obtained by applying A₁₃ to this transported
pair; the other grades remain the actual transported operators. -/

/-- Transport the upper Peirce generator by the defect scale. The first
identity identifies the transported cone; the last identifies its exact new
metric. -/
theorem defect_vielbein_generator_transport (A C : B) :
    let V := genV P A C
    conePlus P ((V - 1) * conePlus P A) = (V - 1) * conePlus P A ∧
    genPhi P ((V - 1) * conePlus P A) C =
      (V - 1) * conePlus P A + coneMinus P C ∧
    genJ P ((V - 1) * conePlus P A) C =
      (V - 1) * conePlus P A - coneMinus P C ∧
    genV P ((V - 1) * conePlus P A) C = V * V - V := by
  dsimp only
  have hLeft : P * ((genV P A C - 1) * conePlus P A) =
      (genV P A C - 1) * conePlus P A := by peirce_nf hP
  have hRight : ((genV P A C - 1) * conePlus P A) * P = 0 := by
    peirce_nf hP
  have hCone : conePlus P ((genV P A C - 1) * conePlus P A) =
      (genV P A C - 1) * conePlus P A := by
    change P * ((genV P A C - 1) * conePlus P A) * (1 - P) = _
    calc
      P * ((genV P A C - 1) * conePlus P A) * (1 - P) =
          ((genV P A C - 1) * conePlus P A) * (1 - P) := by rw [hLeft]
      _ = (genV P A C - 1) * conePlus P A := by
        simp only [mul_sub, mul_one, hRight, sub_zero]
  refine ⟨hCone, ?_, ?_, ?_⟩
  · rw [genPhi, hCone]
  · rw [genJ, hCone]
  · rw [genV, hCone]
    peirce_nf hP

/-- Apply the existing A₁₃ channel theorem to the defect-vielbein transported
pair. This records the exact eigenvalue and the three off-channel annihilation
relations for the transported `Φ` grade, without a defect-shell hypothesis. -/
theorem defect_vielbein_phi_channel_spectrum (A C : B) :
    let V := genV P A C
    let Aδ := (V - 1) * conePlus P A
    let Φδ := genPhi P Aδ C
    let Jδ := genJ P Aδ C
    let Vδ := genV P Aδ C
    let Sigδ := genSig P Aδ C
    hProjPhi P Aδ C Φδ =
        (8 : ℤ) • (((V * V - V) * (V * V - V)) * Φδ) ∧
      hProjPhi P Aδ C Vδ = 0 ∧
      hProjPhi P Aδ C Jδ = 0 ∧
      hProjPhi P Aδ C Sigδ = 0 := by
  dsimp only
  rcases archetype_A13_homogenized_projectors hP
      ((genV P A C - 1) * conePlus P A) C
      (genPhi P ((genV P A C - 1) * conePlus P A) C) with
    ⟨_, _, _, _, _, hEigen, hV, hJ, hSig, _, _, _, _, _, _, _, _⟩
  have hMetric := (defect_vielbein_generator_transport hP A C).2.2.2
  rw [hMetric] at hEigen
  exact ⟨hEigen, hV, hJ, hSig⟩

/-! ### A₁₅ -/

/-- The mass `V` commutes with `Φ`, `J`, `Σ` (right-associated rewriting forms). -/
theorem mass_commute_generators (A C z : B) :
    genPhi P A C * (genV P A C * z) = genV P A C * (genPhi P A C * z) ∧
    genJ P A C * (genV P A C * z) = genV P A C * (genJ P A C * z) ∧
    genSig P A C * (genV P A C * z) = genV P A C * (genSig P A C * z) ∧
    genPhi P A C * genV P A C = genV P A C * genPhi P A C ∧
    genJ P A C * genV P A C = genV P A C * genJ P A C ∧
    genSig P A C * genV P A C = genV P A C * genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Conditional Peirce covariance.** Under symmetric
rescaling by the Peirce metric `V`, the double commutators of `Φ` and `J`
scale by `V²`, while the double commutator of `Σ` scales by `V⁴`. The input
`X` must commute with `V`; without that condition, commutators with the scale
produce extra terms. -/
theorem peirce_double_derivation_covariance_on_centralizer
    (A C X : B) (hVX : genV P A C * X = X * genV P A C) :
    comm (genV P A C * genPhi P A C)
        (comm (genV P A C * genPhi P A C) X) =
      (genV P A C * genV P A C) *
        comm (genPhi P A C) (comm (genPhi P A C) X) ∧
    comm (genV P A C * genJ P A C)
        (comm (genV P A C * genJ P A C) X) =
      (genV P A C * genV P A C) *
        comm (genJ P A C) (comm (genJ P A C) X) ∧
    comm ((genV P A C * genV P A C) * genSig P A C)
        (comm ((genV P A C * genV P A C) * genSig P A C) X) =
      ((genV P A C * genV P A C) * (genV P A C * genV P A C)) *
        comm (genSig P A C) (comm (genSig P A C) X) := by
  have hVPhi : genV P A C * genPhi P A C = genPhi P A C * genV P A C := by
    peirce_nf hP
  have hVJ : genV P A C * genJ P A C = genJ P A C * genV P A C := by
    peirce_nf hP
  have hVSig : genV P A C * genSig P A C = genSig P A C * genV P A C := by
    peirce_nf hP
  have hV2X : (genV P A C * genV P A C) * X =
      X * (genV P A C * genV P A C) := by
    calc
      (genV P A C * genV P A C) * X =
          genV P A C * (genV P A C * X) := by rw [mul_assoc]
      _ = genV P A C * (X * genV P A C) := by rw [hVX]
      _ = (genV P A C * X) * genV P A C := by rw [← mul_assoc]
      _ = (X * genV P A C) * genV P A C := by rw [hVX]
      _ = X * (genV P A C * genV P A C) := by rw [mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · exact double_comm_left_scale _ _ _ hVPhi hVX
  · exact double_comm_left_scale _ _ _ hVJ hVX
  · exact double_comm_left_scale _ _ _ (by
      calc
        (genV P A C * genV P A C) * genSig P A C =
            genV P A C * (genV P A C * genSig P A C) := by rw [mul_assoc]
        _ = genV P A C * (genSig P A C * genV P A C) := by rw [hVSig]
        _ = (genV P A C * genSig P A C) * genV P A C := by rw [← mul_assoc]
        _ = (genSig P A C * genV P A C) * genV P A C := by rw [hVSig]
        _ = genSig P A C * (genV P A C * genV P A C) := by rw [mul_assoc]) hV2X

omit hP in
/-- The homogenized projectors are additive. -/
theorem hProj_add (A C X Y : B) :
    hProjV P A C (X + Y) = hProjV P A C X + hProjV P A C Y ∧
    hProjPhi P A C (X + Y) = hProjPhi P A C X + hProjPhi P A C Y ∧
    hProjJ P A C (X + Y) = hProjJ P A C X + hProjJ P A C Y ∧
    hProjSig P A C (X + Y) = hProjSig P A C X + hProjSig P A C Y := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [hProjV, hProjPhi, hProjJ, hProjSig, derivSqPhi, derivSqJ, derivSqSig, comm];
      noncomm_ring)

omit hP in
/-- The homogenized projectors are `ℤ`-linear. -/
theorem hProj_zsmul (A C Y : B) (n : ℤ) :
    hProjV P A C (n • Y) = n • hProjV P A C Y ∧
    hProjPhi P A C (n • Y) = n • hProjPhi P A C Y ∧
    hProjJ P A C (n • Y) = n • hProjJ P A C Y ∧
    hProjSig P A C (n • Y) = n • hProjSig P A C Y :=
  ⟨map_zsmul (AddMonoidHom.mk' (hProjV P A C) fun X Y => (hProj_add A C X Y).1) n Y,
    map_zsmul (AddMonoidHom.mk' (hProjPhi P A C) fun X Y => (hProj_add A C X Y).2.1) n Y,
    map_zsmul (AddMonoidHom.mk' (hProjJ P A C) fun X Y => (hProj_add A C X Y).2.2.1) n Y,
    map_zsmul (AddMonoidHom.mk' (hProjSig P A C) fun X Y => (hProj_add A C X Y).2.2.2) n Y⟩

/-- The homogenized projectors commute with left multiplication by `V`. -/
theorem hProj_mass_mul (A C Y : B) :
    hProjV P A C (genV P A C * Y) = genV P A C * hProjV P A C Y ∧
    hProjPhi P A C (genV P A C * Y) = genV P A C * hProjPhi P A C Y ∧
    hProjJ P A C (genV P A C * Y) = genV P A C * hProjJ P A C Y ∧
    hProjSig P A C (genV P A C * Y) = genV P A C * hProjSig P A C Y := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [hProjV, hProjPhi, hProjJ, hProjSig, derivSqPhi, derivSqJ, derivSqSig, comm,
      mul_sub, sub_mul, mul_add, neg_sub, mul_smul_comm, mul_assoc,
      (mass_commute_generators hP A C _).1, (mass_commute_generators hP A C _).2.1,
      (mass_commute_generators hP A C _).2.2.1]

/-- Iterated operator-mass dilation: each homogenized channel intertwines
left multiplication by every natural power of `V`. This follows from the
one-step mass-intertwining law; it does not assert covariance under rescaling
the generators or centrality of `V` in the ambient ring. -/
theorem hProj_mass_power_mul (A C : B) (n : ℕ) (Y : B) :
    hProjV P A C (genV P A C ^ n * Y) =
      genV P A C ^ n * hProjV P A C Y ∧
    hProjPhi P A C (genV P A C ^ n * Y) =
      genV P A C ^ n * hProjPhi P A C Y ∧
    hProjJ P A C (genV P A C ^ n * Y) =
      genV P A C ^ n * hProjJ P A C Y ∧
    hProjSig P A C (genV P A C ^ n * Y) =
      genV P A C ^ n * hProjSig P A C Y := by
  induction n generalizing Y with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      rcases hProj_mass_mul hP A C Y with ⟨hV, hPhi, hJ, hSig⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · calc
          hProjV P A C ((genV P A C ^ n * genV P A C) * Y) =
              hProjV P A C (genV P A C ^ n * (genV P A C * Y)) := by rw [mul_assoc]
          _ = genV P A C ^ n * hProjV P A C (genV P A C * Y) :=
            (ih (genV P A C * Y)).1
          _ = genV P A C ^ n * (genV P A C * hProjV P A C Y) := by rw [hV]
          _ = (genV P A C ^ n * genV P A C) * hProjV P A C Y := by rw [mul_assoc]
      · calc
          hProjPhi P A C ((genV P A C ^ n * genV P A C) * Y) =
              hProjPhi P A C (genV P A C ^ n * (genV P A C * Y)) := by rw [mul_assoc]
          _ = genV P A C ^ n * hProjPhi P A C (genV P A C * Y) :=
            (ih (genV P A C * Y)).2.1
          _ = genV P A C ^ n * (genV P A C * hProjPhi P A C Y) := by rw [hPhi]
          _ = (genV P A C ^ n * genV P A C) * hProjPhi P A C Y := by rw [mul_assoc]
      · calc
          hProjJ P A C ((genV P A C ^ n * genV P A C) * Y) =
              hProjJ P A C (genV P A C ^ n * (genV P A C * Y)) := by rw [mul_assoc]
          _ = genV P A C ^ n * hProjJ P A C (genV P A C * Y) :=
            (ih (genV P A C * Y)).2.2.1
          _ = genV P A C ^ n * (genV P A C * hProjJ P A C Y) := by rw [hJ]
          _ = (genV P A C ^ n * genV P A C) * hProjJ P A C Y := by rw [mul_assoc]
      · calc
          hProjSig P A C ((genV P A C ^ n * genV P A C) * Y) =
              hProjSig P A C (genV P A C ^ n * (genV P A C * Y)) := by rw [mul_assoc]
          _ = genV P A C ^ n * hProjSig P A C (genV P A C * Y) :=
            (ih (genV P A C * Y)).2.2.2
          _ = genV P A C ^ n * (genV P A C * hProjSig P A C Y) := by rw [hSig]
          _ = (genV P A C ^ n * genV P A C) * hProjSig P A C Y := by rw [mul_assoc]

theorem archetype_A15_second_order_orthogonality (A C : B) :
    hProjV P A C (hProjV P A C (genV P A C)) =
      (8 : ℤ) • ((genV P A C * genV P A C) * hProjV P A C (genV P A C)) ∧
    hProjPhi P A C (hProjPhi P A C (genPhi P A C)) =
      (8 : ℤ) • ((genV P A C * genV P A C) * hProjPhi P A C (genPhi P A C)) ∧
    hProjJ P A C (hProjJ P A C (genJ P A C)) =
      (8 : ℤ) • ((genV P A C * genV P A C) * hProjJ P A C (genJ P A C)) ∧
    hProjSig P A C (hProjSig P A C (genSig P A C)) =
      (8 : ℤ) • ((genV P A C * genV P A C) * hProjSig P A C (genSig P A C)) ∧
    hProjPhi P A C (hProjV P A C (genV P A C)) = 0 ∧
    hProjJ P A C (hProjV P A C (genV P A C)) = 0 ∧
    hProjSig P A C (hProjV P A C (genV P A C)) = 0 ∧
    hProjV P A C (hProjPhi P A C (genPhi P A C)) = 0 ∧
    hProjJ P A C (hProjPhi P A C (genPhi P A C)) = 0 ∧
    hProjSig P A C (hProjPhi P A C (genPhi P A C)) = 0 ∧
    hProjV P A C (hProjJ P A C (genJ P A C)) = 0 ∧
    hProjPhi P A C (hProjJ P A C (genJ P A C)) = 0 ∧
    hProjSig P A C (hProjJ P A C (genJ P A C)) = 0 ∧
    hProjV P A C (hProjSig P A C (genSig P A C)) = 0 ∧
    hProjPhi P A C (hProjSig P A C (genSig P A C)) = 0 ∧
    hProjJ P A C (hProjSig P A C (genSig P A C)) = 0 := by
  obtain ⟨_, hV1, hV2, hV3, hV4, hF1, hF2, hF3, hF4, hJ1, hJ2, hJ3, hJ4, hS1, hS2, hS3, hS4⟩ :=
    archetype_A13_homogenized_projectors hP A C (0 : B)
  have m := hProj_mass_mul hP A C
  have z := fun Y : B => hProj_zsmul (P := P) A C Y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hV1, hF1, hJ1, hS1, mul_assoc, (z _ _).1, (z _ _).2.1, (z _ _).2.2.1, (z _ _).2.2.2,
      (m _).1, (m _).2.1, (m _).2.2.1, (m _).2.2.2,
      hV2, hV3, hV4, hF2, hF3, hF4, hJ2, hJ3, hJ4, hS2, hS3, hS4, mul_zero, smul_zero]

/-! ### A₂₀: equivariance of the homogenized channels under Peirce sandwiches -/

/-- A two-sided multiplication expansion of the `V`-homogenized channel. -/
theorem hProjV_expansion (A C X : B) :
    hProjV P A C X =
      (5 : ℤ) • ((genV P A C * genV P A C) * X) -
        (2 : ℤ) • (genV P A C * X * genV P A C) -
        X * (genV P A C * genV P A C) +
        (2 : ℤ) • (genV P A C * genPhi P A C * X * genPhi P A C) -
        (2 : ℤ) • (genV P A C * genJ P A C * X * genJ P A C) +
        (2 : ℤ) • (genSig P A C * X * genSig P A C) := by
  simp only [hProjV, derivSqPhi, derivSqJ, derivSqSig, comm]
  peirce_nf hP

theorem hProjPhi_sandwichJ (A C X : B) :
    hProjPhi P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjPhi P A C X * (-genJ P A C) := by
  simp only [hProjPhi, derivSqPhi, derivSqJ, derivSqSig]
  peirce_nf hP

theorem hProjJ_sandwichJ (A C X : B) :
    hProjJ P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjJ P A C X * (-genJ P A C) := by
  simp only [hProjJ, derivSqPhi, derivSqJ, derivSqSig]
  peirce_nf hP

theorem hProjSig_sandwichJ (A C X : B) :
    hProjSig P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjSig P A C X * (-genJ P A C) := by
  simp only [hProjSig, derivSqPhi, derivSqJ, derivSqSig]
  peirce_nf hP

theorem hProjPhi_sandwichPhi (A C X : B) :
    hProjPhi P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjPhi P A C X * genPhi P A C := by
  simp only [hProjPhi, derivSqPhi, derivSqJ, derivSqSig]
  peirce_nf hP

theorem hProjJ_sandwichPhi (A C X : B) :
    hProjJ P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjJ P A C X * genPhi P A C := by
  simp only [hProjJ, derivSqPhi, derivSqJ, derivSqSig]
  peirce_nf hP

theorem hProjSig_sandwichPhi (A C X : B) :
    hProjSig P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjSig P A C X * genPhi P A C := by
  simp only [hProjSig, derivSqPhi, derivSqJ, derivSqSig]
  peirce_nf hP

omit hP in
theorem hProjV_decomp (A C Y : B) :
    hProjV P A C Y =
      (8 : ℤ) • ((genV P A C * genV P A C) * Y) -
        (hProjPhi P A C Y + hProjJ P A C Y + hProjSig P A C Y) := by
  simp only [hProjV, hProjPhi, hProjJ, hProjSig]
  abel

theorem grpId_sandwichJ (A C X : B) :
    (genV P A C * genV P A C) * (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * ((genV P A C * genV P A C) * X) * (-genJ P A C) := by
  peirce_nf hP

theorem grpId_sandwichPhi (A C X : B) :
    (genV P A C * genV P A C) * (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * ((genV P A C * genV P A C) * X) * genPhi P A C := by
  peirce_nf hP

omit hP in
theorem zsmul_mul_left_right (n : ℤ) (U V : B) :
    (n • U) * V = n • (U * V) ∧
    U * (n • V) = n • (U * V) :=
  ⟨map_zsmul (AddMonoidHom.mk' (fun u => u * V) (fun x y => add_mul x y V)) n U,
   map_zsmul (AddMonoidHom.mk' (fun v => U * v) (fun x y => mul_add U x y)) n V⟩

/-- The `V`-homogenized channel intertwines with the sandwich by `J`. -/
theorem hProjV_sandwichJ (A C X : B) :
    hProjV P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjV P A C X * (-genJ P A C) := by
  rw [hProjV_decomp, hProjV_decomp, grpId_sandwichJ hP,
    hProjPhi_sandwichJ hP, hProjJ_sandwichJ hP, hProjSig_sandwichJ hP]
  simp only [mul_sub, sub_mul, mul_add, add_mul,
    (zsmul_mul_left_right _ _ _).1, (zsmul_mul_left_right _ _ _).2]

/-- The `V`-homogenized channel intertwines with the sandwich by `Φ`. -/
theorem hProjV_sandwichPhi (A C X : B) :
    hProjV P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjV P A C X * genPhi P A C := by
  rw [hProjV_decomp, hProjV_decomp, grpId_sandwichPhi hP,
    hProjPhi_sandwichPhi hP, hProjJ_sandwichPhi hP, hProjSig_sandwichPhi hP]
  simp only [mul_sub, sub_mul, mul_add, add_mul,
    (zsmul_mul_left_right _ _ _).1, (zsmul_mul_left_right _ _ _).2]

/-- Theorem A20 combines the two families of explicit sandwich intertwiners.
These are polynomial maps, not asserted to be automorphisms or group actions. -/
theorem archetype_A20_weyl_clifford_covariance_of_homogenized_projectors (A C X : B) :
    hProjV P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjV P A C X * (-genJ P A C) ∧
    hProjPhi P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjPhi P A C X * (-genJ P A C) ∧
    hProjJ P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjJ P A C X * (-genJ P A C) ∧
    hProjSig P A C (genJ P A C * X * (-genJ P A C)) =
      genJ P A C * hProjSig P A C X * (-genJ P A C) ∧
    hProjV P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjV P A C X * genPhi P A C ∧
    hProjPhi P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjPhi P A C X * genPhi P A C ∧
    hProjJ P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjJ P A C X * genPhi P A C ∧
    hProjSig P A C (genPhi P A C * X * genPhi P A C) =
      genPhi P A C * hProjSig P A C X * genPhi P A C := by
  exact ⟨hProjV_sandwichJ hP A C X, hProjPhi_sandwichJ hP A C X,
    hProjJ_sandwichJ hP A C X, hProjSig_sandwichJ hP A C X,
    hProjV_sandwichPhi hP A C X, hProjPhi_sandwichPhi hP A C X,
    hProjJ_sandwichPhi hP A C X, hProjSig_sandwichPhi hP A C X⟩

/-! ### A₆₂: finite array of homogenized channels and Peirce decomposition maps -/

/-- Row-indexed homogenized channel (`0 = V`, `1 = Φ`, `2 = J`, `3 = Σ`). -/
def homogenizedChannel (P A C : B) (r : Fin 4) : B → B :=
  match r.val with
  | 0 => hProjV P A C
  | 1 => hProjPhi P A C
  | 2 => hProjJ P A C
  | _ => hProjSig P A C

/-- Column-indexed Peirce block extractor (`0 = 11`, `1 = 00`, `2 = 10`, `3 = 01`,
`4 = evenGrade`, `5 = oddGrade`). -/
def peirceDecompositionMap (P : B) (c : Fin 6) : B → B :=
  match c.val with
  | 0 => peirce11 P
  | 1 => peirce00 P
  | 2 => conePlus P
  | 3 => coneMinus P
  | 4 => evenGrade P
  | _ => oddGrade P

/-- Entry `(r, c)` of the finite channel/decomposition array. -/
def peirceChannelEntry (P A C : B) (r : Fin 4) (c : Fin 6) (X : B) : B :=
  homogenizedChannel P A C r (peirceDecompositionMap P c X)

/-- Sum across the six decomposition maps in row `r`. -/
def peirceChannelRowSum (P A C : B) (r : Fin 4) (X : B) : B :=
  peirceChannelEntry P A C r 0 X + peirceChannelEntry P A C r 1 X +
  peirceChannelEntry P A C r 2 X + peirceChannelEntry P A C r 3 X +
  peirceChannelEntry P A C r 4 X + peirceChannelEntry P A C r 5 X

omit hP in
/-- **Theorem A62 (finite Peirce channel/decomposition partition):**
1. The first four columns (`peirce11`, `peirce00`, `conePlus`, `coneMinus`) partition the
   identity (`peirceDecompositionMap P 0 X + ... + peirceDecompositionMap P 3 X = X`).
2. Columns `4` and `5` (`evenGrade`, `oddGrade`) partition the identity
   (`peirceDecompositionMap P 4 X + peirceDecompositionMap P 5 X = X`).
3. Every row sum across all 6 columns equals `(2 : ℤ) • homogenizedChannel P A C r X`.
4. Summing all 24 entries of the `4 × 6` array yields `(16 : ℤ) • ((genV P A C * genV P A C) * X)`. -/
theorem archetype_A62_peirce_channel_decomposition_partition (A C X : B) :
    peirceDecompositionMap P 0 X + peirceDecompositionMap P 1 X + peirceDecompositionMap P 2 X + peirceDecompositionMap P 3 X = X ∧
    peirceDecompositionMap P 4 X + peirceDecompositionMap P 5 X = X ∧
    (∀ r : Fin 4, peirceChannelRowSum P A C r X = (2 : ℤ) • homogenizedChannel P A C r X) ∧
    peirceChannelRowSum P A C 0 X + peirceChannelRowSum P A C 1 X + peirceChannelRowSum P A C 2 X + peirceChannelRowSum P A C 3 X =
      (16 : ℤ) • ((genV P A C * genV P A C) * X) := by
  have hRow : ∀ r : Fin 4, peirceChannelRowSum P A C r X = (2 : ℤ) • homogenizedChannel P A C r X := by
    rintro ⟨r, hr⟩
    rcases r with _ | _ | _ | _ | r
    · change hProjV P A C (peirce11 P X) + hProjV P A C (peirce00 P X) +
          hProjV P A C (conePlus P X) + hProjV P A C (coneMinus P X) +
          hProjV P A C (evenGrade P X) + hProjV P A C (oddGrade P X) =
        (2 : ℤ) • hProjV P A C X
      unfold peirce11 peirce00 conePlus coneMinus evenGrade oddGrade
        hProjV derivSqPhi derivSqJ derivSqSig comm
      noncomm_ring
    · change hProjPhi P A C (peirce11 P X) + hProjPhi P A C (peirce00 P X) +
          hProjPhi P A C (conePlus P X) + hProjPhi P A C (coneMinus P X) +
          hProjPhi P A C (evenGrade P X) + hProjPhi P A C (oddGrade P X) =
        (2 : ℤ) • hProjPhi P A C X
      unfold peirce11 peirce00 conePlus coneMinus evenGrade oddGrade
        hProjPhi derivSqPhi derivSqJ derivSqSig comm
      noncomm_ring
    · change hProjJ P A C (peirce11 P X) + hProjJ P A C (peirce00 P X) +
          hProjJ P A C (conePlus P X) + hProjJ P A C (coneMinus P X) +
          hProjJ P A C (evenGrade P X) + hProjJ P A C (oddGrade P X) =
        (2 : ℤ) • hProjJ P A C X
      unfold peirce11 peirce00 conePlus coneMinus evenGrade oddGrade
        hProjJ derivSqPhi derivSqJ derivSqSig comm
      noncomm_ring
    · change hProjSig P A C (peirce11 P X) + hProjSig P A C (peirce00 P X) +
          hProjSig P A C (conePlus P X) + hProjSig P A C (coneMinus P X) +
          hProjSig P A C (evenGrade P X) + hProjSig P A C (oddGrade P X) =
        (2 : ℤ) • hProjSig P A C X
      unfold peirce11 peirce00 conePlus coneMinus evenGrade oddGrade
        hProjSig derivSqPhi derivSqJ derivSqSig comm
      noncomm_ring
    · omega
  refine ⟨?_, ?_, hRow, ?_⟩
  · change peirce11 P X + peirce00 P X + conePlus P X + coneMinus P X = X
    unfold peirce11 peirce00 conePlus coneMinus
    noncomm_ring
  · change evenGrade P X + oddGrade P X = X
    unfold evenGrade oddGrade
    noncomm_ring
  · rw [hRow 0, hRow 1, hRow 2, hRow 3]
    change (2 : ℤ) • hProjV P A C X + (2 : ℤ) • hProjPhi P A C X +
        (2 : ℤ) • hProjJ P A C X + (2 : ℤ) • hProjSig P A C X =
      (16 : ℤ) • ((genV P A C * genV P A C) * X)
    unfold hProjV hProjPhi hProjJ hProjSig
    noncomm_ring

end InfoGeometry.OperatorAlgebra.PeirceSpine
