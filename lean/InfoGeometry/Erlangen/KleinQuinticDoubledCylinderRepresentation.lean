/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Erlangen.KleinApolloniusQuinticResolvent
import InfoGeometry.Erlangen.KleinQuinticCantorApollonianBridge
import InfoGeometry.Erlangen.KleinQuinticVietaBinaryBridge
import InfoGeometry.Categorical.CantorDoubleCylinderColimitAlgebra

/-!
# Signed quintic orbit coordinates in doubled finite Cantor-cylinder fibers

This file realizes the complex five-coordinate signed orbit module as a
subspace of the stage-three Cantor cylinder coordinate carrier with fiber
`DoubledSpace ℝ`. The real and imaginary parts occupy the two real components
of that fiber. The signed cycle is extended to the other three cylinders by
the identity. The finite-stage action is also shown to be the restriction of
the owner’s stage operator algebra representation on `H_lp ℝ` to the embedded
finite-coordinate subspace.
-/

noncomputable section

namespace InfoGeometry.Erlangen.KleinQuinticDoubledCylinderRepresentation

open InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent
open InfoGeometry.Erlangen.KleinApolloniusQuinticResolvent
open InfoGeometry.Erlangen.KleinQuinticCantorApollonianBridge
open InfoGeometry.Erlangen.KleinQuinticVietaBinaryBridge
open InfoGeometry.OperatorAlgebra.CantorDoubleCylinderFractalColimit
open InfoGeometry.Categorical.CantorDoubleCylinderColimitAlgebra
open InfoGeometry.Krein
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.ConcreteHilbertCommutation
open InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
open InfoGeometry.Topology
open Classical

private def bit0 : Fin 3 := ⟨0, by decide⟩
private def bit1 : Fin 3 := ⟨1, by decide⟩
private def bit2 : Fin 3 := ⟨2, by decide⟩

private def q0 : Fin 5 := ⟨0, by decide⟩
private def q1 : Fin 5 := ⟨1, by decide⟩
private def q2 : Fin 5 := ⟨2, by decide⟩
private def q3 : Fin 5 := ⟨3, by decide⟩
private def q4 : Fin 5 := ⟨4, by decide⟩

private theorem word_eq_of_bits (w : BitWord 3) (a b c : Bool)
    (h0 : w bit0 = a) (h1 : w bit1 = b) (h2 : w bit2 = c) :
    w = ![a, b, c] := by
  ext i
  fin_cases i
  · simpa [bit0] using h0
  · simpa [bit1] using h1
  · simpa [bit2] using h2

/-- Five distinct depth-three Cantor cylinder addresses. -/
def quinticCylinderAddress (k : Fin 5) : BitWord 3 :=
  match k.val with
  | 0 => ![false, false, false]
  | 1 => ![false, false, true]
  | 2 => ![false, true, false]
  | 3 => ![false, true, true]
  | _ => ![true, false, false]

/-- Encode a complex orbit coordinate by its real and imaginary parts in the
repository’s doubled real Krein fiber. Unused depth-three cylinders are zero. -/
def apolloniusOrbitInDoubledCylinder
    (q : BrioschiRootCoordinateSpace) : BitWord 3 → DoubledSpace ℝ := by
  intro w
  exact match w bit0, w bit1, w bit2 with
  | false, false, false => to_doubled (Complex.re (q q0)) (Complex.im (q q0))
  | false, false, true => to_doubled (Complex.re (q q1)) (Complex.im (q q1))
  | false, true, false => to_doubled (Complex.re (q q2)) (Complex.im (q q2))
  | false, true, true => to_doubled (Complex.re (q q3)) (Complex.im (q q3))
  | true, false, false => to_doubled (Complex.re (q q4)) (Complex.im (q q4))
  | _, _, _ => 0

/-- The selected five-cylinder realification is an actual `ℝ`-linear map
from the complex orbit-coordinate carrier to the finite doubled-fiber
carrier. -/
def apolloniusOrbitRealification :
    BrioschiRootCoordinateSpace →ₗ[ℝ] BitWord 3 → DoubledSpace ℝ where
  toFun := apolloniusOrbitInDoubledCylinder
  map_add' q r := by
    funext w
    cases h0 : w bit0 <;> cases h1 : w bit1 <;> cases h2 : w bit2 <;>
      simp [apolloniusOrbitInDoubledCylinder, to_doubled, h0, h1, h2,
        Complex.add_re, Complex.add_im]
    all_goals rw [← WithLp.toLp_add]
    all_goals simp only [Prod.mk_add_mk]
  map_smul' c q := by
    funext w
    cases h0 : w bit0 <;> cases h1 : w bit1 <;> cases h2 : w bit2 <;>
      simp [apolloniusOrbitInDoubledCylinder, to_doubled, h0, h1, h2,
        Complex.mul_re, Complex.mul_im]
    all_goals rw [← WithLp.toLp_smul]
    all_goals simp only [Prod.smul_mk, smul_eq_mul]

@[simp]
theorem apolloniusOrbitRealification_apply (q : BrioschiRootCoordinateSpace)
    (w : BitWord 3) :
    apolloniusOrbitRealification q w = apolloniusOrbitInDoubledCylinder q w := rfl

/-- Recover a complex scalar from the two real components of a doubled fiber.
This uses the underlying `WithLp` pair of `DoubledSpace ℝ`, not its Krein
pairing. -/
def doubledCylinderComplexReadout (x : DoubledSpace ℝ) : ℂ :=
  let p := WithLp.ofLp x
  ⟨p.1, p.2⟩

/-- The five selected doubled fibers read back the original complex orbit
coordinates exactly. -/
theorem doubledCylinderComplexReadout_orbit (q : BrioschiRootCoordinateSpace)
    (k : Fin 5) :
    doubledCylinderComplexReadout
      (apolloniusOrbitInDoubledCylinder q (quinticCylinderAddress k)) = q k := by
  fin_cases k <;>
    simp [doubledCylinderComplexReadout, quinticCylinderAddress,
      apolloniusOrbitInDoubledCylinder, bit0, bit1, bit2,
      q0, q1, q2, q3, q4, to_doubled]

/-- Decode the five selected complex diagonal entries of the matrix-stage
orbit embedding and realize them as doubled real fibers. This is a map on the
stage carrier whose relevant behavior is certified on the five-coordinate
orbit subspace; it discards all other matrix entries. -/
def complexCylinderDiagonalRealification
    (M : DoubleCylinderStage ℂ 3) : BitWord 3 → DoubledSpace ℝ :=
  apolloniusOrbitInDoubledCylinder
    (fun i => M (orbitCylinderAddress i) (orbitCylinderAddress i))

/-- The complex matrix-unit embedding and the doubled real-fiber embedding
are the same five-coordinate representation after diagonal realification.
This identifies the two finite-stage carriers on the actual orbit subspace. -/
theorem complexCylinderDiagonalRealification_orbit (q : BrioschiRootCoordinateSpace) :
    complexCylinderDiagonalRealification (orbitCoordinatesToCylinderStage q) =
      apolloniusOrbitInDoubledCylinder q := by
  unfold complexCylinderDiagonalRealification
  congr 1
  funext i
  have hdiag :
      (orbitCoordinatesToCylinderStage q)
        (orbitCylinderAddress i) (orbitCylinderAddress i) = q i := by
    classical
    change (∑ j : Fin 5, q j •
      doubleCylinderUnit ℂ 3 (orbitCylinderAddress j) (orbitCylinderAddress j)
        (orbitCylinderAddress i) (orbitCylinderAddress i)) = q i
    rw [Finset.sum_eq_single i]
    · simp [doubleCylinderUnit]
    · intro j hj hji
      have haddr : orbitCylinderAddress j ≠ orbitCylinderAddress i := by
        intro heq
        exact hji (orbitCylinderAddress_injective heq)
      simp [doubleCylinderUnit, haddr]
    · simp
  exact hdiag

/-- Read the five selected diagonal coefficients from a complex Cantor
matrix stage. This is a real-linear map; off-diagonal entries and the three
unused diagonal addresses are discarded. -/
def cylinderStageDiagonalReadout :
    DoubleCylinderStage ℂ 3 →ₗ[ℝ] BrioschiRootCoordinateSpace where
  toFun M := fun i => M (orbitCylinderAddress i) (orbitCylinderAddress i)
  map_add' M N := by
    funext i
    rfl
  map_smul' c M := by
    funext i
    simp

/-- The whole-stage realification is the composition of the diagonal
readout with the real-linear orbit-to-doubled-fiber map. -/
def complexCylinderDiagonalRealificationLinear :
    DoubleCylinderStage ℂ 3 →ₗ[ℝ] BitWord 3 → DoubledSpace ℝ :=
  apolloniusOrbitRealification.comp cylinderStageDiagonalReadout

@[simp]
theorem complexCylinderDiagonalRealificationLinear_apply
    (M : DoubleCylinderStage ℂ 3) :
    complexCylinderDiagonalRealificationLinear M =
      complexCylinderDiagonalRealification M := rfl

/-- The polynomial read directly from the five doubled Cantor-cylinder
fibers, after squaring to remove the order-ten sign, is the existing
binary-quintic evaluation resolvent. -/
def doubledCylinderEvaluationResolvent (q : BrioschiRootCoordinateSpace) :
    Polynomial ℂ :=
  ∏ k : Fin 5, (Polynomial.X - Polynomial.C
    ((doubledCylinderComplexReadout
      (apolloniusOrbitInDoubledCylinder q (quinticCylinderAddress k))) ^ 2))

/-- **Doubled-cylinder representation-to-resolvent identity.** The resolvent
read from the finite Cantor-cylinder realization is exactly the Brioschi
owner's squared five-coordinate evaluation resolvent. -/
theorem doubledCylinderEvaluationResolvent_eq_binaryQuinticEvaluationResolvent
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) :
    doubledCylinderEvaluationResolvent (binaryQuinticOrbitEvaluation z v) =
      binaryQuinticEvaluationResolvent v z := by
  unfold doubledCylinderEvaluationResolvent binaryQuinticEvaluationResolvent
    binaryQuinticResolventTuple
  congr 1
  funext k
  rw [doubledCylinderComplexReadout_orbit]
  rfl

/-- **Ordered roots to the finite doubled-cylinder resolvent.** Starting
from five ordered complex roots, form their source-ordered binary quintic by
Vieta, evaluate its signed orbit on the Klein five-cycle, and place those
coordinates in the five selected depth-three Cantor fibers. The resulting
resolvent is the product of the squared homogeneous root evaluations at
those orbit points. No affine-chart nonvanishing assumption is needed. -/
theorem rootTupleVieta_doubledCylinderResolvent
    (x : Fin 5 → ℂ) (z : ℂ × ℂ) :
    doubledCylinderEvaluationResolvent
        (binaryQuinticOrbitEvaluation z (rootTupleBinaryQuintic x)) =
      ∏ k : Fin 5, (Polynomial.X - Polynomial.C
        ((∏ i : Fin 5,
          ((kleinOrderFiveIterate k.val z).2 -
            x i * (kleinOrderFiveIterate k.val z).1)) ^ 2)) := by
  rw [doubledCylinderEvaluationResolvent_eq_binaryQuinticEvaluationResolvent]
  exact rootTupleVietaEvaluationResolvent_eq_homogeneous_root_orbit x z

/-- Apollonius specialization: the cylinder-readout polynomial for the
source-ordered coefficient vector at the Apollonius binary-form point equals
the owner-defined Apollonius evaluation resolvent. -/
theorem apolloniusDoubledCylinderResolvent_eq_evaluationResolvent
    (ξ θ : ℝ) (v : BinaryQuinticCoefficientSpace) :
    doubledCylinderEvaluationResolvent
        (binaryQuinticOrbitEvaluation
          (apolloniusBinaryQuinticPoint ξ θ) v) =
      binaryQuinticEvaluationResolvent v
        (apolloniusBinaryQuinticPoint ξ θ) := by
  exact doubledCylinderEvaluationResolvent_eq_binaryQuinticEvaluationResolvent
    v (apolloniusBinaryQuinticPoint ξ θ)

/-- **Apollonius-to-Cantor realization of the Brioschi resolvent.** There
are Apollonius coordinates and a source-ordered binary quintic whose signed
five-orbit coordinates occupy the five selected doubled Cantor cylinders,
and the polynomial read from those fibers is exactly the Brioschi
resolvent. The coefficient vector remains the noncanonical interpolation
witness supplied by the Apollonius/Brioschi owner. -/
theorem exists_apollonius_doubledCylinder_brioschiResolvent :
    ∃ ξ θ : ℝ, ∃ v : BinaryQuinticCoefficientSpace,
      doubledCylinderEvaluationResolvent
          (binaryQuinticOrbitEvaluation (apolloniusBinaryQuinticPoint ξ θ) v) =
        brioschiResolvent (brioschiParameter
          (apolloniusBinaryQuinticPoint ξ θ).1
          (apolloniusBinaryQuinticPoint ξ θ).2) := by
  obtain ⟨ξ, θ, v, hres⟩ :=
    exists_apollonius_binary_quintic_with_brioschi_evaluation_resolvent
  exact ⟨ξ, θ, v, (apolloniusDoubledCylinderResolvent_eq_evaluationResolvent
    ξ θ v).trans hres⟩

/-- The realification into the five selected doubled cylinder fibers is
injective, so the orbit module is represented as an actual subspace of the
stage-three coordinate carrier. -/
theorem apolloniusOrbitInDoubledCylinder_injective :
    Function.Injective apolloniusOrbitInDoubledCylinder := by
  intro q r h
  have hcoord : ∀ k : Fin 5, ((q k).re, (q k).im) = ((r k).re, (r k).im) := by
    intro k
    have hval := congrFun h (quinticCylinderAddress k)
    have hpair := congrArg WithLp.ofLp hval
    fin_cases k <;>
      simpa [quinticCylinderAddress, apolloniusOrbitInDoubledCylinder,
        bit0, bit1, bit2, q0, q1, q2, q3, q4, to_doubled] using hpair
  funext k
  apply Complex.ext
  · exact congrArg Prod.fst (hcoord k)
  · exact congrArg Prod.snd (hcoord k)

/-- Successor permutation on the five selected depth-three addresses,
extended by fixing the other three addresses. -/
def signedCylinderSuccessor (w : BitWord 3) : BitWord 3 :=
  match w bit0, w bit1, w bit2 with
  | false, false, false => ![false, false, true]
  | false, false, true => ![false, true, false]
  | false, true, false => ![false, true, true]
  | false, true, true => ![true, false, false]
  | true, false, false => ![false, false, false]
  | _, _, _ => w

/-- Sign character for the extended cylinder permutation: the five orbit
addresses carry the odd-degree spinor sign, while the three unused addresses
are fixed with positive sign. -/
def signedCylinderSign (w : BitWord 3) : ℝ :=
  if signedCylinderSuccessor w = w then 1 else -1

/-- Signed cyclic shift on the five selected cylinders, extended by the
identity on the three remaining depth-three cylinders. -/
def doubledCylinderSignedShift
    (x : BitWord 3 → DoubledSpace ℝ) : BitWord 3 → DoubledSpace ℝ :=
  fun w => signedCylinderSign w • x (signedCylinderSuccessor w)

/-- The corresponding signed permutation matrix in the repository-owned
stage-three double-cylinder algebra. Its rows and columns are indexed by
actual `BitWord 3` addresses. -/
def signedCylinderStageMatrix : DoubleCylinderStage ℝ 3 :=
  fun w v =>
    if v = signedCylinderSuccessor w then signedCylinderSign w else 0

/-- Action of a stage matrix on doubled real cylinder fibers, using the
ordinary finite matrix-module action. -/
def doubledCylinderStageAction (M : DoubleCylinderStage ℝ 3)
    (x : BitWord 3 → DoubledSpace ℝ) : BitWord 3 → DoubledSpace ℝ :=
  fun w => ∑ v : BitWord 3, M w v • x v

private def doubledFiberAtom : DoubledSpace ℝ →ₗ[ℝ] H_lp ℝ :=
  lp.lsingle (E := fun _ : BinaryCantorBoundary => DoubledSpace ℝ)
    (2 : ENNReal) basePlusWord

/-- Embed a finite doubled fiber-coordinate vector into the owner Hilbert
carrier by placing each fiber on the cylinder word above the common base
atom. The `wordCLM` maps put these atoms in disjoint cylinder positions. -/
def doubledCylinderCoordinatesToHlp (n : ℕ)
    (x : BitWord n → DoubledSpace ℝ) : H_lp ℝ :=
  ∑ w : BitWord n,
    wordCLM n w (doubledFiberAtom (x w))

/-- The finite doubled-coordinate map is injective: applying the word
pullback recovers each fiber atom, and evaluating that atom at the selected
base boundary recovers the original doubled vector. -/
theorem doubledCylinderCoordinatesToHlp_injective (n : ℕ) :
    Function.Injective (doubledCylinderCoordinatesToHlp n) := by
  intro x y hxy
  funext w
  have hrecover (z : BitWord n → DoubledSpace ℝ) :
      wordPullbackCLM n w (doubledCylinderCoordinatesToHlp n z) =
        doubledFiberAtom (z w) := by
    calc
      wordPullbackCLM n w (doubledCylinderCoordinatesToHlp n z) =
          ∑ i : BitWord n, if w = i then doubledFiberAtom (z i) else 0 := by
        simp only [doubledCylinderCoordinatesToHlp, map_sum,
          ← ContinuousLinearMap.comp_apply, wordPullbackCLM_comp_wordCLM]
        apply Finset.sum_congr rfl
        intro i hi
        split_ifs <;> simp
      _ = doubledFiberAtom (z w) := by
        rw [Finset.sum_eq_single w]
        · simp
        · intro i hi hiw
          simp [Ne.symm hiw]
        · simp
  have hpull := congrArg (wordPullbackCLM n w) hxy
  rw [hrecover x, hrecover y] at hpull
  have hvalue := congrArg (fun f : H_lp ℝ => f basePlusWord) hpull
  simpa [doubledFiberAtom, lp.single_apply] using hvalue

/-- The existing Cuntz cylinder operator representation restricts to the
finite cylinder-coordinate embedding as ordinary matrix action. This is the
link from the finite doubled fibers to `stageRepresentationCLM` on the actual
owner `H_lp ℝ` carrier. -/
theorem stageRepresentationCLM_doubledCylinderCoordinates
    (n : ℕ) (M : DoubleCylinderStage ℝ n)
    (x : BitWord n → DoubledSpace ℝ) :
    stageRepresentationCLM n M (doubledCylinderCoordinatesToHlp n x) =
      doubledCylinderCoordinatesToHlp n (fun u =>
        ∑ v : BitWord n, M u v • x v) := by
  have hpull (v w : BitWord n) (z : H_lp ℝ) :
      wordPullbackCLM n v (wordCLM n w z) = if v = w then z else 0 := by
    rw [← ContinuousLinearMap.comp_apply,
      wordPullbackCLM_comp_wordCLM]
    split_ifs <;> simp
  have hcollapse (u v : BitWord n) :
      (∑ w : BitWord n,
        wordCLM n u (if v = w then doubledFiberAtom (x w) else 0)) =
        wordCLM n u (doubledFiberAtom (x v)) := by
    rw [← map_sum]
    congr 1
    rw [Finset.sum_eq_single v]
    · simp
    · intro w hw hwv
      simp [Ne.symm hwv]
    · intro hv
      exact (hv (Finset.mem_univ v)).elim
  simp only [stageRepresentationCLM, doubledCylinderCoordinatesToHlp,
    sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, bitWordUnitCLM]
  simp_rw [map_sum, hpull]
  simp_rw [hcollapse]
  simp only [map_smul]

/-- The signed stage matrix acts on the doubled cylinder-coordinate module by
the specified signed address permutation. -/
theorem signedCylinderStageMatrix_action
    (x : BitWord 3 → DoubledSpace ℝ) :
    doubledCylinderStageAction signedCylinderStageMatrix x =
      doubledCylinderSignedShift x := by
  funext w
  unfold doubledCylinderStageAction signedCylinderStageMatrix
  rw [Finset.sum_eq_single (signedCylinderSuccessor w)]
  · simp [doubledCylinderSignedShift]
  · intro v hv hne
    simp [hne]
  · simp

/-- The quintic orbit evaluation embeds into the doubled stage-three cylinder
carrier and intertwines the binary quintic signed five-cycle with the
depth-three cylinder shift. The statement is at the finite-stage coordinate
carrier used by `DoubleCylinderStage ℝ 3`; no colimit or completed-operator
claim is implicit. -/
theorem signedOrbit_embeds_and_intertwines
    (q : BrioschiRootCoordinateSpace) :
    doubledCylinderSignedShift (apolloniusOrbitInDoubledCylinder q) =
      apolloniusOrbitInDoubledCylinder (binaryQuinticSignedCycle q) := by
  funext w
  cases h0 : w bit0 <;> cases h1 : w bit1 <;> cases h2 : w bit2
  all_goals
    have hw := word_eq_of_bits w _ _ _ h0 h1 h2
    rw [hw]
    simp [doubledCylinderSignedShift, signedCylinderSign, signedCylinderSuccessor,
      apolloniusOrbitInDoubledCylinder,
      binaryQuinticSignedCycle, kleinResolventCycleSucc, bit0, bit1, bit2,
      q0, q1, q2, q3, q4, to_doubled]
    all_goals
      rw [← WithLp.toLp_neg]
      apply congrArg (WithLp.toLp (2 : ENNReal))
      ext <;> simp

/-- The stage-three double-cylinder matrix itself realizes the signed orbit
action on the embedded five-coordinate subspace of doubled fibers. -/
theorem signedOrbit_stageMatrix_intertwines
    (q : BrioschiRootCoordinateSpace) :
    doubledCylinderStageAction signedCylinderStageMatrix
        (apolloniusOrbitInDoubledCylinder q) =
      apolloniusOrbitInDoubledCylinder (binaryQuinticSignedCycle q) := by
  rw [signedCylinderStageMatrix_action]
  exact signedOrbit_embeds_and_intertwines q

/-- The complex matrix-stage action and the doubled real-fiber action agree
on the orbit subspace after diagonal decoding. Thus the two finite-stage
realizations carry exactly the same signed five-cycle. -/
theorem complexCylinderDiagonalRealification_intertwines
    (q : BrioschiRootCoordinateSpace) :
    complexCylinderDiagonalRealification
        (signedCylinderStageAction (orbitCoordinatesToCylinderStage q)) =
      doubledCylinderStageAction signedCylinderStageMatrix
        (apolloniusOrbitInDoubledCylinder q) := by
  rw [signedCylinderStageAction_orbitCoordinates,
    complexCylinderDiagonalRealification_orbit]
  exact (signedOrbit_stageMatrix_intertwines q).symm

/-- The Apollonius coefficient-quotient representation composed with its
five-node evaluation equivalence and the doubled-cylinder embedding. -/
def apolloniusQuotientToDoubledCylinder (ξ θ : ℝ)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker
        (binaryQuinticOrbitEvaluation (apolloniusBinaryQuinticPoint ξ θ))) :
    BitWord 3 → DoubledSpace ℝ :=
  apolloniusOrbitInDoubledCylinder
    (binaryQuinticAffineOrbitQuotientEquiv
      (apollonius_parameter_ne_zero ξ θ) q)

/-- **Coefficient quotient → Apollonius orbit module → doubled Cantor
cylinder representation.** The quotient generator induced by the source
binary-quintic generator is carried to the signed depth-three cylinder
matrix action. This is a finite-stage intertwining on actual `DoubledSpace ℝ`
fibers; it does not assert a new identification with `stageRepresentationCLM`
on `H_lp ℝ`. -/
theorem apolloniusQuotientToDoubledCylinder_intertwines
    (ξ θ : ℝ)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker
        (binaryQuinticOrbitEvaluation (apolloniusBinaryQuinticPoint ξ θ))) :
    doubledCylinderStageAction signedCylinderStageMatrix
        (apolloniusQuotientToDoubledCylinder ξ θ q) =
      apolloniusQuotientToDoubledCylinder ξ θ
        (binaryQuinticOrbitQuotientGenerator
          (apolloniusBinaryQuinticPoint ξ θ) q) := by
  unfold apolloniusQuotientToDoubledCylinder
  rw [signedCylinderStageMatrix_action]
  rw [signedOrbit_embeds_and_intertwines]
  exact congrArg apolloniusOrbitInDoubledCylinder
    (binaryQuinticAffineOrbitQuotientEquiv_intertwines
      (apollonius_parameter_ne_zero ξ θ) q).symm

/-- The same composed representation theorem on an actual source-ordered
binary-quintic coefficient vector, before passing to its quotient class. -/
theorem apolloniusCoefficientVectorToDoubledCylinder_intertwines
    (ξ θ : ℝ) (v : BinaryQuinticCoefficientSpace) :
    doubledCylinderStageAction signedCylinderStageMatrix
        (apolloniusOrbitInDoubledCylinder
          (binaryQuinticOrbitEvaluation
            (apolloniusBinaryQuinticPoint ξ θ) v)) =
      apolloniusOrbitInDoubledCylinder
        (binaryQuinticOrbitEvaluation
          (apolloniusBinaryQuinticPoint ξ θ)
          (binaryQuinticGenerator v)) := by
  rw [binaryQuinticOrbitEvaluation_intertwines]
  exact signedOrbit_stageMatrix_intertwines
    (binaryQuinticOrbitEvaluation
      (apolloniusBinaryQuinticPoint ξ θ) v)

/-- The source-ordered binary-quintic signed generator is represented by the
owner's stage-three Cuntz cylinder operator on the embedded `H_lp ℝ`
coordinates, after evaluation at the Apollonius point. -/
theorem apolloniusCoefficientVectorToHlp_intertwines
    (ξ θ : ℝ) (v : BinaryQuinticCoefficientSpace) :
    stageRepresentationCLM 3 signedCylinderStageMatrix
        (doubledCylinderCoordinatesToHlp 3
          (apolloniusOrbitInDoubledCylinder
            (binaryQuinticOrbitEvaluation
              (apolloniusBinaryQuinticPoint ξ θ) v))) =
      doubledCylinderCoordinatesToHlp 3
        (apolloniusOrbitInDoubledCylinder
          (binaryQuinticOrbitEvaluation
            (apolloniusBinaryQuinticPoint ξ θ)
            (binaryQuinticGenerator v))) := by
  rw [stageRepresentationCLM_doubledCylinderCoordinates]
  apply congrArg (doubledCylinderCoordinatesToHlp 3)
  change doubledCylinderStageAction signedCylinderStageMatrix
      (apolloniusOrbitInDoubledCylinder
        (binaryQuinticOrbitEvaluation
          (apolloniusBinaryQuinticPoint ξ θ) v)) = _
  exact apolloniusCoefficientVectorToDoubledCylinder_intertwines ξ θ v

/-- The same owner-operator intertwining for the actual Apollonius
coefficient-quotient representation, where the source generator is induced
on the orbit-evaluation quotient. -/
theorem apolloniusQuotientToHlp_intertwines
    (ξ θ : ℝ)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker
        (binaryQuinticOrbitEvaluation (apolloniusBinaryQuinticPoint ξ θ))) :
    stageRepresentationCLM 3 signedCylinderStageMatrix
        (doubledCylinderCoordinatesToHlp 3
          (apolloniusQuotientToDoubledCylinder ξ θ q)) =
      doubledCylinderCoordinatesToHlp 3
        (apolloniusQuotientToDoubledCylinder ξ θ
          (binaryQuinticOrbitQuotientGenerator
            (apolloniusBinaryQuinticPoint ξ θ) q)) := by
  rw [stageRepresentationCLM_doubledCylinderCoordinates]
  apply congrArg (doubledCylinderCoordinatesToHlp 3)
  change doubledCylinderStageAction signedCylinderStageMatrix
      (apolloniusQuotientToDoubledCylinder ξ θ q) = _
  exact apolloniusQuotientToDoubledCylinder_intertwines ξ θ q

end InfoGeometry.Erlangen.KleinQuinticDoubledCylinderRepresentation
