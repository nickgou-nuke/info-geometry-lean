/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Erlangen.KleinQuinticOrderTenAction
import InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent
import InfoGeometry.Categorical.CantorDoubleCylinderColimitAlgebra
import InfoGeometry.Canonical.ChiralApollonianCylinderBridge
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Quintic Orbit Coordinates, Doubled Cantor Cylinders, and the Soddy Carrier

This file makes two carrier-level facts explicit. The signed five-coordinate
orbit representation embeds into the depth-three double-cylinder matrix stage
and hence into its colimit. By contrast, the Apollonian owner has four
curvature coordinates; there is no injective complex-linear map from the
five-coordinate orbit carrier into that carrier. The latter obstruction does
not identify the Soddy reflections with the order-ten quintic action.
-/

noncomputable section

namespace InfoGeometry.Erlangen.KleinQuinticCantorApollonianBridge

open InfoGeometry.Erlangen.KleinQuinticOrderTenAction
open InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent
open InfoGeometry.OperatorAlgebra.CantorDoubleCylinderFractalColimit
open InfoGeometry.Categorical.CantorDoubleCylinderColimitAlgebra
open InfoGeometry.Canonical.ChiralApollonian
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-- Five distinct binary addresses at depth three. -/
def orbitCylinderAddress (i : Fin 5) : BitWord 3 :=
  match i.val with
  | 0 => fun _ => false
  | 1 => fun j => j.val = 2
  | 2 => fun j => j.val = 1
  | 3 => fun j => j.val = 1 ∨ j.val = 2
  | _ => fun j => j.val = 0

theorem orbitCylinderAddress_injective :
    Function.Injective orbitCylinderAddress := by
  decide

/-- Put the five orbit coordinates on five diagonal depth-three double
cylinders. This is a linear map into the actual Cantor matrix stage. -/
def orbitCoordinatesToCylinderStage :
    BrioschiRootCoordinateSpace →ₗ[ℂ] DoubleCylinderStage ℂ 3 where
  toFun q := ∑ i : Fin 5,
    q i • doubleCylinderUnit ℂ 3 (orbitCylinderAddress i) (orbitCylinderAddress i)
  map_add' q r := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c q := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]
    simp only [RingHom.id_apply]

/-- The five-cylinder coordinate map is injective, since its five diagonal
matrix units have distinct addresses. -/
theorem orbitCoordinatesToCylinderStage_injective :
    Function.Injective orbitCoordinatesToCylinderStage := by
  intro q r h
  funext i
  have hij := congrFun (congrFun h (orbitCylinderAddress i))
    (orbitCylinderAddress i)
  have hdiag (x : BrioschiRootCoordinateSpace) :
      (orbitCoordinatesToCylinderStage x)
          (orbitCylinderAddress i) (orbitCylinderAddress i) = x i := by
    classical
    change (∑ j : Fin 5, x j •
      doubleCylinderUnit ℂ 3 (orbitCylinderAddress j) (orbitCylinderAddress j)
        (orbitCylinderAddress i) (orbitCylinderAddress i)) = x i
    rw [Finset.sum_eq_single i]
    · simp [doubleCylinderUnit]
    · intro j hj hji
      have haddr : orbitCylinderAddress j ≠ orbitCylinderAddress i := by
        intro heq
        exact hji (orbitCylinderAddress_injective heq)
      simp [doubleCylinderUnit, haddr]
    · simp
  rw [hdiag q, hdiag r] at hij
  exact hij

/-- Compress a general stage matrix to the five selected diagonal cylinder
coefficients, apply the signed successor action, then re-embed. This is a
linear operator on the matrix stage; it is not asserted to be an algebra
automorphism of the full Cantor stage. -/
def signedCylinderStageAction (M : DoubleCylinderStage ℂ 3) :
    DoubleCylinderStage ℂ 3 :=
  ∑ i : Fin 5,
    (-(M (orbitCylinderAddress (kleinResolventCycleSucc i))
        (orbitCylinderAddress (kleinResolventCycleSucc i)))) •
      doubleCylinderUnit ℂ 3 (orbitCylinderAddress i) (orbitCylinderAddress i)

/-- The signed cylinder-stage action restricts exactly to the signed
five-coordinate representation. -/
theorem signedCylinderStageAction_orbitCoordinates
    (q : BrioschiRootCoordinateSpace) :
    signedCylinderStageAction (orbitCoordinatesToCylinderStage q) =
      orbitCoordinatesToCylinderStage (binaryQuinticSignedCycle q) := by
  classical
  change (∑ i : Fin 5,
      -(orbitCoordinatesToCylinderStage q)
          (orbitCylinderAddress (kleinResolventCycleSucc i))
          (orbitCylinderAddress (kleinResolventCycleSucc i)) •
        doubleCylinderUnit ℂ 3 (orbitCylinderAddress i) (orbitCylinderAddress i)) =
    ∑ i : Fin 5, (binaryQuinticSignedCycle q i) •
      doubleCylinderUnit ℂ 3 (orbitCylinderAddress i) (orbitCylinderAddress i)
  apply Finset.sum_congr rfl
  intro i hi
  have hdiag :
      (orbitCoordinatesToCylinderStage q)
          (orbitCylinderAddress (kleinResolventCycleSucc i))
          (orbitCylinderAddress (kleinResolventCycleSucc i)) =
      q (kleinResolventCycleSucc i) := by
    change (∑ j : Fin 5, q j •
      doubleCylinderUnit ℂ 3 (orbitCylinderAddress j) (orbitCylinderAddress j)
        (orbitCylinderAddress (kleinResolventCycleSucc i))
        (orbitCylinderAddress (kleinResolventCycleSucc i))) =
      q (kleinResolventCycleSucc i)
    rw [Finset.sum_eq_single (kleinResolventCycleSucc i)]
    · simp [doubleCylinderUnit]
    · intro j hj hji
      have haddr : orbitCylinderAddress j ≠
          orbitCylinderAddress (kleinResolventCycleSucc i) := by
        intro heq
        exact hji (orbitCylinderAddress_injective heq)
      simp [doubleCylinderUnit, haddr]
    · simp
  rw [hdiag]
  rfl

/-- Transport a binary quintic coefficient vector to the depth-three Cantor
stage by evaluating it on the existing Klein orbit, then using the five
selected cylinder addresses. This factors through the owner's actual orbit
evaluation map (and therefore has its evaluation kernel); it is not claimed
to be injective on all six-dimensional coefficient vectors. -/
def binaryQuinticCoefficientsToCylinderStage (z : ℂ × ℂ) :
    BinaryQuinticCoefficientSpace →ₗ[ℂ] DoubleCylinderStage ℂ 3 :=
  (orbitCoordinatesToCylinderStage).comp (binaryQuinticOrbitEvaluation z)

/-- The coefficient-to-cylinder map is equivariant for the actual order-ten
binary-quintic generator and the signed five-coordinate orbit action. -/
theorem binaryQuinticCoefficientsToCylinderStage_equivariant
    (z : ℂ × ℂ) (v : BinaryQuinticCoefficientSpace) :
    signedCylinderStageAction
        (binaryQuinticCoefficientsToCylinderStage z v) =
      binaryQuinticCoefficientsToCylinderStage z (binaryQuinticGenerator v) := by
  have heval : binaryQuinticOrbitEvaluation z (binaryQuinticGenerator v) =
      binaryQuinticSignedCycle (binaryQuinticOrbitEvaluation z v) := by
    funext k
    change binaryQuinticSignedOrbit (binaryQuinticGenerator v) z k =
      -(binaryQuinticOrbitEvaluation z v) (kleinResolventCycleSucc k)
    exact congrFun (binaryQuinticSignedOrbit_equivariant v z) k
  change signedCylinderStageAction
      (orbitCoordinatesToCylinderStage (binaryQuinticOrbitEvaluation z v)) =
    orbitCoordinatesToCylinderStage (binaryQuinticOrbitEvaluation z (binaryQuinticGenerator v))
  rw [signedCylinderStageAction_orbitCoordinates, heval]

/-- Every iterate of the restricted cylinder-stage action agrees with the
same iterate of the signed five-cycle. -/
theorem signedCylinderStageAction_iterate (n : ℕ)
    (q : BrioschiRootCoordinateSpace) :
    (signedCylinderStageAction^[n]) (orbitCoordinatesToCylinderStage q) =
      orbitCoordinatesToCylinderStage ((binaryQuinticSignedCycle^[n]) q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        (signedCylinderStageAction^[n + 1]) (orbitCoordinatesToCylinderStage q) =
            signedCylinderStageAction
              ((signedCylinderStageAction^[n]) (orbitCoordinatesToCylinderStage q)) := by
                rw [Function.iterate_succ_apply']
        _ = signedCylinderStageAction
              (orbitCoordinatesToCylinderStage ((binaryQuinticSignedCycle^[n]) q)) := by
                rw [ih]
        _ = orbitCoordinatesToCylinderStage
              (binaryQuinticSignedCycle ((binaryQuinticSignedCycle^[n]) q)) :=
                signedCylinderStageAction_orbitCoordinates _
        _ = orbitCoordinatesToCylinderStage ((binaryQuinticSignedCycle^[n + 1]) q) := by
                change orbitCoordinatesToCylinderStage
                  (binaryQuinticSignedCycle ((binaryQuinticSignedCycle^[n]) q)) =
                  orbitCoordinatesToCylinderStage
                    ((binaryQuinticSignedCycle^[Nat.succ n]) q)
                rw [Function.iterate_succ_apply']

/-- The fifth iterate on the embedded cylinder subspace is central negation,
matching the spinor sign in the binary-quintic representation. -/
theorem signedCylinderStageAction_fifth (q : BrioschiRootCoordinateSpace) :
    (signedCylinderStageAction^[5]) (orbitCoordinatesToCylinderStage q) =
      orbitCoordinatesToCylinderStage (-q) := by
  rw [signedCylinderStageAction_iterate]
  have h5 : (binaryQuinticSignedCycle^[5]) q =
      binaryQuinticSignedCycleFive q := by
    rfl
  rw [h5, binaryQuinticSignedCycle_fifth]

/-- The tenth iterate is the identity on the embedded signed orbit carrier. -/
theorem signedCylinderStageAction_tenth (q : BrioschiRootCoordinateSpace) :
    (signedCylinderStageAction^[10]) (orbitCoordinatesToCylinderStage q) =
      orbitCoordinatesToCylinderStage q := by
  rw [signedCylinderStageAction_iterate]
  have h10 : (binaryQuinticSignedCycle^[10]) q =
      binaryQuinticSignedCycleFive (binaryQuinticSignedCycleFive q) := by
    rfl
  rw [h10, binaryQuinticSignedCycle_tenth]

/-- The transported coefficient representation inherits the central
spinor sign and period ten on the image of the evaluation map. -/
theorem binaryQuinticCoefficientsToCylinderStage_fifth
    (z : ℂ × ℂ) (v : BinaryQuinticCoefficientSpace) :
    (signedCylinderStageAction^[5])
        (binaryQuinticCoefficientsToCylinderStage z v) =
      binaryQuinticCoefficientsToCylinderStage z (-v) := by
  change (signedCylinderStageAction^[5])
      (orbitCoordinatesToCylinderStage (binaryQuinticOrbitEvaluation z v)) =
    orbitCoordinatesToCylinderStage (binaryQuinticOrbitEvaluation z (-v))
  rw [signedCylinderStageAction_fifth,
    map_neg (binaryQuinticOrbitEvaluation z) v,
    map_neg orbitCoordinatesToCylinderStage]

/-- The tenth iterate is the identity on every coefficient image. -/
theorem binaryQuinticCoefficientsToCylinderStage_tenth
    (z : ℂ × ℂ) (v : BinaryQuinticCoefficientSpace) :
    (signedCylinderStageAction^[10])
        (binaryQuinticCoefficientsToCylinderStage z v) =
      binaryQuinticCoefficientsToCylinderStage z v := by
  change (signedCylinderStageAction^[10])
      (orbitCoordinatesToCylinderStage (binaryQuinticOrbitEvaluation z v)) =
    orbitCoordinatesToCylinderStage (binaryQuinticOrbitEvaluation z v)
  exact signedCylinderStageAction_tenth _

/-- The coordinate embedding persists as an injective map into the
categorical doubled-cylinder colimit. -/
theorem orbitCoordinatesToCantorColimit_injective :
    Function.Injective
      (fun q => colimitInclusion ℂ 3 (orbitCoordinatesToCylinderStage q)) := by
  intro q r h
  apply orbitCoordinatesToCylinderStage_injective
  exact colimitInclusion_injective ℂ 3 h

/-- The Apollonian carrier has four complex curvature coordinates, whereas
the signed orbit carrier has five. Consequently it cannot receive an
injective complex-linear representation map. This is an ambient carrier
obstruction, independent of which Soddy reflection is chosen. -/
theorem no_linear_embedding_orbit_coordinates_into_curvatures
    (f : BrioschiRootCoordinateSpace →ₗ[ℂ] (Fin 4 → ℂ)) :
    ¬ Function.Injective f := by
  intro hf
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  have hsource : Module.finrank ℂ BrioschiRootCoordinateSpace = 5 := by
    simp [BrioschiRootCoordinateSpace]
  have htarget : Module.finrank ℂ (Fin 4 → ℂ) = 4 := by
    simp
  rw [hsource, htarget] at hdim
  omega

/-- The four Soddy reflections preserve the Descartes quadric individually;
none of these facts supplies a five-cycle action on the five-coordinate
quintic orbit carrier. -/
theorem soddy_reflections_preserve_apollonian_data
    (q : CurvatureQuadruple ℂ) :
    descartesForm (soddyReflect1 q) = descartesForm q ∧
    descartesForm (soddyReflect2 q) = descartesForm q ∧
    descartesForm (soddyReflect3 q) = descartesForm q ∧
    descartesForm (soddyReflect4 q) = descartesForm q := by
  exact ⟨descartesForm_soddyReflect1 q, descartesForm_soddyReflect2 q,
    descartesForm_soddyReflect3 q, descartesForm_soddyReflect4 q⟩

/-- The one-dimensional sign-character quotient of the signed orbit module.
The cycle negates the coordinate sum because its underlying successor is a
permutation of the five indices. -/
def signedOrbitTotal (q : BrioschiRootCoordinateSpace) : ℂ :=
  ∑ i : Fin 5, q i

/-- The total-coordinate quotient as an actual linear functional. -/
def signedOrbitTotalMap : BrioschiRootCoordinateSpace →ₗ[ℂ] ℂ where
  toFun := signedOrbitTotal
  map_add' q r := by simp [signedOrbitTotal, Finset.sum_add_distrib]
  map_smul' c q := by
    simp [signedOrbitTotal, Finset.mul_sum]

theorem signedOrbitTotal_cycle (q : BrioschiRootCoordinateSpace) :
    signedOrbitTotal (binaryQuinticSignedCycle q) = -signedOrbitTotal q := by
  change (∑ i : Fin 5, -(q (kleinResolventCycleSucc i))) =
    -(∑ i : Fin 5, q i)
  simp [Fin.sum_univ_succ, kleinResolventCycleSucc]
  ring

/-- The `-1` eigenspace in the dual of the signed five-cycle is exactly the
line spanned by the total-coordinate functional. Thus the one-dimensional
Soddy eigenspace readout below is not just an example: every scalar linear
readout intertwining this source cycle with negation is a scalar multiple of
the sum of the five orbit coordinates. -/
theorem anticyclic_linear_functional_is_total
    (ℓ : BrioschiRootCoordinateSpace →ₗ[ℂ] ℂ)
    (hℓ : ∀ q, ℓ (binaryQuinticSignedCycle q) = -ℓ q) :
    ∀ q, ℓ q = ℓ (Pi.single 0 (1 : ℂ)) * ∑ i : Fin 5, q i := by
  let b (i : Fin 5) : BrioschiRootCoordinateSpace := Pi.single i 1
  have hstep (i : Fin 5) : ℓ (b i) = ℓ (b (kleinResolventCycleSucc i)) := by
    have hshift : binaryQuinticSignedCycle (b (kleinResolventCycleSucc i)) = -b i := by
      funext j
      fin_cases i <;> fin_cases j <;>
        norm_num [binaryQuinticSignedCycle, b, kleinResolventCycleSucc,
          Pi.single_apply]
    have h := hℓ (b (kleinResolventCycleSucc i))
    rw [hshift, map_neg] at h
    exact neg_injective h
  have h0 (i : Fin 5) : ℓ (b i) = ℓ (b 0) := by
    fin_cases i
    · rfl
    · exact (hstep 0).symm
    · exact ((hstep 0).trans (hstep 1)).symm
    · exact ((hstep 0).trans (hstep 1)).trans (hstep 2) |>.symm
    · exact (((hstep 0).trans (hstep 1)).trans (hstep 2)).trans (hstep 3) |>.symm
  intro q
  have hdecomp : q = ∑ i : Fin 5, q i • b i := by
    funext j
    simp [b, Pi.single_apply]
  calc
    ℓ q = ℓ (∑ i : Fin 5, q i • b i) := congrArg ℓ hdecomp
    _ = ∑ i : Fin 5, q i * ℓ (b i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [map_smul, smul_eq_mul]
    _ = ∑ i : Fin 5, q i * ℓ (Pi.single 0 (1 : ℂ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun c : ℂ => q i * c) (h0 i)
    _ = ℓ (Pi.single 0 (1 : ℂ)) * ∑ i : Fin 5, q i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Embed the sign-character quotient into the −-one eigendirection of the
fourth Soddy reflection. This is a genuine map to the existing curvature
carrier, but deliberately forgets four of the five orbit degrees of freedom. -/
def signedOrbitToSoddyFourthEigenspace
    (q : BrioschiRootCoordinateSpace) : CurvatureQuadruple ℂ :=
  ⟨0, 0, 0, signedOrbitTotal q⟩

/-- The total-coordinate quotient reaches every vector in the `-1`
eigenspace of the fourth Soddy reflection. Together with
`equivariant_map_lands_in_soddyFourth_minus_eigenspace`, this shows that its
one-dimensional image is the largest possible equivariant image for this
single-reflection target. -/
theorem signedOrbitToSoddyFourthEigenspace_range (x : CurvatureQuadruple ℂ) :
    (x.k1 = 0 ∧ x.k2 = 0 ∧ x.k3 = 0) ↔
      ∃ q : BrioschiRootCoordinateSpace,
        signedOrbitToSoddyFourthEigenspace q = x := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    let q : BrioschiRootCoordinateSpace := Pi.single (0 : Fin 5) x.k4
    have htotal : signedOrbitTotal q = x.k4 := by
      classical
      unfold signedOrbitTotal q
      rw [Finset.sum_eq_single (0 : Fin 5)]
      · simp
      · intro i hi hne
        simp [hne]
      · simp
    refine ⟨q, ?_⟩
    ext <;> simp [signedOrbitToSoddyFourthEigenspace, h1, h2, h3, htotal]
  · rintro ⟨q, rfl⟩
    exact ⟨rfl, rfl, rfl⟩

/-- Read the five selected Cantor cylinder diagonal coefficients as the
Soddy fourth-reflection sign-character coordinate. -/
def cylinderStageToSoddyFourthEigenspace
    (M : DoubleCylinderStage ℂ 3) : CurvatureQuadruple ℂ :=
  ⟨0, 0, 0, ∑ i : Fin 5,
    M (orbitCylinderAddress i) (orbitCylinderAddress i)⟩

/-- On the embedded orbit subspace, cylinder diagonal readout agrees exactly
with the sign-character quotient of the five-coordinate carrier. -/
theorem cylinderStageToSoddy_on_orbitCoordinates
    (q : BrioschiRootCoordinateSpace) :
    cylinderStageToSoddyFourthEigenspace (orbitCoordinatesToCylinderStage q) =
      signedOrbitToSoddyFourthEigenspace q := by
  have hdiag (i : Fin 5) :
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
  ext <;> simp [cylinderStageToSoddyFourthEigenspace,
    signedOrbitToSoddyFourthEigenspace]
  congr 1
  funext i
  exact hdiag i

/-- The scalar map records the eigenspace equation for the actual fourth
Soddy reflection. -/
theorem soddyFourth_on_signedOrbitEigenspace
    (q : BrioschiRootCoordinateSpace) :
    soddyReflect4 (signedOrbitToSoddyFourthEigenspace q) =
      signedOrbitToSoddyFourthEigenspace (binaryQuinticSignedCycle q) := by
  have htotal := signedOrbitTotal_cycle q
  ext <;> simp [signedOrbitToSoddyFourthEigenspace, soddyReflect4, htotal]

/-- Klein-style invariant comparison: the Descartes quadratic form pulled
back along the sign-character map is the square of the total-coordinate
character, hence is invariant under the signed quintic cycle. -/
theorem pulledBackDescartesForm_eq_square_and_cycle_invariant
    (q : BrioschiRootCoordinateSpace) :
    descartesForm (signedOrbitToSoddyFourthEigenspace q) =
      signedOrbitTotal q ^ 2 ∧
    descartesForm (signedOrbitToSoddyFourthEigenspace
      (binaryQuinticSignedCycle q)) =
      descartesForm (signedOrbitToSoddyFourthEigenspace q) := by
  constructor
  · dsimp [descartesForm, signedOrbitToSoddyFourthEigenspace]
    ring
  · rw [← soddyFourth_on_signedOrbitEigenspace,
      descartesForm_soddyReflect4]

/-- The same pulled-back Descartes invariant is preserved by the original
binary-quintic coefficient generator after evaluation on any Klein orbit. -/
theorem pulledBackDescartesForm_binaryQuinticGenerator_invariant
    (z : ℂ × ℂ) (v : BinaryQuinticCoefficientSpace) :
    descartesForm (signedOrbitToSoddyFourthEigenspace
      (binaryQuinticOrbitEvaluation z (binaryQuinticGenerator v))) =
      descartesForm (signedOrbitToSoddyFourthEigenspace
        (binaryQuinticOrbitEvaluation z v)) := by
  rw [binaryQuinticOrbitEvaluation_intertwines]
  exact (pulledBackDescartesForm_eq_square_and_cycle_invariant
    (binaryQuinticOrbitEvaluation z v)).2

/-- Direct binary-coefficient-to-Soddy intertwining. It factors through the
actual Klein orbit evaluation and then its one-dimensional sign character. -/
theorem binaryQuinticEvaluation_to_soddy_intertwines
    (z : ℂ × ℂ) (v : BinaryQuinticCoefficientSpace) :
    soddyReflect4 (signedOrbitToSoddyFourthEigenspace
      (binaryQuinticOrbitEvaluation z v)) =
      signedOrbitToSoddyFourthEigenspace
        (binaryQuinticOrbitEvaluation z (binaryQuinticGenerator v)) := by
  rw [binaryQuinticOrbitEvaluation_intertwines]
  exact soddyFourth_on_signedOrbitEigenspace _

/-- The complete finite-stage chain from binary-quintic coefficients through
Klein orbit evaluation and Cantor-cylinder coordinates to the Soddy action
commutes. This is the one-dimensional sign-character quotient; it does not
assert a five-dimensional faithful Soddy representation. -/
theorem binaryQuinticCylinderToSoddy_intertwines
    (z : ℂ × ℂ) (v : BinaryQuinticCoefficientSpace) :
    soddyReflect4 (cylinderStageToSoddyFourthEigenspace
      (binaryQuinticCoefficientsToCylinderStage z v)) =
      cylinderStageToSoddyFourthEigenspace
        (binaryQuinticCoefficientsToCylinderStage z (binaryQuinticGenerator v)) := by
  change soddyReflect4 (cylinderStageToSoddyFourthEigenspace
      (orbitCoordinatesToCylinderStage (binaryQuinticOrbitEvaluation z v))) =
    cylinderStageToSoddyFourthEigenspace
      (orbitCoordinatesToCylinderStage
        (binaryQuinticOrbitEvaluation z (binaryQuinticGenerator v)))
  rw [cylinderStageToSoddy_on_orbitCoordinates,
    cylinderStageToSoddy_on_orbitCoordinates]
  exact binaryQuinticEvaluation_to_soddy_intertwines z v

/-- The quotient is nonzero: the constant five-coordinate vector maps to
the nonzero eigendirection parameter `5`. -/
theorem signedOrbitToSoddyFourthEigenspace_nontrivial :
    signedOrbitToSoddyFourthEigenspace (fun _ : Fin 5 => (1 : ℂ)) ≠
      (⟨0, 0, 0, 0⟩ : CurvatureQuadruple ℂ) := by
  intro h
  have hlast := congrArg CurvatureQuadruple.k4 h
  norm_num [signedOrbitToSoddyFourthEigenspace, signedOrbitTotal,
    Fin.sum_univ_succ] at hlast

/-- The sign-character bridge does not preserve the Apollonian null quadric
except at zero: the Descartes form on this eigendirection is the square of
its parameter. Thus it bridges the Soddy *linear action*, not nonzero circle
packings or their integral positivity constraints. -/
theorem apollonian_null_on_soddyFourth_eigenspace_only_zero
    (q : BrioschiRootCoordinateSpace)
    (h : IsApollonian (signedOrbitToSoddyFourthEigenspace q)) :
    signedOrbitTotal q = 0 := by
  have h' : 2 * (signedOrbitTotal q) ^ 2 -
      (signedOrbitTotal q) ^ 2 = 0 := by
    simpa [IsApollonian, descartesForm, signedOrbitToSoddyFourthEigenspace] using h
  have hform : signedOrbitTotal q * signedOrbitTotal q = 0 := by
    linear_combination h'
  rcases mul_eq_zero.mp hform with hzero | hzero <;> exact hzero

/-- A complex-linear map to the curvature carrier is represented by four
complex-linear coordinate readouts. `CurvatureQuadruple` itself intentionally
has no vector-space instance in the Apollonian owner. -/
structure QuinticToCurvatureLinearMap where
  k1 : BrioschiRootCoordinateSpace →ₗ[ℂ] ℂ
  k2 : BrioschiRootCoordinateSpace →ₗ[ℂ] ℂ
  k3 : BrioschiRootCoordinateSpace →ₗ[ℂ] ℂ
  k4 : BrioschiRootCoordinateSpace →ₗ[ℂ] ℂ

/-- Evaluate the four coordinate readouts as an Apollonian curvature tuple. -/
def QuinticToCurvatureLinearMap.toCurvature (f : QuinticToCurvatureLinearMap)
    (q : BrioschiRootCoordinateSpace) : CurvatureQuadruple ℂ :=
  ⟨f.k1 q, f.k2 q, f.k3 q, f.k4 q⟩

/-- Any coordinate-linear intertwiner from the signed quintic five-cycle to a
single Soddy reflection has image in that reflection's `-1` eigenspace.
This follows from the source fifth power `-id` and the target reflection's
involutivity. -/
theorem equivariant_map_lands_in_soddyFourth_minus_eigenspace
    (f : QuinticToCurvatureLinearMap)
    (hintertwine : ∀ q,
      f.toCurvature (binaryQuinticSignedCycle q) =
        soddyReflect4 (f.toCurvature q))
    (q : BrioschiRootCoordinateSpace) :
    (f.toCurvature q).k1 = 0 ∧ (f.toCurvature q).k2 = 0 ∧
      (f.toCurvature q).k3 = 0 := by
  have hIter (n : ℕ) :
      f.toCurvature ((binaryQuinticSignedCycle^[n]) q) =
        (soddyReflect4^[n]) (f.toCurvature q) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [Function.iterate_succ_apply']
        rw [hintertwine, ih]
  have hcycle5 : (binaryQuinticSignedCycle^[5]) q = -q := by
    calc
      (binaryQuinticSignedCycle^[5]) q = binaryQuinticSignedCycleFive q := rfl
      _ = -q := binaryQuinticSignedCycle_fifth q
  have hSoddy5 (x : CurvatureQuadruple ℂ) :
      (soddyReflect4^[5]) x = soddyReflect4 x := by
    change soddyReflect4 (soddyReflect4 (soddyReflect4 (soddyReflect4
      (soddyReflect4 x)))) = soddyReflect4 x
    rw [soddyReflect4_involutive, soddyReflect4_involutive]
  have hNeg : f.toCurvature (-q) = soddyReflect4 (f.toCurvature q) := by
    calc
      f.toCurvature (-q) = f.toCurvature ((binaryQuinticSignedCycle^[5]) q) := by
        rw [hcycle5]
      _ = (soddyReflect4^[5]) (f.toCurvature q) := hIter 5
      _ = soddyReflect4 (f.toCurvature q) := hSoddy5 _
  have h1Eigen : (soddyReflect4 (f.toCurvature q)).k1 =
      -(f.toCurvature q).k1 := by
    calc
      (soddyReflect4 (f.toCurvature q)).k1 = (f.toCurvature (-q)).k1 := by
        rw [← hNeg]
      _ = f.k1 (-q) := rfl
      _ = -f.k1 q := map_neg f.k1 q
      _ = -(f.toCurvature q).k1 := rfl
  have h2Eigen : (soddyReflect4 (f.toCurvature q)).k2 =
      -(f.toCurvature q).k2 := by
    calc
      (soddyReflect4 (f.toCurvature q)).k2 = (f.toCurvature (-q)).k2 := by
        rw [← hNeg]
      _ = f.k2 (-q) := rfl
      _ = -f.k2 q := map_neg f.k2 q
      _ = -(f.toCurvature q).k2 := rfl
  have h3Eigen : (soddyReflect4 (f.toCurvature q)).k3 =
      -(f.toCurvature q).k3 := by
    calc
      (soddyReflect4 (f.toCurvature q)).k3 = (f.toCurvature (-q)).k3 := by
        rw [← hNeg]
      _ = f.k3 (-q) := rfl
      _ = -f.k3 q := map_neg f.k3 q
      _ = -(f.toCurvature q).k3 := rfl
  constructor
  · dsimp [soddyReflect4] at h1Eigen
    have hdouble : (2 : ℂ) * (f.toCurvature q).k1 = 0 := by
      linear_combination h1Eigen
    exact (mul_eq_zero.mp hdouble).resolve_left (by norm_num)
  constructor
  · dsimp [soddyReflect4] at h2Eigen
    have hdouble : (2 : ℂ) * (f.toCurvature q).k2 = 0 := by
      linear_combination h2Eigen
    exact (mul_eq_zero.mp hdouble).resolve_left (by norm_num)
  · dsimp [soddyReflect4] at h3Eigen
    have hdouble : (2 : ℂ) * (f.toCurvature q).k3 = 0 := by
      linear_combination h3Eigen
    exact (mul_eq_zero.mp hdouble).resolve_left (by norm_num)

/-- Exact classification of linear intertwiners from the signed five-cycle
to a single fourth Soddy reflection: the first three curvature coordinates
vanish, and the remaining coordinate is a scalar multiple of the total
orbit-coordinate character. Thus the sign-character quotient above accounts
for every possible linear intertwiner to this target action. -/
theorem equivariant_map_fourth_coordinate_is_total
    (f : QuinticToCurvatureLinearMap)
    (hintertwine : ∀ q,
      f.toCurvature (binaryQuinticSignedCycle q) =
        soddyReflect4 (f.toCurvature q)) :
    ∀ q, f.k4 q = f.k4 (Pi.single 0 (1 : ℂ)) * ∑ i : Fin 5, q i := by
  have hanti (q : BrioschiRootCoordinateSpace) :
      f.k4 (binaryQuinticSignedCycle q) = -f.k4 q := by
    have heigen := congrArg CurvatureQuadruple.k4 (hintertwine q)
    obtain ⟨h1, h2, h3⟩ :=
      equivariant_map_lands_in_soddyFourth_minus_eigenspace f hintertwine q
    dsimp [QuinticToCurvatureLinearMap.toCurvature, soddyReflect4] at heigen
    change f.k1 q = 0 at h1
    change f.k2 q = 0 at h2
    change f.k3 q = 0 at h3
    rw [h1, h2, h3] at heigen
    simpa using heigen
  exact anticyclic_linear_functional_is_total f.k4 hanti

/-- No nonzero Descartes-null vector can be in the image of an intertwiner
from the signed quintic five-cycle to one Soddy reflection. Thus the
one-dimensional sign-character map above intertwines the linear actions,
but no such map can send a quintic orbit to a nonzero Apollonian curvature
quadruple. -/
theorem equivariant_apollonian_image_is_zero
    (f : QuinticToCurvatureLinearMap)
    (hintertwine : ∀ q,
      f.toCurvature (binaryQuinticSignedCycle q) =
        soddyReflect4 (f.toCurvature q))
    (q : BrioschiRootCoordinateSpace)
    (hApollonian : IsApollonian (f.toCurvature q)) :
    f.toCurvature q = ⟨0, 0, 0, 0⟩ := by
  obtain ⟨h1, h2, h3⟩ :=
    equivariant_map_lands_in_soddyFourth_minus_eigenspace f hintertwine q
  have h4sq : (f.toCurvature q).k4 ^ 2 = 0 := by
    change f.k4 q ^ 2 = 0
    have hform := hApollonian
    simp only [IsApollonian, descartesForm,
      QuinticToCurvatureLinearMap.toCurvature] at hform
    change f.k1 q = 0 at h1
    change f.k2 q = 0 at h2
    change f.k3 q = 0 at h3
    rw [h1, h2, h3] at hform
    linear_combination hform
  have h4 : (f.toCurvature q).k4 = 0 :=
    mul_self_eq_zero.mp (by simpa [pow_two] using h4sq)
  ext <;> simp only [QuinticToCurvatureLinearMap.toCurvature]
  · exact h1
  · exact h2
  · exact h3
  · exact h4

end InfoGeometry.Erlangen.KleinQuinticCantorApollonianBridge
