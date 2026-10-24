/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.BosonCARRepresentation
import InfoGeometry.Algebraic.SplitQuadraticForm
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Nonvacuity at every finite number of sites

These are native endomorphisms of functions on bit configurations. They provide
examples, not a restriction of the arbitrary ambient ring in the theorem owner.
-/
namespace InfoGeometry.Core.BosonFermionRegression
open BosonParityString

variable {R : Type*} [CommRing R] {N : ℕ}

/-- A local hard-core mode on the native configuration module. -/
def localMode (c : Bool) (j : Fin N) : Module.End R ((Fin N → Bool) → R) where
  toFun v s := if s j = c then v (Function.update s j (!c)) else 0
  map_add' v w := by
    funext s
    split_ifs <;> simp_all
  map_smul' r v := by
    funext s
    split_ifs <;> simp_all

lemma localMode_sq (c : Bool) (j : Fin N) :
    localMode (R := R) c j * localMode c j = 0 := by
  apply LinearMap.ext
  intro v
  funext s
  change (if s j = c then (if (Function.update s j (!c)) j = c then _ else 0) else 0) = 0
  cases c <;> simp

lemma localMode_car (j : Fin N) :
    localMode (R := R) false j * localMode true j + localMode true j * localMode false j = 1 := by
  apply LinearMap.ext
  intro v
  funext s
  change (if s j = false then (if (Function.update s j true) j = true then
      v (Function.update (Function.update s j true) j false) else 0) else 0) +
    (if s j = true then (if (Function.update s j false) j = false then
      v (Function.update (Function.update s j false) j true) else 0) else 0) = v s
  cases hs : s j <;> simp [← hs]

lemma localMode_commute (c e : Bool) {j k : Fin N} (hne : j ≠ k) :
    Commute (localMode (R := R) c j) (localMode e k) := by
  change localMode c j * localMode e k = localMode e k * localMode c j
  apply LinearMap.ext
  intro v
  funext s
  change (if s j = c then (if (Function.update s j (!c)) k = e then
      v (Function.update (Function.update s j (!c)) k (!e)) else 0) else 0) =
    (if s k = e then (if (Function.update s k (!e)) j = c then
      v (Function.update (Function.update s k (!e)) j (!c)) else 0) else 0)
  simp only [Function.update_of_ne hne, Function.update_of_ne hne.symm]
  rw [Function.update_comm hne]
  split_ifs <;> rfl

/-- An actual input system for every `N`, over any commutative coefficient ring. -/
theorem configuration_system (R : Type*) [CommRing R] (N : ℕ) :
    IsCommutingBosonSystem (localMode (R := R) (N := N) false) (localMode true) where
  d_sq := localMode_sq false
  B_sq := localMode_sq true
  on_site := localMode_car
  comm_dd := localMode_commute false false
  comm_BB := localMode_commute true true
  comm_dB := localMode_commute false true

/-- Neither local mode is the zero operator over a nontrivial coefficient ring. -/
lemma localMode_ne_zero [Nontrivial R] (c : Bool) (j : Fin N) :
    localMode (R := R) c j ≠ 0 := by
  intro he
  have hv := congrArg (fun T : Module.End R ((Fin N → Bool) → R) => T (fun _ => 1) (fun _ => c)) he
  simp [localMode] at hv

/-- The two local modes do not commute, in every characteristic. -/
lemma localMode_noncommute [Nontrivial R] (j : Fin N) :
    localMode (R := R) false j * localMode true j ≠
      localMode true j * localMode false j := by
  intro he
  have hv := congrArg
    (fun T : Module.End R ((Fin N → Bool) → R) => T (fun _ => 1) (fun _ => false)) he
  simp [Module.End.mul_apply, localMode] at hv

/-- In characteristic two the Majorana pair collapses; division by two is invalid. -/
lemma charTwo_majoranas_coincide (j : Fin N) :
    (configuration_system (ZMod 2) N).plus j = (configuration_system (ZMod 2) N).minus j := by
  change _ + _ = _ - _
  have hneg : ∀ x : Module.End (ZMod 2) ((Fin N → Bool) → ZMod 2), -x = x := by
    intro x
    apply LinearMap.ext
    intro v
    funext s
    exact CharTwo.neg_eq _
  rw [sub_eq_add_neg, hneg]

/-- Characteristic two does not destroy the actual nonzero nilpotent mode. -/
lemma charTwo_dressed_nonzero (c : Bool) (j : Fin N) :
    (configuration_system (ZMod 2) N).dressed c j ≠ 0 := by
  intro he
  have hu := (configuration_system (ZMod 2) N).undress c j
  rw [he, mul_zero] at hu
  cases c
  · exact localMode_ne_zero false j hu.symm
  · exact localMode_ne_zero true j hu.symm

/-- The rational one-site annihilation matrix. -/
def matrixAnnihilator : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]

/-- Its star-dual creation matrix. -/
def matrixCreator : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]

/-- The rational star-dual matrix modes have distinct ordered products. -/
theorem matrix_modes_noncommute :
    matrixAnnihilator * matrixCreator ≠ matrixCreator * matrixAnnihilator := by
  intro h
  have hh := congrArg (fun a : Matrix (Fin 2) (Fin 2) ℚ => a 0 0) h
  norm_num [matrixAnnihilator, matrixCreator, Matrix.mul_apply, Fin.sum_univ_two] at hh

/-- The additional adjoint hypothesis is inhabited by a nonzero system too. -/
theorem star_system_nonempty :
    ∃ d B : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ,
      IsCommutingBosonSystem d B ∧ (∀ j, B j = star (d j)) ∧ d 0 ≠ 0 := by
  refine ⟨fun _ => matrixAnnihilator, fun _ => matrixCreator, ?_, ?_, ?_⟩
  all_goals dsimp only [matrixAnnihilator, matrixCreator]
  · constructor
    · intro j; ext a b
      fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    · intro j; ext a b
      fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    · intro j; ext a b
      fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    · intro j k hne; exact (hne (Subsingleton.elim j k)).elim
    · intro j k hne; exact (hne (Subsingleton.elim j k)).elim
    · intro j k hne; exact (hne (Subsingleton.elim j k)).elim
  · intro j; ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  · intro he
    have he01 := congrArg (fun T : Matrix (Fin 2) (Fin 2) ℚ => T 0 1) he
    norm_num at he01

/-- Native neutral-Clifford images remain distinct in characteristic two, even
though the positive and negative Majoranas coincide. -/
lemma native_car_charTwo_distinct (j : Fin N) :
    (configuration_system (ZMod 2) N).carRepresentation (R := ZMod 2)
      (CliffordAlgebra.ι _ (0, Pi.single j 1)) ≠
    (configuration_system (ZMod 2) N).carRepresentation (R := ZMod 2)
      (CliffordAlgebra.ι _ ((Pi.basisFun (ZMod 2) (Fin N)).dualBasis j, 0)) := by
  rw [IsCommutingBosonSystem.carRepresentation_annihilate,
    IsCommutingBosonSystem.carRepresentation_create]
  intro he
  have hc := (configuration_system (ZMod 2) N).dressed_mixed_car j j
  rw [← he, (configuration_system (ZMod 2) N).dressed_sq] at hc
  simp at hc

/-- The generic lift's real specialization equals the existing split-quadratic
owner, with its positive/negative ordering and signs. This equality supplies
literal carrier transport; it is not a claim based on matching dimensions. -/
lemma native_real_split_form (N : ℕ) :
    QuadraticMap.weightedSumSquares ℝ
      (Sum.elim (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => -1)) =
      InfoGeometry.Algebraic.SplitSignature.splitQuadraticForm N := by
  unfold InfoGeometry.Algebraic.SplitSignature.splitQuadraticForm
  congr 1
  funext i
  cases i <;> rfl

end InfoGeometry.Core.BosonFermionRegression
