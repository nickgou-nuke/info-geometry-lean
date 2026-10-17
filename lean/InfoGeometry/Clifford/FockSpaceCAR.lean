/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ChevalleySpinorBlueprint
import InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
import InfoGeometry.Clifford.ClNNToDoubledKreinTransport
import InfoGeometry.Algebra.ChakravalaGA

/-!
# Exterior Fock space and its canonical CAR action

The Fock carrier is Mathlib's exterior algebra. Creation and annihilation are
transported from the native Clifford-algebra model at quadratic form zero by
Mathlib's `CliffordAlgebra.equivExterior`. The dual argument of annihilation
is the algebraic dual; no inner-product or Hilbert-space identification is
assumed here.
-/

noncomputable section

namespace InfoGeometry.Clifford.FockSpaceCAR

open InfoGeometry.Clifford
open InfoGeometry.Clifford.ClNNToDoubledKreinTransport
open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
open InfoGeometry.Krein

variable {L : Type*} [AddCommGroup L] [Module ℝ L]

/-- The algebraic Fock space over a real mode space. -/
abbrev FockSpace (L : Type*) [AddCommGroup L] [Module ℝ L] :=
  ExteriorAlgebra ℝ L

/-- Mathlib's native equivalence from the zero-quadratic Clifford model to
the exterior-algebra Fock carrier. -/
def fockExteriorEquiv : SpinorSpace L ≃ₗ[ℝ] FockSpace L :=
  CliffordAlgebra.equivExterior (0 : QuadraticForm ℝ L)

/-- Creation by `u`, transported as exterior multiplication by the mode. -/
def creation (u : L) : Module.End ℝ (FockSpace L) :=
  (fockExteriorEquiv (L := L)).toLinearMap.comp
    ((extAction u).comp (fockExteriorEquiv (L := L)).symm.toLinearMap)

/-- Annihilation by an algebraic covector, transported from Mathlib's
canonical left contraction on the zero-quadratic Clifford algebra. -/
def annihilation (f : Dual L) : Module.End ℝ (FockSpace L) :=
  (fockExteriorEquiv (L := L)).toLinearMap.comp
    ((intAction f).comp (fockExteriorEquiv (L := L)).symm.toLinearMap)

@[simp] theorem creation_apply (u : L) (ψ : FockSpace L) :
    creation u ψ = fockExteriorEquiv (L := L)
      (extAction u ((fockExteriorEquiv (L := L)).symm ψ)) := rfl

@[simp] theorem annihilation_apply (f : Dual L) (ψ : FockSpace L) :
    annihilation f ψ = fockExteriorEquiv (L := L)
      (intAction f ((fockExteriorEquiv (L := L)).symm ψ)) := rfl

/-- Mathlib's Clifford-to-exterior equivalence at the zero quadratic form is
the identity on the underlying carrier. -/
@[simp] theorem fockExteriorEquiv_zero_apply (ψ : SpinorSpace L) :
    fockExteriorEquiv (L := L) ψ = ψ := by
  simp [fockExteriorEquiv, CliffordAlgebra.equivExterior]

/-- The inverse zero-form equivalence is also the identity on the underlying
carrier. -/
@[simp] theorem fockExteriorEquiv_zero_symm_apply (ψ : FockSpace L) :
    (fockExteriorEquiv (L := L)).symm ψ = ψ := by
  apply (fockExteriorEquiv (L := L)).injective
  simp

/-- The transported creation action is exterior multiplication by its mode. -/
@[simp] theorem creation_apply_ι_mul (u : L) (ψ : FockSpace L) :
    creation u ψ = ExteriorAlgebra.ι ℝ u * ψ := by
  simp [creation, extAction]

/-- The transported annihilation action is Mathlib's native left contraction. -/
@[simp] theorem annihilation_apply_contractLeft (f : Dual L) (ψ : FockSpace L) :
    annihilation f ψ = CliffordAlgebra.contractLeft f ψ := by
  simp [annihilation, intAction]

/-- Two creation operators anticommute. -/
theorem creation_anticommute (u v : L) (ψ : FockSpace L) :
    creation u (creation v ψ) + creation v (creation u ψ) = 0 := by
  have hCl (w : SpinorSpace L) :
      extAction u (extAction v w) + extAction v (extAction u w) = 0 := by
    have hmul :
        CliffordAlgebra.ι (0 : QuadraticForm ℝ L) u *
            CliffordAlgebra.ι (0 : QuadraticForm ℝ L) v +
          CliffordAlgebra.ι (0 : QuadraticForm ℝ L) v *
            CliffordAlgebra.ι (0 : QuadraticForm ℝ L) u = 0 := by
      have h := CliffordAlgebra.ι_mul_ι_add_swap
        (Q := (0 : QuadraticForm ℝ L)) u v
      simp
    change (CliffordAlgebra.ι (0 : QuadraticForm ℝ L) u *
          (CliffordAlgebra.ι (0 : QuadraticForm ℝ L) v * w)) +
        (CliffordAlgebra.ι (0 : QuadraticForm ℝ L) v *
          (CliffordAlgebra.ι (0 : QuadraticForm ℝ L) u * w)) = 0
    calc
      _ = (CliffordAlgebra.ι (0 : QuadraticForm ℝ L) u *
            CliffordAlgebra.ι (0 : QuadraticForm ℝ L) v +
          CliffordAlgebra.ι (0 : QuadraticForm ℝ L) v *
            CliffordAlgebra.ι (0 : QuadraticForm ℝ L) u) * w := by
              rw [← mul_assoc, ← mul_assoc, ← add_mul]
      _ = 0 := by rw [hmul, zero_mul]
  calc
    creation u (creation v ψ) + creation v (creation u ψ) =
        fockExteriorEquiv (L := L)
          (extAction u (extAction v ((fockExteriorEquiv (L := L)).symm ψ)) +
            extAction v (extAction u ((fockExteriorEquiv (L := L)).symm ψ))) := by
          simp only [creation_apply, LinearEquiv.map_add]
          simp only [LinearEquiv.symm_apply_apply]
    _ = 0 := by rw [hCl]; simp

/-- Two annihilation operators anticommute. -/
theorem annihilation_anticommute (f g : Dual L) (ψ : FockSpace L) :
    annihilation f (annihilation g ψ) + annihilation g (annihilation f ψ) = 0 := by
  have hCl (w : SpinorSpace L) :
      intAction f (intAction g w) + intAction g (intAction f w) = 0 := by
    have h := CliffordAlgebra.contractLeft_contractLeft
      (Q := (0 : QuadraticForm ℝ L)) (d := f + g) w
    change intAction (f + g) (intAction (f + g) w) = 0 at h
    have hlin : intAction (f + g) = intAction f + intAction g := by
      change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ L)) (f + g) = _
      exact LinearMap.map_add (CliffordAlgebra.contractLeft
        (Q := (0 : QuadraticForm ℝ L))) f g
    simp only [hlin, LinearMap.add_apply] at h
    simp only [map_add] at h
    rw [int_sq_zero f w, int_sq_zero g w] at h
    simpa only [zero_add, add_zero, add_assoc, add_left_comm, add_comm] using h
  calc
    annihilation f (annihilation g ψ) + annihilation g (annihilation f ψ) =
        fockExteriorEquiv (L := L)
          (intAction f (intAction g ((fockExteriorEquiv (L := L)).symm ψ)) +
            intAction g (intAction f ((fockExteriorEquiv (L := L)).symm ψ))) := by
          simp only [annihilation_apply, LinearEquiv.map_add,
            LinearEquiv.symm_apply_apply]
    _ = 0 := by rw [hCl]; simp

/-- The mixed creation-annihilation CAR: the anticommutator is evaluation
times the identity action on every Fock vector. -/
theorem creation_annihilation_CAR (u : L) (f : Dual L) (ψ : FockSpace L) :
    creation u (annihilation f ψ) + annihilation f (creation u ψ) =
      (f u) • ψ := by
  calc
    creation u (annihilation f ψ) + annihilation f (creation u ψ) =
        fockExteriorEquiv (L := L)
          (extAction u (intAction f ((fockExteriorEquiv (L := L)).symm ψ)) +
            intAction f (extAction u ((fockExteriorEquiv (L := L)).symm ψ))) := by
          simp only [creation_apply, annihilation_apply, LinearEquiv.map_add,
            LinearEquiv.symm_apply_apply]
    _ = (f u) • ψ := by
      rw [ext_int_anticommutator]
      rw [← Algebra.smul_def]
      simp only [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]

/-- The degree-zero Fock vacuum is annihilated by every covector. -/
theorem annihilation_vacuum (f : Dual L) :
    annihilation f (1 : FockSpace L) = 0 := by
  simp [annihilation, fockExteriorEquiv, intAction]

/-- Creation on the vacuum is the exterior generator. -/
@[simp] theorem creation_vacuum (u : L) :
    creation u (1 : FockSpace L) = ExteriorAlgebra.ι ℝ u := by
  simp [creation, fockExteriorEquiv, extAction,
    CliffordAlgebra.equivExterior]

/-- Creation by a mode is square-zero on the exterior Fock carrier. -/
theorem creation_sq (u : L) (ψ : FockSpace L) :
    creation u (creation u ψ) = 0 := by
  simp only [creation_apply, LinearEquiv.symm_apply_apply,
    ext_sq_zero, LinearEquiv.map_zero]

/-- Annihilation by a covector is square-zero on the exterior Fock carrier. -/
theorem annihilation_sq (f : Dual L) (ψ : FockSpace L) :
    annihilation f (annihilation f ψ) = 0 := by
  simp only [annihilation_apply, LinearEquiv.symm_apply_apply,
    int_sq_zero, LinearEquiv.map_zero]

/-- The square of the neutral creation-plus-annihilation action is its
evaluation quadratic form. This is the CAR normalization used by the split
Clifford generator. -/
theorem creation_annihilation_sum_sq (u : L) (f : Dual L) (ψ : FockSpace L) :
    creation u (creation u ψ + annihilation f ψ) +
      annihilation f (creation u ψ + annihilation f ψ) = (f u) • ψ := by
  calc
    _ = creation u (creation u ψ) +
          (creation u (annihilation f ψ) + annihilation f (creation u ψ)) +
          annihilation f (annihilation f ψ) := by
            simp only [map_add]
            abel
    _ = (f u) • ψ := by
          rw [creation_sq, creation_annihilation_CAR, annihilation_sq]
          simp

/-- Creation depends linearly on its mode. -/
def creationOperator : L →ₗ[ℝ] Module.End ℝ (FockSpace L) where
  toFun := creation
  map_add' u v := by
    ext ψ
    simp [creation, extAction, map_add, add_mul]
  map_smul' c u := by
    ext ψ
    simp [creation, extAction, map_smul]

/-- Annihilation depends linearly on its algebraic covector. -/
def annihilationOperator : Dual L →ₗ[ℝ] Module.End ℝ (FockSpace L) where
  toFun := annihilation
  map_add' f g := by
    ext ψ
    simp [annihilation, intAction, map_add, LinearMap.add_apply]
  map_smul' c f := by
    ext ψ
    simp [annihilation, intAction, map_smul, LinearMap.smul_apply]

/-- The odd--odd superbracket of two creation operators vanishes as an
endomorphism, on every exterior degree. -/
theorem creation_creation_superBracket (u v : L) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
        (creationOperator u) (creationOperator v) = 0 := by
  rw [ChakravalaGA.superBracket_fermionic]
  ext ψ
  exact creation_anticommute u v ψ

/-- The odd--odd superbracket of two contraction operators vanishes as an
endomorphism, on every exterior degree. -/
theorem annihilation_annihilation_superBracket (f g : Dual L) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
        (annihilationOperator f) (annihilationOperator g) = 0 := by
  rw [ChakravalaGA.superBracket_fermionic]
  ext ψ
  exact annihilation_anticommute f g ψ

/-- The full odd--odd Chakravala superbracket of creation and annihilation is
the evaluation scalar times the identity endomorphism. This is the operator
form of the CAR, valid on every exterior degree, not only on the vacuum and
one-particle sectors. -/
theorem creation_annihilation_superBracket (u : L) (f : Dual L) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
        (creationOperator u) (annihilationOperator f) =
      (f u) • (1 : Module.End ℝ (FockSpace L)) := by
  rw [ChakravalaGA.superBracket_fermionic]
  ext ψ
  exact creation_annihilation_CAR u f ψ

/-- Annihilation of a one-particle state evaluates its covector. -/
theorem annihilation_creation_vacuum (f : Dual L) (u : L) :
    annihilation f (creation u (1 : FockSpace L)) = (f u) • (1 : FockSpace L) := by
  calc
    annihilation f (creation u (1 : FockSpace L)) =
        creation u (annihilation f (1 : FockSpace L)) +
          annihilation f (creation u (1 : FockSpace L)) := by
            rw [annihilation_vacuum]
            simp
    _ = (f u) • (1 : FockSpace L) :=
      creation_annihilation_CAR (u := u) (f := f) (ψ := (1 : FockSpace L))

/-! ### The finite-rank `Cl(n,n)` primal and vacuum sheets -/

/-- The actual primal mode carrier in the recursive `Cl(n,n)` tower. -/
abbrev PrimalSheet (n : ℕ) :=
  LinearMap.range (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralPrimalSheetMap n)

/-- The actual covector vacuum-sheet carrier in the recursive `Cl(n,n)` tower. -/
abbrev CovectorSheet (n : ℕ) :=
  LinearMap.range (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralVacuumSheetMap n)

/-- Creation on the exterior Fock space of the native primal sheet. -/
def sheetCreation (n : ℕ) (u : PrimalSheet n) :
    Module.End ℝ (FockSpace (PrimalSheet n)) :=
  creation u

/-- Annihilation on the primal Fock space, transported from the native
covector vacuum sheet through its proved duality equivalence. -/
def sheetAnnihilation (n : ℕ) (α : CovectorSheet n) :
    Module.End ℝ (FockSpace (PrimalSheet n)) :=
  annihilation
    (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralVacuumSheetDualEquiv n α)

/-- The primal/covector sheet CAR has exactly the native cross-pairing as its
scalar. This identifies the algebraic annihilation covector with the
covector-sheet element through the repository's duality equivalence. -/
theorem sheet_creation_annihilation_CAR (n : ℕ)
    (u : PrimalSheet n) (α : CovectorSheet n)
    (ψ : FockSpace (PrimalSheet n)) :
    sheetCreation n u (sheetAnnihilation n α ψ) +
      sheetAnnihilation n α (sheetCreation n u ψ) =
        (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralVacuumSheetDualEquiv n α u) • ψ := by
  exact creation_annihilation_CAR (u := u)
    (f := InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralVacuumSheetDualEquiv n α)
    (ψ := ψ)

/-- In the native finite-rank parametrizations, the CAR scalar is evaluation
of the original algebraic covector on the original primal vector. -/
theorem neutralTower_CAR (n : ℕ)
    (u : InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.Vector n)
    (φ : Dual (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.Vector n))
    (ψ : FockSpace (PrimalSheet n)) :
    sheetCreation n
        (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralPrimalSheetParametrization n u)
        (sheetAnnihilation n
          (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralVacuumSheetParametrization n φ) ψ) +
      sheetAnnihilation n
          (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralVacuumSheetParametrization n φ)
          (sheetCreation n
            (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralPrimalSheetParametrization n u) ψ) =
        (φ u) • ψ := by
  rw [sheet_creation_annihilation_CAR]
  rw [InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralVacuumSheetDualEquiv_apply]

/-- The finite-rank Fock CAR scalar is the cross pairing of the corresponding
primal and covector modes in the repository's doubled real Krein carrier. -/
theorem neutralTower_CAR_eq_doubledKrein_cross (n : ℕ)
    (u : InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.Vector n)
    (φ : Dual (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.Vector n))
    (ψ : FockSpace (PrimalSheet n)) :
    sheetCreation n
        (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralPrimalSheetParametrization n u)
        (sheetAnnihilation n
          (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralVacuumSheetParametrization n φ) ψ) +
      sheetAnnihilation n
          (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralVacuumSheetParametrization n φ)
          (sheetCreation n
            (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralPrimalSheetParametrization n u) ψ) =
        (hessian_indefinite_form (E := EucVector n)
          (realizeToDoubledRho (E := EucVector n) (rieszEquiv n)
            (toEuclideanPhase n (u, 0)))
          (realizeToDoubledRho (E := EucVector n) (rieszEquiv n)
            (toEuclideanPhase n (0, φ)))) • ψ := by
  rw [neutralTower_CAR]
  rw [InfoGeometry.Clifford.ClNNToDoubledKreinTransport.evaluation_eq_doubledKrein_cross]

end InfoGeometry.Clifford.FockSpaceCAR
