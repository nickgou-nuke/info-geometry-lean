/- SPDX-License-Identifier: Apache-2.0 -/

/-
# Arnold forms and KZ flatness bridge

The repository already contains the concrete three-point logarithmic-form
theorem in Projective.Conf3ConcreteDLog and the coefficient-level KZ
curvature theorem in Canonical.KZLogarithmicConnection.  This module
connects those owner theorems and introduces the indexed residue contract
needed for a future general-configuration-space summation.

The present concrete theorem is deliberately stated for Conf₃; no general
Conf n de Rham complex is fabricated here.
-/

import InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection
import InfoGeometry.Canonical.KZLogarithmicConnection
import InfoGeometry.Projective.Conf3ConcreteDLog

noncomputable section

namespace InfoGeometry.Canonical.ArnoldKZFlatnessBridge

open InfoGeometry.Canonical.KZLogarithmicConnection
open InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection
open InfoGeometry.Projective.Conf3ConcreteDLog

/-- Indexed infinitesimal braid residues.

The two commutator fields are precisely the disjoint-pair and shared-index
relations used in the Kohno--Drinfeld flatness calculation. -/
structure InfinitesimalBraidResidues
    (n : ℕ) (A : Type*) [Ring A] where
  residue : Fin n → Fin n → A
  symmetric : ∀ i j, residue i j = residue j i
  disjoint_commute :
    ∀ i j k l,
      i ≠ j → k ≠ l → i ≠ k → i ≠ l → j ≠ k → j ≠ l →
      bracket (residue i j) (residue k l) = 0
  shared_commute :
    ∀ i j k,
      i ≠ j → i ≠ k → j ≠ k →
      bracket (residue i j)
        (residue i k + residue j k) = 0

theorem disjoint_relation
    {n : ℕ} {A : Type*} [Ring A]
    (R : InfinitesimalBraidResidues n A)
    {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) :
    bracket (R.residue i j) (R.residue k l) = 0 :=
  R.disjoint_commute i j k l hij hkl hik hil hjk hjl

theorem shared_relation
    {n : ℕ} {A : Type*} [Ring A]
    (R : InfinitesimalBraidResidues n A)
    {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    bracket (R.residue i j)
        (R.residue i k + R.residue j k) = 0 :=
  R.shared_commute i j k hij hik hjk

/-- Existing concrete Arnold relation on the three-point configuration
carrier, retained in its native exterior-form algebra. -/
theorem conf3_arnold_relation
    {K : Type*} [Field K]
    {A : Type*} [Ring A] [Algebra K A]
    (alg : ExteriorFormAlgebra (R := K) A)
    (dz : Fin 3 → A) (z : Fin 3 → K)
    (h01 : z 0 ≠ z 1) (h12 : z 1 ≠ z 2) (h20 : z 2 ≠ z 0) :
    alg.wedge (conf3ConcreteForm dz z 0 1)
        (conf3ConcreteForm dz z 1 2) +
      alg.wedge (conf3ConcreteForm dz z 1 2)
        (conf3ConcreteForm dz z 2 0) +
      alg.wedge (conf3ConcreteForm dz z 2 0)
        (conf3ConcreteForm dz z 0 1) = 0 :=
  conf3_concrete_arnold_relation alg dz z h01 h12 h20

/-- Existing KZ curvature cancellation for the concrete three-point
logarithmic forms and CYBE residue data. -/
theorem conf3_kz_curvature_zero
    {K : Type*} [Field K]
    {A : Type*} [Ring A] [Algebra K A]
    (alg : ExteriorFormAlgebra (R := K) A)
    (dz : Fin 3 → A) (z : Fin 3 → K)
    (h01 : z 0 ≠ z 1) (h12 : z 1 ≠ z 2) (h20 : z 2 ≠ z 0)
    (C : CYBEExchangeData (K := K) A) :
    let w01 := conf3ConcreteForm dz z 0 1
    let w12 := conf3ConcreteForm dz z 1 2
    let w20 := conf3ConcreteForm dz z 2 0
    alg.wedge w01 w12 * bracket C.t01 C.t12 +
      alg.wedge w12 w20 * bracket C.t12 C.t20 +
      alg.wedge w20 w01 * bracket C.t20 C.t01 = 0 :=
  kz_curvature_vanishes_of_cybe alg dz z h01 h12 h20 C

/-- Combined three-point Arnold--KZ flatness certificate. -/
theorem conf3_arnold_kz_flatness
    {K : Type*} [Field K]
    {A : Type*} [Ring A] [Algebra K A]
    (alg : ExteriorFormAlgebra (R := K) A)
    (dz : Fin 3 → A) (z : Fin 3 → K)
    (h01 : z 0 ≠ z 1) (h12 : z 1 ≠ z 2) (h20 : z 2 ≠ z 0)
    (C : CYBEExchangeData (K := K) A) :
    (alg.wedge (conf3ConcreteForm dz z 0 1)
        (conf3ConcreteForm dz z 1 2) +
      alg.wedge (conf3ConcreteForm dz z 1 2)
        (conf3ConcreteForm dz z 2 0) +
      alg.wedge (conf3ConcreteForm dz z 2 0)
        (conf3ConcreteForm dz z 0 1) = 0) ∧
    (let w01 := conf3ConcreteForm dz z 0 1
     let w12 := conf3ConcreteForm dz z 1 2
     let w20 := conf3ConcreteForm dz z 2 0
     alg.wedge w01 w12 * bracket C.t01 C.t12 +
       alg.wedge w12 w20 * bracket C.t12 C.t20 +
       alg.wedge w20 w01 * bracket C.t20 C.t01 = 0) := by
  refine ⟨conf3_arnold_relation alg dz z h01 h12 h20, ?_⟩
  exact conf3_kz_curvature_zero alg dz z h01 h12 h20 C

end InfoGeometry.Canonical.ArnoldKZFlatnessBridge
