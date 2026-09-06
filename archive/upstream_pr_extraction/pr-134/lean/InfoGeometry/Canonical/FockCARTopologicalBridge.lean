import InfoGeometry.Quantum.Fock
import Mathlib.Topology.Category.TopCat.Basic

/-!
# TopCat readout of the Fock creation/annihilation channels

The Fock owner already provides continuous-linear creation, annihilation, and
Clifford commutator maps.  This file exposes those same maps as `TopCat`
endomorphisms and transports their verified operator identities pointwise.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.FockCARTopologicalBridge

open CategoryTheory
open InfoGeometry.Krein
open InfoGeometry.Quantum

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

def creationTopCatHom :
    TopCat.of (DoubledSpace E) ⟶ TopCat.of (DoubledSpace E) :=
  TopCat.ofHom
    { toFun := creationOp (E := E)
      continuous_toFun := (creationOp (E := E)).continuous }

def annihilationTopCatHom :
    TopCat.of (DoubledSpace E) ⟶ TopCat.of (DoubledSpace E) :=
  TopCat.ofHom
    { toFun := annihilationOp (E := E)
      continuous_toFun := (annihilationOp (E := E)).continuous }

@[simp] theorem creationTopCatHom_apply (v : DoubledSpace E) :
    creationTopCatHom (E := E) v = creationOp (E := E) v :=
  rfl

@[simp] theorem annihilationTopCatHom_apply (v : DoubledSpace E) :
    annihilationTopCatHom (E := E) v = annihilationOp (E := E) v :=
  rfl

theorem fock_topCat_decomposition (v : DoubledSpace E) :
    creationTopCatHom (E := E) v + annihilationTopCatHom (E := E) v = v := by
  simpa [creationTopCatHom, annihilationTopCatHom] using
    (data_model_decomposition (E := E) v).symm

theorem fock_topCat_orthogonality (v : DoubledSpace E) :
    creationTopCatHom (E := E)
        (annihilationTopCatHom (E := E) v) = 0 := by
  simpa [creationTopCatHom, annihilationTopCatHom] using
    congrArg (fun T => T v)
      (creation_annihilation_orthogonal (E := E))

def commutatorTopCatHom
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    TopCat.of (DoubledSpace E) ⟶ TopCat.of (DoubledSpace E) :=
  TopCat.ofHom
    { toFun := commutator A B
      continuous_toFun := (commutator A B).continuous }

theorem fock_topCat_commutator_I_J :
    commutatorTopCatHom (E := E)
        (complex_i (E := E)) (modular_j (E := E)) =
      TopCat.ofHom
        { toFun := (-2 : ℝ) • spectral_epsilon (E := E)
          continuous_toFun := ((-2 : ℝ) • spectral_epsilon (E := E)).continuous } := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro v
  simpa [commutatorTopCatHom, TopCat.ofHom] using
    congrArg (fun T => T v) (commutator_I_J (E := E))

theorem fock_topCat_commutator_J_epsilon :
    commutatorTopCatHom (E := E)
        (modular_j (E := E)) (spectral_epsilon (E := E)) =
      TopCat.ofHom
        { toFun := (2 : ℝ) • complex_i (E := E)
          continuous_toFun := ((2 : ℝ) • complex_i (E := E)).continuous } := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro v
  simpa [commutatorTopCatHom, TopCat.ofHom] using
    congrArg (fun T => T v) (commutator_J_epsilon_eq_two_I (E := E))

end InfoGeometry.Canonical.FockCARTopologicalBridge
