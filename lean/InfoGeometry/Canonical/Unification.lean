import InfoGeometry.Canonical.Singular
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Quantum.ModularAnomaly

set_option linter.unusedSectionVars false

namespace Unification

open InfoGeometry.Krein

open InfoGeometry.Quantum.ModularAnomaly
open InfoGeometry.Quantum.RealMajoranaCategory

/--
Hypothesis-driven Rosetta package for anomaly transport across layers.

It records a single source tension presented in three codomains:
geometric residual, Fock deformation, and modular generator, together with
explicit transport maps and the two commuting equalities.
-/
structure AnomalyRosettaStone
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  -- Geometric layer
  einsteinAnomaly : E →L[ℝ] E

  -- Thermodynamic/Fock layer
  fockDeformation : E →L[ℝ] E

  -- Modular/Majorana layer
  modularGenerator : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E

  -- Transport dictionary
  liftToFock : (E →L[ℝ] E) →ₗ[ℝ] (E →L[ℝ] E)
  embedToMajorana : (E →L[ℝ] E) →ₗ[ℝ]
    (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E)

  -- Commuting-diagram hypotheses
  h_geo_thermo : liftToFock einsteinAnomaly = fockDeformation
  h_thermo_alg : embedToMajorana fockDeformation = modularGenerator

namespace AnomalyRosettaStone

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (R : AnomalyRosettaStone (E := E))

/--
Composed geometric-to-modular transport map.
This is the categorical composition of the dictionary arrows.
-/
noncomputable def geometricToMajorana
    (R : AnomalyRosettaStone (E := E))
    (A : E →L[ℝ] E) :
  InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E :=
  R.embedToMajorana (R.liftToFock A)

end AnomalyRosettaStone

/-!
Concrete scalar-source packaging

The canonical Einstein residual in the current library is scalar-valued (`ℝ`),
and its Fock realization is an operator via scalar multiplication by identity.
This structure packages that concrete layer while still allowing a user-supplied
embedding into the doubled Majorana operator layer.
-/

section ScalarRosetta

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Scalar source to Fock-operator lift (`r ↦ r • Id`). -/
noncomputable def scalarToFockLift :
  ℝ →ₗ[ℝ] (InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism E) where
  toFun r := r • ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)
  map_add' r s := by
    ext w <;> cases w <;> simp [add_smul]
  map_smul' a r := by
    ext w <;> cases w <;> simp [mul_smul]

/--
Adding a scalar offset before the Fock lift contributes only a central identity
term. In the Einstein/fusion reading this is the operator-level gauge mode, not
new dynamics.
-/
theorem scalarToFockLift_add_const_eq_centralGaugeShift
    (r c : ℝ) :
    scalarToFockLift (E := E) (r + c)
      = scalarToFockLift (E := E) r
        + c • ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) := by
  rw [(scalarToFockLift (E := E)).map_add]
  rfl

/--
Concrete Rosetta package for scalar source tension.

`source` is the transported Einstein residual/chemical potential scalar;
`fockDeformation` is its canonical Fock lift; `modularGenerator` is any
Majorana-layer realization linked by `h_fock_mod`.
-/
structure ScalarAnomalyRosettaStone where
  source : ℝ
  fockDeformation : InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism E
  modularGenerator :
    InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E
  embedToMajorana :
    (InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism E) →ₗ[ℝ]
      (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E)
  h_source_fock : scalarToFockLift source = fockDeformation
  h_fock_mod : embedToMajorana fockDeformation = modularGenerator

namespace ScalarAnomalyRosettaStone

variable (S : ScalarAnomalyRosettaStone (E := E))

/-- Composed scalar-to-modular transport. -/
noncomputable def scalarToMajorana :
  ℝ →ₗ[ℝ] (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) :=
  LinearMap.comp S.embedToMajorana scalarToFockLift

end ScalarAnomalyRosettaStone

/--
Canonical scalar-source Rosetta constructor from existing Einstein/Fock definitions.
-/
noncomputable def canonicalScalarRosetta
    (R : InfoGeometry.Canonical.RicciMongeAmpere.RicciTensor E)
  (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection K x V)
    (embedToMajorana :
      (InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism E) →ₗ[ℝ]
        (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E))
    (modularGenerator :
      InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E)
    (h_fock_mod :
      embedToMajorana
          (InfoGeometry.Canonical.BogoliubovFockSuper.einsteinFockDeformationOperator
            (E := E) R K x scalar Λ V Γ)
        = modularGenerator) :
    ScalarAnomalyRosettaStone (E := E) where
  source := InfoGeometry.Canonical.BogoliubovFockSuper.einsteinInducedChemicalPotential
    (E := E) R K x scalar Λ V Γ
  fockDeformation := InfoGeometry.Canonical.BogoliubovFockSuper.einsteinFockDeformationOperator
    (E := E) R K x scalar Λ V Γ
  modularGenerator := modularGenerator
  embedToMajorana := embedToMajorana
  h_source_fock := by
    rfl
  h_fock_mod := h_fock_mod

end ScalarRosetta

section Cl11LatticeRosetta

open InfoGeometry.Quantum.ModularAnomaly.Cl11LatticeBridge

variable {n : ℕ}

noncomputable local instance : NormedAddCommGroup (cl11DoubledCore (FinModel (N := n))) := by
  change NormedAddCommGroup (InfoGeometry.Krein.DoubledSpace (FinModel (N := n)))
  infer_instance

noncomputable local instance : NormedSpace ℝ (cl11DoubledCore (FinModel (N := n))) := by
  change NormedSpace ℝ (InfoGeometry.Krein.DoubledSpace (FinModel (N := n)))
  infer_instance

noncomputable local instance : InnerProductSpace ℝ (cl11DoubledCore (FinModel (N := n))) := by
  change InnerProductSpace ℝ (InfoGeometry.Krein.DoubledSpace (FinModel (N := n)))
  infer_instance

noncomputable local instance : CompleteSpace (cl11DoubledCore (FinModel (N := n))) := by
  change CompleteSpace (InfoGeometry.Krein.DoubledSpace (FinModel (N := n)))
  infer_instance

noncomputable local instance : KreinSpace (cl11DoubledCore (FinModel (N := n))) := by
  change KreinSpace (InfoGeometry.Krein.DoubledSpace (FinModel (N := n)))
  infer_instance

noncomputable local instance :
    NormedRing
      (ContinuousCarrier (N := n) →L[ℝ] ContinuousCarrier (N := n)) := inferInstance

noncomputable local instance :
    NormedAlgebra ℝ
      (ContinuousCarrier (N := n) →L[ℝ] ContinuousCarrier (N := n)) := inferInstance

noncomputable local instance :
    CompleteSpace
      (ContinuousCarrier (N := n) →L[ℝ] ContinuousCarrier (N := n)) := by
  infer_instance

local instance :
    IsTopologicalRing
      (ContinuousCarrier (N := n) →L[ℝ] ContinuousCarrier (N := n)) := inferInstance

/--
Finite-dimensional `Cl(1,1)` Rosetta package:
a continuous canonical modular anomaly together with its transported lattice
shadow under the coordinate avatar functor.
-/
structure Cl11LatticeRosettaStone (n : ℕ) where
  symmetry :
    ContinuousCarrier (N := n) ≃L[ℝ] ContinuousCarrier (N := n)
  continuousAnomaly :
    ContinuousCarrier (N := n) →L[ℝ] ContinuousCarrier (N := n)
  latticeAnomaly :
    LatticeCarrier (N := n) →L[ℝ] LatticeCarrier (N := n)
  h_transport :
    latticeAvatarCLM (N := n) continuousAnomaly = latticeAnomaly

/--
Canonical continuous `Cl(1,1)` anomaly operator attached to a symmetry `U`.

This is the explicit commutator-shadow formula already identified with the
continuous modular anomaly generator in `Quantum.ModularAnomaly`.
-/
noncomputable def canonicalContinuousCl11Anomaly
    (U : ContinuousCarrier (N := n) ≃L[ℝ] ContinuousCarrier (N := n)) :
    ContinuousCarrier (N := n) →L[ℝ] ContinuousCarrier (N := n) :=
  let ε : ContinuousCarrier (N := n) →L[ℝ] ContinuousCarrier (N := n) :=
    Cl11Shadow.canonicalCl11Generator (E := FinModel (N := n))
  (U.symm : ContinuousCarrier (N := n) →L[ℝ] ContinuousCarrier (N := n)).comp
    (ε.comp (U : ContinuousCarrier (N := n) →L[ℝ] ContinuousCarrier (N := n))
      - (U : ContinuousCarrier (N := n) →L[ℝ] ContinuousCarrier (N := n)).comp ε)

/--
Canonical lattice commutator shadow transported by the lattice avatar of `U`.
-/
noncomputable def canonicalLatticeCl11Anomaly
    (U : ContinuousCarrier (N := n) ≃L[ℝ] ContinuousCarrier (N := n)) :
    LatticeCarrier (N := n) →L[ℝ] LatticeCarrier (N := n) :=
  latticeCommutatorShadow (N := n) (latticeAutomorphismAvatar (N := n) U)

/--
Concrete continuous-to-lattice transport theorem for the canonical `Cl(1,1)`
anomaly operator.
-/
theorem latticeAvatar_canonicalContinuousCl11Anomaly
    (U : ContinuousCarrier (N := n) ≃L[ℝ] ContinuousCarrier (N := n)) :
    latticeAvatarCLM (N := n) (canonicalContinuousCl11Anomaly (n := n) U) =
      canonicalLatticeCl11Anomaly (n := n) U := by
  have hCont :
      (Cl11Shadow.canonicalCl11TopologicalShadow (E := FinModel (N := n))).modularAnomalyGenerator U =
        canonicalContinuousCl11Anomaly (n := n) U := by
    simpa [canonicalContinuousCl11Anomaly] using
      (Cl11Shadow.modularAnomalyGenerator_eq_canonicalCl11_commutator_shadow
        (E := FinModel (N := n)) (U := U))
  rw [← hCont]
  simpa [canonicalLatticeCl11Anomaly] using
    (latticeAvatar_canonicalCl11_modularAnomalyGenerator (N := n) U)

/--
Canonical `Cl(1,1)` Rosetta constructor from the modular anomaly transport
theorem.
-/
noncomputable def canonicalCl11LatticeRosettaStone
    (U : ContinuousCarrier (N := n) ≃L[ℝ] ContinuousCarrier (N := n)) :
    Cl11LatticeRosettaStone n where
  symmetry := U
  continuousAnomaly := canonicalContinuousCl11Anomaly (n := n) U
  latticeAnomaly := canonicalLatticeCl11Anomaly (n := n) U
  h_transport := latticeAvatar_canonicalContinuousCl11Anomaly (n := n) U

namespace Cl11LatticeRosettaStone

variable (R : Cl11LatticeRosettaStone n)

/--
The lattice anomaly is exactly the avatar of the continuous canonical anomaly.
-/
theorem continuous_eq_lattice_shadow :
    latticeAvatarCLM (N := n) R.continuousAnomaly = R.latticeAnomaly :=
  R.h_transport

end Cl11LatticeRosettaStone

end Cl11LatticeRosetta

end Unification
