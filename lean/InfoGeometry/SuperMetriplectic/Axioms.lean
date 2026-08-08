import InfoGeometry.Core.SymmetricLie
import InfoGeometry.Canonical.AssociativeSuperBracket

/-!
# Supergraded Metriplectic Axioms

Conservative axiomatic interface for the supergraded metiplectic program
without a background spacetime manifold.

This file deliberately avoids proving analytic positivity, existence of
Moore-Penrose inverses, or existence of Drazin inverses.  Those facts are
carried as explicit fields.  The definitions here only package the stable
algebraic/computational skeleton:

* odd-odd supercharge closure `Q,Q -> P + Z`;
* a Cartan-compatible split supplied by an admissible involution;
* Moore-Penrose-stabilized scalar Schur reduction;
* Drazin projector extraction of the persistent defect lane;
* body-level entropy production as the observable nonnegative quantity.
-/

namespace InfoGeometry.SuperMetriplectic

open InfoGeometry.Canonical.AssociativeSuperBracket

/--
Odd-odd closure packet in an associative real algebra.

`P` is the emergent even translation shadow and `Z` is the residual central or
topological defect contribution.  Centrality/topological meaning is not
asserted here; it should be supplied by downstream operator-algebra contexts.
-/
structure SuperchargeClosure (A : Type*) [Ring A] [Algebra ℝ A] where
  Q₁ : A
  Q₂ : A
  P : A
  Z : A
  gamma : ℝ
  oddOddClosure : anticommutator Q₁ Q₂ = gamma • P + Z

namespace SuperchargeClosure

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The emergent translation component of an odd-odd closure packet. -/
abbrev translationShadow (C : SuperchargeClosure A) : A :=
  C.P

/-- The non-geometrized defect component of an odd-odd closure packet. -/
abbrev defectShadow (C : SuperchargeClosure A) : A :=
  C.Z

/-- Restatement of the closure relation as the public packet equation. -/
theorem anticommutator_eq_translation_add_defect (C : SuperchargeClosure A) :
    anticommutator C.Q₁ C.Q₂ = C.gamma • C.translationShadow + C.defectShadow :=
  C.oddOddClosure

end SuperchargeClosure

/--
Chiral scalar odd-odd closure packet.

This is the chiral refinement of `SuperchargeClosure`: the odd lane is first
split into explicit left/right scalar shadows, then recombined into the net odd
shadow `Q_R - Q_L`.  The closure law is still conservative and scalar/body-level.
-/
structure ChiralSuperchargeClosure (A : Type*) [Ring A] [Algebra ℝ A] where
  QL : A
  QR : A
  P : A
  Z : A
  gamma : ℝ
  netOddOddClosure : anticommutator (QR - QL) (QR - QL) = gamma • P + Z

namespace ChiralSuperchargeClosure

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The net odd shadow obtained from the right-minus-left chiral scalar lanes. -/
noncomputable def netOddShadow (C : ChiralSuperchargeClosure A) : A :=
  C.QR - C.QL

/-- The emergent translation component of the chiral odd-odd closure packet. -/
abbrev translationShadow (C : ChiralSuperchargeClosure A) : A :=
  C.P

/-- The residual defect/central component of the chiral odd-odd closure packet. -/
abbrev defectShadow (C : ChiralSuperchargeClosure A) : A :=
  C.Z

/-- The net odd shadow is definitionally the right-minus-left chiral difference. -/
theorem netOddShadow_eq_right_minus_left (C : ChiralSuperchargeClosure A) :
    C.netOddShadow = C.QR - C.QL := by
  rfl

/-- Restatement of the chiral net odd-odd closure as the public packet equation. -/
theorem anticommutator_netOddShadow_eq_translation_add_defect
    (C : ChiralSuperchargeClosure A) :
    anticommutator C.netOddShadow C.netOddShadow
      = C.gamma • C.translationShadow + C.defectShadow := by
  simpa [netOddShadow, translationShadow, defectShadow] using C.netOddOddClosure

/-- Forget the chiral packet to the older undifferentiated scalar closure packet. -/
noncomputable def toSuperchargeClosure (C : ChiralSuperchargeClosure A) :
    SuperchargeClosure A where
  Q₁ := C.netOddShadow
  Q₂ := C.netOddShadow
  P := C.P
  Z := C.Z
  gamma := C.gamma
  oddOddClosure := C.anticommutator_netOddShadow_eq_translation_add_defect

end ChiralSuperchargeClosure

/--
Cartan-compatible thermodynamic split.

The split is not derived from an arbitrary Onsager tensor.  It is supplied by
an admissible involution through an existing `SymmetricLieAlgebra` structure,
and the Drazin/range lanes are explicitly identified with the `+1` and `-1`
Cartan eigenspaces.
-/
structure CartanOnsagerSplit (L : Type*) [LieRing L] [LieAlgebra ℝ L] where
  S : InfoGeometry.Core.SymmetricLieAlgebra L
  onsager : L →ₗ[ℝ] L
  drazinCore : Submodule ℝ L
  dissipativeRange : Submodule ℝ L
  drazinCore_eq_k : drazinCore = S.𝔨
  dissipativeRange_eq_p : dissipativeRange = S.𝔭

namespace CartanOnsagerSplit

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- The topological/Drazin lane is the `+1` Cartan eigenspace by property. -/
theorem drazinCore_is_cartan_k (C : CartanOnsagerSplit L) :
    C.drazinCore = C.S.𝔨 :=
  C.drazinCore_eq_k

/-- The dissipative/range lane is the `-1` Cartan eigenspace by property. -/
theorem dissipativeRange_is_cartan_p (C : CartanOnsagerSplit L) :
    C.dissipativeRange = C.S.𝔭 :=
  C.dissipativeRange_eq_p

end CartanOnsagerSplit

/--
Scalar Moore-Penrose inverse property.

This is the one-dimensional body-level shadow of the operator inverse data.
Higher-dimensional/operator versions should replace `ℝ` with the existing
`CertifiedInverseKernel` surfaces.
-/
structure ScalarPenroseInverse where
  a : ℝ
  aPlus : ℝ
  aba : a * aPlus * a = a
  bab : aPlus * a * aPlus = aPlus

/-- Scalar Drazin inverse property for spectral/topological memory. -/
structure ScalarDrazinInverse where
  a : ℝ
  aD : ℝ
  index : ℕ
  commute : a * aD = aD * a
  reflexive : aD * a * aD = aD
  spectral :
    a ^ (index + 1) * aD = a ^ index

/--
Two-block scalar shadow of a hidden-sector Onsager matrix.

The fields represent the block matrix
`[[LPP, LPΘ], [LΘP, LΘΘ]]`, together with explicit Penrose and Drazin witnesses
for the hidden block `LΘΘ`.
-/
structure ScalarSchurDrazinBlock where
  LPP : ℝ
  LPΘ : ℝ
  LΘP : ℝ
  LΘΘ : ℝ
  penrose : ScalarPenroseInverse
  drazin : ScalarDrazinInverse
  penrose_matches_hidden : penrose.a = LΘΘ
  drazin_matches_hidden : drazin.a = LΘΘ

/-- Readout-first alias for the scalar Schur/Penrose/Drazin block packet. -/
abbrev ScalarReadoutSchurDrazinBlock := ScalarSchurDrazinBlock

namespace ScalarSchurDrazinBlock

/--
Moore-Penrose-stabilized Schur complement:
`LPP - LPΘ * (LΘΘ)^+ * LΘP`.
-/
noncomputable def effectiveEvenOnsager (B : ScalarSchurDrazinBlock) : ℝ :=
  B.LPP - B.LPΘ * B.penrose.aPlus * B.LΘP

/-- Drazin defect projector scalar shadow: `1 - LΘΘ * (LΘΘ)^D`. -/
noncomputable def drazinDefectProjector (B : ScalarSchurDrazinBlock) : ℝ :=
  1 - B.LΘΘ * B.drazin.aD

/-- Public equation for the stabilized Schur complement. -/
theorem effectiveEvenOnsager_eq (B : ScalarSchurDrazinBlock) :
    B.effectiveEvenOnsager = B.LPP - B.LPΘ * B.penrose.aPlus * B.LΘP :=
  rfl

/-- Readout-first restatement of the stabilized Schur complement equation. -/
theorem effectiveEvenOnsager_readout_eq (B : ScalarSchurDrazinBlock) :
    B.effectiveEvenOnsager = B.LPP - B.LPΘ * B.penrose.aPlus * B.LΘP :=
  effectiveEvenOnsager_eq B

/-- Public equation for the Drazin defect projector. -/
theorem drazinDefectProjector_eq (B : ScalarSchurDrazinBlock) :
    B.drazinDefectProjector = 1 - B.LΘΘ * B.drazin.aD :=
  rfl

/-- Readout-first restatement of the scalar Drazin defect-projector equation. -/
theorem drazinDefectProjector_readout_eq (B : ScalarSchurDrazinBlock) :
    B.drazinDefectProjector = 1 - B.LΘΘ * B.drazin.aD :=
  drazinDefectProjector_eq B

end ScalarSchurDrazinBlock

/--
Body-level entropy production packet.

Grassmann/nilpotent contributions are not ordered here.  The observable second
law is represented by a real body projection and an explicit nonnegativity
property.
-/
structure BodyEntropyProduction where
  bodyForce : ℝ
  effectiveOnsager : ℝ
  production : ℝ
  production_eq : production = bodyForce * effectiveOnsager * bodyForce
  production_nonneg : 0 ≤ production

namespace BodyEntropyProduction

/-- Observable body-level second-law statement. -/
theorem body_second_law (E : BodyEntropyProduction) :
    0 ≤ E.production :=
  E.production_nonneg

/-- The production is the real body quadratic form carried by the packet. -/
theorem production_eq_body_quadratic (E : BodyEntropyProduction) :
    E.production = E.bodyForce * E.effectiveOnsager * E.bodyForce :=
  E.production_eq

end BodyEntropyProduction

/--
Minimal computational triad joining Schur, Penrose, Drazin, and body positivity.
-/
structure DrazinPenroseSchurTriad where
  block : ScalarSchurDrazinBlock
  entropy : BodyEntropyProduction
  entropy_uses_effective_block :
    entropy.effectiveOnsager = block.effectiveEvenOnsager

namespace DrazinPenroseSchurTriad

/-- Scalar readout of the effective Onsager coefficient carried by the triad packet. -/
noncomputable def effectiveOnsagerReadout (T : DrazinPenroseSchurTriad) : ℝ :=
  T.block.effectiveEvenOnsager

/-- Scalar readout of the Drazin defect-projector coefficient carried by the triad packet. -/
noncomputable def defectProjectorReadout (T : DrazinPenroseSchurTriad) : ℝ :=
  T.block.drazinDefectProjector

/--
Readout-seal theorem for the scalar triad packet.

This records that exported scalar quantities are readouts tied to the carried
Schur/Penrose/Drazin block; it does not replace noncommuting operator lanes.
-/
theorem scalar_readout_seal (T : DrazinPenroseSchurTriad) :
    (T.effectiveOnsagerReadout = T.block.effectiveEvenOnsager)
      ∧ (T.defectProjectorReadout = T.block.drazinDefectProjector) := by
  exact ⟨rfl, rfl⟩

/--
The effective macroscopic Onsager coefficient is the
Moore-Penrose-stabilized Schur complement of the hidden sector.
-/
theorem effective_metric_is_schur_complement (T : DrazinPenroseSchurTriad) :
    T.entropy.effectiveOnsager =
      T.block.LPP - T.block.LPΘ * T.block.penrose.aPlus * T.block.LΘP := by
  rw [T.entropy_uses_effective_block]
  rfl

/-- The observable second-law statement is carried at body level. -/
theorem body_entropy_nonnegative (T : DrazinPenroseSchurTriad) :
    0 ≤ T.entropy.production :=
  T.entropy.production_nonneg

end DrazinPenroseSchurTriad

end InfoGeometry.SuperMetriplectic
