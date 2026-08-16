import InfoGeometry.Core.SymmetricLie
import InfoGeometry.Canonical.AssociativeSuperBracket
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.Drazin

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
* Moore-Penrose-stabilized operator Schur reduction;
* Drazin projector extraction of the persistent defect lane;
* associative operator closure on the native carrier.
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
Chiral odd-odd closure packet on an associative carrier.

This is the chiral refinement of `SuperchargeClosure`: the odd lane is first
split into explicit left/right carrier elements, then recombined into the net
odd carrier element `Q_R - Q_L`.  No commutative or scalar representation is
assumed by this interface.
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

/-- The net odd carrier element obtained from the right-minus-left chiral lanes. -/
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

/-- Forget the chiral packet to the undifferentiated carrier closure packet. -/
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

/-! ### Native noncommutative Schur/Drazin block -/

/-- A Schur/Drazin block on an actual noncommutative observable algebra. -/
structure OperatorSchurDrazinBlock
    (A : Type*) [Ring A] [StarRing A] where
  LPP : A
  LPΘ : A
  LΘP : A
  LΘΘ : A
  penroseElement : A
  drazinElement : A
  index : ℕ
  penrose_is_inverse :
    InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse
      LΘΘ penroseElement
  drazin_is_inverse :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse
      LΘΘ drazinElement index

namespace OperatorSchurDrazinBlock

variable {A : Type*} [Ring A] [StarRing A]

/-- The noncommutative stabilized Schur complement. -/
def effectiveSchur (B : OperatorSchurDrazinBlock A) : A :=
  B.LPP - B.LPΘ * B.penroseElement * B.LΘP

/-- The complementary Drazin projector on the hidden operator lane. -/
def drazinDefectProjector (B : OperatorSchurDrazinBlock A) : A :=
  1 - B.LΘΘ * B.drazinElement

theorem effectiveSchur_eq (B : OperatorSchurDrazinBlock A) :
    B.effectiveSchur = B.LPP - B.LPΘ * B.penroseElement * B.LΘP :=
  rfl

theorem drazinDefectProjector_eq (B : OperatorSchurDrazinBlock A) :
    B.drazinDefectProjector = 1 - B.LΘΘ * B.drazinElement :=
  rfl

/-- The Drazin defect projector is idempotent on the operator carrier. -/
  theorem drazinDefectProjector_idempotent (B : OperatorSchurDrazinBlock A) :
    B.drazinDefectProjector * B.drazinDefectProjector =
      B.drazinDefectProjector := by
  simpa [drazinDefectProjector,
    InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection] using
    InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_is_idempotent
      B.drazin_is_inverse

/-- The Moore--Penrose range projector is idempotent on the operator carrier. -/
theorem penroseRangeProjector_idempotent (B : OperatorSchurDrazinBlock A) :
    (B.LΘΘ * B.penroseElement) * (B.LΘΘ * B.penroseElement) =
      B.LΘΘ * B.penroseElement := by
  simpa [InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector] using
    InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector_idempotent
      B.penrose_is_inverse

end OperatorSchurDrazinBlock


end InfoGeometry.SuperMetriplectic
