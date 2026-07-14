import InfoGeometry.Canonical.BogoliubovCartanEigenOperator
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Krein.KreinSpace

set_option linter.unusedSectionVars false
open InfoGeometry.Krein

namespace DrazinBogoliubovFrameEquiv

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

open InfoGeometry.Canonical.BogoliubovCartanEigenOperator

/--
Drazin witness for a Cartan eigen-operator in the doubled-real bounded operator lane.
-/
def IsDrazinCartanEigenOperator
    (H A B : EndH) (k : ℕ) (lam : ℝ) : Prop :=
  InfoGeometry.Canonical.Drazin.IsDrazinInverse A B k ∧
    IsCartanEigenOperator (E := E) H A lam

/-- Accessor: Drazin witness component. -/
theorem isDrazinInverse_of_isDrazinCartanEigenOperator
    {H A B : EndH} {k : ℕ} {lam : ℝ}
    (h : IsDrazinCartanEigenOperator (E := E) H A B k lam) :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse A B k :=
  h.1

/-- Accessor: Cartan eigen-operator component. -/
theorem isCartanEigenOperator_of_isDrazinCartanEigenOperator
    {H A B : EndH} {k : ℕ} {lam : ℝ}
    (h : IsDrazinCartanEigenOperator (E := E) H A B k lam) :
    IsCartanEigenOperator (E := E) H A lam :=
  h.2

/-- Drazin projection readback for a witness pair `(A,B)`. -/
def drazinProjection (A B : EndH) : EndH :=
  InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection A B

/-- Complementary Drazin projection readback for a witness pair `(A,B)`. -/
def drazinComplementaryProjection (A B : EndH) : EndH :=
  InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection A B

/-- Readback decomposition `P + Q = 1` for Drazin projectors. -/
theorem drazinProjection_add_complementaryProjection (A B : EndH) :
    drazinProjection (E := E) A B + drazinComplementaryProjection (E := E) A B =
      (ContinuousLinearMap.id ℝ H₂) := by
  simpa [drazinProjection, drazinComplementaryProjection] using
    (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_add_complementaryProjection
      (a := A) (b := B))

/-- Readback: Drazin projection is idempotent under a Drazin-Cartan witness. -/
theorem drazinProjection_is_idempotent_of_isDrazinCartanEigenOperator
    {H A B : EndH} {k : ℕ} {lam : ℝ}
    (h : IsDrazinCartanEigenOperator (E := E) H A B k lam) :
    drazinProjection (E := E) A B * drazinProjection (E := E) A B
      = drazinProjection (E := E) A B := by
  change
    InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection A B *
        InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection A B =
      InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection A B
  exact
    InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_is_idempotent
      (a := A) (b := B) h.1

/-- Readback: Drazin projection commutes with the owner operator under witness. -/
theorem drazinProjection_comm_self_of_isDrazinCartanEigenOperator
    {H A B : EndH} {k : ℕ} {lam : ℝ}
    (h : IsDrazinCartanEigenOperator (E := E) H A B k lam) :
    drazinProjection (E := E) A B * A = A * drazinProjection (E := E) A B := by
  change
    InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection A B * A =
      A * InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection A B
  exact
    InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_comm_self
      (a := A) (b := B) h.1

/--
Frame-transport statement schema: if a frame transports Cartan adjoint on `A`,
then Drazin-Cartan witness transports to the framed operator.
-/
theorem isDrazinCartanEigenOperator_conjugate
    {Hsrc Htgt U Uinv A B : EndH} {k : ℕ} {lam : ℝ}
    (h : IsDrazinCartanEigenOperator (E := E) Hsrc A B k lam)
    (hAconj :
      cartanAdjoint (E := E) Htgt ((U.comp A).comp Uinv)
        = (U.comp (cartanAdjoint (E := E) Hsrc A)).comp Uinv)
    (hBconj :
      InfoGeometry.Canonical.Drazin.IsDrazinInverse ((U.comp A).comp Uinv) ((U.comp B).comp Uinv) k) :
    IsDrazinCartanEigenOperator (E := E) Htgt ((U.comp A).comp Uinv) ((U.comp B).comp Uinv) k lam := by
  refine ⟨hBconj, ?_⟩
  exact cartanEigenOperator_conjugate (E := E) Hsrc Htgt U Uinv A lam hAconj h.2

/--
Readback transport schema for Drazin projectors under a Bogoliubov frame.

This theorem is intentionally hypothesis-driven: projector conjugation is supplied
explicitly as a certified transport identity, then reused as the canonical
readback bridge.
-/
theorem drazinProjection_conjugate_readback
    {U Uinv A B : EndH}
    (hprojConj :
      drazinProjection (E := E) ((U.comp A).comp Uinv) ((U.comp B).comp Uinv)
        = (U.comp (drazinProjection (E := E) A B)).comp Uinv) :
    drazinProjection (E := E) ((U.comp A).comp Uinv) ((U.comp B).comp Uinv)
      = (U.comp (drazinProjection (E := E) A B)).comp Uinv :=
  hprojConj

/--
Owner package: Drazin split + grading + real doubled Cl(1,1) atom data.

This package treats projectors/subspaces/gradings as canonical, while concrete
Bogoliubov frames are representatives.
-/
structure ChiralDrazinKreinPackage where
  A : EndH
  AD : EndH
  k : ℕ
  hDrazin : InfoGeometry.Canonical.Drazin.IsDrazinInverse A AD k
  ΓS : EndH
  J : EndH
  eps : EndH
  K : EndH
  form_preserved : ∀ x y : H₂, KreinSpace.kreinInner (H := H₂) (J x) (J y) = KreinSpace.kreinInner (H := H₂) x y
  drazin_split_compatible : J * drazinProjection A AD = drazinProjection A AD * J
  cl11_laws : eps * eps = 1 ∧ J * J = -1 ∧ eps * J = -J * eps

/--
A Bogoliubov frame represented over a fixed owner package.
-/
structure BogoliubovFrameOver (P : ChiralDrazinKreinPackage (E := E)) where
  U : EndH
  Uinv : EndH
  left_inv : Uinv.comp U = 1
  right_inv : U.comp Uinv = 1
  compatible_with_drazin_split : U * drazinProjection P.A P.AD = drazinProjection P.A P.AD * U
  compatible_with_phase_axis : U * P.J = P.J * U
  compatible_with_krein_form : ∀ x y : H₂, KreinSpace.kreinInner (H := H₂) (U x) (U y) = KreinSpace.kreinInner (H := H₂) x y

/--
Frame equivalence relation: existence of a structure-preserving automorphism
between representatives over the same owner package.
-/
def EquivalentBogoliubovFrames
    (P : ChiralDrazinKreinPackage (E := E))
    (F G : BogoliubovFrameOver (E := E) P) : Prop :=
  ∃ U : EndH,
    (U.comp (drazinProjection (E := E) P.A P.AD) =
      (drazinProjection (E := E) P.A P.AD).comp U) ∧
    (U.comp P.J = P.J.comp U) ∧
    (U.comp P.eps = P.eps.comp U) ∧
    (U.comp P.K = P.K.comp U) ∧
    (U.comp F.U = G.U)

namespace EquivalentBogoliubovFrames

variable {P : ChiralDrazinKreinPackage (E := E)}
variable {F G : BogoliubovFrameOver (E := E) P}

/-- Readback: frame equivalence carries a certified Drazin-projector commutation witness. -/
theorem preserves_drazinProjection_comm
    (hEq : EquivalentBogoliubovFrames (E := E) P F G) :
    ∃ U : EndH,
      U.comp (drazinProjection (E := E) P.A P.AD)
        = (drazinProjection (E := E) P.A P.AD).comp U := by
  rcases hEq with ⟨U, hP, _hJ, _hEps, _hK, _hFrame⟩
  exact ⟨U, hP⟩

/-- Readback: equivalent frames are linked by a certified representative action on frame maps. -/
theorem frame_action
    (hEq : EquivalentBogoliubovFrames (E := E) P F G) :
    ∃ U : EndH, U.comp F.U = G.U := by
  rcases hEq with ⟨U, _hP, _hJ, _hEps, _hK, hFrame⟩
  exact ⟨U, hFrame⟩

/--
Projected frame readout is invariant under equivalent Bogoliubov frames,
assuming the readout is invariant under certified Drazin-projector-preserving
representative actions.
-/
theorem projected_frame_readout_invariant
    (hEq : EquivalentBogoliubovFrames (E := E) P F G)
    (Φ : EndH → ℝ)
    (hpres :
      ∀ U X : EndH,
        U.comp (drazinProjection (E := E) P.A P.AD)
          = (drazinProjection (E := E) P.A P.AD).comp U →
        Φ (U.comp X) = Φ X) :
    Φ ((drazinProjection (E := E) P.A P.AD).comp G.U)
      = Φ ((drazinProjection (E := E) P.A P.AD).comp F.U) := by
  rcases hEq with ⟨U, hP, _hJ, _hEps, _hK, hFrame⟩
  have htransport :
      (drazinProjection (E := E) P.A P.AD).comp (U.comp F.U)
        = U.comp ((drazinProjection (E := E) P.A P.AD).comp F.U) := by
    simpa [ContinuousLinearMap.comp_assoc] using
      congrArg (fun T : EndH => T.comp F.U) hP.symm
  calc
    Φ ((drazinProjection (E := E) P.A P.AD).comp G.U)
        = Φ ((drazinProjection (E := E) P.A P.AD).comp (U.comp F.U)) := by
            simp [hFrame]
    _ = Φ (U.comp ((drazinProjection (E := E) P.A P.AD).comp F.U)) := by
          rw [htransport]
    _ = Φ ((drazinProjection (E := E) P.A P.AD).comp F.U) := by
          exact hpres U ((drazinProjection (E := E) P.A P.AD).comp F.U) hP

end EquivalentBogoliubovFrames

end Core

end DrazinBogoliubovFrameEquiv
