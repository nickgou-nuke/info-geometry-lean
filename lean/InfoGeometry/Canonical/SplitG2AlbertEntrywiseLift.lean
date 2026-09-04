import Mathlib
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Lie.SplitOctonionGogberashviliDerivationBridge
import InfoGeometry.Algebra.BaezF4H3Zorn

noncomputable section

namespace InfoGeometry.Canonical.SplitG2AlbertEntrywiseLift

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Lie.CanonicalZornDerivation

abbrev CZ := InfoGeometry.Lie.CanonicalZornDerivation.CZ
abbrev Zorn := ZornVectorMatrix ℝ
abbrev G2Der := canonicalZornDerivations
abbrev H3 := H3Zorn ℝ
abbrev EndH3 := Module.End ℝ H3

/-- Entrywise action of a canonical split-octonion derivation on the three
off-diagonal Zorn slots of the split Albert carrier.  The real diagonal is
fixed pointwise. -/
noncomputable def liftG2End (D : G2Der) : EndH3 where
  toFun X :=
    { α₁ := 0
      α₂ := 0
      α₃ := 0
      a := canonicalToVectorDerivation D X.a
      b := canonicalToVectorDerivation D X.b
      c := canonicalToVectorDerivation D X.c }
  map_add' X Y := by
    apply H3Zorn.ext_h3 <;>
      simp [canonicalToVectorDerivation, ZornVectorMatrix.add]
  map_smul' r X := by
    apply H3Zorn.ext_h3 <;>
      simp [canonicalToVectorDerivation, ZornVectorMatrix.smul]

/-- The entrywise lift is linear in the derivation parameter. -/
noncomputable def liftG2Linear : G2Der →ₗ[ℝ] EndH3 where
  toFun := liftG2End
  map_add' D E := by
    apply LinearMap.ext
    intro X
    apply H3Zorn.ext_h3 <;>
      simp [liftG2End, canonicalToVectorDerivation]
  map_smul' r D := by
    apply LinearMap.ext
    intro X
    apply H3Zorn.ext_h3 <;>
      simp [liftG2End, canonicalToVectorDerivation]

/-- The lifted `G2` action annihilates all three primitive diagonal
idempotents used throughout the split-Albert development. -/
theorem liftG2End_annihilates_diag₁ (D : G2Der) :
    liftG2End D h3_diag₁ = 0 := by
  apply H3Zorn.ext_h3 <;>
    simp [liftG2End, h3_diag₁, canonicalToVectorDerivation,
      ZornVectorMatrix.zero]

theorem liftG2End_annihilates_diag₂ (D : G2Der) :
    liftG2End D h3_diag₂ = 0 := by
  apply H3Zorn.ext_h3 <;>
    simp [liftG2End, h3_diag₂, canonicalToVectorDerivation,
      ZornVectorMatrix.zero]

theorem liftG2End_annihilates_diag₃ (D : G2Der) :
    liftG2End D h3_diag₃ = 0 := by
  apply H3Zorn.ext_h3 <;>
    simp [liftG2End, h3_diag₃, canonicalToVectorDerivation,
      ZornVectorMatrix.zero]

/-- Uniform finite-index idempotent readout. -/
theorem liftG2End_annihilates_idempotents (D : G2Der) (i : Fin 3) :
    liftG2End D
      (match i.1 with
       | 0 => h3_diag₁
       | 1 => h3_diag₂
       | _ => h3_diag₃) = 0 := by
  fin_cases i
  · exact liftG2End_annihilates_diag₁ D
  · exact liftG2End_annihilates_diag₂ D
  · exact liftG2End_annihilates_diag₃ D

/-- The entrywise lift is faithful.  Evaluating on one off-diagonal slot
recovers the original canonical derivation after transport through the native
Zorn linear equivalence. -/
theorem liftG2Linear_injective : Function.Injective liftG2Linear := by
  intro D E hDE
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  apply InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.injective
  let probe : H3 :=
    { α₁ := 0, α₂ := 0, α₃ := 0
      a := InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv X
      b := 0, c := 0 }
  have hp := LinearMap.congr_fun hDE probe
  have ha := congrArg (fun Y : H3 => Y.a) hp
  simpa [liftG2Linear, liftG2End, probe,
    canonicalToVectorDerivation_apply] using ha

/-- The entrywise lift preserves the Lie bracket at the endomorphism level. -/
theorem liftG2End_map_lie (D E : G2Der) :
    liftG2End ⁅D, E⁆ = ⁅liftG2End D, liftG2End E⁆ := by
  apply LinearMap.ext
  intro X
  apply H3Zorn.ext_h3
  · simp [liftG2End, Ring.lie_def]
  · simp [liftG2End, Ring.lie_def]
  · simp [liftG2End, Ring.lie_def]
  · change
      canonicalToVectorDerivation ⁅D, E⁆ X.a =
        canonicalToVectorDerivation D (canonicalToVectorDerivation E X.a) -
          canonicalToVectorDerivation E (canonicalToVectorDerivation D X.a)
    have h :=
      (vectorCanonicalLieEquiv.symm.map_lie D E)
    exact congrArg (fun K => K X.a) h
  · change
      canonicalToVectorDerivation ⁅D, E⁆ X.b =
        canonicalToVectorDerivation D (canonicalToVectorDerivation E X.b) -
          canonicalToVectorDerivation E (canonicalToVectorDerivation D X.b)
    have h :=
      (vectorCanonicalLieEquiv.symm.map_lie D E)
    exact congrArg (fun K => K X.b) h
  · change
      canonicalToVectorDerivation ⁅D, E⁆ X.c =
        canonicalToVectorDerivation D (canonicalToVectorDerivation E X.c) -
          canonicalToVectorDerivation E (canonicalToVectorDerivation D X.c)
    have h :=
      (vectorCanonicalLieEquiv.symm.map_lie D E)
    exact congrArg (fun K => K X.c) h

/-- Faithful Lie representation of split `G2(2)` on the split-Albert carrier
before imposing the Jordan-derivation landing condition. -/
noncomputable def liftG2LieHom : G2Der →ₗ⁅ℝ⁆ EndH3 :=
  { liftG2Linear with
    map_lie' := liftG2End_map_lie }

@[simp] theorem liftG2LieHom_injective : Function.Injective liftG2LieHom :=
  liftG2Linear_injective

/-- The range of the faithful entrywise action has the expected dimension 14. -/
theorem liftG2LieHom_range_finrank :
    Module.finrank ℝ (LinearMap.range liftG2LieHom) = 14 := by
  let e : G2Der ≃ₗ[ℝ] LinearMap.range liftG2LieHom :=
    LinearEquiv.ofInjective liftG2LieHom liftG2LieHom_injective
  calc
    Module.finrank ℝ (LinearMap.range liftG2LieHom) =
        Module.finrank ℝ G2Der := e.finrank_eq.symm
    _ = 14 :=
      InfoGeometry.Lie.CanonicalZornDerivationDimension.finrank_canonicalZornDerivations

/-- The only additional compatibility needed to land the entrywise action in
the native split-Albert `F4` derivation algebra.  This is deliberately a
soldering datum rather than an unproved theorem. -/
structure G2F4Soldering where
  jordan : ∀ D : G2Der, H3ZornJordanDerivation (liftG2End D)

/-- A supplied Jordan-compatibility soldering upgrades the faithful entrywise
representation to a genuine Lie homomorphism into the native `F4` derivation
subalgebra. -/
noncomputable def g2ToF4LieHom (S : G2F4Soldering) :
    G2Der →ₗ⁅ℝ⁆ H3ZornF4Derivations where
  toLinearMap :=
    { toFun := fun D => ⟨liftG2End D, S.jordan D⟩
      map_add' := by
        intro D E
        apply Subtype.ext
        exact liftG2Linear.map_add D E
      map_smul' := by
        intro r D
        apply Subtype.ext
        exact liftG2Linear.map_smul r D }
  map_lie' := by
    intro D E
    apply Subtype.ext
    exact liftG2End_map_lie D E

/-- The soldered `G2 -> F4` map remains injective. -/
theorem g2ToF4LieHom_injective (S : G2F4Soldering) :
    Function.Injective (g2ToF4LieHom S) := by
  intro D E h
  apply liftG2LieHom_injective
  apply LinearMap.ext
  intro X
  have h' := congrArg Subtype.val h
  exact LinearMap.congr_fun h' X

/-- Hence the soldered diagonal `G2` subalgebra inside `F4` has finrank 14. -/
theorem g2ToF4_range_finrank (S : G2F4Soldering) :
    Module.finrank ℝ (LinearMap.range (g2ToF4LieHom S)) = 14 := by
  let e : G2Der ≃ₗ[ℝ] LinearMap.range (g2ToF4LieHom S) :=
    LinearEquiv.ofInjective (g2ToF4LieHom S) (g2ToF4LieHom_injective S)
  calc
    Module.finrank ℝ (LinearMap.range (g2ToF4LieHom S)) =
        Module.finrank ℝ G2Der := e.finrank_eq.symm
    _ = 14 :=
      InfoGeometry.Lie.CanonicalZornDerivationDimension.finrank_canonicalZornDerivations

end InfoGeometry.Canonical.SplitG2AlbertEntrywiseLift
