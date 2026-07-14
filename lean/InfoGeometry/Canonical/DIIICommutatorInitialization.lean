import InfoGeometry.Canonical.RealBdG
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.DIIICommutatorInitialization

Symbol-first initialization surface for DIII operator constraints on the doubled
real carrier.

This file is intentionally thin:

- it defines commutator/anticommutator operators on endomorphisms,
- it packages the DIII algebra as a typeclass,
- and it provides a constructor theorem from the two core constraints
  `[T, H] = 0` and `{P, H} = 0`.

No physical narrative is used as proof evidence; only operator identities.
-/

namespace DIIICommutatorInitialization

open InfoGeometry.Canonical.RealBdG
open InfoGeometry.Krein

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Endomorphism commutator `[A,B] = AB - BA` on the doubled carrier. -/
noncomputable def endCommutator (A B : EndH) : EndH :=
  A.comp B - B.comp A

/-- Endomorphism anticommutator `{A,B} = AB + BA` on the doubled carrier. -/
noncomputable def endAnticommutator (A B : EndH) : EndH :=
  A.comp B + B.comp A

/--
Operator-level DIII initialization package.

`T` and `P` satisfy the Clifford signatures, while `H` is constrained by
the commutator/anticommutator laws and induced chiral product `C = T ∘ P`.
-/
class TopologicalClassDIII (H T P : EndH) : Prop where
  T_squared : T.comp T = -(ContinuousLinearMap.id ℝ H₂)
  P_squared : P.comp P = ContinuousLinearMap.id ℝ H₂
  T_commutes : T.comp H = H.comp T
  P_anticommutes : P.comp H = -(H.comp P)
  C_definition : ∃ C : EndH, C = T.comp P ∧ C.comp H = -(H.comp C)

/-- Class law `[T,H]=0` in explicit commutator form. -/
@[rep_depth transport]
theorem commutator_T_H_eq_zero
    {H T P : EndH}
    [hDIII : TopologicalClassDIII (E := E) H T P] :
    endCommutator T H = 0 := by
  simpa [endCommutator] using (sub_eq_zero.mpr hDIII.T_commutes)

/-- Class law `{P,H}=0` in explicit anticommutator form. -/
@[rep_depth transport]
theorem anticommutator_P_H_eq_zero
    {H T P : EndH}
    [hDIII : TopologicalClassDIII (E := E) H T P] :
    endAnticommutator P H = 0 := by
  unfold endAnticommutator
  calc
    P.comp H + H.comp P = -(H.comp P) + H.comp P := by
      rw [hDIII.P_anticommutes]
    _ = 0 := by
      abel

/-- The induced chiral witness is available as an explicit existential theorem. -/
@[rep_depth transport]
theorem chiral_witness_exists
    {H T P : EndH}
    [hDIII : TopologicalClassDIII (E := E) H T P] :
    ∃ C : EndH, C = T.comp P ∧ C.comp H = -(H.comp C) :=
  hDIII.C_definition

/--
Constructor theorem: if `T²=-1`, `P²=1`, `[T,H]=0`, and `{P,H}=0`, then the
full DIII package is forced.
-/
@[rep_depth transport]
theorem topologicalClassDIII_of_commutation_data
    (H T P : EndH)
    (hTsq : T.comp T = -(ContinuousLinearMap.id ℝ H₂))
    (hPsq : P.comp P = ContinuousLinearMap.id ℝ H₂)
    (hTH : T.comp H = H.comp T)
    (hPH : P.comp H = -(H.comp P)) :
    TopologicalClassDIII (E := E) H T P := by
  refine ⟨hTsq, hPsq, hTH, hPH, ?_⟩
  refine ⟨T.comp P, rfl, ?_⟩
  calc
    (T.comp P).comp H = T.comp (P.comp H) := by
      simp [ContinuousLinearMap.comp_assoc]
    _ = T.comp (-(H.comp P)) := by
      rw [hPH]
    _ = -(T.comp (H.comp P)) := by
      simp
    _ = -((T.comp H).comp P) := by
      simp [ContinuousLinearMap.comp_assoc]
    _ = -((H.comp T).comp P) := by
      rw [hTH]
    _ = -(H.comp (T.comp P)) := by
      simp [ContinuousLinearMap.comp_assoc]

section Bridge

variable [CompleteSpace E]

/--
Bridge constructor from the real BdG datum to DIII constraints with
`T := K = J ∘ ε` and `P := J`, assuming the datum's chiral lane is `J`.
-/
@[rep_depth transport]
theorem topologicalClassDIII_of_realBdGDatum
    (X : RealBdGDatum (E := E))
    (hChiral : X.chiral = modular_j (E := E)) :
    TopologicalClassDIII (E := E) X.H (modularK (E := E)) (modular_j (E := E)) := by
  have hTH : (modularK (E := E)).comp X.H = X.H.comp (modularK (E := E)) := by
    simpa [KLinear] using X.H_KLinear.symm
  have hPH : (modular_j (E := E)).comp X.H = -(X.H.comp (modular_j (E := E))) := by
    calc
      (modular_j (E := E)).comp X.H = X.chiral.comp X.H := by
        simp [hChiral]
      _ = -(X.H.comp X.chiral) := X.H_chiral
      _ = -(X.H.comp (modular_j (E := E))) := by
        simp [hChiral]
  exact topologicalClassDIII_of_commutation_data
    (E := E) X.H (modularK (E := E)) (modular_j (E := E))
    (modularK_sq (E := E))
    (modular_j_involution (E := E))
    hTH hPH

end Bridge

end Core

end DIIICommutatorInitialization
