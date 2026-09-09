import Mathlib
import InfoGeometry.Algebra.BaezF4H3Zorn
import InfoGeometry.Algebra.H3ZornCarrierBasis
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.SplitOctonionStandardDerivation

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

namespace InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionStandardDerivation

abbrev G2Derivation := canonicalZornDerivations
abbrev VectorZorn := InfoGeometry.Algebra.ZornVectorMatrix ℝ
abbrev H3 := H3Zorn ℝ

/-- Apply a canonical split-octonion derivation entrywise to the three
off-diagonal Peirce slots of `H3Zorn`, while killing the real diagonal. -/
noncomputable def liftG2End (D : G2Derivation) : Module.End ℝ H3 where
  toFun X :=
    { α₁ := 0
      α₂ := 0
      α₃ := 0
      a := canonicalToVectorDerivation D X.a
      b := canonicalToVectorDerivation D X.b
      c := canonicalToVectorDerivation D X.c }
  map_add' X Y := by
    apply H3Zorn.ext_h3 <;>
      simp [H3Zorn.add_readback, canonicalToVectorDerivation]
  map_smul' r X := by
    apply H3Zorn.ext_h3 <;>
      simp [H3Zorn.smul_readback, canonicalToVectorDerivation]

@[simp] theorem liftG2End_alpha1 (D : G2Derivation) (X : H3) :
    (liftG2End D X).α₁ = 0 := rfl

@[simp] theorem liftG2End_alpha2 (D : G2Derivation) (X : H3) :
    (liftG2End D X).α₂ = 0 := rfl

@[simp] theorem liftG2End_alpha3 (D : G2Derivation) (X : H3) :
    (liftG2End D X).α₃ = 0 := rfl

@[simp] theorem liftG2End_a (D : G2Derivation) (X : H3) :
    (liftG2End D X).a = canonicalToVectorDerivation D X.a := rfl

@[simp] theorem liftG2End_b (D : G2Derivation) (X : H3) :
    (liftG2End D X).b = canonicalToVectorDerivation D X.b := rfl

@[simp] theorem liftG2End_c (D : G2Derivation) (X : H3) :
    (liftG2End D X).c = canonicalToVectorDerivation D X.c := rfl

/-- The three primitive diagonal idempotents, packaged as one finite family. -/
def peirceIdempotent : Fin 3 → H3 :=
  ![h3_diag₁, h3_diag₂, h3_diag₃]

/-- Entrywise split-octonion derivations annihilate every primitive diagonal
idempotent. -/
@[simp] theorem liftG2End_peirceIdempotent
    (D : G2Derivation) (i : Fin 3) :
    liftG2End D (peirceIdempotent i) = 0 := by
  fin_cases i <;>
    change liftG2End D
      { α₁ := _, α₂ := _, α₃ := _,
        a := (0 : VectorZorn), b := 0, c := 0 } = 0
  · have hz : (⟨0, 0, (fun _ : Fin 3 => 0), (fun _ : Fin 3 => 0)⟩ :
        InfoGeometry.Canonical.ZornMatrix ℝ) = 0 := by rfl
    have hDzero : (D.1) (⟨0, 0, (fun _ : Fin 3 => 0), (fun _ : Fin 3 => 0)⟩ :
        InfoGeometry.Canonical.ZornMatrix ℝ) = 0 := by
      rw [hz]
      exact D.1.map_zero
    simp [liftG2End, hz, hDzero, canonicalToVectorDerivation_zero,
      canonicalZornDerivation_map_zero,
      canonicalVectorEquiv_symm_zero, H3Zorn.zero_readback,
      canonicalVectorEquiv_symm_zero_record, ZornVectorMatrix.zero]
    funext i
    rfl
  · have hz : (⟨0, 0, (fun _ : Fin 3 => 0), (fun _ : Fin 3 => 0)⟩ :
        InfoGeometry.Canonical.ZornMatrix ℝ) = 0 := by rfl
    have hDzero : (D.1) (⟨0, 0, (fun _ : Fin 3 => 0), (fun _ : Fin 3 => 0)⟩ :
        InfoGeometry.Canonical.ZornMatrix ℝ) = 0 := by
      rw [hz]
      exact D.1.map_zero
    simp [liftG2End, hz, hDzero, canonicalToVectorDerivation_zero,
      canonicalZornDerivation_map_zero,
      canonicalVectorEquiv_symm_zero, H3Zorn.zero_readback,
      canonicalVectorEquiv_symm_zero_record, ZornVectorMatrix.zero]
    funext i
    rfl
  · have hz : (⟨0, 0, (fun _ : Fin 3 => 0), (fun _ : Fin 3 => 0)⟩ :
        InfoGeometry.Canonical.ZornMatrix ℝ) = 0 := by rfl
    have hDzero : (D.1) (⟨0, 0, (fun _ : Fin 3 => 0), (fun _ : Fin 3 => 0)⟩ :
        InfoGeometry.Canonical.ZornMatrix ℝ) = 0 := by
      rw [hz]
      exact D.1.map_zero
    simp [liftG2End, hz, hDzero, canonicalToVectorDerivation_zero,
      canonicalZornDerivation_map_zero,
      canonicalVectorEquiv_symm_zero, H3Zorn.zero_readback,
      canonicalVectorEquiv_symm_zero_record, ZornVectorMatrix.zero]
    funext i
    rfl

/-- Entrywise lifting is additive in the derivation parameter. -/
theorem liftG2End_add (D E : G2Derivation) :
    liftG2End (D + E) = liftG2End D + liftG2End E := by
  have hD := (vectorCanonicalLinearEquiv.symm).map_add D E
  apply LinearMap.ext
  intro X
  apply H3Zorn.ext_h3 <;>
    simp [liftG2End, H3Zorn.add_readback, LinearMap.add_apply, map_add, hD] <;> try rfl

/-- Entrywise lifting is homogeneous in the derivation parameter. -/
theorem liftG2End_smul (r : ℝ) (D : G2Derivation) :
    liftG2End (r • D) = r • liftG2End D := by
  have hD := (vectorCanonicalLinearEquiv.symm).map_smul r D
  apply LinearMap.ext
  intro X
  apply H3Zorn.ext_h3 <;>
    simp [liftG2End, H3Zorn.smul_readback, LinearMap.smul_apply, map_smul, hD] <;> try rfl
  all_goals
    apply H3Zorn.ext_h3
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · rfl

@[simp] theorem liftG2End_zero :
    liftG2End (0 : G2Derivation) = 0 := by
  apply LinearMap.ext
  intro X
  apply H3Zorn.ext_h3 <;>
    simp [liftG2End, canonicalToVectorDerivation_apply,
      ZornVectorMatrix.zero]
  all_goals
    funext i
    rfl

/-- The entrywise action remembers the original split-octonion derivation.
It is enough to test the `(1,2)` Peirce slot. -/
theorem liftG2End_injective : Function.Injective liftG2End := by
  intro D E hDE
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  apply canonicalVectorEquiv.injective
  let X : H3 :=
    { α₁ := 0, α₂ := 0, α₃ := 0
      a := canonicalVectorEquiv z
      b := 0
      c := 0 }
  have hX := LinearMap.congr_fun hDE X
  have ha := congrArg (fun Y : H3 => Y.a) hX
  simpa [X, liftG2End, canonicalToVectorDerivation_apply] using ha

theorem canonicalToVectorDerivation_lie (D E : G2Derivation) :
    canonicalToVectorDerivation ⁅D, E⁆ =
      ⁅canonicalToVectorDerivation D, canonicalToVectorDerivation E⁆ := by
  apply ZornVectorMatrix.Derivation.ext
  intro X
  apply canonicalVectorEquiv.symm.injective
  simp only [canonicalToVectorDerivation_apply,
    LieRing.of_associative_ring_bracket, Subtype.coe_mk,
    LinearMap.sub_apply, Module.End.mul_apply]
  rfl

/-- Entrywise lifting commutes exactly with the Lie commutator. -/
theorem liftG2End_lie (D E : G2Derivation) :
    liftG2End ⁅D, E⁆ = ⁅liftG2End D, liftG2End E⁆ := by
  have hDE := canonicalToVectorDerivation_lie D E
  apply LinearMap.ext
  intro X
  have ha := congrArg (fun d : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ) => d X.a) hDE
  have hb := congrArg (fun d : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ) => d X.b) hDE
  have hc := congrArg (fun d : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ) => d X.c) hDE
  have hD1 : ∀ Y : H3, (liftG2End D Y).α₁ = 0 := fun Y => rfl
  have hD2 : ∀ Y : H3, (liftG2End D Y).α₂ = 0 := fun Y => rfl
  have hD3 : ∀ Y : H3, (liftG2End D Y).α₃ = 0 := fun Y => rfl
  have hE1 : ∀ Y : H3, (liftG2End E Y).α₁ = 0 := fun Y => rfl
  have hE2 : ∀ Y : H3, (liftG2End E Y).α₂ = 0 := fun Y => rfl
  have hE3 : ∀ Y : H3, (liftG2End E Y).α₃ = 0 := fun Y => rfl
  refine H3Zorn.ext_h3 _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [LieRing.of_associative_ring_bracket]
    change (liftG2End ⁅D, E⁆ X).α₁ =
      (liftG2End D (liftG2End E X) - liftG2End E (liftG2End D X)).α₁
    simp [liftG2End, H3Zorn.sub_readback]
  · rw [LieRing.of_associative_ring_bracket]
    change (liftG2End ⁅D, E⁆ X).α₂ =
      (liftG2End D (liftG2End E X) - liftG2End E (liftG2End D X)).α₂
    simp [liftG2End, H3Zorn.sub_readback]
  · rw [LieRing.of_associative_ring_bracket]
    change (liftG2End ⁅D, E⁆ X).α₃ =
      (liftG2End D (liftG2End E X) - liftG2End E (liftG2End D X)).α₃
    simp [liftG2End, H3Zorn.sub_readback]
  · simpa [liftG2End, canonicalToVectorDerivation_apply,
      LieRing.of_associative_ring_bracket] using ha
  · simpa [liftG2End, canonicalToVectorDerivation_apply,
      LieRing.of_associative_ring_bracket] using hb
  · simpa [liftG2End, canonicalToVectorDerivation_apply,
      LieRing.of_associative_ring_bracket] using hc

/-- The unconditional entrywise representation into ambient `H3Zorn`
endomorphisms.  No Jordan-product compatibility is assumed here. -/
noncomputable def g2EntrywiseLieHom :
    G2Derivation →ₗ⁅ℝ⁆ Module.End ℝ H3 where
  toFun := liftG2End
  map_add' := liftG2End_add
  map_smul' := liftG2End_smul
  map_lie' := by
    intro D E
    exact liftG2End_lie D E

/-- The raw entrywise Lie representation is faithful. -/
theorem g2EntrywiseLieHom_injective :
    Function.Injective g2EntrywiseLieHom :=
  by
    intro D E h
    exact liftG2End_injective h

/-- Exact remaining compatibility condition for the desired `G2 -> F4`
embedding: the entrywise action must satisfy the installed H3 Jordan Leibniz
rule.  Isolating this predicate prevents the classical statement from being
smuggled in as an axiom. -/
def EntrywiseJordanCompatible (D : G2Derivation) : Prop :=
  H3ZornJordanDerivation (liftG2End D)

/-- The derivations for which the entrywise action is already certified as an
H3 Jordan derivation form a Lie subalgebra of the native split `G2` carrier. -/
noncomputable def entrywiseCompatibleG2 : LieSubalgebra ℝ G2Derivation where
  carrier := {D | EntrywiseJordanCompatible D}
  zero_mem' := by
    change H3ZornJordanDerivation (liftG2End (0 : G2Derivation))
    rw [liftG2End_zero]
    exact zero_H3ZornJordanDerivation
  add_mem' := by
    intro D E hD hE
    change H3ZornJordanDerivation (liftG2End (D + E))
    rw [liftG2End_add]
    exact H3ZornF4Derivations.add_mem hD hE
  smul_mem' := by
    intro r D hD
    change H3ZornJordanDerivation
      (liftG2End ((r : ℝ) • (D : G2Derivation)))
    rw [liftG2End_smul]
    exact H3ZornF4Derivations.smul_mem r hD
  lie_mem' := by
    intro D E hD hE
    change H3ZornJordanDerivation (liftG2End ⁅D, E⁆)
    rw [liftG2End_lie]
    exact H3ZornF4Derivations.lie_mem hD hE

/-- On the theorem-safe compatible subalgebra, the classical entrywise action
is a genuine Lie homomorphism into the native split-Albert derivation algebra. -/
noncomputable def compatibleG2ToF4LieHom :
    entrywiseCompatibleG2 →ₗ⁅ℝ⁆ H3ZornF4Derivations where
  toFun D := ⟨liftG2End D.1, D.2⟩
  map_add' D E := by
    apply Subtype.ext
    exact liftG2End_add D.1 E.1
  map_smul' r D := by
    apply Subtype.ext
    exact liftG2End_smul r D.1
  map_lie' := by
    intro D E
    apply Subtype.ext
    exact liftG2End_lie D.1 E.1

/-- The compatible `G2 -> F4` Lie map is injective. -/
theorem compatibleG2ToF4LieHom_injective :
    Function.Injective compatibleG2ToF4LieHom := by
  intro D E h
  apply Subtype.ext
  apply liftG2End_injective
  exact congrArg Subtype.val h

/-- The constructive standard-derivation theorem already proves that the
native split-octonion derivation carrier has no missing linear directions. -/
theorem standard_derivations_generate_all_g2 :
    standardDerivationSpan = ⊤ :=
  standardDerivations_span_top

/-- Closing this single theorem upgrades `compatibleG2ToF4LieHom` to the full
native split `G2` carrier. -/
def FullEntrywiseG2F4Compatibility : Prop :=
  entrywiseCompatibleG2 = ⊤

end InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding
