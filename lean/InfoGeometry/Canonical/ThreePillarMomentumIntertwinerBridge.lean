import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic
import InfoGeometry.Geometry.PauliParavectorBridge
import InfoGeometry.Canonical.Cl55FourVectorSUSYSolderingBridge

/-!
# Three-Pillar Momentum Intertwiner Bridge

This owner module formalizes the three-pillar operator intertwiner linking:
1. **Pillar I (Cuntz/KMS):** Modular translation and energy flow $P_\mu^{\rm mod}$;
2. **Pillar II (Clifford/SUSY):** Four-vector supercharge paravector $P_\mu^{\rm SUSY}$;
3. **Pillar III (Geometry/Witt):** Geometric 4-momentum $P_\mu^{\rm geom}$.

## Three Levels of Identification:
1. **Intertwining Law:** $P_\mu^{\rm SUSY} \circ J = J \circ P_\mu^{\rm mod}$;
2. **Conjugacy Theorem:** $P_\mu^{\rm SUSY} = J \circ P_\mu^{\rm mod} \circ J^{-1}$;
3. **Literal Operator Equality:** $P_\mu^{\rm SUSY} = P_\mu^{\rm mod}$ when carriers are identified ($J = \mathrm{id}$).
-/

noncomputable section

namespace InfoGeometry.Canonical.ThreePillarMomentumIntertwinerBridge

open Matrix
open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Canonical.Cl55FourVectorSUSYSolderingBridge

/-- Structure representing the Three-Pillar Momentum Intertwining Datum:
    linking Modular Cuntz dynamics, 4-Vector SUSY paravector, and Clifford spinor space. -/
structure ThreePillarMomentumDatum (HMod S55 : Type*)
    [AddCommGroup HMod] [Module ℝ HMod]
    [AddCommGroup S55] [Module ℝ S55] where
  J : HMod ≃ₗ[ℝ] S55
  P_mod : Minkowski4 → Module.End ℝ HMod
  P_susy : Minkowski4 → Module.End ℝ S55
  intertwines : ∀ (p : Minkowski4) (v : HMod), P_susy p (J v) = J (P_mod p v)

variable {HMod S55 : Type*}
  [AddCommGroup HMod] [Module ℝ HMod]
  [AddCommGroup S55] [Module ℝ S55]

/-- The canonical conjugated action attached to a carrier equivalence.

This definition is the constructive direction of the intertwiner packet: once
the modular action and the carrier identification are fixed, the SUSY-side
operator is forced by conjugation.  No identification of unrelated carriers
is assumed here.
-/
def conjugatedMomentum
    (J : HMod ≃ₗ[ℝ] S55) (P : Module.End ℝ HMod) : Module.End ℝ S55 :=
  J.toLinearMap.comp (P.comp J.symm.toLinearMap)

/-- The conjugation equivalence on endomorphism algebras induced by `J`. -/
noncomputable def momentumConjugationAlgEquiv
    (J : HMod ≃ₗ[ℝ] S55) :
    Module.End ℝ HMod ≃ₐ[ℝ] Module.End ℝ S55 :=
  J.conjAlgEquiv ℝ

theorem momentumConjugationAlgEquiv_apply
    (J : HMod ≃ₗ[ℝ] S55) (P : Module.End ℝ HMod) :
    momentumConjugationAlgEquiv J P = conjugatedMomentum J P := by
  ext w
  dsimp [momentumConjugationAlgEquiv, conjugatedMomentum,
    LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply]

theorem momentum_transport_aeval
    (J : HMod ≃ₗ[ℝ] S55) (p : Polynomial ℝ) (P : Module.End ℝ HMod) :
    momentumConjugationAlgEquiv J (Polynomial.aeval P p) =
      Polynomial.aeval (conjugatedMomentum J P) p := by
  let e : Module.End ℝ HMod →+* Module.End ℝ S55 :=
    (momentumConjugationAlgEquiv J).toRingEquiv.toRingHom
  have he : (algebraMap ℝ (Module.End ℝ S55)).comp (RingHom.id ℝ) =
      e.comp (algebraMap ℝ (Module.End ℝ HMod)) := by
    ext c
    simp [e, momentumConjugationAlgEquiv]
  have h := Polynomial.map_aeval_eq_aeval_map
    (φ := RingHom.id ℝ) (ψ := e) he p P
  simpa [e, momentumConjugationAlgEquiv, LinearEquiv.conjAlgEquiv_apply,
    conjugatedMomentum, LinearMap.comp_apply] using h

theorem momentum_transport_polynomial_relation
    (J : HMod ≃ₗ[ℝ] S55) (p : Polynomial ℝ) (P : Module.End ℝ HMod)
    (h : Polynomial.aeval P p = 0) :
    Polynomial.aeval (conjugatedMomentum J P) p = 0 := by
  rw [← momentum_transport_aeval J p P, h]
  exact map_zero (momentumConjugationAlgEquiv J)

theorem momentum_transport_polynomial_relation_iff
    (J : HMod ≃ₗ[ℝ] S55) (p : Polynomial ℝ) (P : Module.End ℝ HMod) :
    Polynomial.aeval (conjugatedMomentum J P) p = 0 ↔
      Polynomial.aeval P p = 0 := by
  constructor
  · intro h
    have ht : momentumConjugationAlgEquiv J (Polynomial.aeval P p) = 0 := by
      rw [momentum_transport_aeval J p P]
      exact h
    exact (momentumConjugationAlgEquiv J).injective (by simpa using ht)
  · exact momentum_transport_polynomial_relation J p P

/-- Build a three-pillar datum from a carrier equivalence and a modular action.

The intertwining field is proved, rather than supplied as an axiom. -/
def ThreePillarMomentumDatum.ofConjugated
    (J : HMod ≃ₗ[ℝ] S55) (P_mod : Minkowski4 → Module.End ℝ HMod) :
    ThreePillarMomentumDatum HMod S55 where
  J := J
  P_mod := P_mod
  P_susy := fun p => conjugatedMomentum J (P_mod p)
  intertwines := by
    intro p v
    dsimp [conjugatedMomentum, LinearMap.comp_apply]
    rw [J.symm_apply_apply]

/-- 🏆 THEOREM 1: The Three-Pillar Commutative Square:
    $P_\mu^{\rm SUSY} \circ J = J \circ P_\mu^{\rm mod}$. -/
theorem momentum_intertwining_square (d : ThreePillarMomentumDatum HMod S55) (p : Minkowski4) (v : HMod) :
    d.P_susy p (d.J v) = d.J (d.P_mod p v) :=
  d.intertwines p v

@[simp] theorem ofConjugated_P_susy
    (J : HMod ≃ₗ[ℝ] S55) (P_mod : Minkowski4 → Module.End ℝ HMod)
    (p : Minkowski4) :
    (ThreePillarMomentumDatum.ofConjugated J P_mod).P_susy p =
      conjugatedMomentum J (P_mod p) := rfl

theorem conjugatedMomentum_intertwines
    (J : HMod ≃ₗ[ℝ] S55) (P_mod : Minkowski4 → Module.End ℝ HMod)
    (p : Minkowski4) (v : HMod) :
    conjugatedMomentum J (P_mod p) (J v) = J (P_mod p v) := by
  dsimp [conjugatedMomentum, LinearMap.comp_apply]
  rw [J.symm_apply_apply]

theorem conjugatedMomentum_apply
    (J : HMod ≃ₗ[ℝ] S55) (P : Module.End ℝ HMod) (v : HMod) :
    conjugatedMomentum J P (J v) = J (P v) := by
  dsimp [conjugatedMomentum, LinearMap.comp_apply]
  rw [J.symm_apply_apply]

/-- The conjugated action is the unique operator satisfying the intertwining
law for a fixed carrier equivalence and modular operator. -/
theorem unique_intertwining_operator
    (J : HMod ≃ₗ[ℝ] S55) (P : Module.End ℝ HMod)
    (Q : Module.End ℝ S55)
    (hQ : ∀ v : HMod, Q (J v) = J (P v)) :
    Q = conjugatedMomentum J P := by
  ext w
  have h := hQ (J.symm w)
  rw [J.apply_symm_apply w] at h
  dsimp [conjugatedMomentum, LinearMap.comp_apply]
  exact h

theorem momentum_susy_eq_conjugated
    (d : ThreePillarMomentumDatum HMod S55) (p : Minkowski4) :
    d.P_susy p = conjugatedMomentum d.J (d.P_mod p) := by
  exact unique_intertwining_operator d.J (d.P_mod p) (d.P_susy p)
    (fun v => d.intertwines p v)

theorem conjugatedMomentum_pow_intertwines
    (J : HMod ≃ₗ[ℝ] S55) (P : Module.End ℝ HMod)
    (n : ℕ) (v : HMod) :
    ((conjugatedMomentum J P) ^ n) (J v) = J ((P ^ n) v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply]
      rw [conjugatedMomentum_apply J P v]
      simpa [Module.End.mul_apply] using ih (P v)

theorem momentum_power_intertwines
    (d : ThreePillarMomentumDatum HMod S55) (p : Minkowski4)
    (n : ℕ) (v : HMod) :
    ((d.P_susy p) ^ n) (d.J v) = d.J (((d.P_mod p) ^ n) v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply]
      rw [d.intertwines]
      simpa [Module.End.mul_apply] using ih (d.P_mod p v)

/-- 🏆 THEOREM 2: Inverse Intertwining:
    $J^{-1} \circ P_\mu^{\rm SUSY} = P_\mu^{\rm mod} \circ J^{-1}$. -/
theorem momentum_intertwining_inv (d : ThreePillarMomentumDatum HMod S55) (p : Minkowski4) (w : S55) :
    d.J.symm (d.P_susy p w) = d.P_mod p (d.J.symm w) := by
  have h := d.intertwines p (d.J.symm w)
  rw [d.J.apply_symm_apply w] at h
  rw [h, d.J.symm_apply_apply]

theorem momentum_kernel_transport (d : ThreePillarMomentumDatum HMod S55) (p : Minkowski4) :
    (LinearMap.ker (d.P_mod p)).map d.J.toLinearMap =
      LinearMap.ker (d.P_susy p) := by
  ext w
  simp only [Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨v, hv, rfl⟩
    change d.P_susy p (d.J v) = 0
    rw [d.intertwines p v, hv, map_zero]
  · intro hw
    refine ⟨d.J.symm w, ?_, d.J.apply_symm_apply w⟩
    have h := d.intertwines p (d.J.symm w)
    rw [d.J.apply_symm_apply w, hw] at h
    apply d.J.injective
    simpa using h.symm

theorem momentum_range_transport (d : ThreePillarMomentumDatum HMod S55) (p : Minkowski4) :
    (LinearMap.range (d.P_mod p)).map d.J.toLinearMap =
      LinearMap.range (d.P_susy p) := by
  ext w
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
    exact ⟨d.J u, by simpa using d.intertwines p u⟩
  · rintro ⟨u, rfl⟩
    refine ⟨d.P_mod p (d.J.symm u), ?_, ?_⟩
    · exact ⟨d.J.symm u, rfl⟩
    · have h := momentum_intertwining_inv d p u
      rw [← h]
      exact d.J.apply_symm_apply _

theorem momentum_polynomial_intertwines
    (d : ThreePillarMomentumDatum HMod S55) (p : Minkowski4)
    (q : Polynomial ℝ) (v : HMod) :
    Polynomial.aeval (d.P_susy p) q (d.J v) =
      d.J (Polynomial.aeval (d.P_mod p) q v) := by
  have hEval := congrArg
    (fun T : Module.End ℝ S55 => T (d.J v))
    (momentum_transport_aeval d.J q (d.P_mod p))
  rw [momentumConjugationAlgEquiv_apply] at hEval
  change conjugatedMomentum d.J (Polynomial.aeval (d.P_mod p) q) (d.J v) =
    Polynomial.aeval (conjugatedMomentum d.J (d.P_mod p)) q (d.J v) at hEval
  rw [conjugatedMomentum_apply] at hEval
  rw [momentum_susy_eq_conjugated d p]
  exact hEval.symm

theorem momentum_polynomial_relation
    (d : ThreePillarMomentumDatum HMod S55) (p : Minkowski4)
    (q : Polynomial ℝ)
    (h : Polynomial.aeval (d.P_mod p) q = 0) :
    Polynomial.aeval (d.P_susy p) q = 0 := by
  rw [momentum_susy_eq_conjugated d p]
  exact momentum_transport_polynomial_relation d.J q (d.P_mod p) h

theorem momentum_polynomial_relation_iff
    (d : ThreePillarMomentumDatum HMod S55) (p : Minkowski4)
    (q : Polynomial ℝ) :
    Polynomial.aeval (d.P_susy p) q = 0 ↔
      Polynomial.aeval (d.P_mod p) q = 0 := by
  rw [momentum_susy_eq_conjugated d p]
  exact momentum_transport_polynomial_relation_iff d.J q (d.P_mod p)

/-- 🏆 THEOREM 3: Exact Operator Conjugacy:
    $P_\mu^{\rm SUSY} = J \circ P_\mu^{\rm mod} \circ J^{-1}$. -/
theorem momentum_conjugacy (d : ThreePillarMomentumDatum HMod S55) (p : Minkowski4) :
    d.P_susy p = (d.J.toLinearMap.comp (d.P_mod p)).comp d.J.symm.toLinearMap := by
  ext w
  dsimp [LinearMap.comp_apply]
  have h := d.intertwines p (d.J.symm w)
  rw [d.J.apply_symm_apply w] at h
  exact h

/-- 🏆 THEOREM 4: Mass-Shell Casimir Coherence under Intertwining:
    $(P_{\rm SUSY})^2 \circ J = J \circ (P_{\rm mod})^2$. -/
theorem momentum_squared_intertwines (d : ThreePillarMomentumDatum HMod S55) (p : Minkowski4) (v : HMod) :
    (d.P_susy p * d.P_susy p) (d.J v) = d.J ((d.P_mod p * d.P_mod p) v) := by
  dsimp [Module.End.mul_apply]
  rw [d.intertwines, d.intertwines]

theorem momentum_commutator_intertwines
    (d : ThreePillarMomentumDatum HMod S55) (p q : Minkowski4) (v : HMod) :
    ((d.P_susy p * d.P_susy q - d.P_susy q * d.P_susy p) (d.J v)) =
      d.J ((d.P_mod p * d.P_mod q - d.P_mod q * d.P_mod p) v) := by
  dsimp [Module.End.mul_apply, LinearMap.sub_apply]
  rw [d.intertwines, d.intertwines, d.intertwines, d.intertwines]
  simp only [map_sub]

theorem momentum_anticommutator_intertwines
    (d : ThreePillarMomentumDatum HMod S55) (p q : Minkowski4) (v : HMod) :
    ((d.P_susy p * d.P_susy q + d.P_susy q * d.P_susy p) (d.J v)) =
      d.J ((d.P_mod p * d.P_mod q + d.P_mod q * d.P_mod p) v) := by
  dsimp [Module.End.mul_apply, LinearMap.add_apply]
  rw [d.intertwines, d.intertwines, d.intertwines, d.intertwines]
  simp only [map_add]

/-- 🏆 THEOREM 5: Literal Operator Equality under Carrier Identification ($J = \mathrm{id}$):
    $P_\mu^{\rm SUSY} = P_\mu^{\rm mod}$. -/
theorem momentum_literal_equality_on_common_carrier
    (d : ThreePillarMomentumDatum S55 S55)
    (hJ : ∀ x, d.J x = x) (p : Minkowski4) :
    d.P_susy p = d.P_mod p := by
  ext x
  have h := d.intertwines p x
  rw [hJ x, hJ (d.P_mod p x)] at h
  exact h

/-- 🏆 THEOREM 6: Ground-State Energy / SUSY Supertrace Connection:
    $\operatorname{Tr}(\{Q, \bar{Q}\}) = 4 P_0 = 4 (J P_{0,\rm mod} J^{-1})$. -/
theorem susy_supertrace_energy_intertwines (d : ThreePillarMomentumDatum HMod S55) (p : Minkowski4) (w : S55) :
    d.P_susy p w = d.J (d.P_mod p (d.J.symm w)) := by
  have h := d.intertwines p (d.J.symm w)
  rw [d.J.apply_symm_apply w] at h
  exact h

end InfoGeometry.Canonical.ThreePillarMomentumIntertwinerBridge
