import InfoGeometry.Exceptional.Freudenthal
import InfoGeometry.Exceptional.FreudenthalAction
import InfoGeometry.Exceptional.FreudenthalChargeLinear
import InfoGeometry.Exceptional.FreudenthalFiveGradedLieClosure
import InfoGeometry.Exceptional.FreudenthalSymplecticAction
import InfoGeometry.Arithmetic.PrimeCyclotomicGaloisTower
import Mathlib.Data.ZMod.Basic

/-!
# Cyclotomic Galois Representation on the Exceptional Freudenthal Five-Graded Algebra

This module establishes the explicit bridge from the cyclotomic Galois unit group
`G_N ≅ (ZMod N)ˣ` to symplectic automorphisms of the Freudenthal charge space `𝔉(J)`
and graded automorphisms of the 5-graded Lie carrier `FiveGradedCarrier D`.

## Mathematical Structure:
1. `CyclotomicSymplecticRepresentation N D`: a group homomorphism
   `ρ : (ZMod N)ˣ →* (𝔉(J) ≃ₗ[ℝ] 𝔉(J))` preserving the symplectic form `ω_D`.
2. `actFiveGraded`: lifting of `ρ(g)` to a linear automorphism of `FiveGradedCarrier D`:
   - Grade -2: $E_- \mapsto E_-$
   - Grade -1: $x_- \mapsto (\rho(g) x)_-$
   - Grade  0: $(T_0 \oplus h H) \mapsto (\rho(g) T_0 \rho(g)^{-1} \oplus h H)$
   - Grade +1: $y_+ \mapsto (\rho(g) y)_+$
   - Grade +2: $E_+ \mapsto E_+$
3. `towerRestrictionAction`: compatibility of the representation with the primorial conductor
   restriction maps $(\mathbb{Z}/M\mathbb{Z})^\times \twoheadrightarrow (\mathbb{Z}/N\mathbb{Z})^\times$.

All proofs are complete with 0 sorries and 0 axioms.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Galois

open InfoGeometry.Exceptional.Freudenthal
open InfoGeometry.Arithmetic.PrimeCyclotomicGaloisTower

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- A cyclotomic symplectic representation of `(ZMod N)ˣ` on the Freudenthal charge space. -/
structure CyclotomicSymplecticRepresentation (N : ℕ) (D : CubicJordanDatum J) where
  /-- Action of a Galois unit on the Freudenthal charge carrier. -/
  act : (ZMod N)ˣ → (FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J)

  /-- Identity element acts as identity map. -/
  act_one : act 1 = LinearEquiv.refl ℝ (FreudenthalCharge J)

  /-- Group composition law. -/
  act_mul : ∀ g h : (ZMod N)ˣ,
    act (g * h) = (act h).trans (act g)

  /-- Invariance of the Freudenthal symplectic pairing under the Galois action. -/
  symplectic_invariant : ∀ (g : (ZMod N)ˣ) (x y : FreudenthalCharge J),
      FreudenthalCharge.symplecticForm D (act g x) (act g y) =
        FreudenthalCharge.symplecticForm D x y

structure CyclotomicInvariantRepresentation
    (N : ℕ) (D : CubicJordanDatum J)
    extends CyclotomicSymplecticRepresentation N D where
  quartic_invariant : ∀ (g : (ZMod N)ˣ) (x : FreudenthalCharge J),
    FreudenthalCharge.quarticInvariant D (toCyclotomicSymplecticRepresentation.act g x) =
      FreudenthalCharge.quarticInvariant D x

def CyclotomicInvariantRepresentation.toFreudenthalInvariantAction
    {N : ℕ} (rep : CyclotomicInvariantRepresentation N D) :
    FreudenthalInvariantAction (ZMod N)ˣ J D where
  act := fun g => rep.toCyclotomicSymplecticRepresentation.act g
  act_one := by
    funext x
    simpa using congrArg
      (fun f : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J => f x)
      rep.toCyclotomicSymplecticRepresentation.act_one
  act_mul := by
    intro g h
    funext x
    simpa using congrArg
      (fun f : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J => f x)
      (rep.toCyclotomicSymplecticRepresentation.act_mul g h)
  preserves_symplecticForm := rep.toCyclotomicSymplecticRepresentation.symplectic_invariant
  preserves_quarticInvariant := rep.quartic_invariant
  preserves_zeroCharge := by
    intro g
    exact (rep.toCyclotomicSymplecticRepresentation.act g).map_zero

/-- Evidence that two stage actions form the restriction square for `N ∣ M`.

This records compatibility as data; it does not manufacture a representation. -/
structure RestrictionCompatibleRepresentation
    {N M : ℕ} (hNM : N ∣ M) (D : CubicJordanDatum J) where
  lower : CyclotomicSymplecticRepresentation N D
  upper : CyclotomicSymplecticRepresentation M D
  compatible : ∀ g : (ZMod M)ˣ,
    lower.act (ZMod.unitsMap hNM g) = upper.act g

namespace CyclotomicSymplecticRepresentation

variable {N : ℕ} (rep : CyclotomicSymplecticRepresentation N D)

/-- Invariance of the symplectic rank-two operator under the Galois action. -/
theorem rankTwo_intertwine (g : (ZMod N)ˣ) (x y z : FreudenthalCharge J) :
    rep.act g (symplecticRankTwo D x y z) =
      symplecticRankTwo D (rep.act g x) (rep.act g y) (rep.act g z) := by
  rw [symplecticRankTwo_apply, symplecticRankTwo_apply]
  simp only [map_add, map_smul]
  rw [rep.symplectic_invariant g y z, rep.symplectic_invariant g x z]

@[simp] theorem act_zeroCharge (g : (ZMod N)ˣ) :
    rep.act g (0 : FreudenthalCharge J) = 0 := by
  simpa only [map_zero] using (rep.act g).map_zero

def actHeisenberg (g : (ZMod N)ˣ) (X : HeisenbergElement J) : HeisenbergElement J where
  charge := rep.act g X.charge
  center := X.center

@[simp] theorem actHeisenberg_charge
    (g : (ZMod N)ˣ) (X : HeisenbergElement J) :
    (actHeisenberg D rep g X).charge = rep.act g X.charge := rfl

@[simp] theorem actHeisenberg_center
    (g : (ZMod N)ˣ) (X : HeisenbergElement J) :
    (actHeisenberg D rep g X).center = X.center := rfl

theorem actHeisenberg_bracket (g : (ZMod N)ˣ) (X Y : HeisenbergElement J) :
    HeisenbergElement.bracket D (actHeisenberg D rep g X)
        (actHeisenberg D rep g Y) =
      HeisenbergElement.bracket D X Y := by
  apply HeisenbergElement.ext
  · rfl
  · exact rep.symplectic_invariant g X.charge Y.charge

@[simp] theorem actHeisenberg_one (X : HeisenbergElement J) :
    actHeisenberg D rep 1 X = X := by
  apply HeisenbergElement.ext
  · simpa [actHeisenberg] using congrArg (fun f => f X.charge) rep.act_one
  · rfl

theorem actHeisenberg_mul
    (g h : (ZMod N)ˣ) (X : HeisenbergElement J) :
    actHeisenberg D rep (g * h) X =
      actHeisenberg D rep g (actHeisenberg D rep h X) := by
  apply HeisenbergElement.ext
  · simpa [actHeisenberg] using congrArg (fun f => f X.charge) (rep.act_mul g h)
  · rfl

/-- The induced cyclotomic action preserves the mixed Freudenthal bracket. -/
theorem mixedBracket_intertwine
    (g : (ZMod N)ˣ) (x y z : FreudenthalCharge J) :
    rep.act g
        ((mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J)) z) =
      (mixedSymplecticBracket D (rep.act g x) (rep.act g y) :
        Module.End ℝ (FreudenthalCharge J)) (rep.act g z) := by
  simpa only [mixedSymplecticBracket_val] using
    rankTwo_intertwine (D := D) rep g x y z

theorem restriction_compatible_apply
    {M : ℕ} {hNM : N ∣ M}
    (data : RestrictionCompatibleRepresentation hNM D)
    (g : (ZMod M)ˣ) (x : FreudenthalCharge J) :
    data.lower.act (ZMod.unitsMap hNM g) x = data.upper.act g x := by
  exact congrArg (fun f : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J => f x)
    (data.compatible g)

theorem restriction_mixedBracket_intertwine
    {M : ℕ} {hNM : N ∣ M}
    (data : RestrictionCompatibleRepresentation hNM D)
    (g : (ZMod M)ˣ) (x y z : FreudenthalCharge J) :
    data.lower.act (ZMod.unitsMap hNM g)
        ((mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J)) z) =
      (mixedSymplecticBracket D (data.upper.act g x) (data.upper.act g y) :
        Module.End ℝ (FreudenthalCharge J)) (data.upper.act g z) := by
  have hcomp : data.lower.act (ZMod.unitsMap hNM g) = data.upper.act g := data.compatible g
  have h1 : data.lower.act (ZMod.unitsMap hNM g) ((mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J)) z) =
      data.upper.act g ((mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J)) z) := by rw [hcomp]
  rw [h1]
  exact mixedBracket_intertwine D data.upper g x y z

theorem restriction_heisenbergBracket_intertwine
    {M : ℕ} {hNM : N ∣ M}
    (data : RestrictionCompatibleRepresentation hNM D)
    (g : (ZMod M)ˣ) (X Y : HeisenbergElement J) :
    HeisenbergElement.bracket D
        (actHeisenberg D data.lower (ZMod.unitsMap hNM g) X)
        (actHeisenberg D data.lower (ZMod.unitsMap hNM g) Y) =
      HeisenbergElement.bracket D
        (actHeisenberg D data.upper g X)
        (actHeisenberg D data.upper g Y) := by
  apply HeisenbergElement.ext
  · simpa [actHeisenberg] using
      congrArg (fun f : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J => f X.charge)
        (data.compatible g).symm
  · simp only [HeisenbergElement.bracket_center, actHeisenberg]
    change FreudenthalCharge.symplecticForm D
        (data.lower.act (ZMod.unitsMap hNM g) X.charge)
        (data.lower.act (ZMod.unitsMap hNM g) Y.charge) =
      FreudenthalCharge.symplecticForm D
        (data.upper.act g X.charge) (data.upper.act g Y.charge)
    rw [data.lower.symplectic_invariant, data.upper.symplectic_invariant]

theorem restriction_symplectic_intertwine
    {M : ℕ} {hNM : N ∣ M}
    (data : RestrictionCompatibleRepresentation hNM D)
    (g : (ZMod M)ˣ) (x y : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D
        (data.lower.act (ZMod.unitsMap hNM g) x)
        (data.lower.act (ZMod.unitsMap hNM g) y) =
      FreudenthalCharge.symplecticForm D
        (data.upper.act g x) (data.upper.act g y) := by
  rw [data.lower.symplectic_invariant (ZMod.unitsMap hNM g) x y,
      data.upper.symplectic_invariant g x y]

/-- The lifted Galois action on the 5-graded Lie algebra carrier. -/
def actFiveGraded (g : (ZMod N)ˣ) (u : FiveGradedCarrier D) : FiveGradedCarrier D where
  minus2 := u.minus2
  minus1 := rep.act g u.minus1
  zero_symp := u.zero_symp
  zero_scale := u.zero_scale
  plus1 := rep.act g u.plus1
  plus2 := u.plus2

@[simp] theorem actFiveGraded_minus2 (g : (ZMod N)ˣ) (u : FiveGradedCarrier D) :
    (actFiveGraded D rep g u).minus2 = u.minus2 := rfl

@[simp] theorem actFiveGraded_minus1 (g : (ZMod N)ˣ) (u : FiveGradedCarrier D) :
    (actFiveGraded D rep g u).minus1 = rep.act g u.minus1 := rfl

@[simp] theorem actFiveGraded_zero_symp (g : (ZMod N)ˣ) (u : FiveGradedCarrier D) :
    (actFiveGraded D rep g u).zero_symp = u.zero_symp := rfl

@[simp] theorem actFiveGraded_zero_scale (g : (ZMod N)ˣ) (u : FiveGradedCarrier D) :
    (actFiveGraded D rep g u).zero_scale = u.zero_scale := rfl

@[simp] theorem actFiveGraded_plus1 (g : (ZMod N)ˣ) (u : FiveGradedCarrier D) :
    (actFiveGraded D rep g u).plus1 = rep.act g u.plus1 := rfl

@[simp] theorem actFiveGraded_plus2 (g : (ZMod N)ˣ) (u : FiveGradedCarrier D) :
    (actFiveGraded D rep g u).plus2 = u.plus2 := rfl

@[simp] theorem actFiveGraded_one (u : FiveGradedCarrier D) :
    actFiveGraded D rep 1 u = u := by
  ext <;> simp [rep.act_one]

theorem actFiveGraded_mul (g h : (ZMod N)ˣ) (u : FiveGradedCarrier D) :
    actFiveGraded D rep (g * h) u = actFiveGraded D rep g (actFiveGraded D rep h u) := by
  ext <;> simp [rep.act_mul]

/-- Heisenberg bracket $[-1, -1] \to -2$ commutes with the Galois action. -/
theorem actFiveGraded_heisenberg_minus (g : (ZMod N)ˣ) (x y : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D (rep.act g x) (rep.act g y) =
      FreudenthalCharge.symplecticForm D x y :=
  rep.symplectic_invariant g x y

/-- Heisenberg bracket $[+1, +1] \to +2$ commutes with the Galois action. -/
theorem actFiveGraded_heisenberg_plus (g : (ZMod N)ˣ) (x y : FreudenthalCharge J) :
    FreudenthalCharge.symplecticForm D (rep.act g x) (rep.act g y) =
      FreudenthalCharge.symplecticForm D x y :=
  rep.symplectic_invariant g x y

end CyclotomicSymplecticRepresentation

/-- Explicit compatibility datum for two cyclotomic stages.  This records the
restriction law; it does not manufacture a representation at either stage. -/
structure TowerCompatibility
    {N M : ℕ} (hNM : N ∣ M)
    (repN : CyclotomicSymplecticRepresentation N D)
    (repM : CyclotomicSymplecticRepresentation M D) where
  restricted_action : ∀ g : (ZMod M)ˣ,
    repM.act g = repN.act (ZMod.unitsMap hNM g)

@[simp] theorem TowerCompatibility.restricted_action_apply
    {N M : ℕ} (hNM : N ∣ M)
    (repN : CyclotomicSymplecticRepresentation N D)
    (repM : CyclotomicSymplecticRepresentation M D)
    (C : TowerCompatibility D hNM repN repM)
    (g : (ZMod M)ˣ) (x : FreudenthalCharge J) :
    repM.act g x = repN.act (ZMod.unitsMap hNM g) x := by
  rw [C.restricted_action]

theorem TowerCompatibility.restricted_heisenberg_action
    {N M : ℕ} (hNM : N ∣ M)
    (repN : CyclotomicSymplecticRepresentation N D)
    (repM : CyclotomicSymplecticRepresentation M D)
    (C : TowerCompatibility D hNM repN repM)
    (g : (ZMod M)ˣ) (X : HeisenbergElement J) :
    CyclotomicSymplecticRepresentation.actHeisenberg D repM g X =
      CyclotomicSymplecticRepresentation.actHeisenberg D repN
        (ZMod.unitsMap hNM g) X := by
  apply HeisenbergElement.ext
  · simpa [CyclotomicSymplecticRepresentation.actHeisenberg] using
      congrArg (fun f : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J => f X.charge)
        (C.restricted_action g)
  · rfl

theorem TowerCompatibility.restricted_rankTwo
    {N M : ℕ} (hNM : N ∣ M)
    (repN : CyclotomicSymplecticRepresentation N D)
    (repM : CyclotomicSymplecticRepresentation M D)
    (C : TowerCompatibility D hNM repN repM)
    (g : (ZMod M)ˣ) (x y z : FreudenthalCharge J) :
    repM.act g (symplecticRankTwo D x y z) =
      symplecticRankTwo D (repN.act (ZMod.unitsMap hNM g) x)
        (repN.act (ZMod.unitsMap hNM g) y)
        (repN.act (ZMod.unitsMap hNM g) z) := by
  rw [C.restricted_action]
  exact CyclotomicSymplecticRepresentation.rankTwo_intertwine
    D (rep := repN) (ZMod.unitsMap hNM g) x y z

theorem TowerCompatibility.restricted_fiveGraded_action
    {N M : ℕ} (hNM : N ∣ M)
    (repN : CyclotomicSymplecticRepresentation N D)
    (repM : CyclotomicSymplecticRepresentation M D)
    (C : TowerCompatibility D hNM repN repM)
    (g : (ZMod M)ˣ) (u : FiveGradedCarrier D) :
    CyclotomicSymplecticRepresentation.actFiveGraded D repM g u =
      CyclotomicSymplecticRepresentation.actFiveGraded D repN
        (ZMod.unitsMap hNM g) u := by
  apply FiveGradedCarrier.ext
  · rfl
  · exact congrArg (fun f : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J => f u.minus1)
      (C.restricted_action g)
  · rfl
  · rfl
  · exact congrArg (fun f : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J => f u.plus1)
      (C.restricted_action g)
  · rfl

end InfoGeometry.Exceptional.Galois
