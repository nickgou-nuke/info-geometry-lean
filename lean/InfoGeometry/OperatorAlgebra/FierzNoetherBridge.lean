import InfoGeometry.OperatorAlgebra.NoetherModularFlow

/-!
# InfoGeometry.OperatorAlgebra.FierzNoetherBridge

Lean-owned bridge from Fierz recombination carriers to Noether/modular
invariance predicates.

This module still does not assume a Fierz completeness theorem.  It proves the
linear algebra fact that any explicitly linear operator preserves the finite
Fierz recombination sum.  Concrete Fierz completeness must come from owner
modules such as `Quantum.Fierz` / `Canonical.Fierz` / `OperatorialFierz*`.
-/

namespace FierzNoetherBridge

open InfoGeometry.OperatorAlgebra.NoetherModularFlow

/-- Operators fixed by a flow carrier. -/
def FixedByFlow
    {Time Alg : Type*}
    (F : Time → Alg → Alg) (A : Alg) : Prop :=
  ∀ t, F t A = A

/-- Definitional readback for flow-fixed operators. -/
@[rep_depth operator]
theorem fixedByFlow_iff
    {Time Alg : Type*}
    (F : Time → Alg → Alg) (A : Alg) :
    FixedByFlow F A ↔ ∀ t, F t A = A :=
  Iff.rfl

/-- Elements commuting with every member of a supplied set. -/
def CommutesWithSet
    {Alg : Type*} [Mul Alg]
    (S : Set Alg) (A : Alg) : Prop :=
  ∀ B ∈ S, A * B = B * A

/-- Definitional readback for commuting with a set. -/
@[rep_depth operator]
theorem commutesWithSet_iff
    {Alg : Type*} [Mul Alg]
    (S : Set Alg) (A : Alg) :
    CommutesWithSet S A ↔ ∀ B ∈ S, A * B = B * A :=
  Iff.rfl

/-- Modular-Noether readout carrier. No invariance law is bundled. -/
structure ModularNoetherReadout
    (Time Alg Readout : Type*) where
  flow : Time → Alg → Alg
  readout : Alg → Readout
  charge : Alg

namespace ModularNoetherReadout

variable {Time Alg Readout : Type*}
variable (M : ModularNoetherReadout Time Alg Readout)

@[rep_depth operator]
theorem flow_apply (t : Time) (A : Alg) :
    M.flow t A = M.flow t A := rfl

@[rep_depth operator]
theorem readout_apply (A : Alg) :
    M.readout A = M.readout A := rfl

@[rep_depth operator]
theorem charge_apply :
    M.charge = M.charge := rfl

end ModularNoetherReadout

/-- A modular-Noether charge is fixed by its modular/readout flow. -/
def IsModularNoetherCharge
    {Time Alg Readout : Type*}
    (M : ModularNoetherReadout Time Alg Readout) : Prop :=
  FixedByFlow M.flow M.charge

/-- Definitional readback for modular-Noether charges. -/
@[rep_depth operator]
theorem isModularNoetherCharge_iff_fixed
    {Time Alg Readout : Type*}
    (M : ModularNoetherReadout Time Alg Readout) :
    IsModularNoetherCharge M ↔ ∀ t, M.flow t M.charge = M.charge :=
  Iff.rfl

/-- Additive maps send zero to zero. -/
private theorem map_zero_of_additive
    {Alg : Type*} [AddCommGroup Alg]
    (δ : Alg → Alg)
    (hδ_add : ∀ A B : Alg, δ (A + B) = δ A + δ B) :
    δ 0 = 0 := by
  have h : δ 0 = δ 0 + δ 0 := by
    simpa using hδ_add 0 0
  have h' : δ 0 + 0 = δ 0 + δ 0 := by
    simpa using h
  exact (add_left_cancel h').symm

/--
An explicitly linear operator preserves a finite Fierz recombination sum.

This is the precise algebraic content behind “Killing fields preserve Fierz
recombination” when the Killing field is supplied with actual linearity
theorems.
-/
@[rep_depth operator]
theorem map_fierzRecombinationSum_of_linear
    {Alg BasisIndex : Type*}
    [AddCommGroup Alg] [Module ℝ Alg] [Fintype BasisIndex] [DecidableEq BasisIndex]
    (δ : Alg → Alg)
    (hδ_add : ∀ A B : Alg, δ (A + B) = δ A + δ B)
    (hδ_smul : ∀ (r : ℝ) (A : Alg), δ (r • A) = r • δ A)
    (F : FierzRecombinationChannel Alg BasisIndex) :
    δ (fierzRecombinationSum F)
      =
    Finset.univ.sum fun i => F.recombinationCoefficients i • δ (F.recombinationBasis i) := by
  classical
  have hδ_zero : δ (0 : Alg) = 0 :=
    map_zero_of_additive δ hδ_add
  have hsum :
      ∀ s : Finset BasisIndex,
        δ (s.sum fun i => F.recombinationCoefficients i • F.recombinationBasis i)
          =
        s.sum fun i => F.recombinationCoefficients i • δ (F.recombinationBasis i) := by
    intro s
    refine Finset.induction_on s ?base ?step
    · simp [hδ_zero]
    · intro a s has ih
      rw [Finset.sum_insert has, Finset.sum_insert has, hδ_add, hδ_smul, ih]
  exact hsum Finset.univ

/--
If a supplied bilinear product is already proved to equal the Fierz
recombination sum, then a linear operator maps that product to the recombined
sum of mapped basis channels.
-/
@[rep_depth operator]
theorem map_fierzComplete_product_of_linear
    {Alg BasisIndex : Type*}
    [AddCommGroup Alg] [Module ℝ Alg] [Fintype BasisIndex] [DecidableEq BasisIndex]
    (bilinearProduct : Alg → Alg → Alg)
    (δ : Alg → Alg)
    (hδ_add : ∀ A B : Alg, δ (A + B) = δ A + δ B)
    (hδ_smul : ∀ (r : ℝ) (A : Alg), δ (r • A) = r • δ A)
    (F : FierzRecombinationChannel Alg BasisIndex)
    (hF : IsFierzComplete bilinearProduct F) :
    δ (bilinearProduct F.bilinearA F.bilinearB)
      =
    Finset.univ.sum fun i => F.recombinationCoefficients i • δ (F.recombinationBasis i) := by
  rw [hF]
  exact map_fierzRecombinationSum_of_linear δ hδ_add hδ_smul F

end FierzNoetherBridge
