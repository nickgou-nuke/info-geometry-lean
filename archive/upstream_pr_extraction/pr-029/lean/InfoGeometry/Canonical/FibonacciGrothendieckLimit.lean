import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.External.Virasoro.FockSpaceSugawara
import InfoGeometry.External.Virasoro.Sugawara
import Mathlib.Algebra.Colimit.Module

/-!
# InfoGeometry.Canonical.FibonacciGrothendieckLimit

Direct algebraic `L₀` readout for staged Fibonacci fermionic operator systems.

This file follows the external Virasoro/Sugawara pattern: the Heisenberg mode
operators, local truncation, and commutator law are ordinary theorem
hypotheses.  The staged Grothendieck semiring is an algebraic direct limit with
explicit bonding maps and a compatible cone into endomorphisms.

The concrete Fibonacci fermionic task is to construct the stages, the
upper-triangular tensor bonding maps, and the compatible endomorphism cone.
Once a finite-stage operator reads as the Sugawara zero mode, the theorem below
identifies its direct-limit image with the external Virasoro `L₀` action.

The Fibonacci Grothendieck fusion lane is additive: the class `a·1 + b·τ` is
represented by `(a,b) : ℕ × ℕ`, and tensoring by `τ` is the additive map
`(a,b) ↦ (b,a+b)`.  This is not a unital semiring bond, because it sends `1` to
`τ`; it is therefore formalized with `AddCommGroup.DirectLimit`, not with the
unital semiring direct-limit API.
-/

noncomputable section

set_option autoImplicit false

namespace InfoGeometry.Canonical.FibonacciGrothendieckLimit

open Filter
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

universe u

variable {𝕜 V : Type u} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/-! ## Fibonacci Grothendieck fusion series -/

/-- The finite Fibonacci fusion Grothendieck class `a·1 + b·τ`. -/
abbrev fibFusionClass : Type :=
  Nat × Nat

/-- Tensoring a Fibonacci fusion class by `τ`: `1 ↦ τ`, `τ ↦ 1 + τ`. -/
def fibFusionTensorTau : fibFusionClass →+ fibFusionClass where
  toFun x := (x.2, x.1 + x.2)
  map_zero' := rfl
  map_add' x y := by
    ext <;> simp [add_comm, add_left_comm]

/-- Iterated tensor-by-`τ` map between finite Grothendieck stages. -/
def fibFusionTensorMap (m n : Nat) (h : m ≤ n) : fibFusionClass →+ fibFusionClass :=
  Nat.leRecOn h
    (C := fun _ => fibFusionClass →+ fibFusionClass)
    (fun {_} ih => fibFusionTensorTau.comp ih)
    (AddMonoidHom.id fibFusionClass)

@[simp]
theorem fibFusionTensorMap_refl (m : Nat) :
    fibFusionTensorMap m m le_rfl = AddMonoidHom.id fibFusionClass := by
  simpa [fibFusionTensorMap] using
    (Nat.leRecOn_self
      (C := fun _ => fibFusionClass →+ fibFusionClass)
      (next := fun {_} ih => fibFusionTensorTau.comp ih)
      (x := AddMonoidHom.id fibFusionClass))

@[simp]
theorem fibFusionTensorMap_succ (m n : Nat) (h : m ≤ n) :
    fibFusionTensorMap m (n + 1) (Nat.le_trans h (Nat.le_succ n)) =
      fibFusionTensorTau.comp (fibFusionTensorMap m n h) := by
  unfold fibFusionTensorMap
  rw [Nat.leRecOn_trans h (Nat.le_succ n)]
  rw [Nat.leRecOn_succ']

theorem fibFusionTensorMap_apply_trans
    (m n k : Nat) (hmn : m ≤ n) (hnk : n ≤ k)
    (x : fibFusionClass) :
    fibFusionTensorMap m k (hmn.trans hnk) x =
      fibFusionTensorMap n k hnk (fibFusionTensorMap m n hmn x) := by
  refine Nat.le_induction
    (m := n)
    (P := fun t ht =>
      fibFusionTensorMap m t (Nat.le_trans hmn ht) x =
        fibFusionTensorMap n t ht (fibFusionTensorMap m n hmn x))
    ?base ?succ k hnk
  · simp
  · intro t ht ih
    have hmt : m ≤ t := Nat.le_trans hmn ht
    rw [fibFusionTensorMap_succ m t hmt, fibFusionTensorMap_succ n t ht]
    exact congrArg fibFusionTensorTau ih

instance fibFusionDirectedSystem :
    DirectedSystem (fun _ : Nat => fibFusionClass)
      (fun m n h => fibFusionTensorMap m n h) where
  map_self := by
    intro m x
    simp
  map_map := by
    intro k j i hij hjk x
    simpa using (fibFusionTensorMap_apply_trans i j k hij hjk x).symm

/-- The additive Grothendieck colimit of repeated Fibonacci tensoring by `τ`. -/
abbrev fibFusionGrothendieckColimit : Type :=
  AddCommGroup.DirectLimit (fun _ : Nat => fibFusionClass)
    (fun m n h => fibFusionTensorMap m n h)

/-- Canonical map from a finite Fibonacci fusion stage into the additive colimit. -/
def fibFusionOf (n : Nat) : fibFusionClass →+ fibFusionGrothendieckColimit :=
  AddCommGroup.DirectLimit.of
    (fun _ : Nat => fibFusionClass)
    (fun m n h => fibFusionTensorMap m n h)
    n

/-- One tensor-by-`τ` step is identified in the additive Grothendieck colimit. -/
theorem fibFusionOf_tensorTau (n : Nat) (x : fibFusionClass) :
    fibFusionOf (n + 1) (fibFusionTensorTau x) = fibFusionOf n x := by
  have hstep :
      fibFusionTensorMap n (n + 1) (Nat.le_succ n) x = fibFusionTensorTau x := by
    have hmap :
        fibFusionTensorMap n (n + 1) (Nat.le_succ n) =
          fibFusionTensorTau.comp (AddMonoidHom.id fibFusionClass) := by
      rw [fibFusionTensorMap_succ n n le_rfl, fibFusionTensorMap_refl]
    simpa only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.id_apply] using
      congrFun (congrArg DFunLike.coe hmap) x
  simpa [fibFusionOf, hstep] using
    (AddCommGroup.DirectLimit.of_f
      (G := fun _ : Nat => fibFusionClass)
      (f := fun m n h => fibFusionTensorMap m n h)
      (Nat.le_succ n) x)

/-- The Fibonacci vector `(Fₙ, Fₙ₊₁)` in the fusion Grothendieck semigroup. -/
def fibFusionVector (n : Nat) : fibFusionClass :=
  (Nat.fib n, Nat.fib (n + 1))

/-- Tensoring `(Fₙ, Fₙ₊₁)` by `τ` gives `(Fₙ₊₁, Fₙ₊₂)`. -/
theorem fibFusionVector_step (n : Nat) :
    fibFusionTensorTau (fibFusionVector n) = fibFusionVector (n + 1) := by
  ext <;> simp [fibFusionTensorTau, fibFusionVector, Nat.fib_add_two]

/--
The staged Fibonacci vectors all determine the same additive Grothendieck
colimit class.
-/
theorem fibFusionOf_vector_eq_initial (n : Nat) :
    fibFusionOf n (fibFusionVector n) = fibFusionOf 0 (fibFusionVector 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [← fibFusionVector_step n]
      rw [fibFusionOf_tensorTau n (fibFusionVector n)]
      exact ih

/-! ## Additive `L₀` readout from the Fibonacci Grothendieck colimit -/

/--
Stage-dependent diagonal coefficients for a compatible additive readout from
the Fibonacci fusion series to an operator additive group.
-/
def fibFusionLZeroCoeff (L : V →ₗ[𝕜] V) : Nat → (V →ₗ[𝕜] V) × (V →ₗ[𝕜] V)
  | 0 => (0, L)
  | n + 1 =>
      ((fibFusionLZeroCoeff L n).2 - (fibFusionLZeroCoeff L n).1,
        (fibFusionLZeroCoeff L n).1)

/--
Additive stage readout sending `a·1 + b·τ` to the corresponding linear
combination of the stage coefficients.
-/
def fibFusionLZeroReadout (L : V →ₗ[𝕜] V) (n : Nat) :
    fibFusionClass →+ (V →ₗ[𝕜] V) where
  toFun x := x.1 • (fibFusionLZeroCoeff L n).1 + x.2 • (fibFusionLZeroCoeff L n).2
  map_zero' := by
    simp
  map_add' x y := by
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    let A := (fibFusionLZeroCoeff L n).1
    let B := (fibFusionLZeroCoeff L n).2
    change (a + c) • A + (b + d) • B = (a • A + b • B) + (c • A + d • B)
    rw [add_nsmul, add_nsmul]
    abel

omit [CharZero 𝕜] in
/-- The stage readouts are compatible with tensoring by `τ`. -/
theorem fibFusionLZeroReadout_tensorTau
    (L : V →ₗ[𝕜] V) (n : Nat) (x : fibFusionClass) :
    fibFusionLZeroReadout L (n + 1) (fibFusionTensorTau x) =
      fibFusionLZeroReadout L n x := by
  rcases x with ⟨a, b⟩
  let A := (fibFusionLZeroCoeff L n).1
  let B := (fibFusionLZeroCoeff L n).2
  dsimp [fibFusionLZeroReadout, fibFusionTensorTau, fibFusionLZeroCoeff]
  change b • (B - A) + (a + b) • A = a • A + b • B
  rw [add_nsmul, nsmul_sub]
  abel

omit [CharZero 𝕜] in
/-- The stage readouts are compatible with every iterated tensor map. -/
theorem fibFusionLZeroReadout_tensorMap
    (L : V →ₗ[𝕜] V) (m n : Nat) (h : m ≤ n) (x : fibFusionClass) :
    fibFusionLZeroReadout L n (fibFusionTensorMap m n h x) =
      fibFusionLZeroReadout L m x := by
  refine Nat.le_induction
    (m := m)
    (P := fun t ht =>
      fibFusionLZeroReadout L t (fibFusionTensorMap m t ht x) =
        fibFusionLZeroReadout L m x)
    ?base ?succ n h
  · simp
  · intro t hmt ih
    rw [fibFusionTensorMap_succ m t hmt]
    exact (fibFusionLZeroReadout_tensorTau L t (fibFusionTensorMap m t hmt x)).trans ih

/-- The induced additive map from the Fibonacci Grothendieck colimit to operators. -/
def fibFusionLZeroLift (L : V →ₗ[𝕜] V) :
    fibFusionGrothendieckColimit →+ (V →ₗ[𝕜] V) :=
  AddCommGroup.DirectLimit.lift
    (fun _ : Nat => fibFusionClass)
    (fun m n h => fibFusionTensorMap m n h)
    (V →ₗ[𝕜] V)
    (fun n => fibFusionLZeroReadout L n)
    (fun i j hij x => fibFusionLZeroReadout_tensorMap L i j hij x)

omit [CharZero 𝕜] in
/-- The finite Fibonacci vector at every stage reads as the chosen operator `L`. -/
theorem fibFusionLZeroReadout_vector
    (L : V →ₗ[𝕜] V) (n : Nat) :
    fibFusionLZeroReadout L n (fibFusionVector n) = L := by
  induction n with
  | zero =>
      simp [fibFusionLZeroReadout, fibFusionVector, fibFusionLZeroCoeff]
  | succ n ih =>
      rw [← fibFusionVector_step n]
      exact (fibFusionLZeroReadout_tensorTau L n (fibFusionVector n)).trans ih

omit [CharZero 𝕜] in
/--
The additive Grothendieck colimit readout sends every Fibonacci stage vector to
the same operator.
-/
theorem fibFusionGrothendieck_lzero_lift_of_vector
    (L : V →ₗ[𝕜] V) (n : Nat) :
    fibFusionLZeroLift L (fibFusionOf n (fibFusionVector n)) = L := by
  rw [fibFusionLZeroLift, fibFusionOf, AddCommGroup.DirectLimit.lift_of]
  exact fibFusionLZeroReadout_vector L n

/-- The external Sugawara representation sends `L₀` to the Sugawara zero mode. -/
theorem sugawaraRepresentation_lzero_eq_sugawaraGen_zero
    (heiOper : Int → V →ₗ[𝕜] V)
    (heiTrunc : ∀ v, atTop.Eventually (fun l : Int => heiOper l v = 0))
    (heiComm : ∀ k l,
      (heiOper k).commutator (heiOper l) =
        if k + l = 0 then (k : 𝕜) • (1 : V →ₗ[𝕜] V) else 0) :
    VirasoroProject.sugawaraRepresentation (heiOper := heiOper) heiTrunc heiComm
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0) =
      VirasoroProject.sugawaraGen (heiOper := heiOper) heiTrunc 0 := by
  ext v
  rw [VirasoroProject.sugawaraRepresentation_lgen_apply',
    VirasoroProject.sugawaraGen_apply]

/--
The Fibonacci Grothendieck fusion colimit has a canonical additive readout to
the external Sugawara `L₀` operator once the Heisenberg current hypotheses are
supplied.
-/
theorem fibFusionGrothendieck_lzero_lift_eq_sugawara_lzero
    (heiOper : Int → V →ₗ[𝕜] V)
    (heiTrunc : ∀ v, atTop.Eventually (fun l : Int => heiOper l v = 0))
    (heiComm : ∀ k l,
      (heiOper k).commutator (heiOper l) =
        if k + l = 0 then (k : 𝕜) • (1 : V →ₗ[𝕜] V) else 0)
    (n : Nat) :
    fibFusionLZeroLift (VirasoroProject.sugawaraGen (heiOper := heiOper) heiTrunc 0)
        (fibFusionOf n (fibFusionVector n)) =
      VirasoroProject.sugawaraRepresentation (heiOper := heiOper) heiTrunc heiComm
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0) := by
  rw [fibFusionGrothendieck_lzero_lift_of_vector]
  exact (sugawaraRepresentation_lzero_eq_sugawaraGen_zero heiOper heiTrunc heiComm).symm

/-- The Heisenberg current mode acting on the charged Fock space. -/
def chargedFockHeisenbergMode (α : 𝕜) (k : Int) :
    VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
      VirasoroProject.ChargedFockSpace 𝕜 α :=
  ModuleOfModuleAlgebra.lsmul 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)
    (ιUEA 𝕜 (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 k))

/-- The charged Fock Heisenberg current satisfies the Sugawara local truncation hypothesis. -/
theorem chargedFockHeisenbergMode_eventually_eq_zero
    (α : 𝕜) (v : VirasoroProject.ChargedFockSpace 𝕜 α) :
    atTop.Eventually (fun k : Int => chargedFockHeisenbergMode (𝕜 := 𝕜) α k v = 0) := by
  simpa [chargedFockHeisenbergMode, ModuleOfModuleAlgebra.lsmul_apply] using
    VirasoroProject.ChargedFockSpace.eventually_jgen_smul_eq_zero 𝕜 α v

/--
The charged Fock Heisenberg current satisfies the exact Heisenberg commutator
required by the Sugawara construction.
-/
theorem chargedFockHeisenbergMode_commutator
    (α : 𝕜) (k l : Int) :
    (chargedFockHeisenbergMode (𝕜 := 𝕜) α k).commutator
        (chargedFockHeisenbergMode (𝕜 := 𝕜) α l) =
      if k + l = 0 then
        (k : 𝕜) •
          (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α)
      else 0 := by
  let ρ : LieAlgebra.Representation 𝕜 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜)
      (VirasoroProject.ChargedFockSpace 𝕜 α) :=
    UniversalEnvelopingAlgebra.representation
      (𝕜 := 𝕜) (𝓰 := VirasoroProject.HeisenbergAlgebra 𝕜)
      (V := VirasoroProject.ChargedFockSpace 𝕜 α)
  have hmode :
      ∀ i : Int,
        chargedFockHeisenbergMode (𝕜 := 𝕜) α i =
          ρ (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 i) := by
    intro i
    rfl
  rw [hmode k, hmode l]
  have hkgen :
      ρ (VirasoroProject.HeisenbergAlgebra.kgen 𝕜) =
        (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
          VirasoroProject.ChargedFockSpace 𝕜 α) := by
    ext v
    change
      ModuleOfModuleAlgebra.lsmul 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)
          (ιUEA 𝕜 (VirasoroProject.HeisenbergAlgebra.kgen 𝕜)) v = v
    rw [ModuleOfModuleAlgebra.lsmul_apply]
    change ιUEA 𝕜 (VirasoroProject.HeisenbergAlgebra.kgen 𝕜) • v = v
    exact VirasoroProject.ChargedFockSpace.kgen_smul 𝕜 α v
  have hbr := LieAlgebra.Representation.apply_bracket_eq_commutator ρ
    (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 k)
    (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 l)
  rw [← hbr]
  by_cases hkl : k + l = 0
  · simp [VirasoroProject.HeisenbergAlgebra.lie_jgen, hkl, hkgen]
  · simp [VirasoroProject.HeisenbergAlgebra.lie_jgen, hkl]

/--
Concrete charged-Fock closure of the Fibonacci Grothendieck `L₀` readout.

The local truncation and Heisenberg-current commutator hypotheses are discharged
inside `External.Virasoro.FockSpaceSugawara`: the charged Fock space supplies
`ChargedFockSpace.eventually_jgen_smul_eq_zero`, `ChargedFockSpace.kgen_smul`,
and the resulting Sugawara representation.
-/
theorem fibFusionGrothendieck_lzero_lift_eq_chargedFock_sugawara_lzero
    (α : 𝕜) (n : Nat) :
    fibFusionLZeroLift
        (V := VirasoroProject.ChargedFockSpace 𝕜 α)
        (VirasoroProject.ChargedFockSpace.sugawaraRepresentation 𝕜 α
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0))
        (fibFusionOf n (fibFusionVector n)) =
      VirasoroProject.ChargedFockSpace.sugawaraRepresentation 𝕜 α
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0) := by
  exact fibFusionGrothendieck_lzero_lift_of_vector
    (VirasoroProject.ChargedFockSpace.sugawaraRepresentation 𝕜 α
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0)) n

/--
Direct-limit `L₀` readout.

For a staged semiring of finite Fibonacci fermionic operators, if a compatible
endomorphism cone sends a finite-stage element to the Sugawara zero mode, then
the induced map from the algebraic direct limit sends its canonical image to
the external Virasoro `L₀` operator.
-/
theorem grothendieck_colimit_stage_operator_eq_sugawara_lzero
    {Stage : Nat → Type u} [∀ n : Nat, Semiring (Stage n)]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (heiOper : Int → V →ₗ[𝕜] V)
    (heiTrunc : ∀ v, atTop.Eventually (fun l : Int => heiOper l v = 0))
    (heiComm : ∀ k l,
      (heiOper k).commutator (heiOper l) =
        if k + l = 0 then (k : 𝕜) • (1 : V →ₗ[𝕜] V) else 0)
    (toEnd : ∀ n : Nat, Stage n →+* (V →ₗ[𝕜] V))
    (hcone : CompatibleCone (Stage := Stage) bond toEnd)
    (n : Nat) (x : Stage n)
    (hx : toEnd n x = VirasoroProject.sugawaraGen (heiOper := heiOper) heiTrunc 0) :
    directLimitLift (Stage := Stage) bond toEnd hcone
        (directLimitOf (Stage := Stage) bond n x) =
      VirasoroProject.sugawaraRepresentation (heiOper := heiOper) heiTrunc heiComm
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 0) := by
  rw [directLimitLift_of, hx]
  exact (sugawaraRepresentation_lzero_eq_sugawaraGen_zero heiOper heiTrunc heiComm).symm

end InfoGeometry.Canonical.FibonacciGrothendieckLimit
