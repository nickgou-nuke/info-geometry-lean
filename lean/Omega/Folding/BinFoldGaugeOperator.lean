import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Module.End
import Mathlib.Tactic
import Omega.Folding.BinFoldGaugeDecomposition

noncomputable section

namespace Omega.Folding

/-- The actual subgroup of input-cube permutations preserving every BinFold
fiber. This supplies the group structure missing from the original subtype
and retains the exact fiber-preservation predicate. -/
def binFoldGaugeSubgroup (m : ℕ) : Subgroup (Equiv.Perm (BinFoldInput m)) where
  carrier := {σ | ∀ n, Omega.cBinFold m (σ n).1 = Omega.cBinFold m n.1}
  one_mem' := by
    intro n
    rfl
  mul_mem' := by
    intro σ τ hσ hτ n
    change Omega.cBinFold m (σ (τ n)).1 = Omega.cBinFold m n.1
    calc
      Omega.cBinFold m (σ (τ n)).1 = Omega.cBinFold m (τ n).1 := hσ (τ n)
      _ = Omega.cBinFold m n.1 := hτ n
  inv_mem' := by
    intro σ hσ n
    have h := hσ (σ⁻¹ n)
    simpa using h.symm

/-- The original fiber-preserving permutation subtype is the same carrier as
the subgroup presentation. -/
def binFoldGaugeCarrierEquiv (m : ℕ) :
    BinFoldGauge m ≃ binFoldGaugeSubgroup m where
  toFun σ := ⟨σ.1, σ.2⟩
  invFun σ := ⟨σ.1, σ.2⟩
  left_inv := by intro σ; apply Subtype.ext; rfl
  right_inv := by intro σ; apply Subtype.ext; rfl

/-- Pullback by a fiber-preserving permutation as a linear operator on
real-valued functions over the full input cube. -/
def binFoldGaugeOperator {m : ℕ} (σ : binFoldGaugeSubgroup m) :
    Module.End ℝ (BinFoldInput m → ℝ) where
  toFun f n := f (σ.1.symm n)
  map_add' f g := by funext n; rfl
  map_smul' c f := by funext n; rfl

/-- An invertible operator induced by a BinFold gauge symmetry. -/
def binFoldGaugeOperatorUnit {m : ℕ} (σ : binFoldGaugeSubgroup m) :
    (Module.End ℝ (BinFoldInput m → ℝ))ˣ where
  val := binFoldGaugeOperator σ
  inv := binFoldGaugeOperator σ⁻¹
  val_inv := by
    apply LinearMap.ext
    intro f
    funext n
    simp [binFoldGaugeOperator, Equiv.Perm.inv_def]
  inv_val := by
    apply LinearMap.ext
    intro f
    funext n
    simp [binFoldGaugeOperator, Equiv.Perm.inv_def]

/-- Faithful representation of the BinFold gauge subgroup by operator units. -/
def binFoldGaugeOperatorRep (m : ℕ) : binFoldGaugeSubgroup m →*
    (Module.End ℝ (BinFoldInput m → ℝ))ˣ where
  toFun := binFoldGaugeOperatorUnit
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro f
    funext n
    simp [binFoldGaugeOperatorUnit, binFoldGaugeOperator, Equiv.Perm.one_def]
  map_mul' σ τ := by
    apply Units.ext
    apply LinearMap.ext
    intro f
    funext n
    simp [binFoldGaugeOperatorUnit, binFoldGaugeOperator, Equiv.Perm.inv_def,
      Equiv.Perm.mul_def]

theorem binFoldGaugeOperatorRep_injective (m : ℕ) :
    Function.Injective (binFoldGaugeOperatorRep m) := by
  intro σ τ hστ
  have hop : binFoldGaugeOperator σ = binFoldGaugeOperator τ :=
    congrArg Units.val hστ
  have hinv : σ.1.symm = τ.1.symm := by
    apply Equiv.ext
    intro n
    let s := σ.1.symm n
    let t := τ.1.symm n
    let δ : BinFoldInput m → ℝ := fun x => if x = s then 1 else 0
    have hEval := congrArg (fun T : Module.End ℝ (BinFoldInput m → ℝ) => T δ n) hop
    change δ s = δ t at hEval
    by_cases hst : t = s
    · exact hst.symm
    · simp [δ, s, t, hst] at hEval
  apply Subtype.ext
  have h := congrArg Equiv.symm hinv
  simpa using h

/-- The faithful image of the BinFold gauge group in the endomorphism-unit
group of its real observable space. -/
def binFoldGaugeOperatorGroup (m : ℕ) :
    Subgroup (Module.End ℝ (BinFoldInput m → ℝ))ˣ :=
  (⊤ : Subgroup (binFoldGaugeSubgroup m)).map (binFoldGaugeOperatorRep m)

theorem binFoldGaugeOperatorUnit_mem_group {m : ℕ}
    (σ : binFoldGaugeSubgroup m) :
    binFoldGaugeOperatorUnit σ ∈ binFoldGaugeOperatorGroup m := by
  rw [binFoldGaugeOperatorGroup, Subgroup.mem_map]
  exact ⟨σ, trivial, rfl⟩

private theorem binFoldGauge_swap_mem {m : ℕ} {a b : BinFoldInput m}
    (hab : Omega.cBinFold m a.1 = Omega.cBinFold m b.1) (hne : a ≠ b) :
    Equiv.swap a b ∈ binFoldGaugeSubgroup m := by
  change ∀ n, Omega.cBinFold m (Equiv.swap a b n).1 = Omega.cBinFold m n.1
  intro n
  by_cases hna : n = a
  · subst n
    simp [Equiv.swap_apply_def, hab, hne]
  · by_cases hnb : n = b
    · subst n
      simp [Equiv.swap_apply_def, hab, hne]
    · simp [Equiv.swap_apply_def, hna, hnb]

/-- Three distinct inputs in the same audited window-6 fiber. The owner
`BinFold.boundary_fiber_sizes_six` records a four-element fiber at the value
of input 37; finite computation extracts three points from that concrete
fiber. -/
private theorem binFoldGauge_three_same_fiber :
    ∃ a b c : BinFoldInput 6,
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
        Omega.cBinFold 6 a.1 = Omega.cBinFold 6 37 ∧
        Omega.cBinFold 6 b.1 = Omega.cBinFold 6 37 ∧
        Omega.cBinFold 6 c.1 = Omega.cBinFold 6 37 := by
  native_decide

/-- The window-6 BinFold gauge subgroup is noncommutative: two adjacent
transpositions on three inputs in one fiber generate an `S₃` witness. -/
theorem binFoldGaugeSubgroup_exists_noncommuting_pair :
    ∃ σ τ : binFoldGaugeSubgroup 6, σ * τ ≠ τ * σ := by
  obtain ⟨a, b, c, hab, hbc, hac, hfa, hfb, hfc⟩ :=
    binFoldGauge_three_same_fiber
  let σ : binFoldGaugeSubgroup 6 :=
    ⟨Equiv.swap a b, binFoldGauge_swap_mem (hfa.trans hfb.symm) hab⟩
  let τ : binFoldGaugeSubgroup 6 :=
    ⟨Equiv.swap b c, binFoldGauge_swap_mem (hfb.trans hfc.symm) hbc⟩
  have hperm : σ.1 * τ.1 ≠ τ.1 * σ.1 := by
    intro h
    have heval := congrArg (fun p : Equiv.Perm (BinFoldInput 6) => p a) h
    have hleft : (Equiv.swap a b * Equiv.swap b c) a = b := by
      simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, hab, hac]
    have hright : (Equiv.swap b c * Equiv.swap a b) a = c := by
      simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, hab, hac, hbc]
    rw [hleft, hright] at heval
    exact hbc heval
  refine ⟨σ, τ, ?_⟩
  intro h
  exact hperm (congrArg Subtype.val h)

/-- The faithful endomorphism-unit image retains the concrete noncommuting
window-6 gauge operators. -/
theorem binFoldGaugeOperatorGroup_exists_noncommuting_pair :
    ∃ u v : ↥(binFoldGaugeOperatorGroup 6), u * v ≠ v * u := by
  obtain ⟨σ, τ, hστ⟩ := binFoldGaugeSubgroup_exists_noncommuting_pair
  let u : ↥(binFoldGaugeOperatorGroup 6) :=
    ⟨binFoldGaugeOperatorUnit σ, binFoldGaugeOperatorUnit_mem_group σ⟩
  let v : ↥(binFoldGaugeOperatorGroup 6) :=
    ⟨binFoldGaugeOperatorUnit τ, binFoldGaugeOperatorUnit_mem_group τ⟩
  refine ⟨u, v, ?_⟩
  intro huv
  apply hστ
  apply binFoldGaugeOperatorRep_injective 6
  have hval := congrArg Subtype.val huv
  simpa [u, v, binFoldGaugeOperatorRep, map_mul] using hval

end Omega.Folding

end noncomputable section
