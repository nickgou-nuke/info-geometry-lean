import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.MetricSpace.PiNat
import Omega.Folding.InverseLimit

namespace Omega.X

/-- No11Inf is a closed subset of the product space ℕ → Bool.
    thm:fold-suite-item3-topo-closed -/
theorem isClosed_no11Inf : IsClosed {a : ℕ → Bool | No11Inf a} := by
  have h_eq : {a : ℕ → Bool | No11Inf a} = ⋂ i : ℕ, {a : ℕ → Bool | ¬ (a i = true ∧ a (i + 1) = true)} := by
    ext a
    simp [No11Inf]
  rw [h_eq]
  apply isClosed_iInter
  intro i
  have h_compl : {a : ℕ → Bool | ¬ (a i = true ∧ a (i + 1) = true)} =
      ({a : ℕ → Bool | a i = true ∧ a (i + 1) = true})ᶜ := by
    ext a
    simp
  rw [h_compl]
  apply IsOpen.isClosed_compl
  -- Show {a | a i = true ∧ a (i+1) = true} is open
  have hOpen_i : IsOpen ((fun a : ℕ → Bool => a i) ⁻¹' {true}) :=
    (isOpen_discrete ({true} : Set Bool)).preimage (continuous_apply i)
  have hOpen_i1 : IsOpen ((fun a : ℕ → Bool => a (i + 1)) ⁻¹' {true}) :=
    (isOpen_discrete ({true} : Set Bool)).preimage (continuous_apply (i + 1))
  have h_inter : {a : ℕ → Bool | a i = true ∧ a (i + 1) = true} =
      ((fun a => a i) ⁻¹' {true}) ∩ ((fun a => a (i + 1)) ⁻¹' {true}) := by
    ext a
    simp
  exact h_inter ▸ hOpen_i.inter hOpen_i1

/-- XInfinity is compact: closed subset of compact product space ℕ → Bool. -/
instance : CompactSpace XInfinity :=
  isCompact_iff_compactSpace.mp isClosed_no11Inf.isCompact

/-- XInfinity is totally disconnected: subspace of ℕ → Bool (product of discrete spaces). -/
instance : TotallyDisconnectedSpace XInfinity :=
  Subtype.totallyDisconnectedSpace

/-- XInfinity carries a metric compatible with the product topology. -/
noncomputable instance : MetricSpace XInfinity :=
  letI : MetricSpace (ℕ → Bool) := PiNat.metricSpaceOfDiscreteUniformity fun _ => rfl
  Subtype.metricSpace

/-- XInfinity is inhabited: the all-false sequence satisfies No11Inf. -/
instance : Inhabited XInfinity :=
  ⟨⟨fun _ => false, fun _ h => by simp at h⟩⟩

/-- XInfinity is infinite: the map n ↦ (bit 2n = true, rest false) is injective. -/
instance : Infinite XInfinity := by
  apply Infinite.of_injective (fun n : ℕ => (⟨fun i => if i = 2 * n then true else false,
    fun i ⟨hi, hi1⟩ => by simp at hi hi1; omega⟩ : XInfinity))
  intro a b h
  have := congr_arg (fun x : XInfinity => x.1 (2 * a)) h
  simp at this; omega

/-- Two infinite sequences differing at any bit are distinct.
    lem:ne-of-bit-ne -/
theorem ne_of_bit_ne (a b : XInfinity) (n : Nat) (h : a.1 n ≠ b.1 n) : a ≠ b :=
  fun hab => h (congrArg (fun x => x.1 n) hab)

/-- XInfinity is nonempty.
    thm:fold-suite -/
theorem XInfinity_nonempty : Nonempty XInfinity := ⟨default⟩

/-- The universe of XInfinity is compact.
    thm:fold-suite -/
theorem XInfinity_univ_isCompact : IsCompact (Set.univ : Set XInfinity) :=
  CompactSpace.isCompact_univ

/-- Extensionality of XInfinity via bitwise equality.
    thm:fold-suite / lem:ne-of-bit-ne -/
theorem XInfinity_ext_iff (a b : XInfinity) :
    a = b ↔ ∀ n, a.1 n = b.1 n := by
  constructor
  · intro hab n
    exact congrArg (fun x : XInfinity => x.1 n) hab
  · intro h
    apply Subtype.ext
    funext n
    exact h n

/-- Paper-facing XInfinity topology package.
    thm:fold-suite / lem:ne-of-bit-ne -/
theorem paper_XInfinity_topology_package :
    Nonempty XInfinity ∧
    IsCompact (Set.univ : Set XInfinity) ∧
    (∀ a b : XInfinity, a = b ↔ ∀ n, a.1 n = b.1 n) ∧
    (∀ a b : XInfinity, ∀ n, a.1 n ≠ b.1 n → a ≠ b) :=
  ⟨XInfinity_nonempty,
   XInfinity_univ_isCompact,
   XInfinity_ext_iff,
   ne_of_bit_ne⟩

end Omega.X
