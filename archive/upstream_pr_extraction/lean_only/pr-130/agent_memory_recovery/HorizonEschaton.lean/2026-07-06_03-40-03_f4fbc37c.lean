-/
def HolographicMemoryRetentionOwnerTarget
    (State Memory Readout : Type*) : Prop :=
  ∀ H : HolographicMemoryRetention State Memory Readout,
    ∀ x y : State,
      H.readout (H.terminalize x) =
        H.readout (H.terminalize y) →
          H.memoryOf x = H.memoryOf y

/-- A supplied terminal-retention datum faithfully reads memory from terminal data. -/
theorem holographicMemoryRetentionOwnerTarget
    (State Memory Readout : Type*) :
    HolographicMemoryRetentionOwnerTarget State Memory Readout := by
  intro H x y hread
  exact H.memory_eq_of_terminal_readout_eq hread

/--
Owner target for Mahapralaya/reset obstruction.
-/
def MahapralayaResetOwnerTarget
    (State Memory Readout : Type*) : Prop :=
  ∀ R : MahapralayaResetDatum State Memory Readout,
    (∀ x y : State,
      R.readout (R.terminalize x) =
        R.readout (R.terminalize y)) ∧
    ¬ ∀ x y : State,
      R.readout (R.terminalize x) =
        R.readout (R.terminalize y) →
          R.memoryOf x = R.memoryOf y

/-- A supplied reset datum collapses terminal readout and forbids faithful retention. -/
theorem mahapralayaResetOwnerTarget
    (State Memory Readout : Type*) :
    MahapralayaResetOwnerTarget State Memory Readout := by
  intro R
  exact ⟨
    (fun x y => R.terminal_readout_eq x y),
    R.terminal_collapse_not_faithful⟩

/--
Owner target for memory-level holographic retention data.
-/
def HolographicRetentionOwnerTarget
    (Memory Readout : Type*) : Prop :=
  ∀ H : HolographicRetentionDatum Memory Readout,
    Function.Injective H.encode

/-- A supplied memory-level retention datum is exactly an injective encoding. -/
theorem holographicRetentionOwnerTarget
    (Memory Readout : Type*) :
    HolographicRetentionOwnerTarget Memory Readout := by
  intro H
  exact H.faithful

/--
Owner target for memory-level computational reset data.
-/
def ComputationalResetOwnerTarget
    (Memory Readout : Type*) : Prop :=
  ∀ R : ComputationalResetDatum Memory Readout,
    (∀ m₁ m₂ : Memory, R.encode m₁ = R.encode m₂) ∧
      ¬ Function.Injective R.encode

/-- A supplied computational reset collapses encoding and cannot be faithful. -/
theorem computationalResetOwnerTarget
    (Memory Readout : Type*) :
    ComputationalResetOwnerTarget Memory Readout := by
  intro R
  exact ⟨
    (fun m₁ m₂ => R.encode_eq_encode m₁ m₂),
    R.collapse_forbids_faithful_retention⟩

end InfoGeometry.OperatorAlgebra.HorizonEschaton
