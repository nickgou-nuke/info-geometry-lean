import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureFlowCompHaus

open CategoryTheory

/-!
# Composition of modular transport on symbolic-latent orbit closures

The modular flow already transports each closed orbit closure by a native
homeomorphism.  This owner records the composition law for those restricted
homeomorphisms.  It is a groupoid law on the family of closed orbit
subspaces, not a recurrence or minimality assertion.
-/

noncomputable section

namespace InfoGeometry.Topology

variable {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

omit [CompactSpace X] in
theorem SymbolicLatentModularFlow.orbitClosureFlowHomeomorph_trans_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) (t s : ℝ) :
    ∀ y : SymbolicLatentModularOrbitClosure Φ x,
      (Φ.orbitClosureFlowHomeomorph x (t + s) y).1 =
        ((Φ.orbitClosureFlowHomeomorph x t).trans
          (Φ.orbitClosureFlowHomeomorph (Φ.act t x) s) y).1 := by
  intro y
  change Φ.act (t + s) y.1 = Φ.act s (Φ.act t y.1)
  calc
    Φ.act (t + s) y.1 = Φ.act (s + t) y.1 := by rw [add_comm]
    _ = Φ.act s (Φ.act t y.1) := Φ.add_apply s t y.1

omit [CompactSpace X] in
theorem SymbolicLatentModularFlow.orbitClosureFlowHomeomorph_trans
    (Φ : SymbolicLatentModularFlow X) (x : X) (t s : ℝ) :
    ∀ y : SymbolicLatentModularOrbitClosure Φ x,
      (Φ.orbitClosureFlowHomeomorph x (t + s) y).1 =
        ((Φ.orbitClosureFlowHomeomorph x t).trans
          (Φ.orbitClosureFlowHomeomorph (Φ.act t x) s) y).1 := by
  intro y
  exact Φ.orbitClosureFlowHomeomorph_trans_apply x t s y

omit [CompactSpace X] in
theorem SymbolicLatentModularFlow.orbitClosureFlowHomeomorph_zero_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    ∀ y : SymbolicLatentModularOrbitClosure Φ x,
      (Φ.orbitClosureFlowHomeomorph x 0 y).1 = y.1 := by
  intro y
  simp [SymbolicLatentModularFlow.orbitClosureFlowHomeomorph,
    Φ.zero_apply]

omit [CompactSpace X] in
theorem SymbolicLatentModularFlow.orbitClosureFlowTopCatHom_trans_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) (t s : ℝ)
    (y : SymbolicLatentModularOrbitClosure Φ x) :
    (Φ.orbitClosureFlowTopCatHom (t + s) x y).1 =
      ((Φ.orbitClosureFlowTopCatHom t x ≫
        Φ.orbitClosureFlowTopCatHom s (Φ.act t x)) y).1 := by
  change Φ.act (t + s) y.1 = Φ.act s (Φ.act t y.1)
  calc
    Φ.act (t + s) y.1 = Φ.act (s + t) y.1 := by rw [add_comm]
    _ = Φ.act s (Φ.act t y.1) := Φ.add_apply s t y.1

theorem SymbolicLatentModularFlow.orbitClosureFlowCompHausHom_trans_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) (t s : ℝ)
    (y : SymbolicLatentModularOrbitClosure Φ x) :
    (Φ.orbitClosureFlowCompHausHom x (t + s) y).1 =
      ((Φ.orbitClosureFlowCompHausHom x t ≫
        Φ.orbitClosureFlowCompHausHom (Φ.act t x) s) y).1 := by
  change Φ.act (t + s) y.1 = Φ.act s (Φ.act t y.1)
  calc
    Φ.act (t + s) y.1 = Φ.act (s + t) y.1 := by rw [add_comm]
    _ = Φ.act s (Φ.act t y.1) := Φ.add_apply s t y.1


end InfoGeometry.Topology
