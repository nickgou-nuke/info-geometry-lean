import InfoGeometry.RootSystem.D4RootLattice

/-!
# The generated `D₄` Weyl subgroup

This owner packages the already verified simple reflections as a genuine
subgroup of lattice automorphisms.  It deliberately does not identify this
subgroup with an abstract Coxeter group; that is a separate theorem.
-/

namespace InfoGeometry.RootSystem.D4

noncomputable def simpleReflectionEquiv (i : Fin 4) : Lattice ≃ Lattice where
  toFun := reflect_lattice i
  invFun := reflect_lattice i
  left_inv := fun x => reflect_lattice_square i x
  right_inv := fun x => reflect_lattice_square i x

def d4WeylGroup : Subgroup (Lattice ≃ Lattice) :=
  Subgroup.closure (Set.range simpleReflectionEquiv)

theorem simpleReflectionEquiv_mem_d4WeylGroup (i : Fin 4) :
    simpleReflectionEquiv i ∈ d4WeylGroup := by
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem simpleReflectionEquiv_square (i : Fin 4) :
    simpleReflectionEquiv i * simpleReflectionEquiv i = 1 := by
  apply Equiv.ext
  intro x
  exact reflect_lattice_square i x

theorem simpleReflectionEquiv_commute_of_cartan_zero
    (i j : Fin 4) (hij : cartanMatrix i j = 0) :
    simpleReflectionEquiv i * simpleReflectionEquiv j =
      simpleReflectionEquiv j * simpleReflectionEquiv i := by
  apply Equiv.ext
  intro x
  exact reflect_lattice_commute_of_cartan_zero i j hij x

theorem simpleReflectionEquiv_braid_of_cartan_neg_one
    (i j : Fin 4) (hij : cartanMatrix i j = -1) :
    simpleReflectionEquiv i * simpleReflectionEquiv j * simpleReflectionEquiv i =
      simpleReflectionEquiv j * simpleReflectionEquiv i * simpleReflectionEquiv j := by
  apply Equiv.ext
  intro x
  exact reflect_lattice_braid_of_cartan_neg_one i j hij x

theorem d4WeylGroup_preserves_lattice
    (w : d4WeylGroup) (x : Lattice) :
    ((w : Lattice ≃ Lattice) x : Lattice) =
      (w : Lattice ≃ Lattice) x := rfl

/-! The generated subgroup acts on the concrete norm-two root predicate. -/

def IsD4Root (x : Lattice) : Prop :=
  dot x.1 x.1 = 2

theorem reflect_preserves_d4Root (i : Fin 4) {x : Lattice}
    (hx : IsD4Root x) : IsD4Root (reflect_lattice i x) := by
  change dot (reflect i x.1) (reflect i x.1) = 2
  unfold reflect
  have hi : dot (simpleRoot i) (simpleRoot i) = 2 := simpleRoot_norm i
  have hcross : dot (simpleRoot i) x.1 = dot x.1 (simpleRoot i) := by
    simp [dot, mul_comm]
  simp only [dot_sub_left, dot_smul_left, dot_sub_right, dot_smul_right]
  rw [hi]
  ring_nf
  rw [hcross]
  ring_nf
  exact hx

theorem simpleReflectionEquiv_preserves_d4Root
    (i : Fin 4) {x : Lattice} (hx : IsD4Root x) :
    IsD4Root (simpleReflectionEquiv i x) := by
  exact reflect_preserves_d4Root i hx

theorem d4WeylGroup_preserves_d4Root
    (w : d4WeylGroup) {x : Lattice} (hx : IsD4Root x) :
    IsD4Root ((w : Lattice ≃ Lattice) x) := by
  have hw := Subgroup.closure_induction_left
    (p := fun g _ => ∀ y, IsD4Root y → IsD4Root (g y))
    (fun y hy => by simpa using hy)
    (fun a ha b hb hhb y hy => by
      rcases ha with ⟨i, rfl⟩
      exact simpleReflectionEquiv_preserves_d4Root i (hhb y hy))
    (fun a ha b hb hhb y hy => by
      rcases ha with ⟨i, rfl⟩
      simpa [simpleReflectionEquiv_square] using
        (simpleReflectionEquiv_preserves_d4Root i (hhb y hy)))
    w.property
  exact hw x hx

theorem reflect_lattice_preserves_dot_self
    (i : Fin 4) (x : Lattice) :
    dot (reflect_lattice i x) (reflect_lattice i x) = dot x x := by
  change dot (reflect i x.1) (reflect i x.1) = dot x.1 x.1
  unfold reflect
  have hi : dot (simpleRoot i) (simpleRoot i) = 2 := simpleRoot_norm i
  have hcross : dot (simpleRoot i) x.1 = dot x.1 (simpleRoot i) := by
    simp [dot, mul_comm]
  simp only [dot_sub_left, dot_smul_left, dot_sub_right, dot_smul_right]
  rw [hi, hcross]
  ring

theorem simpleReflectionEquiv_preserves_dot_self
    (i : Fin 4) (x : Lattice) :
    dot (simpleReflectionEquiv i x) (simpleReflectionEquiv i x) = dot x x := by
  exact reflect_lattice_preserves_dot_self i x

theorem d4WeylGroup_preserves_dot_self
    (w : d4WeylGroup) (x : Lattice) :
    dot ((w : Lattice ≃ Lattice) x) ((w : Lattice ≃ Lattice) x) = dot x x := by
  have hw := Subgroup.closure_induction_left
    (p := fun g _ => ∀ y : Lattice,
      dot (g y) (g y) = dot y y)
    (fun y => rfl)
    (fun a ha b hb hhb y => by
      rcases ha with ⟨i, rfl⟩
      change dot (simpleReflectionEquiv i (b y))
          (simpleReflectionEquiv i (b y)) = dot y y
      rw [simpleReflectionEquiv_preserves_dot_self]
      exact hhb y)
    (fun a ha b hb hhb y => by
      rcases ha with ⟨i, rfl⟩
      have hi : (simpleReflectionEquiv i)⁻¹ = simpleReflectionEquiv i := by
        exact inv_eq_of_mul_eq_one_left (simpleReflectionEquiv_square i)
      change dot ((simpleReflectionEquiv i)⁻¹ (b y))
          ((simpleReflectionEquiv i)⁻¹ (b y)) = dot y y
      rw [hi, simpleReflectionEquiv_preserves_dot_self]
      exact hhb y)
    w.property
  exact hw x

end InfoGeometry.RootSystem.D4
