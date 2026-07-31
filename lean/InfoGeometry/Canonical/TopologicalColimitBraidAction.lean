import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Braid actions transported through `TopCat` direct colimits

This owner is the categorical bonding layer for finite topological braid
systems.  A pair of natural families of continuous endomorphisms induces braid
endomorphisms of the native colimit via `colim.map`; the Artin relation is then
proved by the colimit hom-ext principle.
-/

noncomputable section

namespace InfoGeometry.Canonical.TopologicalColimitBraidAction

open CategoryTheory CategoryTheory.Limits

universe u v

variable {J : Type u} [Category.{v, u} J]
variable (F : J ⥤ TopCat.{u})

structure ContinuousBraidNaturalData where
  braid1 : F ⟶ F
  braid2 : F ⟶ F
  artin : ∀ j : J,
    braid1.app j ≫ braid2.app j ≫ braid1.app j =
      braid2.app j ≫ braid1.app j ≫ braid2.app j

variable (D : ContinuousBraidNaturalData F)

/-- The two continuous braid endomorphisms induced on the topological colimit. -/
def colimitBraid1 : colimit F ⟶ colimit F :=
  colim.map D.braid1

def colimitBraid2 : colimit F ⟶ colimit F :=
  colim.map D.braid2

theorem colimitInjection_braid1 (j : J) :
    colimit.ι F j ≫ colimitBraid1 F D =
      D.braid1.app j ≫ colimit.ι F j := by
  exact colimit.ι_map D.braid1 j

theorem colimitInjection_braid2 (j : J) :
    colimit.ι F j ≫ colimitBraid2 F D =
      D.braid2.app j ≫ colimit.ι F j := by
  exact colimit.ι_map D.braid2 j

theorem colimitInjection_word (α β γ : F ⟶ F) (j : J) :
    colimit.ι F j ≫ colim.map α ≫ colim.map β ≫ colim.map γ =
      α.app j ≫ β.app j ≫ γ.app j ≫ colimit.ι F j := by
  have hα := colimit.ι_map α j
  have hβ := colimit.ι_map β j
  have hγ := colimit.ι_map γ j
  calc
    colimit.ι F j ≫ colim.map α ≫ colim.map β ≫ colim.map γ =
        (α.app j ≫ colimit.ι F j) ≫ colim.map β ≫ colim.map γ := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ colim.map β ≫ colim.map γ) hα
    _ = α.app j ≫ (β.app j ≫ colimit.ι F j) ≫ colim.map γ := by
          simpa only [Category.assoc] using
            congrArg (fun k => α.app j ≫ k ≫ colim.map γ) hβ
    _ = α.app j ≫ β.app j ≫ γ.app j ≫ colimit.ι F j := by
          simpa only [Category.assoc] using
            congrArg (fun k => α.app j ≫ β.app j ≫ k) hγ

theorem colimitInjection_pair (α β : F ⟶ F) (j : J) :
    colimit.ι F j ≫ colim.map α ≫ colim.map β =
      α.app j ≫ β.app j ≫ colimit.ι F j := by
  have hα := colimit.ι_map α j
  have hβ := colimit.ι_map β j
  calc
    colimit.ι F j ≫ colim.map α ≫ colim.map β =
        (α.app j ≫ colimit.ι F j) ≫ colim.map β := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ colim.map β) hα
    _ = α.app j ≫ β.app j ≫ colimit.ι F j := by
          simpa only [Category.assoc] using
            congrArg (fun k => α.app j ≫ k) hβ

theorem colimit_map_involutive
    (α : F ⟶ F)
    (hα : ∀ j : J, α.app j ≫ α.app j = 𝟙 _) :
    colim.map α ≫ colim.map α = 𝟙 _ := by
  apply colimit.hom_ext
  intro j
  calc
    colimit.ι F j ≫ colim.map α ≫ colim.map α =
        α.app j ≫ α.app j ≫ colimit.ι F j :=
      colimitInjection_pair (F := F) α α j
    _ = 𝟙 _ ≫ colimit.ι F j := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ colimit.ι F j) (hα j)
    _ = colimit.ι F j := by simp

theorem colimit_braid1_involutive
    (h : ∀ j : J, D.braid1.app j ≫ D.braid1.app j = 𝟙 _) :
    colimitBraid1 F D ≫ colimitBraid1 F D = 𝟙 _ := by
  exact colimit_map_involutive (F := F) D.braid1 h

theorem colimit_braid2_involutive
    (h : ∀ j : J, D.braid2.app j ≫ D.braid2.app j = 𝟙 _) :
    colimitBraid2 F D ≫ colimitBraid2 F D = 𝟙 _ := by
  exact colimit_map_involutive (F := F) D.braid2 h

/-- A compatible stagewise readout is invariant under a natural endomorphism
which preserves that readout at every stage.  This is the categorical form
of trace invariance; it does not put an algebra structure on the colimit
carrier. -/
theorem colimit_readout_invariant
    (α : F ⟶ F) (c : Cocone F)
    (hα : ∀ j : J, α.app j ≫ c.ι.app j = c.ι.app j) :
    colim.map α ≫ colimit.desc F c = colimit.desc F c := by
  apply colimit.hom_ext
  intro j
  have hmap := colimit.ι_map α j
  have hdesc := colimit.ι_desc c j
  calc
    colimit.ι F j ≫ colim.map α ≫ colimit.desc F c =
        (α.app j ≫ colimit.ι F j) ≫ colimit.desc F c := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ colimit.desc F c) hmap
    _ = α.app j ≫ c.ι.app j := by
          simpa only [Category.assoc] using
            congrArg (fun k => α.app j ≫ k) hdesc
    _ = c.ι.app j := hα j
    _ = colimit.ι F j ≫ colimit.desc F c := by
          exact hdesc.symm

theorem colimit_readout_invariant_apply
    (α : F ⟶ F) (c : Cocone F)
    (hα : ∀ j : J, α.app j ≫ c.ι.app j = c.ι.app j)
    (x : (colimit F).carrier) :
    colimit.desc F c (colim.map α x) = colimit.desc F c x := by
  exact congrArg (fun f => f x) (colimit_readout_invariant (F := F) α c hα)

theorem colimit_readout_cyclic
    (α β : F ⟶ F) (c : Cocone F)
    (hcyc : ∀ j : J,
      α.app j ≫ β.app j ≫ c.ι.app j =
        β.app j ≫ α.app j ≫ c.ι.app j) :
    colim.map α ≫ colim.map β ≫ colimit.desc F c =
      colim.map β ≫ colim.map α ≫ colimit.desc F c := by
  apply colimit.hom_ext
  intro j
  calc
    colimit.ι F j ≫ colim.map α ≫ colim.map β ≫ colimit.desc F c =
        α.app j ≫ β.app j ≫ colimit.ι F j ≫ colimit.desc F c := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ colimit.desc F c)
              (colimitInjection_pair (F := F) α β j)
    _ = α.app j ≫ β.app j ≫ c.ι.app j := by
          simpa only [Category.assoc] using
            congrArg (fun k => α.app j ≫ β.app j ≫ k) (colimit.ι_desc c j)
    _ = β.app j ≫ α.app j ≫ c.ι.app j := hcyc j
    _ = colimit.ι F j ≫ colim.map β ≫ colim.map α ≫
        colimit.desc F c := by
          calc
            β.app j ≫ α.app j ≫ c.ι.app j =
                β.app j ≫ α.app j ≫ colimit.ι F j ≫
                  colimit.desc F c := by
                    simpa only [Category.assoc] using
                      congrArg (fun k => β.app j ≫ α.app j ≫ k)
                        (colimit.ι_desc c j).symm
            _ = colimit.ι F j ≫ colim.map β ≫ colim.map α ≫
                colimit.desc F c := by
                  simpa only [Category.assoc] using
                    congrArg (fun k => k ≫ colimit.desc F c)
                      (colimitInjection_pair (F := F) β α j).symm

theorem colimit_artin_relation :
    colimitBraid1 F D ≫ colimitBraid2 F D ≫ colimitBraid1 F D =
      colimitBraid2 F D ≫ colimitBraid1 F D ≫ colimitBraid2 F D := by
  apply colimit.hom_ext
  intro j
  calc
    colimit.ι F j ≫ colimitBraid1 F D ≫ colimitBraid2 F D ≫
        colimitBraid1 F D =
        D.braid1.app j ≫ D.braid2.app j ≫ D.braid1.app j ≫
        colimit.ι F j := by
          change colimit.ι F j ≫ colim.map D.braid1 ≫
              colim.map D.braid2 ≫ colim.map D.braid1 = _
          exact colimitInjection_word (F := F) D.braid1 D.braid2 D.braid1 j
    _ = D.braid2.app j ≫ D.braid1.app j ≫ D.braid2.app j ≫
        colimit.ι F j := by
          simpa only [Category.assoc] using
            congrArg (fun h => h ≫ colimit.ι F j) (D.artin j)
    _ = colimit.ι F j ≫ colimitBraid2 F D ≫ colimitBraid1 F D ≫
        colimitBraid2 F D := by
          symm
          change colimit.ι F j ≫ colim.map D.braid2 ≫
              colim.map D.braid1 ≫ colim.map D.braid2 = _
          exact colimitInjection_word (F := F) D.braid2 D.braid1 D.braid2 j

/-! ## Full twist in the descended braid image -/

/-- The positive Coxeter word on the colimit. -/
def colimitCoxeter : colimit F ⟶ colimit F :=
  colimitBraid2 F D ≫ colimitBraid1 F D

/-- The full twist, defined as the cube of the positive Coxeter word. -/
def colimitFullTwist : colimit F ⟶ colimit F :=
  colimitCoxeter F D ≫ colimitCoxeter F D ≫ colimitCoxeter F D

/-- The full twist is the square of the Garside word. -/
theorem colimitFullTwist_eq_garside_sq :
    colimitFullTwist F D =
      (colimitBraid1 F D ≫ colimitBraid2 F D ≫ colimitBraid1 F D) ≫
        (colimitBraid1 F D ≫ colimitBraid2 F D ≫ colimitBraid1 F D) := by
  let x := colimitBraid1 F D
  let y := colimitBraid2 F D
  have h := colimit_artin_relation (F := F) D
  change (y ≫ x) ≫ (y ≫ x) ≫ (y ≫ x) =
    (x ≫ y ≫ x) ≫ (x ≫ y ≫ x)
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ x ≫ y ≫ x) h.symm

/-- The full twist commutes with the first descended braid generator. -/
theorem colimitFullTwist_commutes_braid1 :
    colimitFullTwist F D ≫ colimitBraid1 F D =
      colimitBraid1 F D ≫ colimitFullTwist F D := by
  let x := colimitBraid1 F D
  let y := colimitBraid2 F D
  let Δ := x ≫ y ≫ x
  have h := colimit_artin_relation (F := F) D
  have hΔx : Δ ≫ x = y ≫ Δ := by
    simpa only [Δ, Category.assoc] using
      congrArg (fun k => k ≫ x) h
  have hΔy : Δ ≫ y = x ≫ Δ := by
    simpa only [Δ, Category.assoc] using
      (congrArg (fun k => x ≫ k) h).symm
  rw [colimitFullTwist_eq_garside_sq (F := F) (D := D)]
  change (Δ ≫ Δ) ≫ x = x ≫ (Δ ≫ Δ)
  calc
    (Δ ≫ Δ) ≫ x = Δ ≫ (Δ ≫ x) := by simp only [Category.assoc]
    _ = Δ ≫ (y ≫ Δ) := by rw [hΔx]
    _ = (Δ ≫ y) ≫ Δ := by simp only [Category.assoc]
    _ = (x ≫ Δ) ≫ Δ := by rw [hΔy]
    _ = x ≫ (Δ ≫ Δ) := by simp only [Category.assoc]

/-- The full twist commutes with the second descended braid generator. -/
theorem colimitFullTwist_commutes_braid2 :
    colimitFullTwist F D ≫ colimitBraid2 F D =
      colimitBraid2 F D ≫ colimitFullTwist F D := by
  let x := colimitBraid1 F D
  let y := colimitBraid2 F D
  let Δ := x ≫ y ≫ x
  have h := colimit_artin_relation (F := F) D
  have hΔx : Δ ≫ x = y ≫ Δ := by
    simpa only [Δ, Category.assoc] using
      congrArg (fun k => k ≫ x) h
  have hΔy : Δ ≫ y = x ≫ Δ := by
    simpa only [Δ, Category.assoc] using
      (congrArg (fun k => x ≫ k) h).symm
  rw [colimitFullTwist_eq_garside_sq (F := F) (D := D)]
  change (Δ ≫ Δ) ≫ y = y ≫ (Δ ≫ Δ)
  calc
    (Δ ≫ Δ) ≫ y = Δ ≫ (Δ ≫ y) := by simp only [Category.assoc]
    _ = Δ ≫ (x ≫ Δ) := by rw [hΔy]
    _ = (Δ ≫ x) ≫ Δ := by simp only [Category.assoc]
    _ = (y ≫ Δ) ≫ Δ := by rw [hΔx]
    _ = y ≫ (Δ ≫ Δ) := by simp only [Category.assoc]

end InfoGeometry.Canonical.TopologicalColimitBraidAction
