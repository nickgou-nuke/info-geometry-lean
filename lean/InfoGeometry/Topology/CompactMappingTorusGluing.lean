/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Constructions

noncomputable section
namespace InfoGeometry.Topology.CompactMappingTorus

abbrev Base := Set.Icc (0 : ℝ) 1

def endpointStep {F : Type*} (f : F → F)
    (p q : Base × F) : Prop :=
  (p.1.1 = 0 ∧ q.1.1 = 1 ∧ q.2 = f p.2) ∨
  (p.1.1 = 1 ∧ q.1.1 = 0 ∧ p.2 = f q.2)

def endpointSetoid {F : Type*} (f : F → F) : Setoid (Base × F) where
  r := Relation.EqvGen (endpointStep f)
  iseqv := Relation.EqvGen.is_equivalence _

abbrev Carrier {F : Type*} (f : F → F) :=
  @Quotient (Base × F) (endpointSetoid f)

def project {F : Type*} (f : F → F) : Base × F → Carrier f :=
  @Quotient.mk (Base × F) (endpointSetoid f)

@[simp] theorem project_endpoint {F : Type*} (f : F → F) (x : F) :
    project f (⟨0, by constructor <;> norm_num⟩, x) =
      project f (⟨1, by constructor <;> norm_num⟩, f x) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (Or.inl ⟨rfl, rfl, rfl⟩)

theorem project_surjective {F : Type*} (f : F → F) :
    Function.Surjective (project f) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro p
  exact ⟨p, rfl⟩

private theorem endpointStep_respects
    {F G : Type*} {f : F → F} {g : G → G} (e : F ≃ G)
    (hconj : ∀ x, e (f x) = g (e x))
    {p q : Base × F} (h : endpointStep f p q) :
    endpointStep g (p.1, e p.2) (q.1, e q.2) := by
  rcases h with h | h
  · left
    exact ⟨h.1, h.2.1, by rw [h.2.2, hconj]⟩
  · right
    exact ⟨h.1, h.2.1, by rw [h.2.2, hconj]⟩

private theorem endpointEqvGen_respects
    {F G : Type*} {f : F → F} {g : G → G} (e : F ≃ G)
    (hconj : ∀ x, e (f x) = g (e x)) : ∀ {p q : Base × F},
    Relation.EqvGen (endpointStep f) p q →
      Relation.EqvGen (endpointStep g) (p.1, e p.2) (q.1, e q.2) := by
  intro p q h
  induction h with
  | rel p q h => exact Relation.EqvGen.rel _ _ (endpointStep_respects e hconj h)
  | refl p => exact Relation.EqvGen.refl _
  | symm p q _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans p q r _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

def equivOfConjugacy
    {F G : Type*} {f : F → F} {g : G → G} (e : F ≃ G)
    (hconj : ∀ x, e (f x) = g (e x)) : Carrier f ≃ Carrier g where
  toFun := @Quotient.lift (Base × F) (Carrier g) (endpointSetoid f)
    (fun p : Base × F => @Quotient.mk (Base × G) (endpointSetoid g) (p.1, e p.2))
    (by
      intro p q h
      apply Quotient.sound
      exact endpointEqvGen_respects e hconj h)
  invFun := @Quotient.lift (Base × G) (Carrier f) (endpointSetoid g)
    (fun p : Base × G => @Quotient.mk (Base × F) (endpointSetoid f) (p.1, e.symm p.2))
    (by
      intro p q h
      apply Quotient.sound
      exact endpointEqvGen_respects e.symm (fun x => by
        apply e.injective
        simpa using (hconj (e.symm x)).symm) h)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro p
    change @Quotient.mk (Base × F) (endpointSetoid f)
      (p.1, e.symm (e p.2)) = @Quotient.mk _ _ p
    rw [e.symm_apply_apply]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro p
    change @Quotient.mk (Base × G) (endpointSetoid g)
      (p.1, e (e.symm p.2)) = @Quotient.mk _ _ p
    rw [e.apply_symm_apply]

@[simp] theorem equivOfConjugacy_project
    {F G : Type*} {f : F → F} {g : G → G} (e : F ≃ G)
    (hconj : ∀ x, e (f x) = g (e x)) (p : Base × F) :
    equivOfConjugacy e hconj (project f p) = project g (p.1, e p.2) := by
  rfl

def lift {F Y : Type*} {f : F → F} (g : Base × F → Y)
    (hg : ∀ {p q : Base × F},
      @Setoid.r (Base × F) (endpointSetoid f) p q → g p = g q) :
    Carrier f → Y :=
  @Quotient.lift (Base × F) Y (endpointSetoid f) g (by
    intro p q h
    exact hg h)

@[simp] theorem lift_project {F Y : Type*} {f : F → F} (g : Base × F → Y)
    (hg : ∀ {p q : Base × F},
      @Setoid.r (Base × F) (endpointSetoid f) p q → g p = g q) (p : Base × F) :
    lift g hg (project f p) = g p := by
  rfl

end InfoGeometry.Topology.CompactMappingTorus
end noncomputable section
