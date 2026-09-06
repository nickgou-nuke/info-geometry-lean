import Mathlib.Tactic
import InfoGeometry.Causal.ProofDAGRepresentation
open Classical
open InfoGeometry.Causal.ProofDAGRepresentation

universe u
set_option autoImplicit false

namespace InfoGeometry.Causal.ProofCohomology

structure Edge {α : Type u} (G : ProofDAG α) where
  source : α
  target : α
  dep : G.le source target

structure Triangle {α : Type u} (G : ProofDAG α) where
  a : α
  b : α
  c : α
  ab : G.le a b
  bc : G.le b c

namespace Triangle

/-- The long edge is derived from the two composable dependency proofs. -/
def ac {α : Type u} {G : ProofDAG α} (t : Triangle G) : G.le t.a t.c :=
  G.trans t.ab t.bc

end Triangle

def C0 (α : Type u) : Type u := α → ℝ
def C1 {α : Type u} (G : ProofDAG α) : Type u := Edge G → ℝ
def C2 {α : Type u} (G : ProofDAG α) : Type u := Triangle G → ℝ

noncomputable def d0 {α : Type u} {G : ProofDAG α} (f : C0 α) : C1 G :=
  λ (e : Edge G) => f e.target - f e.source

noncomputable def d1 {α : Type u} {G : ProofDAG α} (omega : C1 G) : C2 G :=
  λ (t : Triangle G) => omega ⟨t.a, t.b, t.ab⟩ + omega ⟨t.b, t.c, t.bc⟩ - omega ⟨t.a, t.c, t.ac⟩

theorem d1_d0_zero {α : Type u} {G : ProofDAG α} (f : C0 α) (t : Triangle G) :
    d1 (d0 f) t = 0 := by
  dsimp [d1, d0]; ring

theorem H0_is_constant {α : Type u} {G : ProofDAG α} (h_connected : ∀ a b, G.le a b ∨ G.le b a)
    (f : C0 α) (h_cocycle : ∀ (e : Edge G), d0 f e = 0) : ∀ a b, f a = f b := by
  intro a b
  rcases h_connected a b with (h | h)
  · have h_edge : d0 f ⟨a, b, h⟩ = 0 := h_cocycle _
    dsimp [d0] at h_edge; linarith
  · have h_edge : d0 f ⟨b, a, h⟩ = 0 := h_cocycle _
    dsimp [d0] at h_edge; linarith

def IsCocycle {α : Type u} {G : ProofDAG α} (omega : C1 G) : Prop :=
  ∀ (t : Triangle G), d1 omega t = 0

def IsCoboundary {α : Type u} {G : ProofDAG α} (omega : C1 G) : Prop :=
  ∃ (f : C0 α), ∀ (e : Edge G), omega e = d0 f e

theorem H1_vanishes {α : Type u} {G : ProofDAG α}
    (h_connected : ∀ a b, G.le a b ∨ G.le b a)
    (h_inhabited : Nonempty α) (omega : C1 G) (h_cocycle : IsCocycle omega) : IsCoboundary omega := by
  rcases h_inhabited with ⟨a0⟩
  let f : C0 α := λ v =>
    if h : G.le a0 v then omega ⟨a0, v, h⟩
    else -omega ⟨v, a0, (h_connected a0 v).resolve_left h⟩
  refine ⟨f, λ e => ?_⟩
  dsimp [d0]
  have hsrc_exp : f e.source = (if h : G.le a0 e.source then omega ⟨a0, e.source, h⟩
    else -omega ⟨e.source, a0, (h_connected a0 e.source).resolve_left h⟩) := rfl
  have htgt_exp : f e.target = (if h : G.le a0 e.target then omega ⟨a0, e.target, h⟩
    else -omega ⟨e.target, a0, (h_connected a0 e.target).resolve_left h⟩) := rfl
  rw [hsrc_exp, htgt_exp]
  by_cases hsrc : G.le a0 e.source
  · rw [dif_pos hsrc]
    by_cases htgt : G.le a0 e.target
    · rw [dif_pos htgt]
      let ht : Triangle G := ⟨a0, e.source, e.target, hsrc, e.dep⟩
      have hc : omega ⟨a0, e.source, hsrc⟩ + omega e - omega ⟨a0, e.target, htgt⟩ = 0 := by
        calc
          omega ⟨a0, e.source, hsrc⟩ + omega e - omega ⟨a0, e.target, htgt⟩
              = d1 omega ht := by
                unfold ht; simp [d1]
          _ = 0 := h_cocycle ht
      have hsum : omega ⟨a0, e.source, hsrc⟩ + omega e = omega ⟨a0, e.target, htgt⟩ := by
        calc
          omega ⟨a0, e.source, hsrc⟩ + omega e
              = (omega ⟨a0, e.source, hsrc⟩ + omega e - omega ⟨a0, e.target, htgt⟩) + omega ⟨a0, e.target, htgt⟩ := by ring
          _ = 0 + omega ⟨a0, e.target, htgt⟩ := by rw [hc]
          _ = omega ⟨a0, e.target, htgt⟩ := by simp
      calc
        omega e = (omega ⟨a0, e.source, hsrc⟩ + omega e) - omega ⟨a0, e.source, hsrc⟩ := by ring
        _ = omega ⟨a0, e.target, htgt⟩ - omega ⟨a0, e.source, hsrc⟩ := by rw [hsum]
    · have ha0tgt : G.le a0 e.target := G.trans hsrc e.dep
      exact absurd ha0tgt htgt
  · have hsrc' : G.le e.source a0 := (h_connected a0 e.source).resolve_left hsrc
    rw [dif_neg hsrc]
    by_cases htgt : G.le a0 e.target
    · rw [dif_pos htgt]
      let ht : Triangle G := ⟨e.source, a0, e.target, hsrc', htgt⟩
      have hc : omega ⟨e.source, a0, hsrc'⟩ + omega ⟨a0, e.target, htgt⟩ - omega e = 0 := by
        calc
          omega ⟨e.source, a0, hsrc'⟩ + omega ⟨a0, e.target, htgt⟩ - omega e
              = d1 omega ht := by
                unfold ht; simp [d1]
          _ = 0 := h_cocycle ht
      have hsum : omega e = omega ⟨a0, e.target, htgt⟩ + omega ⟨e.source, a0, hsrc'⟩ := by
        calc
          omega e = (omega ⟨e.source, a0, hsrc'⟩ + omega ⟨a0, e.target, htgt⟩) - (omega ⟨e.source, a0, hsrc'⟩ + omega ⟨a0, e.target, htgt⟩ - omega e) := by ring
          _ = (omega ⟨e.source, a0, hsrc'⟩ + omega ⟨a0, e.target, htgt⟩) - 0 := by rw [hc]
          _ = omega ⟨a0, e.target, htgt⟩ + omega ⟨e.source, a0, hsrc'⟩ := by ring
      calc
        omega e = omega ⟨a0, e.target, htgt⟩ + omega ⟨e.source, a0, hsrc'⟩ := hsum
        _ = omega ⟨a0, e.target, htgt⟩ - (-omega ⟨e.source, a0, hsrc'⟩) := by ring
    · have htgt' : G.le e.target a0 := (h_connected a0 e.target).resolve_left htgt
      rw [dif_neg htgt]
      let ht : Triangle G := ⟨e.source, e.target, a0, e.dep, htgt'⟩
      have hc : omega e + omega ⟨e.target, a0, htgt'⟩ - omega ⟨e.source, a0, hsrc'⟩ = 0 := by
        calc
          omega e + omega ⟨e.target, a0, htgt'⟩ - omega ⟨e.source, a0, hsrc'⟩
              = d1 omega ht := by
                unfold ht; simp [d1]
          _ = 0 := h_cocycle ht
      have hsum : omega e + omega ⟨e.target, a0, htgt'⟩ = omega ⟨e.source, a0, hsrc'⟩ := by
        calc
          omega e + omega ⟨e.target, a0, htgt'⟩
              = (omega e + omega ⟨e.target, a0, htgt'⟩ - omega ⟨e.source, a0, hsrc'⟩) + omega ⟨e.source, a0, hsrc'⟩ := by ring
          _ = 0 + omega ⟨e.source, a0, hsrc'⟩ := by rw [hc]
          _ = omega ⟨e.source, a0, hsrc'⟩ := by simp
      calc
        omega e = (omega e + omega ⟨e.target, a0, htgt'⟩) - omega ⟨e.target, a0, htgt'⟩ := by ring
        _ = omega ⟨e.source, a0, hsrc'⟩ - omega ⟨e.target, a0, htgt'⟩ := by rw [hsum]
        _ = (-omega ⟨e.target, a0, htgt'⟩) - (-omega ⟨e.source, a0, hsrc'⟩) := by ring

end InfoGeometry.Causal.ProofCohomology
