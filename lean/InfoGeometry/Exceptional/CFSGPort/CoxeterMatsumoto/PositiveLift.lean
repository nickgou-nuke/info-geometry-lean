/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
module

public import InfoGeometry.Exceptional.CFSGPort.CoxeterMatsumoto.Matsumoto

public section

namespace InfoGeometry.Exceptional.CFSGPort.CoxeterMatsumoto

open CoxeterSystem

universe u w

variable {I : Type*}

section PositiveLift

variable {M : CoxeterMatrix I} {W : Type*} [Group W] (cs : CoxeterSystem M W)
  {G : Type*} [Group G] (f : I → G)
  (hf : ∀ i j, ((braidWord M i j).map f).prod = ((braidWord M j i).map f).prod)

local prefix:100 "ℓ " => cs.length

noncomputable def posLift : W → G :=
  (TauCeti.existsUnique_reducedWordLift cs f hf).exists.choose

theorem posLift_wordProd {ω : List I} (hω : cs.IsReduced ω) :
    posLift cs f hf (cs.wordProd ω) = (ω.map f).prod :=
  (TauCeti.existsUnique_reducedWordLift cs f hf).exists.choose_spec ω hω

theorem posLift_one : posLift cs f hf 1 = 1 := by
  have h := posLift_wordProd cs f hf (ω := []) (by simp [CoxeterSystem.IsReduced])
  simpa using h

theorem posLift_mul {a b : W} (h : ℓ (a * b) = ℓ a + ℓ b) :
    posLift cs f hf (a * b) = posLift cs f hf a * posLift cs f hf b := by
  obtain ⟨ωa, hωa, rfl⟩ := cs.exists_isReduced a
  obtain ⟨ωb, hωb, rfl⟩ := cs.exists_isReduced b
  have hred : cs.IsReduced (ωa ++ ωb) := by
    rw [CoxeterSystem.IsReduced, cs.wordProd_append, h, hωa.eq, hωb.eq, List.length_append]
  rw [← cs.wordProd_append, posLift_wordProd cs f hf hred, posLift_wordProd cs f hf hωa,
    posLift_wordProd cs f hf hωb, List.map_append, List.prod_append]

theorem posLift_simple_mul {w : W} {k : I} (h : ¬ cs.IsLeftDescent w k) :
    posLift cs f hf (cs.simple k * w) = f k * posLift cs f hf w := by
  have hlen : ℓ (cs.simple k * w) = ℓ (cs.simple k) + ℓ w := by
    rw [cs.not_isLeftDescent_iff.mp h, cs.length_simple, add_comm]
  rw [posLift_mul cs f hf hlen]
  congr 1
  have h1 := posLift_wordProd cs f hf (ω := [k]) (by
    rw [CoxeterSystem.IsReduced, cs.wordProd_singleton, cs.length_simple]; rfl)
  simpa using h1

theorem posLift_mem (S : Subgroup G) (hS : ∀ i, f i ∈ S) (w : W) : posLift cs f hf w ∈ S := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [posLift_wordProd cs f hf hω]
  exact S.list_prod_mem fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact hS i

theorem map_posLift {G' : Type*} [Group G'] (g : G →* G')
    (hf' : ∀ i j, ((braidWord M i j).map (g ∘ f)).prod = ((braidWord M j i).map (g ∘ f)).prod)
    (w : W) : g (posLift cs f hf w) = posLift cs (g ∘ f) hf' w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [posLift_wordProd cs f hf hω, posLift_wordProd cs _ hf' hω, map_list_prod, List.map_map]

end PositiveLift

end InfoGeometry.Exceptional.CFSGPort.CoxeterMatsumoto
