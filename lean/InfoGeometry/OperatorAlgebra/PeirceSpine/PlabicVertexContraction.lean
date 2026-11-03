/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing
import InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentZornChainArchetypes

/-!
# Ordered Peirce-ring identities for eliminating a three-corner middle site

The signed contraction is stated with its actual ordered-product result. In
particular, its two-hop term is the symmetric bridge, not the antisymmetric
edge coordinate.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.PlabicVertexContraction

open InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentZornChainArchetypes

variable {B : Type*} [Ring B]

/-- Contract a middle idempotent against an incoming and outgoing nilpotent
sum. The factors remain in the indicated noncommutative order. -/
theorem middle_vertex_contraction {e q r : B}
    (hqe : q * e = q) (her : e * r = r)
    (hq : q * q = 0) (hr : r * r = 0) :
    (1 - q) * (e + q + r) * (1 - r) = e - q * r := by
  noncomm_ring [hqe, her, hq, hr]

/-- The signed counterpart of middle-vertex contraction. The surviving term
is the ordered product `q*s`; the statement makes no symmetry assumption. -/
theorem middle_vertex_signed_contraction {e q s : B}
    (hqe : q * e = q) (hes : e * s = s)
    (hq : q * q = 0) (hs : s * s = 0) :
    (1 - q) * (e + q - s) * (1 + s) = e + q * s := by
  noncomm_ring [hqe, hes, hq, hs]

/-- Contraction of the four directed arrows around an orthogonal middle
corner. The endpoint self-products and both parallel two-hop paths are
retained explicitly. -/
theorem three_corner_plabic_contraction
    {E₁ E₂ E₃ A C₁ C₂ D : B}
    (hE₂ : E₂ * E₂ = E₂)
    (h₁₂ : E₁ * E₂ = 0) (h₂₁ : E₂ * E₁ = 0)
    (h₂₃ : E₂ * E₃ = 0) (h₃₂ : E₃ * E₂ = 0) :
    let x := root12 E₁ E₂ A
    let y := root21 E₂ E₁ C₁
    let u := root23 E₂ E₃ C₂
    let v := root32 E₃ E₂ D
    (1 - x - v) * (E₂ + x + y + u + v) * (1 - y - u) =
      E₂ - (x * y + v * u) - (x * u + v * y) ∧
    (1 - x + v) * (E₂ + x - y + u - v) * (1 + y - u) =
      E₂ + (x * y + v * u) - (x * u + v * y) := by
  dsimp
  let x := root12 E₁ E₂ A
  let y := root21 E₂ E₁ C₁
  let u := root23 E₂ E₃ C₂
  let v := root32 E₃ E₂ D
  have hxe : x * E₂ = x := by
    dsimp [x, root12]
    rw [mul_assoc, hE₂]
  have hve : v * E₂ = v := by
    dsimp [v, root32]
    rw [mul_assoc, hE₂]
  have hey : E₂ * y = y := by
    dsimp [y, root21]
    calc
      E₂ * (E₂ * C₁ * E₁) = (E₂ * E₂) * C₁ * E₁ := by noncomm_ring
      _ = E₂ * C₁ * E₁ := by rw [hE₂]
  have heu : E₂ * u = u := by
    dsimp [u, root23]
    calc
      E₂ * (E₂ * C₂ * E₃) = (E₂ * E₂) * C₂ * E₃ := by noncomm_ring
      _ = E₂ * C₂ * E₃ := by rw [hE₂]
  have hxx : x * x = 0 := by
    dsimp [x, root12]
    calc
      (E₁ * A * E₂) * (E₁ * A * E₂) = E₁ * A * (E₂ * E₁) * A * E₂ := by
        noncomm_ring
      _ = 0 := by rw [h₂₁]; noncomm_ring
  have hvv : v * v = 0 := by
    dsimp [v, root32]
    calc
      (E₃ * D * E₂) * (E₃ * D * E₂) = E₃ * D * (E₂ * E₃) * D * E₂ := by
        noncomm_ring
      _ = 0 := by rw [h₂₃]; noncomm_ring
  have hxv : x * v = 0 := by
    dsimp [x, v, root12, root32]
    calc
      (E₁ * A * E₂) * (E₃ * D * E₂) = E₁ * A * (E₂ * E₃) * D * E₂ := by
        noncomm_ring
      _ = 0 := by rw [h₂₃]; noncomm_ring
  have hvx : v * x = 0 := by
    dsimp [x, v, root12, root32]
    calc
      (E₃ * D * E₂) * (E₁ * A * E₂) = E₃ * D * (E₂ * E₁) * A * E₂ := by
        noncomm_ring
      _ = 0 := by rw [h₂₁]; noncomm_ring
  have hyy : y * y = 0 := by
    dsimp [y, root21]
    calc
      (E₂ * C₁ * E₁) * (E₂ * C₁ * E₁) = E₂ * C₁ * (E₁ * E₂) * C₁ * E₁ := by
        noncomm_ring
      _ = 0 := by rw [h₁₂]; noncomm_ring
  have huu : u * u = 0 := by
    dsimp [u, root23]
    calc
      (E₂ * C₂ * E₃) * (E₂ * C₂ * E₃) = E₂ * C₂ * (E₃ * E₂) * C₂ * E₃ := by
        noncomm_ring
      _ = 0 := by rw [h₃₂]; noncomm_ring
  have hyu : y * u = 0 := by
    dsimp [y, u, root21, root23]
    calc
      (E₂ * C₁ * E₁) * (E₂ * C₂ * E₃) = E₂ * C₁ * (E₁ * E₂) * C₂ * E₃ := by
        noncomm_ring
      _ = 0 := by rw [h₁₂]; noncomm_ring
  have huy : u * y = 0 := by
    dsimp [y, u, root21, root23]
    calc
      (E₂ * C₂ * E₃) * (E₂ * C₁ * E₁) = E₂ * C₂ * (E₃ * E₂) * C₁ * E₁ := by
        noncomm_ring
      _ = 0 := by rw [h₃₂]; noncomm_ring
  have hqE : (x + v) * E₂ = x + v := by rw [add_mul, hxe, hve]
  have hrE : E₂ * (y + u) = y + u := by rw [mul_add, hey, heu]
  have hq2 : (x + v) * (x + v) = 0 := by
    noncomm_ring [hxx, hvv, hxv, hvx]
  have hr2 : (y + u) * (y + u) = 0 := by
    noncomm_ring [hyy, huu, hyu, huy]
  have hleft := middle_vertex_contraction hqE hrE hq2 hr2
  have hqsE : (x - v) * E₂ = x - v := by rw [sub_mul, hxe, hve]
  have hEs : E₂ * (y - u) = y - u := by rw [mul_sub, hey, heu]
  have hqs2 : (x - v) * (x - v) = 0 := by
    noncomm_ring [hxx, hvv, hxv, hvx]
  have hs2 : (y - u) * (y - u) = 0 := by
    noncomm_ring [hyy, huu, hyu, huy]
  have hright := middle_vertex_signed_contraction hqsE hEs hqs2 hs2
  constructor
  · calc
      (1 - x - v) * (E₂ + x + y + u + v) * (1 - y - u) =
          (1 - (x + v)) * (E₂ + (x + v) + (y + u)) * (1 - (y + u)) := by
            noncomm_ring
      _ = E₂ - (x + v) * (y + u) := hleft
      _ = E₂ - (x * y + v * u) - (x * u + v * y) := by noncomm_ring
  · calc
      (1 - x + v) * (E₂ + x - y + u - v) * (1 + y - u) =
          (1 - (x - v)) * (E₂ + (x - v) - (y - u)) * (1 + (y - u)) := by
            noncomm_ring
      _ = E₂ + (x - v) * (y - u) := hright
      _ = E₂ + (x * y + v * u) - (x * u + v * y) := by noncomm_ring

/-- Specialization of the two contractions to the shells cut out by a nested
pair of idempotents. -/
theorem nested_zorn_plabic_vertex_contraction
    {P₁ P₂ A C₁ C₂ D : B}
    (hP₁ : P₁ * P₁ = P₁) (hP₂ : P₂ * P₂ = P₂)
    (hChain : idemLe P₁ P₂) :
    let E₁ := shell1 P₁
    let E₂ := shell2 P₁ P₂
    let E₃ := shell3 P₂
    let x := root12 E₁ E₂ A
    let y := root21 E₂ E₁ C₁
    let u := root23 E₂ E₃ C₂
    let v := root32 E₃ E₂ D
    (1 - x - v) * (E₂ + x + y + u + v) * (1 - y - u) =
      E₂ - (x * y + v * u) - (x * u + v * y) ∧
    (1 - x + v) * (E₂ + x - y + u - v) * (1 + y - u) =
      E₂ + (x * y + v * u) - (x * u + v * y) := by
  intro E₁ E₂ E₃ x y u v
  rcases three_shell_partition hP₁ hP₂ hChain with
    ⟨_, _, hE₂, _, h₁₂, h₂₁, _, _, h₂₃, h₃₂⟩
  exact three_corner_plabic_contraction hE₂ h₁₂ h₂₁ h₂₃ h₃₂

end InfoGeometry.OperatorAlgebra.PeirceSpine.PlabicVertexContraction
