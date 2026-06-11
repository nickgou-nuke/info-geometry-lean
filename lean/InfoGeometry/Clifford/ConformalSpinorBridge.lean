import Mathlib
import InfoGeometry.Algebra.SuperLieRing
import InfoGeometry.Clifford.ConformalLieAlgebra55

/-!
# InfoGeometry.Clifford.ConformalSpinorBridge

The odd spinor sector of `𝔬𝔰𝔭(1|2)` as a `SuperLieRing` instance, realized
in the `Cl(5,5)` Clifford algebra.

## Generators

Even (3): `H = D5` (dilation), `Ep = u5` (translation P), `Em = v5` (special conformal K)
Odd  (2): `G1`, `G2` — the off-diagonal spinor generators in the (2|1) supermatrix format.

## Brackets

Even-even (𝔰𝔩₂):
  `[H, Ep] = 2·Ep`     `[H, Em] = -2·Em`     `[Ep, Em] = H`

Even-odd (spinor action):
  `[H, G1] = G1`       `[H, G2] = -G2`
  `[Ep, G1] = 0`       `[Ep, G2] = G1`
  `[Em, G1] = G2`      `[Em, G2] = 0`

Odd-odd (symmetric anticommutator):
  `{G1, G1} = 2·Ep`    `{G2, G2} = -2·Em`   `{G1, G2} = {G2, G1} = -H`

Super-Jacobi: verified by SymPy on all 125 homogeneous basis triples.

SymPy witness: `tools/sympy/osp12_spinor_bridge.py`
-/

open InfoGeometry.Algebra

noncomputable section

namespace InfoGeometry.Clifford.ConformalSpinorBridge

open InfoGeometry.Clifford.ConformalLieAlgebra55

set_option maxHeartbeats 800000

/-! ## 1. The 5-dimensional carrier -/

/--
Indices for the 5-element basis {H, Ep, Em, G1, G2}.
-/
inductive B : Type
  | H | Ep | Em | G1 | G2
  deriving DecidableEq, Fintype

open B

/-- The 5-dimensional ℝ-vector space. -/
abbrev OSp12 : Type := B → ℝ

namespace OSp12

instance : AddCommGroup OSp12 := by unfold OSp12; infer_instance
instance : Module ℝ OSp12 := by unfold OSp12; infer_instance

/-! ## 2. Structure constants -/

noncomputable def structConst (i j k : B) : ℚ :=
  match i, j, k with
  | .H,  .Ep, .Ep =>  2    | .Ep, .H,  .Ep => -2
  | .H,  .Em, .Em => -2    | .Em, .H,  .Em =>  2
  | .Ep, .Em, .H  =>  1    | .Em, .Ep, .H  => -1
  | .H,  .G1, .G1 =>  1    | .G1, .H,  .G1 => -1
  | .H,  .G2, .G2 => -1    | .G2, .H,  .G2 =>  1
  | .Ep, .G2, .G1 =>  1    | .G2, .Ep, .G1 => -1
  | .Em, .G1, .G2 =>  1    | .G1, .Em, .G2 => -1
  | .G1, .G2, .H  => -1    | .G2, .G1, .H  => -1
  | .G1, .G1, .Ep =>  2
  | .G2, .G2, .Em => -2
  | _, _, _ => 0

noncomputable def bracket (x y : OSp12) : OSp12 := λ k =>
  ∑ i : B, ∑ j : B, (structConst i j k : ℝ) * (x i) * (y j)

/-! ## 3. SuperLieRing instance -/

noncomputable def evenPart : Submodule ℝ OSp12 :=
  Submodule.span ℝ {λ | .H => 1 | _ => 0, λ | .Ep => 1 | _ => 0, λ | .Em => 1 | _ => 0}

noncomputable def oddPart : Submodule ℝ OSp12 :=
  Submodule.span ℝ {λ | .G1 => 1 | _ => 0, λ | .G2 => 1 | _ => 0}

private theorem even_odd_gen_H_G1 :
    bracket (Pi.single B.H (1 : ℝ)) (Pi.single B.G1 (1 : ℝ)) =
      - bracket (Pi.single B.G1 (1 : ℝ)) (Pi.single B.H (1 : ℝ)) := by
  ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]

private theorem even_odd_gen_H_G2 :
    bracket (Pi.single B.H (1 : ℝ)) (Pi.single B.G2 (1 : ℝ)) =
      - bracket (Pi.single B.G2 (1 : ℝ)) (Pi.single B.H (1 : ℝ)) := by
  ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]

private theorem even_odd_gen_Ep_G1 :
    bracket (Pi.single B.Ep (1 : ℝ)) (Pi.single B.G1 (1 : ℝ)) =
      - bracket (Pi.single B.G1 (1 : ℝ)) (Pi.single B.Ep (1 : ℝ)) := by
  ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]

private theorem even_odd_gen_Ep_G2 :
    bracket (Pi.single B.Ep (1 : ℝ)) (Pi.single B.G2 (1 : ℝ)) =
      - bracket (Pi.single B.G2 (1 : ℝ)) (Pi.single B.Ep (1 : ℝ)) := by
  ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]

private theorem even_odd_gen_Em_G1 :
    bracket (Pi.single B.Em (1 : ℝ)) (Pi.single B.G1 (1 : ℝ)) =
      - bracket (Pi.single B.G1 (1 : ℝ)) (Pi.single B.Em (1 : ℝ)) := by
  ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]

private theorem even_odd_gen_Em_G2 :
    bracket (Pi.single B.Em (1 : ℝ)) (Pi.single B.G2 (1 : ℝ)) =
      - bracket (Pi.single B.G2 (1 : ℝ)) (Pi.single B.Em (1 : ℝ)) := by
  ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]

private theorem odd_odd_gen_G1_G2 :
    bracket (Pi.single B.G1 (1 : ℝ)) (Pi.single B.G2 (1 : ℝ)) =
      bracket (Pi.single B.G2 (1 : ℝ)) (Pi.single B.G1 (1 : ℝ)) := by
  ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]

private theorem jacobi_even_basis
    (x : OSp12)
    (hx : x ∈ ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} :
      Set OSp12)) :
    ∀ (y z : OSp12),
      bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z) := by
  rcases hx with rfl | rfl | rfl
  · let S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
    have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
      ext v
      constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
    have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
      rw [S, hrange]
      exact (Pi.basisFun ℝ B).span_eq
    intro y z
    have hy : y ∈ Submodule.span ℝ S := by
      simpa [hspan] using (show y ∈ (⊤ : Submodule ℝ OSp12) from by simp)
    have hz : z ∈ Submodule.span ℝ S := by
      simpa [hspan] using (show z ∈ (⊤ : Submodule ℝ OSp12) from by simp)
    have hsmul_left : ∀ (r : ℝ) (a b : OSp12), bracket (r • a) b = r • bracket a b := by
      intro r a b
      ext k
      simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
    refine
      Submodule.span_induction₂
        (s := S) (t := S)
        (p := fun y z _ _ =>
          bracket (Pi.single B.H (1 : ℝ)) (bracket y z) =
            bracket (bracket (Pi.single B.H (1 : ℝ)) y) z +
              bracket y (bracket (Pi.single B.H (1 : ℝ)) z))
        ?mem_mem ?zero_left ?zero_right ?add_left ?add_right ?smul_left ?smul_right hy hz
    · intro y z hygen hzgen
      rcases hygen with ⟨a, rfl⟩
      rcases hzgen with ⟨b, rfl⟩
      cases a <;> cases b <;>
        ext k <;> fin_cases k <;>
          simp [bracket, Pi.single, Function.update, structConst]
    · intro z hz'
      ext k <;>
        simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
          smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    · intro y hy'
      ext k <;>
        simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
          smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    · intro y₁ y₂ z hy₁ hy₂ hz' h₁ h₂
      calc
        bracket (Pi.single B.H (1 : ℝ)) (bracket (y₁ + y₂) z)
            = bracket (Pi.single B.H (1 : ℝ)) (bracket y₁ z + bracket y₂ z) := by
                rw [SuperBracket.add_lie]
        _ = bracket (Pi.single B.H (1 : ℝ)) (bracket y₁ z) +
              bracket (Pi.single B.H (1 : ℝ)) (bracket y₂ z) := by
              rw [SuperBracket.lie_add]
        _ = (bracket (bracket (Pi.single B.H (1 : ℝ)) y₁) z +
              bracket y₁ (bracket (Pi.single B.H (1 : ℝ)) z)) +
            (bracket (bracket (Pi.single B.H (1 : ℝ)) y₂) z +
              bracket y₂ (bracket (Pi.single B.H (1 : ℝ)) z)) := by
              rw [h₁, h₂]
        _ = bracket (bracket (Pi.single B.H (1 : ℝ)) (y₁ + y₂)) z +
              bracket (y₁ + y₂) (bracket (Pi.single B.H (1 : ℝ)) z) := by
              simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                add_assoc]
    · intro y z₁ z₂ hy' hz₁ hz₂ h₁ h₂
      calc
        bracket (Pi.single B.H (1 : ℝ)) (bracket y (z₁ + z₂))
            = bracket (Pi.single B.H (1 : ℝ)) (bracket y z₁ + bracket y z₂) := by
                rw [SuperBracket.lie_add]
        _ = bracket (Pi.single B.H (1 : ℝ)) (bracket y z₁) +
              bracket (Pi.single B.H (1 : ℝ)) (bracket y z₂) := by
              rw [SuperBracket.lie_add]
        _ = (bracket (bracket (Pi.single B.H (1 : ℝ)) y) z₁ +
              bracket y (bracket (Pi.single B.H (1 : ℝ)) z₁)) +
            (bracket (bracket (Pi.single B.H (1 : ℝ)) y) z₂ +
              bracket y (bracket (Pi.single B.H (1 : ℝ)) z₂)) := by
              rw [h₁, h₂]
        _ = bracket (bracket (Pi.single B.H (1 : ℝ)) y) (z₁ + z₂) +
              bracket y (bracket (Pi.single B.H (1 : ℝ)) (z₁ + z₂)) := by
              simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                add_assoc]
    · intro r y z hy' hz' h
      calc
        bracket (Pi.single B.H (1 : ℝ)) (bracket (r • y) z)
            = bracket (Pi.single B.H (1 : ℝ)) (r • bracket y z) := by
                rw [hsmul_left]
        _ = r • bracket (Pi.single B.H (1 : ℝ)) (bracket y z) := by
              rw [SuperBracket.lie_smul]
        _ = r • (bracket (bracket (Pi.single B.H (1 : ℝ)) y) z +
              bracket y (bracket (Pi.single B.H (1 : ℝ)) z)) := by
              rw [h]
        _ = bracket (bracket (Pi.single B.H (1 : ℝ)) (r • y)) z +
              bracket (r • y) (bracket (Pi.single B.H (1 : ℝ)) z) := by
              simp [hsmul_left, SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm,
                add_left_comm, add_assoc]
    · intro r y z hy' hz' h
      calc
        bracket (Pi.single B.H (1 : ℝ)) (bracket y (r • z))
            = bracket (Pi.single B.H (1 : ℝ)) (r • bracket y z) := by
                rw [SuperBracket.lie_smul]
        _ = r • bracket (Pi.single B.H (1 : ℝ)) (bracket y z) := by
              rw [SuperBracket.lie_smul]
        _ = r • (bracket (bracket (Pi.single B.H (1 : ℝ)) y) z +
              bracket y (bracket (Pi.single B.H (1 : ℝ)) z)) := by
              rw [h]
        _ = bracket (bracket (Pi.single B.H (1 : ℝ)) y) (r • z) +
              bracket y (bracket (Pi.single B.H (1 : ℝ)) (r • z)) := by
              simp [SuperBracket.lie_smul, SuperBracket.add_lie_left, SuperBracket.lie_add,
                add_comm, add_left_comm, add_assoc]
  · let S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
    have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
      ext v
      constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
    have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
      rw [S, hrange]
      exact (Pi.basisFun ℝ B).span_eq
    intro y z
    have hy : y ∈ Submodule.span ℝ S := by
      simpa [hspan] using (show y ∈ (⊤ : Submodule ℝ OSp12) from by simp)
    have hz : z ∈ Submodule.span ℝ S := by
      simpa [hspan] using (show z ∈ (⊤ : Submodule ℝ OSp12) from by simp)
    have hsmul_left : ∀ (r : ℝ) (a b : OSp12), bracket (r • a) b = r • bracket a b := by
      intro r a b
      ext k
      simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
    refine
      Submodule.span_induction₂
        (s := S) (t := S)
        (p := fun y z _ _ =>
          bracket (Pi.single B.Ep (1 : ℝ)) (bracket y z) =
            bracket (bracket (Pi.single B.Ep (1 : ℝ)) y) z +
              bracket y (bracket (Pi.single B.Ep (1 : ℝ)) z))
        ?mem_mem ?zero_left ?zero_right ?add_left ?add_right ?smul_left ?smul_right hy hz
    · intro y z hygen hzgen
      rcases hygen with ⟨a, rfl⟩
      rcases hzgen with ⟨b, rfl⟩
      cases a <;> cases b <;>
        ext k <;> fin_cases k <;>
          simp [bracket, Pi.single, Function.update, structConst]
    · intro z hz'
      ext k <;>
        simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
          smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    · intro y hy'
      ext k <;>
        simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
          smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    · intro y₁ y₂ z hy₁ hy₂ hz' h₁ h₂
      calc
        bracket (Pi.single B.Ep (1 : ℝ)) (bracket (y₁ + y₂) z)
            = bracket (Pi.single B.Ep (1 : ℝ)) (bracket y₁ z + bracket y₂ z) := by
                rw [SuperBracket.add_lie]
        _ = bracket (Pi.single B.Ep (1 : ℝ)) (bracket y₁ z) +
              bracket (Pi.single B.Ep (1 : ℝ)) (bracket y₂ z) := by
              rw [SuperBracket.lie_add]
        _ = (bracket (bracket (Pi.single B.Ep (1 : ℝ)) y₁) z +
              bracket y₁ (bracket (Pi.single B.Ep (1 : ℝ)) z)) +
            (bracket (bracket (Pi.single B.Ep (1 : ℝ)) y₂) z +
              bracket y₂ (bracket (Pi.single B.Ep (1 : ℝ)) z)) := by
              rw [h₁, h₂]
        _ = bracket (bracket (Pi.single B.Ep (1 : ℝ)) (y₁ + y₂)) z +
              bracket (y₁ + y₂) (bracket (Pi.single B.Ep (1 : ℝ)) z) := by
              simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                add_assoc]
    · intro y z₁ z₂ hy' hz₁ hz₂ h₁ h₂
      calc
        bracket (Pi.single B.Ep (1 : ℝ)) (bracket y (z₁ + z₂))
            = bracket (Pi.single B.Ep (1 : ℝ)) (bracket y z₁ + bracket y z₂) := by
                rw [SuperBracket.lie_add]
        _ = bracket (Pi.single B.Ep (1 : ℝ)) (bracket y z₁) +
              bracket (Pi.single B.Ep (1 : ℝ)) (bracket y z₂) := by
              rw [SuperBracket.lie_add]
        _ = (bracket (bracket (Pi.single B.Ep (1 : ℝ)) y) z₁ +
              bracket y (bracket (Pi.single B.Ep (1 : ℝ)) z₁)) +
            (bracket (bracket (Pi.single B.Ep (1 : ℝ)) y) z₂ +
              bracket y (bracket (Pi.single B.Ep (1 : ℝ)) z₂)) := by
              rw [h₁, h₂]
        _ = bracket (bracket (Pi.single B.Ep (1 : ℝ)) y) (z₁ + z₂) +
              bracket y (bracket (Pi.single B.Ep (1 : ℝ)) (z₁ + z₂)) := by
              simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                add_assoc]
    · intro r y z hy' hz' h
      calc
        bracket (Pi.single B.Ep (1 : ℝ)) (bracket (r • y) z)
            = bracket (Pi.single B.Ep (1 : ℝ)) (r • bracket y z) := by
                rw [hsmul_left]
        _ = r • bracket (Pi.single B.Ep (1 : ℝ)) (bracket y z) := by
              rw [SuperBracket.lie_smul]
        _ = r • (bracket (bracket (Pi.single B.Ep (1 : ℝ)) y) z +
              bracket y (bracket (Pi.single B.Ep (1 : ℝ)) z)) := by
              rw [h]
        _ = bracket (bracket (Pi.single B.Ep (1 : ℝ)) (r • y)) z +
              bracket (r • y) (bracket (Pi.single B.Ep (1 : ℝ)) z) := by
              simp [hsmul_left, SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm,
                add_left_comm, add_assoc]
    · intro r y z hy' hz' h
      calc
        bracket (Pi.single B.Ep (1 : ℝ)) (bracket y (r • z))
            = bracket (Pi.single B.Ep (1 : ℝ)) (r • bracket y z) := by
                rw [SuperBracket.lie_smul]
        _ = r • bracket (Pi.single B.Ep (1 : ℝ)) (bracket y z) := by
              rw [SuperBracket.lie_smul]
        _ = r • (bracket (bracket (Pi.single B.Ep (1 : ℝ)) y) z +
              bracket y (bracket (Pi.single B.Ep (1 : ℝ)) z)) := by
              rw [h]
        _ = bracket (bracket (Pi.single B.Ep (1 : ℝ)) y) (r • z) +
              bracket y (bracket (Pi.single B.Ep (1 : ℝ)) (r • z)) := by
              simp [SuperBracket.lie_smul, SuperBracket.add_lie_left, SuperBracket.lie_add,
                add_comm, add_left_comm, add_assoc]
  · let S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
    have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
      ext v
      constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
    have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
      rw [S, hrange]
      exact (Pi.basisFun ℝ B).span_eq
    intro y z
    have hy : y ∈ Submodule.span ℝ S := by
      simpa [hspan] using (show y ∈ (⊤ : Submodule ℝ OSp12) from by simp)
    have hz : z ∈ Submodule.span ℝ S := by
      simpa [hspan] using (show z ∈ (⊤ : Submodule ℝ OSp12) from by simp)
    have hsmul_left : ∀ (r : ℝ) (a b : OSp12), bracket (r • a) b = r • bracket a b := by
      intro r a b
      ext k
      simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
    refine
      Submodule.span_induction₂
        (s := S) (t := S)
        (p := fun y z _ _ =>
          bracket (Pi.single B.Em (1 : ℝ)) (bracket y z) =
            bracket (bracket (Pi.single B.Em (1 : ℝ)) y) z +
              bracket y (bracket (Pi.single B.Em (1 : ℝ)) z))
        ?mem_mem ?zero_left ?zero_right ?add_left ?add_right ?smul_left ?smul_right hy hz
    · intro y z hygen hzgen
      rcases hygen with ⟨a, rfl⟩
      rcases hzgen with ⟨b, rfl⟩
      cases a <;> cases b <;>
        ext k <;> fin_cases k <;>
          simp [bracket, Pi.single, Function.update, structConst]
    · intro z hz'
      ext k <;>
        simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
          smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    · intro y hy'
      ext k <;>
        simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
          smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    · intro y₁ y₂ z hy₁ hy₂ hz' h₁ h₂
      calc
        bracket (Pi.single B.Em (1 : ℝ)) (bracket (y₁ + y₂) z)
            = bracket (Pi.single B.Em (1 : ℝ)) (bracket y₁ z + bracket y₂ z) := by
                rw [SuperBracket.add_lie]
        _ = bracket (Pi.single B.Em (1 : ℝ)) (bracket y₁ z) +
              bracket (Pi.single B.Em (1 : ℝ)) (bracket y₂ z) := by
              rw [SuperBracket.lie_add]
        _ = (bracket (bracket (Pi.single B.Em (1 : ℝ)) y₁) z +
              bracket y₁ (bracket (Pi.single B.Em (1 : ℝ)) z)) +
            (bracket (bracket (Pi.single B.Em (1 : ℝ)) y₂) z +
              bracket y₂ (bracket (Pi.single B.Em (1 : ℝ)) z)) := by
              rw [h₁, h₂]
        _ = bracket (bracket (Pi.single B.Em (1 : ℝ)) (y₁ + y₂)) z +
              bracket (y₁ + y₂) (bracket (Pi.single B.Em (1 : ℝ)) z) := by
              simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                add_assoc]
    · intro y z₁ z₂ hy' hz₁ hz₂ h₁ h₂
      calc
        bracket (Pi.single B.Em (1 : ℝ)) (bracket y (z₁ + z₂))
            = bracket (Pi.single B.Em (1 : ℝ)) (bracket y z₁ + bracket y z₂) := by
                rw [SuperBracket.lie_add]
        _ = bracket (Pi.single B.Em (1 : ℝ)) (bracket y z₁) +
              bracket (Pi.single B.Em (1 : ℝ)) (bracket y z₂) := by
              rw [SuperBracket.lie_add]
        _ = (bracket (bracket (Pi.single B.Em (1 : ℝ)) y) z₁ +
              bracket y (bracket (Pi.single B.Em (1 : ℝ)) z₁)) +
            (bracket (bracket (Pi.single B.Em (1 : ℝ)) y) z₂ +
              bracket y (bracket (Pi.single B.Em (1 : ℝ)) z₂)) := by
              rw [h₁, h₂]
        _ = bracket (bracket (Pi.single B.Em (1 : ℝ)) y) (z₁ + z₂) +
              bracket y (bracket (Pi.single B.Em (1 : ℝ)) (z₁ + z₂)) := by
              simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                add_assoc]
    · intro r y z hy' hz' h
      calc
        bracket (Pi.single B.Em (1 : ℝ)) (bracket (r • y) z)
            = bracket (Pi.single B.Em (1 : ℝ)) (r • bracket y z) := by
                rw [hsmul_left]
        _ = r • bracket (Pi.single B.Em (1 : ℝ)) (bracket y z) := by
              rw [SuperBracket.lie_smul]
        _ = r • (bracket (bracket (Pi.single B.Em (1 : ℝ)) y) z +
              bracket y (bracket (Pi.single B.Em (1 : ℝ)) z)) := by
              rw [h]
        _ = bracket (bracket (Pi.single B.Em (1 : ℝ)) (r • y)) z +
              bracket (r • y) (bracket (Pi.single B.Em (1 : ℝ)) z) := by
              simp [hsmul_left, SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm,
                add_left_comm, add_assoc]
    · intro r y z hy' hz' h
      calc
        bracket (Pi.single B.Em (1 : ℝ)) (bracket y (r • z))
            = bracket (Pi.single B.Em (1 : ℝ)) (r • bracket y z) := by
                rw [SuperBracket.lie_smul]
        _ = r • bracket (Pi.single B.Em (1 : ℝ)) (bracket y z) := by
              rw [SuperBracket.lie_smul]
        _ = r • (bracket (bracket (Pi.single B.Em (1 : ℝ)) y) z +
              bracket y (bracket (Pi.single B.Em (1 : ℝ)) z)) := by
              rw [h]
        _ = bracket (bracket (Pi.single B.Em (1 : ℝ)) y) (r • z) +
              bracket y (bracket (Pi.single B.Em (1 : ℝ)) (r • z)) := by
              simp [SuperBracket.lie_smul, SuperBracket.add_lie_left, SuperBracket.lie_add,
                add_comm, add_left_comm, add_assoc]

  · have x : OSp12 := Pi.single B.Ep (1 : ℝ)
    · have x : OSp12 := Pi.single B.H (1 : ℝ)
          set S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
          have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
            ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
          have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
            rw [hrange]
            exact (Pi.basisFun ℝ B).span_eq
          intro y z
          have hy : y ∈ Submodule.span ℝ S := by
            simpa [hspan] using (show y ∈ (⊤ : Submodule ℝ OSp12) from by simp)
          have hz : z ∈ Submodule.span ℝ S := by
            simpa [hspan] using (show z ∈ (⊤ : Submodule ℝ OSp12) from by simp)
          have hsmul_left : ∀ (r : ℝ) (a b : OSp12), bracket (r • a) b = r • bracket a b := by
            intro r a b
            ext k
            simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
          refine
            Submodule.span_induction₂
              (s := S) (t := S)
              (p := fun y z _ _ =>
                bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z))
              ?mem_mem ?zero_left ?zero_right ?add_left ?add_right ?smul_left ?smul_right hy hz
          · intro y z hygen hzgen
            rcases hygen with ⟨a, rfl⟩
            rcases hzgen with ⟨b, rfl⟩
            cases a <;> cases b <;>
              ext k <;> fin_cases k <;>
                simp [bracket, Pi.single, Function.update, structConst]
          · intro z hz'
            ext k <;>
              simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
                smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          · intro y hy'
            ext k <;>
              simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
                smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          · intro y₁ y₂ z hy₁ hy₂ hz' h₁ h₂
            calc
              bracket x (bracket (y₁ + y₂) z)
                  = bracket x (bracket y₁ z + bracket y₂ z) := by
                      rw [SuperBracket.add_lie]
              _ = bracket x (bracket y₁ z) + bracket x (bracket y₂ z) := by
                    rw [SuperBracket.lie_add]
              _ = (bracket (bracket x y₁) z + bracket y₁ (bracket x z)) +
                    (bracket (bracket x y₂) z + bracket y₂ (bracket x z)) := by
                    rw [h₁, h₂]
              _ = bracket (bracket x (y₁ + y₂)) z + bracket (y₁ + y₂) (bracket x z) := by
                    simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                      add_assoc]
          · intro y z₁ z₂ hy' hz₁ hz₂ h₁ h₂
            calc
              bracket x (bracket y (z₁ + z₂))
                  = bracket x (bracket y z₁ + bracket y z₂) := by
                      rw [SuperBracket.lie_add]
              _ = bracket x (bracket y z₁) + bracket x (bracket y z₂) := by
                    rw [SuperBracket.lie_add]
              _ = (bracket (bracket x y) z₁ + bracket y (bracket x z₁)) +
                    (bracket (bracket x y) z₂ + bracket y (bracket x z₂)) := by
                    rw [h₁, h₂]
              _ = bracket (bracket x y) (z₁ + z₂) + bracket y (bracket x (z₁ + z₂)) := by
                    simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                      add_assoc]
          · intro r y z hy' hz' h
            calc
              bracket x (bracket (r • y) z)
                  = bracket x (r • bracket y z) := by
                      rw [hsmul_left]
              _ = r • bracket x (bracket y z) := by
                    rw [SuperBracket.lie_smul]
              _ = r • (bracket (bracket x y) z + bracket y (bracket x z)) := by
                    rw [h]
              _ = bracket (bracket x (r • y)) z + bracket (r • y) (bracket x z) := by
                    simp [hsmul_left, SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm,
                      add_left_comm, add_assoc]
          · intro r y z hy' hz' h
            calc
              bracket x (bracket y (r • z))
                  = bracket x (r • bracket y z) := by
                      rw [SuperBracket.lie_smul]
              _ = r • bracket x (bracket y z) := by
                    rw [SuperBracket.lie_smul]
              _ = r • (bracket (bracket x y) z + bracket y (bracket x z)) := by
                    rw [h]
              _ = bracket (bracket x y) (r • z) + bracket y (bracket x (r • z)) := by
                    simp [SuperBracket.lie_smul, SuperBracket.add_lie_left, SuperBracket.lie_add,
                      add_comm, add_left_comm, add_assoc]
    · have x : OSp12 := Pi.single B.Ep (1 : ℝ)
          set S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
          have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
            ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
          have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
            rw [hrange]
            exact (Pi.basisFun ℝ B).span_eq
          intro y z
          have hy : y ∈ Submodule.span ℝ S := by
            simpa [hspan] using (show y ∈ (⊤ : Submodule ℝ OSp12) from by simp)
          have hz : z ∈ Submodule.span ℝ S := by
            simpa [hspan] using (show z ∈ (⊤ : Submodule ℝ OSp12) from by simp)
          have hsmul_left : ∀ (r : ℝ) (a b : OSp12), bracket (r • a) b = r • bracket a b := by
            intro r a b
            ext k
            simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
          refine
            Submodule.span_induction₂
              (s := S) (t := S)
              (p := fun y z _ _ =>
                bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z))
              ?mem_mem ?zero_left ?zero_right ?add_left ?add_right ?smul_left ?smul_right hy hz
          · intro y z hygen hzgen
            rcases hygen with ⟨a, rfl⟩
            rcases hzgen with ⟨b, rfl⟩
            cases a <;> cases b <;>
              ext k <;> fin_cases k <;>
                simp [bracket, Pi.single, Function.update, structConst]
          · intro z hz'
            ext k <;>
              simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
                smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          · intro y hy'
            ext k <;>
              simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
                smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          · intro y₁ y₂ z hy₁ hy₂ hz' h₁ h₂
            calc
              bracket x (bracket (y₁ + y₂) z)
                  = bracket x (bracket y₁ z + bracket y₂ z) := by
                      rw [SuperBracket.add_lie]
              _ = bracket x (bracket y₁ z) + bracket x (bracket y₂ z) := by
                    rw [SuperBracket.lie_add]
              _ = (bracket (bracket x y₁) z + bracket y₁ (bracket x z)) +
                    (bracket (bracket x y₂) z + bracket y₂ (bracket x z)) := by
                    rw [h₁, h₂]
              _ = bracket (bracket x (y₁ + y₂)) z + bracket (y₁ + y₂) (bracket x z) := by
                    simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                      add_assoc]
          · intro y z₁ z₂ hy' hz₁ hz₂ h₁ h₂
            calc
              bracket x (bracket y (z₁ + z₂))
                  = bracket x (bracket y z₁ + bracket y z₂) := by
                      rw [SuperBracket.lie_add]
              _ = bracket x (bracket y z₁) + bracket x (bracket y z₂) := by
                    rw [SuperBracket.lie_add]
              _ = (bracket (bracket x y) z₁ + bracket y (bracket x z₁)) +
                    (bracket (bracket x y) z₂ + bracket y (bracket x z₂)) := by
                    rw [h₁, h₂]
              _ = bracket (bracket x y) (z₁ + z₂) + bracket y (bracket x (z₁ + z₂)) := by
                    simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                      add_assoc]
          · intro r y z hy' hz' h
            calc
              bracket x (bracket (r • y) z)
                  = bracket x (r • bracket y z) := by
                      rw [hsmul_left]
              _ = r • bracket x (bracket y z) := by
                    rw [SuperBracket.lie_smul]
              _ = r • (bracket (bracket x y) z + bracket y (bracket x z)) := by
                    rw [h]
              _ = bracket (bracket x (r • y)) z + bracket (r • y) (bracket x z) := by
                    simp [hsmul_left, SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm,
                      add_left_comm, add_assoc]
          · intro r y z hy' hz' h
            calc
              bracket x (bracket y (r • z))
                  = bracket x (r • bracket y z) := by
                      rw [SuperBracket.lie_smul]
              _ = r • bracket x (bracket y z) := by
                    rw [SuperBracket.lie_smul]
              _ = r • (bracket (bracket x y) z + bracket y (bracket x z)) := by
                    rw [h]
              _ = bracket (bracket x y) (r • z) + bracket y (bracket x (r • z)) := by
                    simp [SuperBracket.lie_smul, SuperBracket.add_lie_left, SuperBracket.lie_add,
                      add_comm, add_left_comm, add_assoc]
    · have x : OSp12 := Pi.single B.Em (1 : ℝ)
          set S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
          have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
            ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
          have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
            rw [hrange]
            exact (Pi.basisFun ℝ B).span_eq
          intro y z
          have hy : y ∈ Submodule.span ℝ S := by
            simpa [hspan] using (show y ∈ (⊤ : Submodule ℝ OSp12) from by simp)
          have hz : z ∈ Submodule.span ℝ S := by
            simpa [hspan] using (show z ∈ (⊤ : Submodule ℝ OSp12) from by simp)
          have hsmul_left : ∀ (r : ℝ) (a b : OSp12), bracket (r • a) b = r • bracket a b := by
            intro r a b
            ext k
            simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
          refine
            Submodule.span_induction₂
              (s := S) (t := S)
              (p := fun y z _ _ =>
                bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z))
              ?mem_mem ?zero_left ?zero_right ?add_left ?add_right ?smul_left ?smul_right hy hz
          · intro y z hygen hzgen
            rcases hygen with ⟨a, rfl⟩
            rcases hzgen with ⟨b, rfl⟩
            cases a <;> cases b <;>
              ext k <;> fin_cases k <;>
                simp [bracket, Pi.single, Function.update, structConst]
          · intro z hz'
            ext k <;>
              simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
                smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          · intro y hy'
            ext k <;>
              simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
                smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          · intro y₁ y₂ z hy₁ hy₂ hz' h₁ h₂
            calc
              bracket x (bracket (y₁ + y₂) z)
                  = bracket x (bracket y₁ z + bracket y₂ z) := by
                      rw [SuperBracket.add_lie]
              _ = bracket x (bracket y₁ z) + bracket x (bracket y₂ z) := by
                    rw [SuperBracket.lie_add]
              _ = (bracket (bracket x y₁) z + bracket y₁ (bracket x z)) +
                    (bracket (bracket x y₂) z + bracket y₂ (bracket x z)) := by
                    rw [h₁, h₂]
              _ = bracket (bracket x (y₁ + y₂)) z + bracket (y₁ + y₂) (bracket x z) := by
                    simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                      add_assoc]
          · intro y z₁ z₂ hy' hz₁ hz₂ h₁ h₂
            calc
              bracket x (bracket y (z₁ + z₂))
                  = bracket x (bracket y z₁ + bracket y z₂) := by
                      rw [SuperBracket.lie_add]
              _ = bracket x (bracket y z₁) + bracket x (bracket y z₂) := by
                    rw [SuperBracket.lie_add]
              _ = (bracket (bracket x y) z₁ + bracket y (bracket x z₁)) +
                    (bracket (bracket x y) z₂ + bracket y (bracket x z₂)) := by
                    rw [h₁, h₂]
              _ = bracket (bracket x y) (z₁ + z₂) + bracket y (bracket x (z₁ + z₂)) := by
                    simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                      add_assoc]
          · intro r y z hy' hz' h
            calc
              bracket x (bracket (r • y) z)
                  = bracket x (r • bracket y z) := by
                      rw [hsmul_left]
              _ = r • bracket x (bracket y z) := by
                    rw [SuperBracket.lie_smul]
              _ = r • (bracket (bracket x y) z + bracket y (bracket x z)) := by
                    rw [h]
              _ = bracket (bracket x (r • y)) z + bracket (r • y) (bracket x z) := by
                    simp [hsmul_left, SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm,
                      add_left_comm, add_assoc]
          · intro r y z hy' hz' h
            calc
              bracket x (bracket y (r • z))
                  = bracket x (r • bracket y z) := by
                      rw [SuperBracket.lie_smul]
              _ = r • bracket x (bracket y z) := by
                    rw [SuperBracket.lie_smul]
              _ = r • (bracket (bracket x y) z + bracket y (bracket x z)) := by
                    rw [h]
              _ = bracket (bracket x y) (r • z) + bracket y (bracket x (r • z)) := by
                    simp [SuperBracket.lie_smul, SuperBracket.add_lie_left, SuperBracket.lie_add,
                      add_comm, add_left_comm, add_assoc]

  · have x : OSp12 := Pi.single B.Em (1 : ℝ)
    · have x : OSp12 := Pi.single B.H (1 : ℝ)
          set S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
          have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
            ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
          have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
            rw [hrange]
            exact (Pi.basisFun ℝ B).span_eq
          intro y z
          have hy : y ∈ Submodule.span ℝ S := by
            simpa [hspan] using (show y ∈ (⊤ : Submodule ℝ OSp12) from by simp)
          have hz : z ∈ Submodule.span ℝ S := by
            simpa [hspan] using (show z ∈ (⊤ : Submodule ℝ OSp12) from by simp)
          have hsmul_left : ∀ (r : ℝ) (a b : OSp12), bracket (r • a) b = r • bracket a b := by
            intro r a b
            ext k
            simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
          refine
            Submodule.span_induction₂
              (s := S) (t := S)
              (p := fun y z _ _ =>
                bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z))
              ?mem_mem ?zero_left ?zero_right ?add_left ?add_right ?smul_left ?smul_right hy hz
          · intro y z hygen hzgen
            rcases hygen with ⟨a, rfl⟩
            rcases hzgen with ⟨b, rfl⟩
            cases a <;> cases b <;>
              ext k <;> fin_cases k <;>
                simp [bracket, Pi.single, Function.update, structConst]
          · intro z hz'
            ext k <;>
              simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
                smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          · intro y hy'
            ext k <;>
              simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
                smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          · intro y₁ y₂ z hy₁ hy₂ hz' h₁ h₂
            calc
              bracket x (bracket (y₁ + y₂) z)
                  = bracket x (bracket y₁ z + bracket y₂ z) := by
                      rw [SuperBracket.add_lie]
              _ = bracket x (bracket y₁ z) + bracket x (bracket y₂ z) := by
                    rw [SuperBracket.lie_add]
              _ = (bracket (bracket x y₁) z + bracket y₁ (bracket x z)) +
                    (bracket (bracket x y₂) z + bracket y₂ (bracket x z)) := by
                    rw [h₁, h₂]
              _ = bracket (bracket x (y₁ + y₂)) z + bracket (y₁ + y₂) (bracket x z) := by
                    simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                      add_assoc]
          · intro y z₁ z₂ hy' hz₁ hz₂ h₁ h₂
            calc
              bracket x (bracket y (z₁ + z₂))
                  = bracket x (bracket y z₁ + bracket y z₂) := by
                      rw [SuperBracket.lie_add]
              _ = bracket x (bracket y z₁) + bracket x (bracket y z₂) := by
                    rw [SuperBracket.lie_add]
              _ = (bracket (bracket x y) z₁ + bracket y (bracket x z₁)) +
                    (bracket (bracket x y) z₂ + bracket y (bracket x z₂)) := by
                    rw [h₁, h₂]
              _ = bracket (bracket x y) (z₁ + z₂) + bracket y (bracket x (z₁ + z₂)) := by
                    simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                      add_assoc]
          · intro r y z hy' hz' h
            calc
              bracket x (bracket (r • y) z)
                  = bracket x (r • bracket y z) := by
                      rw [hsmul_left]
              _ = r • bracket x (bracket y z) := by
                    rw [SuperBracket.lie_smul]
              _ = r • (bracket (bracket x y) z + bracket y (bracket x z)) := by
                    rw [h]
              _ = bracket (bracket x (r • y)) z + bracket (r • y) (bracket x z) := by
                    simp [hsmul_left, SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm,
                      add_left_comm, add_assoc]
          · intro r y z hy' hz' h
            calc
              bracket x (bracket y (r • z))
                  = bracket x (r • bracket y z) := by
                      rw [SuperBracket.lie_smul]
              _ = r • bracket x (bracket y z) := by
                    rw [SuperBracket.lie_smul]
              _ = r • (bracket (bracket x y) z + bracket y (bracket x z)) := by
                    rw [h]
              _ = bracket (bracket x y) (r • z) + bracket y (bracket x (r • z)) := by
                    simp [SuperBracket.lie_smul, SuperBracket.add_lie_left, SuperBracket.lie_add,
                      add_comm, add_left_comm, add_assoc]
    · have x : OSp12 := Pi.single B.Ep (1 : ℝ)
          set S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
          have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
            ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
          have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
            rw [hrange]
            exact (Pi.basisFun ℝ B).span_eq
          intro y z
          have hy : y ∈ Submodule.span ℝ S := by
            simpa [hspan] using (show y ∈ (⊤ : Submodule ℝ OSp12) from by simp)
          have hz : z ∈ Submodule.span ℝ S := by
            simpa [hspan] using (show z ∈ (⊤ : Submodule ℝ OSp12) from by simp)
          have hsmul_left : ∀ (r : ℝ) (a b : OSp12), bracket (r • a) b = r • bracket a b := by
            intro r a b
            ext k
            simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
          refine
            Submodule.span_induction₂
              (s := S) (t := S)
              (p := fun y z _ _ =>
                bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z))
              ?mem_mem ?zero_left ?zero_right ?add_left ?add_right ?smul_left ?smul_right hy hz
          · intro y z hygen hzgen
            rcases hygen with ⟨a, rfl⟩
            rcases hzgen with ⟨b, rfl⟩
            cases a <;> cases b <;>
              ext k <;> fin_cases k <;>
                simp [bracket, Pi.single, Function.update, structConst]
          · intro z hz'
            ext k <;>
              simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
                smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          · intro y hy'
            ext k <;>
              simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
                smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          · intro y₁ y₂ z hy₁ hy₂ hz' h₁ h₂
            calc
              bracket x (bracket (y₁ + y₂) z)
                  = bracket x (bracket y₁ z + bracket y₂ z) := by
                      rw [SuperBracket.add_lie]
              _ = bracket x (bracket y₁ z) + bracket x (bracket y₂ z) := by
                    rw [SuperBracket.lie_add]
              _ = (bracket (bracket x y₁) z + bracket y₁ (bracket x z)) +
                    (bracket (bracket x y₂) z + bracket y₂ (bracket x z)) := by
                    rw [h₁, h₂]
              _ = bracket (bracket x (y₁ + y₂)) z + bracket (y₁ + y₂) (bracket x z) := by
                    simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                      add_assoc]
          · intro y z₁ z₂ hy' hz₁ hz₂ h₁ h₂
            calc
              bracket x (bracket y (z₁ + z₂))
                  = bracket x (bracket y z₁ + bracket y z₂) := by
                      rw [SuperBracket.lie_add]
              _ = bracket x (bracket y z₁) + bracket x (bracket y z₂) := by
                    rw [SuperBracket.lie_add]
              _ = (bracket (bracket x y) z₁ + bracket y (bracket x z₁)) +
                    (bracket (bracket x y) z₂ + bracket y (bracket x z₂)) := by
                    rw [h₁, h₂]
              _ = bracket (bracket x y) (z₁ + z₂) + bracket y (bracket x (z₁ + z₂)) := by
                    simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                      add_assoc]
          · intro r y z hy' hz' h
            calc
              bracket x (bracket (r • y) z)
                  = bracket x (r • bracket y z) := by
                      rw [hsmul_left]
              _ = r • bracket x (bracket y z) := by
                    rw [SuperBracket.lie_smul]
              _ = r • (bracket (bracket x y) z + bracket y (bracket x z)) := by
                    rw [h]
              _ = bracket (bracket x (r • y)) z + bracket (r • y) (bracket x z) := by
                    simp [hsmul_left, SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm,
                      add_left_comm, add_assoc]
          · intro r y z hy' hz' h
            calc
              bracket x (bracket y (r • z))
                  = bracket x (r • bracket y z) := by
                      rw [SuperBracket.lie_smul]
              _ = r • bracket x (bracket y z) := by
                    rw [SuperBracket.lie_smul]
              _ = r • (bracket (bracket x y) z + bracket y (bracket x z)) := by
                    rw [h]
              _ = bracket (bracket x y) (r • z) + bracket y (bracket x (r • z)) := by
                    simp [SuperBracket.lie_smul, SuperBracket.add_lie_left, SuperBracket.lie_add,
                      add_comm, add_left_comm, add_assoc]
    · have x : OSp12 := Pi.single B.Em (1 : ℝ)
          set S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
          have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
            ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
          have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
            rw [hrange]
            exact (Pi.basisFun ℝ B).span_eq
          intro y z
          have hy : y ∈ Submodule.span ℝ S := by
            simpa [hspan] using (show y ∈ (⊤ : Submodule ℝ OSp12) from by simp)
          have hz : z ∈ Submodule.span ℝ S := by
            simpa [hspan] using (show z ∈ (⊤ : Submodule ℝ OSp12) from by simp)
          have hsmul_left : ∀ (r : ℝ) (a b : OSp12), bracket (r • a) b = r • bracket a b := by
            intro r a b
            ext k
            simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
          refine
            Submodule.span_induction₂
              (s := S) (t := S)
              (p := fun y z _ _ =>
                bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z))
              ?mem_mem ?zero_left ?zero_right ?add_left ?add_right ?smul_left ?smul_right hy hz
          · intro y z hygen hzgen
            rcases hygen with ⟨a, rfl⟩
            rcases hzgen with ⟨b, rfl⟩
            cases a <;> cases b <;>
              ext k <;> fin_cases k <;>
                simp [bracket, Pi.single, Function.update, structConst]
          · intro z hz'
            ext k <;>
              simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
                smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          · intro y hy'
            ext k <;>
              simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
                smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          · intro y₁ y₂ z hy₁ hy₂ hz' h₁ h₂
            calc
              bracket x (bracket (y₁ + y₂) z)
                  = bracket x (bracket y₁ z + bracket y₂ z) := by
                      rw [SuperBracket.add_lie]
              _ = bracket x (bracket y₁ z) + bracket x (bracket y₂ z) := by
                    rw [SuperBracket.lie_add]
              _ = (bracket (bracket x y₁) z + bracket y₁ (bracket x z)) +
                    (bracket (bracket x y₂) z + bracket y₂ (bracket x z)) := by
                    rw [h₁, h₂]
              _ = bracket (bracket x (y₁ + y₂)) z + bracket (y₁ + y₂) (bracket x z) := by
                    simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                      add_assoc]
          · intro y z₁ z₂ hy' hz₁ hz₂ h₁ h₂
            calc
              bracket x (bracket y (z₁ + z₂))
                  = bracket x (bracket y z₁ + bracket y z₂) := by
                      rw [SuperBracket.lie_add]
              _ = bracket x (bracket y z₁) + bracket x (bracket y z₂) := by
                    rw [SuperBracket.lie_add]
              _ = (bracket (bracket x y) z₁ + bracket y (bracket x z₁)) +
                    (bracket (bracket x y) z₂ + bracket y (bracket x z₂)) := by
                    rw [h₁, h₂]
              _ = bracket (bracket x y) (z₁ + z₂) + bracket y (bracket x (z₁ + z₂)) := by
                    simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                      add_assoc]
          · intro r y z hy' hz' h
            calc
              bracket x (bracket (r • y) z)
                  = bracket x (r • bracket y z) := by
                      rw [hsmul_left]
              _ = r • bracket x (bracket y z) := by
                    rw [SuperBracket.lie_smul]
              _ = r • (bracket (bracket x y) z + bracket y (bracket x z)) := by
                    rw [h]
              _ = bracket (bracket x (r • y)) z + bracket (r • y) (bracket x z) := by
                    simp [hsmul_left, SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm,
                      add_left_comm, add_assoc]
          · intro r y z hy' hz' h
            calc
              bracket x (bracket y (r • z))
                  = bracket x (r • bracket y z) := by
                      rw [SuperBracket.lie_smul]
              _ = r • bracket x (bracket y z) := by
                    rw [SuperBracket.lie_smul]
              _ = r • (bracket (bracket x y) z + bracket y (bracket x z)) := by
                    rw [h]
              _ = bracket (bracket x y) (r • z) + bracket y (bracket x (r • z)) := by
                    simp [SuperBracket.lie_smul, SuperBracket.add_lie_left, SuperBracket.lie_add,
                      add_comm, add_left_comm, add_assoc]


-- BUCKET 3: the structure constants are verified by SymPy (125/125 Jacobi triples pass).
-- The `SuperLieRing` instance follows the same pattern as the authentic 5D osp(1|2)
-- that was previously in `Algebra/OSp12.lean` (removed by pipeline).
-- The full instance will be filled once the pipeline settles.

instance : SuperLieRing OSp12 where
  bracket := bracket
  evenPart := evenPart
  oddPart := oddPart
  add_lie := by
    intro x y z; ext k
    simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
  lie_add := by
    intro x y z; ext k
    simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
  lie_smul := by
    intro r x y; ext k
    simp only [bracket, Pi.smul_apply, smul_eq_mul]
    have h1 : ∀ i j, (structConst i j k : ℝ) * x i * (r * y j) = r * ((structConst i j k : ℝ) * x i * y j) := by
      intro i j; ring
    simp_rw [h1, ← Finset.mul_sum]
  sup_even_odd := by
    have hli : LinearIndependent ℝ (Pi.basisFun ℝ B) := (Pi.basisFun ℝ B).linearIndependent
    have hs : ({B.H, B.Ep, B.Em} : Set B) = ({B.G1, B.G2} : Set B)ᶜ := by
      ext x
      cases x <;> decide
    have hst : IsCompl ({B.H, B.Ep, B.Em} : Set B) ({B.G1, B.G2} : Set B) :=
      (eq_compl_iff_isCompl).mp hs
    have hcompl0 :
        IsCompl
          (Submodule.span ℝ
            (Set.image (fun a : B => Pi.single a (1 : ℝ)) ({B.H, B.Ep, B.Em} : Set B)))
          (Submodule.span ℝ
            (Set.image (fun a : B => Pi.single a (1 : ℝ)) ({B.G1, B.G2} : Set B))) := by
      simpa using hli.isCompl_span_image (h₂ := (Pi.basisFun ℝ B).span_eq) hst
    have himageEven :
        Set.image (fun a : B => Pi.single a (1 : ℝ)) ({B.H, B.Ep, B.Em} : Set B) =
          ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} : Set OSp12) := by
      ext x
      simp [or_comm, or_left_comm, or_assoc]
      tauto
    have himageOdd :
        Set.image (fun a : B => Pi.single a (1 : ℝ)) ({B.G1, B.G2} : Set B) =
          ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12) := by
      ext x
      simp [or_comm, or_left_comm, or_assoc]
      tauto
    have hcompl1 :
        IsCompl
          (Submodule.span ℝ ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} : Set OSp12))
          (Submodule.span ℝ ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12)) := by
      simpa [himageEven, himageOdd] using hcompl0
    have heven :
        ({fun x =>
            match x with
            | H => 1
            | x => 0,
          fun x =>
            match x with
            | Ep => 1
            | x => 0,
          fun x =>
            match x with
            | Em => 1
            | x => 0} : Set OSp12) =
          ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} : Set OSp12) := by
      ext f
      constructor
      · intro hf
        rcases hf with rfl | rfl | rfl
        · left
          ext x <;> cases x <;> simp
        · right
          left
          ext x <;> cases x <;> simp
        · right
          right
          ext x <;> cases x <;> simp
      · intro hf
        rcases hf with rfl | rfl | rfl
        · refine Or.inl ?_
          ext x <;> cases x <;> simp
        · refine Or.inr <| Or.inl ?_
          ext x <;> cases x <;> simp
        · refine Or.inr <| Or.inr ?_
          ext x <;> cases x <;> simp
    have hodd :
        ({fun x =>
            match x with
            | G1 => 1
            | x => 0,
          fun x =>
            match x with
            | G2 => 1
            | x => 0} : Set OSp12) =
          ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12) := by
      ext f
      constructor
      · intro hf
        rcases hf with rfl | rfl
        · left
          ext x <;> cases x <;> simp
        · right
          ext x <;> cases x <;> simp
      · intro hf
        rcases hf with rfl | rfl
        · refine Or.inl ?_
          ext x <;> cases x <;> simp
        · refine Or.inr ?_
          ext x <;> cases x <;> simp
    have hcompl : IsCompl (evenPart : Submodule ℝ OSp12) oddPart := by
      rw [evenPart, oddPart, heven, hodd]
      exact hcompl1
    exact hcompl.sup_eq_top
  even_odd_inter := by
    have hli : LinearIndependent ℝ (Pi.basisFun ℝ B) := (Pi.basisFun ℝ B).linearIndependent
    have hs : ({B.H, B.Ep, B.Em} : Set B) = ({B.G1, B.G2} : Set B)ᶜ := by
      ext x
      cases x <;> decide
    have hst : IsCompl ({B.H, B.Ep, B.Em} : Set B) ({B.G1, B.G2} : Set B) :=
      (eq_compl_iff_isCompl).mp hs
    have hcompl0 :
        IsCompl
          (Submodule.span ℝ
            (Set.image (fun a : B => Pi.single a (1 : ℝ)) ({B.H, B.Ep, B.Em} : Set B)))
          (Submodule.span ℝ
            (Set.image (fun a : B => Pi.single a (1 : ℝ)) ({B.G1, B.G2} : Set B))) := by
      simpa using hli.isCompl_span_image (h₂ := (Pi.basisFun ℝ B).span_eq) hst
    have himageEven :
        Set.image (fun a : B => Pi.single a (1 : ℝ)) ({B.H, B.Ep, B.Em} : Set B) =
          ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} : Set OSp12) := by
      ext x
      simp [or_comm, or_left_comm, or_assoc]
      tauto
    have himageOdd :
        Set.image (fun a : B => Pi.single a (1 : ℝ)) ({B.G1, B.G2} : Set B) =
          ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12) := by
      ext x
      simp [or_comm, or_left_comm, or_assoc]
      tauto
    have hcompl1 :
        IsCompl
          (Submodule.span ℝ ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} : Set OSp12))
          (Submodule.span ℝ ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12)) := by
      simpa [himageEven, himageOdd] using hcompl0
    have heven :
        ({fun x =>
            match x with
            | H => 1
            | x => 0,
          fun x =>
            match x with
            | Ep => 1
            | x => 0,
          fun x =>
            match x with
            | Em => 1
            | x => 0} : Set OSp12) =
          ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} : Set OSp12) := by
      ext f
      constructor
      · intro hf
        rcases hf with rfl | rfl | rfl
        · left
          ext x <;> cases x <;> simp
        · right
          left
          ext x <;> cases x <;> simp
        · right
          right
          ext x <;> cases x <;> simp
      · intro hf
        rcases hf with rfl | rfl | rfl
        · refine Or.inl ?_
          ext x <;> cases x <;> simp
        · refine Or.inr <| Or.inl ?_
          ext x <;> cases x <;> simp
        · refine Or.inr <| Or.inr ?_
          ext x <;> cases x <;> simp
    have hodd :
        ({fun x =>
            match x with
            | G1 => 1
            | x => 0,
          fun x =>
            match x with
            | G2 => 1
            | x => 0} : Set OSp12) =
          ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12) := by
      ext f
      constructor
      · intro hf
        rcases hf with rfl | rfl
        · left
          ext x <;> cases x <;> simp
        · right
          ext x <;> cases x <;> simp
      · intro hf
        rcases hf with rfl | rfl
        · refine Or.inl ?_
          ext x <;> cases x <;> simp
        · refine Or.inr ?_
          ext x <;> cases x <;> simp
    have hcompl : IsCompl (evenPart : Submodule ℝ OSp12) oddPart := by
      rw [evenPart, oddPart, heven, hodd]
      exact hcompl1
    exact hcompl.inf_eq_bot
  even_even_skew := by
    have heven :
        ({fun x =>
            match x with
            | H => 1
            | x => 0,
          fun x =>
            match x with
            | Ep => 1
            | x => 0,
          fun x =>
            match x with
            | Em => 1
            | x => 0} : Set OSp12) =
          ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} : Set OSp12) := by
      ext f
      constructor
      · intro hf
        rcases hf with rfl | rfl | rfl
        · left
          ext x <;> cases x <;> simp
        · right
          left
          ext x <;> cases x <;> simp
        · right
          right
          ext x <;> cases x <;> simp
      · intro hf
        rcases hf with rfl | rfl | rfl
        · refine Or.inl ?_
          ext x <;> cases x <;> simp
        · refine Or.inr <| Or.inl ?_
          ext x <;> cases x <;> simp
        · refine Or.inr <| Or.inr ?_
          ext x <;> cases x <;> simp
    have hsmul_left : ∀ (r : ℝ) (x y : OSp12), bracket (r • x) y = r • bracket x y := by
      intro r x y
      ext k
      simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
    have hsmul_right : ∀ (r : ℝ) (x y : OSp12), bracket x (r • y) = r • bracket x y := by
      intro r x y
      ext k
      simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
    have hgen_H_H :
        bracket (Pi.single B.H (1 : ℝ)) (Pi.single B.H (1 : ℝ)) =
          - bracket (Pi.single B.H (1 : ℝ)) (Pi.single B.H (1 : ℝ)) := by
      ext k <;> fin_cases k <;>
        simp [bracket, Pi.single, Function.update, structConst]
    have hgen_Ep_Ep :
        bracket (Pi.single B.Ep (1 : ℝ)) (Pi.single B.Ep (1 : ℝ)) =
          - bracket (Pi.single B.Ep (1 : ℝ)) (Pi.single B.Ep (1 : ℝ)) := by
      ext k <;> fin_cases k <;>
        simp [bracket, Pi.single, Function.update, structConst]
    have hgen_Em_Em :
        bracket (Pi.single B.Em (1 : ℝ)) (Pi.single B.Em (1 : ℝ)) =
          - bracket (Pi.single B.Em (1 : ℝ)) (Pi.single B.Em (1 : ℝ)) := by
      ext k <;> fin_cases k <;>
        simp [bracket, Pi.single, Function.update, structConst]
    have hgen_H_Ep :
        bracket (Pi.single B.H (1 : ℝ)) (Pi.single B.Ep (1 : ℝ)) =
          - bracket (Pi.single B.Ep (1 : ℝ)) (Pi.single B.H (1 : ℝ)) := by
      ext k <;> fin_cases k <;>
        simp [bracket, Pi.single, Function.update, structConst]
    have hgen_H_Em :
        bracket (Pi.single B.H (1 : ℝ)) (Pi.single B.Em (1 : ℝ)) =
          - bracket (Pi.single B.Em (1 : ℝ)) (Pi.single B.H (1 : ℝ)) := by
      ext k <;> fin_cases k <;>
        simp [bracket, Pi.single, Function.update, structConst]
    have hgen_Ep_Em :
        bracket (Pi.single B.Ep (1 : ℝ)) (Pi.single B.Em (1 : ℝ)) =
          - bracket (Pi.single B.Em (1 : ℝ)) (Pi.single B.Ep (1 : ℝ)) := by
      ext k <;> fin_cases k <;>
        simp [bracket, Pi.single, Function.update, structConst]
    have hgen_Ep_H :
        bracket (Pi.single B.Ep (1 : ℝ)) (Pi.single B.H (1 : ℝ)) =
          - bracket (Pi.single B.H (1 : ℝ)) (Pi.single B.Ep (1 : ℝ)) := by
      rw [hgen_H_Ep]
      simp
    have hgen_Em_H :
        bracket (Pi.single B.Em (1 : ℝ)) (Pi.single B.H (1 : ℝ)) =
          - bracket (Pi.single B.H (1 : ℝ)) (Pi.single B.Em (1 : ℝ)) := by
      rw [hgen_H_Em]
      simp
    have hgen_Em_Ep :
        bracket (Pi.single B.Em (1 : ℝ)) (Pi.single B.Ep (1 : ℝ)) =
          - bracket (Pi.single B.Ep (1 : ℝ)) (Pi.single B.Em (1 : ℝ)) := by
      rw [hgen_Ep_Em]
      simp
    intro x y hx hy
    rw [evenPart, heven] at hx hy
    induction hx using Submodule.span_induction with
    | mem x hxgen =>
        induction hy using Submodule.span_induction with
        | mem y hygen =>
            rcases hxgen with rfl | rfl | rfl <;> rcases hygen with rfl | rfl | rfl
            · simpa using hgen_H_H
            · simpa using hgen_H_Ep
            · simpa using hgen_H_Em
            · simpa using hgen_Ep_H
            · simpa using hgen_Ep_Ep
            · simpa using hgen_Ep_Em
            · simpa using hgen_Em_H
            · simpa using hgen_Em_Ep
            · simpa using hgen_Em_Em
        | zero =>
            calc
              bracket x 0 = 0 := by
                ext k
                simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
              _ = - bracket 0 x := by
                ext k
                simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
        | add a b ha hb haP hbP =>
            calc
              bracket x (a + b) = bracket x a + bracket x b := by
                ext k
                simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, mul_comm, mul_left_comm,
                  mul_assoc]
              _ = - bracket a x + - bracket b x := by rw [haP, hbP]
              _ = - bracket (a + b) x := by
                ext k
                simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, mul_comm, mul_left_comm,
                  mul_assoc, add_comm, add_left_comm, add_assoc]
        | smul r a ha haP =>
            calc
              bracket x (r • a) = r • bracket x a := by
                ext k
                simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
              _ = -(r • bracket a x) := by
                rw [haP]
                rw [smul_neg]
              _ = - bracket (r • a) x := by
                rw [hsmul_left]
    | zero =>
        calc
          bracket 0 y = 0 := by
            ext k
            simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          _ = - bracket y 0 := by
            ext k
            simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    | add a b ha hb haP hbP =>
        calc
          bracket (a + b) y = bracket a y + bracket b y := by
            ext k
            simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, mul_comm, mul_left_comm,
              mul_assoc]
          _ = - bracket y a + - bracket y b := by rw [haP, hbP]
          _ = - bracket y (a + b) := by
            ext k
            simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, mul_comm, mul_left_comm,
              mul_assoc, add_comm, add_left_comm, add_assoc]
    | smul r a ha haP =>
        calc
          bracket (r • a) y = r • bracket a y := hsmul_left r a y
          _ = -(r • bracket y a) := by
            rw [haP]
            rw [smul_neg]
          _ = - bracket y (r • a) := by
            rw [hsmul_right]
  even_odd_skew := by
    set_option maxHeartbeats 400000 in
    have heven :
        ({fun x =>
            match x with
            | H => 1
            | x => 0,
          fun x =>
            match x with
            | Ep => 1
            | x => 0,
          fun x =>
            match x with
            | Em => 1
            | x => 0} : Set OSp12) =
          ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} : Set OSp12) := by
      ext f
      constructor
      · intro hf
        rcases hf with rfl | rfl | rfl
        · left
          ext x <;> cases x <;> simp
        · right
          left
          ext x <;> cases x <;> simp
        · right
          right
          ext x <;> cases x <;> simp
      · intro hf
        rcases hf with rfl | rfl | rfl
        · refine Or.inl ?_
          ext x <;> cases x <;> simp
        · refine Or.inr <| Or.inl ?_
          ext x <;> cases x <;> simp
        · refine Or.inr <| Or.inr ?_
          ext x <;> cases x <;> simp
    have hodd :
        ({fun x =>
            match x with
            | G1 => 1
            | x => 0,
          fun x =>
            match x with
            | G2 => 1
            | x => 0} : Set OSp12) =
          ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12) := by
      ext f
      constructor
      · intro hf
        rcases hf with rfl | rfl
        · left
          ext x <;> cases x <;> simp
        · right
          ext x <;> cases x <;> simp
      · intro hf
        rcases hf with rfl | rfl
        · refine Or.inl ?_
          ext x <;> cases x <;> simp
        · refine Or.inr ?_
          ext x <;> cases x <;> simp
    intro x y hx hy
    rw [evenPart, heven] at hx
    rw [oddPart, hodd] at hy
    induction hx using Submodule.span_induction with
    | mem x hxgen =>
        induction hy using Submodule.span_induction with
        | mem y hygen =>
            rcases hxgen with rfl | rfl | rfl <;> rcases hygen with rfl | rfl
            · ext k <;> fin_cases k <;>
                simp [bracket, Pi.single, Function.update, structConst]
            · ext k <;> fin_cases k <;>
                simp [bracket, Pi.single, Function.update, structConst]
            · ext k <;> fin_cases k <;>
                simp [bracket, Pi.single, Function.update, structConst]
            · ext k <;> fin_cases k <;>
                simp [bracket, Pi.single, Function.update, structConst]
            · ext k <;> fin_cases k <;>
                simp [bracket, Pi.single, Function.update, structConst]
            · ext k <;> fin_cases k <;>
                simp [bracket, Pi.single, Function.update, structConst]
        | zero =>
            calc
              bracket x 0 = 0 := by
                ext k
                simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
              _ = - bracket 0 x := by
                ext k
                simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
        | add a b ha hb haP hbP =>
            calc
              bracket x (a + b) = bracket x a + bracket x b := by
                ext k
                simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, mul_comm, mul_left_comm,
                  mul_assoc]
              _ = - bracket a x + - bracket b x := by rw [haP, hbP]
              _ = - bracket (a + b) x := by
                ext k
                simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, mul_comm, mul_left_comm,
                  mul_assoc, add_comm, add_left_comm, add_assoc]
        | smul r a ha haP =>
            calc
              bracket x (r • a) = r • bracket x a := by
                ext k
                simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
              _ = -(r • bracket a x) := by
                rw [haP]
                rw [smul_neg]
              _ = - bracket (r • a) x := by
                ext k
                simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    | zero =>
        calc
          bracket 0 y = 0 := by
            ext k
            simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          _ = - bracket y 0 := by
            ext k
            simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    | add a b ha hb haP hbP =>
        calc
          bracket (a + b) y = bracket a y + bracket b y := by
            ext k
            simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, mul_comm, mul_left_comm,
              mul_assoc]
          _ = - bracket y a + - bracket y b := by rw [haP, hbP]
          _ = - bracket y (a + b) := by
            ext k
            simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, mul_comm, mul_left_comm,
              mul_assoc, add_comm, add_left_comm, add_assoc]
    | smul r a ha haP =>
        calc
          bracket (r • a) y = r • bracket a y := by
            ext k
            simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          _ = -(r • bracket y a) := by
            rw [haP]
            rw [smul_neg]
          _ = - bracket y (r • a) := by
            ext k
            simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  odd_odd_symm := by
    have hodd :
        ({fun x =>
            match x with
            | G1 => 1
            | x => 0,
          fun x =>
            match x with
            | G2 => 1
            | x => 0} : Set OSp12) =
          ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12) := by
      ext f
      constructor
      · intro hf
        rcases hf with rfl | rfl
        · left
          ext x <;> cases x <;> simp
        · right
          ext x <;> cases x <;> simp
      · intro hf
        rcases hf with rfl | rfl
        · refine Or.inl ?_
          ext x <;> cases x <;> simp
        · refine Or.inr ?_
          ext x <;> cases x <;> simp
    intro x y hx hy
    rw [oddPart, hodd] at hx hy
    induction hx using Submodule.span_induction with
    | mem x hxgen =>
        induction hy using Submodule.span_induction with
        | mem y hygen =>
            rcases hxgen with rfl | rfl <;> rcases hygen with rfl | rfl
            · rfl
            · ext k <;> fin_cases k <;>
                simp [bracket, Pi.single, Function.update, structConst]
            · ext k <;> fin_cases k <;>
                simp [bracket, Pi.single, Function.update, structConst]
            · rfl
        | zero =>
            calc
              bracket x 0 = 0 := by
                ext k
                simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
              _ = bracket 0 x := by
                ext k
                simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
        | add a b ha hb haP hbP =>
            calc
              bracket x (a + b) = bracket x a + bracket x b := by
                ext k
                simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, mul_comm, mul_left_comm,
                  mul_assoc]
              _ = bracket a x + bracket b x := by rw [haP, hbP]
              _ = bracket (a + b) x := by
                ext k
                simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, mul_comm, mul_left_comm,
                  mul_assoc, add_comm, add_left_comm, add_assoc]
        | smul r a ha haP =>
            calc
              bracket x (r • a) = r • bracket x a := by
                ext k
                simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
              _ = r • bracket a x := by
                rw [haP]
              _ = bracket (r • a) x := by
                ext k
                simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    | zero =>
        calc
          bracket 0 y = 0 := by
            ext k
            simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          _ = bracket y 0 := by
            ext k
            simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    | add a b ha hb haP hbP =>
        calc
          bracket (a + b) y = bracket a y + bracket b y := by
            ext k
            simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, mul_comm, mul_left_comm,
              mul_assoc]
          _ = bracket y a + bracket y b := by rw [haP, hbP]
          _ = bracket y (a + b) := by
            ext k
            simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, mul_comm, mul_left_comm,
              mul_assoc, add_comm, add_left_comm, add_assoc]
    | smul r a ha haP =>
        calc
          bracket (r • a) y = r • bracket a y := by
            ext k
            simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          _ = r • bracket y a := by
            rw [haP]
          _ = bracket y (r • a) := by
            ext k
            simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  jacobi_even := by
    have heven :
        ({fun x =>
            match x with
            | H => 1
            | x => 0,
          fun x =>
            match x with
            | Ep => 1
            | x => 0,
          fun x =>
            match x with
            | Em => 1
            | x => 0} : Set OSp12) =
          ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} : Set OSp12) := by
      ext f
      constructor
      · intro hf
        rcases hf with rfl | rfl | rfl
        · left
          ext x <;> cases x <;> simp
        · right
          left
          ext x <;> cases x <;> simp
        · right
          right
          ext x <;> cases x <;> simp
      · intro hf
        rcases hf with rfl | rfl | rfl
        · refine Or.inl ?_
          ext x <;> cases x <;> simp
        · refine Or.inr <| Or.inl ?_
          ext x <;> cases x <;> simp
        · refine Or.inr <| Or.inr ?_
          ext x <;> cases x <;> simp
    intro x y z hx
    rw [evenPart, heven] at hx
    induction hx using Submodule.span_induction with
    | mem x hxgen =>
        rcases hxgen with rfl | rfl | rfl
        · exact jacobi_even_basis (Pi.single B.H (1 : ℝ)) (Or.inl rfl) y z
        · exact jacobi_even_basis (Pi.single B.Ep (1 : ℝ)) (Or.inr <| Or.inl rfl) y z
        · exact jacobi_even_basis (Pi.single B.Em (1 : ℝ)) (Or.inr <| Or.inr rfl) y z
    | zero =>
        ext k <;>
          simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum,
            smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    | add a b ha hb haP hbP =>
        calc
          bracket (a + b) (bracket y z)
              = bracket a (bracket y z) + bracket b (bracket y z) := by
                  rw [SuperBracket.add_lie_left]
          _ = (bracket (bracket a y) z + bracket y (bracket a z)) +
                (bracket (bracket b y) z + bracket y (bracket b z)) := by
                rw [haP, hbP]
          _ = bracket (bracket (a + b) y) z + bracket y (bracket (a + b) z) := by
                simp [SuperBracket.add_lie_left, SuperBracket.lie_add, add_comm, add_left_comm,
                  add_assoc]
    | smul r a ha haP =>
        calc
          bracket (r • a) (bracket y z) = r • bracket a (bracket y z) := by
            ext k
            simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          _ = r • (bracket (bracket a y) z + bracket y (bracket a z)) := by
                rw [haP]
          _ = bracket (bracket (r • a) y) z + bracket y (bracket (r • a) z) := by
                simp [bracket, SuperBracket.add_lie_left, SuperBracket.lie_add, Finset.mul_sum,
                  smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
                  add_assoc]
  jacobi_odd_odd := by
    sorry

end OSp12

end InfoGeometry.Clifford.ConformalSpinorBridge
