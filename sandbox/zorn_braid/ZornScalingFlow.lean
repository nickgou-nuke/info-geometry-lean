import Mathlib
import SplitOctonionBraidSU3

/-!
# Modular/RG scaling flow on Zorn split-octonion matrices

For a Zorn element `X=(a,u,v,b)` and a diagonal boost
`D=diag(α,β)`, Zorn conjugation by `D` and `D⁻¹` gives

* `a ↦ a`, `b ↦ b`;
* `u ↦ (α/β) u`;
* `v ↦ (β/α) v`.

With `α=e^{kε}`, `β=e^{-kε}`, these are the expected weights
`u ↦ e^{+2kε}u` and `v ↦ e^{-2kε}v`.  Diagonal Zorn matrices are
strict fixed points, and pure upper/lower off-diagonal matrices are
nilpotents on the split-octonion null cone.
-/

noncomputable section

namespace ZornScalingFlow

abbrev Vec3 := Fin 3 → ℂ

/-- Canonical Zorn coordinates from the split-octonion kernel. -/
abbrev Zorn := SplitOctonionBraidSU3.Zorn

/-- Canonical coordinate operations reused by the scaling layer. -/
abbrev dot3 := SplitOctonionBraidSU3.dot3
abbrev cross3 := SplitOctonionBraidSU3.cross3
abbrev zornMul := SplitOctonionBraidSU3.zornMul
abbrev zornAdd := SplitOctonionBraidSU3.zornAdd
abbrev zornZero := SplitOctonionBraidSU3.zornZero
abbrev zornNorm := SplitOctonionBraidSU3.zornNorm

/-- Extensionality for Zorn coordinates. -/
theorem zorn_ext {X Y : Zorn}
    (ha : X.a = Y.a) (hu : X.u = Y.u) (hv : X.v = Y.v) (hb : X.b = Y.b) : X = Y := by
  exact SplitOctonionBraidSU3.zorn_ext ha hu hv hb

/-- Diagonal Zorn element. -/
def zornDiag (α β : ℂ) : Zorn where
  a := α; u := fun _ => 0; v := fun _ => 0; b := β

/-- Conjugation by a diagonal Zorn boost. -/
def diagConj (α β : ℂ) (X : Zorn) : Zorn :=
  zornMul (zornMul (zornDiag α β) X) (zornDiag α⁻¹ β⁻¹)

/-- The norm of a diagonal Zorn element is the product of its diagonal entries. -/
theorem zornNorm_zornDiag (α β : ℂ) :
    zornNorm (zornDiag α β) = α * β := by
  simp [SplitOctonionBraidSU3.zornNorm, zornDiag,
    SplitOctonionBraidSU3.dot3]

/-- Closed formula for diagonal Zorn conjugation. -/
theorem diagConj_formula {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) (X : Zorn) :
    diagConj α β X =
      { a := X.a,
        u := fun i => (α / β) * X.u i,
        v := fun i => (β / α) * X.v i,
        b := X.b } := by
  apply zorn_ext
  · simp [diagConj, zornDiag, SplitOctonionBraidSU3.zornMul,
      SplitOctonionBraidSU3.dot3]
    field_simp [hα]
  · funext i
    fin_cases i <;> simp [diagConj, zornDiag,
      SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.cross3] <;>
      field_simp [hβ]
  · funext i
    fin_cases i <;> simp [diagConj, zornDiag,
      SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.cross3] <;>
      field_simp [hα]
  · simp [diagConj, zornDiag, SplitOctonionBraidSU3.zornMul,
      SplitOctonionBraidSU3.dot3]
    field_simp [hβ]

/-- Pure diagonal elements are strict fixed points of diagonal conjugation. -/
theorem diagonal_fixed {α β a b : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) :
    diagConj α β (zornDiag a b) = zornDiag a b := by
  rw [diagConj_formula hα hβ]
  apply zorn_ext <;> simp [zornDiag]

/-- Diagonal Zorn conjugation preserves the composition norm. -/
theorem diagConj_norm {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) (X : Zorn) :
    zornNorm (diagConj α β X) = zornNorm X := by
  change SplitOctonionBraidSU3.zornNorm
      (SplitOctonionBraidSU3.zornMul
        (SplitOctonionBraidSU3.zornMul (zornDiag α β) X)
        (zornDiag α⁻¹ β⁻¹)) = SplitOctonionBraidSU3.zornNorm X
  rw [SplitOctonionBraidSU3.zornNorm_mul,
    SplitOctonionBraidSU3.zornNorm_mul]
  rw [show SplitOctonionBraidSU3.zornNorm (zornDiag α β) = α * β from
      zornNorm_zornDiag α β]
  rw [show SplitOctonionBraidSU3.zornNorm (zornDiag α⁻¹ β⁻¹) = α⁻¹ * β⁻¹ from
      zornNorm_zornDiag α⁻¹ β⁻¹]
  field_simp [hα, hβ]

/-- Successive diagonal flows multiply their two diagonal parameters. -/
theorem diagConj_comp {α β γ δ : ℂ}
    (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (X : Zorn) :
    diagConj α β (diagConj γ δ X) = diagConj (α * γ) (β * δ) X := by
  rw [diagConj_formula hα hβ, diagConj_formula hγ hδ,
    diagConj_formula (mul_ne_zero hα hγ) (mul_ne_zero hβ hδ)]
  apply zorn_ext
  · rfl
  · funext i
    field_simp [hβ, hδ]
  · funext i
    field_simp [hα, hγ]
  · rfl

/-- The determinant-one diagonal scaling flow `diag(p,p⁻¹)`. -/
def scalingFlow (p : ℂ) (X : Zorn) : Zorn :=
  diagConj p p⁻¹ X

/-- The scaling flow has weights `+2` on `u` and `-2` on `v`. -/
theorem scalingFlow_formula {p : ℂ} (hp : p ≠ 0) (X : Zorn) :
    scalingFlow p X =
      { a := X.a,
        u := fun i => p ^ 2 * X.u i,
        v := fun i => (p⁻¹) ^ 2 * X.v i,
        b := X.b } := by
  rw [scalingFlow, diagConj_formula hp (inv_ne_zero hp)]
  apply zorn_ext
  · rfl
  · funext i
    field_simp [hp]
  · funext i
    field_simp [hp]
  · rfl

/-- The determinant-one scaling flow preserves the composition norm. -/
theorem scalingFlow_norm {p : ℂ} (hp : p ≠ 0) (X : Zorn) :
    zornNorm (scalingFlow p X) = zornNorm X := by
  exact diagConj_norm hp (inv_ne_zero hp) X

/-- The nonzero complex parameters act multiplicatively by scaling flows. -/
theorem scalingFlow_comp {p q : ℂ} (hp : p ≠ 0) (hq : q ≠ 0) (X : Zorn) :
    scalingFlow p (scalingFlow q X) = scalingFlow (p * q) X := by
  rw [scalingFlow_formula hp, scalingFlow_formula hq,
    scalingFlow_formula (mul_ne_zero hp hq)]
  apply zorn_ext
  · rfl
  · funext i
    ring
  · funext i
    field_simp [hp, hq]
  · rfl

/-! ## Unit-parameter scaling action and its algebraic boundary -/

/--
The canonical unit-parameter scaling action.  It is a linear isometry of the
underlying split quadratic space; multiplication preservation is treated
separately below.
-/
def zornScale (p : ℂˣ) (X : Zorn) : Zorn where
  a := X.a
  u := fun i => (p : ℂ) ^ 2 * X.u i
  v := fun i => ((p : ℂ)⁻¹) ^ 2 * X.v i
  b := X.b

/-- The unit formulation agrees with diagonal Zorn conjugation. -/
theorem zornScale_eq_scalingFlow (p : ℂˣ) (X : Zorn) :
    zornScale p X = scalingFlow (p : ℂ) X := by
  rw [scalingFlow_formula p.ne_zero]
  rfl

/-- The identity unit acts trivially. -/
theorem zornScale_one (X : Zorn) : zornScale 1 X = X := by
  apply zorn_ext <;> simp [zornScale]

/-- Unit multiplication is composition of scaling transformations. -/
theorem zornScale_mul_parameter (p q : ℂˣ) (X : Zorn) :
    zornScale p (zornScale q X) = zornScale (p * q) X := by
  apply zorn_ext
  · rfl
  · funext i
    simp [zornScale]
    ring
  · funext i
    simp [zornScale]
    ring
  · rfl

/-- Scaling by the inverse unit undoes scaling. -/
theorem zornScale_inv (p : ℂˣ) (X : Zorn) :
    zornScale p⁻¹ (zornScale p X) = X := by
  rw [zornScale_mul_parameter]
  simp [zornScale_one]

/-- Scaling by negative p is equivalent to scaling by p. -/
theorem zornScale_neg (p : ℂˣ) :
    zornScale (-p) = zornScale p := by
  funext X
  apply zorn_ext
  · rfl
  · simp [zornScale]
  · simp [zornScale]
  · rfl

/-- Scaling operators are equal if their parameters' squares are equal. -/
theorem zornScale_eq_of_sq_eq (p q : ℂˣ) (h : (p : ℂ) ^ 2 = (q : ℂ) ^ 2) :
    zornScale p = zornScale q := by
  have hinv : ((p : ℂ)⁻¹) ^ 2 = ((q : ℂ)⁻¹) ^ 2 := by
    simpa [inv_pow] using congrArg Inv.inv h
  funext X
  apply zorn_ext
  · rfl
  · funext i
    change (p : ℂ) ^ 2 * X.u i = (q : ℂ) ^ 2 * X.u i
    rw [h]
  · funext i
    change ((p : ℂ)⁻¹) ^ 2 * X.v i = ((q : ℂ)⁻¹) ^ 2 * X.v i
    rw [hinv]
  · rfl

/-- The unit-parameter action preserves the Zorn composition norm. -/
theorem zornNorm_zornScale (p : ℂˣ) (X : Zorn) :
    zornNorm (zornScale p X) = zornNorm X := by
  rw [zornScale_eq_scalingFlow]
  exact scalingFlow_norm p.ne_zero X

/-- The scaling action is additive on the underlying Zorn vector space. -/
theorem zornScale_add (p : ℂˣ) (X Y : Zorn) :
    zornScale p (zornAdd X Y) = zornAdd (zornScale p X) (zornScale p Y) := by
  apply zorn_ext
  · simp [zornScale, SplitOctonionBraidSU3.zornAdd]
  · funext i
    simp [zornScale, SplitOctonionBraidSU3.zornAdd]
    ring
  · funext i
    simp [zornScale, SplitOctonionBraidSU3.zornAdd]
    ring
  · simp [zornScale, SplitOctonionBraidSU3.zornAdd]

/-- The scaling action commutes with complex scalar multiplication. -/
theorem zornScale_smul (p : ℂˣ) (c : ℂ) (X : Zorn) :
    zornScale p (SplitOctonionBraidSU3.zornSmul c X) =
      SplitOctonionBraidSU3.zornSmul c (zornScale p X) := by
  apply zorn_ext
  · simp [zornScale, SplitOctonionBraidSU3.zornSmul]
  · funext i
    simp [zornScale, SplitOctonionBraidSU3.zornSmul]
    ring
  · funext i
    simp [zornScale, SplitOctonionBraidSU3.zornSmul]
    ring
  · simp [zornScale, SplitOctonionBraidSU3.zornSmul]

/--
Uniform scaling preserves the full Zorn product exactly at the sixth roots of
unity.  For general parameters it remains a norm-preserving linear action, not
an algebra automorphism.
-/
theorem zornScale_mul_iff_pow_six_eq_one (p : ℂˣ) :
    (∀ X Y : Zorn,
      zornScale p (zornMul X Y) = zornMul (zornScale p X) (zornScale p Y)) ↔
      (p : ℂ) ^ 6 = 1 := by
  constructor
  · intro h
    have hc := congrArg (fun Z : Zorn => Z.u (2 : Fin 3))
      (h (SplitOctonionBraidSU3.F_k 0) (SplitOctonionBraidSU3.F_k 1))
    simp [zornScale, SplitOctonionBraidSU3.zornMul,
      SplitOctonionBraidSU3.F_k, SplitOctonionBraidSU3.e_k,
      SplitOctonionBraidSU3.cross3, SplitOctonionBraidSU3.dot3] at hc
    field_simp [p.ne_zero] at hc
    exact hc
  · intro hp X Y
    apply zorn_ext
    · simp [zornScale, SplitOctonionBraidSU3.zornMul,
        SplitOctonionBraidSU3.dot3]
      field_simp [p.ne_zero]
    · funext i
      fin_cases i <;>
        simp [zornScale, SplitOctonionBraidSU3.zornMul,
          SplitOctonionBraidSU3.cross3] <;>
        field_simp [p.ne_zero] <;>
        ring_nf at hp ⊢ <;>
        rw [hp] <;> ring
    · funext i
      fin_cases i <;>
        simp [zornScale, SplitOctonionBraidSU3.zornMul,
          SplitOctonionBraidSU3.cross3] <;>
        field_simp [p.ne_zero] <;>
        ring_nf at hp ⊢ <;>
        rw [hp] <;> ring
    · simp [zornScale, SplitOctonionBraidSU3.zornMul,
        SplitOctonionBraidSU3.dot3]
      field_simp [p.ne_zero]

/-- Multiplicativity at a sixth root, isolated from the exact characterization. -/
theorem zornScale_zornMul_of_pow_six_eq_one
    (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) (X Y : Zorn) :
    zornScale p (zornMul X Y) =
      zornMul (zornScale p X) (zornScale p Y) :=
  (zornScale_mul_iff_pow_six_eq_one p).2 hp X Y

/-- A globally multiplicative uniform scale necessarily has sixth-root parameter. -/
theorem pow_six_eq_one_of_zornScale_multiplicative
    (p : ℂˣ)
    (h : ∀ X Y : Zorn,
      zornScale p (zornMul X Y) =
        zornMul (zornScale p X) (zornScale p Y)) :
    (p : ℂ) ^ 6 = 1 :=
  (zornScale_mul_iff_pow_six_eq_one p).1 h

/-- On the automorphism locus, the effective multiplier `p²` is a cube root. -/
theorem automorphic_zornScale_effective_cube_root
    (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    ((p : ℂ) ^ 2) ^ 3 = 1 := by
  calc
    ((p : ℂ) ^ 2) ^ 3 = (p : ℂ) ^ 6 := by ring
    _ = 1 := hp

/-! ## Weights of the canonical nilpotent and Clifford generators -/

/-- The upper nilpotent generator has weight `+2`. -/
theorem zornScale_E_k (p : ℂˣ) (k : Fin 3) :
    zornScale p (SplitOctonionBraidSU3.E_k k) =
      SplitOctonionBraidSU3.zornSmul ((p : ℂ) ^ 2)
        (SplitOctonionBraidSU3.E_k k) := by
  apply zorn_ext
  · simp [zornScale, SplitOctonionBraidSU3.zornSmul,
      SplitOctonionBraidSU3.E_k]
  · funext i
    simp [zornScale, SplitOctonionBraidSU3.zornSmul,
      SplitOctonionBraidSU3.E_k]
  · funext i
    simp [zornScale, SplitOctonionBraidSU3.zornSmul,
      SplitOctonionBraidSU3.E_k]
  · simp [zornScale, SplitOctonionBraidSU3.zornSmul,
      SplitOctonionBraidSU3.E_k]

/-- The lower nilpotent generator has weight `-2`. -/
theorem zornScale_F_k (p : ℂˣ) (k : Fin 3) :
    zornScale p (SplitOctonionBraidSU3.F_k k) =
      SplitOctonionBraidSU3.zornSmul (((p : ℂ)⁻¹) ^ 2)
        (SplitOctonionBraidSU3.F_k k) := by
  apply zorn_ext
  · simp [zornScale, SplitOctonionBraidSU3.zornSmul,
      SplitOctonionBraidSU3.F_k]
  · funext i
    simp [zornScale, SplitOctonionBraidSU3.zornSmul,
      SplitOctonionBraidSU3.F_k]
  · funext i
    simp [zornScale, SplitOctonionBraidSU3.zornSmul,
      SplitOctonionBraidSU3.F_k]
  · simp [zornScale, SplitOctonionBraidSU3.zornSmul,
      SplitOctonionBraidSU3.F_k]

/-- The Clifford generator splits into its `+2` and `-2` weight components. -/
theorem zornScale_Q_k (p : ℂˣ) (k : Fin 3) :
    zornScale p (SplitOctonionBraidSU3.Q_k k) =
      SplitOctonionBraidSU3.zornAdd
        (SplitOctonionBraidSU3.zornSmul ((p : ℂ) ^ 2)
          (SplitOctonionBraidSU3.E_k k))
        (SplitOctonionBraidSU3.zornSmul (((p : ℂ)⁻¹) ^ 2)
          (SplitOctonionBraidSU3.F_k k)) := by
  apply zorn_ext
  · simp [zornScale, SplitOctonionBraidSU3.zornAdd,
      SplitOctonionBraidSU3.zornSmul, SplitOctonionBraidSU3.Q_k,
      SplitOctonionBraidSU3.E_k, SplitOctonionBraidSU3.F_k]
  · funext i
    simp [zornScale, SplitOctonionBraidSU3.zornAdd,
      SplitOctonionBraidSU3.zornSmul, SplitOctonionBraidSU3.Q_k,
      SplitOctonionBraidSU3.E_k, SplitOctonionBraidSU3.F_k]
  · funext i
    simp [zornScale, SplitOctonionBraidSU3.zornAdd,
      SplitOctonionBraidSU3.zornSmul, SplitOctonionBraidSU3.Q_k,
      SplitOctonionBraidSU3.E_k, SplitOctonionBraidSU3.F_k]
  · simp [zornScale, SplitOctonionBraidSU3.zornAdd,
      SplitOctonionBraidSU3.zornSmul, SplitOctonionBraidSU3.Q_k,
      SplitOctonionBraidSU3.E_k, SplitOctonionBraidSU3.F_k]

/-! ## Sector-exchange automorphism -/

/--
Exchange the diagonal and nilpotent sectors with the signs required by the
Zorn cross-product convention.
-/
def sectorExchange (X : Zorn) : Zorn where
  a := X.b
  u := fun i => -X.v i
  v := fun i => -X.u i
  b := X.a

/-- Sector exchange is involutive. -/
theorem sectorExchange_involutive (X : Zorn) :
    sectorExchange (sectorExchange X) = X := by
  apply zorn_ext
  · rfl
  · funext i
    simp [sectorExchange]
  · funext i
    simp [sectorExchange]
  · rfl

/-- Sector exchange preserves the split composition norm. -/
theorem sectorExchange_norm (X : Zorn) :
    zornNorm (sectorExchange X) = zornNorm X := by
  simp [sectorExchange, SplitOctonionBraidSU3.zornNorm,
    SplitOctonionBraidSU3.dot3]
  ring

/-- Sector exchange reverses the uniform scaling parameter. -/
theorem sectorExchange_zornScale (p : ℂˣ) (X : Zorn) :
    sectorExchange (zornScale p X) =
      zornScale p⁻¹ (sectorExchange X) := by
  apply zorn_ext
  · rfl
  · funext i
    simp [sectorExchange, zornScale]
  · funext i
    simp [sectorExchange, zornScale]
  · rfl

/-- With the canonical signs, sector exchange is a Zorn algebra automorphism. -/
theorem sectorExchange_zornMul (X Y : Zorn) :
    sectorExchange (zornMul X Y) =
      zornMul (sectorExchange X) (sectorExchange Y) := by
  apply zorn_ext
  · simp [sectorExchange, SplitOctonionBraidSU3.zornMul,
      SplitOctonionBraidSU3.dot3]
    ring
  · funext i
    fin_cases i <;>
      simp [sectorExchange, SplitOctonionBraidSU3.zornMul,
        SplitOctonionBraidSU3.cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [sectorExchange, SplitOctonionBraidSU3.zornMul,
        SplitOctonionBraidSU3.cross3] <;> ring
  · simp [sectorExchange, SplitOctonionBraidSU3.zornMul,
      SplitOctonionBraidSU3.dot3]
    ring

/-! ## The determinant-one diagonal torus -/

/-- The three determinant-one diagonal weights `p`, `q`, and `(pq)⁻¹`. -/
def torusWeight (p q : ℂˣ) (i : Fin 3) : ℂ :=
  if i = 0 then (p : ℂ)
  else if i = 1 then (q : ℂ)
  else ((p * q : ℂˣ) : ℂ)⁻¹

/--
The rank-two diagonal torus action: `uᵢ` has weight `torusWeight p q i`
and `vᵢ` has the inverse weight.
-/
def torusFlow (p q : ℂˣ) (X : Zorn) : Zorn where
  a := X.a
  u := fun i => torusWeight p q i * X.u i
  v := fun i => (torusWeight p q i)⁻¹ * X.v i
  b := X.b

/-- The identity pair acts trivially. -/
theorem torusFlow_one (X : Zorn) : torusFlow 1 1 X = X := by
  apply zorn_ext
  · rfl
  · funext i
    fin_cases i <;> simp [torusFlow, torusWeight]
  · funext i
    fin_cases i <;> simp [torusFlow, torusWeight]
  · rfl

/-- Torus parameters compose componentwise. -/
theorem torusFlow_comp (p₁ q₁ p₂ q₂ : ℂˣ) (X : Zorn) :
    torusFlow p₁ q₁ (torusFlow p₂ q₂ X) =
      torusFlow (p₁ * p₂) (q₁ * q₂) X := by
  apply zorn_ext
  · rfl
  · funext i
    fin_cases i <;> simp [torusFlow, torusWeight] <;> ring
  · funext i
    fin_cases i <;> simp [torusFlow, torusWeight] <;> ring
  · rfl

/-- The determinant-one torus preserves the Zorn composition norm. -/
theorem torusFlow_norm (p q : ℂˣ) (X : Zorn) :
    zornNorm (torusFlow p q X) = zornNorm X := by
  simp [torusFlow, torusWeight, SplitOctonionBraidSU3.zornNorm,
    SplitOctonionBraidSU3.dot3]
  field_simp [p.ne_zero, q.ne_zero]

/-- The determinant-one torus acts by automorphisms of Zorn multiplication. -/
theorem torusFlow_mul (p q : ℂˣ) (X Y : Zorn) :
    torusFlow p q (zornMul X Y) =
      zornMul (torusFlow p q X) (torusFlow p q Y) := by
  apply zorn_ext
  · simp [torusFlow, torusWeight, SplitOctonionBraidSU3.zornMul,
      SplitOctonionBraidSU3.dot3]
    field_simp [p.ne_zero, q.ne_zero]
  · funext i
    fin_cases i <;>
      simp [torusFlow, torusWeight, SplitOctonionBraidSU3.zornMul,
        SplitOctonionBraidSU3.cross3] <;>
      field_simp [p.ne_zero, q.ne_zero]
  · funext i
    fin_cases i <;>
      simp [torusFlow, torusWeight, SplitOctonionBraidSU3.zornMul,
        SplitOctonionBraidSU3.cross3] <;>
      field_simp [p.ne_zero, q.ne_zero]
  · simp [torusFlow, torusWeight, SplitOctonionBraidSU3.zornMul,
      SplitOctonionBraidSU3.dot3]
    field_simp [p.ne_zero, q.ne_zero]

/-- Sector exchange inverts both parameters of the determinant-one torus. -/
theorem sectorExchange_torusFlow (p q : ℂˣ) (X : Zorn) :
    sectorExchange (torusFlow p q X) =
      torusFlow p⁻¹ q⁻¹ (sectorExchange X) := by
  apply zorn_ext
  · rfl
  · funext i
    fin_cases i <;> simp [sectorExchange, torusFlow, torusWeight, mul_comm]
  · funext i
    fin_cases i <;> simp [sectorExchange, torusFlow, torusWeight, mul_comm]
  · rfl

/-- Upper pure off-diagonal Zorn element. -/
def upperNil (u : Vec3) : Zorn where
  a := 0; u := u; v := fun _ => 0; b := 0

/-- Lower pure off-diagonal Zorn element. -/
def lowerNil (v : Vec3) : Zorn where
  a := 0; u := fun _ => 0; v := v; b := 0

/-- Upper off-diagonal states are nilpotent. -/
theorem upperNil_sq_zero (u : Vec3) : zornMul (upperNil u) (upperNil u) = zornZero := by
  apply zorn_ext
  · simp [upperNil, SplitOctonionBraidSU3.zornMul,
      SplitOctonionBraidSU3.zornZero, SplitOctonionBraidSU3.dot3]
  · funext i; fin_cases i <;> simp [upperNil,
      SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornZero,
      SplitOctonionBraidSU3.cross3]
  · funext i; fin_cases i <;> simp [upperNil,
      SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornZero,
      SplitOctonionBraidSU3.cross3] <;> ring
  · simp [upperNil, SplitOctonionBraidSU3.zornMul,
      SplitOctonionBraidSU3.zornZero, SplitOctonionBraidSU3.dot3]

/-- Lower off-diagonal states are nilpotent. -/
theorem lowerNil_sq_zero (v : Vec3) : zornMul (lowerNil v) (lowerNil v) = zornZero := by
  apply zorn_ext
  · simp [lowerNil, SplitOctonionBraidSU3.zornMul,
      SplitOctonionBraidSU3.zornZero, SplitOctonionBraidSU3.dot3]
  · funext i; fin_cases i <;> simp [lowerNil,
      SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornZero,
      SplitOctonionBraidSU3.cross3] <;> ring
  · funext i; fin_cases i <;> simp [lowerNil,
      SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornZero,
      SplitOctonionBraidSU3.cross3]
  · simp [lowerNil, SplitOctonionBraidSU3.zornMul,
      SplitOctonionBraidSU3.zornZero, SplitOctonionBraidSU3.dot3]

end ZornScalingFlow
