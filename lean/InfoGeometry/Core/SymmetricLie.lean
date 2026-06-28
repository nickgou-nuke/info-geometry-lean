import InfoGeometry.Core.UnifiedGeometry
import InfoGeometry.Meta.Vacuity

/-!
# Symmetric Lie Algebra Core

Abstract Cartan decomposition machinery induced by an involutive Lie algebra automorphism.

This file provides:
- `SymmetricLieAlgebra`
- canonical plus/minus one eigenspaces (`even`/`odd`)
- symmetric pair bracket axioms
- Cartan projector decomposition and linear splitting
- Lie triple system structure on the odd part
-/

namespace InfoGeometry.Core

/-- A Lie algebra with a distinguished involutive Lie automorphism. -/
structure SymmetricLieAlgebra (L : Type _)
    [LieRing L] [LieAlgebra ℝ L] where
  θ : InvolutiveAutomorphism L
  [lin : PreservesLinear L θ]
  [lie : PreservesLieBracket L θ]

/-- A Cartan Lie algebra: symmetric Lie algebra with nondegenerate Killing form. -/
structure CartanLieAlgebra (L : Type _)
    [LieRing L] [LieAlgebra ℝ L]
    [Module.Free ℝ L] [Module.Finite ℝ L]
    extends SymmetricLieAlgebra L where
  killing_nondegenerate : (killingForm ℝ L).Nondegenerate

/-- Canonical Mathlib-native alias for Lie algebra automorphisms. -/
abbrev LieAut (L : Type _)
    [LieRing L] [LieAlgebra ℝ L] := L ≃ₗ⁅ℝ⁆ L

/-- Involutive Lie automorphisms as a subtype (`θ ∘ θ = id`). -/
abbrev InvolutiveLieAut (L : Type _)
    [LieRing L] [LieAlgebra ℝ L] :=
  { θ : LieAut L // Function.Involutive θ }

/-- Minimal Lie triple system structure over `ℝ`. -/
structure LieTripleSystem (P : Type _)
    [AddCommGroup P] [Module ℝ P] where
  triple : P → P → P → P
  skew₁ : ∀ x y z, triple x y z = -triple y x z
  jacobi_like :
    ∀ x y z u v,
      triple x y (triple z u v)
        = triple (triple x y z) u v
        + triple z (triple x y u) v
        + triple z u (triple x y v)

/-- Compact local symmetric-space package on an odd sector:
triple system + convexity + path connectedness. -/
structure OddLocalModel (L : Type _)
    [LieRing L] [LieAlgebra ℝ L]
    [TopologicalSpace L] [ContinuousAdd L] [ContinuousSMul ℝ L] where
  odd : Submodule ℝ L
  tripleSystem : LieTripleSystem odd
  convex : Convex ℝ (odd : Set L)
  pathConnected : IsPathConnected (odd : Set L)

attribute [infrastructure]
  LieTripleSystem.skew₁
  LieTripleSystem.jacobi_like
  CartanLieAlgebra.killing_nondegenerate

namespace SymmetricLieAlgebra

variable {L : Type _} [LieRing L] [LieAlgebra ℝ L]

instance instPreservesLinear (S : SymmetricLieAlgebra L) :
    PreservesLinear L S.θ := S.lin

instance instPreservesLieBracket (S : SymmetricLieAlgebra L) :
    PreservesLieBracket L S.θ := S.lie

instance instPreservesLie (S : SymmetricLieAlgebra L) :
    PreservesLie L S.θ where
  toPreservesLinear := S.lin
  toPreservesLieBracket := S.lie

/-- Involutivity of the distinguished symmetry map. -/
lemma involutive (S : SymmetricLieAlgebra L) :
    Function.Involutive S.θ :=
  S.θ.involutive

/-- Canonical Lie automorphism attached to the involution package. -/
noncomputable def toLieAut (S : SymmetricLieAlgebra L) :
    LieAut L where
  toFun := S.θ
  invFun := S.θ
  left_inv := S.involutive
  right_inv := S.involutive
  map_add' := by
    intro x y
    exact S.θ.map_add x y
  map_smul' := by
    intro a x
    exact S.θ.map_smul a x
  map_lie' := by
    intro x y
    exact S.θ.map_lie x y

/-- Build a symmetric Lie algebra from an involutive Lie automorphism. -/
def ofInvolutiveLieAut (θ : InvolutiveLieAut L) :
    SymmetricLieAlgebra L := by
  refine
    { θ := ⟨θ.1, θ.2⟩
      lin := ?_
      lie := ?_ }
  · refine
      { map_add := ?_
        map_smul := ?_ }
    · intro x y
      exact θ.1.toLinearEquiv.map_add x y
    · intro a x
      exact θ.1.toLinearEquiv.map_smul a x
  · exact
      { map_lie := by
          intro x y
          exact θ.1.map_lie x y }

/-- Forget a symmetric Lie algebra to its underlying involutive Lie automorphism. -/
noncomputable def toInvolutiveLieAut (S : SymmetricLieAlgebra L) :
    InvolutiveLieAut L :=
  ⟨S.toLieAut, S.involutive⟩

@[simp] lemma of_toInvolutiveLieAut (S : SymmetricLieAlgebra L) :
    ofInvolutiveLieAut (S.toInvolutiveLieAut) = S := by
  cases S
  rfl

@[simp] lemma to_ofInvolutiveLieAut (θ : InvolutiveLieAut L) :
    (ofInvolutiveLieAut θ).toInvolutiveLieAut = θ := by
  apply Subtype.ext
  ext x
  rfl

/-- Canonical equivalence: symmetric Lie algebra structures are involutive Lie automorphisms. -/
noncomputable def equivInvolutiveLieAut :
    SymmetricLieAlgebra L ≃ InvolutiveLieAut L where
  toFun := toInvolutiveLieAut
  invFun := ofInvolutiveLieAut
  left_inv := of_toInvolutiveLieAut
  right_inv := to_ofInvolutiveLieAut

/-- `+1` eigenspace of `θ`. -/
noncomputable def evenSubmodule (S : SymmetricLieAlgebra L) : Submodule ℝ L :=
  { carrier := {x | S.θ x = x}
    zero_mem' := by
      have h0 : S.θ (0 : L) = 0 := by
        simpa using (S.θ.map_smul (0 : ℝ) (0 : L))
      simpa using h0
    add_mem' := by
      intro x y hx hy
      have hx' : S.θ x = x := hx
      have hy' : S.θ y = y := hy
      calc
        S.θ (x + y) = S.θ x + S.θ y := by exact S.θ.map_add x y
        _ = x + y := by simp [hx', hy']
    smul_mem' := by
      intro a x hx
      have hx' : S.θ x = x := hx
      calc
        S.θ (a • x) = a • S.θ x := by exact S.θ.map_smul a x
        _ = a • x := by simp [hx'] }

/-- `-1` eigenspace of `θ`. -/
noncomputable def oddSubmodule (S : SymmetricLieAlgebra L) : Submodule ℝ L :=
  { carrier := {x | S.θ x = -x}
    zero_mem' := by
      have h0 : S.θ (0 : L) = 0 := by
        simpa using (S.θ.map_smul (0 : ℝ) (0 : L))
      simpa using h0
    add_mem' := by
      intro x y hx hy
      calc
        S.θ (x + y) = S.θ x + S.θ y := by exact S.θ.map_add x y
        _ = -x + -y := by rw [hx, hy]
        _ = -(x + y) := by abel_nf
    smul_mem' := by
      intro a x hx
      calc
        S.θ (a • x) = a • S.θ x := by exact S.θ.map_smul a x
        _ = a • (-x) := by rw [hx]
        _ = -(a • x) := by simp }

lemma mem_evenSubmodule_iff (S : SymmetricLieAlgebra L) {x : L} :
    x ∈ S.evenSubmodule ↔ S.θ x = x := by
  rfl

lemma mem_oddSubmodule_iff (S : SymmetricLieAlgebra L) {x : L} :
    x ∈ S.oddSubmodule ↔ S.θ x = -x := by
  rfl

/-- Grade intersection is zero: the even and odd submodules are disjoint except at 0. -/
theorem intersection_eq_zero (S : SymmetricLieAlgebra L) (x : L)
    (h_even : x ∈ S.evenSubmodule)
    (h_odd : x ∈ S.oddSubmodule) :
    x = 0 := by
  have h1 : S.θ x = x := (S.mem_evenSubmodule_iff).1 h_even
  have h2 : S.θ x = -x := (S.mem_oddSubmodule_iff).1 h_odd
  have h_eq : x = -x := by
    calc
      x = S.θ x := h1.symm
      _ = -x := h2
  have htwo : (2 : ℝ) • x = 0 := by
    calc
      (2 : ℝ) • x = x + x := by simp [two_smul]
      _ = x + -x := by exact congrArg (fun y : L => x + y) h_eq
      _ = 0 := by simp
  have hhalf :
      ((2 : ℝ)⁻¹) • ((2 : ℝ) • x) = ((2 : ℝ)⁻¹) • (0 : L) := by
    exact congrArg (fun y : L => ((2 : ℝ)⁻¹) • y) htwo
  simpa [smul_smul] using hhalf

/-- Compatibility alias for the `+1` Cartan projector linear map. -/
noncomputable def P_plus (S : SymmetricLieAlgebra L) : L →ₗ[ℝ] L :=
  { toFun := fun x => ((2 : ℝ)⁻¹) • (x + S.θ x)
    map_add' := by
      intro x y
      simp [smul_add, add_assoc, add_left_comm]
    map_smul' := by
      intro a x
      simp [smul_add, smul_smul, mul_comm] }

/-- Compatibility alias for the `-1` Cartan projector linear map. -/
noncomputable def P_minus (S : SymmetricLieAlgebra L) : L →ₗ[ℝ] L :=
  { toFun := fun x => ((2 : ℝ)⁻¹) • (x - S.θ x)
    map_add' := by
      intro x y
      simp [smul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    map_smul' := by
      intro a x
      simp [smul_sub, smul_smul, mul_comm] }

/-- Compatibility alias for the `+1` eigenspace (`𝔨` part). -/
noncomputable def 𝔨 (S : SymmetricLieAlgebra L) : Submodule ℝ L :=
  S.evenSubmodule

/-- Compatibility alias for the `-1` eigenspace (`𝔭` part). -/
noncomputable def 𝔭 (S : SymmetricLieAlgebra L) : Submodule ℝ L :=
  S.oddSubmodule

/-- The `+1` eigenspace as a Lie subalgebra. -/
noncomputable def evenLieSubalgebra (S : SymmetricLieAlgebra L) : LieSubalgebra ℝ L where
  carrier := S.evenSubmodule
  zero_mem' := by
    exact (S.evenSubmodule).zero_mem
  add_mem' := by
    intro x y hx hy
    exact (S.evenSubmodule).add_mem hx hy
  smul_mem' := by
    intro a x hx
    exact (S.evenSubmodule).smul_mem a hx
  lie_mem' := by
    intro x y hx hy
    have hx' : S.θ x = x := (S.mem_evenSubmodule_iff).1 hx
    have hy' : S.θ y = y := (S.mem_evenSubmodule_iff).1 hy
    have h : S.θ ⁅x, y⁆ = ⁅x, y⁆ := by
      simpa [hx', hy'] using S.θ.map_lie x y
    exact (S.mem_evenSubmodule_iff).2 h

lemma mem_even_iff (S : SymmetricLieAlgebra L) {x : L} :
    x ∈ S.evenLieSubalgebra ↔ S.θ x = x :=
  S.mem_evenSubmodule_iff

/-- The even part is convex as a submodule. -/
lemma even_convex (S : SymmetricLieAlgebra L) :
    Convex ℝ (S.evenLieSubalgebra : Set L) := by
  simpa using (Submodule.convex S.evenLieSubalgebra.toSubmodule)

/-- The odd part is convex as a submodule. -/
lemma odd_convex (S : SymmetricLieAlgebra L) :
    Convex ℝ (S.oddSubmodule : Set L) := by
  simpa using (Submodule.convex S.oddSubmodule)

lemma segment_subset_even (S : SymmetricLieAlgebra L) {x y : L}
    (hx : x ∈ S.evenLieSubalgebra) (hy : y ∈ S.evenLieSubalgebra) :
    segment ℝ x y ⊆ (S.evenLieSubalgebra : Set L) :=
  S.even_convex.segment_subset hx hy

lemma segment_subset_odd (S : SymmetricLieAlgebra L) {x y : L}
    (hx : x ∈ S.oddSubmodule) (hy : y ∈ S.oddSubmodule) :
    segment ℝ x y ⊆ (S.oddSubmodule : Set L) :=
  S.odd_convex.segment_subset hx hy

lemma add_smul_sub_mem_even (S : SymmetricLieAlgebra L) {x y : L}
    (hx : x ∈ S.evenLieSubalgebra) (hy : y ∈ S.evenLieSubalgebra)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ S.evenLieSubalgebra :=
  S.even_convex.add_smul_sub_mem hx hy ht

lemma add_smul_sub_mem_odd (S : SymmetricLieAlgebra L) {x y : L}
    (hx : x ∈ S.oddSubmodule) (hy : y ∈ S.oddSubmodule)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ S.oddSubmodule :=
  S.odd_convex.add_smul_sub_mem hx hy ht

/-- Abstract symmetric-pair bracket relations:
`[k,k] ⊆ k`, `[k,p] ⊆ p`, `[p,p] ⊆ k`. -/
theorem symmetric_pair_axioms (S : SymmetricLieAlgebra L) :
    (∀ {x y}, x ∈ S.evenLieSubalgebra →
      y ∈ S.evenLieSubalgebra →
      ⁅x, y⁆ ∈ S.evenLieSubalgebra)
    ∧
    (∀ {x y}, x ∈ S.evenLieSubalgebra →
      y ∈ S.oddSubmodule →
      ⁅x, y⁆ ∈ S.oddSubmodule)
    ∧
    (∀ {x y}, x ∈ S.oddSubmodule →
      y ∈ S.oddSubmodule →
      ⁅x, y⁆ ∈ S.evenLieSubalgebra) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy
    exact (S.evenLieSubalgebra).lie_mem hx hy
  · intro x y hx hy
    have hx' : S.θ x = x := (S.mem_even_iff).1 hx
    have hy' : S.θ y = -y := (S.mem_oddSubmodule_iff).1 hy
    have h : S.θ ⁅x, y⁆ = -⁅x, y⁆ := by
      calc
        S.θ ⁅x, y⁆ = ⁅S.θ x, S.θ y⁆ := S.θ.map_lie x y
        _ = ⁅x, -y⁆ := by simp [hx', hy']
        _ = -⁅x, y⁆ := by simp
    exact (S.mem_oddSubmodule_iff).2 h
  · intro x y hx hy
    have hx' : S.θ x = -x := (S.mem_oddSubmodule_iff).1 hx
    have hy' : S.θ y = -y := (S.mem_oddSubmodule_iff).1 hy
    have h : S.θ ⁅x, y⁆ = ⁅x, y⁆ := by
      calc
        S.θ ⁅x, y⁆ = ⁅S.θ x, S.θ y⁆ := S.θ.map_lie x y
        _ = ⁅-x, -y⁆ := by simp [hx', hy']
        _ = ⁅x, y⁆ := by simp
    exact (S.mem_even_iff).2 h

/-- Cartan decomposition (`x = x₊ + x₋`) in compatibility naming. -/
theorem cartan_decomposition (S : SymmetricLieAlgebra L) (x : L) :
    x = S.P_plus x + S.P_minus x := by
  have hsplit :
      S.P_plus x + S.P_minus x = ((2 : ℝ)⁻¹) • x + ((2 : ℝ)⁻¹) • x := by
    simp [P_plus, P_minus, smul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hhalf : (((2 : ℝ)⁻¹) + ((2 : ℝ)⁻¹)) = (1 : ℝ) := by norm_num
  calc
    x = (1 : ℝ) • x := by simp
    _ = ((((2 : ℝ)⁻¹) + ((2 : ℝ)⁻¹)) : ℝ) • x := by simp [hhalf]
    _ = ((2 : ℝ)⁻¹) • x + ((2 : ℝ)⁻¹) • x := by simp [add_smul]
    _ = S.P_plus x + S.P_minus x := hsplit.symm

/-- Bracket parity `[𝔨, 𝔨] ⊆ 𝔨` in compatibility naming. -/
theorem bracket_k_k
    (S : SymmetricLieAlgebra L)
    {x y : L}
    (hx : x ∈ S.𝔨)
    (hy : y ∈ S.𝔨) :
    ⁅x, y⁆ ∈ S.𝔨 := by
  have hx' : S.θ x = x := (S.mem_evenSubmodule_iff).1 hx
  have hy' : S.θ y = y := (S.mem_evenSubmodule_iff).1 hy
  have h : S.θ ⁅x, y⁆ = ⁅x, y⁆ := by
    simpa [hx', hy'] using S.θ.map_lie x y
  exact (S.mem_evenSubmodule_iff).2 h

/-- Bracket parity `[𝔨, 𝔭] ⊆ 𝔭` in compatibility naming. -/
theorem bracket_k_p
    (S : SymmetricLieAlgebra L)
    {x y : L}
    (hx : x ∈ S.𝔨)
    (hy : y ∈ S.𝔭) :
    ⁅x, y⁆ ∈ S.𝔭 := by
  have hx' : S.θ x = x := (S.mem_evenSubmodule_iff).1 hx
  have hy' : S.θ y = -y := (S.mem_oddSubmodule_iff).1 hy
  have h : S.θ ⁅x, y⁆ = -⁅x, y⁆ := by
    calc
      S.θ ⁅x, y⁆ = ⁅S.θ x, S.θ y⁆ := S.θ.map_lie x y
      _ = ⁅x, -y⁆ := by simp [hx', hy']
      _ = -⁅x, y⁆ := by simp
  exact (S.mem_oddSubmodule_iff).2 h

/-- Bracket parity `[𝔭, 𝔭] ⊆ 𝔨` in compatibility naming. -/
theorem bracket_p_p
    (S : SymmetricLieAlgebra L)
    {x y : L}
    (hx : x ∈ S.𝔭)
    (hy : y ∈ S.𝔭) :
    ⁅x, y⁆ ∈ S.𝔨 := by
  have hx' : S.θ x = -x := (S.mem_oddSubmodule_iff).1 hx
  have hy' : S.θ y = -y := (S.mem_oddSubmodule_iff).1 hy
  have h : S.θ ⁅x, y⁆ = ⁅x, y⁆ := by
    calc
      S.θ ⁅x, y⁆ = ⁅S.θ x, S.θ y⁆ := S.θ.map_lie x y
      _ = ⁅-x, -y⁆ := by simp [hx', hy']
      _ = ⁅x, y⁆ := by simp
  exact (S.mem_evenSubmodule_iff).2 h

/-- `+` Cartan projector `(Id + θ)/2`. -/
noncomputable def plusPart (S : SymmetricLieAlgebra L) (x : L) : L :=
  Projector.plus S.θ x

/-- `-` Cartan projector `(Id - θ)/2`. -/
noncomputable def minusPart (S : SymmetricLieAlgebra L) (x : L) : L :=
  Projector.minus S.θ x

/-- Compatibility bridge: `P_plus` is exactly `plusPart`. -/
@[simp] lemma P_plus_eq_plusPart (S : SymmetricLieAlgebra L) (x : L) :
    S.P_plus x = S.plusPart x := by
  simp [P_plus, plusPart, Projector.plus]

/-- Compatibility bridge: `P_minus` is exactly `minusPart`. -/
@[simp] lemma P_minus_eq_minusPart (S : SymmetricLieAlgebra L) (x : L) :
    S.P_minus x = S.minusPart x := by
  simp [P_minus, minusPart, Projector.minus]

lemma plusPart_add (S : SymmetricLieAlgebra L) (x y : L) :
    S.plusPart (x + y) = S.plusPart x + S.plusPart y := by
  simp [plusPart, Projector.plus, smul_add, add_assoc, add_left_comm]

lemma minusPart_add (S : SymmetricLieAlgebra L) (x y : L) :
    S.minusPart (x + y) = S.minusPart x + S.minusPart y := by
  simp [minusPart, Projector.minus, smul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma plusPart_smul (S : SymmetricLieAlgebra L) (a : ℝ) (x : L) :
    S.plusPart (a • x) = a • S.plusPart x := by
  simp [plusPart, Projector.plus, smul_add, smul_smul, mul_comm]

lemma minusPart_smul (S : SymmetricLieAlgebra L) (a : ℝ) (x : L) :
    S.minusPart (a • x) = a • S.minusPart x := by
  simp [minusPart, Projector.minus, smul_sub, smul_smul, mul_comm]

/-- `plusPart` as a linear map. -/
noncomputable def plusPartLinear (S : SymmetricLieAlgebra L) : L →ₗ[ℝ] L where
  toFun := S.plusPart
  map_add' := S.plusPart_add
  map_smul' := S.plusPart_smul

/-- `minusPart` as a linear map. -/
noncomputable def minusPartLinear (S : SymmetricLieAlgebra L) : L →ₗ[ℝ] L where
  toFun := S.minusPart
  map_add' := S.minusPart_add
  map_smul' := S.minusPart_smul

lemma convex_plusPart_image (S : SymmetricLieAlgebra L) {s : Set L}
    (hs : Convex ℝ s) :
    Convex ℝ (S.plusPart '' s) := by
  simpa [plusPartLinear] using hs.linear_image (S.plusPartLinear)

lemma convex_minusPart_image (S : SymmetricLieAlgebra L) {s : Set L}
    (hs : Convex ℝ s) :
    Convex ℝ (S.minusPart '' s) := by
  simpa [minusPartLinear] using hs.linear_image (S.minusPartLinear)

lemma convex_plusPart_preimage (S : SymmetricLieAlgebra L) {s : Set L}
    (hs : Convex ℝ s) :
    Convex ℝ (S.plusPart ⁻¹' s) := by
  simpa [plusPartLinear] using hs.linear_preimage (S.plusPartLinear)

lemma convex_minusPart_preimage (S : SymmetricLieAlgebra L) {s : Set L}
    (hs : Convex ℝ s) :
    Convex ℝ (S.minusPart ⁻¹' s) := by
  simpa [minusPartLinear] using hs.linear_preimage (S.minusPartLinear)

lemma decomposition (S : SymmetricLieAlgebra L) (x : L) :
    x = S.plusPart x + S.minusPart x := by
  simpa [plusPart, minusPart] using (Projector.decomposition (θ := S.θ) x)

lemma plusPart_mem_even (S : SymmetricLieAlgebra L) (x : L) :
    S.plusPart x ∈ S.evenLieSubalgebra := by
  have hθ : S.θ (S.plusPart x) = S.plusPart x := by
    simpa [plusPart] using (Projector.plus_fixed (θ := S.θ) x)
  exact (S.mem_even_iff).2 hθ

lemma minusPart_mem_odd (S : SymmetricLieAlgebra L) (x : L) :
    S.minusPart x ∈ S.oddSubmodule := by
  have hθ : S.θ (S.minusPart x) = -S.minusPart x := by
    simpa [minusPart] using (Projector.minus_neg_fixed (θ := S.θ) x)
  exact (S.mem_oddSubmodule_iff).2 hθ

lemma plusPart_of_mem_even (S : SymmetricLieAlgebra L) {x : L}
    (hx : x ∈ S.evenLieSubalgebra) : S.plusPart x = x := by
  have hx' : S.θ x = x := (S.mem_even_iff).1 hx
  have hhalf : ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = 1 := by norm_num
  calc
    S.plusPart x = ((2 : ℝ)⁻¹) • (x + x) := by
      simp [plusPart, Projector.plus, hx']
    _ = (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • x := by
          simp [add_smul]
    _ = (1 : ℝ) • x := by simp [hhalf]
    _ = x := by simp

lemma minusPart_of_mem_even (S : SymmetricLieAlgebra L) {x : L}
    (hx : x ∈ S.evenLieSubalgebra) : S.minusPart x = 0 := by
  have hx' : S.θ x = x := (S.mem_even_iff).1 hx
  simp [minusPart, Projector.minus, hx']

lemma plusPart_of_mem_odd (S : SymmetricLieAlgebra L) {x : L}
    (hx : x ∈ S.oddSubmodule) : S.plusPart x = 0 := by
  have hx' : S.θ x = -x := (S.mem_oddSubmodule_iff).1 hx
  simp [plusPart, Projector.plus, hx']

lemma minusPart_of_mem_odd (S : SymmetricLieAlgebra L) {x : L}
    (hx : x ∈ S.oddSubmodule) : S.minusPart x = x := by
  have hx' : S.θ x = -x := (S.mem_oddSubmodule_iff).1 hx
  have hhalf : ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = 1 := by norm_num
  calc
    S.minusPart x = ((2 : ℝ)⁻¹) • (x - (-x)) := by
      simp [minusPart, Projector.minus, hx']
    _ = ((2 : ℝ)⁻¹) • (x + x) := by simp
    _ = (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • x := by
          simp [add_smul]
    _ = (1 : ℝ) • x := by simp [hhalf]
    _ = x := by simp

/-- Canonical linear decomposition map `x ↦ (x₊, x₋)`. -/
noncomputable def cartanDecomposeLinear (S : SymmetricLieAlgebra L) :
    L →ₗ[ℝ] S.evenLieSubalgebra × S.oddSubmodule :=
{ toFun := fun x =>
    (⟨S.plusPart x, S.plusPart_mem_even x⟩,
      ⟨S.minusPart x, S.minusPart_mem_odd x⟩)
  map_add' := by
    intro x y
    ext <;> simp [plusPart_add, minusPart_add]
  map_smul' := by
    intro a x
    ext <;> simp [plusPart_smul, minusPart_smul] }

/-- Reassembly map `(k, p) ↦ k + p`. -/
noncomputable def cartanAssembleLinear (S : SymmetricLieAlgebra L) :
    S.evenLieSubalgebra × S.oddSubmodule →ₗ[ℝ] L :=
{ toFun := fun x => x.1 + x.2
  map_add' := by
    intro x y
    simp [add_left_comm, add_comm]
  map_smul' := by
    intro a x
    simp [smul_add] }

lemma cartan_left_inverse (S : SymmetricLieAlgebra L) :
    Function.LeftInverse (S.cartanAssembleLinear) (S.cartanDecomposeLinear) := by
  intro x
  simpa [cartanAssembleLinear, cartanDecomposeLinear] using (S.decomposition x).symm

lemma cartan_right_inverse (S : SymmetricLieAlgebra L) :
    Function.RightInverse (S.cartanAssembleLinear) (S.cartanDecomposeLinear) := by
  intro x
  ext
  · change S.plusPart ((x.1 : L) + (x.2 : L)) = x.1
    rw [S.plusPart_add]
    simp [S.plusPart_of_mem_even x.1.property, S.plusPart_of_mem_odd x.2.property]
  · change S.minusPart ((x.1 : L) + (x.2 : L)) = x.2
    rw [S.minusPart_add]
    simp [S.minusPart_of_mem_even x.1.property, S.minusPart_of_mem_odd x.2.property]

/-- Explicit linear equivalence `L ≃ k × p`. -/
noncomputable def cartanLinearEquiv (S : SymmetricLieAlgebra L) :
    L ≃ₗ[ℝ] S.evenLieSubalgebra × S.oddSubmodule :=
{ toLinearMap := S.cartanDecomposeLinear
  invFun := S.cartanAssembleLinear
  left_inv := S.cartan_left_inverse
  right_inv := S.cartan_right_inverse }

/-- The Cartan decomposition as an actual linear equivalence, not an existence wrapper. -/
noncomputable def cartan_direct_sum (S : SymmetricLieAlgebra L) :
    L ≃ₗ[ℝ] S.evenLieSubalgebra × S.oddSubmodule :=
  S.cartanLinearEquiv

theorem cartan_direct_sum_eq_cartanLinearEquiv (S : SymmetricLieAlgebra L) :
    S.cartan_direct_sum = S.cartanLinearEquiv :=
  rfl

section Topology

variable [TopologicalSpace L] [ContinuousAdd L] [ContinuousSMul ℝ L]

lemma odd_isConnected (S : SymmetricLieAlgebra L) :
    IsConnected (S.oddSubmodule : Set L) := by
  exact (S.odd_convex.isConnected ⟨0, S.oddSubmodule.zero_mem⟩)

lemma odd_isPathConnected (S : SymmetricLieAlgebra L) :
    IsPathConnected (S.oddSubmodule : Set L) := by
  exact (S.odd_convex.isPathConnected ⟨0, S.oddSubmodule.zero_mem⟩)

lemma even_isConnected (S : SymmetricLieAlgebra L) :
    IsConnected (S.evenLieSubalgebra : Set L) := by
  exact (S.even_convex.isConnected ⟨0, S.evenLieSubalgebra.zero_mem⟩)

lemma even_isPathConnected (S : SymmetricLieAlgebra L) :
    IsPathConnected (S.evenLieSubalgebra : Set L) := by
  exact (S.even_convex.isPathConnected ⟨0, S.evenLieSubalgebra.zero_mem⟩)

end Topology

/-- Triple bracket `[[x,y],z]`. -/
def triple (S : SymmetricLieAlgebra L) (x y z : L) : L :=
  let _ := S
  ⁅⁅x, y⁆, z⁆

/-- The odd submodule is closed under the triple bracket. -/
lemma triple_closed (S : SymmetricLieAlgebra L)
    {x y z : L}
    (hx : x ∈ S.oddSubmodule)
    (hy : y ∈ S.oddSubmodule)
    (hz : z ∈ S.oddSubmodule) :
    S.triple x y z ∈ S.oddSubmodule := by
  have h1 : ⁅x, y⁆ ∈ S.evenLieSubalgebra := (S.symmetric_pair_axioms.2.2) hx hy
  exact (S.symmetric_pair_axioms.2.1) h1 hz

/-- Fundamental identity for the induced triple product. -/
lemma triple_jacobi (S : SymmetricLieAlgebra L) (x y z u v : L) :
    S.triple x y (S.triple z u v)
      = S.triple (S.triple x y z) u v
      + S.triple z (S.triple x y u) v
      + S.triple z u (S.triple x y v) := by
  have h₁ :
      ⁅⁅x, y⁆, ⁅⁅z, u⁆, v⁆⁆
        = ⁅⁅⁅x, y⁆, ⁅z, u⁆⁆, v⁆ + ⁅⁅z, u⁆, ⁅⁅x, y⁆, v⁆⁆ := by
    have hLie :
        ⁅⁅⁅x, y⁆, ⁅z, u⁆⁆, v⁆
          = ⁅⁅x, y⁆, ⁅⁅z, u⁆, v⁆⁆ - ⁅⁅z, u⁆, ⁅⁅x, y⁆, v⁆⁆ :=
      lie_lie ⁅x, y⁆ ⁅z, u⁆ v
    calc
      ⁅⁅x, y⁆, ⁅⁅z, u⁆, v⁆⁆
          = (⁅⁅x, y⁆, ⁅⁅z, u⁆, v⁆⁆ - ⁅⁅z, u⁆, ⁅⁅x, y⁆, v⁆⁆)
            + ⁅⁅z, u⁆, ⁅⁅x, y⁆, v⁆⁆ := by abel_nf
      _ = ⁅⁅⁅x, y⁆, ⁅z, u⁆⁆, v⁆ + ⁅⁅z, u⁆, ⁅⁅x, y⁆, v⁆⁆ := by
            rw [← hLie]
  have h₂ :
      ⁅⁅x, y⁆, ⁅z, u⁆⁆
        = ⁅⁅⁅x, y⁆, z⁆, u⁆ + ⁅z, ⁅⁅x, y⁆, u⁆⁆ := by
    have hLie :
        ⁅⁅⁅x, y⁆, z⁆, u⁆ = ⁅⁅x, y⁆, ⁅z, u⁆⁆ - ⁅z, ⁅⁅x, y⁆, u⁆⁆ :=
      lie_lie ⁅x, y⁆ z u
    calc
      ⁅⁅x, y⁆, ⁅z, u⁆⁆
          = (⁅⁅x, y⁆, ⁅z, u⁆⁆ - ⁅z, ⁅⁅x, y⁆, u⁆⁆) + ⁅z, ⁅⁅x, y⁆, u⁆⁆ := by
              abel_nf
      _ = ⁅⁅⁅x, y⁆, z⁆, u⁆ + ⁅z, ⁅⁅x, y⁆, u⁆⁆ := by
            rw [← hLie]
  calc
    S.triple x y (S.triple z u v)
        = ⁅⁅x, y⁆, ⁅⁅z, u⁆, v⁆⁆ := by rfl
    _ = ⁅⁅⁅x, y⁆, ⁅z, u⁆⁆, v⁆ + ⁅⁅z, u⁆, ⁅⁅x, y⁆, v⁆⁆ := h₁
    _ = ⁅⁅⁅⁅x, y⁆, z⁆, u⁆ + ⁅z, ⁅⁅x, y⁆, u⁆⁆, v⁆
        + ⁅⁅z, u⁆, ⁅⁅x, y⁆, v⁆⁆ := by rw [h₂]
    _ = (⁅⁅⁅⁅x, y⁆, z⁆, u⁆, v⁆ + ⁅⁅z, ⁅⁅x, y⁆, u⁆⁆, v⁆)
        + ⁅⁅z, u⁆, ⁅⁅x, y⁆, v⁆⁆ := by rw [add_lie]
    _ = ⁅⁅⁅⁅x, y⁆, z⁆, u⁆, v⁆
        + ⁅⁅z, ⁅⁅x, y⁆, u⁆⁆, v⁆
        + ⁅⁅z, u⁆, ⁅⁅x, y⁆, v⁆⁆ := by
          abel_nf
    _ = S.triple (S.triple x y z) u v
        + S.triple z (S.triple x y u) v
        + S.triple z u (S.triple x y v) := by
          rfl

/-- Triple operation restricted to the odd eigenspace. -/
noncomputable def oddTriple (S : SymmetricLieAlgebra L)
    (x y z : S.oddSubmodule) : S.oddSubmodule :=
  ⟨S.triple x y z, S.triple_closed x.property y.property z.property⟩

/-- Triple operation on `𝔭` in compatibility naming. -/
noncomputable abbrev tripleOnP (S : SymmetricLieAlgebra L)
    (x y z : S.𝔭) : S.𝔭 :=
  S.oddTriple x y z

/-- Curvature sign convention on the odd/triple system sector. -/
noncomputable def curvature
    (S : SymmetricLieAlgebra L)
    (x y z : S.𝔭) : S.𝔭 :=
  -S.tripleOnP x y z

lemma oddTriple_skew₁ (S : SymmetricLieAlgebra L)
    (x y z : S.oddSubmodule) :
    S.oddTriple x y z = -S.oddTriple y x z := by
  ext
  simp [oddTriple, triple]

lemma oddTriple_jacobi (S : SymmetricLieAlgebra L)
    (x y z u v : S.oddSubmodule) :
    S.oddTriple x y (S.oddTriple z u v)
      = S.oddTriple (S.oddTriple x y z) u v
      + S.oddTriple z (S.oddTriple x y u) v
      + S.oddTriple z u (S.oddTriple x y v) := by
  ext
  exact S.triple_jacobi (x := x) (y := y) (z := z) (u := u) (v := v)

/-- The odd part of a symmetric Lie algebra is a Lie triple system. -/
noncomputable def oddLieTripleSystem (S : SymmetricLieAlgebra L) :
    LieTripleSystem S.oddSubmodule where
  triple := S.oddTriple
  skew₁ := S.oddTriple_skew₁
  jacobi_like := S.oddTriple_jacobi

section TopologicalModel

variable [TopologicalSpace L] [ContinuousAdd L] [ContinuousSMul ℝ L]

/-- Canonical local symmetric-space wrapper for the odd sector. -/
noncomputable def oddLocalModel (S : SymmetricLieAlgebra L) : OddLocalModel L where
  odd := S.oddSubmodule
  tripleSystem := S.oddLieTripleSystem
  convex := S.odd_convex
  pathConnected := S.odd_isPathConnected

@[simp] lemma oddLocalModel_odd (S : SymmetricLieAlgebra L) :
    (S.oddLocalModel).odd = S.oddSubmodule := rfl

@[simp] lemma oddLocalModel_tripleSystem (S : SymmetricLieAlgebra L) :
    (S.oddLocalModel).tripleSystem = S.oddLieTripleSystem := rfl

lemma oddLocalModel_convex (S : SymmetricLieAlgebra L) :
    (S.oddLocalModel).convex = S.odd_convex := rfl

lemma oddLocalModel_pathConnected (S : SymmetricLieAlgebra L) :
    (S.oddLocalModel).pathConnected = S.odd_isPathConnected := rfl

end TopologicalModel

section KillingForm

/-- Invariance of the Killing form under the symmetric involution. -/
lemma killing_invariant (S : SymmetricLieAlgebra L) (x y : L) :
    killingForm ℝ L (S.θ x) (S.θ y)
      = killingForm ℝ L x y := by
  exact LieAlgebra.killingForm_of_equiv_apply
    (R := ℝ) (L := L) (L' := L) S.toLieAut x y

/-- Orthogonality of the Cartan decomposition pieces for the Killing form. -/
lemma killing_orthogonal
    (S : SymmetricLieAlgebra L)
    {k p : L}
    (hk : k ∈ S.evenLieSubalgebra)
    (hp : p ∈ S.oddSubmodule) :
    killingForm ℝ L k p = 0 := by
  have hk' : S.θ k = k := (S.mem_even_iff).1 hk
  have hp' : S.θ p = -p := (S.mem_oddSubmodule_iff).1 hp
  have h := killing_invariant (S := S) k p
  rw [hk', hp'] at h
  have hneg : killingForm ℝ L k (-p)
      = -killingForm ℝ L k p := by
    exact map_neg (killingForm ℝ L k) p
  rw [hneg] at h
  have hsymm : -killingForm ℝ L k p = killingForm ℝ L k p := h
  linarith

/-- Cartan form associated to a symmetric Lie algebra. -/
noncomputable def cartanForm (S : SymmetricLieAlgebra L) (x y : L) : ℝ :=
  -killingForm ℝ L x (S.θ y)

@[simp] lemma cartanForm_def (S : SymmetricLieAlgebra L) (x y : L) :
    S.cartanForm x y = -killingForm ℝ L x (S.θ y) :=
  rfl

/-- The Cartan form vanishes on mixed `𝔨/𝔭` terms. -/
lemma cartanForm_orthogonal
    (S : SymmetricLieAlgebra L)
    {k p : L}
    (hk : k ∈ S.evenLieSubalgebra)
    (hp : p ∈ S.oddSubmodule) :
    S.cartanForm k p = 0 := by
  have hp' : S.θ p = -p := (S.mem_oddSubmodule_iff).1 hp
  have hkp : killingForm ℝ L k p = 0 := killing_orthogonal (S := S) hk hp
  unfold cartanForm
  rw [hp']
  simp [map_neg, hkp]

/-- Abstract signature split assumptions for the Cartan form. -/
structure CartanSignature (S : SymmetricLieAlgebra L) where
  nonneg_on_odd :
    ∀ x, x ∈ S.oddSubmodule → 0 ≤ S.cartanForm x x
  nonpos_on_even :
    ∀ x, x ∈ S.evenLieSubalgebra → S.cartanForm x x ≤ 0

attribute [infrastructure]
  CartanSignature.nonneg_on_odd
  CartanSignature.nonpos_on_even

attribute [infrastructure]
  instPreservesLinear
  instPreservesLieBracket
  instPreservesLie
  involutive
  mem_even_iff
  plusPart_of_mem_even
  minusPart_of_mem_even
  plusPart_of_mem_odd
  minusPart_of_mem_odd
  cartan_left_inverse
  oddTriple_jacobi

attribute [expository]
  segment_subset_even
  segment_subset_odd
  add_smul_sub_mem_even
  add_smul_sub_mem_odd
  decomposition
  cartan_decomposition
  odd_isConnected
  odd_isPathConnected
  even_isConnected
  even_isPathConnected
  oddLocalModel_odd
  oddLocalModel_tripleSystem
  oddLocalModel_convex
  oddLocalModel_pathConnected
  cartanForm_def

attribute [terminal]
  cartan_direct_sum

end KillingForm

end SymmetricLieAlgebra

section Endomorphism

variable {V : Type _} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Conjugation by an involutive endomorphism as an abstract symmetric Lie algebra. -/
noncomputable def endoSymmetricLieAlgebra
    (J : V →L[ℝ] V)
    (hJ : J.comp J = ContinuousLinearMap.id ℝ V) :
    SymmetricLieAlgebra (V →L[ℝ] V) :=
  SymmetricLieAlgebra.ofInvolutiveLieAut
    ⟨conjugationLieEquiv J hJ, by
      simpa [conjugationLieEquiv] using
        (conjugationMap_involutive J hJ :
          Function.Involutive (conjugationMap J))⟩

/-- Conjugation by an endomorphism squaring to -Id as an abstract symmetric Lie algebra. -/
noncomputable def endoSymmetricLieAlgebra_sq_neg_one
    (J : V →L[ℝ] V)
    (hJ : J.comp J = -ContinuousLinearMap.id ℝ V) :
    SymmetricLieAlgebra (V →L[ℝ] V) :=
  SymmetricLieAlgebra.ofInvolutiveLieAut
    ⟨conjugationLieEquiv_sq_neg_one J hJ, by
      simpa [conjugationLieEquiv_sq_neg_one] using
        (conjugationMapNeg_involutive J hJ :
          Function.Involutive (conjugationMapNeg J))⟩

end Endomorphism

end InfoGeometry.Core
