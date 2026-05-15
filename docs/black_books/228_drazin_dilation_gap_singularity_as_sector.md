# Chapter 228: The Drazin Dilation Gap — Singularity as a Sector

## Theorem-safe correction (core distinction)

For this lane, keep these objects distinct:

- Drazin regular support: `P_D := A A^D = A^D A`
- Drazin defect projector (singular sector): `Q_0 := 1 - P_D`
- Moore–Penrose range support: `P_range := A A^†`
- Moore–Penrose domain support: `P_domain := A^† A`
- Dilation gap: `G_A := (1/2) (P_range - P_domain)`

So:

- `Q_0` is the singular/generalized-zero sector.
- `G_A` is the range-domain support mismatch (EP obstruction).

Do **not** identify `G_A` with the singular sector.

---

## 1. Principle

The Drazin inverse does not erase singularity; it indexes it.

`A^D` is inverse on the regular sector and zero on the generalized singular sector.

With `P_D := A A^D` and `Q_0 := 1 - P_D`, singularity is formalized as a sector, not treated as an algebraic pathology.

---

## 2. Drazin support vs Moore–Penrose support

For Hilbert-space `A` with Moore–Penrose inverse `A^†`:

- `P_range := A A^†`
- `P_domain := A^† A`

Define the Drazin Dilation Gap:

`G_A := (1/2) (P_range - P_domain)`.

Balanced/EP-aligned case: `P_range = P_domain`, hence `G_A = 0`.

Two different obstructions are now explicit:

- `Q_0`: where regular invertibility fails.
- `G_A`: how input/output supports fail to align.

---

## 3. Drazin supercharge

Let `P_D := A A^D` and `G_A := (1/2)(P_range - P_domain)`.

Odd commutator generator:

`C_D := [P_D, G_A]`.

If `P_D` and `G_A` are self-adjoint, then `C_D` is skew-adjoint. For Hilbert-space physics, use the self-adjoint normalization

`Q_D := 2 i [P_D, G_A]`.

Algebraic real-lane variant keeps `2 [P_D, G_A]` as odd anti-self-adjoint generator.

Grading from Drazin split:

`Γ_D := 2 P_D - 1`.

Then `[P_D, G_A]` is odd relative to `Γ_D`.

---

## 4. Kinetic/defect split (witness-gated)

Use this as a calibrated structural law, not an automatic identity in every algebra:

`Q_D^2 = H_kin + Z`.

Interpretation:

- `H_kin`: regular dissipative/thermalized contribution.
- `Z`: defect/central/topological memory contribution.

Support constraints (representative forms):

- `P_D H_kin P_D = H_kin`
- `Q_0 Z Q_0 = Z` (or central-charge commutator lane).

Thus the Drazin split separates heat dynamics from protected memory structure.

---

## 5. Thermodynamic role

Entropy production belongs to the regular dissipative support; singular zero modes should not be naively treated as invertible thermal modes.

Drazin decomposition enforces this support discipline:

- regular lane contributes to entropy production,
- defect lane carries index/central/memory observables.

Slogan:

- heat flows in the Drazin regular sector,
- memory lives in the Drazin defect sector.

---

## 6. Schur reduction and effective dynamics

For singular block elimination, ordinary inverse may fail. Stabilized Schur complements use generalized inverses:

- Moore–Penrose lane: `S_eff = A - B D^† C`
- Drazin lane: `S_eff^D = A - B D^D C`

The choice encodes which modes are thermally eliminated and which are retained as defect-memory variables.

---

## 7. Cartan split viewpoint

With involution `θ^2 = 1`, write `𝒜 = 𝒜_+ ⊕ 𝒜_-`.

In the intended interpretation:

- one lane carries memory/defect/central behavior,
- the other carries heat/dissipative behavior.

`P_D`, `Q_0`, and `G_A` jointly witness whether support decomposition aligns with thermodynamic splitting.

---

## 8. Final principle

- Drazin inverse: invert only where inversion is meaningful.
- Drazin support: regular sector.
- Drazin complement: defect sector.
- MP dilation gap: input/output support mismatch.
- Drazin supercharge: odd transition witness across the support split.

Conceptual closure:

**Singularity becomes structured memory when indexed by Drazin support.**

---

## Lean-facing socket (theorem-safe carrier)

```lean
/-
InfoGeometry/Canonical/DrazinDilationGap.lean

Drazin Dilation Gap:
  Drazin support      P_D = A Aᴰ
  Drazin defect       Q₀  = 1 - P_D
  MP range support    P_R = A A†
  MP domain support   P_I = A† A
  Dilation gap        G   = 1/2 (P_R - P_I)
  Drazin supercharge  Q   = 2 [P_D, G]    -- algebraic odd generator
                    or 2 i [P_D, G]       -- Hilbert self-adjoint version
-/

import Mathlib

noncomputable section

namespace InfoGeometry.Canonical.DrazinDilationGap

structure DrazinData
    (Op : Type*)
    [Ring Op]
    [Star Op] where
  A : Op
  AD : Op
  P_D : Op
  Q₀ : Op
  P_D_def : P_D = A * AD
  commute : A * AD = AD * A
  P_D_idempotent : P_D * P_D = P_D
  P_D_self_adjoint : star P_D = P_D
  Q₀_def : Q₀ = 1 - P_D

structure MoorePenroseSupportData
    (Op : Type*)
    [Ring Op]
    [Star Op] where
  A : Op
  A_MP : Op
  P_range : Op
  P_domain : Op
  P_range_def : P_range = A * A_MP
  P_domain_def : P_domain = A_MP * A
  P_range_idempotent : P_range * P_range = P_range
  P_domain_idempotent : P_domain * P_domain = P_domain
  P_range_self_adjoint : star P_range = P_range
  P_domain_self_adjoint : star P_domain = P_domain

structure DilationGapData
    (Op : Type*)
    [Ring Op]
    [Star Op]
    [SMul ℝ Op] where
  mp : MoorePenroseSupportData Op
  halfScalar : ℝ
  G : Op
  G_def : G = halfScalar • (mp.P_range - mp.P_domain)

def commutator
    {Op : Type*}
    [Mul Op] [Sub Op]
    (X Y : Op) : Op :=
  X * Y - Y * X

structure DrazinSuperchargeData
    (Op : Type*)
    [Ring Op]
    [Star Op]
    [SMul ℝ Op] where
  drazin : DrazinData Op
  gap : DilationGapData Op
  Q_alg : Op
  Q_alg_def : Q_alg = (2 : ℝ) • commutator drazin.P_D gap.G

structure DrazinKineticDefectSplit
    (Op : Type*)
    [Ring Op]
    [Star Op]
    [SMul ℝ Op] where
  supercharge : DrazinSuperchargeData Op
  H_kin : Op
  Z_defect : Op
  split_law : supercharge.Q_alg * supercharge.Q_alg = H_kin + Z_defect
  H_kin_regular :
    supercharge.drazin.P_D * H_kin * supercharge.drazin.P_D = H_kin
  Z_defect_supported :
    supercharge.drazin.Q₀ * Z_defect * supercharge.drazin.Q₀ = Z_defect

theorem drazin_supercharge_square_split
    {Op : Type*}
    [Ring Op]
    [Star Op]
    [SMul ℝ Op]
    (S : DrazinKineticDefectSplit Op) :
    S.supercharge.Q_alg * S.supercharge.Q_alg =
      S.H_kin + S.Z_defect :=
  S.split_law

theorem dilation_gap_zero_of_supports_equal
    {Op : Type*}
    [Ring Op]
    [Star Op]
    [SMul ℝ Op]
    (G : DilationGapData Op)
    (h : G.mp.P_range = G.mp.P_domain)
    (hzero : G.halfScalar • (0 : Op) = 0) :
    G.G = 0 := by
  rw [G.G_def, h]
  simp only [sub_self]
  exact hzero

end InfoGeometry.Canonical.DrazinDilationGap
```

---

## Final sentence

The Drazin Dilation Gap measures how regular support, singular memory, and Moore–Penrose input/output asymmetry fail to coincide.

Physical reading: Drazin support carries heat, Drazin defect carries memory, and the dilation gap measures the anomaly between them.
