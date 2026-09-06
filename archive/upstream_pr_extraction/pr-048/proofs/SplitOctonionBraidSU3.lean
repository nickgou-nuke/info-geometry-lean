import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.GroupTheory.Perm.Basic
/-!
# Split octonions, braid permutations, and SU(3) color data

This file formalizes finite algebraic checks for the proposed
Bilson-Thompson/Furey/split-octonion color layer:

* the two adjacent color transpositions satisfy the B₃ Artin relation;
* these transpositions satisfy the braid relation in `S₃`;
* the `S₃` color permutation action is recorded as Weyl-group data for
  `SU(3)_c`;
* the complexified split quadratic form has a concrete nonzero isotropic vector;
* Zorn-style split-octonion coordinates contain a concrete nonzero nilpotent;
* the tripotent scale determinant has a simple zero at `s = 0`.
-/

noncomputable section

namespace SplitOctonionBraidSU3

/-! ## Coxeter generator data in S₃ -/

inductive Color where
  | red | green | blue
  deriving DecidableEq, Repr

open Color

/-- First adjacent transposition: red ↔ green. -/
def swapRG : Color → Color
  | red => green
  | green => red
  | blue => blue

/-- Second adjacent transposition: green ↔ blue. -/
def swapGB : Color → Color
  | red => red
  | green => blue
  | blue => green

/-- Ordinary function composition, applying `g` first and then `f`. -/
def comp (f g : Color → Color) : Color → Color := fun c => f (g c)

/-- Adjacent transpositions square to identity. -/
theorem swapRG_sq : comp swapRG swapRG = id := by
  funext c
  cases c <;> rfl

/-- Adjacent transpositions square to identity. -/
theorem swapGB_sq : comp swapGB swapGB = id := by
  funext c
  cases c <;> rfl

/-- The Artin braid relation for the adjacent transpositions in `S₃`. -/
theorem S3_braid_relation :
    comp swapRG (comp swapGB swapRG) = comp swapGB (comp swapRG swapGB) := by
  funext c <;> cases c <;> rfl

/-! ## Bundled permutation/Weyl-group data -/

/--
The finite color Weyl-group model.

Mathematically, the Weyl group of type `A₂`, hence of `SU(3)`,
is isomorphic to the permutation group on three colors.
This definition records only that finite permutation model.
-/
abbrev SU3ColorWeylModel := Equiv.Perm Color

/-- Bundled permutation corresponding to red ↔ green. -/
def swapRGPerm : SU3ColorWeylModel where
  toFun := swapRG
  invFun := swapRG
  left_inv := by
    intro c
    cases c <;> rfl
  right_inv := by
    intro c
    cases c <;> rfl

/-- Bundled permutation corresponding to green ↔ blue. -/
def swapGBPerm : SU3ColorWeylModel where
  toFun := swapGB
  invFun := swapGB
  left_inv := by
    intro c
    cases c <;> rfl
  right_inv := by
    intro c
    cases c <;> rfl

/-- The first simple reflection is involutive. -/
theorem swapRGPerm_sq :
    swapRGPerm * swapRGPerm = 1 := by
  apply Equiv.ext
  intro c
  cases c <;> rfl

/-- The second simple reflection is involutive. -/
theorem swapGBPerm_sq :
    swapGBPerm * swapGBPerm = 1 := by
  apply Equiv.ext
  intro c
  cases c <;> rfl

/--
The type-`A₂` Coxeter braid relation in the bundled permutation group.
-/
theorem SU3ColorWeyl_braid_relation :
    swapRGPerm * swapGBPerm * swapRGPerm =
      swapGBPerm * swapRGPerm * swapGBPerm := by
  apply Equiv.ext
  intro c
  cases c <;> rfl


/-! ## Complexified split quadratic form and zero-divisors -/

/-- Coordinate model for a complexified split-octonion vector. -/
structure Split8 where
  x0 : ℂ
  x1 : ℂ
  x2 : ℂ
  x3 : ℂ
  x4 : ℂ
  x5 : ℂ
  x6 : ℂ
  x7 : ℂ

/-- The complexified split quadratic form has a concrete nonzero isotropic vector. -/
def splitQuadratic (x : Split8) : ℂ :=
  x.x0^2 + x.x1^2 + x.x2^2 + x.x3^2 - x.x4^2 - x.x5^2 - x.x6^2 - x.x7^2

/-- A concrete nonzero isotropic vector: `(1,0,0,0,1,0,0,0)`. -/
def nullVector : Split8 where
  x0 := 1; x1 := 0; x2 := 0; x3 := 0; x4 := 1; x5 := 0; x6 := 0; x7 := 0

/-- The concrete vector lies on the split null cone. -/
theorem nullVector_norm_zero : splitQuadratic nullVector = 0 := by
  simp [splitQuadratic, nullVector]

/-- The concrete null vector is nonzero. -/
theorem nullVector_nonzero : nullVector.x0 ≠ 0 := by
  norm_num [nullVector]

/-- Minimal Zorn-style split-octonion coordinates. -/
structure Zorn where
  a : ℂ
  u : Fin 3 → ℂ
  v : Fin 3 → ℂ
  b : ℂ

/-- Extensionality for Zorn coordinates. -/
theorem zorn_ext {X Y : Zorn}
    (ha : X.a = Y.a) (hu : X.u = Y.u) (hv : X.v = Y.v) (hb : X.b = Y.b) : X = Y := by
  cases X
  cases Y
  simp_all

/-- Dot product in three complex coordinates. -/
def dot3 (u v : Fin 3 → ℂ) : ℂ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- The Zorn determinant (norm). -/
def zornNorm (X : Zorn) : ℂ :=
  X.a * X.b - dot3 X.u X.v

/-- Coordinate transformation mapping Split8 components to Zorn coordinates. -/
def split8ToZorn (x : Split8) : Zorn where
  a := x.x0 + x.x4
  b := x.x0 - x.x4
  u := fun i => match i with
    | ⟨0, _⟩ => x.x1 + x.x5
    | ⟨1, _⟩ => x.x2 + x.x6
    | ⟨2, _⟩ => x.x3 + x.x7
  v := fun i => match i with
    | ⟨0, _⟩ => x.x5 - x.x1
    | ⟨1, _⟩ => x.x6 - x.x2
    | ⟨2, _⟩ => x.x7 - x.x3

/-- The coordinate transformation carries the diagonal split form to the Zorn norm. -/
theorem split8ToZorn_norm (x : Split8) :
    zornNorm (split8ToZorn x) = splitQuadratic x := by
  dsimp [zornNorm, split8ToZorn, splitQuadratic, dot3]
  ring

/-- Cross product in three coordinates using robust Fin 3 matching. -/
def cross3 (u v : Fin 3 → ℂ) : Fin 3 → ℂ := fun i =>
  match i with
  | ⟨0, _⟩ => u 1 * v 2 - u 2 * v 1
  | ⟨1, _⟩ => u 2 * v 0 - u 0 * v 2
  | ⟨2, _⟩ => u 0 * v 1 - u 1 * v 0

/-- Zorn multiplication for split octonions. -/
def zornMul (X Y : Zorn) : Zorn where
  a := X.a * Y.a + dot3 X.u Y.v
  u := fun i => X.a * Y.u i + Y.b * X.u i - cross3 X.v Y.v i
  v := fun i => Y.a * X.v i + X.b * Y.v i + cross3 X.u Y.u i
  b := dot3 X.v Y.u + X.b * Y.b

/-- The canonical Zorn product as Lean's multiplication operation.

This instance is intentionally only a `Mul`: Zorn multiplication is
nonassociative, so no semigroup instance is asserted.
-/
instance : Mul Zorn := ⟨zornMul⟩

def zornAdd (X Y : Zorn) : Zorn where
  a := X.a + Y.a
  u := fun i => X.u i + Y.u i
  v := fun i => X.v i + Y.v i
  b := X.b + Y.b

def zornSub (X Y : Zorn) : Zorn where
  a := X.a - Y.a
  u := fun i => X.u i - Y.u i
  v := fun i => X.v i - Y.v i
  b := X.b - Y.b

def zornSmul (c : ℂ) (X : Zorn) : Zorn where
  a := c * X.a
  u := fun i => c * X.u i
  v := fun i => c * X.v i
  b := c * X.b

/-- Zero Zorn element. -/
def zornZero : Zorn where
  a := 0; u := fun _ => 0; v := fun _ => 0; b := 0

/-- The coordinate zero on the canonical Zorn carrier. -/
instance : Zero Zorn := ⟨zornZero⟩

/-- A concrete nonzero nilpotent Zorn element. -/
def zornNilpotent : Zorn where
  a := 0
  u := fun i => if i = 0 then (1 : ℂ) else (0 : ℂ)
  v := fun _ => 0
  b := 0

/-- The imaginary unit in ℂ -/
def I_c : ℂ := Complex.I

/-- A unit vector along the color axis k -/
def e_k (k : Fin 3) : Fin 3 → ℂ := fun i => if i = k then (1 : ℂ) else (0 : ℂ)

/-- Upper nilpotent (E_k) along axis k -/
def E_k (k : Fin 3) : Zorn where
  a := 0; u := e_k k; v := fun _ => 0; b := 0

/-- Lower nilpotent (F_k) along axis k -/
def F_k (k : Fin 3) : Zorn where
  a := 0; u := fun _ => 0; v := e_k k; b := 0

/-- The Clifford/Majorana symmetric generator Q_k = E_k + F_k -/
def Q_k (k : Fin 3) : Zorn where
  a := 0; u := e_k k; v := e_k k; b := 0

/-- The paracomplex split unit ℓ -/
def ell : Zorn where
  a := 1; u := fun _ => 0; v := fun _ => 0; b := -1

/-- Identity element -/
def I_zorn : Zorn where
  a := 1; u := fun _ => 0; v := fun _ => 0; b := 1

/-- The two-sided Zorn identity as Lean's `One` operation. -/
instance : One Zorn := ⟨I_zorn⟩

/-- Topological braid generator (unnormalized) -/
def unnormalizedR_k (k : Fin 3) : Zorn :=
  zornAdd I_zorn (zornSmul I_c (Q_k k))

/-- Inverse topological braid generator (unnormalized) -/
def unnormalizedR_k_inv (k : Fin 3) : Zorn :=
  zornSmul (1 / 2 : ℂ) (zornSub I_zorn (zornSmul I_c (Q_k k)))

theorem Q_k_sq (k : Fin 3) :
    zornMul (Q_k k) (Q_k k) = I_zorn := by
  apply zorn_ext
  · fin_cases k <;>
      simp [zornMul, Q_k, e_k, I_zorn, dot3, cross3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [zornMul, Q_k, e_k, I_zorn, dot3, cross3]
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [zornMul, Q_k, e_k, I_zorn, dot3, cross3]
  · fin_cases k <;>
      simp [zornMul, Q_k, e_k, I_zorn, dot3, cross3]

theorem unnormalizedR_k_mul_unnormalizedR_k_inv (k : Fin 3) :
    zornMul (unnormalizedR_k k) (unnormalizedR_k_inv k) = I_zorn := by
  apply zorn_ext
  · fin_cases k <;>
      simp [
        unnormalizedR_k, unnormalizedR_k_inv, zornMul, zornAdd, zornSub,
        zornSmul, I_c, Q_k, e_k, I_zorn, dot3, cross3
      ] <;> ring_nf <;> try rw [Complex.I_sq] <;> ring
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [
        unnormalizedR_k, unnormalizedR_k_inv, zornMul, zornAdd, zornSub,
        zornSmul, I_c, Q_k, e_k, I_zorn, dot3, cross3
      ] <;> ring_nf <;> try rw [Complex.I_sq] <;> ring
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [
        unnormalizedR_k, unnormalizedR_k_inv, zornMul, zornAdd, zornSub,
        zornSmul, I_c, Q_k, e_k, I_zorn, dot3, cross3
      ] <;> ring_nf <;> try rw [Complex.I_sq] <;> ring
  · fin_cases k <;>
      simp [
        unnormalizedR_k, unnormalizedR_k_inv, zornMul, zornAdd, zornSub,
        zornSmul, I_c, Q_k, e_k, I_zorn, dot3, cross3
      ] <;> ring_nf <;> try rw [Complex.I_sq] <;> ring

theorem unnormalizedR_k_inv_mul_unnormalizedR_k (k : Fin 3) :
    zornMul (unnormalizedR_k_inv k) (unnormalizedR_k k) = I_zorn := by
  apply zorn_ext
  · fin_cases k <;>
      simp [
        unnormalizedR_k, unnormalizedR_k_inv, zornMul, zornAdd, zornSub,
        zornSmul, I_c, Q_k, e_k, I_zorn, dot3, cross3
      ] <;> ring_nf <;> try rw [Complex.I_sq] <;> ring
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [
        unnormalizedR_k, unnormalizedR_k_inv, zornMul, zornAdd, zornSub,
        zornSmul, I_c, Q_k, e_k, I_zorn, dot3, cross3
      ] <;> ring_nf <;> try rw [Complex.I_sq] <;> ring
  · funext i
    fin_cases k <;> fin_cases i <;>
      simp [
        unnormalizedR_k, unnormalizedR_k_inv, zornMul, zornAdd, zornSub,
        zornSmul, I_c, Q_k, e_k, I_zorn, dot3, cross3
      ] <;> ring_nf <;> try rw [Complex.I_sq] <;> ring
  · fin_cases k <;>
      simp [
        unnormalizedR_k, unnormalizedR_k_inv, zornMul, zornAdd, zornSub,
        zornSmul, I_c, Q_k, e_k, I_zorn, dot3, cross3
      ] <;> ring_nf <;> try rw [Complex.I_sq] <;> ring

/-- Temporary compatibility aliases for YangBaxterZornBridge -/
abbrev R_k := unnormalizedR_k
abbrev R_k_inv := unnormalizedR_k_inv

-- Distributive laws
lemma zornMul_add (X Y Z : Zorn) : 
    zornMul X (zornAdd Y Z) = zornAdd (zornMul X Y) (zornMul X Z) := by
  apply zorn_ext
  · simp [zornMul, zornAdd, dot3]; ring
  · funext i; fin_cases i <;> (simp [zornMul, zornAdd, cross3]; ring)
  · funext i; fin_cases i <;> (simp [zornMul, zornAdd, cross3]; ring)
  · simp [zornMul, zornAdd, dot3]; ring

lemma add_zornMul (X Y Z : Zorn) : 
    zornMul (zornAdd X Y) Z = zornAdd (zornMul X Z) (zornMul Y Z) := by
  apply zorn_ext
  · simp [zornMul, zornAdd, dot3]; ring
  · funext i; fin_cases i <;> (simp [zornMul, zornAdd, cross3]; ring)
  · funext i; fin_cases i <;> (simp [zornMul, zornAdd, cross3]; ring)
  · simp [zornMul, zornAdd, dot3]; ring

-- Scalar multiplication laws
lemma zornMul_smul (c : ℂ) (X Y : Zorn) : 
    zornMul X (zornSmul c Y) = zornSmul c (zornMul X Y) := by
  apply zorn_ext
  · simp [zornMul, zornSmul, dot3]; ring
  · funext i; fin_cases i <;> (simp [zornMul, zornSmul, cross3]; ring)
  · funext i; fin_cases i <;> (simp [zornMul, zornSmul, cross3]; ring)
  · simp [zornMul, zornSmul, dot3]; ring

lemma smul_zornMul (c : ℂ) (X Y : Zorn) : 
    zornMul (zornSmul c X) Y = zornSmul c (zornMul X Y) := by
  apply zorn_ext
  · simp [zornMul, zornSmul, dot3]; ring
  · funext i; fin_cases i <;> (simp [zornMul, zornSmul, cross3]; ring)
  · funext i; fin_cases i <;> (simp [zornMul, zornSmul, cross3]; ring)
  · simp [zornMul, zornSmul, dot3]; ring

-- Identity laws
lemma zornMul_I_zorn (X : Zorn) : zornMul X I_zorn = X := by
  apply zorn_ext
  · simp [zornMul, I_zorn, dot3]
  · funext i; fin_cases i <;> simp [zornMul, I_zorn, cross3]
  · funext i; fin_cases i <;> simp [zornMul, I_zorn, cross3]
  · simp [zornMul, I_zorn, dot3]

lemma I_zorn_zornMul (X : Zorn) : zornMul I_zorn X = X := by
  apply zorn_ext
  · simp [zornMul, I_zorn, dot3]
  · funext i; fin_cases i <;> simp [zornMul, I_zorn, cross3]
  · funext i; fin_cases i <;> simp [zornMul, I_zorn, cross3]
  · simp [zornMul, I_zorn, dot3]

/-!
The Zorn multiplication is a composition law.  This is the central norm
identity for the complexified split-octonion coordinate model.
-/
theorem zornNorm_mul (X Y : Zorn) :
    zornNorm (zornMul X Y) = zornNorm X * zornNorm Y := by
  simp [zornNorm, zornMul, dot3, cross3]
  ring

/-- The concrete nilpotent is not the zero Zorn element. -/
theorem zornNilpotent_nonzero :
    zornNilpotent ≠ zornZero := by
  intro h
  have hcoord : (1 : ℂ) = 0 := by
    simpa [zornNilpotent, zornZero] using
      congrArg (fun X : Zorn => X.u (0 : Fin 3)) h
  exact one_ne_zero hcoord

/-- The concrete nonzero Zorn element has square zero. -/
theorem zornNilpotent_sq_zero :
    zornMul zornNilpotent zornNilpotent = zornZero := by
  apply zorn_ext
  · simp [zornMul, zornNilpotent, zornZero, dot3]
  · funext i
    fin_cases i <;>
      simp [zornMul, zornNilpotent, zornZero, cross3]
  · funext i
    fin_cases i <;>
      simp [zornMul, zornNilpotent, zornZero, cross3]
  · simp [zornMul, zornNilpotent, zornZero, dot3]

/-! ## Tripotent spectral determinant -/

/--
The nonzero-mode cofactor associated with the tripotent eigenvalues
`-1`, `0`, and `1`.
-/
def tripotentScaleCofactor (s : ℂ) : ℂ :=
  (s + 1) * (s - 1)

/--
The spectral determinant associated with eigenvalues `-1`, `0`, and `1`.

It is written with the zero-mode factor exposed:
`det(s) = s (s + 1) (s - 1)`.
-/
def tripotentScaleDet (s : ℂ) : ℂ :=
  s * tripotentScaleCofactor s

/-- The tripotent spectral determinant vanishes at the zero mode. -/
theorem tripotentScaleDet_zero_mode :
    tripotentScaleDet 0 = 0 := by
  norm_num [tripotentScaleDet, tripotentScaleCofactor]

/--
The cofactor multiplying the zero-mode factor is nonzero at `s = 0`.
This is the algebraic certificate that the zero-mode root is simple.
-/
theorem tripotentScaleCofactor_zero :
    tripotentScaleCofactor 0 = -1 := by
  norm_num [tripotentScaleCofactor]

/-- The zero-mode cofactor does not vanish. -/
theorem tripotentScaleCofactor_zero_ne_zero :
    tripotentScaleCofactor 0 ≠ 0 := by
  norm_num [tripotentScaleCofactor]

/-- All three tripotent spectral values are roots of the determinant. -/
theorem tripotentScaleDet_at_neg_one :
    tripotentScaleDet (-1) = 0 := by
  norm_num [tripotentScaleDet, tripotentScaleCofactor]

theorem tripotentScaleDet_at_one :
    tripotentScaleDet 1 = 0 := by
  norm_num [tripotentScaleDet, tripotentScaleCofactor]

end SplitOctonionBraidSU3
