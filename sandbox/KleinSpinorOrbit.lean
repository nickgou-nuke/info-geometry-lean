import InfoGeometry.Clifford.Arxiv160309063SplitAlgebra
import Mathlib.Tactic

set_option linter.dupNamespace false

/-!
# Theorem-safe split-complex Klein spinor stabilizer equations

This file records only finite coordinate facts around the `Spin(2,2) ≃ SL(2,C_s)`
spinor discussion of Fioresi--Latini--Marrani, arXiv:1603.09063v2.

We do **not** prove a global spin-group isomorphism, orbit classification, or
manifold dimension theorem.  We work with raw `2 × 2` matrices over the concrete
split-complex coordinate model from `Arxiv160309063SplitAlgebra` and prove exact
stabilizer equations for selected representatives.
-/

namespace InfoGeometry.Algebra.KleinSpinorOrbit

namespace Cs

abbrev Cs := InfoGeometry.Clifford.Arxiv160309063.SplitC

/-- Split-complex zero. -/
def zero : Cs := ⟨0, 0⟩

/-- Split-complex one. -/
def one : Cs := InfoGeometry.Clifford.Arxiv160309063.SplitC.one

/-- Split-complex addition. -/
def add : Cs → Cs → Cs := InfoGeometry.Clifford.Arxiv160309063.SplitC.add

/-- Split-complex negation. -/
def neg : Cs → Cs := InfoGeometry.Clifford.Arxiv160309063.SplitC.neg

/-- Split-complex multiplication. -/
def mul : Cs → Cs → Cs := InfoGeometry.Clifford.Arxiv160309063.SplitC.mul

/-- Scalar embedding. -/
def scalar : ℚ → Cs := InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar

/-- Lightlike zero divisor `E = 1 + j`. -/
def E : Cs := InfoGeometry.Clifford.Arxiv160309063.SplitC.E

/-- Conjugate lightlike zero divisor `Ebar = 1 - j`. -/
def Ebar : Cs := InfoGeometry.Clifford.Arxiv160309063.SplitC.Ebar

/-- Coordinate extensionality helper. -/
theorem ext {x y : Cs} (hre : x.re = y.re) (him : x.im = y.im) : x = y :=
  InfoGeometry.Clifford.Arxiv160309063.SplitC.ext hre him

@[simp] theorem mul_E_coord (a b : ℚ) : mul ⟨a, b⟩ E = ⟨a + b, a + b⟩ := by
  exact InfoGeometry.Clifford.Arxiv160309063.SplitC.mul_E a b

@[simp] theorem mul_Ebar_coord (a b : ℚ) : mul ⟨a, b⟩ Ebar = ⟨a - b, -(a - b)⟩ := by
  exact InfoGeometry.Clifford.Arxiv160309063.SplitC.mul_Ebar a b

/-- The distinguished lightlike directions multiply to zero. -/
theorem E_zero_divisor : mul E Ebar = zero := by
  exact InfoGeometry.Clifford.Arxiv160309063.SplitC.E_mul_Ebar

/-- Coordinate criterion for stabilizing the `E` line at the vector `E`. -/
theorem mul_E_eq_E_iff (z : Cs) : mul z E = E ↔ z.re + z.im = 1 := by
  cases z with
  | mk a b =>
    constructor
    · intro h
      have hre := congrArg InfoGeometry.Clifford.Arxiv160309063.SplitC.re h
      simpa [mul, E, InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.E] using hre
    · intro h
      apply ext <;> simp [mul, E, InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.E, h]

/-- Coordinate criterion for annihilating the lightlike vector `E`. -/
theorem mul_E_eq_zero_iff (z : Cs) : mul z E = zero ↔ z.re + z.im = 0 := by
  cases z with
  | mk a b =>
    constructor
    · intro h
      have hre := congrArg InfoGeometry.Clifford.Arxiv160309063.SplitC.re h
      simpa [mul, E, zero, InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.E] using hre
    · intro h
      apply ext <;> simp [mul, E, zero, InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.E, h]

/-- The affine `E`-line equation `re+im=1` is exactly `1 + t Ebar`. -/
theorem sum_eq_one_iff_exists_one_add_scalar_Ebar (z : Cs) :
    z.re + z.im = 1 ↔ ∃ t : ℚ, z = add one (mul (scalar t) Ebar) := by
  cases z with
  | mk a b =>
    constructor
    · intro h
      refine ⟨a - 1, ?_⟩
      apply ext
      · simp [add, one, mul, scalar, Ebar,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.add,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.one,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.Ebar]
      · simp [add, one, mul, scalar, Ebar,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.add,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.one,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.Ebar]
        linarith
    · rintro ⟨t, ht⟩
      rw [ht]
      simp [add, one, mul, scalar, Ebar,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.add,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.one,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.Ebar]

/-- The homogeneous `E`-line annihilator equation `re+im=0` is exactly `t Ebar`. -/
theorem sum_eq_zero_iff_exists_scalar_Ebar (z : Cs) :
    z.re + z.im = 0 ↔ ∃ t : ℚ, z = mul (scalar t) Ebar := by
  cases z with
  | mk a b =>
    constructor
    · intro h
      refine ⟨a, ?_⟩
      apply ext
      · simp [mul, scalar, Ebar,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.Ebar]
      · simp [mul, scalar, Ebar,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.Ebar]
        linarith
    · rintro ⟨t, ht⟩
      rw [ht]
      simp [mul, scalar, Ebar,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar,
        InfoGeometry.Clifford.Arxiv160309063.SplitC.Ebar]

@[simp] theorem add_zero (x : Cs) : add x zero = x := by
  cases x
  apply ext <;> simp [add, zero, InfoGeometry.Clifford.Arxiv160309063.SplitC.add]

@[simp] theorem zero_add (x : Cs) : add zero x = x := by
  cases x
  apply ext <;> simp [add, zero, InfoGeometry.Clifford.Arxiv160309063.SplitC.add]

@[simp] theorem mul_zero (x : Cs) : mul x zero = zero := by
  cases x
  apply ext <;> simp [mul, zero, InfoGeometry.Clifford.Arxiv160309063.SplitC.mul]

@[simp] theorem zero_mul (x : Cs) : mul zero x = zero := by
  cases x
  apply ext <;> simp [mul, zero, InfoGeometry.Clifford.Arxiv160309063.SplitC.mul]

@[simp] theorem one_mul (x : Cs) : mul one x = x := by
  cases x
  apply ext <;> simp [mul, one, InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.one,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar]

@[simp] theorem mul_one (x : Cs) : mul x one = x := by
  cases x
  apply ext <;> simp [mul, one, InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.one,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar]

@[simp] theorem add_neg_self (x : Cs) : add x (neg x) = zero := by
  cases x
  apply ext <;> simp [add, neg, zero, InfoGeometry.Clifford.Arxiv160309063.SplitC.add,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.neg]

end Cs

/-- A column spinor in `C_s²`. -/
structure CsSpinor where
  plus : Cs.Cs
  minus : Cs.Cs
  deriving DecidableEq, Repr

/-- A raw `2 × 2` matrix over `C_s`. -/
structure CsMatrix2 where
  aa : Cs.Cs
  ab : Cs.Cs
  ba : Cs.Cs
  bb : Cs.Cs
  deriving DecidableEq, Repr

namespace CsMatrix2

/-- Matrix-vector action by explicit coordinates. -/
def action (M : CsMatrix2) (ψ : CsSpinor) : CsSpinor :=
  ⟨Cs.add (Cs.mul M.aa ψ.plus) (Cs.mul M.ab ψ.minus),
   Cs.add (Cs.mul M.ba ψ.plus) (Cs.mul M.bb ψ.minus)⟩

/-- Raw determinant `aa*bb - ab*ba`. -/
def det (M : CsMatrix2) : Cs.Cs :=
  Cs.add (Cs.mul M.aa M.bb) (Cs.neg (Cs.mul M.ab M.ba))

/-- Determinant-one predicate for the raw coordinate matrix. -/
def DetOne (M : CsMatrix2) : Prop :=
  det M = Cs.one

/-- Identity matrix. -/
def identity : CsMatrix2 :=
  ⟨Cs.one, Cs.zero, Cs.zero, Cs.one⟩

/-- Upper unipotent family, a determinant-one generic stabilizer family. -/
def genericUnipotent (b : Cs.Cs) : CsMatrix2 :=
  ⟨Cs.one, b, Cs.zero, Cs.one⟩

/-- Lower `Ebar`-line family stabilizing the `E`-null representative. -/
def nullEbarFamily (t : ℚ) : CsMatrix2 :=
  ⟨Cs.one, Cs.zero, Cs.mul (Cs.scalar t) Cs.Ebar, Cs.one⟩

@[simp] theorem identity_action (ψ : CsSpinor) : action identity ψ = ψ := by
  cases ψ
  simp [action, identity]

@[simp] theorem identity_det_one : DetOne identity := by
  apply Cs.ext <;> norm_num [DetOne, det, identity, Cs.add, Cs.mul, Cs.neg, Cs.one, Cs.zero,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.add,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.neg,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.one,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar]

@[simp] theorem genericUnipotent_det_one (b : Cs.Cs) : DetOne (genericUnipotent b) := by
  cases b
  apply Cs.ext <;> norm_num [DetOne, det, genericUnipotent, Cs.add, Cs.mul, Cs.neg, Cs.one,
    Cs.zero, InfoGeometry.Clifford.Arxiv160309063.SplitC.add,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.neg,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.one,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar]

@[simp] theorem nullEbarFamily_det_one (t : ℚ) : DetOne (nullEbarFamily t) := by
  apply Cs.ext <;> norm_num [DetOne, det, nullEbarFamily, Cs.add, Cs.mul, Cs.neg, Cs.one,
    Cs.zero, Cs.scalar, Cs.Ebar, InfoGeometry.Clifford.Arxiv160309063.SplitC.add,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.neg,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.one,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.Ebar]

end CsMatrix2

/-- Generic representative `(1,0)`. -/
def genericRep : CsSpinor :=
  ⟨Cs.one, Cs.zero⟩

/-- Null zero-divisor representative `(E,0)`. -/
def nullRep : CsSpinor :=
  ⟨Cs.E, Cs.zero⟩

/-- Diagonal null representative `(E,E)`, useful for row-sum equations. -/
def diagonalNullRep : CsSpinor :=
  ⟨Cs.E, Cs.E⟩

/-- Stabilizer predicate for a spinor. -/
def Stabilizes (M : CsMatrix2) (ψ : CsSpinor) : Prop :=
  CsMatrix2.action M ψ = ψ

@[simp] theorem identity_stabilizes (ψ : CsSpinor) : Stabilizes CsMatrix2.identity ψ := by
  simp [Stabilizes]

/-- Exact generic-representative stabilizer equations for raw matrices. -/
theorem stabilizes_generic_iff (M : CsMatrix2) :
    Stabilizes M genericRep ↔ M.aa = Cs.one ∧ M.ba = Cs.zero := by
  constructor
  · intro h
    change CsMatrix2.action M genericRep = genericRep at h
    constructor
    · simpa [CsMatrix2.action, genericRep] using congrArg CsSpinor.plus h
    · simpa [CsMatrix2.action, genericRep] using congrArg CsSpinor.minus h
  · intro h
    rcases h with ⟨haa, hba⟩
    cases M
    simp_all [Stabilizes, CsMatrix2.action, genericRep]

/-- Exact null-representative stabilizer equations for raw matrices. -/
theorem stabilizes_null_iff (M : CsMatrix2) :
    Stabilizes M nullRep ↔ Cs.mul M.aa Cs.E = Cs.E ∧ Cs.mul M.ba Cs.E = Cs.zero := by
  constructor
  · intro h
    change CsMatrix2.action M nullRep = nullRep at h
    constructor
    · simpa [CsMatrix2.action, nullRep] using congrArg CsSpinor.plus h
    · simpa [CsMatrix2.action, nullRep] using congrArg CsSpinor.minus h
  · intro h
    rcases h with ⟨haa, hba⟩
    cases M
    simp_all [Stabilizes, CsMatrix2.action, nullRep]

/-- The lower `Ebar` family gives determinant-one null stabilizers. -/
theorem nullEbarFamily_stabilizes (t : ℚ) :
    Stabilizes (CsMatrix2.nullEbarFamily t) nullRep := by
  rw [stabilizes_null_iff]
  constructor
  · exact Cs.one_mul Cs.E
  · unfold CsMatrix2.nullEbarFamily
    change Cs.mul (Cs.mul (Cs.scalar t) Cs.Ebar) Cs.E = Cs.zero
    apply Cs.ext <;> simp [Cs.mul, Cs.scalar, Cs.Ebar, Cs.E, Cs.zero,
      InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
      InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar,
      InfoGeometry.Clifford.Arxiv160309063.SplitC.Ebar,
      InfoGeometry.Clifford.Arxiv160309063.SplitC.E]

/-- Exact diagonal-null stabilizer equations: only the two row sums matter. -/
theorem stabilizes_diagonalNull_iff (M : CsMatrix2) :
    Stabilizes M diagonalNullRep ↔
      Cs.add (Cs.mul M.aa Cs.E) (Cs.mul M.ab Cs.E) = Cs.E ∧
      Cs.add (Cs.mul M.ba Cs.E) (Cs.mul M.bb Cs.E) = Cs.E := by
  constructor
  · intro h
    change CsMatrix2.action M diagonalNullRep = diagonalNullRep at h
    constructor
    · exact congrArg CsSpinor.plus h
    · exact congrArg CsSpinor.minus h
  · intro h
    rcases h with ⟨h₁, h₂⟩
    cases M
    simp [Stabilizes, CsMatrix2.action, diagonalNullRep, h₁, h₂]

/-- Upper unipotents are determinant-one stabilizers of the generic representative. -/
theorem genericUnipotent_stabilizes (b : Cs.Cs) :
    CsMatrix2.DetOne (CsMatrix2.genericUnipotent b) ∧
    Stabilizes (CsMatrix2.genericUnipotent b) genericRep := by
  constructor
  · simp
  · rw [stabilizes_generic_iff]
    simp [CsMatrix2.genericUnipotent]

/--
Bundled determinant-one raw `2 × 2` split-complex matrices.

This is a theorem-safe local coordinate stand-in for the paper's
`SL(2, C_s)` notation.  We only bundle the determinant-one equation proved for
our concrete coordinate determinant; we do not claim a global Lie-group or Spin
isomorphism here.
-/
structure CsSL2 where
  M : CsMatrix2
  det_one : CsMatrix2.DetOne M
  deriving Repr

namespace CsSL2

/-- The bundled identity determinant-one matrix. -/
def identity : CsSL2 :=
  ⟨CsMatrix2.identity, CsMatrix2.identity_det_one⟩

/-- The bundled upper-unipotent determinant-one family. -/
def genericUnipotent (b : Cs.Cs) : CsSL2 :=
  ⟨CsMatrix2.genericUnipotent b, CsMatrix2.genericUnipotent_det_one b⟩

/-- The bundled lower `Ebar` determinant-one null-stabilizer family. -/
def nullEbarFamily (t : ℚ) : CsSL2 :=
  ⟨CsMatrix2.nullEbarFamily t, CsMatrix2.nullEbarFamily_det_one t⟩

/-- Action of a bundled determinant-one matrix on a split spinor. -/
def action (g : CsSL2) (ψ : CsSpinor) : CsSpinor :=
  CsMatrix2.action g.M ψ

/-- Stabilizer predicate for a bundled determinant-one matrix. -/
def Stabilizes (g : CsSL2) (ψ : CsSpinor) : Prop :=
  action g ψ = ψ

@[simp] theorem identity_action (ψ : CsSpinor) : action identity ψ = ψ := by
  simp [action, identity]

@[simp] theorem identity_stabilizes (ψ : CsSpinor) : Stabilizes identity ψ := by
  simp [Stabilizes]

/-- Determinant-one matrices stabilize `(1,0)` exactly when the first column is `(1,0)`. -/
theorem stabilizes_generic_iff (g : CsSL2) :
    Stabilizes g genericRep ↔ g.M.aa = Cs.one ∧ g.M.ba = Cs.zero := by
  simpa [Stabilizes, action, InfoGeometry.Algebra.KleinSpinorOrbit.Stabilizes]
    using InfoGeometry.Algebra.KleinSpinorOrbit.stabilizes_generic_iff g.M

/-- Determinant-one matrices stabilize `(E,0)` exactly by the two `E`-line equations. -/
theorem stabilizes_null_iff (g : CsSL2) :
    Stabilizes g nullRep ↔ Cs.mul g.M.aa Cs.E = Cs.E ∧ Cs.mul g.M.ba Cs.E = Cs.zero := by
  simpa [Stabilizes, action, InfoGeometry.Algebra.KleinSpinorOrbit.Stabilizes]
    using InfoGeometry.Algebra.KleinSpinorOrbit.stabilizes_null_iff g.M

/-- Determinant-one matrices stabilize `(E,E)` exactly by the two row-sum equations. -/
theorem stabilizes_diagonalNull_iff (g : CsSL2) :
    Stabilizes g diagonalNullRep ↔
      Cs.add (Cs.mul g.M.aa Cs.E) (Cs.mul g.M.ab Cs.E) = Cs.E ∧
      Cs.add (Cs.mul g.M.ba Cs.E) (Cs.mul g.M.bb Cs.E) = Cs.E := by
  simpa [Stabilizes, action, InfoGeometry.Algebra.KleinSpinorOrbit.Stabilizes]
    using InfoGeometry.Algebra.KleinSpinorOrbit.stabilizes_diagonalNull_iff g.M

/-- Eq.-5.22-style local content: the generic upper-unipotent family is determinant-one
and stabilizes the generic representative `(1,0)`. -/
theorem eq_5_22_generic_unipotent_stabilizes (b : Cs.Cs) :
    Stabilizes (genericUnipotent b) genericRep := by
  rw [stabilizes_generic_iff]
  simp [genericUnipotent, CsMatrix2.genericUnipotent]

lemma det_one_upper_triangular_bb_eq_one (ab bb : Cs.Cs)
    (hdet : CsMatrix2.DetOne ⟨Cs.one, ab, Cs.zero, bb⟩) : bb = Cs.one := by
  cases bb with
  | mk bre bim =>
    cases ab with
    | mk are aim =>
      apply Cs.ext
      · have hre := congrArg InfoGeometry.Clifford.Arxiv160309063.SplitC.re hdet
        norm_num [CsMatrix2.DetOne, CsMatrix2.det, Cs.add, Cs.mul, Cs.neg, Cs.one,
          Cs.zero, InfoGeometry.Clifford.Arxiv160309063.SplitC.add,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.neg,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.one,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar] at hre
        exact hre
      · have him := congrArg InfoGeometry.Clifford.Arxiv160309063.SplitC.im hdet
        norm_num [CsMatrix2.DetOne, CsMatrix2.det, Cs.add, Cs.mul, Cs.neg, Cs.one,
          Cs.zero, InfoGeometry.Clifford.Arxiv160309063.SplitC.add,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.mul,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.neg,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.one,
          InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar] at him
        exact him

/-- Determinant-one generic stabilizers are exactly upper unipotents in coordinates. -/
theorem eq_5_22_generic_stabilizer_shape (g : CsSL2) :
    Stabilizes g genericRep ↔ g.M = CsMatrix2.genericUnipotent g.M.ab := by
  constructor
  · intro hstab
    rcases (stabilizes_generic_iff g).mp hstab with ⟨haa, hba⟩
    cases g with
    | mk M hdet =>
      cases M with
      | mk aa ab ba bb =>
        dsimp at haa hba hdet ⊢
        subst aa
        subst ba
        have hbb : bb = Cs.one := det_one_upper_triangular_bb_eq_one ab bb hdet
        subst bb
        rfl
  · intro hshape
    change CsMatrix2.action g.M genericRep = genericRep
    rw [hshape]
    exact (InfoGeometry.Algebra.KleinSpinorOrbit.genericUnipotent_stabilizes g.M.ab).2

/-- Null stabilization by determinant-one matrices, reduced to two scalar row-sum equations
on the `E` line. -/
theorem eq_5_23_null_scalar_conditions (g : CsSL2) :
    Stabilizes g nullRep ↔ g.M.aa.re + g.M.aa.im = 1 ∧ g.M.ba.re + g.M.ba.im = 0 := by
  rw [stabilizes_null_iff]
  constructor
  · intro h
    exact ⟨(Cs.mul_E_eq_E_iff g.M.aa).mp h.1, (Cs.mul_E_eq_zero_iff g.M.ba).mp h.2⟩
  · intro h
    exact ⟨(Cs.mul_E_eq_E_iff g.M.aa).mpr h.1, (Cs.mul_E_eq_zero_iff g.M.ba).mpr h.2⟩

/-- Null stabilizers have first column on the affine/homogeneous `Ebar` lines.
This is a coordinate first-column shape theorem only; it does not identify the
full stabilizer as an abstract semidirect product. -/
theorem eq_5_23_null_first_column_Ebar_shape (g : CsSL2) :
    Stabilizes g nullRep ↔
      ∃ r s : ℚ,
        g.M.aa = Cs.add Cs.one (Cs.mul (Cs.scalar r) Cs.Ebar) ∧
        g.M.ba = Cs.mul (Cs.scalar s) Cs.Ebar := by
  rw [eq_5_23_null_scalar_conditions]
  constructor
  · intro h
    rcases (Cs.sum_eq_one_iff_exists_one_add_scalar_Ebar g.M.aa).mp h.1 with ⟨r, hr⟩
    rcases (Cs.sum_eq_zero_iff_exists_scalar_Ebar g.M.ba).mp h.2 with ⟨s, hs⟩
    exact ⟨r, s, hr, hs⟩
  · rintro ⟨r, s, hr, hs⟩
    constructor
    · exact (Cs.sum_eq_one_iff_exists_one_add_scalar_Ebar g.M.aa).mpr ⟨r, hr⟩
    · exact (Cs.sum_eq_zero_iff_exists_scalar_Ebar g.M.ba).mpr ⟨s, hs⟩

/-- Eq.-5.23-style local content: the `Ebar` lower family is determinant-one and
stabilizes the null representative `(E,0)`. -/
theorem eq_5_23_null_Ebar_family_stabilizes (t : ℚ) :
    Stabilizes (nullEbarFamily t) nullRep := by
  simpa [Stabilizes, action, nullEbarFamily]
    using InfoGeometry.Algebra.KleinSpinorOrbit.nullEbarFamily_stabilizes t

/-- Eq.-5.24-style local content: for the diagonal null representative `(E,E)`,
stabilization is the pair of row-sum equations on the `E` line. -/
theorem eq_5_24_diagonal_null_row_sum_iff (g : CsSL2) :
    Stabilizes g diagonalNullRep ↔
      Cs.add (Cs.mul g.M.aa Cs.E) (Cs.mul g.M.ab Cs.E) = Cs.E ∧
      Cs.add (Cs.mul g.M.ba Cs.E) (Cs.mul g.M.bb Cs.E) = Cs.E :=
  stabilizes_diagonalNull_iff g

end CsSL2

end InfoGeometry.Algebra.KleinSpinorOrbit
