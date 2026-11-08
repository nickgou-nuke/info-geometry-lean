import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Tactic
import InfoGeometry.Clifford.Tower

/-!
# A Grassmannian/exterior tower with a metric geometric product

The carrier is Mathlib's exterior algebra with its native natural grading and
wedge product. A quadratic form adds the Clifford geometric product through
Mathlib's characteristic-not-two module equivalence. Metric interior product
is transported from Mathlib's Clifford contraction. Wedge, contraction, and
geometric multiplication remain distinct operations.
-/

noncomputable section

namespace InfoGeometry.Algebra.SuperGrassmannianClifford

open scoped DirectSum

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- The full exterior carrier for the graded Grassmannian tower. -/
abbrev ExteriorTower (R : Type*) [CommRing R] (V : Type*)
    [AddCommGroup V] [Module R V] := ExteriorAlgebra R V

/-- Its degree-`d` homogeneous component. -/
abbrev ExteriorGrade (R : Type*) [CommRing R] (V : Type*)
    [AddCommGroup V] [Module R V] (d : ℕ) := ⋀[R]^d V

/-- Parity of an exterior degree, giving the induced supergrading index. -/
def gradeParity (d : ℕ) : ZMod 2 := d

theorem gradeParity_add (i j : ℕ) :
    gradeParity (i + j) = gradeParity i + gradeParity j := by
  simp [gradeParity, Nat.cast_add]

/-- The exterior multiplication, i.e. the outer/wedge product. -/
def outerProduct (x y : ExteriorTower R V) : ExteriorTower R V := x * y

/-- The symmetric scalar product associated to a quadratic form. -/
def metricInner (Q : QuadraticForm R V) (v w : V) : R :=
  QuadraticMap.associated Q v w

/-- The module equivalence from the Clifford geometric algebra to its exterior
model; it identifies carriers, not products. -/
def cliffordExteriorEquiv (Q : QuadraticForm R V) :
    CliffordAlgebra Q ≃ₗ[R] ExteriorTower R V :=
  CliffordAlgebra.equivExterior Q

/-- The even/odd supergrading transported from Mathlib's Clifford algebra to
its exterior carrier. -/
def superGrade (Q : QuadraticForm R V) (p : ZMod 2) :
    Submodule R (ExteriorTower R V) :=
  (CliffordAlgebra.evenOdd Q p).comap (cliffordExteriorEquiv Q).symm.toLinearMap

/-- The transported even and odd components are complementary subspaces of
the exterior carrier. -/
theorem superGrade_isCompl (Q : QuadraticForm R V) :
    IsCompl (superGrade Q 0) (superGrade Q 1) := by
  simpa [superGrade, Submodule.map_equiv_eq_comap_symm] using
    (Submodule.orderIsoMapComap (cliffordExteriorEquiv Q)).isCompl
      (CliffordAlgebra.evenOdd_isCompl Q)

/-- The generalized geometric product on the exterior carrier, transported
from the Clifford algebra of `Q`. -/
def geometricProduct (Q : QuadraticForm R V) (x y : ExteriorTower R V) :
    ExteriorTower R V :=
  cliffordExteriorEquiv Q
    ((cliffordExteriorEquiv Q).symm x * (cliffordExteriorEquiv Q).symm y)

/-- Left metric contraction by a vector, transported from Mathlib's native
Clifford contraction by the associated covector. -/
def interiorProduct (Q : QuadraticForm R V) (v : V) (x : ExteriorTower R V) :
    ExteriorTower R V :=
  cliffordExteriorEquiv Q
    (CliffordAlgebra.contractLeft (QuadraticMap.associated Q v)
      ((cliffordExteriorEquiv Q).symm x))

omit [Invertible (2 : R)] in
theorem exteriorGrade_outerProduct_mem {i j : ℕ}
    (x : ExteriorGrade R V i) (y : ExteriorGrade R V j) :
    outerProduct x.val y.val ∈ ExteriorGrade R V (i + j) := by
  exact SetLike.GradedMonoid.toGradedMul.mul_mem x.property y.property

omit [Invertible (2 : R)] in
/-- Homogeneous exterior grades commute with the Koszul sign.  The proof
extends Mathlib's generator-level `ιMulti_mul_ιMulti_anticomm` identity from
decomposable generators to the full homogeneous submodules. -/
theorem exteriorGrade_mul_koszul
    (i j : ℕ) {x y : ExteriorTower R V}
    (hx : x ∈ ExteriorGrade R V i) (hy : y ∈ ExteriorGrade R V j) :
    outerProduct x y = ((-1 : ℤˣ) ^ (j * i)) • outerProduct y x := by
  have hspan_i : ExteriorGrade R V i =
      Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R i :
        (Fin i → V) → ExteriorTower R V)) := by
    simpa [ExteriorGrade, ExteriorTower] using
      (ExteriorAlgebra.ιMulti_span_fixedDegree (R := R) (M := V) i).symm
  have hspan_j : ExteriorGrade R V j =
      Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R j :
        (Fin j → V) → ExteriorTower R V)) := by
    simpa [ExteriorGrade, ExteriorTower] using
      (ExteriorAlgebra.ιMulti_span_fixedDegree (R := R) (M := V) j).symm
  have hy' : y ∈ Submodule.span R
      (Set.range (ExteriorAlgebra.ιMulti R j :
        (Fin j → V) → ExteriorTower R V)) := by
    rw [← hspan_j]
    exact hy
  have hgen : ∀ u : Fin i → V,
      ∀ z ∈ Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R j :
        (Fin j → V) → ExteriorTower R V)),
        outerProduct (ExteriorAlgebra.ιMulti R i u) z =
          ((-1 : ℤˣ) ^ (j * i)) •
            outerProduct z (ExteriorAlgebra.ιMulti R i u) := by
    intro u z hz
    refine Submodule.span_induction
      (p := fun z _ => outerProduct (ExteriorAlgebra.ιMulti R i u) z =
        ((-1 : ℤˣ) ^ (j * i)) •
          outerProduct z (ExteriorAlgebra.ιMulti R i u)) ?_ ?_ ?_ ?_ hz
    · intro z hz
      rcases hz with ⟨v, rfl⟩
      simpa [outerProduct, Nat.mul_comm] using
        (ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm
          (R := R) u v)
    · simp [outerProduct]
    · intro z₁ z₂ _ _ hz₁ hz₂
      change ExteriorAlgebra.ιMulti R i u * (z₁ + z₂) =
        ((-1 : ℤˣ) ^ (j * i)) • ((z₁ + z₂) * ExteriorAlgebra.ιMulti R i u)
      change ExteriorAlgebra.ιMulti R i u * z₁ =
        ((-1 : ℤˣ) ^ (j * i)) • (z₁ * ExteriorAlgebra.ιMulti R i u) at hz₁
      change ExteriorAlgebra.ιMulti R i u * z₂ =
        ((-1 : ℤˣ) ^ (j * i)) • (z₂ * ExteriorAlgebra.ιMulti R i u) at hz₂
      rw [mul_add, hz₁, hz₂, add_mul, smul_add]
    · intro c z _ hz
      calc
        outerProduct (ExteriorAlgebra.ιMulti R i u) (c • z) =
            c • outerProduct (ExteriorAlgebra.ιMulti R i u) z := by
              simp [outerProduct]
        _ = c • (((-1 : ℤˣ) ^ (j * i)) •
              outerProduct z (ExteriorAlgebra.ιMulti R i u)) := by rw [hz]
        _ = ((-1 : ℤˣ) ^ (j * i)) •
              (c • outerProduct z (ExteriorAlgebra.ιMulti R i u)) := by
                rw [smul_comm]
        _ = ((-1 : ℤˣ) ^ (j * i)) •
              outerProduct (c • z) (ExteriorAlgebra.ιMulti R i u) := by
                simp [outerProduct]
  have hx' : x ∈ Submodule.span R
      (Set.range (ExteriorAlgebra.ιMulti R i :
        (Fin i → V) → ExteriorTower R V)) := by
    rw [← hspan_i]
    exact hx
  refine Submodule.span_induction
    (p := fun x _ => outerProduct x y =
      ((-1 : ℤˣ) ^ (j * i)) • outerProduct y x) ?_ ?_ ?_ ?_ hx'
  · intro x hx
    rcases hx with ⟨u, rfl⟩
    exact hgen u y hy'
  · simp [outerProduct]
  · intro x₁ x₂ _ _ hx₁ hx₂
    change (x₁ + x₂) * y =
      ((-1 : ℤˣ) ^ (j * i)) • (y * (x₁ + x₂))
    change x₁ * y = ((-1 : ℤˣ) ^ (j * i)) • (y * x₁) at hx₁
    change x₂ * y = ((-1 : ℤˣ) ^ (j * i)) • (y * x₂) at hx₂
    rw [add_mul, hx₁, hx₂, mul_add, smul_add]
  · intro c x _ hx
    calc
      outerProduct (c • x) y = c • outerProduct x y := by
        simp [outerProduct]
      _ = c • (((-1 : ℤˣ) ^ (j * i)) • outerProduct y x) := by rw [hx]
      _ = ((-1 : ℤˣ) ^ (j * i)) •
            (c • outerProduct y x) := by rw [smul_comm]
      _ = ((-1 : ℤˣ) ^ (j * i)) • outerProduct y (c • x) := by
            simp [outerProduct]

@[simp] theorem geometricProduct_toClifford (Q : QuadraticForm R V)
    (x y : ExteriorTower R V) :
    (cliffordExteriorEquiv Q).symm (geometricProduct Q x y) =
      (cliffordExteriorEquiv Q).symm x * (cliffordExteriorEquiv Q).symm y := by
  simp [geometricProduct]

theorem geometricProduct_assoc (Q : QuadraticForm R V)
    (x y z : ExteriorTower R V) :
    geometricProduct Q (geometricProduct Q x y) z =
      geometricProduct Q x (geometricProduct Q y z) := by
  apply (cliffordExteriorEquiv Q).symm.injective
  calc
    (cliffordExteriorEquiv Q).symm (geometricProduct Q (geometricProduct Q x y) z) =
        (cliffordExteriorEquiv Q).symm (geometricProduct Q x y) *
          (cliffordExteriorEquiv Q).symm z := geometricProduct_toClifford Q _ _
    _ = ((cliffordExteriorEquiv Q).symm x * (cliffordExteriorEquiv Q).symm y) *
        (cliffordExteriorEquiv Q).symm z := by rw [geometricProduct_toClifford]
    _ = (cliffordExteriorEquiv Q).symm x *
        ((cliffordExteriorEquiv Q).symm y * (cliffordExteriorEquiv Q).symm z) := by
          rw [mul_assoc]
    _ = (cliffordExteriorEquiv Q).symm x *
        (cliffordExteriorEquiv Q).symm (geometricProduct Q y z) := by
          rw [geometricProduct_toClifford]
    _ = (cliffordExteriorEquiv Q).symm
        (geometricProduct Q x (geometricProduct Q y z)) :=
          (geometricProduct_toClifford Q _ _).symm

theorem geometricProduct_preserves_superGrade
    (Q : QuadraticForm R V) (p q : ZMod 2)
    {x y : ExteriorTower R V}
    (hx : x ∈ superGrade Q p) (hy : y ∈ superGrade Q q) :
    geometricProduct Q x y ∈ superGrade Q (p + q) := by
  change (cliffordExteriorEquiv Q).symm x ∈ CliffordAlgebra.evenOdd Q p at hx
  change (cliffordExteriorEquiv Q).symm y ∈ CliffordAlgebra.evenOdd Q q at hy
  change (cliffordExteriorEquiv Q).symm (geometricProduct Q x y) ∈
    CliffordAlgebra.evenOdd Q (p + q)
  rw [geometricProduct_toClifford]
  exact SetLike.GradedMonoid.toGradedMul.mul_mem hx hy

theorem exteriorGenerator_mem_superGrade_one
    (Q : QuadraticForm R V) (v : V) :
    ExteriorAlgebra.ι R v ∈ superGrade Q (1 : ZMod 2) := by
  change (cliffordExteriorEquiv Q).symm (ExteriorAlgebra.ι R v) ∈
    CliffordAlgebra.evenOdd Q 1
  have hgen : (cliffordExteriorEquiv Q).symm (ExteriorAlgebra.ι R v) =
      CliffordAlgebra.ι Q v := by
    apply (cliffordExteriorEquiv Q).injective
    simp [cliffordExteriorEquiv]
  rw [hgen]
  exact CliffordAlgebra.ι_mem_evenOdd_one Q v

omit [Invertible (2 : R)] in
theorem contractLeft_even_to_odd (Q : QuadraticForm R V) (d : Module.Dual R V)
    {x : CliffordAlgebra Q} (hx : x ∈ CliffordAlgebra.evenOdd Q 0) :
    CliffordAlgebra.contractLeft d x ∈ CliffordAlgebra.evenOdd Q 1 := by
  refine CliffordAlgebra.even_induction (Q := Q)
    (motive := fun x _ => CliffordAlgebra.contractLeft d x ∈ CliffordAlgebra.evenOdd Q 1)
    ?_ ?_ ?_ x hx
  · intro r
    simp
  · intro x y hx hy ihx ihy
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  · intro a b x hx ih
    have hbx : CliffordAlgebra.ι Q b * x ∈ CliffordAlgebra.evenOdd Q 1 := by
      apply CliffordAlgebra.evenOdd_mul_le Q 1 0
      exact Submodule.mul_mem_mul (CliffordAlgebra.ι_mem_evenOdd_one Q b) hx
    have hax : CliffordAlgebra.ι Q a * x ∈ CliffordAlgebra.evenOdd Q 1 := by
      apply CliffordAlgebra.evenOdd_mul_le Q 1 0
      exact Submodule.mul_mem_mul (CliffordAlgebra.ι_mem_evenOdd_one Q a) hx
    have hpair : CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b ∈
        CliffordAlgebra.evenOdd Q 0 :=
      CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q a b
    have htriple : CliffordAlgebra.ι Q a *
        (CliffordAlgebra.ι Q b * CliffordAlgebra.contractLeft d x) ∈
          CliffordAlgebra.evenOdd Q 1 := by
      have hprod : (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) *
          CliffordAlgebra.contractLeft d x ∈
            CliffordAlgebra.evenOdd Q 0 * CliffordAlgebra.evenOdd Q 1 :=
        Submodule.mul_mem_mul hpair ih
      have h := (CliffordAlgebra.evenOdd_mul_le Q 0 1) hprod
      simpa [mul_assoc] using h
    have hfirst : d a • (CliffordAlgebra.ι Q b * x) ∈
        CliffordAlgebra.evenOdd Q 1 := Submodule.smul_mem _ _ hbx
    have hsecond : CliffordAlgebra.ι Q a * (d b • x) ∈
        CliffordAlgebra.evenOdd Q 1 := by
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ hax
    rw [mul_assoc]
    rw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul]
    have hsum :
        d a • (CliffordAlgebra.ι Q b * x) - CliffordAlgebra.ι Q a * (d b • x) +
          CliffordAlgebra.ι Q a * (CliffordAlgebra.ι Q b *
            CliffordAlgebra.contractLeft d x) ∈ CliffordAlgebra.evenOdd Q 1 := by
      exact Submodule.add_mem _ (Submodule.sub_mem _ hfirst hsecond) htriple
    have hEq :
        d a • (CliffordAlgebra.ι Q b * x) - CliffordAlgebra.ι Q a *
            (d b • x - CliffordAlgebra.ι Q b * CliffordAlgebra.contractLeft d x) =
          d a • (CliffordAlgebra.ι Q b * x) - CliffordAlgebra.ι Q a * (d b • x) +
            CliffordAlgebra.ι Q a * (CliffordAlgebra.ι Q b *
              CliffordAlgebra.contractLeft d x) := by
      rw [mul_sub]
      abel
    rw [hEq]
    exact hsum

omit [Invertible (2 : R)] in
theorem contractLeft_odd_to_even (Q : QuadraticForm R V) (d : Module.Dual R V)
    {x : CliffordAlgebra Q} (hx : x ∈ CliffordAlgebra.evenOdd Q 1) :
    CliffordAlgebra.contractLeft d x ∈ CliffordAlgebra.evenOdd Q 0 := by
  refine CliffordAlgebra.odd_induction (Q := Q)
    (P := fun x _ => CliffordAlgebra.contractLeft d x ∈ CliffordAlgebra.evenOdd Q 0)
    ?_ ?_ ?_ x hx
  · intro v
    rw [CliffordAlgebra.contractLeft_ι]
    have hone : (1 : CliffordAlgebra Q) ∈ CliffordAlgebra.evenOdd Q 0 :=
      Submodule.one_le.mp (CliffordAlgebra.one_le_evenOdd_zero Q)
    simpa [Algebra.algebraMap_eq_smul_one] using
      Submodule.smul_mem (CliffordAlgebra.evenOdd Q 0) (d v) hone
  · intro x y hx hy ihx ihy
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  · intro a b x hx ih
    have hbx : CliffordAlgebra.ι Q b * x ∈ CliffordAlgebra.evenOdd Q 0 := by
      apply CliffordAlgebra.evenOdd_mul_le Q 1 1
      exact Submodule.mul_mem_mul (CliffordAlgebra.ι_mem_evenOdd_one Q b) hx
    have hax : CliffordAlgebra.ι Q a * x ∈ CliffordAlgebra.evenOdd Q 0 := by
      apply CliffordAlgebra.evenOdd_mul_le Q 1 1
      exact Submodule.mul_mem_mul (CliffordAlgebra.ι_mem_evenOdd_one Q a) hx
    have hpair : CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b ∈
        CliffordAlgebra.evenOdd Q 0 :=
      CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q a b
    have htriple : CliffordAlgebra.ι Q a *
        (CliffordAlgebra.ι Q b * CliffordAlgebra.contractLeft d x) ∈
          CliffordAlgebra.evenOdd Q 0 := by
      have hprod : (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) *
          CliffordAlgebra.contractLeft d x ∈
            CliffordAlgebra.evenOdd Q 0 * CliffordAlgebra.evenOdd Q 0 :=
        Submodule.mul_mem_mul hpair ih
      have h := (CliffordAlgebra.evenOdd_mul_le Q 0 0) hprod
      simpa [mul_assoc] using h
    have hfirst : d a • (CliffordAlgebra.ι Q b * x) ∈
        CliffordAlgebra.evenOdd Q 0 := Submodule.smul_mem _ _ hbx
    have hsecond : CliffordAlgebra.ι Q a * (d b • x) ∈
        CliffordAlgebra.evenOdd Q 0 := by
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ hax
    rw [mul_assoc]
    rw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul]
    have hsum :
        d a • (CliffordAlgebra.ι Q b * x) - CliffordAlgebra.ι Q a * (d b • x) +
          CliffordAlgebra.ι Q a * (CliffordAlgebra.ι Q b *
            CliffordAlgebra.contractLeft d x) ∈ CliffordAlgebra.evenOdd Q 0 := by
      exact Submodule.add_mem _ (Submodule.sub_mem _ hfirst hsecond) htriple
    have hEq :
        d a • (CliffordAlgebra.ι Q b * x) - CliffordAlgebra.ι Q a *
            (d b • x - CliffordAlgebra.ι Q b * CliffordAlgebra.contractLeft d x) =
          d a • (CliffordAlgebra.ι Q b * x) - CliffordAlgebra.ι Q a * (d b • x) +
            CliffordAlgebra.ι Q a * (CliffordAlgebra.ι Q b *
              CliffordAlgebra.contractLeft d x) := by
      rw [mul_sub]
      abel
    rw [hEq]
    exact hsum

omit [Invertible (2 : R)] in
theorem contractLeft_parity (Q : QuadraticForm R V) (d : Module.Dual R V)
    (p : ZMod 2) {x : CliffordAlgebra Q}
    (hx : x ∈ CliffordAlgebra.evenOdd Q p) :
    CliffordAlgebra.contractLeft d x ∈ CliffordAlgebra.evenOdd Q (p + 1) := by
  classical
  have hp : p = 0 ∨ p = 1 := by
    fin_cases p
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hp with hp | hp
  · subst p
    simpa using contractLeft_even_to_odd Q d hx
  · subst p
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rw [h11]
    exact contractLeft_odd_to_even Q d hx

theorem cliffordExteriorEquiv_symm_ι_mul (Q : QuadraticForm R V) (v : V)
    (x : ExteriorTower R V) :
    (cliffordExteriorEquiv Q).symm (ExteriorAlgebra.ι R v * x) =
      CliffordAlgebra.ι Q v * (cliffordExteriorEquiv Q).symm x -
        CliffordAlgebra.contractLeft (QuadraticMap.associated Q v)
          ((cliffordExteriorEquiv Q).symm x) := by
  simp [cliffordExteriorEquiv, CliffordAlgebra.equivExterior,
    CliffordAlgebra.changeFormEquiv, CliffordAlgebra.changeForm_ι_mul]

theorem exteriorBlade_mem_superGrade (Q : QuadraticForm R V)
    (d : ℕ) (v : Fin d → V) :
    (cliffordExteriorEquiv Q).symm (ExteriorAlgebra.ιMulti R d v) ∈
      CliffordAlgebra.evenOdd Q (d : ZMod 2) := by
  induction d with
  | zero =>
      rw [ExteriorAlgebra.ιMulti_zero_apply]
      simpa [cliffordExteriorEquiv] using
        Submodule.one_le.mp (CliffordAlgebra.one_le_evenOdd_zero Q)
  | succ d ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, cliffordExteriorEquiv_symm_ι_mul]
      have htail := ih (Matrix.vecTail v)
      have hleft : CliffordAlgebra.ι Q (v 0) *
          (cliffordExteriorEquiv Q).symm (ExteriorAlgebra.ιMulti R d (Matrix.vecTail v)) ∈
            CliffordAlgebra.evenOdd Q ((d + 1 : ℕ) : ZMod 2) := by
        have hprod : CliffordAlgebra.ι Q (v 0) *
            (cliffordExteriorEquiv Q).symm (ExteriorAlgebra.ιMulti R d (Matrix.vecTail v)) ∈
              CliffordAlgebra.evenOdd Q 1 * CliffordAlgebra.evenOdd Q (d : ZMod 2) :=
          Submodule.mul_mem_mul (CliffordAlgebra.ι_mem_evenOdd_one Q (v 0)) htail
        simpa [Nat.cast_succ, add_comm] using
          (CliffordAlgebra.evenOdd_mul_le Q 1 (d : ZMod 2)) hprod
      have hright := contractLeft_parity Q
        (QuadraticMap.associated Q (v 0)) (d : ZMod 2) htail
      have hright' : CliffordAlgebra.contractLeft (QuadraticMap.associated Q (v 0))
          ((cliffordExteriorEquiv Q).symm (ExteriorAlgebra.ιMulti R d (Matrix.vecTail v))) ∈
            CliffordAlgebra.evenOdd Q ((d + 1 : ℕ) : ZMod 2) := by
        simpa [Nat.cast_succ] using hright
      exact Submodule.sub_mem _ hleft hright'

theorem exteriorGrade_mem_superGrade (Q : QuadraticForm R V)
    (d : ℕ) {x : ExteriorTower R V} (hx : x ∈ ExteriorGrade R V d) :
    x ∈ superGrade Q (gradeParity d) := by
  change (cliffordExteriorEquiv Q).symm.toLinearMap x ∈
    CliffordAlgebra.evenOdd Q (d : ZMod 2)
  have hspan : ExteriorGrade R V d = Submodule.span R
      (Set.range (ExteriorAlgebra.ιMulti R d : (Fin d → V) → ExteriorTower R V)) := by
    simpa [ExteriorGrade, ExteriorTower] using
      (ExteriorAlgebra.ιMulti_span_fixedDegree (R := R) (M := V) d).symm
  have hmap : (ExteriorGrade R V d).map (cliffordExteriorEquiv Q).symm.toLinearMap ≤
      CliffordAlgebra.evenOdd Q (d : ZMod 2) := by
    rw [hspan, Submodule.map_span]
    apply Submodule.span_le.2
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨w, rfl⟩ := hv
    exact exteriorBlade_mem_superGrade Q d w
  exact hmap (Submodule.mem_map_of_mem hx)

@[simp] theorem interiorProduct_generator (Q : QuadraticForm R V) (v w : V) :
    interiorProduct Q v (ExteriorAlgebra.ι R w) =
      algebraMap R (ExteriorTower R V) (metricInner Q v w) := by
  have hgen : (cliffordExteriorEquiv Q).symm (ExteriorAlgebra.ι R w) =
      CliffordAlgebra.ι Q w := by
    apply (cliffordExteriorEquiv Q).injective
    simp [cliffordExteriorEquiv]
  rw [interiorProduct, hgen]
  simp [metricInner, cliffordExteriorEquiv]

theorem geometricProduct_vector_decomposition (Q : QuadraticForm R V)
    (v w : V) :
    geometricProduct Q (ExteriorAlgebra.ι R v) (ExteriorAlgebra.ι R w) =
      algebraMap R (ExteriorTower R V) (metricInner Q v w) +
        outerProduct (ExteriorAlgebra.ι R v) (ExteriorAlgebra.ι R w) := by
  have hv : (cliffordExteriorEquiv Q).symm (ExteriorAlgebra.ι R v) =
      CliffordAlgebra.ι Q v := by
    apply (cliffordExteriorEquiv Q).injective
    simp [cliffordExteriorEquiv]
  have hw : (cliffordExteriorEquiv Q).symm (ExteriorAlgebra.ι R w) =
      CliffordAlgebra.ι Q w := by
    apply (cliffordExteriorEquiv Q).injective
    simp [cliffordExteriorEquiv]
  rw [geometricProduct, hv, hw]
  simp [cliffordExteriorEquiv, CliffordAlgebra.equivExterior,
    CliffordAlgebra.changeFormEquiv, CliffordAlgebra.changeForm_ι_mul_ι,
    metricInner, outerProduct] ; abel

theorem metricInner_symmetric (Q : QuadraticForm R V) (v w : V) :
    metricInner Q v w = metricInner Q w v := by
  exact QuadraticMap.associated_isSymm (S := R) Q v w

omit [Invertible (2 : R)] in
theorem outerProduct_vectors_anticommute (v w : V) :
    outerProduct (ExteriorAlgebra.ι R v) (ExteriorAlgebra.ι R w) =
      -outerProduct (ExteriorAlgebra.ι R w) (ExteriorAlgebra.ι R v) := by
  have hv : ExteriorAlgebra.ι R v ∈ ExteriorGrade R V 1 := by
    simpa only [pow_one] using
      (LinearMap.mem_range_self (ExteriorAlgebra.ι R :
        V →ₗ[R] ExteriorTower R V) v)
  have hw : ExteriorAlgebra.ι R w ∈ ExteriorGrade R V 1 := by
    simpa only [pow_one] using
      (LinearMap.mem_range_self (ExteriorAlgebra.ι R :
        V →ₗ[R] ExteriorTower R V) w)
  simpa [outerProduct] using exteriorGrade_mul_koszul 1 1 hv hw

theorem geometricProduct_vector_square (Q : QuadraticForm R V) (v : V) :
    geometricProduct Q (ExteriorAlgebra.ι R v) (ExteriorAlgebra.ι R v) =
      algebraMap R (ExteriorTower R V) (Q v) := by
  rw [geometricProduct_vector_decomposition]
  simp [outerProduct, metricInner, QuadraticMap.associated_eq_self_apply]

/-! ## A stage-indexed split super-Grassmannian tower -/

local instance splitTwoInvertible : Invertible (2 : ℝ) :=
  invertibleOfNonzero (by norm_num)

abbrev SplitExteriorStage (n : ℕ) :=
  ExteriorAlgebra ℝ (InfoGeometry.CliffordTower.SplitSpace n)

/-- Embed stage `n` as the second summand at stage `n+1`. -/
def splitStageVectorInclude (n : ℕ) :
    InfoGeometry.CliffordTower.SplitSpace n →ₗ[ℝ]
      InfoGeometry.CliffordTower.SplitSpace (n + 1) where
  toFun x := (0, x)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- The stage inclusion preserves the recursive split quadratic form. -/
def splitStageIsometry (n : ℕ) :
    InfoGeometry.CliffordTower.Qsplit n →qᵢ
      InfoGeometry.CliffordTower.Qsplit (n + 1) where
  __ := splitStageVectorInclude n
  map_app' x := by
    change InfoGeometry.CliffordTower.Q11 0 +
      InfoGeometry.CliffordTower.Qsplit n x = InfoGeometry.CliffordTower.Qsplit n x
    simp

@[simp] theorem splitStageIsometry_apply (n : ℕ)
    (x : InfoGeometry.CliffordTower.SplitSpace n) :
    splitStageIsometry n x = splitStageVectorInclude n x := rfl

/-- Clifford algebra homomorphism induced by the isometric stage inclusion. -/
def splitStageCliffordMap (n : ℕ) :
    InfoGeometry.CliffordTower.Clsplit n →ₐ[ℝ]
      InfoGeometry.CliffordTower.Clsplit (n + 1) :=
  CliffordAlgebra.map (splitStageIsometry n)

/-- The Clifford map induced by a stage inclusion preserves each even/odd
component. This follows from its action on the generating vector range, which
is the construction from which Mathlib's `evenOdd` components are generated. -/
theorem splitStageCliffordMap_preserves_evenOdd (n : ℕ) (p : ZMod 2) :
    (CliffordAlgebra.evenOdd (InfoGeometry.CliffordTower.Qsplit n) p).map
        (splitStageCliffordMap n).toLinearMap ≤
      CliffordAlgebra.evenOdd (InfoGeometry.CliffordTower.Qsplit (n + 1)) p := by
  rw [CliffordAlgebra.evenOdd, Submodule.map_iSup]
  apply iSup_le
  intro d
  rw [Submodule.map_pow]
  simp only [splitStageCliffordMap, CliffordAlgebra.ι_range_map_map]
  have h_range :
      (splitStageIsometry n).range.map
          (CliffordAlgebra.ι (InfoGeometry.CliffordTower.Qsplit (n + 1))) ≤
        LinearMap.range
          (CliffordAlgebra.ι (InfoGeometry.CliffordTower.Qsplit (n + 1))) := by
    calc
      (splitStageIsometry n).range.map
          (CliffordAlgebra.ι (InfoGeometry.CliffordTower.Qsplit (n + 1))) ≤
        (⊤ : Submodule ℝ (InfoGeometry.CliffordTower.SplitSpace (n + 1))).map
          (CliffordAlgebra.ι (InfoGeometry.CliffordTower.Qsplit (n + 1))) :=
            Submodule.map_mono le_top
      _ = LinearMap.range
          (CliffordAlgebra.ι (InfoGeometry.CliffordTower.Qsplit (n + 1))) := by
            simp
  have h_pow : ∀ k : ℕ,
      ((splitStageIsometry n).range.map
          (CliffordAlgebra.ι (InfoGeometry.CliffordTower.Qsplit (n + 1)))) ^ k ≤
        (LinearMap.range
          (CliffordAlgebra.ι (InfoGeometry.CliffordTower.Qsplit (n + 1)))) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', pow_succ']
      exact Submodule.smul_mono h_range ih
  calc
    ((splitStageIsometry n).range.map
        (CliffordAlgebra.ι (InfoGeometry.CliffordTower.Qsplit (n + 1)))) ^ (d : ℕ) ≤
      (LinearMap.range
        (CliffordAlgebra.ι (InfoGeometry.CliffordTower.Qsplit (n + 1)))) ^ (d : ℕ) :=
          h_pow (d : ℕ)
    _ ≤ CliffordAlgebra.evenOdd
        (InfoGeometry.CliffordTower.Qsplit (n + 1)) p := by
          exact le_iSup_of_le ⟨d, d.property⟩ le_rfl

/-- The corresponding map of exterior carriers, transported through the
canonical Clifford/exterior module equivalences. -/
noncomputable def splitStageExteriorMap (n : ℕ) :
    SplitExteriorStage n →ₗ[ℝ] SplitExteriorStage (n + 1) :=
  (cliffordExteriorEquiv (InfoGeometry.CliffordTower.Qsplit (n + 1))).toLinearMap.comp
    ((splitStageCliffordMap n).toLinearMap.comp
      (cliffordExteriorEquiv (InfoGeometry.CliffordTower.Qsplit n)).symm.toLinearMap)

/-- Native exterior-algebra stage map, preserving the outer product. -/
noncomputable def splitStageWedgeMap (n : ℕ) :
    SplitExteriorStage n →ₐ[ℝ] SplitExteriorStage (n + 1) :=
  ExteriorAlgebra.map (splitStageVectorInclude n)

@[simp] theorem splitStageWedgeMap_generator (n : ℕ)
    (v : InfoGeometry.CliffordTower.SplitSpace n) :
    splitStageWedgeMap n (ExteriorAlgebra.ι ℝ v) =
      ExteriorAlgebra.ι ℝ (splitStageVectorInclude n v) := by
  simp [splitStageWedgeMap]

theorem splitStageWedgeMap_outerProduct (n : ℕ)
    (x y : SplitExteriorStage n) :
    splitStageWedgeMap n (outerProduct x y) =
      outerProduct (splitStageWedgeMap n x) (splitStageWedgeMap n y) := by
  exact (splitStageWedgeMap n).map_mul x y

theorem splitStage_metricInner (n : ℕ)
    (v w : InfoGeometry.CliffordTower.SplitSpace n) :
    metricInner (InfoGeometry.CliffordTower.Qsplit (n + 1))
      (splitStageVectorInclude n v) (splitStageVectorInclude n w) =
      metricInner (InfoGeometry.CliffordTower.Qsplit n) v w := by
  have hQ : (InfoGeometry.CliffordTower.Qsplit (n + 1)).comp
      (splitStageVectorInclude n) = InfoGeometry.CliffordTower.Qsplit n := by
    apply QuadraticMap.ext
    intro x
    change InfoGeometry.CliffordTower.Qsplit (n + 1) (0, x) =
      InfoGeometry.CliffordTower.Qsplit n x
    rw [InfoGeometry.CliffordTower.Qsplit_succ_apply]
    simp
  rw [← hQ]
  simp [metricInner, QuadraticMap.associated_comp]

@[simp] theorem splitStageExteriorMap_scalar (n : ℕ) (r : ℝ) :
    splitStageExteriorMap n (algebraMap ℝ (SplitExteriorStage n) r) =
      algebraMap ℝ (SplitExteriorStage (n + 1)) r := by
  simp [splitStageExteriorMap, splitStageCliffordMap, cliffordExteriorEquiv]

theorem splitStageExteriorMap_interiorProduct_generator (n : ℕ)
    (v w : InfoGeometry.CliffordTower.SplitSpace n) :
    splitStageExteriorMap n
      (interiorProduct (InfoGeometry.CliffordTower.Qsplit n) v (ExteriorAlgebra.ι ℝ w)) =
      interiorProduct (InfoGeometry.CliffordTower.Qsplit (n + 1))
        (splitStageVectorInclude n v) (ExteriorAlgebra.ι ℝ (splitStageVectorInclude n w)) := by
  rw [interiorProduct_generator, splitStageExteriorMap_scalar,
    interiorProduct_generator, splitStage_metricInner]

@[simp] theorem splitStageExteriorMap_generator (n : ℕ)
    (v : InfoGeometry.CliffordTower.SplitSpace n) :
    splitStageExteriorMap n (ExteriorAlgebra.ι ℝ v) =
      ExteriorAlgebra.ι ℝ (splitStageVectorInclude n v) := by
  simp [splitStageExteriorMap, splitStageCliffordMap, splitStageVectorInclude,
    cliffordExteriorEquiv]
  change splitStageIsometry n v = (0, v)
  rw [splitStageIsometry_apply, splitStageVectorInclude]
  rfl

theorem splitStageExteriorMap_geometricProduct (n : ℕ)
    (x y : SplitExteriorStage n) :
    splitStageExteriorMap n (geometricProduct (InfoGeometry.CliffordTower.Qsplit n) x y) =
      geometricProduct (InfoGeometry.CliffordTower.Qsplit (n + 1))
        (splitStageExteriorMap n x) (splitStageExteriorMap n y) := by
  simp [splitStageExteriorMap, splitStageCliffordMap, geometricProduct]

/-- The exterior-stage map preserves the transported even and odd components. -/
theorem splitStageExteriorMap_preserves_superGrade (n : ℕ) (p : ZMod 2)
    {x : SplitExteriorStage n} (hx : x ∈ superGrade
      (InfoGeometry.CliffordTower.Qsplit n) p) :
    splitStageExteriorMap n x ∈ superGrade
      (InfoGeometry.CliffordTower.Qsplit (n + 1)) p := by
  change (cliffordExteriorEquiv (InfoGeometry.CliffordTower.Qsplit n)).symm x ∈
    CliffordAlgebra.evenOdd (InfoGeometry.CliffordTower.Qsplit n) p at hx
  have hmap : splitStageCliffordMap n
      ((cliffordExteriorEquiv (InfoGeometry.CliffordTower.Qsplit n)).symm x) ∈
      CliffordAlgebra.evenOdd (InfoGeometry.CliffordTower.Qsplit (n + 1)) p :=
    splitStageCliffordMap_preserves_evenOdd n p (Submodule.mem_map_of_mem hx)
  change (cliffordExteriorEquiv (InfoGeometry.CliffordTower.Qsplit (n + 1))).symm
      (splitStageExteriorMap n x) ∈
    CliffordAlgebra.evenOdd (InfoGeometry.CliffordTower.Qsplit (n + 1)) p
  simpa [splitStageExteriorMap, splitStageCliffordMap] using hmap

end InfoGeometry.Algebra.SuperGrassmannianClifford
