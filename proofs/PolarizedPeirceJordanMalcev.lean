import proofs.OneSheetChiralAlgebra

/-!
# Polarized Peirce sheet and Jordan--Malcev separation

This owner distinguishes three objects which share basis labels but have
different operations: the positive Peirce polarization, the opposite Zorn
lane, and the dual middle argument of the rank-one Jordan pair.
-/

noncomputable section

namespace PolarizedPeirceJordanMalcev

open SplitOctonionChiralClosure

abbrev Zorn := SplitOctonionChiralClosure.Zorn
abbrev Vec3 := SplitOctonionChiralClosure.Vec3

def jordan := OneSheetChiralAlgebra.jordan
def assoc := OneSheetChiralAlgebra.assoc

/-- Tagged coordinates of the positive polarized Peirce sheet. -/
structure PlusSheet where
  scalar : ℂ
  vector : Vec3

/-- Tagged coordinates of its chosen dual/opposite polarization. -/
structure MinusSheet where
  scalar : ℂ
  vector : Vec3

@[ext] theorem PlusSheet.ext {x y : PlusSheet}
    (hs : x.scalar = y.scalar) (hv : x.vector = y.vector) : x = y := by
  cases x
  cases y
  simp_all

def plusZorn (x : PlusSheet) : Zorn :=
  OneSheetChiralAlgebra.oneSheet x.scalar x.vector

def minusZorn (y : MinusSheet) : Zorn :=
  add (smul y.scalar uMinus) (sigmaMinus y.vector)

def plusUnit : PlusSheet := ⟨1, 0⟩
def minusUnit : MinusSheet := ⟨1, 0⟩

/-- Explicit dual pairing; it pairs `u₊` with `u₋` and `σᵢ⁺` with `σᵢ⁻`. -/
def beta (x : PlusSheet) (y : MinusSheet) : ℂ :=
  x.scalar * y.scalar + dot x.vector y.vector

/-- Rank-one rectangular Jordan-pair triple in tagged plus coordinates. -/
def pairTriple (x : PlusSheet) (y : MinusSheet) (z : PlusSheet) : PlusSheet :=
  ⟨beta x y * z.scalar + beta z y * x.scalar,
    fun i => beta x y * z.vector i + beta z y * x.vector i⟩

theorem pairTriple_formula (x : PlusSheet) (y : MinusSheet) (z : PlusSheet) :
    (pairTriple x y z).scalar =
        beta x y * z.scalar + beta z y * x.scalar ∧
      (pairTriple x y z).vector = fun i =>
        beta x y * z.vector i + beta z y * x.vector i := by
  exact ⟨rfl, rfl⟩

theorem pairTriple_outer_symm (x : PlusSheet) (y : MinusSheet)
    (z : PlusSheet) : pairTriple x y z = pairTriple z y x := by
  cases x with
  | mk ax ux =>
    cases z with
    | mk az uz =>
      apply PlusSheet.ext
      · simp [pairTriple]
        ring
      · funext i
        simp [pairTriple]
        ring

/-- The positive polarization is closed under the Jordan product. -/
theorem polarized_jordan_closure (x y : PlusSheet) :
    jordan (plusZorn x) (plusZorn y) =
      plusZorn
        ⟨x.scalar * y.scalar,
          fun i => (x.scalar * y.vector i + y.scalar * x.vector i) / 2⟩ := by
  exact OneSheetChiralAlgebra.oneSheet_jordan_formula
    x.scalar y.scalar x.vector y.vector

/-- The vector radical of the polarization is square-zero. -/
theorem vector_jordan_zero (u v : Vec3) :
    jordan (sigmaPlus u) (sigmaPlus v) = zero := by
  unfold jordan OneSheetChiralAlgebra.jordan
  rw [plus_plus_anti]
  apply SplitOctonionBraidSU3.zorn_ext <;>
    simp [smul, zero, SplitOctonionBraidSU3.zornSmul] <;>
    try funext i <;> simp

/-- The scalar idempotent acts internally by the raw commutator. -/
theorem idempotent_vector_comm (u : Vec3) :
    comm uPlus (sigmaPlus u) = sigmaPlus u := by
  apply SplitOctonionBraidSU3.zorn_ext <;>
    simp [SplitOctonionChiralClosure.comm, mul, sub, uPlus, sigmaPlus, zero,
      SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornSub,
      SplitOctonionBraidSU3.dot3, SplitOctonionBraidSU3.cross3] <;>
    try funext i <;> simp

/-- Vector bivectors cross to the opposite Zorn lane. -/
theorem vector_vector_comm (u v : Vec3) :
    comm (sigmaPlus u) (sigmaPlus v) =
      smul 2 (sigmaMinus (cross u v)) :=
  plus_plus_comm u v

/-- Both off-diagonal lanes belong to the full Peirce `1/2` sector. -/
theorem full_peirce_half_lanes (u v : Vec3) :
    jordan uPlus (sigmaPlus u) = smul (1 / 2) (sigmaPlus u) ∧
    jordan uPlus (sigmaMinus v) = smul (1 / 2) (sigmaMinus v) := by
  constructor <;>
    apply SplitOctonionBraidSU3.zorn_ext <;>
    simp [jordan, OneSheetChiralAlgebra.jordan, antiComm, mul, add, smul,
      uPlus, sigmaPlus, sigmaMinus, SplitOctonionBraidSU3.zornMul,
      SplitOctonionBraidSU3.zornAdd, SplitOctonionBraidSU3.zornSmul,
      SplitOctonionBraidSU3.dot3, SplitOctonionBraidSU3.cross3] <;>
    try funext i <;> try fin_cases i <;> simp <;> ring

/-- Three positive vector lanes generate the parity element through the raw
octonionic associator. -/
theorem vector_associator_parity :
    assoc (sigmaPlus (axis 0)) (sigmaPlus (axis 1))
        (sigmaPlus (axis 2)) = smul (-1) ell := by
  apply SplitOctonionBraidSU3.zorn_ext <;>
    simp [assoc, OneSheetChiralAlgebra.assoc, mul, sub, smul, ell,
      sigmaPlus, sigmaMinus, axis, SplitOctonionBraidSU3.ell,
      SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornSub,
      SplitOctonionBraidSU3.zornSmul, SplitOctonionBraidSU3.dot3,
      SplitOctonionBraidSU3.cross3] <;>
    try funext i <;> try fin_cases i <;>
    simp [axis, SplitOctonionBraidSU3.cross3]

/-- Interpret the tagged Jordan-pair output in the positive Zorn sheet. -/
def pairTripleZorn (x : PlusSheet) (y : MinusSheet) (z : PlusSheet) : Zorn :=
  plusZorn (pairTriple x y z)

/-- The outer-symmetric Jordan-pair triple is not the alternating octonionic
associator, even on the canonical scalar dual pair. -/
theorem pairTriple_ne_associator :
    pairTripleZorn plusUnit minusUnit plusUnit ≠
      assoc (plusZorn plusUnit) (minusZorn minusUnit) (plusZorn plusUnit) := by
  intro h
  have ha := congrArg (fun X : Zorn => X.a) h
  norm_num [pairTripleZorn, pairTriple, beta, plusUnit, minusUnit,
    plusZorn, minusZorn, OneSheetChiralAlgebra.oneSheet, assoc,
    OneSheetChiralAlgebra.assoc, dot, mul, add, sub, smul, uPlus, uMinus,
    sigmaPlus, sigmaMinus, SplitOctonionBraidSU3.zornMul,
    SplitOctonionBraidSU3.zornAdd, SplitOctonionBraidSU3.zornSub,
    SplitOctonionBraidSU3.zornSmul, SplitOctonionBraidSU3.dot3] at ha

theorem polarized_owner_synthesis :
    (∀ x y : PlusSheet, ∃ z : PlusSheet,
      jordan (plusZorn x) (plusZorn y) = plusZorn z) ∧
    (∀ u v : Vec3, jordan (sigmaPlus u) (sigmaPlus v) = zero) ∧
    (∀ u : Vec3, comm uPlus (sigmaPlus u) = sigmaPlus u) ∧
    (∀ u v : Vec3, comm (sigmaPlus u) (sigmaPlus v) =
      smul 2 (sigmaMinus (cross u v))) ∧
    assoc (sigmaPlus (axis 0)) (sigmaPlus (axis 1))
      (sigmaPlus (axis 2)) = smul (-1) ell ∧
    (∀ x y z, pairTriple x y z = pairTriple z y x) := by
  refine ⟨?_, vector_jordan_zero, idempotent_vector_comm,
    vector_vector_comm, vector_associator_parity, pairTriple_outer_symm⟩
  intro x y
  exact ⟨⟨x.scalar * y.scalar,
    fun i => (x.scalar * y.vector i + y.scalar * x.vector i) / 2⟩,
    polarized_jordan_closure x y⟩

end PolarizedPeirceJordanMalcev

end noncomputable section
