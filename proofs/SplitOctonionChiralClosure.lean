import proofs.ZornOPParavector
import proofs.TKKJordanPairData

/-!
# Full split-octonion chiral closure

The canonical complex Zorn carrier is written in the circular basis
`{u₊,u₋,σ⁺₁,σ⁺₂,σ⁺₃,σ⁻₁,σ⁻₂,σ⁻₃}`.  The vector-valued formulas below are
the complete 8 by 8 product, commutator, and anticommutator tables.
-/

noncomputable section

namespace SplitOctonionChiralClosure

abbrev Zorn := SplitOctonionBraidSU3.Zorn
abbrev Vec3 := Fin 3 → ℂ

def mul (X Y : Zorn) : Zorn := SplitOctonionBraidSU3.zornMul X Y
def add (X Y : Zorn) : Zorn := SplitOctonionBraidSU3.zornAdd X Y
def sub (X Y : Zorn) : Zorn := SplitOctonionBraidSU3.zornSub X Y
def smul (c : ℂ) (X : Zorn) : Zorn := SplitOctonionBraidSU3.zornSmul c X
def comm (X Y : Zorn) : Zorn := sub (mul X Y) (mul Y X)
def antiComm (X Y : Zorn) : Zorn := add (mul X Y) (mul Y X)

def zero : Zorn := ⟨0, 0, 0, 0⟩
def one : Zorn := ⟨1, 0, 0, 1⟩
def uPlus : Zorn := ⟨1, 0, 0, 0⟩
def uMinus : Zorn := ⟨0, 0, 0, 1⟩
def sigmaPlus (u : Vec3) : Zorn := ⟨0, u, 0, 0⟩
def sigmaMinus (v : Vec3) : Zorn := ⟨0, 0, v, 0⟩
def kreinParity : Zorn := sub uPlus uMinus
def ell : Zorn := SplitOctonionBraidSU3.ell
def axis (k : Fin 3) : Vec3 := fun i => if i = k then 1 else 0
def dot (u v : Vec3) : ℂ := SplitOctonionBraidSU3.dot3 u v
def cross (u v : Vec3) : Vec3 := SplitOctonionBraidSU3.cross3 u v

/-- Cartesian (`i,j,k`) and ell-partner lanes.  Their half-sum/difference is
the circular `σ±` basis, exactly as for circular polarization. -/
def cartesian (u : Vec3) : Zorn := sub (sigmaPlus u) (sigmaMinus u)
def hypercomplex (u : Vec3) : Zorn := add (sigmaPlus u) (sigmaMinus u)

/-- Split-octonion conjugation exchanges the sheets and negates null lanes. -/
def conjugate (X : Zorn) : Zorn := ⟨X.b, fun i => -X.u i, fun i => -X.v i, X.a⟩

private theorem ext {X Y : Zorn}
    (ha : X.a = Y.a) (hu : X.u = Y.u) (hv : X.v = Y.v) (hb : X.b = Y.b) : X = Y :=
  SplitOctonionBraidSU3.zorn_ext ha hu hv hb

macro "zorn_coords" : tactic =>
  `(tactic| (apply ext <;>
    simp [mul, add, sub, smul, comm, antiComm, zero, one, uPlus, uMinus,
      sigmaPlus, sigmaMinus, kreinParity, ell, axis, dot, cross, cartesian, conjugate,
      hypercomplex, SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornAdd,
      SplitOctonionBraidSU3.zornSub, SplitOctonionBraidSU3.zornSmul,
      SplitOctonionBraidSU3.dot3, SplitOctonionBraidSU3.cross3,
      SplitOctonionBraidSU3.ell] <;> try funext i <;> try fin_cases i <;>
    simp [SplitOctonionBraidSU3.cross3] <;> try norm_num <;> try ring_nf))

theorem projector_sum : add uPlus uMinus = one := by zorn_coords
theorem projector_difference : kreinParity = ell := by zorn_coords

theorem peirce_products :
    mul uPlus uPlus = uPlus ∧ mul uMinus uMinus = uMinus ∧
    mul uPlus uMinus = zero ∧ mul uMinus uPlus = zero := by
  exact ⟨by zorn_coords, by zorn_coords, by zorn_coords, by zorn_coords⟩

/-- `u±=(1±ell)/2`, the scalar/hypercomplex circular split. -/
theorem cartan_circular_projectors :
    smul (1 / 2) (add one ell) = uPlus ∧
    smul (1 / 2) (sub one ell) = uMinus := by
  constructor <;> zorn_coords
  all_goals norm_num

/-- `σ±=(hypercomplex±cartesian)/2`, componentwise for all three axes. -/
theorem vector_circular_decomposition (u : Vec3) :
    smul (1 / 2) (add (hypercomplex u) (cartesian u)) = sigmaPlus u ∧
    smul (1 / 2) (sub (hypercomplex u) (cartesian u)) = sigmaMinus u := by
  constructor <;> zorn_coords

/-! Complete product table. -/

theorem plus_plus_product (u v : Vec3) :
    mul (sigmaPlus u) (sigmaPlus v) = sigmaMinus (cross u v) := by zorn_coords

theorem minus_minus_product (u v : Vec3) :
    mul (sigmaMinus u) (sigmaMinus v) = sigmaPlus (fun i => -cross u v i) := by
  zorn_coords

theorem plus_minus_product (u v : Vec3) :
    mul (sigmaPlus u) (sigmaMinus v) = smul (dot u v) uPlus := by zorn_coords

theorem minus_plus_product (u v : Vec3) :
    mul (sigmaMinus v) (sigmaPlus u) = smul (dot v u) uMinus := by zorn_coords

theorem projector_actions (u : Vec3) :
    mul uPlus (sigmaPlus u) = sigmaPlus u ∧
    mul (sigmaPlus u) uMinus = sigmaPlus u ∧
    mul uMinus (sigmaMinus u) = sigmaMinus u ∧
    mul (sigmaMinus u) uPlus = sigmaMinus u ∧
    mul uMinus (sigmaPlus u) = zero ∧
    mul (sigmaPlus u) uPlus = zero ∧
    mul uPlus (sigmaMinus u) = zero ∧
    mul (sigmaMinus u) uMinus = zero := by
  exact ⟨by zorn_coords, by zorn_coords, by zorn_coords, by zorn_coords,
    by zorn_coords, by zorn_coords, by zorn_coords, by zorn_coords⟩

/-! Complete commutator/anticommutator table. -/

theorem plus_plus_comm (u v : Vec3) :
    comm (sigmaPlus u) (sigmaPlus v) = smul 2 (sigmaMinus (cross u v)) := by
  zorn_coords

theorem plus_plus_anti (u v : Vec3) :
    antiComm (sigmaPlus u) (sigmaPlus v) = zero := by zorn_coords

theorem minus_minus_comm (u v : Vec3) :
    comm (sigmaMinus u) (sigmaMinus v) = smul (-2) (sigmaPlus (cross u v)) := by
  zorn_coords

theorem minus_minus_anti (u v : Vec3) :
    antiComm (sigmaMinus u) (sigmaMinus v) = zero := by zorn_coords

theorem mixed_anti (u v : Vec3) :
    antiComm (sigmaPlus u) (sigmaMinus v) = smul (dot u v) one := by
  zorn_coords
  all_goals ring

theorem mixed_comm (u v : Vec3) :
    comm (sigmaPlus u) (sigmaMinus v) = smul (dot u v) kreinParity := by
  zorn_coords
  all_goals ring

@[simp] theorem conjugate_involutive (X : Zorn) : conjugate (conjugate X) = X := by
  cases X
  zorn_coords

theorem conjugate_basis (u : Vec3) :
    conjugate uPlus = uMinus ∧ conjugate uMinus = uPlus ∧
    conjugate (sigmaPlus u) = sigmaPlus (fun i => -u i) ∧
    conjugate (sigmaMinus u) = sigmaMinus (fun i => -u i) ∧
    conjugate kreinParity = smul (-1) kreinParity := by
  exact ⟨by zorn_coords, by zorn_coords, by zorn_coords, by zorn_coords,
    by zorn_coords⟩

/-! The raw commutator is Malcev, not Lie.  TKK therefore requires its added
derivation/grade sectors; it cannot be the same eight-dimensional bracket. -/

theorem raw_commutator_jacobi_defect :
    add (add
      (comm (sigmaPlus (axis 0)) (comm (sigmaPlus (axis 1)) (sigmaMinus (axis 0))))
      (comm (sigmaPlus (axis 1)) (comm (sigmaMinus (axis 0)) (sigmaPlus (axis 0)))))
      (comm (sigmaMinus (axis 0)) (comm (sigmaPlus (axis 0)) (sigmaPlus (axis 1)))) =
        smul 6 (sigmaPlus (axis 1)) := by
  zorn_coords

theorem tkk_grade_window :
    TKKJordanPairData.Legacy.gradeAdd TKKJordanPairData.Legacy.TKKGrade.p1
        TKKJordanPairData.Legacy.TKKGrade.m1 = some TKKJordanPairData.Legacy.TKKGrade.z0 ∧
    TKKJordanPairData.Legacy.gradeAdd TKKJordanPairData.Legacy.TKKGrade.z0
        TKKJordanPairData.Legacy.TKKGrade.p1 = some TKKJordanPairData.Legacy.TKKGrade.p1 ∧
    TKKJordanPairData.Legacy.gradeAdd TKKJordanPairData.Legacy.TKKGrade.p2
        TKKJordanPairData.Legacy.TKKGrade.p1 = none := by
  exact ⟨rfl, rfl, rfl⟩

theorem split_octonion_chiral_closure_synthesis :
    (∀ u v, comm (sigmaPlus u) (sigmaPlus v) = smul 2 (sigmaMinus (cross u v))) ∧
    (∀ u v, antiComm (sigmaPlus u) (sigmaPlus v) = zero) ∧
    (∀ u v, comm (sigmaMinus u) (sigmaMinus v) = smul (-2) (sigmaPlus (cross u v))) ∧
    (∀ u v, antiComm (sigmaMinus u) (sigmaMinus v) = zero) ∧
    (∀ u v, antiComm (sigmaPlus u) (sigmaMinus v) = smul (dot u v) one) ∧
    (∀ u v, comm (sigmaPlus u) (sigmaMinus v) = smul (dot u v) kreinParity) ∧
    add uPlus uMinus = one ∧ kreinParity = ell ∧
    TKKJordanPairData.Legacy.gradeAdd TKKJordanPairData.Legacy.TKKGrade.p1
      TKKJordanPairData.Legacy.TKKGrade.m1 = some TKKJordanPairData.Legacy.TKKGrade.z0 := by
  exact ⟨plus_plus_comm, plus_plus_anti, minus_minus_comm, minus_minus_anti,
    mixed_anti, mixed_comm, projector_sum, projector_difference, rfl⟩

end SplitOctonionChiralClosure

end noncomputable section
