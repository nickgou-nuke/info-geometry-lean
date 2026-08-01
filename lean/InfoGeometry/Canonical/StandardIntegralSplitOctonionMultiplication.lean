import InfoGeometry.Canonical.ThreeColorIntegralCliffordEmbedding
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

namespace InfoGeometry.Canonical

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/-! Bridge the named coordinate carrier to the already existing integral Zorn
split-octonion multiplication owner.  No second multiplication table is
introduced here. -/

def zornCoordinateMap (x : StandardIntegralSplitOctonion) : SplitOct :=
  ⟨x .one + x .l, x .one - x .l,
    x .i - x .il, x .j - x .jl, x .k - x .kl,
    -x .i - x .il, -x .j - x .jl, -x .k - x .kl⟩

theorem zornCoordinateMap_injective :
    Function.Injective zornCoordinateMap := by
  intro x y h
  have ha : x .one + x .l = y .one + y .l := by
    exact congrArg SplitOct.a h
  have hb : x .one - x .l = y .one - y .l := by
    exact congrArg SplitOct.b h
  have hi : x .i - x .il = y .i - y .il := by
    exact congrArg SplitOct.x0 h
  have hil : -x .i - x .il = -y .i - y .il := by
    exact congrArg SplitOct.y0 h
  have hj : x .j - x .jl = y .j - y .jl := by
    exact congrArg SplitOct.x1 h
  have hjl : -x .j - x .jl = -y .j - y .jl := by
    exact congrArg SplitOct.y1 h
  have hk : x .k - x .kl = y .k - y .kl := by
    exact congrArg SplitOct.x2 h
  have hkl : -x .k - x .kl = -y .k - y .kl := by
    exact congrArg SplitOct.y2 h
  funext b
  cases b
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith

/-! The named basis is mapped to the standard Zorn coordinates.  These are
coordinate facts only; signs of products remain owned by `mulZ`. -/

theorem zornCoordinateMap_one :
    zornCoordinateMap oneOct = scalarZ 1 := by
  ext <;> simp [zornCoordinateMap, oneOct, splitBasisVector, scalarZ]

theorem zornCoordinateMap_l :
    zornCoordinateMap lOct = subZ ePlus eMinus := by
  ext <;> simp [zornCoordinateMap, lOct, splitBasisVector, ePlus, eMinus, subZ]

theorem zornCoordinateMap_i :
    zornCoordinateMap iOct = subZ up0 down0 := by
  ext <;> simp [zornCoordinateMap, iOct, splitBasisVector, up0, down0, subZ]

theorem zornCoordinateMap_j :
    zornCoordinateMap jOct = subZ up1 down1 := by
  ext <;> simp [zornCoordinateMap, jOct, splitBasisVector, up1, down1, subZ]

theorem zornCoordinateMap_k :
    zornCoordinateMap kOct = subZ up2 down2 := by
  ext <;> simp [zornCoordinateMap, kOct, splitBasisVector, up2, down2, subZ]

theorem zornCoordinateMap_il :
    zornCoordinateMap ilOct = negZ (up0 + down0) := by
  ext <;> simp [zornCoordinateMap, ilOct, splitBasisVector, up0, down0, negZ]

theorem zornCoordinateMap_jl :
    zornCoordinateMap jlOct = negZ (up1 + down1) := by
  ext <;> simp [zornCoordinateMap, jlOct, splitBasisVector, up1, down1, negZ]

theorem zornCoordinateMap_kl :
    zornCoordinateMap klOct = negZ (up2 + down2) := by
  ext <;> simp [zornCoordinateMap, klOct, splitBasisVector, up2, down2, negZ]

theorem zornCoordinateMap_i_sq :
    mulZ (zornCoordinateMap iOct) (zornCoordinateMap iOct) =
      negZ (scalarZ 1) := by
  rw [zornCoordinateMap_i]
  ext <;> simp [subZ, negZ, scalarZ, up0, down0, mulZ]

end InfoGeometry.Canonical
