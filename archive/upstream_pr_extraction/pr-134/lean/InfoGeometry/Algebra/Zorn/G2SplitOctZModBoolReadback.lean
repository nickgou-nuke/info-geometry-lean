import InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

namespace InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

theorem zModToBool_injective :
    Function.Injective zModToBool := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [zModToBool] at h ⊢

theorem boolToZMod_injective :
    Function.Injective boolToZMod := by
  intro a b h
  rw [← zModToBool_boolToZMod a, ← zModToBool_boolToZMod b]
  exact congrArg zModToBool h

end InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge
