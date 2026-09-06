import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

/-!
# Split-octonion modular-J conjugation packet

\[
J(X):=\mathrm{conjZ}(X),\qquad
J^2=\mathrm{id},\qquad
J(XY)=J(Y)J(X),\qquad
\detZ(JX)=\detZ(X),\qquad
XJX=\detZ(X)\cdot 1.
\]
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/-- `J(X):=\mathrm{conjZ}(X)`. -/
def modularJ (X : SplitOct) : SplitOct := conjZ X

@[simp] theorem modularJ_apply (X : SplitOct) :
    modularJ X = ⟨X.b, X.a, -X.x0, -X.x1, -X.x2, -X.y0, -X.y1, -X.y2⟩ := by
  rfl

/-- `J^2=\mathrm{id}`. -/
theorem modularJ_involutive (X : SplitOct) : modularJ (modularJ X) = X := by
  exact conjZ_conjZ X

/-- `J(XY)=J(Y)J(X)`. -/
theorem modularJ_anti_automorphism (X Y : SplitOct) :
    modularJ (mulZ X Y) = mulZ (modularJ Y) (modularJ X) := by
  exact conjZ_mulZ X Y

/-- `\detZ(JX)=\detZ(X)`. -/
theorem detZ_modularJ_invariant (X : SplitOct) :
    detZ (modularJ X) = detZ X := by
  exact detZ_conjZ X

/-- `XJX=\detZ(X)\cdot 1`. -/
theorem mul_modularJ_eq_scalar_detZ (X : SplitOct) :
    mulZ X (modularJ X) = scalarZ (detZ X) := by
  exact mul_conjZ_eq_scalar_detZ X

/-- `J^2=\mathrm{id}\wedge J(XY)=J(Y)J(X)\wedge \detZ(JX)=\detZ(X)\wedge XJX=\detZ(X)\cdot 1`. -/
theorem modularJ_structure_packet :
    (∀ X : SplitOct, modularJ (modularJ X) = X) ∧
      (∀ X Y : SplitOct, modularJ (mulZ X Y) = mulZ (modularJ Y) (modularJ X)) ∧
      (∀ X : SplitOct, detZ (modularJ X) = detZ X) ∧
      (∀ X : SplitOct, mulZ X (modularJ X) = scalarZ (detZ X)) := by
  exact ⟨modularJ_involutive, modularJ_anti_automorphism,
    detZ_modularJ_invariant, mul_modularJ_eq_scalar_detZ⟩

end InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
