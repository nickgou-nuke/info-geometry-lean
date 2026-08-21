import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-!
# A concrete finite split-Zorn automorphism

The coordinate transposition `0 ↔ 1` in both vector slots is an actual
automorphism of the characteristic-two Zorn multiplication.  This gives a
native nontrivial generator for subsequent orbit/stabilizer constructions.
-/

namespace InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def swap01Fun : SplitOctF2 → SplitOctF2
  | ⟨a, b, x0, x1, x2, y0, y1, y2⟩ =>
      ⟨a, b, x1, x0, x2, y1, y0, y2⟩

noncomputable def swap01Equiv : SplitOctF2 ≃ SplitOctF2 where
  toFun := swap01Fun
  invFun := swap01Fun
  left_inv := by intro X; cases X <;> rfl
  right_inv := by intro X; cases X <;> rfl

theorem swap01_add (X Y : SplitOctF2) :
    swap01Fun (add X Y) = add (swap01Fun X) (swap01Fun Y) := by
  native_decide +revert

theorem swap01_mul (X Y : SplitOctF2) :
    swap01Fun (mul X Y) = mul (swap01Fun X) (swap01Fun Y) := by
  native_decide +revert

noncomputable def swap01Aut : SplitOctF2Aut :=
  ⟨swap01Equiv, by
    refine ⟨?_, ?_, ?_⟩
    · rfl
    · intro X Y
      exact swap01_add X Y
    · intro X Y
      exact swap01_mul X Y⟩

theorem swap01Aut_apply (X : SplitOctF2) :
    swap01Aut.1 X = swap01Fun X :=
  rfl

theorem swap01Aut_sq :
    swap01Aut * swap01Aut = (1 : SplitOctF2Aut) := by
  apply Subtype.ext
  apply Equiv.ext
  intro X
  cases X <;> rfl

theorem swap01Aut_ne_one :
    swap01Aut ≠ (1 : SplitOctF2Aut) := by
  intro h
  have h_apply := congrArg (fun f : SplitOctF2Aut => f.1 up0) h
  have hx := congrArg (fun X : SplitOctF2 => X.x0) h_apply
  simp [swap01Aut, swap01Equiv, swap01Fun, up0, up1] at hx

end InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
