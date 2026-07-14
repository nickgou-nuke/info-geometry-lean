import Mathlib
import InfoGeometry.Physics.SplitOctonionBraidSU3
open InfoGeometry.Physics.SplitOctonionBraidSU3

instance : Add Zorn := ⟨zornAdd⟩
instance : Sub Zorn := ⟨zornSub⟩
instance : Zero Zorn := ⟨zornZero⟩
instance : Neg Zorn := ⟨fun X => zornSub zornZero X⟩
instance : SMul ℂ Zorn := ⟨zornSmul⟩

instance : AddCommGroup Zorn where
  add_assoc := by intro a b c; apply zorn_ext <;> (simp [zornAdd, dot3]; ring)
  zero_add := by intro a; apply zorn_ext <;> (simp [zornAdd, zornZero, dot3])
  add_zero := by intro a; apply zorn_ext <;> (simp [zornAdd, zornZero, dot3])
  neg_add_cancel := by intro a; apply zorn_ext <;> (simp [zornAdd, zornSub, zornZero, dot3]; ring)
  add_comm := by intro a b; apply zorn_ext <;> (simp [zornAdd, dot3]; ring)
  sub_eq_add_neg := by intro a b; apply zorn_ext <;> (simp [zornAdd, zornSub, zornZero, dot3]; ring)

instance : Module ℂ Zorn where
  one_smul := by intro a; apply zorn_ext <;> (simp [zornSmul, dot3])
  mul_smul := by intro x y a; apply zorn_ext <;> (simp [zornSmul, dot3]; ring)
  smul_zero := by intro a; apply zorn_ext <;> (simp [zornSmul, zornZero, dot3])
  smul_add := by intro a x y; apply zorn_ext <;> (simp [zornSmul, zornAdd, dot3]; ring)
  add_smul := by intro a b x; apply zorn_ext <;> (simp [zornSmul, zornAdd, dot3]; ring)
  zero_smul := by intro x; apply zorn_ext <;> (simp [zornSmul, zornZero, dot3])

