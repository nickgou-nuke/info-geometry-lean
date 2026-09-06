import InfoGeometry.Physics.Octonion.ChiralZornAlgebra

/-!
# Finite colour/sheet symmetries of the chiral Zorn carrier

This file works directly on the eight-slot, possibly nonassociative carrier
`ChiralZornMatrix A`.  It does not introduce a ring structure or identify the
carrier with an associative matrix algebra.  The cyclic action is an
orientation-preserving permutation of the three colour components.  The
reflection exchanges the two diagonal/sheet slots and the two chiral vectors;
its colour permutation reverses orientation, and the sheet exchange supplies
the corresponding sign in the same-chiral cross channel.
-/

namespace InfoGeometry.Physics.Octonion

noncomputable section

variable {A : Type*} [Ring A]

namespace ChiralZornMatrix

def reflectColor : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 2
  | 2 => 1

def rotateColor (X : ChiralZornMatrix A) : ChiralZornMatrix A where
  n_plus := X.n_plus
  n_minus := X.n_minus
  sigma_plus := fun c => X.sigma_plus (prevColor c)
  sigma_minus := fun c => X.sigma_minus (prevColor c)

def reflect (X : ChiralZornMatrix A) : ChiralZornMatrix A where
  n_plus := X.n_minus
  n_minus := X.n_plus
  sigma_plus := fun c => X.sigma_minus (reflectColor c)
  sigma_minus := fun c => X.sigma_plus (reflectColor c)

def firstPlus : ChiralZornMatrix A where
  n_plus := 0
  n_minus := 0
  sigma_plus := ![1, 0, 0]
  sigma_minus := ![0, 0, 0]

@[simp] theorem mul_n_plus (X Y : ChiralZornMatrix A) :
    (X * Y).n_plus = X.n_plus * Y.n_plus +
      colorDot X.sigma_plus Y.sigma_minus := rfl

@[simp] theorem mul_n_minus (X Y : ChiralZornMatrix A) :
    (X * Y).n_minus = colorDot X.sigma_minus Y.sigma_plus +
      X.n_minus * Y.n_minus := rfl

@[simp] theorem mul_sigma_plus (X Y : ChiralZornMatrix A) (c : Fin 3) :
    (X * Y).sigma_plus c =
      X.n_plus * Y.sigma_plus c + X.sigma_plus c * Y.n_minus -
        colorCross X.sigma_minus Y.sigma_minus c := rfl

@[simp] theorem mul_sigma_minus (X Y : ChiralZornMatrix A) (c : Fin 3) :
    (X * Y).sigma_minus c =
      X.sigma_minus c * Y.n_plus + X.n_minus * Y.sigma_minus c +
        colorCross X.sigma_plus Y.sigma_plus c := rfl

theorem ext {X Y : ChiralZornMatrix A}
    (hnp : X.n_plus = Y.n_plus)
    (hnm : X.n_minus = Y.n_minus)
    (hsp : X.sigma_plus = Y.sigma_plus)
    (hsm : X.sigma_minus = Y.sigma_minus) :
    X = Y := by
  cases X
  cases Y
  simp_all

@[simp] theorem rotateColor_n_plus (X : ChiralZornMatrix A) :
    (rotateColor X).n_plus = X.n_plus := rfl

@[simp] theorem rotateColor_n_minus (X : ChiralZornMatrix A) :
    (rotateColor X).n_minus = X.n_minus := rfl

@[simp] theorem reflect_n_plus (X : ChiralZornMatrix A) :
    (reflect X).n_plus = X.n_minus := rfl

@[simp] theorem reflect_n_minus (X : ChiralZornMatrix A) :
    (reflect X).n_minus = X.n_plus := rfl

theorem rotateColor_three (X : ChiralZornMatrix A) :
    rotateColor (rotateColor (rotateColor X)) = X := by
  apply ext <;>
    try rfl
  · funext c
    fin_cases c <;> rfl
  · funext c
    fin_cases c <;> rfl

theorem reflect_two (X : ChiralZornMatrix A) :
    reflect (reflect X) = X := by
  apply ext <;>
    try rfl
  · funext c
    fin_cases c <;> rfl
  · funext c
    fin_cases c <;> rfl

theorem colorDot_rotate (x y : Fin 3 → A) :
    colorDot (fun c => x (prevColor c)) (fun c => y (prevColor c)) =
      colorDot x y := by
  dsimp [colorDot, prevColor]
  abel

theorem colorCross_rotate (x y : Fin 3 → A) :
    (fun c => colorCross (fun k => x (prevColor k))
      (fun k => y (prevColor k)) c) =
      (fun c => colorCross x y (prevColor c)) := by
  funext c
  fin_cases c <;>
    simp [colorCross, nextColor, prevColor]

theorem colorDot_reflect (x y : Fin 3 → A) :
    colorDot (fun c => x (reflectColor c)) (fun c => y (reflectColor c)) =
      colorDot x y := by
  dsimp [colorDot, reflectColor]
  abel

theorem colorCross_reflect (x y : Fin 3 → A) :
    (fun c => colorCross (fun k => x (reflectColor k))
      (fun k => y (reflectColor k)) c) =
      (fun c => -colorCross x y (reflectColor c)) := by
  funext c
  fin_cases c <;>
    simp [colorCross, nextColor, prevColor, reflectColor]

theorem rotateColor_mul (X Y : ChiralZornMatrix A) :
    rotateColor (X * Y) = rotateColor X * rotateColor Y := by
  apply ext
  · change (X * Y).n_plus = (rotateColor X * rotateColor Y).n_plus
    rw [mul_n_plus X Y, mul_n_plus (rotateColor X) (rotateColor Y)]
    dsimp [rotateColor]
    rw [colorDot_rotate]
  · change (X * Y).n_minus = (rotateColor X * rotateColor Y).n_minus
    rw [mul_n_minus X Y, mul_n_minus (rotateColor X) (rotateColor Y)]
    dsimp [rotateColor]
    rw [colorDot_rotate]
  · funext c
    change (X * Y).sigma_plus (prevColor c) =
      (rotateColor X * rotateColor Y).sigma_plus c
    rw [mul_sigma_plus X Y, mul_sigma_plus (rotateColor X) (rotateColor Y)]
    fin_cases c <;>
      simp [rotateColor, colorCross, nextColor, prevColor]
  · funext c
    change (X * Y).sigma_minus (prevColor c) =
      (rotateColor X * rotateColor Y).sigma_minus c
    rw [mul_sigma_minus X Y, mul_sigma_minus (rotateColor X) (rotateColor Y)]
    fin_cases c <;>
      simp [rotateColor, colorCross, nextColor, prevColor]

theorem reflect_mul (X Y : ChiralZornMatrix A) :
    reflect (X * Y) = reflect X * reflect Y := by
  apply ext
  · change (X * Y).n_minus = (reflect X * reflect Y).n_plus
    rw [mul_n_minus X Y, mul_n_plus (reflect X) (reflect Y)]
    dsimp [reflect]
    rw [colorDot_reflect]
    exact add_comm _ _
  · change (X * Y).n_plus = (reflect X * reflect Y).n_minus
    rw [mul_n_plus X Y, mul_n_minus (reflect X) (reflect Y)]
    dsimp [reflect]
    rw [colorDot_reflect]
    exact add_comm _ _
  · funext c
    change (X * Y).sigma_minus (reflectColor c) =
      (reflect X * reflect Y).sigma_plus c
    rw [mul_sigma_minus X Y, mul_sigma_plus (reflect X) (reflect Y)]
    fin_cases c <;>
      simp [reflect, colorCross, reflectColor, nextColor, prevColor] <;> abel
  · funext c
    change (X * Y).sigma_plus (reflectColor c) =
      (reflect X * reflect Y).sigma_minus c
    rw [mul_sigma_plus X Y, mul_sigma_minus (reflect X) (reflect Y)]
    fin_cases c <;>
      simp [reflect, colorCross, reflectColor, nextColor, prevColor] <;> abel

theorem reflect_rotate_reflect (X : ChiralZornMatrix A) :
    reflect (rotateColor (reflect X)) =
      rotateColor (rotateColor X) := by
  apply ext <;>
    try rfl
  · funext c
    fin_cases c <;> rfl
  · funext c
    fin_cases c <;> rfl

def rotateMulEquiv : ChiralZornMatrix A ≃* ChiralZornMatrix A where
  toEquiv :=
    { toFun := rotateColor
      invFun := fun X => rotateColor (rotateColor X)
      left_inv := by intro X; exact rotateColor_three X
      right_inv := by intro X; exact rotateColor_three X }
  map_mul' := rotateColor_mul

def reflectMulEquiv : ChiralZornMatrix A ≃* ChiralZornMatrix A where
  toEquiv :=
    { toFun := reflect
      invFun := reflect
      left_inv := reflect_two
      right_inv := reflect_two }
  map_mul' := reflect_mul

@[simp] theorem rotateMulEquiv_apply (X : ChiralZornMatrix A) :
    rotateMulEquiv X = rotateColor X := rfl

@[simp] theorem reflectMulEquiv_apply (X : ChiralZornMatrix A) :
    reflectMulEquiv X = reflect X := rfl

theorem reflectMulEquiv_rotateMulEquiv_reflectMulEquiv_apply
    (X : ChiralZornMatrix A) :
    reflectMulEquiv (rotateMulEquiv (reflectMulEquiv X)) =
      rotateMulEquiv (rotateMulEquiv X) :=
  reflect_rotate_reflect X

theorem rotateColor_sq_ne_rotateColor [Nontrivial A] :
    rotateColor (rotateColor (firstPlus (A := A))) ≠
      rotateColor (firstPlus (A := A)) := by
  intro h
  have hc := congrFun (congrArg (fun Z : ChiralZornMatrix A => Z.sigma_plus) h) 1
  simpa [firstPlus, rotateColor, prevColor] using hc

theorem rotateColor_reflect_not_commute [Nontrivial A] :
    ¬ (∀ X : ChiralZornMatrix A,
      reflect (rotateColor X) = rotateColor (reflect X)) := by
  intro hcomm
  have hcycle : ∀ X : ChiralZornMatrix A,
      rotateColor (rotateColor X) = rotateColor X := by
    intro X
    have h := hcomm (reflect X)
    rw [reflect_rotate_reflect X] at h
    simpa [reflect_two] using h
  exact rotateColor_sq_ne_rotateColor (A := A) (hcycle (firstPlus (A := A)))

end ChiralZornMatrix

end
end InfoGeometry.Physics.Octonion
