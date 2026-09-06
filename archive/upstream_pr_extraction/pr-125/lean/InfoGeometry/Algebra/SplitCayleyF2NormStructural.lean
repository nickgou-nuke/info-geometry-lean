import InfoGeometry.Algebra.SplitCayleyF2

namespace InfoGeometry.Algebra.SplitCayleyF2

@[simp] theorem shearU_apply_zero (u : Vec3) : shearU u 0 = u 0 + u 1 := by
  rfl

@[simp] theorem shearU_apply_one (u : Vec3) : shearU u 1 = u 1 := by
  rfl

@[simp] theorem shearU_apply_two (u : Vec3) : shearU u 2 = u 2 := by
  rfl

@[simp] theorem shearV_apply_zero (v : Vec3) : shearV v 0 = v 0 := by
  rfl

@[simp] theorem shearV_apply_one (v : Vec3) : shearV v 1 = v 1 + v 0 := by
  rfl

@[simp] theorem shearV_apply_two (v : Vec3) : shearV v 2 = v 2 := by
  rfl

theorem shearU_add (u v : Vec3) :
    shearU (fun i => u i + v i) =
      (fun i => shearU u i + shearU v i) := by
  funext i
  fin_cases i
  · change (u 0 + v 0) + (u 1 + v 1) =
      (u 0 + u 1) + (v 0 + v 1)
    ring
  · change (u 1 + v 1) = u 1 + v 1
    rfl
  · change (u 2 + v 2) = u 2 + v 2
    rfl

theorem shearV_add (u v : Vec3) :
    shearV (fun i => u i + v i) =
      (fun i => shearV u i + shearV v i) := by
  funext i
  fin_cases i
  · change (u 0 + v 0) = u 0 + v 0
    rfl
  · change (u 1 + v 1) + (u 0 + v 0) =
      (u 1 + u 0) + (v 1 + v 0)
    ring
  · change (u 2 + v 2) = u 2 + v 2
    rfl

theorem shearU_smul (a : Scalar) (u : Vec3) :
    shearU (fun i => a * u i) =
      (fun i => a * shearU u i) := by
  funext i
  fin_cases i <;> simp [shearU]
  all_goals ring

theorem shearV_smul (a : Scalar) (u : Vec3) :
    shearV (fun i => a * u i) =
      (fun i => a * shearV u i) := by
  funext i
  fin_cases i <;> simp [shearV]
  all_goals ring

theorem shearU_linear_combination (a b : Scalar) (u v w : Vec3) :
    shearU (fun i => a * u i + b * v i - w i) =
      (fun i => a * shearU u i + b * shearU v i - shearU w i) := by
  funext i
  fin_cases i <;> simp [shearU]
  all_goals ring

theorem shearV_linear_combination (a b : Scalar) (u v w : Vec3) :
    shearV (fun i => a * u i + b * v i + w i) =
      (fun i => a * shearV u i + b * shearV v i + shearV w i) := by
  funext i
  fin_cases i <;> simp [shearV]
  all_goals ring

theorem cyclicAction_add_structural (x y : Cayley) :
    cyclicAction (add x y) = add (cyclicAction x) (cyclicAction y) := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      apply Cayley.ext <;> simp [cyclicAction, add, cyclic]
      all_goals funext i
      all_goals fin_cases i <;> rfl

theorem shearAction_add_structural (x y : Cayley) :
    shearAction (add x y) = add (shearAction x) (shearAction y) := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      apply Cayley.ext
      · rfl
      · change shearU (fun i => xu i + yu i) =
          (fun i => shearU xu i + shearU yu i)
        exact shearU_add xu yu
      · change shearV (fun i => xv i + yv i) =
          (fun i => shearV xv i + shearV yv i)
        exact shearV_add xv yv
      · rfl

@[simp] theorem mul_u_apply (x y : Cayley) (i : Fin 3) :
    (x * y).u i =
      (x.α * y.u i + y.β * x.u i) - cross x.v y.v i := by
  rfl

@[simp] theorem mul_v_apply (x y : Cayley) (i : Fin 3) :
    (x * y).v i =
      (y.α * x.v i + x.β * y.v i) + cross x.u y.u i := by
  rfl

theorem dot_cyclicAction (u v : Vec3) :
    dot (cyclic u) (cyclic v) = dot u v := by
  simp [dot, cyclic]
  ring

theorem dot_shearAction (u v : Vec3) :
    dot (shearU u) (shearV v) = dot u v := by
  simp [dot, shearU, shearV]
  have htwo : (2 : Scalar) = 0 := CharP.cast_eq_zero Scalar 2
  ring_nf
  simp [htwo]

theorem cross_cyclicAction (u v : Vec3) :
    cross (cyclic u) (cyclic v) = cyclic (cross u v) := by
  funext i
  fin_cases i <;> simp [cross, cyclic]

theorem cross_shearV (u v : Vec3) :
    cross (shearV u) (shearV v) = shearU (cross u v) := by
  funext i
  fin_cases i <;> simp [cross, shearU, shearV]
  all_goals ring_nf
  all_goals simp [sub_eq_add_neg]
  all_goals ring

theorem shear_mul_u_structural (x y : Cayley) :
    (shearAction (x * y)).u = (shearAction x * shearAction y).u := by
  have hmul : (x * y).u =
      (fun i => x.α * y.u i + y.β * x.u i - cross x.v y.v i) := by
    funext i
    exact mul_u_apply x y i
  rw [show (shearAction (x * y)).u = shearU ((x * y).u) by rfl, hmul]
  rw [shearU_linear_combination]
  funext i
  simp only [shearAction, mul_u_apply]
  rw [cross_shearV]

theorem cross_shearU (u v : Vec3) :
    cross (shearU u) (shearU v) = shearV (cross u v) := by
  funext i
  fin_cases i <;> simp [cross, shearU, shearV]
  all_goals ring_nf
  all_goals simp [sub_eq_add_neg]
  all_goals ring

theorem shear_mul_v_structural (x y : Cayley) :
    (shearAction (x * y)).v = (shearAction x * shearAction y).v := by
  have hmul : (x * y).v =
      (fun i => y.α * x.v i + x.β * y.v i + cross x.u y.u i) := by
    funext i
    exact mul_v_apply x y i
  rw [show (shearAction (x * y)).v = shearV ((x * y).v) by rfl, hmul]
  rw [shearV_linear_combination]
  funext i
  simp only [shearAction, mul_v_apply]
  rw [cross_shearU]

@[simp] theorem cross_shearV_apply_zero (u v : Vec3) :
    cross (shearV u) (shearV v) 0 = cross u v 0 + cross u v 1 := by
  rw [cross_shearV]
  rfl

@[simp] theorem cross_shearV_apply_one (u v : Vec3) :
    cross (shearV u) (shearV v) 1 = cross u v 1 := by
  rw [cross_shearV]
  rfl

@[simp] theorem cross_shearV_apply_two (u v : Vec3) :
    cross (shearV u) (shearV v) 2 = cross u v 2 := by
  rw [cross_shearV]
  rfl

@[simp] theorem cross_shearU_apply_zero (u v : Vec3) :
    cross (shearU u) (shearU v) 0 = cross u v 0 := by
  rw [cross_shearU]
  rfl

@[simp] theorem cross_shearU_apply_one (u v : Vec3) :
    cross (shearU u) (shearU v) 1 = cross u v 1 + cross u v 0 := by
  rw [cross_shearU]
  rfl

@[simp] theorem cross_shearU_apply_two (u v : Vec3) :
    cross (shearU u) (shearU v) 2 = cross u v 2 := by
  rw [cross_shearU]
  rfl

theorem cyclic_mul_alpha_structural (x y : Cayley) :
    (cyclicAction (x * y)).α = (cyclicAction x * cyclicAction y).α := by
  change (x * y).α = (cyclicAction x * cyclicAction y).α
  change x.α * y.α + dot x.u y.v =
    x.α * y.α + dot (cyclic x.u) (cyclic y.v)
  rw [dot_cyclicAction]

theorem cyclic_mul_beta_structural (x y : Cayley) :
    (cyclicAction (x * y)).β = (cyclicAction x * cyclicAction y).β := by
  change (x * y).β = (cyclicAction x * cyclicAction y).β
  change dot x.v y.u + x.β * y.β =
    dot (cyclic x.v) (cyclic y.u) + x.β * y.β
  rw [dot_cyclicAction]

theorem cyclic_mul_u_structural (x y : Cayley) :
    (cyclicAction (x * y)).u = (cyclicAction x * cyclicAction y).u := by
  funext i
  fin_cases i
  · change (x.α * y.u 2 + y.β * x.u 2) - cross x.v y.v 2 =
      x.α * y.u 2 + y.β * x.u 2 - cross (cyclic x.v) (cyclic y.v) 0
    rw [cross_cyclicAction]
    rfl
  · change (x.α * y.u 0 + y.β * x.u 0) - cross x.v y.v 0 =
      x.α * y.u 0 + y.β * x.u 0 - cross (cyclic x.v) (cyclic y.v) 1
    rw [cross_cyclicAction]
    rfl
  · change (x.α * y.u 1 + y.β * x.u 1) - cross x.v y.v 1 =
      x.α * y.u 1 + y.β * x.u 1 - cross (cyclic x.v) (cyclic y.v) 2
    rw [cross_cyclicAction]
    rfl

theorem cyclic_mul_v_structural (x y : Cayley) :
    (cyclicAction (x * y)).v = (cyclicAction x * cyclicAction y).v := by
  funext i
  fin_cases i
  · change (y.α * x.v 2 + x.β * y.v 2) + cross x.u y.u 2 =
      y.α * x.v 2 + x.β * y.v 2 + cross (cyclic x.u) (cyclic y.u) 0
    rw [cross_cyclicAction]
    rfl
  · change (y.α * x.v 0 + x.β * y.v 0) + cross x.u y.u 0 =
      y.α * x.v 0 + x.β * y.v 0 + cross (cyclic x.u) (cyclic y.u) 1
    rw [cross_cyclicAction]
    rfl
  · change (y.α * x.v 1 + x.β * y.v 1) + cross x.u y.u 1 =
      y.α * x.v 1 + x.β * y.v 1 + cross (cyclic x.u) (cyclic y.u) 2
    rw [cross_cyclicAction]
    rfl

theorem shear_mul_alpha_structural (x y : Cayley) :
    (shearAction (x * y)).α = (shearAction x * shearAction y).α := by
  change x.α * y.α + dot x.u y.v =
    x.α * y.α + dot (shearU x.u) (shearV y.v)
  rw [dot_shearAction]

theorem shear_mul_beta_structural (x y : Cayley) :
    (shearAction (x * y)).β = (shearAction x * shearAction y).β := by
  change dot x.v y.u + x.β * y.β =
    dot (shearV x.v) (shearU y.u) + x.β * y.β
  rw [dot_comm (shearV x.v) (shearU y.u), dot_comm x.v y.u,
    dot_shearAction]

theorem norm_mul_structural (x y : Cayley) :
    norm (x * y) = norm x * norm y := by
  cases x with
  | mk xa xu xv xb =>
    cases y with
    | mk ya yu yv yb =>
      change norm (mul {α := xa, u := xu, v := xv, β := xb}
        {α := ya, u := yu, v := yv, β := yb}) =
        norm {α := xa, u := xu, v := xv, β := xb} *
          norm {α := ya, u := yu, v := yv, β := yb}
      simp [norm, mul, dot, cross]
      ring

end InfoGeometry.Algebra.SplitCayleyF2
