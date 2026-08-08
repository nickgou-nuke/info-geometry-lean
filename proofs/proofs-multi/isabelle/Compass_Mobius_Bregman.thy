theory Compass_Mobius_Bregman
  imports Complex_Main
begin

(* ================================================================== *)
(* 1. Compass geometric algebra in ℝ²                                 *)
(* ================================================================== *)

type_synonym Vec2 = "real × real"

definition dot :: "Vec2 ⇒ Vec2 ⇒ real" where
  "dot u v = fst u * fst v + snd u * snd v"

definition norm :: "Vec2 ⇒ real" where
  "norm u = sqrt (dot u u)"

definition cross :: "Vec2 ⇒ Vec2 ⇒ real" where
  "cross u v = fst u * snd v - snd u * fst v"

definition geom_prod :: "Vec2 ⇒ Vec2 ⇒ real × real" where
  "geom_prod u v = (- (dot u v), cross u v)"

definition rotate :: "real ⇒ Vec2 ⇒ Vec2" where
  "rotate θ x = (fst x * cos θ - snd x * sin θ,
                 fst x * sin θ + snd x * cos θ)"

(* Basis orthonormality: dot (1,0) with (1,0) is 1. *)
lemma basis_dot_self [simp]: "dot (1, 0) (1, 0) = 1"
  unfolding dot_def by simp

(* Basis orthonormality: dot (1,0) with (0,1) is 0. *)
lemma basis_dot_orth [simp]: "dot (1, 0) (0, 1) = 0"
  unfolding dot_def by simp

(* Geometric product decomposes into scalar + bivector parts. *)
lemma geom_prod_basis: "geom_prod (1, 0) (0, 1) = (0, 1)"
  unfolding geom_prod_def dot_def cross_def by simp

lemma geom_prod_decomp:
  fixes a1 a2 b1 b2 :: real
  shows "geom_prod (a1, a2) (b1, b2) =
         (- (a1 * b1 + a2 * b2), a1 * b2 - a2 * b1)"
  unfolding geom_prod_def dot_def cross_def by simp

(* Rotation angle addition: rot(α+β) = rot α ∘ rot β *)
lemma rotate_angle_add:
  fixes α β x y :: real
  shows "rotate (α + β) (x, y) = rotate α (rotate β (x, y))"
  unfolding rotate_def
  by (simp add: cos_add sin_add algebra_simps distrib_right)

(* Unit rotor preserves the standard Euclidean dot product. *)
lemma rotate_dot_preserving:
  fixes θ x y :: real
  shows "dot (rotate θ (x, y)) (rotate θ (x, y)) = dot (x, y) (x, y)"
proof -
  have "dot (rotate θ (x, y)) (rotate θ (x, y)) =
        (x*cos θ - y*sin θ)^2 + (x*sin θ + y*cos θ)^2"
    unfolding dot_def rotate_def by simp
  then show ?thesis
    unfolding dot_def by (simp add: field_simps cos_squared_eq sin_squared_eq)
qed

lemma rotate_zero [simp]: "rotate 0 (x, y) = (x, y)"
  unfolding rotate_def by simp

(* ================================================================== *)
(* 2. Möbius transformations: f(z)=(a*z+b)/(c*z+d), a*d−b*c≠0       *)
(* ================================================================== *)

definition mob_numer :: "real ⇒ real ⇒ real ⇒ real ⇒ real ⇒ real"
  where "mob_numer a b c d z = a * z + b"

definition mob_denom :: "real ⇒ real ⇒ real ⇒ real ⇒ real ⇒ real"
  where "mob_denom a b c d z = c * z + d"

definition mobius :: "real ⇒ real ⇒ real ⇒ real ⇒ real ⇒ real"
  where "mobius a b c d z = mob_numer a b c d z / mob_denom a b c d z"

(* Möbius composition recombines coefficients *)
lemma mob_compose:
  fixes a1 b1 c1 d1 a2 b2 c2 d2 z :: real
  assumes "(a1 * d1 - b1 * c1) ≠ 0"
          "(a2 * d2 - b2 * c2) ≠ 0"
          "c1 * z + d1 ≠ 0"
          "c2 * mobius a1 b1 c1 d1 z + d2 ≠ 0"
  shows "mobius a2 b2 c2 d2 (mobius a1 b1 c1 d1 z) =
         mobius (a2 * a1 + b2 * c1)
                (a2 * b1 + b2 * d1)
                (c2 * a1 + d2 * c1)
                (c2 * b1 + d2 * d1)
                z"
proof -
  have lhs: "mobius a2 b2 c2 d2 (mobius a1 b1 c1 d1 z) =
        (a2 * (a1 * z + b1) + b2 * (c1 * z + d1)) /
        (c2 * (a1 * z + b1) + d2 * (c1 * z + d1))"
    unfolding mobius_def mob_numer_def mob_denom_def
    by (simp add: field_simps)
  from lhs assms show ?thesis
    unfolding mobius_def mob_numer_def mob_denom_def
    by (simp add: field_simps)
qed

(* Determinant of composition equals product of determinants. *)
lemma mob_det_compose:
  fixes a1 b1 c1 d1 a2 b2 c2 d2 :: real
  shows "((a2 * a1 + b2 * c1) * (c2 * b1 + d2 * d1) -
           (a2 * b1 + b2 * d1) * (c2 * a1 + d2 * c1)) =
          (a2 * d2 - b2 * c2) * (a1 * d1 - b1 * c1)"
  by (simp add: algebra_simps)

(* Cross-ratio is invariant under Möbius maps. *)
definition cross_ratio :: "real ⇒ real ⇒ real ⇒ real ⇒ real" where
  "cross_ratio z1 z2 z3 z4 =
     (z1 - z2) / (z1 - z3) * (z3 - z4) / (z2 - z4)"

lemma mob_preserves_cross_ratio:
  fixes z1 z2 z3 z4 a b c d :: real
  assumes "z1 ≠ z2" "z1 ≠ z3" "z2 ≠ z3"
  shows "cross_ratio
           (mobius a b c d z1)
           (mobius a b c d z2)
           (mobius a b c d z3)
           (mobius a b c d z4)
         = cross_ratio z1 z2 z3 z4"
  unfolding cross_ratio_def mobius_def mob_numer_def mob_denom_def
  using assms by (simp add: field_simps)

(* ================================================================== *)
(* 3. Bregman divergence: D_f(p,q)=f(p)−f(q)−∇f(q)ᵀ(p−q)            *)
(* ================================================================== *)

definition bregman_entropy :: "real ⇒ real ⇒ real"
  where "bregman_entropy p q =
           (if p > 0 ∧ q > 0 then p * log (p / q) - (p - q) else 1)"

definition bregman_quadratic :: "real ⇒ real ⇒ real"
  where "bregman_quadratic x y = ((x - y)^2) / 2"

(* Bregman identities *)
lemma bregman_entropy_form:
  fixes p q :: real
  assumes "p > 0" "q > 0"
  shows "bregman_entropy p q = p*log (p / q) - (p - q)"
  unfolding bregman_entropy_def using assms by simp

lemma bregman_self_diverge_zero:
  fixes p :: real
  assumes "p > 0"
  shows "bregman_entropy p p = 0"
  unfolding bregman_entropy_def using assms by simp

lemma bregman_quadratic_form:
  "bregman_quadratic x y = ((x - y)^2) / 2"
  unfolding bregman_quadratic_def by simp

lemma bregman_quadratic_triangle:
  fixes x y z :: real
  shows "sqrt (bregman_quadratic x y) ≤
         sqrt (bregman_quadratic x z) + sqrt (bregman_quadratic z y)"
  unfolding bregman_quadratic_def
  by (simp add: abs_bound_triangle_inequality)

lemma bregman_quad_nonneg: "bregman_quadratic x y ≥ 0"
  unfolding bregman_quadratic_def
  by (simp add: zero_le_divide1 zero_le_power2)

end
