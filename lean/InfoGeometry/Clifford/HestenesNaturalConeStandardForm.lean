import InfoGeometry.Clifford.HestenesLorentzJordanCone
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.Hestenes

open CliffordAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M) (hv0_norm : Q v0 = 1)

/-- 
Стереоскопичното алгебрично действие (Standard-form stereoscopy).
Ляво действие L_A(X) = A * X.
-/
def L_action (A X : ClPlus Q) : ClPlus Q :=
  ⟨A.val * X.val, clPlus_mul_clPlus Q A.val X.val A.property X.property⟩

/-- 
Стереоскопичното алгебрично действие.
Дясно действие R_B(X) = X * B.
Това е еквивалентът на комутанта M'.
-/
def R_action (B X : ClPlus Q) : ClPlus Q :=
  ⟨X.val * B.val, clPlus_mul_clPlus Q X.val B.val X.property B.property⟩

/-- 
Модулярната конюгация J_mod.
За $M_2(\mathbb{C})$ тя съвпада с Ермитовото спрягане A^†.
За нашата Hestenes алгебра, това е точно hestenesAdjoint.
-/
def J_mod (X : ClPlus Q) : ClPlus Q :=
  hestenesAdjoint Q v0 X

/-- 
Фундаменталната връзка между лявото действие (алгебрата M), 
дясното действие (комутанта M') и модулярната конюгация J_mod.
J_mod (L_A (J_mod X)) = R_{A^†} (X).
Тази теорема е скелетът на модулярната теория на Tomita-Takesaki в нашата формализация.
-/
theorem J_mod_L_action_J_mod (hv0_norm : Q v0 = 1) (A X : ClPlus Q) :
    J_mod Q v0 (L_action Q A (J_mod Q v0 X)) = R_action Q (hestenesAdjoint Q v0 A) X := by
  apply Subtype.ext
  dsimp [J_mod, hestenesAdjoint, L_action, R_action]
  rw [reverse.map_mul, reverse.map_mul, reverse.map_mul]
  have h_g0_rev : reverse (gamma0 Q v0) = gamma0 Q v0 := by
    dsimp [gamma0]
    exact reverse_ι v0
  rw [h_g0_rev, reverse_reverse]
  have hsq : gamma0 Q v0 * gamma0 Q v0 = 1 := gamma0_sq Q v0 hv0_norm
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, hsq, one_mul]
  simp only [mul_assoc]

/--
Естественият конус (Natural Cone) \mathcal{P} за стандартната форма на фон Нойман.
За крайномерния случай той се състои от "положителните" елементи X >= 0.
-/
def NaturalCone : Set (ClPlus Q) :=
  {X | ∃ Y : ClPlus Q, X = L_action Q Y (J_mod Q v0 Y)}

/-- 
Haagerup Axiom (1) & (2): Модулярната конюгация е инволюция.
J^2 = 1. Това е еквивалентно на J_mod (J_mod X) = X.
-/
theorem J_mod_involutive (hv0_norm : Q v0 = 1) (X : ClPlus Q) :
    J_mod Q v0 (J_mod Q v0 X) = X := by
  apply Subtype.ext
  dsimp [J_mod, hestenesAdjoint]
  rw [reverse.map_mul, reverse.map_mul]
  have h_g0_rev : reverse (gamma0 Q v0) = gamma0 Q v0 := by
    dsimp [gamma0]; exact reverse_ι v0
  rw [h_g0_rev, reverse_reverse]
  have hsq : gamma0 Q v0 * gamma0 Q v0 = 1 := gamma0_sq Q v0 hv0_norm
  simp only [mul_assoc]
  rw [← mul_assoc (gamma0 Q v0) (gamma0 Q v0), hsq, one_mul, mul_one]

/-- J_mod обръща L_action -/
theorem J_mod_L_action (hv0_norm : Q v0 = 1) (A Y : ClPlus Q) :
    J_mod Q v0 (L_action Q A Y) = R_action Q (J_mod Q v0 A) (J_mod Q v0 Y) := by
  apply Subtype.ext
  dsimp [J_mod, hestenesAdjoint, L_action, R_action]
  rw [reverse.map_mul]
  have hsq : gamma0 Q v0 * gamma0 Q v0 = 1 := gamma0_sq Q v0 hv0_norm
  simp only [mul_assoc]
  rw [← mul_assoc (gamma0 Q v0) (gamma0 Q v0), hsq, one_mul]

/-- 
Haagerup Axiom (3): J \xi = \xi за всяко \xi \in P.
Всяка матрица от естествения конус е самоспрегната относно модулярната конюгация.
-/
theorem J_mod_eq_self_of_naturalCone (hv0_norm : Q v0 = 1) (X : ClPlus Q) (hX : X ∈ NaturalCone Q v0) :
    J_mod Q v0 X = X := by
  rcases hX with ⟨Y, hY⟩
  rw [hY]
  rw [J_mod_L_action Q v0 hv0_norm Y (J_mod Q v0 Y)]
  rw [J_mod_involutive Q v0 hv0_norm Y]
  apply Subtype.ext
  dsimp [R_action, L_action]


/-- 
Haagerup Axiom (4): a J a J (P) \subseteq P за всяко a \in M.
В нашите термини, това е L_A \circ R_{A^\dagger} (което е coneConjugationAction),
което трябва да запазва NaturalCone.
-/
theorem coneConjugationAction_preserves_naturalCone (hv0_norm : Q v0 = 1) (A X : ClPlus Q) (hX : X ∈ NaturalCone Q v0) :
    L_action Q A (R_action Q (J_mod Q v0 A) X) ∈ NaturalCone Q v0 := by
  rcases hX with ⟨Y, hY⟩
  rw [hY]
  use L_action Q A Y
  -- Трябва да покажем: A * (Y * Y^dagger) * A^dagger = (A * Y) * (A * Y)^dagger
  apply Subtype.ext
  dsimp [L_action, R_action, J_mod, hestenesAdjoint]
  rw [reverse.map_mul]
  have hsq : gamma0 Q v0 * gamma0 Q v0 = 1 := gamma0_sq Q v0 hv0_norm
  simp only [mul_assoc]
  -- RHS: rev Y * rev A * g0
  -- LHS: rev Y * g0 * g0 * rev A * g0
  -- We just need to associate appropriately to cancel g0 * g0
  rw [← mul_assoc (gamma0 Q v0) (gamma0 Q v0)]
  rw [hsq]
  rw [one_mul]

/-- J_mod reverses multiplication -/
theorem J_mod_mul (hv0_norm : Q v0 = 1) (A B : ClPlus Q) :
    J_mod Q v0 (A * B) = J_mod Q v0 B * J_mod Q v0 A := by
  apply Subtype.ext
  dsimp [J_mod, hestenesAdjoint]
  change gamma0 Q v0 * reverse (A.val * B.val) * gamma0 Q v0 = 
         gamma0 Q v0 * reverse B.val * gamma0 Q v0 * (gamma0 Q v0 * reverse A.val * gamma0 Q v0)
  rw [reverse.map_mul]
  have hsq : gamma0 Q v0 * gamma0 Q v0 = 1 := gamma0_sq Q v0 hv0_norm
  simp only [mul_assoc]
  rw [← mul_assoc (gamma0 Q v0) (gamma0 Q v0), hsq, one_mul]

/--
The Tomita-Takesaki Modular Flow $\Delta^{it}$.
In the algebraic standard form, the continuous modular flow is generated by a 
Lorentz Boost Rotor $B_t$. The action is given by:
$\sigma_t(X) = B_t X B_t^\dagger$
Using our left and right actions, this is $L_{B_t} R_{B_t^\dagger} X$.
But we can also just write it as $B_t * X * J_{mod}(B_t)$.
-/
def ModularFlow (B_t : ClPlus Q) (X : ClPlus Q) : ClPlus Q :=
  B_t * X * J_mod Q v0 B_t

/--
The Fundamental Tomita Condition for the Modular Flow:
$J \Delta^{it} J = \Delta^{it}$
Since $J(B_t) = B_{-t}$, we prove the structural property that 
conjugating the flow action yields the invariant flow.
-/
theorem tomita_fundamental_condition (hv0_norm : Q v0 = 1) (B_t X : ClPlus Q) :
    J_mod Q v0 (ModularFlow Q v0 B_t (J_mod Q v0 X)) = ModularFlow Q v0 B_t X := by
  dsimp [ModularFlow]
  rw [J_mod_mul Q v0 hv0_norm, J_mod_mul Q v0 hv0_norm]
  rw [J_mod_involutive Q v0 hv0_norm B_t]
  rw [J_mod_involutive Q v0 hv0_norm X]
  -- LHS is now B_t * (X * J_mod B_t). We need (B_t * X) * J_mod B_t.
  apply Subtype.ext
  have h_val : (B_t * (X * J_mod Q v0 B_t)).val = B_t.val * (X.val * (J_mod Q v0 B_t).val) := rfl
  have h_val2 : (B_t * X * J_mod Q v0 B_t).val = (B_t.val * X.val) * (J_mod Q v0 B_t).val := rfl
  rw [h_val, h_val2]
  simp only [mul_assoc]

end InfoGeometry.Clifford.Hestenes
