import InfoGeometry.Clifford.HestenesLorentzJordanCone

namespace InfoGeometry.Clifford.Hestenes

open CliffordAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M) (hv0_norm : Q v0 = 1)
variable (hsq : gamma0 Q v0 * gamma0 Q v0 = 1)

/-- 
Стереоскопичното алгебрично действие (Standard-form stereoscopy).
Ляво действие L_A(X) = A * X.
-/
def L_action (A X : ClPlus Q) : ClPlus Q :=
  ⟨A.val * X.val, sorry⟩

/-- 
Стереоскопичното алгебрично действие.
Дясно действие R_B(X) = X * B.
Това е еквивалентът на комутанта M'.
-/
def R_action (B X : ClPlus Q) : ClPlus Q :=
  ⟨X.val * B.val, sorry⟩

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
  sorry

/--
Естественият конус (Natural Cone) \mathcal{P} за стандартната форма на фон Нойман.
За крайномерния случай той се състои от "положителните" елементи X >= 0.
-/
def NaturalCone : Set (ClPlus Q) :=
  -- В пълната теория тук бихме изисквали X да има форма Y * J_mod Y за някакво Y, 
  -- или еквивалентно да е Ермитов и положително дефинитен.
  {X | ∃ Y : ClPlus Q, X = L_action Q Y (J_mod Q v0 Y)}

end InfoGeometry.Clifford.Hestenes
