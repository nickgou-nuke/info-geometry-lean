import Mathlib

/-!
# Algebraic Bogoliubov transport of CAR relations

The coefficients are complex scalars acting on an arbitrary associative
operator ring.  The result records preservation of the CAR identities; it
does not assert a state, a Hilbert-space representation, or an analytic
exponential.
-/

namespace InfoGeometry.OperatorAlgebra

section

variable {A : Type*} [Ring A] [Algebra ℂ A]

def thermalAnticommutator (x y : A) : A := x * y + y * x

def thermalAnnihilator (a d : A) (u v : ℂ) : A := u • a + v • d

def thermalCreator (c b : A) (u v : ℂ) : A := u • c + v • b

omit [Algebra ℂ A] in
theorem thermalAnticommutator_map
    {B : Type*} [Ring B]
    (φ : A →+* B) (x y : A) :
    φ (thermalAnticommutator x y) =
      thermalAnticommutator (φ x) (φ y) := by
  simp [thermalAnticommutator]

theorem thermalAnnihilator_map
    {B : Type*} [Ring B] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) (a d : A) (u v : ℂ) :
    φ (thermalAnnihilator a d u v) =
      thermalAnnihilator (φ a) (φ d) u v := by
  simp [thermalAnnihilator]

theorem thermalCreator_map
    {B : Type*} [Ring B] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) (c b : A) (u v : ℂ) :
    φ (thermalCreator c b u v) =
      thermalCreator (φ c) (φ b) u v := by
  simp [thermalCreator]

omit [Algebra ℂ A] in
lemma thermalAnticommutator_symm (x y : A) :
    thermalAnticommutator x y = thermalAnticommutator y x := by
  dsimp [thermalAnticommutator]
  exact add_comm _ _

lemma thermalAnticommutator_expand (x₁ x₂ y₁ y₂ : A) (c₁ c₂ d₁ d₂ : ℂ) :
    thermalAnticommutator (c₁ • x₁ + c₂ • x₂) (d₁ • y₁ + d₂ • y₂) =
      (c₁ * d₁) • thermalAnticommutator x₁ y₁ +
        (c₁ * d₂) • thermalAnticommutator x₁ y₂ +
        (c₂ * d₁) • thermalAnticommutator x₂ y₁ +
        (c₂ * d₂) • thermalAnticommutator x₂ y₂ := by
  dsimp [thermalAnticommutator]
  simp only [mul_add, add_mul, smul_add, smul_smul,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  rw [mul_comm d₁ c₁, mul_comm d₁ c₂, mul_comm d₂ c₁, mul_comm d₂ c₂]
  abel

theorem thermal_bogoliubov_nilpotent_ann
    (a d : A) (u v : ℂ)
    (haa : thermalAnticommutator a a = 0)
    (hdd : thermalAnticommutator d d = 0)
    (had : thermalAnticommutator a d = 0) :
    thermalAnticommutator (thermalAnnihilator a d u v)
      (thermalAnnihilator a d u v) = 0 := by
  dsimp [thermalAnnihilator]
  rw [thermalAnticommutator_expand, haa, hdd, had]
  have hda : thermalAnticommutator d a = 0 := by
    rw [thermalAnticommutator_symm, had]
  rw [hda]
  simp

theorem thermal_bogoliubov_nilpotent_cre
    (c b : A) (u v : ℂ)
    (hcc : thermalAnticommutator c c = 0)
    (hbb : thermalAnticommutator b b = 0)
    (hcb : thermalAnticommutator c b = 0) :
    thermalAnticommutator (thermalCreator c b u v)
      (thermalCreator c b u v) = 0 := by
  dsimp [thermalCreator]
  rw [thermalAnticommutator_expand, hcc, hbb, hcb]
  have hbc : thermalAnticommutator b c = 0 := by
    rw [thermalAnticommutator_symm, hcb]
  rw [hbc]
  simp

theorem thermal_bogoliubov_car_preserved
    (a c b d : A) (u v : ℂ)
    (huv : u ^ 2 + v ^ 2 = 1)
    (hac : thermalAnticommutator a c = 1)
    (hbd : thermalAnticommutator b d = 1)
    (hab : thermalAnticommutator a b = 0)
    (hcd : thermalAnticommutator c d = 0) :
    thermalAnticommutator (thermalAnnihilator a d u v)
      (thermalCreator c b u v) = 1 := by
  dsimp [thermalAnnihilator, thermalCreator]
  rw [thermalAnticommutator_expand, hac, hab]
  have hdb : thermalAnticommutator d b = 1 := by
    rw [thermalAnticommutator_symm, hbd]
  have hdc : thermalAnticommutator d c = 0 := by
    rw [thermalAnticommutator_symm, hcd]
  rw [hdb, hdc]
  simp only [smul_zero, add_zero]
  rw [← add_smul, show u * u = u ^ 2 by ring, show v * v = v ^ 2 by ring,
    huv, one_smul]

theorem AlgHom.map_thermal_bogoliubov_car_preserved
    {B : Type*} [Ring B] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) (a c b d : A) (u v : ℂ)
    (huv : u ^ 2 + v ^ 2 = 1)
    (hac : thermalAnticommutator a c = 1)
    (hbd : thermalAnticommutator b d = 1)
    (hab : thermalAnticommutator a b = 0)
    (hcd : thermalAnticommutator c d = 0) :
    thermalAnticommutator
        (thermalAnnihilator (φ a) (φ d) u v)
        (thermalCreator (φ c) (φ b) u v) = 1 := by
  apply thermal_bogoliubov_car_preserved (φ a) (φ c) (φ b) (φ d) u v huv
  · calc
      thermalAnticommutator (φ a) (φ c) =
          φ (thermalAnticommutator a c) :=
        (thermalAnticommutator_map φ.toRingHom a c).symm
      _ = φ 1 := by rw [hac]
      _ = 1 := map_one φ
  · calc
      thermalAnticommutator (φ b) (φ d) =
          φ (thermalAnticommutator b d) :=
        (thermalAnticommutator_map φ.toRingHom b d).symm
      _ = φ 1 := by rw [hbd]
      _ = 1 := map_one φ
  · calc
      thermalAnticommutator (φ a) (φ b) =
          φ (thermalAnticommutator a b) :=
        (thermalAnticommutator_map φ.toRingHom a b).symm
      _ = φ 0 := by rw [hab]
      _ = 0 := map_zero φ
  · calc
      thermalAnticommutator (φ c) (φ d) =
          φ (thermalAnticommutator c d) :=
        (thermalAnticommutator_map φ.toRingHom c d).symm
      _ = φ 0 := by rw [hcd]
      _ = 0 := map_zero φ

end

end InfoGeometry.OperatorAlgebra
