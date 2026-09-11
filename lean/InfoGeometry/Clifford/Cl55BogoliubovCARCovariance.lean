import InfoGeometry.Clifford.Cl55CAROperatorTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Concrete Bogoliubov covariance of the `Cl(5,5)` CAR carrier

This owner uses the already constructed real left-action operators on the
native `Cl(5,5)` carrier.  The coefficients are real, so the statement is an
algebraic CAR theorem on `Module.End ℝ Cl55`; no Hilbert-space implementer,
state, or C*-completion is asserted here.

For distinct modes `i` and `j`, the pair

`a_i^B = u a_i + v a_j†`, `a_i^{B†} = u a_i† + v a_j`

preserves the CAR when `u² + v² = 1`.  Spin transport of this mixed pair is
left as a separate covariance consumer.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Optics.OperatorLiftCarrier

abbrev RealCAROperator := Cl55Operator

def realBogoliubovAnnihilator
    (a d : RealCAROperator) (u v : ℝ) : RealCAROperator :=
  u • a + v • d

def realBogoliubovCreator
    (c b : RealCAROperator) (u v : ℝ) : RealCAROperator :=
  u • c + v • b

def realAnticommutator (x y : RealCAROperator) : RealCAROperator :=
  x * y + y * x

@[simp] theorem realAnticommutator_comm (x y : RealCAROperator) :
    realAnticommutator x y = realAnticommutator y x := by
  simp [realAnticommutator, add_comm]

theorem realAnticommutator_expand
    (x₁ x₂ y₁ y₂ : RealCAROperator) (c₁ c₂ d₁ d₂ : ℝ) :
    realAnticommutator (c₁ • x₁ + c₂ • x₂) (d₁ • y₁ + d₂ • y₂) =
      (c₁ * d₁) • realAnticommutator x₁ y₁ +
        (c₁ * d₂) • realAnticommutator x₁ y₂ +
        (c₂ * d₁) • realAnticommutator x₂ y₁ +
        (c₂ * d₂) • realAnticommutator x₂ y₂ := by
  unfold realAnticommutator
  simp only [mul_add, add_mul, smul_add, smul_smul,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  rw [mul_comm d₁ c₁, mul_comm d₁ c₂, mul_comm d₂ c₁, mul_comm d₂ c₂]
  abel_nf

theorem real_bogoliubov_car_preserved
    (a c b d : RealCAROperator) (u v : ℝ)
    (huv : u ^ 2 + v ^ 2 = 1)
    (hac : realAnticommutator a c = 1)
    (hbd : realAnticommutator b d = 1)
    (hab : realAnticommutator a b = 0)
    (hcd : realAnticommutator c d = 0) :
    realAnticommutator
        (realBogoliubovAnnihilator a d u v)
        (realBogoliubovCreator c b u v) = 1 := by
  have hba : realAnticommutator b a = 0 := by
    simpa [realAnticommutator, add_comm] using hab
  have hdc : realAnticommutator d c = 0 := by
    simpa [realAnticommutator, add_comm] using hcd
  have hca : realAnticommutator c a = 1 := by
    simpa [realAnticommutator, add_comm] using hac
  have hdb : realAnticommutator d b = 1 := by
    simpa [realAnticommutator, add_comm] using hbd
  change realAnticommutator (u • a + v • d) (u • c + v • b) = 1
  rw [realAnticommutator_expand]
  simp only [hac, hdb, hab, hdc, smul_zero, add_zero]
  rw [← add_smul, show u * u = u ^ 2 by ring,
    show v * v = v ^ 2 by ring, huv, one_smul]

theorem real_bogoliubov_car_preserved_reverse
    (a c b d : RealCAROperator) (u v : ℝ)
    (huv : u ^ 2 + v ^ 2 = 1)
    (hac : realAnticommutator a c = 1)
    (hbd : realAnticommutator b d = 1)
    (hab : realAnticommutator a b = 0)
    (hcd : realAnticommutator c d = 0) :
    realAnticommutator
        (realBogoliubovCreator c b u v)
        (realBogoliubovAnnihilator a d u v) = 1 := by
  simpa [realAnticommutator_comm] using
    real_bogoliubov_car_preserved a c b d u v huv hac hbd hab hcd

theorem real_bogoliubov_annihilator_nilpotent
    (a d : RealCAROperator) (u v : ℝ)
    (haa : realAnticommutator a a = 0)
    (hdd : realAnticommutator d d = 0)
    (had : realAnticommutator a d = 0) :
    realAnticommutator
        (realBogoliubovAnnihilator a d u v)
        (realBogoliubovAnnihilator a d u v) = 0 := by
  have hda : realAnticommutator d a = 0 := by
    simpa [realAnticommutator, add_comm] using had
  change realAnticommutator (u • a + v • d) (u • a + v • d) = 0
  rw [realAnticommutator_expand, haa, hdd, had, hda]
  simp

theorem real_bogoliubov_creator_nilpotent
    (c b : RealCAROperator) (u v : ℝ)
    (hcc : realAnticommutator c c = 0)
    (hbb : realAnticommutator b b = 0)
    (hcb : realAnticommutator c b = 0) :
    realAnticommutator
        (realBogoliubovCreator c b u v)
        (realBogoliubovCreator c b u v) = 0 := by
  have hbc : realAnticommutator b c = 0 := by
    simpa [realAnticommutator, add_comm] using hcb
  change realAnticommutator (u • c + v • b) (u • c + v • b) = 0
  rw [realAnticommutator_expand, hcc, hbb, hcb, hbc]
  simp

def cl55BogoliubovAnnihilator
    (i j : Fin 5) (u v : ℝ) : RealCAROperator :=
  realBogoliubovAnnihilator
    (leftAction55 (annihilation55 i))
    (leftAction55 (creation55 j)) u v

def cl55BogoliubovCreator
    (i j : Fin 5) (u v : ℝ) : RealCAROperator :=
  realBogoliubovCreator
    (leftAction55 (creation55 i))
    (leftAction55 (annihilation55 j)) u v

theorem spinTransport_realBogoliubovAnnihilator_apply
    (g : Spin55) (a d : Cl55) (u v : ℝ) (x : Cl55) :
    spinCARAutomorphism g
        (realBogoliubovAnnihilator (leftAction55 a) (leftAction55 d) u v x) =
      realBogoliubovAnnihilator
        (leftAction55 (spinCARAutomorphism g a))
        (leftAction55 (spinCARAutomorphism g d)) u v
        (spinCARAutomorphism g x) := by
  dsimp [realBogoliubovAnnihilator, spinCARAutomorphism, spinCliffordRingEquiv, leftAction55]
  rw [InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_add,
      InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_smul,
      InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_smul,
      InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_mul,
      InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_mul]

theorem spinTransport_realBogoliubovCreator_apply
    (g : Spin55) (c b : Cl55) (u v : ℝ) (x : Cl55) :
    spinCARAutomorphism g
        (realBogoliubovCreator (leftAction55 c) (leftAction55 b) u v x) =
      realBogoliubovCreator
        (leftAction55 (spinCARAutomorphism g c))
        (leftAction55 (spinCARAutomorphism g b)) u v
        (spinCARAutomorphism g x) := by
  dsimp [realBogoliubovCreator, spinCARAutomorphism, spinCliffordRingEquiv, leftAction55]
  rw [InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_add,
      InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_smul,
      InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_smul,
      InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_mul,
      InfoGeometry.Clifford.ChiralLorentzCARLift.unitConjugation_mul]

theorem realAnticommutator_leftAction (x y : Cl55) :
    realAnticommutator (leftAction55 x) (leftAction55 y) =
      leftAction55 (x * y + y * x) := by
  unfold realAnticommutator
  rw [leftAction55_add, leftAction55_mul, leftAction55_mul]

theorem cl55_leftAction_annihilation_anticommutator
    (i j : Fin 5) :
    realAnticommutator
        (leftAction55 (annihilation55 i))
        (leftAction55 (annihilation55 j)) = 0 := by
  rw [realAnticommutator_leftAction]
  simpa [leftAction55_zero] using
    congrArg leftAction55 (annihilation55_anticommutator i j)

theorem cl55_leftAction_creation_anticommutator
    (i j : Fin 5) :
    realAnticommutator
        (leftAction55 (creation55 i))
        (leftAction55 (creation55 j)) = 0 := by
  rw [realAnticommutator_leftAction]
  simpa [leftAction55_zero] using
    congrArg leftAction55 (creation55_anticommutator i j)

theorem cl55_leftAction_bogoliubov_car_preserved
    (i j : Fin 5) (u v : ℝ) (huv : u ^ 2 + v ^ 2 = 1) :
    realAnticommutator
        (cl55BogoliubovAnnihilator i j u v)
        (cl55BogoliubovCreator i j u v) = 1 := by
  apply real_bogoliubov_car_preserved
    (leftAction55 (annihilation55 i))
    (leftAction55 (creation55 i))
    (leftAction55 (annihilation55 j))
    (leftAction55 (creation55 j)) u v huv
  · exact cl55CAR_leftAction_anticommutator i
  · exact cl55CAR_leftAction_anticommutator j
  · exact cl55_leftAction_annihilation_anticommutator i j
  · exact cl55_leftAction_creation_anticommutator i j

theorem cl55_leftAction_bogoliubov_isCARPair
    {i j : Fin 5} (hij : i ≠ j) (u v : ℝ)
    (huv : u ^ 2 + v ^ 2 = 1) :
    realAnticommutator
        (cl55BogoliubovAnnihilator i j u v)
        (cl55BogoliubovAnnihilator i j u v) = 0 ∧
      realAnticommutator
        (cl55BogoliubovCreator i j u v)
        (cl55BogoliubovCreator i j u v) = 0 ∧
      realAnticommutator
        (cl55BogoliubovAnnihilator i j u v)
        (cl55BogoliubovCreator i j u v) = 1 := by
  have h_ann_sq : realAnticommutator
      (leftAction55 (annihilation55 i))
      (leftAction55 (annihilation55 i)) = 0 := by
    rw [realAnticommutator_leftAction]
    simp [annihilation55_sq, leftAction55_zero]
  have h_cre_sq : realAnticommutator
      (leftAction55 (creation55 j))
      (leftAction55 (creation55 j)) = 0 := by
    rw [realAnticommutator_leftAction]
    simp [creation55_sq, leftAction55_zero]
  have h_cross_ann_cre : realAnticommutator
      (leftAction55 (annihilation55 i))
      (leftAction55 (creation55 j)) = 0 := by
    exact cl55CAR_leftAction_anticommutator_offdiag i j hij
  have h_cre_sq_i : realAnticommutator
      (leftAction55 (creation55 i))
      (leftAction55 (creation55 i)) = 0 := by
    rw [realAnticommutator_leftAction]
    simp [creation55_sq, leftAction55_zero]
  have h_ann_sq_j : realAnticommutator
      (leftAction55 (annihilation55 j))
      (leftAction55 (annihilation55 j)) = 0 := by
    rw [realAnticommutator_leftAction]
    simp [annihilation55_sq, leftAction55_zero]
  have h_cross_cre_ann : realAnticommutator
      (leftAction55 (creation55 i))
      (leftAction55 (annihilation55 j)) = 0 := by
    simpa [realAnticommutator, add_comm] using
      cl55CAR_leftAction_anticommutator_offdiag j i hij.symm
  refine ⟨?_, ?_, cl55_leftAction_bogoliubov_car_preserved i j u v huv⟩
  · exact real_bogoliubov_annihilator_nilpotent _ _ u v
      h_ann_sq h_cre_sq h_cross_ann_cre
  · exact real_bogoliubov_creator_nilpotent _ _ u v
      h_cre_sq_i h_ann_sq_j h_cross_cre_ann

theorem cl55_leftAction_bogoliubov_car_preserved_reverse
    (i j : Fin 5) (u v : ℝ) (huv : u ^ 2 + v ^ 2 = 1) :
    realAnticommutator
        (cl55BogoliubovCreator i j u v)
        (cl55BogoliubovAnnihilator i j u v) = 1 := by
  simpa [cl55BogoliubovAnnihilator, cl55BogoliubovCreator] using
    real_bogoliubov_car_preserved_reverse
      (leftAction55 (annihilation55 i))
      (leftAction55 (creation55 i))
      (leftAction55 (annihilation55 j))
      (leftAction55 (creation55 j)) u v huv
      (cl55CAR_leftAction_anticommutator i)
      (cl55CAR_leftAction_anticommutator j)
      (cl55_leftAction_annihilation_anticommutator i j)
      (cl55_leftAction_creation_anticommutator i j)

end InfoGeometry.Clifford.Clifford55
