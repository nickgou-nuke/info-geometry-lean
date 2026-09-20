import Mathlib

namespace InfoGeometry.HodgeCohomology.TwistedCubic

noncomputable section

variable {Scalar : Type*} [Field Scalar]

def parameter (first second : Scalar) : Fin 4 → Scalar :=
  ![first ^ 3, first ^ 2 * second, first * second ^ 2, second ^ 3]

def OnCurve (point : Fin 4 → Scalar) : Prop :=
  point 0 * point 2 = point 1 * point 1 ∧
    point 0 * point 3 = point 1 * point 2 ∧
    point 1 * point 3 = point 2 * point 2

def quadric (left right otherLeft otherRight : Fin 4) : MvPolynomial (Fin 4) Scalar :=
  MvPolynomial.X left * MvPolynomial.X right -
    MvPolynomial.X otherLeft * MvPolynomial.X otherRight

theorem quadric_homogeneous (left right otherLeft otherRight : Fin 4) :
    (quadric (Scalar := Scalar) left right otherLeft otherRight).IsHomogeneous 2 := by
  exact ((MvPolynomial.isHomogeneous_X Scalar left).mul
    (MvPolynomial.isHomogeneous_X Scalar right)).sub
      ((MvPolynomial.isHomogeneous_X Scalar otherLeft).mul
        (MvPolynomial.isHomogeneous_X Scalar otherRight))

theorem onCurve_iff_quadrics (point : Fin 4 → Scalar) :
    OnCurve point ↔
      MvPolynomial.eval point (quadric 0 2 1 1) = 0 ∧
      MvPolynomial.eval point (quadric 0 3 1 2) = 0 ∧
      MvPolynomial.eval point (quadric 1 3 2 2) = 0 := by
  simp [OnCurve, quadric, sub_eq_zero]

theorem parameter_onCurve (first second : Scalar) : OnCurve (parameter first second) := by
  constructor
  · change first ^ 3 * (first * second ^ 2) = (first ^ 2 * second) * (first ^ 2 * second)
    ring
  constructor
  · change first ^ 3 * second ^ 3 = (first ^ 2 * second) * (first * second ^ 2)
    ring
  · change (first ^ 2 * second) * second ^ 3 = (first * second ^ 2) * (first * second ^ 2)
    ring

theorem parameter_nonzero (first second : Scalar) (nonzero : first ≠ 0 ∨ second ≠ 0) :
    parameter first second ≠ 0 := by
  intro equality
  rcases nonzero with firstNonzero | secondNonzero
  · have entry := congrArg (fun point : Fin 4 → Scalar => point 0) equality
    have powerZero : first ^ 3 = 0 := by simpa [parameter] using entry
    exact pow_ne_zero 3 firstNonzero powerZero
  · have entry := congrArg (fun point : Fin 4 → Scalar => point 3) equality
    have powerZero : second ^ 3 = 0 := by simpa [parameter] using entry
    exact pow_ne_zero 3 secondNonzero powerZero

theorem parameter_scale (scale first second : Scalar) :
    parameter (scale * first) (scale * second) = scale ^ 3 • parameter first second := by
  ext coordinate
  fin_cases coordinate <;> simp [parameter] <;> ring

theorem scaled_relation (scale left right otherLeft otherRight : Scalar)
    (relation : left * right = otherLeft * otherRight) :
    (scale * left) * (scale * right) = (scale * otherLeft) * (scale * otherRight) := by
  calc
    _ = scale ^ 2 * (left * right) := by ring
    _ = scale ^ 2 * (otherLeft * otherRight) := by rw [relation]
    _ = _ := by ring

theorem onCurve_smul (scale : Scalar) (point : Fin 4 → Scalar)
    (onCurve : OnCurve point) : OnCurve (scale • point) := by
  exact ⟨scaled_relation scale _ _ _ _ onCurve.1,
    scaled_relation scale _ _ _ _ onCurve.2.1,
    scaled_relation scale _ _ _ _ onCurve.2.2⟩

theorem onCurve_smul_iff (scale : Scalar) (nonzero : scale ≠ 0)
    (point : Fin 4 → Scalar) : OnCurve (scale • point) ↔ OnCurve point := by
  constructor
  · intro onCurve
    have unscaled := onCurve_smul scale⁻¹ (scale • point) onCurve
    simpa [smul_smul, nonzero] using unscaled
  · exact onCurve_smul scale point

theorem zero_patch (point : Fin 4 → Scalar) (onCurve : OnCurve point)
    (firstZero : point 0 = 0) :
    point = point 3 • parameter 0 1 := by
  have secondSquare : point 1 * point 1 = 0 := by
    simpa [firstZero] using onCurve.1.symm
  have secondZero : point 1 = 0 := (mul_eq_zero.mp secondSquare).elim id id
  have thirdSquare : point 2 * point 2 = 0 := by
    simpa [secondZero] using onCurve.2.2.symm
  have thirdZero : point 2 = 0 := (mul_eq_zero.mp thirdSquare).elim id id
  ext coordinate
  fin_cases coordinate <;> simp [parameter, firstZero, secondZero, thirdZero]

theorem nonzero_patch (point : Fin 4 → Scalar) (onCurve : OnCurve point)
    (firstNonzero : point 0 ≠ 0) :
    point = point 0 • parameter 1 (point 1 / point 0) := by
  have third : point 2 = (point 1 * point 1) / point 0 := by
    apply (eq_div_iff firstNonzero).mpr
    simpa only [mul_comm] using onCurve.1
  have fourth : point 3 = (point 1 * point 2) / point 0 := by
    apply (eq_div_iff firstNonzero).mpr
    simpa only [mul_comm] using onCurve.2.1
  ext coordinate
  fin_cases coordinate <;> simp [parameter, fourth, third] <;>
    field_simp [firstNonzero] <;> ring

theorem projective_parameterization (point : Fin 4 → Scalar)
    (nonzero : point ≠ 0) (onCurve : OnCurve point) :
    ∃ first second : Scalar, ∃ parameterNonzero : parameter first second ≠ 0,
      Projectivization.mk Scalar point nonzero =
        Projectivization.mk Scalar (parameter first second) parameterNonzero := by
  by_cases firstZero : point 0 = 0
  · refine ⟨0, 1, parameter_nonzero 0 1 (Or.inr one_ne_zero), ?_⟩
    apply (Projectivization.mk_eq_mk_iff' Scalar _ _ _ _).mpr
    exact ⟨point 3, (zero_patch point onCurve firstZero).symm⟩
  · refine ⟨1, point 1 / point 0,
      parameter_nonzero 1 _ (Or.inl one_ne_zero), ?_⟩
    apply (Projectivization.mk_eq_mk_iff' Scalar _ _ _ _).mpr
    exact ⟨point 0, (nonzero_patch point onCurve firstZero).symm⟩

theorem onCurve_iff_projective_parameterized (point : Fin 4 → Scalar)
    (nonzero : point ≠ 0) :
    OnCurve point ↔
      ∃ first second : Scalar, ∃ parameterNonzero : parameter first second ≠ 0,
        Projectivization.mk Scalar point nonzero =
          Projectivization.mk Scalar (parameter first second) parameterNonzero := by
  constructor
  · exact projective_parameterization point nonzero
  · rintro ⟨first, second, parameterNonzero, equality⟩
    obtain ⟨scale, scaled⟩ :=
      (Projectivization.mk_eq_mk_iff' Scalar _ _ _ _).mp equality
    rw [← scaled]
    exact onCurve_smul scale _ (parameter_onCurve first second)

theorem two_quadrics_decompose (point : Fin 4 → Scalar) :
    (point 0 * point 2 = point 1 * point 1 ∧
      point 0 * point 3 = point 1 * point 2) ↔
    OnCurve point ∨ (point 0 = 0 ∧ point 1 = 0) := by
  constructor
  · intro equations
    by_cases firstZero : point 0 = 0
    · right
      refine ⟨firstZero, ?_⟩
      have squareZero : point 1 * point 1 = 0 := by
        simpa [firstZero] using equations.1.symm
      exact (mul_eq_zero.mp squareZero).elim id id
    · left
      refine ⟨equations.1, equations.2, ?_⟩
      have factored : point 0 * (point 1 * point 3 - point 2 * point 2) = 0 := by
        calc
          _ = point 1 * (point 0 * point 3 - point 1 * point 2) -
              point 2 * (point 0 * point 2 - point 1 * point 1) := by ring
          _ = 0 := by rw [equations.1, equations.2]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp factored).resolve_left firstZero)
  · rintro (onCurve | onLine)
    · exact ⟨onCurve.1, onCurve.2.1⟩
    · simp [onLine.1, onLine.2]

end

end InfoGeometry.HodgeCohomology.TwistedCubic
