structure ChiralDoubledScalarBasis where
  left : ℝ
  right : ℝ
  total : ℝ
  exchange : ℝ
  total_eq_left_add_right : total = left + right
  exchange_eq_left_sub_right : exchange = left - right

namespace ChiralDoubledScalarBasis

/-- The doubled total channel is the sum of the chiral channels. -/
theorem total_eq (B : ChiralDoubledScalarBasis) :
    B.total = B.left + B.right :=
  B.total_eq_left_add_right

/-- The doubled exchange channel is the left-minus-right chiral channel. -/
theorem exchange_eq (B : ChiralDoubledScalarBasis) :
    B.exchange = B.left - B.right :=
  B.exchange_eq_left_sub_right

/-- Left/right equality is equivalent to vanishing doubled exchange. -/
theorem exchange_eq_zero_iff_left_eq_right
    (B : ChiralDoubledScalarBasis) :
    B.exchange = 0 ↔ B.left = B.right := by
  rw [B.exchange_eq]
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    rw [h]
    simp

end ChiralDoubledScalarBasis

/--
Scalar involution-adapted split.

Each pair is a plus/minus decomposition for one organizing involution:

* regular/defect: Penrose/Drazin separation;
* compact/noncompact: Cartan split;
* reversible/dissipative: metriplectic split.
-/
structure InvolutionAdaptedScalarSplit where
  regular : ℝ
  defect : ℝ
  compact : ℝ
  noncompact : ℝ
  reversible : ℝ
  dissipative : ℝ
  regularDefectTotal : ℝ
  cartanTotal : ℝ
  flowTotal : ℝ
  regularDefectTotal_eq : regularDefectTotal = regular + defect
  cartanTotal_eq : cartanTotal = compact + noncompact
  flowTotal_eq : flowTotal = reversible + dissipative

namespace InvolutionAdaptedScalarSplit

/-- The Drazin/Penrose shadow splits into regular and defect channels. -/
theorem regularDefectTotal_eq_add
    (S : InvolutionAdaptedScalarSplit) :
    S.regularDefectTotal = S.regular + S.defect :=
  S.regularDefectTotal_eq

/-- The Cartan shadow splits into compact and noncompact channels. -/
theorem cartanTotal_eq_add
    (S : InvolutionAdaptedScalarSplit) :
    S.cartanTotal = S.compact + S.noncompact :=
  S.cartanTotal_eq

/-- The metriplectic shadow splits into reversible and dissipative channels. -/
theorem flowTotal_eq_add
    (S : InvolutionAdaptedScalarSplit) :
    S.flowTotal = S.reversible + S.dissipative :=
  S.flowTotal_eq

/-- If the defect coordinate vanishes, the regular/defect total is regular. -/
theorem regularDefectTotal_eq_regular_of_defect_zero
    (S : InvolutionAdaptedScalarSplit)
    (h : S.defect = 0) :
    S.regularDefectTotal = S.regular := by
  rw [S.regularDefectTotal_eq, h]
  simp

/-- If the dissipative coordinate vanishes, the flow total is reversible. -/
theorem flowTotal_eq_reversible_of_dissipative_zero