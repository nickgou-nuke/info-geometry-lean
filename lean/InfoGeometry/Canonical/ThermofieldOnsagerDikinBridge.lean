import InfoGeometry.Jordan.LogDet

/-!
# Thermofield connection difference, Onsager splitting, and Dikin mobility

This finite owner closes the algebraic prerequisite for interpreting a
forward/backward connection difference as a dissipative response.

For two real finite connection matrices `Γ⁺, Γ⁻`, the difference

`Γdiff = Γ⁺ - Γ⁻`

is decomposed canonically into its symmetric Onsager part and skew Casimir part.
The skew part contributes exactly zero to every diagonal quadratic form, so the
sign of `xᵀ Γdiff x` is controlled entirely by the symmetric part.

A second layer identifies the symmetric mobility with the inverse of an existing
`InfoGeometry.Jordan.SPD` Hessian metric. Mathlib's native `Matrix.PosDef.inv`
theorem then supplies positivity of the inverse directly; no invertibility axiom
or proof-wrapper field is introduced.

The resulting quadratic quantity is called `entropyProduction` only after an
explicit `IsOnsagerDissipative` hypothesis. The theorem does not identify an
arbitrary connection difference with physical entropy production, nor does it
assert a GENERIC, GKSL, or hydrodynamic constitutive law.
-/

noncomputable section

open Matrix

namespace InfoGeometry.Canonical.ThermofieldOnsagerDikinBridge

variable {n : ℕ}

/-- A finite forward/backward pair of real connection coefficients. -/
structure DoubledConnection (n : ℕ) where
  gammaPlus : Matrix (Fin n) (Fin n) ℝ
  gammaMinus : Matrix (Fin n) (Fin n) ℝ

namespace DoubledConnection

/-- Average branch connection. This is kinematic data only. -/
def gammaSum (Γ : DoubledConnection n) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (Γ.gammaPlus + Γ.gammaMinus)

/-- Forward-minus-backward connection difference. -/
def gammaDiff (Γ : DoubledConnection n) : Matrix (Fin n) (Fin n) ℝ :=
  Γ.gammaPlus - Γ.gammaMinus

/-- Symmetric part of the branch difference. -/
def onsagerTensor (Γ : DoubledConnection n) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (Γ.gammaDiff + Γ.gammaDiff.transpose)

/-- Skew part of the branch difference. -/
def casimirTensor (Γ : DoubledConnection n) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (Γ.gammaDiff - Γ.gammaDiff.transpose)

/-- The symmetric part satisfies Onsager reciprocity identically. -/
theorem onsagerTensor_transpose (Γ : DoubledConnection n) :
    Γ.onsagerTensor.transpose = Γ.onsagerTensor := by
  ext i j
  simp [onsagerTensor, Matrix.transpose_apply]
  ring

/-- The complementary part is skew-symmetric identically. -/
theorem casimirTensor_transpose (Γ : DoubledConnection n) :
    Γ.casimirTensor.transpose = -Γ.casimirTensor := by
  ext i j
  simp [casimirTensor, Matrix.transpose_apply]
  ring

/-- Exact symmetric/skew reconstruction of the connection difference. -/
theorem gammaDiff_eq_onsager_add_casimir (Γ : DoubledConnection n) :
    Γ.gammaDiff = Γ.onsagerTensor + Γ.casimirTensor := by
  ext i j
  simp [onsagerTensor, casimirTensor]
  ring

end DoubledConnection

/-- Diagonal quadratic response of a real matrix. -/
def quadraticResponse
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  dotProduct x (A *ᵥ x)

/-- Transposition leaves a diagonal real quadratic form unchanged. -/
theorem quadraticResponse_transpose
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadraticResponse A.transpose x = quadraticResponse A x := by
  unfold quadraticResponse
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_transpose]
  exact dotProduct_comm _ _

/-- A skew-symmetric real matrix contributes no diagonal quadratic response. -/
theorem skew_quadraticResponse_zero
    (W : Matrix (Fin n) (Fin n) ℝ)
    (hW : W.transpose = -W)
    (x : Fin n → ℝ) :
    quadraticResponse W x = 0 := by
  have h := quadraticResponse_transpose W x
  rw [hW] at h
  simp [quadraticResponse, Matrix.neg_mulVec, dotProduct_neg] at h
  linarith

/-- The branch-difference quadratic form depends only on its symmetric
Onsager component. -/
theorem gammaDiff_quadraticResponse_eq_onsager
    (Γ : DoubledConnection n) (x : Fin n → ℝ) :
    quadraticResponse Γ.gammaDiff x =
      quadraticResponse Γ.onsagerTensor x := by
  rw [Γ.gammaDiff_eq_onsager_add_casimir]
  have hskew :=
    skew_quadraticResponse_zero Γ.casimirTensor Γ.casimirTensor_transpose x
  unfold quadraticResponse at hskew ⊢
  rw [Matrix.add_mulVec, dotProduct_add, hskew, add_zero]

/-- The precise finite second-law hypothesis: the symmetric response is positive
semidefinite as a quadratic form. -/
def IsOnsagerDissipative (Γ : DoubledConnection n) : Prop :=
  ∀ x : Fin n → ℝ, 0 ≤ quadraticResponse Γ.onsagerTensor x

/-- Once dissipativity is supplied, the full branch-difference quadratic
response is nonnegative. -/
theorem branchDifference_nonneg_of_onsager
    (Γ : DoubledConnection n)
    (hΓ : IsOnsagerDissipative Γ)
    (x : Fin n → ℝ) :
    0 ≤ quadraticResponse Γ.gammaDiff x := by
  rw [gammaDiff_quadraticResponse_eq_onsager]
  exact hΓ x

/-- Thermodynamic entropy-production readout. Its nonnegativity is not built
into the definition; it follows only under `IsOnsagerDissipative`. -/
def entropyProduction (Γ : DoubledConnection n) (x : Fin n → ℝ) : ℝ :=
  quadraticResponse Γ.gammaDiff x

/-- Finite second-law theorem under the explicit Onsager positivity condition. -/
theorem entropyProduction_nonneg
    (Γ : DoubledConnection n)
    (hΓ : IsOnsagerDissipative Γ)
    (x : Fin n → ℝ) :
    0 ≤ entropyProduction Γ x := by
  exact branchDifference_nonneg_of_onsager Γ hΓ x

/-- If the two branches coincide, the difference response vanishes identically. -/
theorem reversible_branch_entropyProduction_zero
    (Γ : DoubledConnection n)
    (hrev : Γ.gammaPlus = Γ.gammaMinus)
    (x : Fin n → ℝ) :
    entropyProduction Γ x = 0 := by
  simp [entropyProduction, quadraticResponse, DoubledConnection.gammaDiff, hrev]

/-! ## Koszul--Vinberg / Dikin compatibility -/

/-- The canonical mobility associated with an SPD Hessian metric is its
nonsingular inverse. -/
def dikinMobility (g : InfoGeometry.Jordan.SPD n) :
    Matrix (Fin n) (Fin n) ℝ :=
  g.mat⁻¹

/-- The inverse Dikin mobility remains positive definite by Mathlib's native
`Matrix.PosDef.inv` theorem. -/
theorem dikinMobility_posDef (g : InfoGeometry.Jordan.SPD n) :
    (dikinMobility g).PosDef := by
  exact g.pos.inv

/-- Hence the Dikin mobility is symmetric. -/
theorem dikinMobility_transpose (g : InfoGeometry.Jordan.SPD n) :
    (dikinMobility g).transpose = dikinMobility g := by
  simp [dikinMobility, Matrix.transpose_nonsing_inv,
    InfoGeometry.Jordan.SPD.transpose_eq_self]

/-- Every force has nonnegative quadratic response against inverse Dikin
mobility. -/
theorem dikinMobility_quadraticResponse_nonneg
    (g : InfoGeometry.Jordan.SPD n) (x : Fin n → ℝ) :
    0 ≤ quadraticResponse (dikinMobility g) x := by
  by_cases hx : x = 0
  · subst x
    simp [quadraticResponse]
  · exact le_of_lt (g.pos.inv.dotProduct_mulVec_pos hx)

/-- Compatibility condition identifying the symmetric Onsager tensor with the
inverse Hessian/Dikin metric. -/
def IsKVCompatible
    (Γ : DoubledConnection n) (g : InfoGeometry.Jordan.SPD n) : Prop :=
  Γ.onsagerTensor = dikinMobility g

/-- KV compatibility constructively supplies the finite Onsager second-law
condition; no extra positivity premise is needed. -/
theorem isOnsagerDissipative_of_kvCompatible
    (Γ : DoubledConnection n) (g : InfoGeometry.Jordan.SPD n)
    (hcompat : IsKVCompatible Γ g) :
    IsOnsagerDissipative Γ := by
  intro x
  change Γ.onsagerTensor = dikinMobility g at hcompat
  rw [hcompat]
  exact dikinMobility_quadraticResponse_nonneg g x

/-- Consequently a KV-compatible branch difference has nonnegative quadratic
entropy-production readout. -/
theorem entropyProduction_nonneg_of_kvCompatible
    (Γ : DoubledConnection n) (g : InfoGeometry.Jordan.SPD n)
    (hcompat : IsKVCompatible Γ g)
    (x : Fin n → ℝ) :
    0 ≤ entropyProduction Γ x := by
  exact entropyProduction_nonneg Γ
    (isOnsagerDissipative_of_kvCompatible Γ g hcompat) x

/-- Squared Newton decrement of a force/covector in the inverse Hessian metric. -/
def squaredNewtonDecrement
    (g : InfoGeometry.Jordan.SPD n) (x : Fin n → ℝ) : ℝ :=
  quadraticResponse (dikinMobility g) x

/-- Under KV compatibility the symmetric Onsager dissipation is exactly the
squared Newton decrement quadratic form. This is an algebraic identity; a
physical identification of the supplied vector with `-∇F` is downstream data. -/
theorem onsagerResponse_eq_squaredNewtonDecrement
    (Γ : DoubledConnection n) (g : InfoGeometry.Jordan.SPD n)
    (hcompat : IsKVCompatible Γ g)
    (x : Fin n → ℝ) :
    quadraticResponse Γ.onsagerTensor x =
      squaredNewtonDecrement g x := by
  change Γ.onsagerTensor = dikinMobility g at hcompat
  rw [hcompat]
  rfl

/-- The full branch-difference readout therefore equals the Newton-decrement
quadratic form whenever the symmetric sector is KV-compatible. -/
theorem entropyProduction_eq_squaredNewtonDecrement
    (Γ : DoubledConnection n) (g : InfoGeometry.Jordan.SPD n)
    (hcompat : IsKVCompatible Γ g)
    (x : Fin n → ℝ) :
    entropyProduction Γ x = squaredNewtonDecrement g x := by
  rw [entropyProduction, gammaDiff_quadraticResponse_eq_onsager]
  exact onsagerResponse_eq_squaredNewtonDecrement Γ g hcompat x

/-- Dual Dikin unit ball expressed directly by the same quadratic form. -/
def dualDikinUnitBall
    (g : InfoGeometry.Jordan.SPD n) : Set (Fin n → ℝ) :=
  {x | squaredNewtonDecrement g x ≤ 1}

/-- Under KV compatibility the unit sublevel set of the symmetric Onsager
response is literally the dual Dikin unit ball. -/
theorem onsager_unit_sublevel_eq_dualDikinUnitBall
    (Γ : DoubledConnection n) (g : InfoGeometry.Jordan.SPD n)
    (hcompat : IsKVCompatible Γ g) :
    {x : Fin n → ℝ | quadraticResponse Γ.onsagerTensor x ≤ 1} =
      dualDikinUnitBall g := by
  ext x
  change quadraticResponse Γ.onsagerTensor x ≤ 1 ↔
    squaredNewtonDecrement g x ≤ 1
  rw [onsagerResponse_eq_squaredNewtonDecrement Γ g hcompat x]

/-- Compact theorem packet for the kinematic-to-positive-response bridge. -/
theorem thermofield_onsager_dikin_packet
    (Γ : DoubledConnection n) (g : InfoGeometry.Jordan.SPD n)
    (hcompat : IsKVCompatible Γ g) :
    Γ.onsagerTensor.transpose = Γ.onsagerTensor ∧
    Γ.casimirTensor.transpose = -Γ.casimirTensor ∧
    (∀ x, quadraticResponse Γ.casimirTensor x = 0) ∧
    (∀ x, entropyProduction Γ x = squaredNewtonDecrement g x) ∧
    (∀ x, 0 ≤ entropyProduction Γ x) := by
  exact ⟨Γ.onsagerTensor_transpose,
    Γ.casimirTensor_transpose,
    fun x => skew_quadraticResponse_zero Γ.casimirTensor Γ.casimirTensor_transpose x,
    fun x => entropyProduction_eq_squaredNewtonDecrement Γ g hcompat x,
    fun x => entropyProduction_nonneg_of_kvCompatible Γ g hcompat x⟩

end InfoGeometry.Canonical.ThermofieldOnsagerDikinBridge
