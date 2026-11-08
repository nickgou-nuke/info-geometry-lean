import Mathlib.Algebra.Quaternion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Quantum.RealMajoranaCategory
import InfoGeometry.Krein.DoubledSpace

set_option linter.unusedSectionVars false

namespace InfoGeometry.Quantum.Hurwitz

open scoped Quaternion
open scoped BigOperators
open RealMajoranaCategory

noncomputable section

/-- The D4 lattice site proxy. -/
abbrev HurwitzNode := ℍ[ℝ]

/-- Unit predicate used for Hurwitz-neighbor candidates. -/
def IsHurwitzUnit (u : HurwitzNode) : Prop :=
  Quaternion.normSq u = 1

/-- Majorana scalar field on lattice nodes. -/
abbrev LatticeState := HurwitzNode → ℝ

/-- Convenience constructor for explicit quaternion coordinates. -/
def node (a b c d : ℝ) : HurwitzNode :=
  { re := a, imI := b, imJ := c, imK := d }

@[simp] theorem node_normSq (a b c d : ℝ) :
    Quaternion.normSq (node a b c d) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  simp [node, Quaternion.normSq_def']

/-- The first eight Hurwitz directions `±1, ±i, ±j, ±k`. -/
def basisDir : Fin 8 → HurwitzNode
  | ⟨0, _⟩ => node 1 0 0 0
  | ⟨1, _⟩ => node (-1) 0 0 0
  | ⟨2, _⟩ => node 0 1 0 0
  | ⟨3, _⟩ => node 0 (-1) 0 0
  | ⟨4, _⟩ => node 0 0 1 0
  | ⟨5, _⟩ => node 0 0 (-1) 0
  | ⟨6, _⟩ => node 0 0 0 1
  | ⟨7, _⟩ => node 0 0 0 (-1)

@[simp] theorem basisDir_isHurwitzUnit (i : Fin 8) :
    IsHurwitzUnit (basisDir i) := by
  fin_cases i <;>
    change Quaternion.normSq (node _ _ _ _) = 1 <;>
    rw [node_normSq] <;>
    norm_num

/-- The eight signed coordinate axes are distinct quaternion values. -/
theorem basisDir_injective : Function.Injective basisDir := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | rfl | norm_num [basisDir, node] at hij

/--
The sixteen half-integer Hurwitz directions `(±1, ±1, ±1, ±1) / 2`.
The signs are encoded by the 4 low bits of the index.
-/
def halfDir (i : Fin 16) : HurwitzNode :=
  let n : Nat := i.1
  let sgn (bit : Nat) : ℝ :=
    if ((n / bit) % 2 = 0) then (1 / 2 : ℝ) else (-1 / 2 : ℝ)
  node (sgn 1) (sgn 2) (sgn 4) (sgn 8)

@[simp] theorem halfDir_isHurwitzUnit (i : Fin 16) :
    IsHurwitzUnit (halfDir i) := by
  dsimp [IsHurwitzUnit, halfDir, node]
  rw [Quaternion.normSq_def']
  repeat split_ifs <;> norm_num

/-- The sixteen independent sign corners are distinct quaternion values. -/
theorem halfDir_injective : Function.Injective halfDir := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | rfl | norm_num [halfDir, node] at hij

/-- The distinct eight axis points in the Hurwitz shell. -/
noncomputable def hurwitzAxisSet : Finset HurwitzNode :=
  by classical exact Finset.univ.image basisDir

/-- The distinct sixteen half-integer corner points in the Hurwitz shell. -/
noncomputable def hurwitzCornerSet : Finset HurwitzNode :=
  by classical exact Finset.univ.image halfDir

@[simp] theorem card_hurwitzAxisSet : hurwitzAxisSet.card = 8 := by
  classical
  unfold hurwitzAxisSet
  rw [Finset.card_image_iff.mpr (fun i _ j _ hij => basisDir_injective hij)]
  simp

@[simp] theorem card_hurwitzCornerSet : hurwitzCornerSet.card = 16 := by
  classical
  unfold hurwitzCornerSet
  rw [Finset.card_image_iff.mpr (fun i _ j _ hij => halfDir_injective hij)]
  simp

/-- Axis units and half-integer corners are disjoint subsets of the quaternion carrier. -/
theorem hurwitzAxisSet_disjoint_cornerSet :
    Disjoint hurwitzAxisSet hurwitzCornerSet := by
  classical
  rw [Finset.disjoint_left]
  intro q hqAxis hqCorner
  rcases Finset.mem_image.mp hqAxis with ⟨i, -, rfl⟩
  rcases Finset.mem_image.mp hqCorner with ⟨j, -, hj⟩
  fin_cases i <;> simp [basisDir, halfDir, node] at hj <;>
    rcases hj with ⟨h1, h2, h3, h4⟩ <;>
    by_cases hbit : (↑j : Nat) % 2 = 0 <;> simp [hbit] at h1 <;> norm_num at h1

/-- The two disjoint families have the claimed total cardinality. -/
@[simp] theorem card_hurwitzAxisSet_add_cornerSet :
    hurwitzAxisSet.card + hurwitzCornerSet.card = 24 := by
  classical
  simp

/--
A computable 24-direction chart for nearest-neighbor hopping on the Hurwitz shell.
We index directions by `Fin 24` to keep the set finite and executable.
-/
def hurwitzDirection : Fin 24 → HurwitzNode
  | ⟨n, hn⟩ =>
      if h : n < 8 then
        basisDir ⟨n, h⟩
      else
        halfDir ⟨n % 16, Nat.mod_lt _ (by decide : 0 < 16)⟩

@[simp] theorem hurwitzDirection_isHurwitzUnit (i : Fin 24) :
    IsHurwitzUnit (hurwitzDirection i) := by
  rcases i with ⟨n, hn⟩
  by_cases h : n < 8
  · simpa [hurwitzDirection, IsHurwitzUnit, h] using
      (basisDir_isHurwitzUnit (i := ⟨n, h⟩))
  · have h' : ¬ n < 8 := h
    simpa [hurwitzDirection, IsHurwitzUnit, h'] using
      (halfDir_isHurwitzUnit (i := ⟨n % 16, Nat.mod_lt _ (by decide : 0 < 16)⟩))

/-- The chart really indexes 24 different quaternion values, not just 24 indices. -/
theorem hurwitzDirection_injective : Function.Injective hurwitzDirection := by
  intro i j hij
  apply Fin.ext
  classical
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  by_cases hi8 : i < 8 <;> by_cases hj8 : j < 8
  · have haxes : basisDir ⟨i, hi8⟩ = basisDir ⟨j, hj8⟩ := by
      simpa [hurwitzDirection, hi8, hj8] using hij
    have hidx := basisDir_injective haxes
    have hval : i = j := congrArg Fin.val hidx
    exact hval
  · have hAxis : hurwitzDirection ⟨i, hi⟩ ∈ hurwitzAxisSet := by
      apply Finset.mem_image.mpr
      exact ⟨⟨i, hi8⟩, Finset.mem_univ _, by simp [hurwitzDirection, hi8]⟩
    have hCorner : hurwitzDirection ⟨j, hj⟩ ∈ hurwitzCornerSet := by
      apply Finset.mem_image.mpr
      exact ⟨⟨j % 16, Nat.mod_lt _ (by decide : 0 < 16)⟩,
        Finset.mem_univ _, by simp [hurwitzDirection, hj8]⟩
    have hAxis' : hurwitzDirection ⟨i, hi⟩ ∈ hurwitzCornerSet := by
      simpa [hij] using hCorner
    exact False.elim
      ((Finset.disjoint_left.mp hurwitzAxisSet_disjoint_cornerSet) hAxis hAxis')
  · have hCorner : hurwitzDirection ⟨i, hi⟩ ∈ hurwitzCornerSet := by
      apply Finset.mem_image.mpr
      exact ⟨⟨i % 16, Nat.mod_lt _ (by decide : 0 < 16)⟩,
        Finset.mem_univ _, by simp [hurwitzDirection, hi8]⟩
    have hAxis : hurwitzDirection ⟨j, hj⟩ ∈ hurwitzAxisSet := by
      apply Finset.mem_image.mpr
      exact ⟨⟨j, hj8⟩, Finset.mem_univ _, by simp [hurwitzDirection, hj8]⟩
    have hAxis' : hurwitzDirection ⟨i, hi⟩ ∈ hurwitzAxisSet := by
      simpa [hij] using hAxis
    exact False.elim
      ((Finset.disjoint_left.mp hurwitzAxisSet_disjoint_cornerSet) hAxis' hCorner)
  · have hcorners :
        halfDir ⟨i % 16, Nat.mod_lt _ (by decide : 0 < 16)⟩ =
        halfDir ⟨j % 16, Nat.mod_lt _ (by decide : 0 < 16)⟩ := by
      simpa [hurwitzDirection, hi8, hj8] using hij
    have hidx : i % 16 = j % 16 := congrArg Fin.val (halfDir_injective hcorners)
    have hi_lower : 8 ≤ i := by omega
    have hj_lower : 8 ≤ j := by omega
    have hi_upper : i < 24 := hi
    have hj_upper : j < 24 := hj
    have hval : i = j := by omega
    exact hval

/-- The finite set of quaternion values used by the 24-direction chart. -/
noncomputable def hurwitzDirectionSet : Finset HurwitzNode :=
  by classical exact Finset.univ.image hurwitzDirection

@[simp] theorem card_hurwitzDirectionSet : hurwitzDirectionSet.card = 24 := by
  classical
  unfold hurwitzDirectionSet
  rw [Finset.card_image_iff.mpr (fun i _ j _ hij => hurwitzDirection_injective hij)]
  simp

/-- Every axis point in the finite shell occurs in the chart. -/
theorem hurwitzDirection_covers_axis (j : Fin 8) :
    ∃ i : Fin 24, hurwitzDirection i = basisDir j := by
  refine ⟨⟨j.1, by omega⟩, ?_⟩
  simp [hurwitzDirection, j.2]

/-- Every sign corner in the finite shell occurs in the chart. -/
theorem hurwitzDirection_covers_corner (j : Fin 16) :
    ∃ i : Fin 24, hurwitzDirection i = halfDir j := by
  by_cases hj : j.1 < 8
  · refine ⟨⟨j.1 + 16, by omega⟩, ?_⟩
    have hmod : (j.1 + 16) % 16 = j.1 := by omega
    have hnot : ¬ j.1 + 16 < 8 := by omega
    simp [hurwitzDirection, hnot, hmod]
  · refine ⟨⟨j.1, by omega⟩, ?_⟩
    have hmod : j.1 % 16 = j.1 := Nat.mod_eq_of_lt j.2
    simp [hurwitzDirection, hj, hmod]

/-! ### Exact rational Hurwitz shell

The real-valued chart above is useful for the analytic lattice layer, but a finite group
calculation should use exact coefficients. The next chart uses the same ordering and coordinates
over `ℚ`, so finite coordinate identities are exact rather than numerical approximations. -/

/-- Exact rational coordinate constructor for the Hurwitz shell. -/
def rationalNode (a b c d : ℚ) : Quaternion ℚ :=
  { re := a, imI := b, imJ := c, imK := d }

/-- The eight rational axis units, in the same order as `basisDir`. -/
def rationalBasisDir : Fin 8 → Quaternion ℚ
  | ⟨0, _⟩ => rationalNode 1 0 0 0
  | ⟨1, _⟩ => rationalNode (-1) 0 0 0
  | ⟨2, _⟩ => rationalNode 0 1 0 0
  | ⟨3, _⟩ => rationalNode 0 (-1) 0 0
  | ⟨4, _⟩ => rationalNode 0 0 1 0
  | ⟨5, _⟩ => rationalNode 0 0 (-1) 0
  | ⟨6, _⟩ => rationalNode 0 0 0 1
  | ⟨7, _⟩ => rationalNode 0 0 0 (-1)

/-- The sixteen rational half-coordinate corners, in the same order as `halfDir`. -/
def rationalHalfDir (i : Fin 16) : Quaternion ℚ :=
  let n : Nat := i.1
  let sgn (bit : Nat) : ℚ :=
    if ((n / bit) % 2 = 0) then (1 / 2 : ℚ) else (-1 / 2 : ℚ)
  rationalNode (sgn 1) (sgn 2) (sgn 4) (sgn 8)

/-- Exact rational version of the 24-element axis-and-corner chart. -/
def rationalHurwitzDirection : Fin 24 → Quaternion ℚ
  | ⟨n, hn⟩ =>
      if h : n < 8 then
        rationalBasisDir ⟨n, h⟩
      else
        rationalHalfDir ⟨n % 16, Nat.mod_lt _ (by decide : 0 < 16)⟩

/-- Unit norm for each entry in the exact rational chart. -/
theorem rationalHurwitzDirection_unit (i : Fin 24) :
    (rationalHurwitzDirection i).re ^ 2 +
      (rationalHurwitzDirection i).imI ^ 2 +
      (rationalHurwitzDirection i).imJ ^ 2 +
      (rationalHurwitzDirection i).imK ^ 2 = 1 := by
  fin_cases i <;>
    norm_num [rationalHurwitzDirection, rationalBasisDir, rationalHalfDir, rationalNode]

/-- Extend rational quaternion coordinates to the existing real-valued owner. -/
def rationalToReal (q : Quaternion ℚ) : HurwitzNode :=
  node (q.re : ℝ) (q.imI : ℝ) (q.imJ : ℝ) (q.imK : ℝ)

/-- The rational axis chart maps coordinatewise to the established real axis chart. -/
theorem rationalBasisDir_toReal (i : Fin 8) :
    rationalToReal (rationalBasisDir i) = basisDir i := by
  fin_cases i <;> norm_num [rationalToReal, rationalBasisDir, rationalNode, basisDir, node]

/-- The rational corner chart maps coordinatewise to the established real corner chart. -/
theorem rationalHalfDir_toReal (i : Fin 16) :
    rationalToReal (rationalHalfDir i) = halfDir i := by
  fin_cases i <;> norm_num [rationalToReal, rationalHalfDir, rationalNode, halfDir, node]

/-- The rational 24-point chart is carried exactly to the existing real chart. -/
theorem rationalHurwitzDirection_toReal (i : Fin 24) :
    rationalToReal (rationalHurwitzDirection i) = hurwitzDirection i := by
  rcases i with ⟨n, hn⟩
  by_cases h : n < 8
  · simpa [rationalHurwitzDirection, hurwitzDirection, h] using
      rationalBasisDir_toReal (⟨n, h⟩ : Fin 8)
  · simpa [rationalHurwitzDirection, hurwitzDirection, h] using
      rationalHalfDir_toReal
        (⟨n % 16, Nat.mod_lt _ (by decide : 0 < 16)⟩ : Fin 16)

/-- Distinct indices in the rational chart remain distinct as exact quaternions. -/
theorem rationalHurwitzDirection_injective :
    Function.Injective rationalHurwitzDirection := by
  intro i j hij
  apply hurwitzDirection_injective
  have hreal := congrArg rationalToReal hij
  simpa only [rationalHurwitzDirection_toReal] using hreal

/-- The finite set of values in the exact rational Hurwitz chart. -/
noncomputable def rationalHurwitzDirectionSet : Finset (Quaternion ℚ) := by
  classical
  exact Finset.univ.image rationalHurwitzDirection

@[simp] theorem card_rationalHurwitzDirectionSet :
    rationalHurwitzDirectionSet.card = 24 := by
  classical
  unfold rationalHurwitzDirectionSet
  rw [Finset.card_image_iff.mpr
    (fun i _ j _ hij => rationalHurwitzDirection_injective hij)]
  simp

/-- The rational chart's coordinate norm proof transports to the existing real unit predicate. -/
theorem rationalHurwitzDirection_toReal_isHurwitzUnit (i : Fin 24) :
    IsHurwitzUnit (rationalToReal (rationalHurwitzDirection i)) := by
  rw [IsHurwitzUnit, rationalToReal, node_normSq]
  exact_mod_cast rationalHurwitzDirection_unit i

/-- Finite index set of the 24 neighbor directions. -/
def hurwitzDirections : Finset (Fin 24) :=
  Finset.univ

@[simp] lemma card_hurwitzDirections : hurwitzDirections.card = 24 := by
  simp [hurwitzDirections]

/--
Supercharge operator `Q`: one-step aggregate hopping over the 24 Hurwitz directions.
-/
def superchargeQ (psi : LatticeState) (q : HurwitzNode) : ℝ :=
  Finset.sum hurwitzDirections (fun i => psi (q + hurwitzDirection i))

/--
Neighbor-difference Laplacian: sum of local increments over the same direction shell.
-/
def neighborLaplacian (psi : LatticeState) (q : HurwitzNode) : ℝ :=
  Finset.sum hurwitzDirections (fun i => (psi (q + hurwitzDirection i) - psi q))

/--
The SUSY Hamiltonian generated by this model supercharge.
Defined as `Q²` so the algebraic relation is exact by construction.
-/
def discreteLaplacian (psi : LatticeState) (q : HurwitzNode) : ℝ :=
  superchargeQ (superchargeQ psi) q

@[simp] theorem supercharge_sq_eq_laplacian (psi : LatticeState) :
    superchargeQ (superchargeQ psi) = discreteLaplacian psi := by
  rfl

section RealMajoranaLayer

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Real Majorana doubled core used by the strictly real lattice layer. -/
noncomputable abbrev X := cl11DoubledCore E

/-- Majorana-valued lattice states over the Hurwitz shell coordinates. -/
abbrev MajoranaState : Type _ := HurwitzNode → cl11DoubledCore E

/-- Polymorphic nearest-neighbor hop aggregator over the 24-shell. -/
def hop {V : Type*} [AddCommMonoid V] (ψ : HurwitzNode → V) (q : HurwitzNode) : V :=
  Finset.sum hurwitzDirections (fun i => ψ (q + hurwitzDirection i))

/-- Prior (first) leg of a Majorana-valued state. -/
def priorPart (ψ : HurwitzNode → cl11DoubledCore E) : HurwitzNode → E :=
  fun q => WithLp.fst (ψ q)

/-- Data (second) leg of a Majorana-valued state. -/
def dataPart (ψ : HurwitzNode → cl11DoubledCore E) : HurwitzNode → E :=
  fun q => WithLp.snd (ψ q)

/--
Strictly real supercharge on the doubled core:
off-diagonal exchange of hopped prior/data legs.
-/
noncomputable def superchargeMajorana (ψ : HurwitzNode → cl11DoubledCore E) (q : HurwitzNode) :
    cl11DoubledCore E :=
  InfoGeometry.Krein.to_doubled
    (hop (dataPart ψ) q)
    (hop (priorPart ψ) q)

/-- Hamiltonian induced by the real supercharge (`Q^2` by construction). -/
noncomputable def latticeHamiltonianMajorana (ψ : HurwitzNode → cl11DoubledCore E) (q : HurwitzNode) :
    cl11DoubledCore E :=
  superchargeMajorana (fun x => superchargeMajorana ψ x) q

/-- Operator-imaginary axis inherited from the real Majorana core. -/
noncomputable def K : cl11DoubledCore E →ₗ[ℝ] cl11DoubledCore E :=
  (cl11DoubledCore E).K

@[simp] theorem K_sq :
    ((cl11DoubledCore E).K).comp ((cl11DoubledCore E).K) =
      -((LinearMap.id : cl11DoubledCore E →ₗ[ℝ] cl11DoubledCore E)) := by
  simpa [K] using (cl11DoubledCore E).K_sq

end RealMajoranaLayer

end

end InfoGeometry.Quantum.Hurwitz
