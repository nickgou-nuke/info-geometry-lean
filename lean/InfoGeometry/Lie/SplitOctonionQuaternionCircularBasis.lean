import InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
import InfoGeometry.Canonical.ZornChiralPeirceDecomposition
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

/-!
# Circular basis of the quaternionic split doubling

This owner fixes the sign convention from the pasted construction:

* `rootPlus i = (eᵢ + ell eᵢ)/2`;
* `rootMinus i = (ell eᵢ - eᵢ)/2`.

With that convention the two families map respectively to the native upper
and lower Zorn Peirce bases.  In particular, this lower-root convention is the
negative of owners that define a Witt-minus vector as `(eᵢ-ell eᵢ)/2`.

## The Circular Polarized Basis

The circular polarized basis $\{u_+, \sigma_+^a, u_-, \sigma_-^a\}$ is the
natural Peirce/Witt basis for the split-octonion chiral cone.

Its fundamental properties and roles are:

* **Complementary Idempotents**: $u_\pm$ are complementary idempotents satisfying
  $u_\pm^2 = u_\pm$, $u_+ u_- = 0$, and $u_+ + u_- = 1$. The axial grading
  operator is precisely their difference $\ell = u_+ - u_-$.
* **Opposite Peirce Corners**: The polarized null directions occupy opposite
  Peirce corners: $\sigma_+^a \in u_+ A u_-$ and $\sigma_-^a \in u_- A u_+$.
* **Cone Generators**: They are square-zero cone generators: $(\sigma_\pm^a)^2 = 0$.
* **Color Selection (Inner Products)**: Their opposite products implement color selection:
  $\sigma_+^a \sigma_-^b = \delta_{ab} u_+$ and $\sigma_-^b \sigma_+^a = \delta_{ab} u_-$.

From these, the CAR (Canonical Anticommutation Relations) and Witt commutator
relations immediately follow:
$$ \{\sigma_+^a, \sigma_-^b\} = \delta_{ab} 1, \qquad [\sigma_+^a, \sigma_-^b] = \delta_{ab} \ell $$

Geometrically, $u_+$ and $u_-$ represent the two chiral cone sheets, while the
$\sigma_\pm^a$ are circularly polarized null channels connecting them.
Algebraically, they behave identically to creation/annihilation or off-diagonal
matrix-unit operators, but all reassociation remains governed strictly by the
alternative split-octonion laws rather than full associativity.

This basis therefore simultaneously exposes the deep equivalence between:
$$ \text{Cone Geometry} \longleftrightarrow \text{Peirce Decomposition} \longleftrightarrow \text{CAR/Witt Relations} \longleftrightarrow \text{Axial Grading} $$

It is the distinguished sparse basis in which the chiral multiplication,
grading, and derivation/root actions become completely transparent.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionEllFlowOperator
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

/-- Coordinate unit vector in the imaginary quaternion triple. -/
def axis (i : Fin 3) : Vec3 := Pi.single i 1

/-- The scalar `1` direction in the first quaternion copy. -/
def quaternionScalar : CartesianCoordinates := ((1, 0), (0, 0))

/-- The scalar `ell` direction in the second quaternion copy. -/
def ellScalar : CartesianCoordinates := ((0, 0), (1, 0))

/-- Imaginary quaternion unit `eᵢ`. -/
def quaternionAxis (i : Fin 3) : CartesianCoordinates :=
  ((0, axis i), (0, 0))

/-- Its partner `ell eᵢ`. -/
def ellAxis (i : Fin 3) : CartesianCoordinates :=
  ((0, 0), (0, axis i))

/-- The two diagonal circular idempotent coordinates. -/
def scalarPlus : CartesianCoordinates :=
  (1 / 2 : ℝ) • (quaternionScalar + ellScalar)

def scalarMinus : CartesianCoordinates :=
  (1 / 2 : ℝ) • (quaternionScalar - ellScalar)

/-- Positive and negative circular root coordinates. -/
def rootPlus (i : Fin 3) : CartesianCoordinates :=
  (1 / 2 : ℝ) • (quaternionAxis i + ellAxis i)

def rootMinus (i : Fin 3) : CartesianCoordinates :=
  (1 / 2 : ℝ) • (ellAxis i - quaternionAxis i)

/-- Ordered circular frame: the positive pole and triplet, followed by the
negative pole and triplet. -/
def circularFrame : Fin 8 → CartesianCoordinates
  | 0 => scalarPlus
  | 1 => rootPlus 0
  | 2 => rootPlus 1
  | 3 => rootPlus 2
  | 4 => scalarMinus
  | 5 => rootMinus 0
  | 6 => rootMinus 1
  | 7 => rootMinus 2
  | _ => 0

/-- Coordinates dual to `circularFrame`. -/
def circularCoordinate (qr : CartesianCoordinates) : Fin 8 → ℝ
  | 0 => qr.1.1 + qr.2.1
  | 1 => qr.1.2 0 + qr.2.2 0
  | 2 => qr.1.2 1 + qr.2.2 1
  | 3 => qr.1.2 2 + qr.2.2 2
  | 4 => qr.1.1 - qr.2.1
  | 5 => qr.2.2 0 - qr.1.2 0
  | 6 => qr.2.2 1 - qr.1.2 1
  | 7 => qr.2.2 2 - qr.1.2 2
  | _ => 0

/-- Every Cartesian quaternion pair reconstructs from its eight circular
coordinates. -/
theorem circularFrame_reconstruct (qr : CartesianCoordinates) :
    ∑ i : Fin 8, circularCoordinate qr i • circularFrame i = qr := by
  apply Prod.ext
  · apply Prod.ext
    · simp [circularCoordinate, circularFrame, scalarPlus, scalarMinus,
        rootPlus, rootMinus, quaternionScalar, ellScalar, quaternionAxis,
        ellAxis, axis, Fin.sum_univ_succ, smul_eq_mul]
      <;> ring
    · funext j
      fin_cases j <;>
        simp [circularCoordinate, circularFrame, scalarPlus, scalarMinus,
          rootPlus, rootMinus, quaternionScalar, ellScalar, quaternionAxis,
          ellAxis, axis, Fin.sum_univ_succ, smul_eq_mul]
        <;> ring
  · apply Prod.ext
    · simp [circularCoordinate, circularFrame, scalarPlus, scalarMinus,
        rootPlus, rootMinus, quaternionScalar, ellScalar, quaternionAxis,
        ellAxis, axis, Fin.sum_univ_succ, smul_eq_mul]
      <;> ring
    · funext j
      fin_cases j <;>
        simp [circularCoordinate, circularFrame, scalarPlus, scalarMinus,
          rootPlus, rootMinus, quaternionScalar, ellScalar, quaternionAxis,
          ellAxis, axis, Fin.sum_univ_succ, smul_eq_mul]
        <;> ring

/-- Every native canonical Zorn element has the same eight global circular
    coordinates after transport from the quaternion-pair coordinates.  This
    is a linear reconstruction theorem in the full carrier; it makes no
    associativity claim about the Zorn product. -/
theorem cartesianZorn_circularFrame_reconstruct
    (X : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn) :
    ∑ i : Fin 8,
      circularCoordinate (cartesianZornLinearEquiv.symm X) i •
        cartesianZornLinearEquiv (circularFrame i) = X := by
  have h := circularFrame_reconstruct (cartesianZornLinearEquiv.symm X)
  have h' := congrArg cartesianZornLinearEquiv h
  convert h' using 1 <;> ext <;> simp <;> ring

@[simp] theorem circularCoordinate_frame (i j : Fin 8) :
    circularCoordinate (circularFrame i) j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [circularCoordinate, circularFrame, scalarPlus, scalarMinus,
      rootPlus, rootMinus, quaternionScalar, ellScalar, quaternionAxis,
      ellAxis, axis] <;> norm_num

theorem circularFrame_linearIndependent :
    LinearIndependent ℝ circularFrame := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hc := congrArg (fun qr => circularCoordinate qr i) hg
  fin_cases i <;>
    simp [circularCoordinate, circularFrame, scalarPlus, scalarMinus,
      rootPlus, rootMinus, quaternionScalar, ellScalar, quaternionAxis,
      ellAxis, axis, Fin.sum_univ_succ] at hc ⊢ <;>
    linarith

/-- The eight circular vectors are an actual real basis, not merely a named
list of root directions. -/
noncomputable def circularBasis :
    Module.Basis (Fin 8) ℝ CartesianCoordinates :=
  Module.Basis.mk circularFrame_linearIndependent (by
    intro qr _
    rw [← circularFrame_reconstruct qr]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

@[simp] theorem circularBasis_apply (i : Fin 8) :
    circularBasis i = circularFrame i := by
  exact Module.Basis.mk_apply _ _ _

@[simp] theorem cartesianZorn_quaternionScalar :
    cartesianZornLinearEquiv quaternionScalar = 1 := by
  ext i <;> simp [quaternionScalar]

@[simp] theorem cartesianZorn_ellScalar :
    cartesianZornLinearEquiv ellScalar = diagEll := by
  ext i <;> simp [ellScalar, diagEll, zornPlus, zornMinus]

@[simp] theorem cartesianZorn_scalarPlus :
    cartesianZornLinearEquiv scalarPlus = zornPlus := by
  ext i <;>
    simp [scalarPlus, quaternionScalar, ellScalar, zornPlus,
      Equiv.smul_def, coordEquiv] <;> norm_num

@[simp] theorem cartesianZorn_scalarMinus :
    cartesianZornLinearEquiv scalarMinus = zornMinus := by
  ext i <;>
    simp [scalarMinus, quaternionScalar, ellScalar, zornMinus,
      Equiv.smul_def, coordEquiv] <;> norm_num

@[simp] theorem cartesianZorn_rootPlus (i : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) = chiralUpperBasis i := by
  ext j <;>
    simp [rootPlus, quaternionAxis, ellAxis, axis, chiralUpperBasis,
      Equiv.smul_def, coordEquiv] <;> ring

@[simp] theorem cartesianZorn_rootMinus (i : Fin 3) :
    cartesianZornLinearEquiv (rootMinus i) = chiralLowerBasis i := by
  ext j <;>
    simp [rootMinus, quaternionAxis, ellAxis, axis, chiralLowerBasis,
      Equiv.smul_def, coordEquiv] <;> ring

theorem cartesianZorn_rootPlus_mul_rootMinus (i : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootMinus i) =
      zornPlus := by
  rw [cartesianZorn_rootPlus, cartesianZorn_rootMinus]
  fin_cases i <;>
    ext j <;>
    simp [chiralUpperBasis, chiralLowerBasis,
      zornPlus,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases j <;> norm_num

theorem cartesianZorn_rootMinus_mul_rootPlus (i : Fin 3) :
    cartesianZornLinearEquiv (rootMinus i) *
        cartesianZornLinearEquiv (rootPlus i) =
      zornMinus := by
  rw [cartesianZorn_rootMinus, cartesianZorn_rootPlus]
  fin_cases i <;>
    ext j <;>
    simp [chiralUpperBasis, chiralLowerBasis,
      zornMinus,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases j <;> norm_num

theorem cartesianZorn_rootPlus_sq (i : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootPlus i) = 0 := by
  rw [cartesianZorn_rootPlus]
  fin_cases i <;>
    ext j <;>
    simp [chiralUpperBasis, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases j <;> norm_num

theorem cartesianZorn_rootMinus_sq (i : Fin 3) :
    cartesianZornLinearEquiv (rootMinus i) *
        cartesianZornLinearEquiv (rootMinus i) = 0 := by
  rw [cartesianZorn_rootMinus]
  fin_cases i <;>
    ext j <;>
    simp [chiralLowerBasis, InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases j <;> simp [Pi.single_apply] <;> norm_num

theorem cartesianZorn_root_commutator (i : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootMinus i) -
      cartesianZornLinearEquiv (rootMinus i) *
        cartesianZornLinearEquiv (rootPlus i) =
      diagEll := by
  rw [cartesianZorn_rootPlus_mul_rootMinus,
    cartesianZorn_rootMinus_mul_rootPlus]
  simp [diagEll, zornPlus, zornMinus]

theorem cartesianZorn_root_anticommutator (i : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootMinus i) +
      cartesianZornLinearEquiv (rootMinus i) *
        cartesianZornLinearEquiv (rootPlus i) =
      1 := by
  rw [cartesianZorn_rootPlus_mul_rootMinus,
    cartesianZorn_rootMinus_mul_rootPlus]
  exact zornPlus_add_zornMinus

/-! ## All-color circular multiplication table -/

theorem cartesianZorn_rootPlus_mul_rootMinus_if (i j : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootMinus j) =
      if i = j then zornPlus else 0 := by
  rw [cartesianZorn_rootPlus, cartesianZorn_rootMinus]
  fin_cases i <;> fin_cases j
  all_goals
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp [chiralUpperBasis, chiralLowerBasis, zornPlus,
        InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
    · simp [chiralUpperBasis, chiralLowerBasis, zornPlus,
        InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
    · funext k; fin_cases k <;>
        simp [chiralUpperBasis, chiralLowerBasis, zornPlus,
          InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot,
          InfoGeometry.Canonical.ZornMatrix.cross,
          Function.update, Pi.single_apply]
    · funext k; fin_cases k <;>
        simp [chiralUpperBasis, chiralLowerBasis, zornPlus,
          InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot,
          InfoGeometry.Canonical.ZornMatrix.cross,
          Function.update, Pi.single_apply]

theorem cartesianZorn_rootMinus_mul_rootPlus_if (i j : Fin 3) :
    cartesianZornLinearEquiv (rootMinus i) *
        cartesianZornLinearEquiv (rootPlus j) =
      if i = j then zornMinus else 0 := by
  rw [cartesianZorn_rootMinus, cartesianZorn_rootPlus]
  fin_cases i <;> fin_cases j <;> ext k <;>
    simp [chiralUpperBasis, chiralLowerBasis, zornMinus,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals try fin_cases k
  all_goals simp [Pi.single_apply]

theorem cartesianZorn_root_commutator_if (i j : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootMinus j) -
      cartesianZornLinearEquiv (rootMinus j) *
        cartesianZornLinearEquiv (rootPlus i) =
      if i = j then diagEll else 0 := by
  rw [cartesianZorn_rootPlus_mul_rootMinus_if,
    cartesianZorn_rootMinus_mul_rootPlus_if]
  by_cases h : i = j
  · subst j
    simp [diagEll, zornPlus, zornMinus]
  · simp [h, Ne.symm h]

theorem cartesianZorn_root_anticommutator_if (i j : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootMinus j) +
      cartesianZornLinearEquiv (rootMinus j) *
        cartesianZornLinearEquiv (rootPlus i) =
      if i = j then 1 else 0 := by
  rw [cartesianZorn_rootPlus_mul_rootMinus_if,
    cartesianZorn_rootMinus_mul_rootPlus_if]
  by_cases h : i = j
  · subst j
    simp only [if_pos rfl]
    exact zornPlus_add_zornMinus (R := ℝ)
  · simp [h, Ne.symm h]

/-! ## Finite color completeness -/

theorem cartesianZorn_rootPlus_mul_rootMinus_sum :
    ∑ i : Fin 3,
      cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootMinus i) =
      zornPlus + zornPlus + zornPlus := by
  simp only [cartesianZorn_rootPlus_mul_rootMinus]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  ext <;> simp <;> ring

theorem cartesianZorn_rootMinus_mul_rootPlus_sum :
    ∑ i : Fin 3,
      cartesianZornLinearEquiv (rootMinus i) *
        cartesianZornLinearEquiv (rootPlus i) =
      zornMinus + zornMinus + zornMinus := by
  simp only [cartesianZorn_rootMinus_mul_rootPlus]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  ext <;> simp <;> ring

theorem cartesianZorn_root_anticommutator_sum :
    ∑ i : Fin 3,
      (cartesianZornLinearEquiv (rootPlus i) *
          cartesianZornLinearEquiv (rootMinus i) +
        cartesianZornLinearEquiv (rootMinus i) *
          cartesianZornLinearEquiv (rootPlus i)) =
      (zornPlus + zornMinus) + (zornPlus + zornMinus) +
        (zornPlus + zornMinus) := by
  simp only [cartesianZorn_rootPlus_mul_rootMinus_if,
    cartesianZorn_rootMinus_mul_rootPlus_if, if_pos rfl]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp [add_assoc, add_left_comm, add_comm]

theorem cartesianZorn_root_commutator_sum :
    ∑ i : Fin 3,
      (cartesianZornLinearEquiv (rootPlus i) *
          cartesianZornLinearEquiv (rootMinus i) -
        cartesianZornLinearEquiv (rootMinus i) *
          cartesianZornLinearEquiv (rootPlus i)) =
      diagEll + diagEll + diagEll := by
  simp only [cartesianZorn_root_commutator]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  ext <;> simp <;> ring

theorem cartesianZorn_rootPlus_mul_rootPlus_cross (i j : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) *
        cartesianZornLinearEquiv (rootPlus j) =
      { a := 0, b := 0, x := 0,
        y := InfoGeometry.Canonical.ZornMatrix.cross (axis i) (axis j) } := by
  rw [cartesianZorn_rootPlus, cartesianZorn_rootPlus]
  fin_cases i <;> fin_cases j
  all_goals
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp [chiralUpperBasis, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
    · simp [chiralUpperBasis, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
    · funext k; fin_cases k <;>
        simp [chiralUpperBasis, axis,
          InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot,
          InfoGeometry.Canonical.ZornMatrix.cross,
          Function.update, Pi.single_apply]
    · funext k; fin_cases k <;>
        simp [chiralUpperBasis, axis,
          InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot,
          InfoGeometry.Canonical.ZornMatrix.cross,
          Function.update, Pi.single_apply]

theorem cartesianZorn_rootMinus_mul_rootMinus_cross (i j : Fin 3) :
    cartesianZornLinearEquiv (rootMinus i) *
        cartesianZornLinearEquiv (rootMinus j) =
      { a := 0, b := 0,
        x := -InfoGeometry.Canonical.ZornMatrix.cross (axis i) (axis j), y := 0 } := by
  rw [cartesianZorn_rootMinus, cartesianZorn_rootMinus]
  fin_cases i <;> fin_cases j
  all_goals
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp [chiralLowerBasis, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
    · simp [chiralLowerBasis, InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
    · funext k; fin_cases k <;>
        simp [chiralLowerBasis, axis,
          InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot,
          InfoGeometry.Canonical.ZornMatrix.cross,
          Function.update, Pi.single_apply]
    · funext k; fin_cases k <;>
        simp [chiralLowerBasis, axis,
          InfoGeometry.Canonical.ZornMatrix.mul,
          InfoGeometry.Canonical.ZornMatrix.dot,
          InfoGeometry.Canonical.ZornMatrix.cross,
          Function.update, Pi.single_apply]

theorem zornPlus_mul_cartesianZorn_rootPlus (i : Fin 3) :
    zornPlus * cartesianZornLinearEquiv (rootPlus i) =
      cartesianZornLinearEquiv (rootPlus i) := by
  rw [cartesianZorn_rootPlus]
  fin_cases i <;>
    ext j <;>
    simp [chiralUpperBasis, Pi.single_apply, zornPlus,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases j <;> simp [Pi.single_apply] <;> norm_num

theorem cartesianZorn_rootPlus_mul_zornMinus (i : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) * zornMinus =
      cartesianZornLinearEquiv (rootPlus i) := by
  rw [cartesianZorn_rootPlus]
  fin_cases i <;>
    ext j <;>
    simp [chiralUpperBasis, Pi.single_apply, zornMinus,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases j <;> simp [Pi.single_apply] <;> norm_num

theorem cartesianZorn_rootPlus_mul_zornPlus (i : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) * zornPlus = 0 := by
  rw [cartesianZorn_rootPlus]
  fin_cases i <;>
    ext j <;>
    simp [chiralUpperBasis, Pi.single_apply, zornPlus,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases j <;> simp [Pi.single_apply] <;> norm_num

theorem zornMinus_mul_cartesianZorn_rootPlus (i : Fin 3) :
    zornMinus * cartesianZornLinearEquiv (rootPlus i) = 0 := by
  rw [cartesianZorn_rootPlus]
  fin_cases i <;>
    ext j <;>
    simp [chiralUpperBasis, Pi.single_apply, zornMinus,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases j <;> simp [Pi.single_apply] <;> norm_num

theorem zornMinus_mul_cartesianZorn_rootMinus (i : Fin 3) :
    zornMinus * cartesianZornLinearEquiv (rootMinus i) =
      cartesianZornLinearEquiv (rootMinus i) := by
  rw [cartesianZorn_rootMinus]
  fin_cases i <;>
    ext j <;>
    simp [chiralLowerBasis, Pi.single_apply, zornMinus,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases j <;> simp [Pi.single_apply] <;> norm_num

theorem cartesianZorn_rootMinus_mul_zornPlus (i : Fin 3) :
    cartesianZornLinearEquiv (rootMinus i) * zornPlus =
      cartesianZornLinearEquiv (rootMinus i) := by
  rw [cartesianZorn_rootMinus]
  fin_cases i <;>
    ext j <;>
    simp [chiralLowerBasis, Pi.single_apply, zornPlus,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases j <;> simp [Pi.single_apply] <;> norm_num

theorem cartesianZorn_rootMinus_mul_zornMinus (i : Fin 3) :
    cartesianZornLinearEquiv (rootMinus i) * zornMinus = 0 := by
  rw [cartesianZorn_rootMinus]
  fin_cases i <;>
    ext j <;>
    simp [chiralLowerBasis, Pi.single_apply, zornMinus,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases j <;> simp [Pi.single_apply] <;> norm_num

theorem zornPlus_mul_cartesianZorn_rootMinus (i : Fin 3) :
    zornPlus * cartesianZornLinearEquiv (rootMinus i) = 0 := by
  rw [cartesianZorn_rootMinus]
  fin_cases i <;>
    ext j <;>
    simp [chiralLowerBasis, Pi.single_apply, zornPlus,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases j <;> simp [Pi.single_apply] <;> norm_num

theorem diagEll_mul_cartesianZorn_rootPlus (i : Fin 3) :
    diagEll * cartesianZornLinearEquiv (rootPlus i) =
      cartesianZornLinearEquiv (rootPlus i) := by
  rw [diagEll, InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.sub_mul,
    zornPlus_mul_cartesianZorn_rootPlus,
    zornMinus_mul_cartesianZorn_rootPlus]
  simp

theorem cartesianZorn_rootPlus_mul_diagEll (i : Fin 3) :
    cartesianZornLinearEquiv (rootPlus i) * diagEll =
      -cartesianZornLinearEquiv (rootPlus i) := by
  rw [diagEll, InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_sub,
    cartesianZorn_rootPlus_mul_zornPlus,
    cartesianZorn_rootPlus_mul_zornMinus]
  simp

theorem diagEll_mul_cartesianZorn_rootMinus (i : Fin 3) :
    diagEll * cartesianZornLinearEquiv (rootMinus i) =
      -cartesianZornLinearEquiv (rootMinus i) := by
  rw [diagEll, InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.sub_mul,
    zornPlus_mul_cartesianZorn_rootMinus,
    zornMinus_mul_cartesianZorn_rootMinus]
  simp

theorem cartesianZorn_rootMinus_mul_diagEll (i : Fin 3) :
    cartesianZornLinearEquiv (rootMinus i) * diagEll =
      cartesianZornLinearEquiv (rootMinus i) := by
  rw [diagEll, InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_sub,
    cartesianZorn_rootMinus_mul_zornPlus,
    cartesianZorn_rootMinus_mul_zornMinus]
  simp

/-! ## Inverse circular transformation -/

theorem scalar_reconstruction_one :
    scalarPlus + scalarMinus = quaternionScalar := by
  ext <;>
    simp [scalarPlus, scalarMinus, quaternionScalar, ellScalar] <;> ring

theorem scalar_reconstruction_ell :
    scalarPlus - scalarMinus = ellScalar := by
  ext <;>
    simp [scalarPlus, scalarMinus, quaternionScalar, ellScalar] <;> ring

theorem root_reconstruction_quaternion (i : Fin 3) :
    rootPlus i - rootMinus i = quaternionAxis i := by
  ext <;> simp [rootPlus, rootMinus, quaternionAxis, ellAxis] <;> ring

theorem root_reconstruction_ell (i : Fin 3) :
    rootPlus i + rootMinus i = ellAxis i := by
  ext <;> simp [rootPlus, rootMinus, quaternionAxis, ellAxis] <;> ring

/-! ## Diagonalization of the `ell` exchange operator -/

@[simp] theorem cartesianEllGrading_scalarPlus :
    cartesianEllGrading scalarPlus = 0 := by
  ext <;>
    simp [cartesianEllGrading, scalarPlus, quaternionScalar, ellScalar]

@[simp] theorem cartesianEllGrading_scalarMinus :
    cartesianEllGrading scalarMinus = 0 := by
  ext <;>
    simp [cartesianEllGrading, scalarMinus, quaternionScalar, ellScalar]

@[simp] theorem cartesianEllGrading_rootPlus (i : Fin 3) :
    cartesianEllGrading (rootPlus i) = rootPlus i := by
  ext <;> simp [cartesianEllGrading, rootPlus, quaternionAxis, ellAxis] <;> ring

@[simp] theorem cartesianEllGrading_rootMinus (i : Fin 3) :
    cartesianEllGrading (rootMinus i) = -rootMinus i := by
  ext <;> simp [cartesianEllGrading, rootMinus, quaternionAxis, ellAxis] <;> ring

/-- The closed hyperbolic flow is diagonal on the circular positive roots. -/
@[simp] theorem cartesianHyperbolicFlow_rootPlus (t : ℝ) (i : Fin 3) :
    cartesianHyperbolicFlow t (rootPlus i) =
      Real.exp t • rootPlus i := by
  apply cartesianZornLinearEquiv.injective
  rw [cartesianZorn_intertwines_closedFlow, cartesianZorn_rootPlus,
    map_smul, cartesianZorn_rootPlus]
  rw [InfoGeometry.Lie.SplitOctonionEllClosedFlow.ellFlowPhi_coord]
  ext j <;> simp [chiralUpperBasis, Equiv.smul_def, coordEquiv]

/-- The closed hyperbolic flow is diagonal on the circular negative roots. -/
@[simp] theorem cartesianHyperbolicFlow_rootMinus (t : ℝ) (i : Fin 3) :
    cartesianHyperbolicFlow t (rootMinus i) =
      Real.exp (-t) • rootMinus i := by
  apply cartesianZornLinearEquiv.injective
  rw [cartesianZorn_intertwines_closedFlow, cartesianZorn_rootMinus,
    map_smul, cartesianZorn_rootMinus]
  rw [InfoGeometry.Lie.SplitOctonionEllClosedFlow.ellFlowPhi_coord]
  ext j <;> simp [chiralLowerBasis, Equiv.smul_def, coordEquiv]

end InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
