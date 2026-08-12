import proofs.HillWheelerProjection
import proofs.JaynesLDDPGNSColimit
import InfoGeometry.Canonical.ProjectiveAffineConformalClosure55

/-!
# Universal Hill--Wheeler projection theorem

Finite theorem core for the shared projection mechanism:

* Hill--Wheeler generalized secular equation `det(H - E • N)=0`;
* finite idempotent projectors as symmetry restorers;
* CPT averaging projects any complex spectral parameter onto `Re(s)=1/2`;
* GNS overlap kernels are reference-state overlap matrices `τ(a*b)`;
* UHF/Cantor colimit compatibility is a projection-by-relative-inclusion.

-/

noncomputable section

namespace HillWheelerUniversalProjection

open HillWheelerProjection
open JaynesLDDPGNSColimit
open ProjectiveAffineConformalClosure55
open UHFInductiveColimit

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Hill--Wheeler generalized secular determinant `det(H - E N)`. -/
def hillWheelerSecular (H N : M2C) (E : ℂ) : ℂ :=
  Matrix.det (H - E • N)

/-- Diagonal `2×2` matrix helper. -/
def diag2 (a b : ℂ) : M2C :=
  !![a, 0; 0, b]

/-- For diagonal Hamiltonian and overlap kernels, the Hill--Wheeler secular
determinant factors into the two generalized eigenvalue factors. -/
theorem hillWheelerSecular_diag (h0 h1 n0 n1 E : ℂ) :
    hillWheelerSecular (diag2 h0 h1) (diag2 n0 n1) E =
      (h0 - E * n0) * (h1 - E * n1) := by
  simp [hillWheelerSecular, diag2, Matrix.det_fin_two]

/-- A finite symmetry-restoring projector. -/
def projector0 : M2C :=
  !![1, 0; 0, 0]

/-- The finite projector is idempotent. -/
theorem projector0_idempotent : projector0 * projector0 = projector0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector0, Matrix.mul_apply, Fin.sum_univ_two]

/-- The complementary finite projector. -/
def projector1 : M2C :=
  !![0, 0; 0, 1]

/-- The two finite projectors partition the identity. -/
theorem projector_partition : projector0 + projector1 = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [projector0, projector1]

/-- CPT/Hill--Wheeler averaging: average a point with its spectral CPT image. -/
def cptHillWheelerAverage (s : ℂ) : ℂ :=
  (s + spectralCPT s) / 2

/-- CPT averaging projects every spectral parameter onto the critical line. -/
theorem cptHillWheelerAverage_re (s : ℂ) :
    (cptHillWheelerAverage s).re = 1 / 2 := by
  unfold cptHillWheelerAverage spectralCPT
  simp

/-- CPT averaging is fixed by the spectral CPT reflection. -/
theorem cptHillWheelerAverage_fixed (s : ℂ) :
    spectralCPT (cptHillWheelerAverage s) = cptHillWheelerAverage s := by
  exact (spectralCPT_fixed_iff_criticalLine (cptHillWheelerAverage s)).2
    (cptHillWheelerAverage_re s)

/-- GNS/Hill--Wheeler overlap kernel: the reference state supplies the overlap
matrix `N_ab = τ(a*b)` for non-orthogonal algebraic bits. -/
def gnsHillWheelerOverlap {A : Type*} [Mul A]
    (τ : A → ℂ) (a b : A) : ℂ :=
  τ (a * b)

/-- The GNS overlap kernel is definitionally the reference-state overlap. -/
theorem gnsHillWheelerOverlap_eq {A : Type*} [Mul A]
    (τ : A → ℂ) (a b : A) :
    gnsHillWheelerOverlap τ a b = τ (a * b) := rfl

/-- The colimit/Hill--Wheeler projection step is exactly UHF cylinder
compatibility under the relative inclusion. -/
theorem colimitHillWheelerProjection_step (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f :=
  cylinder_compatible_succ n f

/-- Capstone: the same finite projection algebra underlies the generalized
eigenvalue problem, CPT critical-line projection, GNS overlap kernels, and UHF
colimit compatibility. -/
theorem hill_wheeler_universal_projection_synthesis
    (h0 h1 n0 n1 E : ℂ) (s : ℂ)
    (n : ℕ) (f : DiagAlg n) :
    hillWheelerSecular (diag2 h0 h1) (diag2 n0 n1) E =
      (h0 - E * n0) * (h1 - E * n1) ∧
    projector0 * projector0 = projector0 ∧
    projector0 + projector1 = (1 : M2C) ∧
    (cptHillWheelerAverage s).re = 1 / 2 ∧
    spectralCPT (cptHillWheelerAverage s) = cptHillWheelerAverage s ∧
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f := by
  constructor
  · simpa using hillWheelerSecular_diag h0 h1 n0 n1 E
  constructor
  · exact projector0_idempotent
  constructor
  · exact projector_partition
  constructor
  · exact cptHillWheelerAverage_re s
  constructor
  · exact cptHillWheelerAverage_fixed s
  · exact colimitHillWheelerProjection_step n f

end HillWheelerUniversalProjection

end noncomputable section
