import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Meta.Architecture
import InfoGeometry.Singular.Drazin

namespace InfoGeometry.Canonical.Drazin

/-- Predicate encoding the Drazin inverse laws. -/
@[rep_depth krein]
def IsDrazinInverse {R : Type*} [Ring R] (a b : R) (k : ℕ) : Prop :=
  a * b = b * a ∧ b * a * b = b ∧ a^(k + 1) * b = a^k

namespace IsDrazinInverse

variable {R : Type*} [Ring R] {a b c : R} {k : ℕ}

/-- Constructor for the Drazin laws predicate. -/
@[rep_depth krein]
theorem mk
    (hcomm : a * b = b * a)
    (hidempotent : b * a * b = b)
    (hpower : a^(k + 1) * b = a^k) :
    IsDrazinInverse a b k :=
  ⟨hcomm, hidempotent, hpower⟩

/-- An idempotent is its own Drazin inverse, with index `1`. -/
@[rep_depth krein]
theorem of_idempotent {p : R} (hp : p * p = p) :
    IsDrazinInverse p p 1 := by
  have hppp : p * p * p = p :=
    Eq.trans (congrArg (fun x : R => x * p) hp) hp
  refine mk rfl ?_ ?_
  · exact hppp
  · simpa [pow_two] using hppp

/-- Commutation law for a Drazin inverse witness. -/
@[rep_depth krein]
theorem comm (h : IsDrazinInverse a b k) : a * b = b * a := h.1

/-- Idempotent law for a Drazin inverse witness. -/
@[rep_depth krein]
theorem idempotent (h : IsDrazinInverse a b k) : b * a * b = b := h.2.1

/-- Power law for a Drazin inverse witness. -/
@[rep_depth krein]
theorem power (h : IsDrazinInverse a b k) : a^(k + 1) * b = a^k := h.2.2

/-- Ring equivalences transport Drazin inverse laws. -/
@[rep_depth krein]
theorem map_ringEquiv {S : Type*} [Ring S]
    (e : R ≃+* S)
    (h : IsDrazinInverse a b k) :
    IsDrazinInverse (e a) (e b) k := by
  refine mk ?_ ?_ ?_
  · simpa using congrArg e h.comm
  · simpa [mul_assoc] using congrArg e h.idempotent
  · simpa using congrArg e h.power

/-- Transport a canonical Drazin inverse proof to the singular Drazin API. -/
private theorem toSingular (h : IsDrazinInverse a b k) :
    InfoGeometry.Singular.Drazin.IsDrazinInverse a b k := by
  exact InfoGeometry.Singular.Drazin.IsDrazinInverse.mk
    h.idempotent h.comm h.power.symm

/-- Transport a singular Drazin inverse proof back to the canonical Drazin API. -/
private theorem fromSingular
    (h : InfoGeometry.Singular.Drazin.IsDrazinInverse a b k) :
    IsDrazinInverse a b k := by
  exact mk h.comm h.dad_eq_d h.pow_eq_pow_succ_mul.symm

/-- Definition `projection`. -/
@[rep_depth krein]
def projection (a b : R) : R := a * b

/-- Complementary Drazin projector `Q = 1 - P`. -/
@[rep_depth krein]
def complementaryProjection (a b : R) : R := 1 - projection a b

/-- Theorem `projection_is_idempotent`. -/
@[rep_depth krein]
theorem projection_is_idempotent (h : IsDrazinInverse a b k) :
    (projection a b) * (projection a b) = projection a b := by
  unfold projection
  calc
    (a * b) * (a * b) = a * (b * a * b) := by noncomm_ring
    _ = a * b := by rw [h.idempotent]

/-- The complementary Drazin projector is idempotent. -/
@[rep_depth krein]
theorem complementaryProjection_is_idempotent (h : IsDrazinInverse a b k) :
    (complementaryProjection a b) * (complementaryProjection a b) =
      complementaryProjection a b := by
  have hP : (projection a b) * (projection a b) = projection a b :=
    projection_is_idempotent h
  unfold complementaryProjection
  noncomm_ring [hP]

/-- The Drazin projector and its complement are left-orthogonal. -/
@[rep_depth krein]
theorem projection_mul_complementaryProjection (h : IsDrazinInverse a b k) :
    projection a b * complementaryProjection a b = 0 := by
  have hP : (projection a b) * (projection a b) = projection a b :=
    projection_is_idempotent h
  unfold complementaryProjection
  noncomm_ring [hP]

/-- The Drazin projector and its complement are right-orthogonal. -/
@[rep_depth krein]
theorem complementaryProjection_mul_projection (h : IsDrazinInverse a b k) :
    complementaryProjection a b * projection a b = 0 := by
  have hP : (projection a b) * (projection a b) = projection a b :=
    projection_is_idempotent h
  unfold complementaryProjection
  noncomm_ring [hP]

/-- Drazin projector decomposition of identity: `P + Q = 1`. -/
@[rep_depth krein]
theorem projection_add_complementaryProjection :
    projection a b + complementaryProjection a b = (1 : R) := by
  unfold complementaryProjection
  noncomm_ring

/-- Theorem `projection_comm`. -/
@[rep_depth krein]
theorem projection_comm (h : IsDrazinInverse a b k) :
    (projection a b) * b = b * (projection a b) := by
  unfold projection
  calc
    (a * b) * b = (b * a) * b := by rw [h.comm]
    _ = b * (a * b) := by rw [mul_assoc]

/-- The Drazin regular projector commutes with the original element. -/
@[rep_depth krein]
theorem projection_comm_self (h : IsDrazinInverse a b k) :
    projection a b * a = a * projection a b := by
  unfold projection
  calc
    (a * b) * a = a * (b * a) := by rw [mul_assoc]
    _ = a * (a * b) := by rw [← h.comm]

/-- The complementary Drazin projector commutes with the original element. -/
@[rep_depth krein]
theorem complementaryProjection_comm_self (h : IsDrazinInverse a b k) :
    complementaryProjection a b * a = a * complementaryProjection a b := by
  have hP : projection a b * a = a * projection a b :=
    projection_comm_self h
  unfold complementaryProjection
  calc
    (1 - projection a b) * a = a - projection a b * a := by rw [sub_mul, one_mul]
    _ = a - a * projection a b := by rw [hP]
    _ = a * (1 - projection a b) := by rw [mul_sub, mul_one]

/-! ### Algebraic Fitting-Drazin boundary -/

/-- The regular summand `aP` associated to the Drazin spectral projector `P = a*b`. -/
@[rep_depth krein]
def fittingRegularPart (a b : R) : R := a * projection a b

/-- The nilpotent summand `aQ` associated to the complementary Drazin projector `Q = 1 - a*b`. -/
@[rep_depth krein]
def fittingNilpotentPart (a b : R) : R := a * complementaryProjection a b

/-- The Drazin element splits algebraically into its regular and singular/Fitting parts. -/
@[rep_depth krein]
theorem fittingRegularPart_add_fittingNilpotentPart_eq_self :
    fittingRegularPart a b + fittingNilpotentPart a b = a := by
  unfold fittingRegularPart fittingNilpotentPart complementaryProjection projection
  noncomm_ring

/-- The Drazin power `a^k` annihilates the complementary Fitting projector on the left. -/
@[rep_depth krein]
theorem power_mul_complementaryProjection_eq_zero (h : IsDrazinInverse a b k) :
    a^k * complementaryProjection a b = 0 := by
  unfold complementaryProjection projection
  calc
    a^k * (1 - a * b) = a^k - (a^k * a) * b := by noncomm_ring
    _ = a^k - a^(k + 1) * b := by rw [pow_succ]
    _ = 0 := by rw [h.power]; simp

/-- The Drazin power `a^k` also annihilates the complementary Fitting projector on the right. -/
@[rep_depth krein]
theorem complementaryProjection_mul_power_eq_zero (h : IsDrazinInverse a b k) :
    complementaryProjection a b * a^k = 0 := by
  have hleft : a^k * complementaryProjection a b = 0 :=
    power_mul_complementaryProjection_eq_zero h
  have hcomm : Commute (a^k) (complementaryProjection a b) := by
    exact (show Commute a (complementaryProjection a b) from
      (complementaryProjection_comm_self h).symm).pow_left k
  calc
    complementaryProjection a b * a^k = a^k * complementaryProjection a b := hcomm.eq.symm
    _ = 0 := hleft

/-- Theorem `power_le`. -/
@[rep_depth krein]
theorem power_le (h : IsDrazinInverse a b k) {m : ℕ} (hm : k ≤ m) :
    a^(m + 1) * b = a^m := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
  calc
    a^(k + t + 1) * b = a^(t + (k + 1)) * b := by
      simp [Nat.add_assoc, Nat.add_left_comm]
    _ = (a^t * a^(k + 1)) * b := by rw [pow_add]
    _ = a^t * (a^(k + 1) * b) := by rw [mul_assoc]
    _ = a^t * a^k := by rw [h.power]
    _ = a^(t + k) := by rw [← pow_add]
    _ = a^(k + t) := by simp [Nat.add_comm]

/-- The complementary Fitting summand is nilpotent at index `k + 1`. -/
@[rep_depth krein]
theorem fittingNilpotentPart_pow_succ_eq_zero (h : IsDrazinInverse a b k) :
    (fittingNilpotentPart a b)^(k + 1) = 0 := by
  have hleft : a^(k + 1) * complementaryProjection a b = 0 := by
    unfold complementaryProjection projection
    calc
      a^(k + 1) * (1 - a * b) = a^(k + 1) - (a^(k + 1) * a) * b := by
        noncomm_ring
      _ = a^(k + 1) - a^((k + 1) + 1) * b := by
        rw [← pow_succ a (k + 1)]
      _ = 0 := by
        rw [power_le h (Nat.le_succ k)]
        simp
  have hcomm : Commute a (complementaryProjection a b) :=
    (complementaryProjection_comm_self h).symm
  have hpow : (a * complementaryProjection a b)^(k + 1) =
      a^(k + 1) * (complementaryProjection a b)^(k + 1) := by
    exact hcomm.mul_pow (k + 1)
  have hQpow : (complementaryProjection a b)^(k + 1) = complementaryProjection a b := by
    exact InfoGeometry.Singular.Drazin.pow_succ_eq_of_idempotent
      (complementaryProjection_is_idempotent h) k
  unfold fittingNilpotentPart
  calc
    (a * complementaryProjection a b)^(k + 1)
        = a^(k + 1) * (complementaryProjection a b)^(k + 1) := hpow
    _ = a^(k + 1) * complementaryProjection a b := by rw [hQpow]
    _ = 0 := hleft

/-- Fixed-index uniqueness of the canonical Drazin inverse witness. -/
@[rep_depth krein]
theorem unique (hB : IsDrazinInverse a b k) (hC : IsDrazinInverse a c k) :
    b = c := by
  exact InfoGeometry.Singular.Drazin.Drazin_unique (toSingular hB) (toSingular hC)

/--
Index-independent uniqueness of the canonical Drazin inverse witness.
-/
@[rep_depth krein]
theorem unique_of_indices {ℓ : ℕ}
    (hB : IsDrazinInverse a b k) (hC : IsDrazinInverse a c ℓ) :
    b = c := by
  exact InfoGeometry.Singular.Drazin.Drazin_unique_of_indices
    (toSingular hB) (toSingular hC)

/-! ### Star transport of Drazin inverses -/

section Star

variable [StarRing R]

/--
If `a` is self-adjoint and `b` is a Drazin inverse of `a`, then `star b` is
also a Drazin inverse of `a` with the same index.

This is a root algebraic proof: take `star` of the Drazin equations, use
`star a = a`, and commute `star b` through powers of `a`.
-/
@[rep_depth krein]
theorem star_isDrazinInverse_of_selfAdjoint
    (h : IsDrazinInverse a b k)
    (ha : star a = a) :
    IsDrazinInverse a (star b) k := by
  have hcommStar : star b * a = a * star b := by
    simpa [ha] using congrArg star h.comm
  refine mk hcommStar.symm ?_ ?_
  · simpa [ha, mul_assoc] using congrArg star h.idempotent
  · have hpowStar : star b * a ^ (k + 1) = a ^ k := by
      simpa [ha] using congrArg star h.power
    have hcomm : Commute a (star b) := by
      exact hcommStar.symm
    calc
      a ^ (k + 1) * star b = star b * a ^ (k + 1) := by
        exact (hcomm.pow_left (k + 1)).eq
      _ = a ^ k := hpowStar

/--
Taking `star` transports a Drazin inverse of `a` to a Drazin inverse of
`star a`.

This canonical adapter routes through the compiled singular owner root
`Singular.Drazin.IsDrazinInverse.star_isDrazinInverse`.
-/
@[rep_depth krein]
  theorem star_isDrazinInverse
    (h : IsDrazinInverse a b k) :
    IsDrazinInverse (star a) (star b) k := by
  exact fromSingular
    (InfoGeometry.Singular.Drazin.IsDrazinInverse.star_isDrazinInverse (toSingular h))

/--
A Drazin inverse of a self-adjoint element is self-adjoint.

This canonical adapter routes through the compiled singular owner root
`Singular.Drazin.Drazin_star_eq_self_of_selfAdjoint`.
-/
@[rep_depth krein]
  theorem star_eq_self_of_selfAdjoint
    (h : IsDrazinInverse a b k)
    (ha : star a = a) :
    star b = b :=
  InfoGeometry.Singular.Drazin.Drazin_star_eq_self_of_selfAdjoint (toSingular h) ha

/--
If the base element is self-adjoint, the Drazin spectral projector `a*b` is a
star projection.

The self-adjointness of `b` is derived from the Drazin equations and uniqueness;
it is not a separate hypothesis.
-/
@[rep_depth krein]
theorem projection_isStarProjection_of_selfAdjoint
    (h : IsDrazinInverse a b k)
    (ha : star a = a) :
    IsStarProjection (projection a b) := by
  rw [isStarProjection_iff']
  refine ⟨projection_is_idempotent h, ?_⟩
  have hb : star b = b :=
    star_eq_self_of_selfAdjoint h ha
  unfold projection
  calc
    star (a * b) = star b * star a := by rw [star_mul]
    _ = b * a := by simp [ha, hb]
    _ = a * b := by exact h.comm.symm

end Star

/-! ### Core/nilpotent split construction -/

section CoreNilpotent

variable {u n d : R} {m : ℕ}

private lemma pow_succ_mul_eq_zero_of_mul_eq_zero
    (hxy : u * n = 0) :
    ∀ r : ℕ, u ^ (r + 1) * n = 0 := by
  intro r
  induction r with
  | zero =>
      simpa using hxy
  | succ r ih =>
      calc
        u ^ (r + 1 + 1) * n = u * (u ^ (r + 1) * n) := by
          rw [pow_succ']
          simp [mul_assoc]
        _ = 0 := by rw [ih, mul_zero]

private lemma pow_succ_mul_left_eq_zero_of_mul_eq_zero
    (hyx : n * u = 0) :
    ∀ r : ℕ, n ^ (r + 1) * u = 0 := by
  intro r
  induction r with
  | zero =>
      simpa using hyx
  | succ r ih =>
      calc
        n ^ (r + 1 + 1) * u = n * (n ^ (r + 1) * u) := by
          rw [pow_succ']
          simp [mul_assoc]
        _ = 0 := by rw [ih, mul_zero]

private lemma add_pow_succ_of_orthogonal
    (hun : u * n = 0)
    (hnu : n * u = 0) :
    ∀ r : ℕ, (u + n) ^ (r + 1) = u ^ (r + 1) + n ^ (r + 1) := by
  intro r
  induction r with
  | zero =>
      simp
  | succ r ih =>
      have hunr : u ^ (r + 1) * n = 0 :=
        pow_succ_mul_eq_zero_of_mul_eq_zero (u := u) (n := n) hun r
      have hnur : n ^ (r + 1) * u = 0 :=
        pow_succ_mul_left_eq_zero_of_mul_eq_zero (u := u) (n := n) hnu r
      calc
        (u + n) ^ (r + 1 + 1) = (u ^ (r + 1) + n ^ (r + 1)) * (u + n) := by
          rw [pow_succ, ih]
        _ = u ^ (r + 1) * u + u ^ (r + 1) * n
              + (n ^ (r + 1) * u + n ^ (r + 1) * n) := by
          noncomm_ring
        _ = u ^ (r + 1) * u + n ^ (r + 1) * n := by
          simp [hunr, hnur]
        _ = u ^ (r + 1 + 1) + n ^ (r + 1 + 1) := by
          simp [pow_succ]

private lemma core_pow_succ_succ_mul_inverse
    (hud : u * d = d * u)
    (hudu : u * d * u = u) :
    u ^ (m + 2) * d = u ^ (m + 1) := by
  have hu2d : u ^ 2 * d = u := by
    calc
      u ^ 2 * d = u * u * d := by simp [pow_two]
      _ = u * (u * d) := by rw [mul_assoc]
      _ = u * (d * u) := by rw [hud]
      _ = u * d * u := by rw [mul_assoc]
      _ = u := hudu
  calc
    u ^ (m + 2) * d = (u ^ m * u ^ 2) * d := by
      rw [pow_add]
    _ = u ^ m * (u ^ 2 * d) := by rw [mul_assoc]
    _ = u ^ m * u := by rw [hu2d]
    _ = u ^ (m + 1) := by rw [pow_succ]

/--
Core/nilpotent split constructor for Drazin inverses.

If `a = u + n`, the core part `u` has inverse `d` on its block, the nilpotent
part `n` has nilpotency index `m + 1`, and all cross-block products vanish,
then `d` is a Drazin inverse of `a` with index `m + 1`.

This is the algebraic root underneath a continuous Fitting decomposition:
subspace projections should be used upstream to produce the displayed block
equations, and this theorem then constructs the Drazin inverse.
-/
@[rep_depth krein]
theorem of_core_nilpotent_split
    (ha : a = u + n)
    (hun : u * n = 0)
    (hnu : n * u = 0)
    (hud : u * d = d * u)
    (hnd : n * d = 0)
    (hdn : d * n = 0)
    (hudu : u * d * u = u)
    (hdud : d * u * d = d)
    (hnil : n ^ (m + 1) = 0) :
    IsDrazinInverse a d (m + 1) := by
  subst a
  refine mk ?_ ?_ ?_
  · calc
      (u + n) * d = u * d + n * d := by rw [add_mul]
      _ = u * d := by rw [hnd, add_zero]
      _ = d * u := hud
      _ = d * u + d * n := by rw [hdn, add_zero]
      _ = d * (u + n) := by rw [mul_add]
  · calc
      d * (u + n) * d = (d * u + d * n) * d := by rw [mul_add]
      _ = (d * u) * d := by rw [hdn, add_zero]
      _ = d * u * d := by rw [mul_assoc]
      _ = d := hdud
  · have hpow_left :
        (u + n) ^ (m + 1 + 1) = u ^ (m + 1 + 1) + n ^ (m + 1 + 1) :=
      add_pow_succ_of_orthogonal (u := u) (n := n) hun hnu (m + 1)
    have hpow_right :
        (u + n) ^ (m + 1) = u ^ (m + 1) + n ^ (m + 1) :=
      add_pow_succ_of_orthogonal (u := u) (n := n) hun hnu m
    have hnil_succ : n ^ (m + 1 + 1) = 0 := by
      rw [pow_succ, hnil, zero_mul]
    have hcore : u ^ (m + 1 + 1) * d = u ^ (m + 1) := by
      simpa [Nat.add_assoc] using
        core_pow_succ_succ_mul_inverse (u := u) (d := d) (m := m) hud hudu
    calc
      (u + n) ^ (m + 1 + 1) * d
          = (u ^ (m + 1 + 1) + n ^ (m + 1 + 1)) * d := by rw [hpow_left]
      _ = u ^ (m + 1 + 1) * d + n ^ (m + 1 + 1) * d := by rw [add_mul]
      _ = u ^ (m + 1) := by rw [hcore, hnil_succ, zero_mul, add_zero]
      _ = u ^ (m + 1) + n ^ (m + 1) := by rw [hnil, add_zero]
      _ = (u + n) ^ (m + 1) := hpow_right.symm

end CoreNilpotent

/-! ### Fitting block data -/

/--
Explicit algebraic block data for a Drazin/Fitting decomposition.

This is the theorem-facing normal form for a complemented core/nilpotent split:
upstream submodule constructions should build the three displayed operators
`corePart`, `nilPart`, and `inversePart`, then prove these block equations.
-/
@[rep_depth krein]
structure DrazinFittingDecomposition (a : R) where
  corePart : R
  nilPart : R
  inversePart : R
  nilpotentIndex : ℕ
  decompose : a = corePart + nilPart
  core_mul_nil : corePart * nilPart = 0
  nil_mul_core : nilPart * corePart = 0
  core_comm_inverse : corePart * inversePart = inversePart * corePart
  nil_mul_inverse : nilPart * inversePart = 0
  inverse_mul_nil : inversePart * nilPart = 0
  core_inverse_core : corePart * inversePart * corePart = corePart
  inverse_core_inverse : inversePart * corePart * inversePart = inversePart
  nilpotent : nilPart ^ (nilpotentIndex + 1) = 0

/--
Construct a Drazin inverse from explicit Fitting block data.

This theorem is the named target for the continuous/submodule Fitting
construction. It contains no certificate shortcut: the proof reduces the block
data to the root algebraic theorem `of_core_nilpotent_split`.
-/
@[rep_depth krein]
theorem exists_drazinInverse_of_fittingDecomposition
    {a : R}
    (D : DrazinFittingDecomposition a) :
    ∃ (k : ℕ) (d : R), IsDrazinInverse a d k := by
  refine ⟨D.nilpotentIndex + 1, D.inversePart, ?_⟩
  exact of_core_nilpotent_split
    (a := a)
    (u := D.corePart)
    (n := D.nilPart)
    (d := D.inversePart)
    (m := D.nilpotentIndex)
    D.decompose
    D.core_mul_nil
    D.nil_mul_core
    D.core_comm_inverse
    D.nil_mul_inverse
    D.inverse_mul_nil
    D.core_inverse_core
    D.inverse_core_inverse
    D.nilpotent

/-! ### Continuous operator block data -/

/--
Continuous-operator block data for a Drazin/Fitting split.

This is intentionally named as block data, not as a completed submodule
construction. The fields are concrete bounded operators and equations. A later
submodule theorem should construct these operators from complementary invariant
subspaces and an inverse on the core.
-/
@[rep_depth krein]
structure ContinuousDrazinFittingBlockData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) where
  corePart : E →L[ℝ] E
  nilPart : E →L[ℝ] E
  inversePart : E →L[ℝ] E
  nilpotentIndex : ℕ
  decompose : A = corePart + nilPart
  core_mul_nil : corePart * nilPart = 0
  nil_mul_core : nilPart * corePart = 0
  core_comm_inverse : corePart * inversePart = inversePart * corePart
  nil_mul_inverse : nilPart * inversePart = 0
  inverse_mul_nil : inversePart * nilPart = 0
  core_inverse_core : corePart * inversePart * corePart = corePart
  inverse_core_inverse : inversePart * corePart * inversePart = inversePart
  nilpotent : nilPart ^ (nilpotentIndex + 1) = 0

namespace ContinuousDrazinFittingBlockData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : E →L[ℝ] E}

/--
Convert continuous bounded-operator block data into the algebraic
`DrazinFittingDecomposition` normal form.
-/
@[rep_depth krein]
def toDrazinFittingDecomposition
    (S : ContinuousDrazinFittingBlockData A) :
    DrazinFittingDecomposition A where
  corePart := S.corePart
  nilPart := S.nilPart
  inversePart := S.inversePart
  nilpotentIndex := S.nilpotentIndex
  decompose := S.decompose
  core_mul_nil := S.core_mul_nil
  nil_mul_core := S.nil_mul_core
  core_comm_inverse := S.core_comm_inverse
  nil_mul_inverse := S.nil_mul_inverse
  inverse_mul_nil := S.inverse_mul_nil
  core_inverse_core := S.core_inverse_core
  inverse_core_inverse := S.inverse_core_inverse
  nilpotent := S.nilpotent

/--
Construct a Drazin inverse from continuous bounded-operator block data.

The proof is a transparent reduction to the algebraic
`exists_drazinInverse_of_fittingDecomposition` theorem.
-/
@[rep_depth krein]
theorem exists_drazinInverse
    (S : ContinuousDrazinFittingBlockData A) :
    ∃ (k : ℕ) (D : E →L[ℝ] E), IsDrazinInverse A D k :=
  exists_drazinInverse_of_fittingDecomposition S.toDrazinFittingDecomposition

end ContinuousDrazinFittingBlockData

/-! ### Submodule/projection split data -/

/--
Continuous submodule/projection data for a Drazin/Fitting split.

The submodules `Core` and `Nil` are represented by bounded projections
`Pcore` and `Pnil`. The actual block operators are not stored: they are
constructed as `A * Pcore`, `A * Pnil`, and `Dcore`.

The equations say that the projections split the identity, are mutually
orthogonal, commute with `A`, that `Dcore` is an inverse for the core block,
and that the nil block is nilpotent.
-/
@[rep_depth krein]
structure ContinuousDrazinFittingSubmoduleSplit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) where
  Core : Submodule ℝ E
  Nil : Submodule ℝ E
  Pcore : E →L[ℝ] E
  Pnil : E →L[ℝ] E
  Dcore : E →L[ℝ] E
  nilpotentIndex : ℕ
  Pcore_range : Pcore.range = Core
  Pnil_range : Pnil.range = Nil
  projections_sum : Pcore + Pnil = 1
  projections_core_nil : Pcore * Pnil = 0
  projections_nil_core : Pnil * Pcore = 0
  A_comm_core : A * Pcore = Pcore * A
  A_comm_nil : A * Pnil = Pnil * A
  core_comm_inverse : (A * Pcore) * Dcore = Dcore * (A * Pcore)
  nil_projection_mul_inverse : Pnil * Dcore = 0
  inverse_mul_nil_projection : Dcore * Pnil = 0
  core_inverse_core : (A * Pcore) * Dcore * (A * Pcore) = A * Pcore
  inverse_core_inverse : Dcore * (A * Pcore) * Dcore = Dcore
  nilpotent : (A * Pnil) ^ (nilpotentIndex + 1) = 0

namespace ContinuousDrazinFittingSubmoduleSplit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : E →L[ℝ] E}

/-- The core block operator associated to a submodule/projection split. -/
@[rep_depth krein]
def corePart (S : ContinuousDrazinFittingSubmoduleSplit A) : E →L[ℝ] E :=
  A * S.Pcore

/-- The nilpotent block operator associated to a submodule/projection split. -/
@[rep_depth krein]
def nilPart (S : ContinuousDrazinFittingSubmoduleSplit A) : E →L[ℝ] E :=
  A * S.Pnil

/-- The inverse block operator associated to a submodule/projection split. -/
@[rep_depth krein]
def inversePart (S : ContinuousDrazinFittingSubmoduleSplit A) : E →L[ℝ] E :=
  S.Dcore

/--
Construct bounded-operator block data from actual submodule/projection split
data.
-/
@[rep_depth krein]
def toBlockData
    (S : ContinuousDrazinFittingSubmoduleSplit A) :
    ContinuousDrazinFittingBlockData A where
  corePart := S.corePart
  nilPart := S.nilPart
  inversePart := S.inversePart
  nilpotentIndex := S.nilpotentIndex
  decompose := by
    calc
      A = A * 1 := by simp
      _ = A * (S.Pcore + S.Pnil) := by rw [S.projections_sum]
      _ = A * S.Pcore + A * S.Pnil := by rw [mul_add]
  core_mul_nil := by
    unfold corePart nilPart
    calc
      (A * S.Pcore) * (A * S.Pnil)
          = A * (S.Pcore * A) * S.Pnil := by noncomm_ring
      _ = A * (A * S.Pcore) * S.Pnil := by rw [← S.A_comm_core]
      _ = A * A * (S.Pcore * S.Pnil) := by noncomm_ring
      _ = 0 := by rw [S.projections_core_nil, mul_zero]
  nil_mul_core := by
    unfold corePart nilPart
    calc
      (A * S.Pnil) * (A * S.Pcore)
          = A * (S.Pnil * A) * S.Pcore := by noncomm_ring
      _ = A * (A * S.Pnil) * S.Pcore := by rw [← S.A_comm_nil]
      _ = A * A * (S.Pnil * S.Pcore) := by noncomm_ring
      _ = 0 := by rw [S.projections_nil_core, mul_zero]
  core_comm_inverse := by
    exact S.core_comm_inverse
  nil_mul_inverse := by
    unfold nilPart inversePart
    calc
      (A * S.Pnil) * S.Dcore = A * (S.Pnil * S.Dcore) := by rw [mul_assoc]
      _ = 0 := by rw [S.nil_projection_mul_inverse, mul_zero]
  inverse_mul_nil := by
    unfold nilPart inversePart
    calc
      S.Dcore * (A * S.Pnil) = S.Dcore * (S.Pnil * A) := by rw [S.A_comm_nil]
      _ = (S.Dcore * S.Pnil) * A := by rw [mul_assoc]
      _ = 0 := by rw [S.inverse_mul_nil_projection, zero_mul]
  core_inverse_core := by
    exact S.core_inverse_core
  inverse_core_inverse := by
    exact S.inverse_core_inverse
  nilpotent := by
    unfold nilPart
    exact S.nilpotent

/--
Convert actual submodule/projection split data into the algebraic
`DrazinFittingDecomposition` normal form.
-/
@[rep_depth krein]
def toDrazinFittingDecomposition
    (S : ContinuousDrazinFittingSubmoduleSplit A) :
    DrazinFittingDecomposition A :=
  S.toBlockData.toDrazinFittingDecomposition

/--
Construct a Drazin inverse from actual continuous submodule/projection split
data.
-/
@[rep_depth krein]
theorem exists_drazinInverse
    (S : ContinuousDrazinFittingSubmoduleSplit A) :
    ∃ (k : ℕ) (D : E →L[ℝ] E), IsDrazinInverse A D k :=
  exists_drazinInverse_of_fittingDecomposition S.toDrazinFittingDecomposition

end ContinuousDrazinFittingSubmoduleSplit

/-- Lemma `inverse_eq_pow_mul_pow`. -/
@[rep_depth krein]
lemma inverse_eq_pow_mul_pow (h : IsDrazinInverse a b k) (n : ℕ) :
    b = b^(n + 1) * a^n := by
  have hba : Commute b a := by
    show b * a = a * b
    exact h.comm.symm
  have hbase : b * b * a = b := by
    calc
      b * b * a = b * (b * a) := by rw [mul_assoc]
      _ = b * (a * b) := by rw [h.comm.symm]
      _ = (b * a) * b := by rw [← mul_assoc]
      _ = b := h.idempotent
  have hpow : ∀ n : ℕ, b^(n + 1) * a^n = b := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        calc
          b^(n + 2) * a^(n + 1)
              = (b^(n + 1) * b) * (a^n * a) := by simp [pow_succ]
          _ = b^(n + 1) * (b * a^n) * a := by simp [mul_assoc]
          _ = b^(n + 1) * (a^n * b) * a := by rw [(hba.pow_right n).eq]
          _ = (b^(n + 1) * a^n) * b * a := by simp [mul_assoc]
          _ = b * b * a := by rw [ih]
          _ = b := hbase
  exact (hpow n).symm

/-- Definition `core`. -/
@[rep_depth krein]
def core (a b : R) : R := a * a * b
/-- Definition `nilpotent`. -/
@[rep_depth krein]
def nilpotent (a b : R) : R := a - (core a b)

/-- The Drazin core part is the original element followed by the regular projector. -/
@[rep_depth krein]
theorem core_eq_mul_projection :
    core a b = a * projection a b := by
  simp [core, projection, mul_assoc]

/-- The Drazin nilpotent part is the original element followed by the null projector. -/
@[rep_depth krein]
theorem nilpotent_eq_mul_complementaryProjection :
    nilpotent a b = a * complementaryProjection a b := by
  simp [nilpotent, core, complementaryProjection, projection, mul_sub, mul_assoc]

/-- Theorem `nilpotent_comm_self`. -/
@[rep_depth krein]
theorem nilpotent_comm_self (h : IsDrazinInverse a b k) :
    a * (nilpotent a b) = (nilpotent a b) * a := by
  have hcore : a * core a b = core a b * a := by
    unfold core
    calc
      a * (a * a * b) = a * a * (a * b) := by simp [mul_assoc]
      _ = a * a * (b * a) := by rw [h.comm]
      _ = (a * a * b) * a := by simp [mul_assoc]
  unfold nilpotent
  calc
    a * (a - core a b) = a * a - a * core a b := by rw [mul_sub]
    _ = a * a - core a b * a := by rw [hcore]
    _ = (a - core a b) * a := by rw [sub_mul]

/-- Theorem `fitting_decomposition`. -/
@[rep_depth krein]
theorem fitting_decomposition (_h : IsDrazinInverse a b k) :
    a = (core a b) + (nilpotent a b) := by
  have hrhs : core a b + nilpotent a b = a := by
    unfold core nilpotent
    calc
      a * a * b + (a - (a * a * b))
          = a * a * b + (a + -(a * a * b)) := by rw [sub_eq_add_neg]
      _ = a + (a * a * b + -(a * a * b)) := by
            simp [add_left_comm]
      _ = a := by simp
  exact hrhs.symm

/-- The Drazin core part annihilates the nilpotent part on the left. -/
@[rep_depth krein]
theorem core_mul_nilpotent_eq_zero (h : IsDrazinInverse a b k) :
    core a b * nilpotent a b = 0 := by
  let P : R := projection a b
  let Q : R := complementaryProjection a b
  have hCore : core a b = a * P := by
    simp [core, P, projection, mul_assoc]
  have hNil : nilpotent a b = a * Q := by
    simp [nilpotent, core, Q, complementaryProjection, projection, mul_sub, mul_assoc]
  have hCommP : P * a = a * P := by
    calc
      P * a = (a * b) * a := by rfl
      _ = a * (b * a) := by rw [mul_assoc]
      _ = a * (a * b) := by rw [← h.comm]
      _ = a * P := by rfl
  have hOrth : P * Q = 0 := by
    simpa [P, Q] using projection_mul_complementaryProjection h
  calc
    core a b * nilpotent a b = (a * P) * (a * Q) := by rw [hCore, hNil]
    _ = a * (P * a) * Q := by noncomm_ring
    _ = a * (a * P) * Q := by rw [hCommP]
    _ = a * a * (P * Q) := by noncomm_ring
    _ = 0 := by rw [hOrth]; simp

/-- The Drazin nilpotent part annihilates the core part on the left. -/
@[rep_depth krein]
theorem nilpotent_mul_core_eq_zero (h : IsDrazinInverse a b k) :
    nilpotent a b * core a b = 0 := by
  let P : R := projection a b
  let Q : R := complementaryProjection a b
  have hCore : core a b = a * P := by
    simp [core, P, projection, mul_assoc]
  have hNil : nilpotent a b = a * Q := by
    simp [nilpotent, core, Q, complementaryProjection, projection, mul_sub, mul_assoc]
  have hCommP : P * a = a * P := by
    calc
      P * a = (a * b) * a := by rfl
      _ = a * (b * a) := by rw [mul_assoc]
      _ = a * (a * b) := by rw [← h.comm]
      _ = a * P := by rfl
  have hCommQ : Q * a = a * Q := by
    calc
      Q * a = (1 - P) * a := by rfl
      _ = a - P * a := by rw [sub_mul, one_mul]
      _ = a - a * P := by rw [hCommP]
      _ = a * (1 - P) := by rw [mul_sub, mul_one]
      _ = a * Q := by rfl
  have hOrth : Q * P = 0 := by
    simpa [P, Q] using complementaryProjection_mul_projection h
  calc
    nilpotent a b * core a b = (a * Q) * (a * P) := by rw [hCore, hNil]
    _ = a * (Q * a) * P := by noncomm_ring
    _ = a * (a * Q) * P := by rw [hCommQ]
    _ = a * a * (Q * P) := by noncomm_ring
    _ = 0 := by rw [hOrth]; simp

/-- The earlier Fitting regular summand is the later Drazin core notation. -/
@[rep_depth krein]
theorem fittingRegularPart_eq_core :
    fittingRegularPart a b = core a b := by
  unfold fittingRegularPart core projection
  noncomm_ring

/-- The earlier Fitting nilpotent summand is the later Drazin nilpotent notation. -/
@[rep_depth krein]
theorem fittingNilpotentPart_eq_nilpotent :
    fittingNilpotentPart a b = nilpotent a b := by
  rw [nilpotent_eq_mul_complementaryProjection]
  rfl

/-- The Fitting regular summand annihilates the Fitting nilpotent summand on the left. -/
@[rep_depth krein]
theorem fittingRegularPart_mul_fittingNilpotentPart_eq_zero
    (h : IsDrazinInverse a b k) :
    fittingRegularPart a b * fittingNilpotentPart a b = 0 := by
  rw [fittingRegularPart_eq_core, fittingNilpotentPart_eq_nilpotent]
  exact core_mul_nilpotent_eq_zero h

/-- The Fitting nilpotent summand annihilates the Fitting regular summand on the left. -/
@[rep_depth krein]
theorem fittingNilpotentPart_mul_fittingRegularPart_eq_zero
    (h : IsDrazinInverse a b k) :
    fittingNilpotentPart a b * fittingRegularPart a b = 0 := by
  rw [fittingRegularPart_eq_core, fittingNilpotentPart_eq_nilpotent]
  exact nilpotent_mul_core_eq_zero h

end IsDrazinInverse
end InfoGeometry.Canonical.Drazin
