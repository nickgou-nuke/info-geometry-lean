import InfoGeometry.Canonical.KreinPositionalScoreBridge
import InfoGeometry.GrandCanonical.Core

/-!
# Relative group scores for attention contexts

This is the attention-specific readout of the existing
`PairingGroupRepresentation` owner.  A head supplies keys and their group
positions; the score theorem below says that simultaneous transport depends
only on the relative group element.  No tensor-product, spectral, or physical
interpretation is built into this carrier.
-/

namespace InfoGeometry.Canonical.AttentionRelativeGroupBridge

open InfoGeometry.Canonical.PositionalDynamicsRegimeBridge
open InfoGeometry.GrandCanonical

variable {H G V ι : Type*} [Group G]

/-- A finite or infinite collection of keys and values equipped with group
positions, for a pairing-preserving group representation. -/
structure RelativeAttentionContext
    (R : PairingGroupRepresentation H G) where
  keys : ι → H
  values : ι → V
  positions : ι → G

namespace RelativeAttentionContext

variable {R : PairingGroupRepresentation H G}

/-- The transported query-key score at a head position. -/
def score (C : RelativeAttentionContext (H := H) (G := G) (V := V) (ι := ι) R)
    (q : H) (g : G) (i : ι) : ℝ :=
  R.pairing (R.action g q)
    (R.action (C.positions i) (C.keys i))

/-- Simultaneous transport of a query and a key is a relative-position score.
This is the exact group-theoretic content behind positional attention. -/
theorem score_eq_relative
    (C : RelativeAttentionContext (H := H) (G := G) (V := V) (ι := ι) R)
    (q : H) (g : G) (i : ι) :
    C.score q g i =
      R.pairing q (R.action (g⁻¹ * C.positions i) (C.keys i)) := by
  exact R.relative_score q (C.keys i) g (C.positions i)

/-! ## Common-frame covariance -/

/-- Transport the positional frame by left multiplication.  Keys and values are
unchanged; only the group labels of the positions are moved. -/
def leftTransport
    (h : G)
    (C : RelativeAttentionContext (H := H) (G := G) (V := V) (ι := ι) R) :
    RelativeAttentionContext (H := H) (G := G) (V := V) (ι := ι) R where
  keys := C.keys
  values := C.values
  positions := fun i => h * C.positions i

/-- A simultaneous left transport of query, frame, and key positions leaves
the relative attention score unchanged.  This is the precise covariance law
behind relative positional encodings. -/
theorem score_leftTransport
    (C : RelativeAttentionContext (H := H) (G := G) (V := V) (ι := ι) R)
    (h g : G) (q : H) (i : ι) :
    (C.leftTransport h).score (R.action h q) (h * g * h⁻¹) i =
      C.score q g i := by
  rw [(C.leftTransport h).score_eq_relative, C.score_eq_relative]
  have hrel :
      (h * g * h⁻¹)⁻¹ * (h * C.positions i) =
        h * (g⁻¹ * C.positions i) := by
    group
  change R.pairing (R.action h q)
      (R.action ((h * g * h⁻¹)⁻¹ * (h * C.positions i))
        (C.keys i)) = _
  rw [hrel, R.action_mul]
  exact R.pairing_isometry h q
    (R.action (g⁻¹ * C.positions i) (C.keys i))

/-! ## Gibbs readout of the relative score -/

/-- Grand-canonical parameters whose energy is the negative relative score of
a query against the positioned key at each index. -/
noncomputable def params
    (C : RelativeAttentionContext (H := H) (G := G) (V := V) (ι := ι) R)
    (q : H) (g : G) : GrandCanonicalParams ι where
  energy := fun i => -C.score q g i

/-- Gibbs weights obtained from the relative group score. -/
noncomputable def weights
    [Fintype ι]
    (C : RelativeAttentionContext (H := H) (G := G) (V := V) (ι := ι) R)
    (q : H) (g : G) (β : ℝ) (i : ι) : ℝ :=
  gibbsWeight (C.params q g) β i

theorem weights_sum_one
    [Fintype ι] [Nonempty ι]
    (C : RelativeAttentionContext (H := H) (G := G) (V := V) (ι := ι) R)
    (q : H) (g : G) (β : ℝ) :
    ∑ i, C.weights q g β i = 1 := by
  simpa [weights] using gibbsWeight_sum_one (C.params q g) β

theorem weights_nonneg
    [Fintype ι] [Nonempty ι]
    (C : RelativeAttentionContext (H := H) (G := G) (V := V) (ι := ι) R)
    (q : H) (g : G) (β : ℝ) (i : ι) :
    0 ≤ C.weights q g β i := by
  simpa [weights] using gibbsWeight_nonneg (C.params q g) β i

/-! The normalized thermodynamic readout inherits the same covariance. -/

theorem weights_leftTransport
    [Fintype ι] [Nonempty ι]
    (C : RelativeAttentionContext (H := H) (G := G) (V := V) (ι := ι) R)
    (h g : G) (q : H) (β : ℝ) (i : ι) :
    (C.leftTransport h).weights (R.action h q) (h * g * h⁻¹) β i =
      C.weights q g β i := by
  unfold weights params
  apply congrArg (fun p : GrandCanonicalParams ι => gibbsWeight p β i)
  congr 1
  funext j
  rw [score_leftTransport]

end RelativeAttentionContext

/-- A multi-head family of relative attention contexts.  Heads remain an
indexed family; interactions between heads require additional structure. -/
structure RelativeAttentionHeads (n : ℕ)
    (R : PairingGroupRepresentation H G) where
  heads : Fin n → RelativeAttentionContext (H := H) (G := G) (V := V)
    (ι := ι) R

namespace RelativeAttentionHeads

variable {n : ℕ} {R : PairingGroupRepresentation H G}

/-- Every head in the family has the same relative-position law, with its own
key and position data. -/
theorem head_score_eq_relative
    (A : RelativeAttentionHeads (H := H) (G := G) (V := V) (ι := ι) n R)
    (h : Fin n) (q : H) (g : G) (i : ι) :
    (A.heads h).score q g i =
      R.pairing q
        (R.action (g⁻¹ * (A.heads h).positions i)
          ((A.heads h).keys i)) := by
  exact (A.heads h).score_eq_relative q g i

end RelativeAttentionHeads

end InfoGeometry.Canonical.AttentionRelativeGroupBridge
