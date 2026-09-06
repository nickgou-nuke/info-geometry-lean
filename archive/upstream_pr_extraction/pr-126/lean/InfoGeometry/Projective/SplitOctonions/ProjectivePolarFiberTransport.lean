import Mathlib.Tactic

/-!
# InfoGeometry.Projective.SplitOctonions.ProjectivePolarFiberTransport

Incidence fibers as Erlangen-invariant projective geometry.

A twistor/spacetime point is modeled here as an incidence fiber:

  {Y | B X Y = 0}

If a group action preserves the polar form up to a scalar factor,

  B(gX, gY) = χ(g) B(X,Y),

then the action transports incidence fibers exactly:

  g · Fiber(X) = Fiber(g · X).

No wrappers.
No quotient construction.
No `sorry`.
-/

namespace InfoGeometry.Projective.SplitOctonions.ProjectivePolarFiberTransport

/-- Incidence fiber of a representative `X`: all representatives incident with `X`. -/
def incidenceFiber
    {R Carrier : Type*}
    [Zero R]
    (polar : Carrier → Carrier → R)
    (X : Carrier) : Set Carrier :=
  {Y : Carrier | polar X Y = 0}

/--
A group action preserving the polar form up to a scalar factor transports
incidence fibers exactly.

This is the concrete Erlangen/twistor statement:

  `Set.image (act g) (incidenceFiber polar X)
     = incidenceFiber polar (act g X)`.

It says the incidence-defined “celestial sphere” attached to `X` is not tied to
coordinates; it is carried functorially by the symmetry action.
-/
theorem incidenceFiber_image_eq
    {R G Carrier : Type*}
    [CommRing R] [Group G]
    (polar : Carrier → Carrier → R)
    (act : G → Carrier → Carrier)
    (scale : G → R)
    (hact_one :
      ∀ X : Carrier,
        act 1 X = X)
    (hact_mul :
      ∀ (g h : G) (X : Carrier),
        act (g * h) X = act g (act h X))
    (hcov :
      ∀ (g : G) (X Y : Carrier),
        polar (act g X) (act g Y) = scale g * polar X Y)
    (g : G)
    (X : Carrier) :
    Set.image (act g) (incidenceFiber polar X)
      =
    incidenceFiber polar (act g X) := by
  ext Y
  constructor
  · intro hY
    rcases hY with ⟨Y₀, hY₀, hImage⟩
    unfold incidenceFiber at hY₀
    rw [← hImage]
    unfold incidenceFiber
    change polar (act g X) (act g Y₀) = 0
    rw [hcov g X Y₀]
    rw [hY₀]
    ring
  · intro hY
    refine ⟨act g⁻¹ Y, ?_, ?_⟩
    · unfold incidenceFiber at hY ⊢
      have hpre :
          polar (act g⁻¹ (act g X)) (act g⁻¹ Y)
            =
          scale g⁻¹ * polar (act g X) Y :=
        hcov g⁻¹ (act g X) Y
      have hx : act g⁻¹ (act g X) = X := by
        calc
          act g⁻¹ (act g X)
              = act (g⁻¹ * g) X := by
                  exact (hact_mul g⁻¹ g X).symm
          _   = act 1 X := by rw [inv_mul_cancel]
          _   = X := hact_one X
      rw [hx] at hpre
      rw [hY, mul_zero] at hpre
      exact hpre
    · calc
        act g (act g⁻¹ Y)
            = act (g * g⁻¹) Y := by
                exact (hact_mul g g⁻¹ Y).symm
        _   = act 1 Y := by rw [mul_inv_cancel]
        _   = Y := hact_one Y

/--
Membership form of `incidenceFiber_image_eq`.

This is often the easier theorem for downstream rewriting:
`Y` is incident with `gX` iff it is the image of something incident with `X`.
-/
theorem mem_incidenceFiber_iff_exists_preimage
    {R G Carrier : Type*}
    [CommRing R] [Group G]
    (polar : Carrier → Carrier → R)
    (act : G → Carrier → Carrier)
    (scale : G → R)
    (hact_one :
      ∀ X : Carrier,
        act 1 X = X)
    (hact_mul :
      ∀ (g h : G) (X : Carrier),
        act (g * h) X = act g (act h X))
    (hcov :
      ∀ (g : G) (X Y : Carrier),
        polar (act g X) (act g Y) = scale g * polar X Y)
    (g : G)
    (X Y : Carrier) :
    Y ∈ incidenceFiber polar (act g X)
      ↔
    ∃ Y₀ ∈ incidenceFiber polar X, act g Y₀ = Y := by
  have hset :=
    incidenceFiber_image_eq
      polar act scale hact_one hact_mul hcov g X
  rw [← hset]
  rfl

end InfoGeometry.Projective.SplitOctonions.ProjectivePolarFiberTransport
