import Mathlib.Tactic

/-!
# Brillouin Klein bottle from artificial gauge fields

Formalizes the Z₂ topological invariant derived from the non-orientability of the Brillouin Klein bottle
arising from artificial Z₂ gauge fields, as detailed in Nature Communications (2022) 13:2215.

The momentum-space glide reflection ensures that the topology of the fundamental domain
is a Klein bottle. On this manifold, the standard Chern number classification reduces to Z₂.
The invariant is given by:
  ν = (1 / 2π) * (γ(0) + γ(-π)) mod 2
where γ(k_y) is the Berry phase. We represent the normalized phases (divided by 2π) as integers.
-/

namespace InfoGeometry.Topology.BrillouinKleinGauge

/--
The Brillouin Klein bottle Z₂ invariant.
If the boundaries γ(0) and γ(-π) are related by orientation reversal, their sum 
(normalized by 2π) gives the integer crossing number, which modulo 2 classifies the topological state.
-/
def klein_bottle_z2_invariant (gamma_0 gamma_pi : ℤ) : ℤ :=
  (gamma_0 + gamma_pi) % 2

/--
Theorem: The gauge invariance of the Z₂ classification.
A large gauge transformation shifts the boundary Berry phases by multiples of 2π.
Since we use the normalized winding integers, a gauge shift adds an even number (e.g., 2) to the sum
when considering the full loop. We show that shifting the normalized index by 2n preserves the Z₂ invariant.
-/
theorem klein_bottle_invariant_gauge_stable (gamma_0 gamma_pi n : ℤ) :
    klein_bottle_z2_invariant (gamma_0 + 2 * n) gamma_pi = 
    klein_bottle_z2_invariant gamma_0 gamma_pi := by
  dsimp [klein_bottle_z2_invariant]
  omega

end InfoGeometry.Topology.BrillouinKleinGauge
