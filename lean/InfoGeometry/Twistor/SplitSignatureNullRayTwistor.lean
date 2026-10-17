/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

/-!
# Incidence constancy along null rays in split-signature twistor space

Real twistor space $\mathbb{T}_{\mathbb{R}} \cong \mathbb{R}^2 \oplus \mathbb{R}^2$ carries the
incidence relation of $\mathbb{R}^{2,2}$: a twistor $(\omega^A, \pi_{A'})$ is incident with a
spacetime matrix $x^{AA'}$ iff $\omega^A = \sum_{A'} x^{AA'}\pi_{A'}$.

This module proves the algebraic core of the classical statement that **a single projective
twistor is incident with an entire causal null ray**: the incidence relation does not move
along the ray.

The one ingredient is the self-annihilation of a `2`-spinor under the *alternating*
self-contraction,
$$\sum_{A'} \pi^{A'}\pi_{A'} = \varepsilon^{A'B'}\pi_{B'}\pi_{A'} = \pi_{1'}\pi_{0'} - \pi_{0'}\pi_{1'} = 0,$$
since the null direction carries the index raised by $\varepsilon$ while the incidence
relation contracts the index lowered by the symmetric $2\times 2$ delta.

**Scope note.** This is pure linear algebra over an arbitrary commutative ring; no analytic
continuity, no exponentiation, and no physics is used or asserted. The general
($\mathbb{M}^{1,3}$, complex, $i\neq 0$) twistor correspondence and the
$\mathrm{SO}^+(3,3)\cong\mathrm{SL}(4,\mathbb{R})$ conformal action are **not** claimed here,
nor is any $\mathrm{Cl}(3,3)\cong M_8(\mathbb{R})$ isomorphism (see the disclaimer in
`SplitOctonionClifford33Soldering`).
-/

namespace InfoGeometry.Twistor.SplitSignatureNullRay

open scoped BigOperators

variable {F : Type*} [CommRing F]

/-- Two-term sum over `Fin 2`, expanded. -/
theorem sum2 (f : Fin 2 → F) : (∑ A', f A') = f 0 + f 1 := by
  simp [Fin.sum_univ_succ]

/-- The split-signature alternating pairing $\varepsilon^{A'B'}$ on a real `2`-spinor index. -/
def eps22 (u v : Fin 2 → F) : F :=
  u 0 * v 1 - u 1 * v 0

theorem eps22_self (u : Fin 2 → F) : eps22 u u = 0 := by
  simp [eps22]; ring

theorem eps22_comm (u v : Fin 2 → F) : eps22 u v = -eps22 v u := by
  simp [eps22]; ring

/-- Raising a lowered `2`-spinor index with the symplectic form:
$\pi^{0'} = \varepsilon^{0'1'}\pi_{1'} = \pi_{1'}$, $\pi^{1'} = -\pi_{0'}$. -/
def epsLift (pi : Fin 2 → F) : Fin 2 → F :=
  fun A' => if A' = 0 then pi 1 else -pi 0

/-- **The alternating self-contraction vanishes.** This is the whole algebraic content of
the constancy argument: the null direction carries the *raised* index $\pi^{A'}$ while the
incidence relation contracts the *lowered* $\pi_{A'}$, and

$$\sum_{A'} \pi^{A'}\pi_{A'} = \varepsilon^{A'B'}\pi_{B'}\pi_{A'}
  = \pi_{1'}\pi_{0'} - \pi_{0'}\pi_{1'} = 0 .$$

The symmetric contraction $\sum_{A'}\pi^{A'}\pi_{A'}$ with a single (metric-raised) copy would
*not* vanish; the alternation is essential and is exactly what $\varepsilon$ supplies. -/
theorem epsLift_contraction_vanishes (pi : Fin 2 → F) :
    ∑ A', epsLift pi A' * pi A' = 0 := by
  rw [sum2]
  simp [epsLift]
  ring

/-- A rank-one null direction $p^{AA'} = lam^A \, pi^{A'}$. -/
def nullDir (lam pir : Fin 2 → F) (A A' : Fin 2) : F :=
  lam A * pir A'

/-- The null ray through $x_0$ with direction $lam \otimes pi^{A'}$:
$x^{AA'}(\tau) = x_0^{AA'} + \tau\, lam^A pi^{A'}$. -/
def nullRay (x₀ : Fin 2 → Fin 2 → F) (lam pir : Fin 2 → F) (tau : F) :
    Fin 2 → Fin 2 → F :=
  fun A A' => x₀ A A' + tau * nullDir lam pir A A'

/-- The incidence relation $\omega^A = \sum_{A'} x^{AA'} \pi_{A'}$ (contracting the lowered
index with the symmetric $2\times 2$ delta). -/
def incident (x : Fin 2 → Fin 2 → F) (pi : Fin 2 → F) (A : Fin 2) : F :=
  ∑ A', x A A' * pi A'

/-- **Constancy of the incident twistor along a null ray.** The derivative of the incidence
relation is $p^{AA'}\pi_{A'} = lam^A\pi^{A'}\pi_{A'} = lam^A\cdot 0$, so $\omega^A$ depends
only on $x_0$, not on $\tau$. Hence a single projective twistor $[Z^\alpha]$ is incident with
every point of a null ray. -/
theorem incident_const_along_nullRay (x₀ : Fin 2 → Fin 2 → F) (lam pi : Fin 2 → F) (tau : F)
    (A : Fin 2) :
    incident (nullRay x₀ lam (epsLift pi) tau) pi A = incident x₀ pi A := by
  rw [incident, incident]
  unfold nullRay
  rw [sum2, sum2]
  simp only [nullDir, add_mul]
  simp [epsLift]
  ring

/-- Specialised: the ray parameter does not matter, so $\tau = 0$ and $\tau = 1$ agree. -/
theorem incident_ray_equiv_zeroth_one (x₀ : Fin 2 → Fin 2 → F) (lam pi : Fin 2 → F)
    (A : Fin 2) :
    incident (nullRay x₀ lam (epsLift pi) 1) pi A
      = incident (nullRay x₀ lam (epsLift pi) 0) pi A :=
  (incident_const_along_nullRay x₀ lam pi 1 A).trans
    (incident_const_along_nullRay x₀ lam pi 0 A).symm

end InfoGeometry.Twistor.SplitSignatureNullRay
