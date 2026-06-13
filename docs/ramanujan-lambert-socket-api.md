# Ramanujan / Lambert socket API (truthful live surface)

This note records the exact Lean surfaces currently present in the repository for
Ramanujan-style odd-zeta identities and their centered / canonical bridges.

Honesty boundary:
- `InfoGeometry.Arithmetic.RamanujanOddZeta` provides the main typed analytic
  socket and theorem-safe consequences.
- `InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions` provides a centered
  readout target plus a finite verified `n = 1` Bernoulli / Apéry layer.
- `InfoGeometry.Canonical.SouriauTomitaZetaCenteredBridge` provides a small
  witness-gated canonical bridge socket.
- The direct theorem in `InfoGeometry.Arithmetic.RiemannZetaEquivalences`
  remains open debt (`sorry`), so this document does not describe it as native
  closure.

## 1. Owner analytic socket: `InfoGeometry.Arithmetic.RamanujanOddZeta`

Namespace:
- `InfoGeometry.Arithmetic.RamanujanOddZeta`

Core typed surfaces:

```lean
/-- The positive odd integer `2n+1` used in Ramanujan's odd-zeta formula. -/
def oddZetaIndex (n : ℕ) : ℕ

/-- The real readout of `ζ(2n+1)`. -/
def oddZetaValue (n : ℕ) : ℝ

/-- One positive-index Lambert term `k^{-(2n+1)} / (exp(2αk)-1)`. -/
def lambertTerm (n : ℕ) (α : ℝ) (k : ℕ+) : ℝ

/-- Ramanujan Lambert series over positive integers only. -/
def lambertSeries (n : ℕ) (α : ℝ) : ℝ

/-- The half-zeta plus Lambert block appearing on each thermal side. -/
def ramanujanThermalBlock (n : ℕ) (α : ℝ) : ℝ

/-- The positive-side modular weight `α^{-n}`. -/
def modularWeight (n : ℕ) (α : ℝ) : ℝ

/-- `(-β)^{-n}` represented as `(-1)^n * β^{-n}`. -/
def reflectedModularWeight (n : ℕ) (β : ℝ) : ℝ

/-- Bernoulli/factorial coefficient `B_m / m!` as a real number. -/
def bernoulliFactor (m : ℕ) : ℝ

/-- One finite Bernoulli anomaly summand in Ramanujan's formula. -/
def bernoulliAnomalyTerm (n : ℕ) (α β : ℝ) (k : ℕ) : ℝ

/-- The finite Bernoulli anomaly polynomial. -/
def bernoulliAnomaly (n : ℕ) (α β : ℝ) : ℝ

/-- Left-hand side of Ramanujan's odd-zeta transformation. -/
def ramanujanOddZetaLHS (n : ℕ) (α : ℝ) : ℝ

/-- Right-hand side of Ramanujan's odd-zeta transformation. -/
def ramanujanOddZetaRHS (n : ℕ) (α β : ℝ) : ℝ

/-- Proposition form of Ramanujan's odd-zeta transformation. -/
def RamanujanOddZetaFormula (n : ℕ) (α β : ℝ) : Prop
```

Type-safety / expansion lemmas already present:

```lean
theorem pnat_real_coe_pos (k : ℕ+) :
    0 < (k : ℝ)

theorem lambertTerm_positive_base (n : ℕ) (α : ℝ) (k : ℕ+) :
    0 < (k : ℝ) ∧
      lambertTerm n α k =
        ((k : ℝ) ^ (-(oddZetaIndex n : ℝ))) /
          (Real.exp (2 * α * (k : ℝ)) - 1)

theorem reflectedModularWeight_eq_sign_factored (n : ℕ) (β : ℝ) :
    reflectedModularWeight n β = (-1 : ℝ) ^ n * β ^ (-(n : ℝ))

theorem anomaly_index_le_of_mem_range {n k : ℕ}
    (hk : k ∈ Finset.range (n + 2)) :
    k ≤ n + 1

theorem ramanujanOddZetaLHS_eq (n : ℕ) (α : ℝ) :
    ramanujanOddZetaLHS n α =
      α ^ (-(n : ℝ)) *
        ((1 / 2 : ℝ) * oddZetaValue n + ∑' k : ℕ+, lambertTerm n α k)

theorem ramanujanOddZetaRHS_eq (n : ℕ) (α β : ℝ) :
    ramanujanOddZetaRHS n α β =
      ((-1 : ℝ) ^ n * β ^ (-(n : ℝ))) *
          ((1 / 2 : ℝ) * oddZetaValue n + ∑' k : ℕ+, lambertTerm n β k) -
        (2 : ℝ) ^ (2 * n) *
          (Finset.range (n + 2)).sum (fun k => bernoulliAnomalyTerm n α β k)
```

Proof-carrying analytic socket:

```lean
structure RamanujanOddZetaAnalyticSocket where
  identity :
    ∀ (n : ℕ) (α β : ℝ),
      0 < n →
      0 < α →
      0 < β →
      α * β = Real.pi ^ 2 →
      RamanujanOddZetaFormula n α β
```

Theorem-safe consequences from the socket:

```lean
theorem ramanujan_odd_zeta
    (R : RamanujanOddZetaAnalyticSocket)
    (n : ℕ) (hn : 0 < n) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α * β = Real.pi ^ 2) :
    RamanujanOddZetaFormula n α β

theorem ramanujan_odd_zeta_expanded
    (R : RamanujanOddZetaAnalyticSocket)
    (n : ℕ) (hn : 0 < n) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α * β = Real.pi ^ 2) :
    α ^ (-(n : ℝ)) *
        ((1 / 2 : ℝ) * oddZetaValue n + ∑' k : ℕ+, lambertTerm n α k) =
      ((-1 : ℝ) ^ n * β ^ (-(n : ℝ))) *
          ((1 / 2 : ℝ) * oddZetaValue n + ∑' k : ℕ+, lambertTerm n β k) -
        (2 : ℝ) ^ (2 * n) *
          (Finset.range (n + 2)).sum (fun k => bernoulliAnomalyTerm n α β k)
```

Meaning:
- this is the main honest owner surface for downstream use;
- it packages the analytic theorem as an input witness;
- it does not itself prove the analytic identity.

## 2. Centered arithmetic target: `InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions`

Namespace:
- `InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions`

Ramanujan target surface:

```lean
/-- Ramanujan-style odd-zeta transformation target, with supplied analytic sides. -/
def RamanujanLambertTransform
    (oddZetaReadout lambertSeriesSide bernoulliCorrectionSide : ℕ → ℂ) : Prop :=
  ∀ m, oddZetaReadout m = lambertSeriesSide m + bernoulliCorrectionSide m
```

Finite verified `n = 1` / Apéry Bernoulli layer:

```lean
def ramanujanBernoulliSide (B : ℕ → ℝ) (n : ℕ) (alpha beta : ℝ) : ℝ

def aperyBernoulliReadout (m : ℕ) : ℝ

theorem ramanujanBernoulliSide_apery_n1_explicit (alpha beta : ℝ) :
    ramanujanBernoulliSide aperyBernoulliReadout 1 alpha beta =
      alpha ^ 2 / 180 + alpha * beta / 36 + beta ^ 2 / 180

theorem ramanujanBernoulliSide_apery_n1_of_alpha_beta_eq_pi_sq
    {alpha beta : ℝ} (hαβ : alpha * beta = Real.pi ^ 2) :
    ramanujanBernoulliSide aperyBernoulliReadout 1 alpha beta =
      alpha ^ 2 / 180 + Real.pi ^ 2 / 36 + beta ^ 2 / 180

def aperyBernoulliDefectTau (tau : ℝ) : ℝ

theorem aperyBernoulliDefectTau_explicit {tau : ℝ} (hτ : tau ≠ 0) :
    aperyBernoulliDefectTau tau =
      Real.pi ^ 2 * (tau ^ 2 / 180 + 1 / 36 + (1 / tau ^ 2) / 180)
```

Meaning:
- this file gives a clean centered-coordinate surface;
- it includes a finite closed Bernoulli specialization;
- it does not claim the full infinite Ramanujan identity natively.

## 3. Canonical bridge socket: `InfoGeometry.Canonical.SouriauTomitaZetaCenteredBridge`

Namespace:
- `InfoGeometry.Canonical.SouriauTomitaZetaCenteredBridge`

Canonical socket surface:

```lean
def RamanujanLambertTransform
    (oddZetaReadout lambertSeriesSide bernoulliCorrectionSide : ℕ → ℂ) : Prop :=
  ∀ m, oddZetaReadout m = lambertSeriesSide m + bernoulliCorrectionSide m

structure RamanujanLambertSocket where
  oddZetaReadout : ℕ → ℂ
  lambertSeriesSide : ℕ → ℂ
  bernoulliCorrectionSide : ℕ → ℂ
  transform :
    RamanujanLambertTransform oddZetaReadout lambertSeriesSide bernoulliCorrectionSide

namespace RamanujanLambertSocket

theorem oddZeta_eq_lambert_plus_bernoulli
    (R : RamanujanLambertSocket) (m : ℕ) :
    R.oddZetaReadout m = R.lambertSeriesSide m + R.bernoulliCorrectionSide m
```

Meaning:
- this is a small bridge-level witness package;
- it is suitable for Souriau/Tomita-facing canonical readbacks;
- it is explicitly a socket, not an analytic proof.

## 4. Open debt that should not be overstated

File:
- `lean/InfoGeometry/Arithmetic/RiemannZetaEquivalences.lean`

It contains a direct theorem named:

```lean
theorem ramanujan_odd_zeta (n : ℕ) (hn : 0 < n) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α * β = Real.pi ^ 2) : ... := by
  sorry
```

So the current truthful status is:
- typed analytic socket: yes
- finite verified Bernoulli / Apéry layer: yes
- canonical witness-gated bridge socket: yes
- direct native analytic proof of full Ramanujan odd-zeta identity: not yet

## 5. Suggested downstream usage pattern

Use the owner arithmetic socket when you need the strongest theorem surface:

```lean
open InfoGeometry.Arithmetic.RamanujanOddZeta

variable (R : RamanujanOddZetaAnalyticSocket)
variable (n : ℕ) (hn : 0 < n) (α β : ℝ)
variable (hα : 0 < α) (hβ : 0 < β) (hαβ : α * β = Real.pi ^ 2)

#check ramanujan_odd_zeta R n hn α β hα hβ hαβ
#check ramanujan_odd_zeta_expanded R n hn α β hα hβ hαβ
```

Use the centered arithmetic file when you only need the target proposition or the
finite `ζ(3)` Bernoulli layer.

Use the canonical bridge socket when you want a minimal witness package inside a
Souriau/Tomita-facing bridge.
