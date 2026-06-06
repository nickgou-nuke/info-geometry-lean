# Skill: categorical-infrastructure-projection

Project high-level categorical infrastructure onto concrete matrix computations.
This is the inverse of abstraction: given an object in a category, compute its
explicit matrix representation; given a theorem about a functor, write its
componentwise equivalent.

**GEPA evolution:** `tools/infra/gepa_categorical_projection.py --evolve --generations 10`

## When to use

- A categorical structure exists (`RealKVect`, `ModuleCat ℂ`, colimit, etc.)
- A concrete matrix computation is needed as an instance (`hadjiivanovMonodromy`,
  `fibonacciBMatrix`, `Fmatrix_asRealK`, etc.)
- A bilingual translation is needed (complex `i` → real `K = clockAxis`)

## Procedure

### Phase 1: Read (understanding the layers)

1. **Categorical layer**: read the target category and functors
   - `Quantum/RealKCategory.lean` — `RealKVect`, `complexToRealK`, `realKToComplex`
   - `Categorical/*.lean` — categorical surfaces
   - `Canonical/BilingualRealHestenesDictionary.lean` — `i ↦ K` translation theorems

2. **Concrete owner**: read the matrix-level source file
   - `Clifford/LogCftMonodromy.lean` — `hadjiivanovMonodromy h`, `virasoroL0Cell h`

3. **Bridge theorems**: read existing connections
   - `Canonical/HadjiivanovMonodromyProjection.lean` — bilingual real form

### Phase 2: Identify (the projection)

Determine the triple:

```
Carrier object  = complexToRealK.obj(ℂ²)   (ℂ² as a RealKVect)
Matrix as morph = complexToRealK.map(M)     (M as a K-commuting ℝ-linear map)
Bilingual key   = realPhaseAxis_eq_complex_i (i ↦ K)
```

### Phase 3: Project (write the Lean code)

For each matrix `M ∈ Mat(n, ℂ)`:

```
def M_asRealK : monodromyCarrier ⟶ monodromyCarrier :=
  complexToRealK.map (ModuleCat.ofHom (ℂ-linear map corresponding to M))
```

Prove:
- `commute_K` (functorial: the map is ℂ-linear, so it commutes with K)
- algebraic properties (involution, nilpotency, Hecke relation)
- label unsolved parts as BUCKET 3 with explicit `sorry`

### Phase 4: Never

- ❌ Write a bridge file — use `import` directly
- ❌ Duplicate categorical infrastructure at matrix level
- ❌ Use `Complex.I` when `BilingualRealHestenesDictionary` gives `K`
- ❌ Write a functor when `complexToRealK` already exists

---

## GEPA genome encoding

Each categorical-infrastructure-projection task is encoded as a genome:

```json
{
  "task_id": "monodromy_power_binomial",
  "carrier": "monodromyCarrier",
  "matrix": "hadjiivanovMonodromy h",
  "category": "RealKVect",
  "functor": "complexToRealK",
  "bilingual_key": "realPhaseAxis_eq_complex_i",
  "proof_strategy": "rotor_mul + nilpotent_binomial_expansion",
  "fitness": 0.0,
  "status": "open"
}
```

The GEPA evolves the `proof_strategy` field across a population of candidate
approaches, using `lake build` as the fitness oracle.
