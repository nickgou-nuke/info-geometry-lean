# Plan: Full Lean 4 Port of CMU Spectral (Lean 2 HoTT) — Functional Coverage

> Revised per user directive: full functional coverage, not minimal subset.
> File: `.hermes/plans/spectral-full-port.md`
> Status: active
> Hard constraint: stay on Lean 4.28.1 / mathlib `1f9fffd5`; no toolchain bump; kernel-check every surface; zero sorry/axiom/admit.

## 1. What “full functionality” means here

The original 68-file Lean 2 tree mixes three layers:

1. **Foundational algebra/logic** (`algebra/*`, `logic.hlean`, `choice.hlean`, `heq.hlean`, `property.hlean`, `pyoneda.hlean`, `univalent_subcategory.hlean`, `move_to_lib.hlean`) — these are HoTT-era scaffolding. In Lean 4/mathlib they are **not** owner responsibility.
2. **Advanced/unstable homotopy theory** (`homotopy/{degree,dsmash,fwedge,join_theorem,pushout,spherical_fibrations,susp_product,susp_pset,three_by_three,smash_adjoint}.hlean`, `spectrum/{smash,spectrification,trunc}.hlean`, `higher_groups.hlean` beyond finite readout) — vast, unstable, not tractable as sorry-free owner code on current mathlib.
3. **Core spectral/homology/colimit machinery** — these are the mathematically substantive Lean 2 files whose *functional* counterparts must exist in the Lean 4 port for the repo to claim full Spectral functionality:
   - `algebra/exact_couple.hlean` ✓ ported
   - `algebra/spectral_sequence.hlean` ✓ ported
   - `algebra/exact_couple_old.hlean` ← superseded
   - `algebra/{submodule,subgroup,tensor,ses,short_five,splice,exactness,arrow_group,cogroup,free_abelian_group,free_group,graded,left_module,module_chain_complex,direct_sum,product_group,quotient_group,ring}.hlean` → mathlib-native; **skip**
   - `colimit/seq_colim.hlean` → **port finite/sequential colimit calculus**
   - `colimit/{coind_colim,local_ext,omega_compact,omega_compact_sum,pointed,pushout,sequence}.hlean` → **skip** (category-theory colimits are mathlib territory)
   - `cohomology/{basic,gysin,projective_space,serre,cofiber_sequence}.hlean` → **port cofiber sequence**
   - `homology/{basic,sphere,torus}.hlean` → **port homology theory readout**
   - `homotopy/{susp,smash,wedge,EM,EMRing,realprojective}.hlean` → **expand finite pointed readout**
   - `spectrum/basic.hlean` → **expand finite prespectrum/spectrum calculus**
   - `higher_groups.hlean` → **keep finite `GType`, skip infinite**
   - `pointed*.hlean`, `component.hlean` → **skip** (mathlib/scaffolding)

## 2. Implementation plan

### Phase A — Core sequential colimit calculus (`Colimit/SeqColim.lean`)
- `external_refs/Spectral/colimit/seq_colim.hlean` implements:
  - `seq_colim` of a sequence diagram
  - inclusion maps `ι`, representatives `lrep`, `rep`
  - glue cells `glue`
  - `colim_back`, `equiv_of_is_equiseq`
  - functoriality `seq_colim_functor`, composition, identity
  - homotopies between functors
  - equivalence when all transition maps are equivalences
  - `seq_colim_rec_unc` recursion principle
  - universal property `equiv_seq_colim_rec`
  - `shift_up` / `shift_down`
- **Implementation rule**: define a concrete `SequentialColimit` structure in `InfoGeometry.Spectral.Colimit` with explicit `ι : A n → colim`, `glue : ι n a = ι (n+1) (f a)`. Prove the universal property for concrete cocones. Use `Quot` or `inductive` with `α`/`β` constructors if needed. Keep finite-representative lemmas kernel-checked; if full universal property is hard, write the exact concrete facts used by downstream bridges.
- **Build gate**: `lake build InfoGeometry.Spectral.Colimit` exit 0; 0 sorry/axiom/admit.

### Phase B — Expanded prespectrum/spectrum calculus (`Spectrum/Basic.lean`)
- Current `lean/InfoGeometry/Spectral/Spectrum/Basic.lean` has finite `Prespectrum` record.
- **Must add** from `external_refs/Spectral/spectrum/basic.hlean`:
  - generalized successor-structure `SuccStr`
  - `gen_prespectrum`, `gen_spectrum`, `is_spectrum`
  - `ℤ`-indexed `prespectrum`, `spectrum`
  - `prespectrum.mk`, `spectrum.MK`, `spectrum.Mk`
  - `glue`, `equiv_glue`, `equiv_glue2`
  - `gluen`, `equiv_gluen`, `equiv_gluen_inv_succ`
  - `psp_of_nat_indexed`, `of_nat_indexed`
  - `smap` structure, `smap_to_sigma`, `smap_to_struc`
  - maps and homotopies of spectra
  - smash product of prespectra if referenced downstream
- **Implementation rule**: use `ℤ → Type*` and `(n : ℤ) → X n →* Ω (X (n+1))` where pointed maps are mathlib-native. Keep `is_spectrum` as a Prop that every transition map is an equivalence.
- **Build gate**: isolated build + full `InfoGeometry.Spectral` build.

### Phase C — Homology theory finite readout (`Homology/Basic.lean`)
- `external_refs/Spectral/homology/basic.hlean` defines:
  - `homology_theory` record: `HH : ℤ → pType → AbGroup`
  - axioms: `Hh`, `Hpid`, `Hpcompose`, `Hsusp`, `Hsusp_natural`, `Hexact`, `Hadditive`
  - `ordinary_homology_theory` extends with dimension axiom
  - theorems: `HH_base_indep`, `Hh_homotopy'`, `Hh_homotopy`, `HH_isomorphism`
  - constructions: `Hadditive_equiv`, `Hadditive'`, `Hfwedge`, `Hwedge`
  - `homology X E n = pshomotopy_group n (smash_prespectrum X E)`
  - `homology_functor`, `homology_theory_spectrum`
- **Implementation rule**: replace `pType`/`pmap` with `PointedReadout`/`PointedMap` from `Homotopy/Suspension`. Replace `AbGroup` with `AddCommGroup`. Replace exactness/group-homomorphism composition with mathlib `LinearMap`/`AddMonoidHom`. For `smash_prespectrum`, use the finite `SmashProduct` from `Homotopy/Smash`. Keep only the finite facts actually usable; if `Hexact` or `homology_theory_spectrum` needs sorry, record as explicit debt.
- **Build gate**: `lake build InfoGeometry.Spectral.Homology` and `InfoGeometry.Spectral` exit 0.

### Phase D — Cofiber sequence finite readout (`Cohomology/CofiberSequence.lean`)
- `external_refs/Spectral/cohomology/cofiber_sequence.hlean` builds LES from cofiber sequences.
- **Implementation rule**: record `cofiber_sequence` as a 3-term pointed diagram `X →* Y →* cofiber` with connecting map. Prove the finite exactness triangle. Do not attempt full unstable cofiber-LES machinery if it requires sorry.
- **Build gate**: `lake build InfoGeometry.Spectral.Cohomology.CofiberSequence` exit 0.

### Phase E — Verification
- `rg -n "sorry|axiom|admit" lean/InfoGeometry/Spectral` → 0 matches
- `lake build InfoGeometry.Spectral` exit 0
- Update `lean/InfoGeometry/Spectral/All.lean` to import new files
- Document each ported file with the Lean 2 source filename for provenance

## 3. Order

1. `Colimit/SeqColim.lean`
2. `Spectrum/Basic.lean` expansion
3. `Homology/Basic.lean`
4. `Cohomology/CofiberSequence.lean`
5. Rebuild full `InfoGeometry.Spectral`

## 4. Non-Negotiable

- Every added file must build isolation-first, then in the full module.
- No sorry/axiom/admit. If a proof cannot close natively today, leave the lemma unproved with a docstring debt note.
- No mathlib version bump.
- If a new Lean 2 port step invalidates existing sorry-free surfaces, fix the regression before claiming completion.
