# Zorn braid colimit: mathematical dependency order

The proof dependency diagram is a partial order, not a physical causal claim:

```text
3701: existing zornPhi : B3 →* GL8 ─┐
                                  ├─ 3703: stage equivariance
3702: existing zornStageFunctor ───┘              │
                                                ▼
                              3704: categorical colimit action
                                                │
                                                ▼
                              3705: stage evaluation and uniqueness
```

The local representation and directed diagram are independent inputs. Their
compatibility, not a postulated `MacroscopicAction`, supplies the action through
Mathlib's `colim.map`. The owner `ZornColimitStageAction.lean` packages invertibility
using `Units.map`; `ZornColimitBraidAction.lean` proves unique existence using
`colimit.hom_ext`.

`ZornColimitBraidCovariance.lean` adds the missing generator-to-group step:

1. `stage_braid_equivariant`: all braid words commute with every prefix bond.
2. `conjugacy_of_generator_conjugacy`: equality of conjugated generator images
   implies equality on all of the existing presented group, including inverses.
3. `colimit_action_unique_of_generators`: checking the two generator images on
   stage injections determines the entire unit-valued colimit representation.
4. `colimit_braid_covariance`: generator conjugacy of finite representations
   transports to full-group conjugacy on the categorical colimit.
5. `colimit_braid_covariance_on_stage`: exact evaluation of that transport on
   finite-stage representatives.

This uses the existing complex `zornPhi` and its existing complex module colimit;
it does not relabel that carrier as a real construction. No new transition
system, colimit carrier, equivariance class, or assumed colimit action is added.
The results do not assert faithfulness of the braid representation, a knot
invariant, nuclear shape dynamics, or a holographic principle.

Validation is pending the shared build lane. The accompanying test module checks
arbitrary matrix conjugation, inverse braid evaluation, prefix equivariance, and
prints the axioms of the principal theorems.
