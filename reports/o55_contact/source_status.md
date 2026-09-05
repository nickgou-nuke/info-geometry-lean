# O(5,5) contact multigrading source status

Branch: `o55-contact-multigrading-formalism-v2`

The branch contains explicit proof scripts for the split quadratic carrier,
its native orthogonal Lie algebra, contact five-grading, block bigrading,
parity, Heisenberg radicals, exact five-term reconstruction, two-boundary
selection rules, five Witt pairs, Pin compatibility readouts, common CAR--CCR
representation, crosscap covariance, degree-zero structure and capstone.

No successful Lean kernel run has been recorded for the exact branch head in
the authoring environment.  The focused command is:

```bash
bash scripts/check_o55_contact_full_formalism.sh
```

The PR must remain draft until this command completes and the transitive axiom
audit reports no dependency beyond the permitted logical axioms.

The coordinate-generator lane count `1,12,19,12,1` is proved as a finite
label census with grade membership.  It is not yet a native basis/finrank
theorem for the homogeneous submodules.
