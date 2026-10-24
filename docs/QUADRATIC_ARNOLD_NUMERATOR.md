# Quadratic Arnold numerator classification: accepted

The negative owner `External/Auto/NonIsoConf3LogWedgeObstruction.lean`
evaluates one coefficient to 52. The new `Geometry/QuadraticArnoldNumerator`
uses its existing integer `Vec4`, quadric, endpoint gradients and wedge
coefficient. It defines every ambient coefficient on `Fin 3 × Fin 4`,
including same-point blocks, and proves exact agreement with that evaluation.

The checked positive direction is: if every numerator coefficient vanishes
and `q4 (sub Y Z) ≠ 0`, every displacement minor vanishes. The `xx` block
is `-4 * q4(Y-Z) * sig i * sig j` times the corresponding minor; integer
cancellation supplies necessity. The new `QuadraticArnoldVanishing` owner supplies the converse and exact iff.

The converse is now kernel-checked without any nonisotropy assumption.
Its division-free proof uses the polar form: vanishing minors imply
`polar(u,v)*u_i=q(u)*v_i` and `polar(u,v)*v_i=q(v)*u_i`; the six coordinate
blocks vanish by these identities and `q(u+v)=q(u)+q(v)+2polar(u,v)`.
Skewness handles the three reversed blocks. Necessity and sufficiency combine
into `numerator_vanishes_iff` under `q4 (sub Y Z) ≠ 0`.
No imposed Orlik–Solomon quotient relation is used. All three denominators
would need to be nonzero to interpret this polynomial as logarithmic forms.

Parent locked session 54949 passed (3,097 jobs, exit 0), log
`/tmp/quadratic-arnold-numerator.log`. Two style warnings were subsequently
repaired. The companion audit requests six axiom reports and includes three
examples preserving nonzero numerator, nonisotropy, and a nonzero minor.
Independent kernel QA of the current owner and audit is pending.

Independent necessity QA session 97998 passed (3,098 jobs, exit 0), six axiom
reports and three examples, zero own warnings and traps, log
`/tmp/quadratic-arnold-numerator-qa.log`.

Full-classification parent session 54056 passed (3,098 jobs, exit 0), with
zero own warnings, log `/tmp/quadratic-arnold-vanishing-v3.log`. The new audit
requests ten axiom reports and checks a collinear time-axis triple with
squared separations 1,1,4, as well as the original nonzero coefficient.
Independent full-classification semantic review passed. Kernel QA session
50995 passed (3,099 jobs, exit 0), with ten standard-three-axiom reports,
three examples, zero own warnings and zero traps. Evidence:
`/tmp/quadratic-arnold-vanishing-qa.log`. Acceptance covers the integer
polynomial numerator classification, not cohomology or logarithmic forms.
