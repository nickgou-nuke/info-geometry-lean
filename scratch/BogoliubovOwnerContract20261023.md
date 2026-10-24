# Ground-truth contract: scalar Bogoliubov transport

Carrier: arbitrary associative Ring A with Algebra R A, CommRing R; multiplication remains noncommutative. Native owner OperatorAlgebra/ThermalBogoliubovCAR.lean defines thermalAnnihilator a d u v = u • a + v • d and thermalAnticommutator x y = x*y+y*x.

Existing proved owner statements: thermalAnticommutator_expand is the four-term bilinear expansion over ℂ; thermal_bogoliubov_car_preserved gives the normalized same-mode bracket under u²+v²=1. Existing nilpotent_ann/cre statements assert vanishing self-anticommutator, not square-zero over characteristic two. Algebra/CommutingNilpotentSum.add_sq_eq_zero_iff_cross_terms_cancel gives unweighted square-zero addition.

Small source-confirmed delta: generalize unused ℂ restriction to arbitrary commutative R; prove actual square of thermalAnnihilator from primitive a*a=0, d*d=0, a*d+d*a=0 without cancellation of 2. Preserve existing declaration names and complex instantiations. Consumers include Optics/OperatorLiftCarrier, OperatorAlgebra/InnerConjugation, OperatorMobiusAction, Canonical/ChiralModularFlowColimitBridge and OperatorThermalBogoliubovZ2Bridge.

Not established: full Spin/Pin representation/group classification, star automorphism for hyperbolic mixing, or full two-mode CAR solely from the same-mode bracket. Generated user proof is intake, not kernel evidence. Parent edits owner; independent AA and sequential native kernel QA required.

Independent AA found Algebra/ChiralCARTransport.linear_mix_square already proves the stronger arbitrary-scalar weighted square identity. Parent removed the proposed duplicate thermalAnnihilator_sq_zero rather than adding a forwarding wrapper. Final delta is the scalar generalization in the existing Thermal owner and correction of globally central coefficient prose; square-zero uses the established ChiralCARTransport owner.
