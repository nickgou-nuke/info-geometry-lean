theorem symmetric_supertrace_vanishes (φ : State CuntzUHF) (A : CuntzUHF)
    (h_state_inv : ∀ (x : CuntzUHF), φ (witten_parity x) = - φ x) :
    supertrace witten_parity φ A = - φ A