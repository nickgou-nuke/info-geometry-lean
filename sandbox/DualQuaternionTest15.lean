import Mathlib
variable {S N : Type*} [Ring S] [AddCommGroup N] [Module S N] [Module Sᵐᵒᵖ N] [SMulCommClass S Sᵐᵒᵖ N]
#check (inferInstance : Monoid (TrivSqZeroExt S N))
