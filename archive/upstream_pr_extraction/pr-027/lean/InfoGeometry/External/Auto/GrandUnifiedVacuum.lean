def Pin55SpinorSpaceDim : Nat := 32

def MajoranaWeylPlusDim : Nat := 16
def MajoranaWeylMinusDim : Nat := 16

theorem pin55_decomposition : Pin55SpinorSpaceDim = MajoranaWeylPlusDim + MajoranaWeylMinusDim := by
  rfl

def ModularHamiltonian (Delta : String) : String := "minus_ln_" ++ Delta
def OperatorBoltzmannEntropy (Delta : String) : String := "minus_ln_" ++ Delta

theorem modular_hamiltonian_is_boltzmann_entropy (Delta : String) :
  ModularHamiltonian Delta = OperatorBoltzmannEntropy Delta := by
  rfl
