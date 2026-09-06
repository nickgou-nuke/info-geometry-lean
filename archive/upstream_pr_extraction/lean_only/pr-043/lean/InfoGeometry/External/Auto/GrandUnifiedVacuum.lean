def Pin55SpinorSpaceDim : Nat := 32

def MajoranaWeylPlusDim : Nat := 16
def MajoranaWeylMinusDim : Nat := 16

theorem pin55_decomposition : Pin55SpinorSpaceDim = MajoranaWeylPlusDim + MajoranaWeylMinusDim := by
  rfl
