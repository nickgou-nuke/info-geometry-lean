import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs

open CliffordAlgebra

-- Probe what Mathlib provides for Cl(2) and complex equivalence
#check @CliffordAlgebra.evenSubalgebra
#check @CliffordAlgebra.equivExterior

-- Check if there's a Cl(0,2)≃ℂ or Cl(2,0)≃(matrix algebra) equivalence
#check @CliffordAlgebra.equivCl2