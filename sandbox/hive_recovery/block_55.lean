structure ResidueBCFWInterface where
  residues : ThreePoleResidueDatum
  bcfwRecursion : Prop
  residueBalance_to_bcfw :
    (∑ i : Fin 3, residues.residue i) = 0 → bcfwRecursion