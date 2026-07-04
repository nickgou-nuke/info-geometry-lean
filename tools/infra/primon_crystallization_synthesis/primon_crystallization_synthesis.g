mobius30 := MoebiusMu(30);;
mobius12 := MoebiusMu(12);;
if mobius30 <> -1 then Error("Mobius squarefree parity failed"); fi;
if mobius12 <> 0 then Error("Repeated-prime sector not killed"); fi;
G := SymmetricGroup(4);;
if Size(G) <> 24 then Error("finite permutation sanity failed"); fi;
Print("GAP_PRIMON_CRYSTALLIZATION_SYNTHESIS_OK\n");
Print("mobius30=", mobius30, " mobius12=", mobius12, "\n");
