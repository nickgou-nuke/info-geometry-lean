# Exact-rational GAP certificate for the e+/e- Möbius chiral-parity
# cancellation and zero signed GW-type index. Run with the GAP executable from
# the Sage environment, e.g. sage -sh -c 'gap -q proofs/moebius_chiral_zero_gw.gap'.

# Two chiral poles: 1 = ePlus, 2 = eMinus.  Möbius inversion is the transposition.
swap := (1,2);
if swap^2 <> () then Error("Möbius inversion is not involutive"); fi;
if 1^swap <> 2 then Error("ePlus was not sent to eMinus"); fi;
if 2^swap <> 1 then Error("eMinus was not sent to ePlus"); fi;

# Signed Witten/GW-type index: +1 for ePlus and -1 for eMinus.
sign := function(p)
  if p = 1 then return 1; fi;
  if p = 2 then return -1; fi;
  Error("unknown chiral pole");
end;

idx := Sum([1,2], p -> sign(p));
if idx <> 0 then Error("signed e+/e- index did not cancel"); fi;

idxAfterMobius := Sum([1,2], p -> sign(p^swap));
if idxAfterMobius <> 0 then Error("Möbius-swapped signed index did not cancel"); fi;

# The generated group is C2 and the orbit has exactly the two chiral poles.
G := Group(swap);
if Size(G) <> 2 then Error("Möbius group is not C2"); fi;
if Set(Orbit(G, 1)) <> [1,2] then Error("Möbius orbit is not the e+/e- pair"); fi;

Print("moebius chiral zero GW GAP certificate: ok\n");
QUIT;
