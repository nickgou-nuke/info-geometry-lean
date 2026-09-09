Read("tools/gap/RootAutCarrier.g");

F := GF(2);;
pc := [ [ [One(F), One(F)], [Zero(F), One(F)] ],
         [ [One(F), Zero(F)], [One(F), One(F)] ] ];;
roots := [ [ [Zero(F), One(F)], [One(F), Zero(F)] ] ];;
carrier := InfoGeometryRootAutCarrier.Build(pc, roots);;
report := InfoGeometryRootAutCarrier.Membership(carrier,
  [ One(pc[1]), roots[1] ]);;

if carrier.pcSize <> 6 then
  Error("unexpected PC closure size");
fi;
if carrier.rootAutSize <> 2 then
  Error("unexpected rootAut closure size");
fi;
if carrier.carrierSize <> 6 then
  Error("unexpected combined closure size");
fi;
if carrier.rootAutInPC <> [ true ] then
  Error("unexpected rootAut membership result");
fi;
if not report[1].inCarrier or not report[2].inCarrier then
  Error("membership API failed on carrier elements");
fi;
if report[1].carrierWord = fail or report[2].carrierWord = fail then
  Error("membership API failed to return canonical words");
fi;

InfoGeometryRootAutCarrier.PrintCertificate(carrier);
Print("ROOT_AUT_CARRIER_SMOKE=PASS\n");
QUIT;
