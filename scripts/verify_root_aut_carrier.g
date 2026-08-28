# Reproducible GAP certificate for the concrete root packet.
# The source generator packet remains the authoritative CAS input.

Read("tools/gap/RootAutCarrier.g");;
Read("scripts/derive_root_packet_pc_collector.g");;

carrier := InfoGeometryRootAutCarrier.Build(pc, roots);;
if carrier.pcSize <> 64 then Error("ROOT_AUT_PC_SIZE_FAIL"); fi;;
if carrier.rootAutSize <> 168 then Error("ROOT_AUT_SUBGROUP_SIZE_FAIL"); fi;;
if carrier.carrierSize <> 12096 then Error("ROOT_AUT_CARRIER_SIZE_FAIL"); fi;;
if ForAll(carrier.rootAutInPC, x -> x) then
  Error("ROOT_AUT_ALIGNMENT_UNEXPECTEDLY_PASSES");
fi;;

Print("ROOT_AUT_PC_SIZE=", carrier.pcSize, "\n");
Print("ROOT_AUT_SUBGROUP_SIZE=", carrier.rootAutSize, "\n");
Print("ROOT_AUT_CARRIER_SIZE=", carrier.carrierSize, "\n");
Print("ROOT_AUT_MEMBERSHIP_IN_PC=", ForAll(carrier.rootAutInPC, x -> x), "\n");
Print("ROOT_AUT_REAL_PACKET_CERTIFICATE=PASS\n");
QUIT;
