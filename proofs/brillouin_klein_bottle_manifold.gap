Tx := [[0,1],[1,0]];
Ty := [[1,0],[0,-1]];
I2 := [[1,0],[0,1]];
minusI := -I2;
Txy := Tx*Ty;
if Tx*Tx <> I2 then Error("Tx square failed"); fi;
if Ty*Ty <> I2 then Error("Ty square failed"); fi;
if Tx*Ty <> -(Ty*Tx) then Error("anticommutation failed"); fi;
if Tx*Ty <> minusI*(Ty*Tx) then Error("central sign commutation failed"); fi;
if Txy*Txy <> minusI then Error("mixed channel square failed"); fi;
Glide := p -> [p[1]+1, -p[2]];
GlideInv := p -> [p[1]-1, -p[2]];
YLoop := p -> [p[1], p[2]+2];
YLoopInv := p -> [p[1], p[2]-2];
for x in [-3..3] do
  for y in [-3..3] do
    p := [x,y];
    if Glide(GlideInv(p)) <> p then Error("glide right inverse failed"); fi;
    if GlideInv(Glide(p)) <> p then Error("glide left inverse failed"); fi;
    if Glide(YLoop(GlideInv(p))) <> YLoopInv(p) then Error("Klein conjugacy failed"); fi;
    if Glide(YLoop(GlideInv(YLoop(p)))) <> p then Error("boundary word failed"); fi;
  od;
od;
Print("brillouin Klein bottle manifold GAP certificate: ok\n");
