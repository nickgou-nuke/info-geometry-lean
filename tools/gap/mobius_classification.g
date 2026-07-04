G := SL(2, 11);
classes := ConjugacyClasses(G);
parabolic := 0;
circular := 0;

for c in classes do
    rep := Representative(c);
    tr := TraceMat(rep);
    tr2 := tr^2;
    val := Int(tr2);
    if val = 4 then
        parabolic := parabolic + 1;
    elif val = 0 then
        circular := circular + 1;
    fi;
od;

Print("Parabolic classes (tr^2 = 4): ", parabolic, "\n");
Print("Circular classes (tr^2 = 0): ", circular, "\n");
QUIT;
