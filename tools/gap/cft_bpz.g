Print("Verifying BPZ central charge identity...\n");
b := X( Rationals, "b" );
expr1 := b^2 * (1 + 6 * (b + b^-1)^2);
expr2 := 6*b^4 + 13*b^2 + 6;

if expr1 = expr2 then
    Print("Identity verified successfully.\n");
    FORCE_QUIT_GAP(0);
else
    Print("Identity verification failed!\n");
    Print("LHS: ", expr1, "\n");
    Print("RHS: ", expr2, "\n");
    FORCE_QUIT_GAP(1);
fi;
