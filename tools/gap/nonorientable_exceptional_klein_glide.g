# GAP witness for the Klein-glide braid bookkeeping in arXiv:2504.11983v1.
#
# The non-orientable Klein relation sends a braid/charge a to a^-1 under
# conjugation by a glide g:
#     g a g^-1 = a^-1
# equivalently
#     g a g^-1 a = 1.
#
# This is a finite group-theoretic smoke test only.

RequireTrue := function(name, cond)
  if not cond then
    Error(Concatenation("[FAIL] ", name));
  fi;
  Print("[OK] ", name, "\n");
end;

# DihedralGroup(10) has a rotation r of order 5 and a reflection g with
# g r g^-1 = r^-1.  This models orientation reversal without collapsing r^2=1.
D := DihedralGroup(IsPermGroup, 10);;
cc := ConjugacyClasses(D);;
rotCandidates := Filtered(Elements(D), x -> Order(x) = 5);;
glideCandidates := Filtered(Elements(D), x -> Order(x) = 2);;

a := rotCandidates[1];;
g := First(glideCandidates, h -> h * a * h^-1 = a^-1);;

RequireTrue("found nontrivial braid/charge a of order 5", Order(a) = 5);
RequireTrue("found orientation-reversing glide", g <> fail and Order(g) = 2);
RequireTrue("Klein glide sends a to a^-1", g * a * g^-1 = a^-1);
RequireTrue("Klein boundary word g a g^-1 a is trivial", g * a * g^-1 * a = One(D));
RequireTrue("clockwise and counterclockwise charges are inequivalent", a <> a^-1);
RequireTrue("not an S2/Coxeter collapse: a^2 != 1", a^2 <> One(D));

Print("KLEIN_GLIDE_EP_GAP_OK\n");
