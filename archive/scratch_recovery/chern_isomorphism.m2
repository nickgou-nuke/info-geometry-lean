-- Auto-generated Cyclic Cohomology and Chern Trace Engine
loadPackage "NCAlgebra";

-- Define the even differential forms ring
-- w_0 acts as the scalar trace, w_2 represents the curvature 2-form
R = QQ[w_0, w_2, SkewCommutative => true];

-- The Chern character element ch(E) = Tr(exp(F)) approximated to degree 2
-- ch_E = w_0 + w_2
chernForm = w_0 + w_2;

print "--- M2 CHERN TRACE MAP LOADED ---";
print ("Chern Character Polynomial: " | toString(chernForm));
exit 0;
