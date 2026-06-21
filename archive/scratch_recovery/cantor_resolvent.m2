-- Auto-generated Resolvent Harness. Total Nodes: 14
-- We mock JSON parsing in standard M2 by creating a basic list
eigenvalues = toList(1..14);
traceSum = 0.0;
for i from 0 to #eigenvalues - 1 do (
    traceSum = traceSum + (1.0 / (eigenvalues#i));
);
print ("Total Resolvent Trace Sum: " | toString(traceSum));
exit 0;