-- Macaulay2 script for Madelung-Legendre trace verification
print "=== Macaulay2: Madelung-Legendre Trace Verification ==="

-- Define a 3x3 matrix K with trace 0
K = matrix{{1, 2, 3}, {4, 5, 6}, {7, 8, -6}}
tr_K = trace K
print "Trace of K = "
print tr_K

-- Verify trace of beta * K
beta = 5
u = beta * K
tr_u = trace u
print "Trace of 5 * K = "
print tr_u

if tr_u == beta * tr_K then (
  print "Linearity of trace: trace(beta * K) = beta * trace(K) holds!\n";
) else (
  error "Trace linearity failed!";
)

-- Check that if trace(K) = 0, then trace(beta * K) = 0
if tr_K == 0 then (
  if tr_u == 0 then (
    print "Divergence-free flow is preserved under scaling!\n";
    print "All M2 verifications passed!\n";
  ) else (
    error "Scaling preservation failed!";
  )
) else (
  error "Setup trace(K) must be 0!";
)
