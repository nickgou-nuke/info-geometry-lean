 Yes. The best division of labor is:                                                                                                                                                          
                                                                                                                                                                                              
 - SageMath: exact Zorn/split-octonion multiplication, derivation matrices, linear systems, rank, bases, Lie brackets.                                                                        
 - GAP: finite automorphism groups, permutation representations, (G_2(2)), stabilizers.                                                                                                       
 - Macaulay2: polynomial ideals and Gröbner/elimination calculations.                                                                                                                         
 - SymPy: exploratory symbolic calculations and sign checking.                                                                                                                                
 - Clifford/GAlgebra: Clifford products, pseudoscalars, exterior/Grassmann calculations.                                                                                                      
 - D-modules: only differential-algebra portions.                                                                                                                                             
 - Coq/Isabelle: independent formal verification if desired, but not substitutes for Lean’s owner proofs.                                                                                     
                                                                                                                                                                                              
 The repository already has relevant Sage infrastructure, including:                                                                                                                          
                                                                                                                                                                                              
 ```text                                                                                                                                                                                      
   tools/sage/zorn_split_octonion_invariants.sage.py                                                                                                                                          
   tools/sage/verify_aut_g2.sage                                                                                                                                                              
   tools/sage/zorn_complex_bridge.sage                                                                                                                                                        
   tools/sympy/zorn_g2_su3_formalization.sage                                                                                                                                                 
 ```                                                                                                                                                                                          
                                                                                                                                                                                              
 Correct pipeline:                                                                                                                                                                            
                                                                                                                                                                                              
 1. Compute candidates externally over exact rings.                                                                                                                                           
 2. Export coefficients, matrices, ranks, and identities.                                                                                                                                     
 3. Reconstruct the definitions in Lean.                                                                                                                                                      
 4. Prove the exported identities with ring, norm_num, fin_cases, ext, and native Mathlib.                                                                                                    
 5. Treat Sage/GAP output as discovery evidence only—not as proof authority.                                                                                                                  
                                                                                                                                                                                              
 Lean remains the final mathematical authority; coordinate calculators are appropriate for finding and organizing the finite proofs.                                                          
