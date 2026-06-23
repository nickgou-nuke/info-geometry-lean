#!/usr/bin/env gap
#O55FiveGradeWeights.g
# GAP script to output the O(5,5) five-grade weight mapping as a record.

weights := rec(
    u5  :=  1,
    v5  := -1,
    u4  :=  1,
    v4  := -1,
    D5  :=  0,
    D4  :=  0,
    D   :=  0,
    J5  :=  0,
    J4  :=  0,
    J   :=  0
);

Print( String( weights ), "\n" );