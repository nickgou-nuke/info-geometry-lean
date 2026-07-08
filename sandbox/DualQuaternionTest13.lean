import Mathlib
import InfoGeometry.Capstone.BenamouBrenierBridge

noncomputable section

open InfoGeometry.Capstone.UHFHookup
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Capstone.BenamouBrenierBridge
open TrivSqZeroExt Finset

-- Test the UHF Hookup
#check uhf_duhamel_naturality

-- Demonstrate the naturality commutes on a concrete term
theorem uhf_hookup_test (n : ℕ) (A B : DiagAlg n) (k : ℕ) :
    uhfTrivSqZeroExtEmbed n (discreteDuhamelSum A B k) =
    discreteDuhamelSum (diagEmbedSucc n A) (diagEmbedSucc n B) k := by
  exact uhf_duhamel_naturality n A B k

end
