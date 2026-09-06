import InfoGeometry.Algebra.Zorn.G2CASNativePointEnumeration
import InfoGeometry.Algebra.Zorn.G2TwoExplicitGenerators
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation

/-!
# CAS-certified action on the native 63-point orbit

The seven maps below are the column-action permutations exported by GAP for
the six ordered PC generators followed by swap01Aut. The source orbit is
casPoint; the native theorem below identifies each exported transition with
the corresponding octImAction.
-/

namespace InfoGeometry.Algebra.Zorn.G2CASNativePointAction

open InfoGeometry.Algebra.Zorn.G2CASNativePointEnumeration
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def casPointGenerator : Fin 7 → SplitOctF2Aut
  | 0 => pcGenerator 0
  | 1 => pcGenerator 1
  | 2 => pcGenerator 2
  | 3 => pcGenerator 3
  | 4 => pcGenerator 4
  | 5 => pcGenerator 5
  | 6 => swap01Aut

def casPointPermRaw : Fin 7 → Fin 63 → Fin 63
  | 0 => fun i => match i with
    | 0 => 0
    | 1 => 3
    | 2 => 8
    | 3 => 1
    | 4 => 15
    | 5 => 14
    | 6 => 6
    | 7 => 7
    | 8 => 2
    | 9 => 38
    | 10 => 42
    | 11 => 33
    | 12 => 48
    | 13 => 35
    | 14 => 5
    | 15 => 4
    | 16 => 20
    | 17 => 50
    | 18 => 25
    | 19 => 32
    | 20 => 16
    | 21 => 21
    | 22 => 49
    | 23 => 23
    | 24 => 45
    | 25 => 18
    | 26 => 51
    | 27 => 27
    | 28 => 60
    | 29 => 37
    | 30 => 30
    | 31 => 61
    | 32 => 19
    | 33 => 11
    | 34 => 46
    | 35 => 13
    | 36 => 52
    | 37 => 29
    | 38 => 9
    | 39 => 41
    | 40 => 44
    | 41 => 39
    | 42 => 10
    | 43 => 59
    | 44 => 40
    | 45 => 24
    | 46 => 34
    | 47 => 58
    | 48 => 12
    | 49 => 22
    | 50 => 17
    | 51 => 26
    | 52 => 36
    | 53 => 62
    | 54 => 57
    | 55 => 56
    | 56 => 55
    | 57 => 54
    | 58 => 47
    | 59 => 43
    | 60 => 28
    | 61 => 31
    | 62 => 53
    | _ => 0
  | 1 => fun i => match i with
    | 0 => 0
    | 1 => 4
    | 2 => 12
    | 3 => 14
    | 4 => 1
    | 5 => 20
    | 6 => 55
    | 7 => 29
    | 8 => 53
    | 9 => 2
    | 10 => 36
    | 11 => 40
    | 12 => 13
    | 13 => 9
    | 14 => 3
    | 15 => 16
    | 16 => 15
    | 17 => 54
    | 18 => 26
    | 19 => 39
    | 20 => 5
    | 21 => 24
    | 22 => 48
    | 23 => 25
    | 24 => 27
    | 25 => 6
    | 26 => 56
    | 27 => 57
    | 28 => 28
    | 29 => 7
    | 30 => 37
    | 31 => 8
    | 32 => 44
    | 33 => 52
    | 34 => 32
    | 35 => 31
    | 36 => 19
    | 37 => 30
    | 38 => 22
    | 39 => 10
    | 40 => 47
    | 41 => 33
    | 42 => 34
    | 43 => 62
    | 44 => 42
    | 45 => 17
    | 46 => 11
    | 47 => 46
    | 48 => 59
    | 49 => 61
    | 50 => 45
    | 51 => 18
    | 52 => 58
    | 53 => 35
    | 54 => 50
    | 55 => 23
    | 56 => 51
    | 57 => 21
    | 58 => 41
    | 59 => 38
    | 60 => 60
    | 61 => 43
    | 62 => 49
    | _ => 0
  | 2 => fun i => match i with
    | 0 => 0
    | 1 => 4
    | 2 => 19
    | 3 => 15
    | 4 => 1
    | 5 => 20
    | 6 => 51
    | 7 => 30
    | 8 => 42
    | 9 => 36
    | 10 => 2
    | 11 => 49
    | 12 => 39
    | 13 => 10
    | 14 => 16
    | 15 => 3
    | 16 => 14
    | 17 => 27
    | 18 => 25
    | 19 => 13
    | 20 => 5
    | 21 => 17
    | 22 => 33
    | 23 => 26
    | 24 => 54
    | 25 => 56
    | 26 => 6
    | 27 => 50
    | 28 => 28
    | 29 => 37
    | 30 => 7
    | 31 => 44
    | 32 => 8
    | 33 => 59
    | 34 => 31
    | 35 => 32
    | 36 => 12
    | 37 => 29
    | 38 => 41
    | 39 => 9
    | 40 => 61
    | 41 => 48
    | 42 => 35
    | 43 => 11
    | 44 => 53
    | 45 => 24
    | 46 => 62
    | 47 => 43
    | 48 => 52
    | 49 => 47
    | 50 => 21
    | 51 => 23
    | 52 => 38
    | 53 => 34
    | 54 => 57
    | 55 => 18
    | 56 => 55
    | 57 => 45
    | 58 => 22
    | 59 => 58
    | 60 => 60
    | 61 => 46
    | 62 => 40
    | _ => 0
  | 3 => fun i => match i with
    | 0 => 0
    | 1 => 5
    | 2 => 11
    | 3 => 14
    | 4 => 20
    | 5 => 1
    | 6 => 6
    | 7 => 7
    | 8 => 33
    | 9 => 40
    | 10 => 43
    | 11 => 2
    | 12 => 46
    | 13 => 47
    | 14 => 3
    | 15 => 16
    | 16 => 15
    | 17 => 17
    | 18 => 56
    | 19 => 49
    | 20 => 4
    | 21 => 21
    | 22 => 32
    | 23 => 23
    | 24 => 57
    | 25 => 55
    | 26 => 26
    | 27 => 27
    | 28 => 28
    | 29 => 29
    | 30 => 30
    | 31 => 52
    | 32 => 22
    | 33 => 8
    | 34 => 48
    | 35 => 58
    | 36 => 61
    | 37 => 37
    | 38 => 44
    | 39 => 62
    | 40 => 9
    | 41 => 53
    | 42 => 59
    | 43 => 10
    | 44 => 38
    | 45 => 54
    | 46 => 12
    | 47 => 13
    | 48 => 34
    | 49 => 19
    | 50 => 50
    | 51 => 51
    | 52 => 31
    | 53 => 41
    | 54 => 45
    | 55 => 25
    | 56 => 18
    | 57 => 24
    | 58 => 35
    | 59 => 42
    | 60 => 60
    | 61 => 36
    | 62 => 39
    | _ => 0
  | 4 => fun i => match i with
    | 0 => 0
    | 1 => 4
    | 2 => 12
    | 3 => 16
    | 4 => 1
    | 5 => 20
    | 6 => 27
    | 7 => 7
    | 8 => 34
    | 9 => 13
    | 10 => 39
    | 11 => 46
    | 12 => 2
    | 13 => 9
    | 14 => 15
    | 15 => 14
    | 16 => 3
    | 17 => 51
    | 18 => 45
    | 19 => 36
    | 20 => 5
    | 21 => 23
    | 22 => 52
    | 23 => 21
    | 24 => 55
    | 25 => 57
    | 26 => 50
    | 27 => 6
    | 28 => 28
    | 29 => 29
    | 30 => 30
    | 31 => 32
    | 32 => 31
    | 33 => 48
    | 34 => 8
    | 35 => 44
    | 36 => 19
    | 37 => 37
    | 38 => 58
    | 39 => 10
    | 40 => 47
    | 41 => 59
    | 42 => 53
    | 43 => 62
    | 44 => 35
    | 45 => 18
    | 46 => 11
    | 47 => 40
    | 48 => 33
    | 49 => 61
    | 50 => 26
    | 51 => 17
    | 52 => 22
    | 53 => 42
    | 54 => 56
    | 55 => 24
    | 56 => 54
    | 57 => 25
    | 58 => 38
    | 59 => 41
    | 60 => 60
    | 61 => 49
    | 62 => 43
    | _ => 0
  | 5 => fun i => match i with
    | 0 => 0
    | 1 => 1
    | 2 => 13
    | 3 => 3
    | 4 => 4
    | 5 => 5
    | 6 => 23
    | 7 => 7
    | 8 => 35
    | 9 => 12
    | 10 => 19
    | 11 => 47
    | 12 => 9
    | 13 => 2
    | 14 => 14
    | 15 => 15
    | 16 => 16
    | 17 => 50
    | 18 => 56
    | 19 => 10
    | 20 => 20
    | 21 => 27
    | 22 => 59
    | 23 => 6
    | 24 => 57
    | 25 => 55
    | 26 => 51
    | 27 => 21
    | 28 => 28
    | 29 => 29
    | 30 => 30
    | 31 => 53
    | 32 => 42
    | 33 => 58
    | 34 => 44
    | 35 => 8
    | 36 => 39
    | 37 => 37
    | 38 => 48
    | 39 => 36
    | 40 => 46
    | 41 => 52
    | 42 => 32
    | 43 => 49
    | 44 => 34
    | 45 => 54
    | 46 => 40
    | 47 => 11
    | 48 => 38
    | 49 => 43
    | 50 => 17
    | 51 => 26
    | 52 => 41
    | 53 => 31
    | 54 => 45
    | 55 => 25
    | 56 => 18
    | 57 => 24
    | 58 => 33
    | 59 => 22
    | 60 => 60
    | 61 => 62
    | 62 => 61
    | _ => 0
  | 6 => fun i => match i with
    | 0 => 0
    | 1 => 6
    | 2 => 2
    | 3 => 17
    | 4 => 21
    | 5 => 23
    | 6 => 1
    | 7 => 28
    | 8 => 36
    | 9 => 9
    | 10 => 44
    | 11 => 13
    | 12 => 40
    | 13 => 11
    | 14 => 50
    | 15 => 51
    | 16 => 26
    | 17 => 3
    | 18 => 54
    | 19 => 38
    | 20 => 27
    | 21 => 4
    | 22 => 22
    | 23 => 5
    | 24 => 24
    | 25 => 25
    | 26 => 16
    | 27 => 20
    | 28 => 7
    | 29 => 29
    | 30 => 60
    | 31 => 31
    | 32 => 59
    | 33 => 39
    | 34 => 43
    | 35 => 61
    | 36 => 8
    | 37 => 37
    | 38 => 19
    | 39 => 33
    | 40 => 12
    | 41 => 41
    | 42 => 42
    | 43 => 34
    | 44 => 10
    | 45 => 56
    | 46 => 46
    | 47 => 47
    | 48 => 49
    | 49 => 48
    | 50 => 14
    | 51 => 15
    | 52 => 53
    | 53 => 52
    | 54 => 18
    | 55 => 55
    | 56 => 45
    | 57 => 57
    | 58 => 62
    | 59 => 32
    | 60 => 30
    | 61 => 35
    | 62 => 58
    | _ => 0
  | _ => fun _ => 0
noncomputable def casPointPerm (k : Fin 7) : Equiv.Perm (Fin 63) :=
  Equiv.ofBijective (casPointPermRaw k) (by
    fin_cases k <;> native_decide)

theorem casPointPerm_raw_bijective (k : Fin 7) :
    Function.Bijective (casPointPermRaw k) := by
  fin_cases k <;> native_decide

theorem casPoint_pc_action (k : Fin 6) (i : Fin 63) :
    casPoint (casPointPermRaw ⟨k, by omega⟩ i) =
      octImAction (pcGenerator k) (casPoint i) := by
  fin_cases k <;> fin_cases i <;> native_decide

theorem casPointEnum_pc_intertwines (k : Fin 6) (i : Fin 63) :
    casPointEnum (casPointPerm ⟨k, by omega⟩ i) =
      octImPointPerm (pcGenerator k) (casPointEnum i) := by
  apply Subtype.ext
  exact casPoint_pc_action k i

theorem casPoint_swap_action (i : Fin 63) :
    casPoint (casPointPermRaw 6 i) =
      octImAction swap01Aut (casPoint i) := by
  fin_cases i <;> decide

theorem casPointEnum_swap_intertwines (i : Fin 63) :
    casPointEnum (casPointPerm 6 i) =
      octImPointPerm swap01Aut (casPointEnum i) := by
  apply Subtype.ext
  exact casPoint_swap_action i

def correctedTPointPermRaw : Fin 63 → Fin 63 := fun i => match i with
  | 0 => 28 | 1 => 7 | 2 => 6 | 3 => 16 | 4 => 37 | 5 => 29
  | 6 => 2 | 7 => 1 | 8 => 22 | 9 => 56 | 10 => 45 | 11 => 24
  | 12 => 18 | 13 => 23 | 14 => 14 | 15 => 15 | 16 => 3 | 17 => 40
  | 18 => 12 | 19 => 54 | 20 => 30 | 21 => 36 | 22 => 8 | 23 => 13
  | 24 => 11 | 25 => 62 | 26 => 49 | 27 => 39 | 28 => 0 | 29 => 5
  | 30 => 20 | 31 => 31 | 32 => 42 | 33 => 33 | 34 => 52 | 35 => 59
  | 36 => 21 | 37 => 4 | 38 => 48 | 39 => 27 | 40 => 17 | 41 => 44
  | 42 => 32 | 43 => 51 | 44 => 41 | 45 => 10 | 46 => 50 | 47 => 57
  | 48 => 38 | 49 => 26 | 50 => 46 | 51 => 43 | 52 => 34 | 53 => 53
  | 54 => 19 | 55 => 61 | 56 => 9 | 57 => 47 | 58 => 58 | 59 => 35
  | 60 => 60 | 61 => 55 | 62 => 25 | _ => 0

noncomputable def correctedTPointPerm : Equiv.Perm (Fin 63) :=
  Equiv.ofBijective correctedTPointPermRaw (by native_decide)

theorem correctedTPointPerm_intertwines (i : Fin 63) :
    casPoint (correctedTPointPermRaw i) =
      octImAction correctedT (casPoint i) := by
  fin_cases i <;> decide

theorem casPointEnum_correctedT_intertwines (i : Fin 63) :
    casPointEnum (correctedTPointPerm i) =
      octImPointPerm correctedT (casPointEnum i) := by
  apply Subtype.ext
  exact correctedTPointPerm_intertwines i

end InfoGeometry.Algebra.Zorn.G2CASNativePointAction
