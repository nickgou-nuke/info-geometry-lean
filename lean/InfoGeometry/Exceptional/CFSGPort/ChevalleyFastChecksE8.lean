/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyFastChecksE8Part0
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyFastChecksE8Part1
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyFastChecksE8Part2
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyFastChecksE8Part3
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyFastChecksE8Part4
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyFastChecksE8Part5

public section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

theorem conjRange_E8 : conjRange .E8 0 240 = true := by
  have h40 : conjRange .E8 0 40 := conjRange_E8_part0
  have h80 : conjRange .E8 0 80 :=
    conjRange_trans (by omega) (by omega) h40 conjRange_E8_part1
  have h120 : conjRange .E8 0 120 :=
    conjRange_trans (by omega) (by omega) h80 conjRange_E8_part2
  have h160 : conjRange .E8 0 160 :=
    conjRange_trans (by omega) (by omega) h120 conjRange_E8_part3
  have h200 : conjRange .E8 0 200 :=
    conjRange_trans (by omega) (by omega) h160 conjRange_E8_part4
  exact conjRange_trans (by omega) (by omega) h200 conjRange_E8_part5

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps
