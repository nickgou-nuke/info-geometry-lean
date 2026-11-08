/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.HadjiivanovRankTwoBraidFrame

namespace InfoGeometry.Projective.HadjiivanovRankTwoBraidFrameAudit

open InfoGeometry.Projective.HadjiivanovRankTwoBraidFrame

#check @cellNilpotent_sq
#check @rankTwoBraidFrame_representation_factors_through_S3
#check @rankTwoBraidFrame_representation_trivial_on_permutation_kernel
#check @rankTwo_logarithmicConnection_braid

#print axioms cellNilpotent_sq
#print axioms rankTwoBraidFrame_representation_factors_through_S3
#print axioms rankTwoBraidFrame_representation_trivial_on_permutation_kernel
#print axioms rankTwo_logarithmicConnection_braid

end InfoGeometry.Projective.HadjiivanovRankTwoBraidFrameAudit
