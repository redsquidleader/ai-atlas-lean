/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Atlas.Buildings.code.GeometricAlgebra.WittTheorem

set_option maxHeartbeats 800000

namespace Garrett

variable {k : Type*} [Field k] [NeZero (2 : k)]
variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

end Garrett
