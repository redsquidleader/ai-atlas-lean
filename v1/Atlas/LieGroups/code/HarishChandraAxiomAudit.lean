/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.HarishChandraIsomorphism


noncomputable section AuditChecks

variable {R : Type*} [CommRing R]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

example := @uea_algHom_separates

example := @pbw_hc_eval_kernel_vanishing

example := @verma_embedding_scalar_invariance

example := @filtered_graded_principle_for_hc

example := @HarishChandraIso

example := @evalWeight_separates

end AuditChecks
