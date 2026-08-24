/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.StrongIsometryExt

set_option maxHeartbeats 400000

variable {V : Type*} [DecidableEq V]

/-- One-step extension of a strong isometry: given a partial strong isometry
$f : Y \to A$ into an apartment, a chamber $C' \in A$ adjacent to $f(Y)$ but
not in $f(Y)$ admits a global extension $g$ defined on $f(Y) \cup \{C'\}$ that
agrees with $f^{-1}$ on $f(Y)$. This is the inductive step of the strong
isometry extension lemma (Section 15.5). -/
theorem lemma_one_step_extension
    {b : Building V}
    (δW : Building.WValuedDist b)
    {A : SimplicialComplex V}
    (hA : A ∈ b.apartmentSystem.apartments)
    {Y : Set (Finset V)}
    {f : Finset V → Finset V}
    (hf_strong : IsStrongIsometry δW Y (f '' Y) f)
    (hf_img_in_A : ∀ C ∈ Y, f C ∈ A.faces)
    (hY_chambers : ∀ C ∈ Y, b.toChamberComplex.toSimplicialComplex.IsMaximal C)
    {C' : Finset V}
    (hC'_in_A : C' ∈ A.faces)
    (hC'_maximal : A.IsMaximal C')
    (hC'_not_in_fY : C' ∉ f '' Y)
    (hC'_adj : ∃ D ∈ f '' Y, A.Adjacent C' D) :
    ∃ (g : Finset V → Finset V),
      IsStrongIsometry δW
        (f '' Y ∪ {C'})
        (g '' (f '' Y ∪ {C'}))
        g ∧
      (∀ x ∈ f '' Y, ∃ y ∈ Y, f y = x ∧ g x = y) :=
  strong_isometry_one_step_extension δW hA hf_strong hf_img_in_A hY_chambers
    hC'_in_A hC'_maximal hC'_not_in_fY hC'_adj
