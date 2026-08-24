/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.Folding
import Atlas.Buildings.code.ChamberComplex.CoxeterComplex
import Mathlib.GroupTheory.Coxeter.Length

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace ChamberComplex

/-- Existence of a reversible folding across any adjacent wall in a Coxeter-labelled complex:
given a label $\varphi$ converting chamber adjacency to multiplication by a simple reflection in
$W$, for each adjacent pair $(C, D)$ there is a reversible folding $(f, g)$ with $C$ in
$f$'s fixed half and $D$ in $g$'s fixed half. -/
theorem coxeterReversibleFolding_exists
    (K : ChamberComplex V)
    (B_idx : Type)
    (M : CoxeterMatrix B_idx)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, K.toSimplicialComplex.IsMaximal C →
      ∀ D, K.toSimplicialComplex.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, K.toSimplicialComplex.IsMaximal C ∧ φ C = w)
    (hadj_fwd : ∀ C C', K.toSimplicialComplex.Adjacent C C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (hadj_bwd : ∀ C C', K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C') →
        K.toSimplicialComplex.Adjacent C C')
    (C D : Finset V)
    (hadj : K.toSimplicialComplex.Adjacent C D) :
    ∃ (rf : ReversibleFolding K),
      C ∈ rf.f.fixedChambers ∧ D ∈ rf.g.fixedChambers := by sorry

/-- Strong form of the Coxeter reversible folding: for any adjacent pair $(C, D)$, there is a
reversible folding $(f, g)$ with $f(C) = C$, $f(D) = C$, $g(D) = D$, $g(C) = D$. -/
theorem coxeterReversibleFolding
    (K : ChamberComplex V)
    (B_idx : Type)
    (M : CoxeterMatrix B_idx)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, K.toSimplicialComplex.IsMaximal C →
      ∀ D, K.toSimplicialComplex.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, K.toSimplicialComplex.IsMaximal C ∧ φ C = w)
    (hadj_fwd : ∀ C C', K.toSimplicialComplex.Adjacent C C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (hadj_bwd : ∀ C C', K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C') →
        K.toSimplicialComplex.Adjacent C C')
    (C D : Finset V)
    (hadj : K.toSimplicialComplex.Adjacent C D) :
    ∃ (rf : ReversibleFolding K),
      C.image rf.f.morph.toFun = C ∧ D.image rf.f.morph.toFun = C ∧
      D.image rf.g.morph.toFun = D ∧ C.image rf.g.morph.toFun = D := by

  obtain ⟨rf, hCfixed, hDfixed⟩ :=
    coxeterReversibleFolding_exists K B_idx M φ hinj hsurj hadj_fwd hadj_bwd C D hadj
  refine ⟨rf, ?_, ?_, ?_, ?_⟩

  · exact hCfixed.2

  ·
    have hDmoved_f : D ∈ rf.f.movedChambers := by
      rw [rf.complementary_moved]
      exact hDfixed

    have hDne : D.image rf.f.morph.toFun ≠ D := hDmoved_f.2

    exact rf.f.stutter_at_boundary C D hadj hCfixed hDne

  · exact hDfixed.2

  ·
    have hCmoved_g : C ∈ rf.g.movedChambers := by
      rw [← rf.complementary_fixed]
      exact hCfixed

    have hCne : C.image rf.g.morph.toFun ≠ C := hCmoved_g.2


    obtain ⟨hCmax, hDmax, hne, F, hFC, hFD⟩ := hadj
    have hadj_DC : K.toSimplicialComplex.Adjacent D C :=
      ⟨hDmax, hCmax, hne.symm, F, hFD, hFC⟩
    exact rf.g.stutter_at_boundary D C hadj_DC hDfixed hCne

/-- For a facet $F \subset C$, the simple generator $s_i$ characterizing the other chamber across
$F$ is uniquely determined and any chamber $D$ with $\varphi(D) = \varphi(C) s_i$ also has $F$ as a
facet. -/
theorem coxeterComplex_facet_generator
    (K : ChamberComplex V)
    (B_idx : Type)
    (M : CoxeterMatrix B_idx)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, K.toSimplicialComplex.IsMaximal C →
      ∀ D, K.toSimplicialComplex.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, K.toSimplicialComplex.IsMaximal C ∧ φ C = w)
    (hadj_fwd : ∀ C C', K.toSimplicialComplex.Adjacent C C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (hadj_bwd : ∀ C C', K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C') →
        K.toSimplicialComplex.Adjacent C C')
    (hfacet_shared : ∀ F C, K.toSimplicialComplex.IsFacet F C →
      K.toSimplicialComplex.IsMaximal C →
      ∃ D, D ≠ C ∧ K.toSimplicialComplex.IsMaximal D ∧
        K.toSimplicialComplex.IsFacet F D)
    (F C : Finset V)
    (hFC : K.toSimplicialComplex.IsFacet F C)
    (hC : K.toSimplicialComplex.IsMaximal C) :
    ∃ i : B_idx, ∀ D, K.toSimplicialComplex.IsMaximal D →
      φ D = φ C * M.toCoxeterSystem.simple i →
        K.toSimplicialComplex.IsFacet F D := by


  obtain ⟨D₀, hD₀_ne, hD₀_max, hFD₀⟩ := hfacet_shared F C hFC hC


  have hAdj : K.toSimplicialComplex.Adjacent C D₀ :=
    ⟨hC, hD₀_max, hD₀_ne.symm, F, hFC, hFD₀⟩

  have hCA := hadj_fwd C D₀ hAdj

  obtain ⟨_, i, hi⟩ := hCA

  exact ⟨i, fun D hD_max hφD => by

    have hφ_eq : φ D = φ D₀ := by rw [hφD, hi]

    have hD_eq : D = D₀ := hinj D hD_max D₀ hD₀_max hφ_eq

    rw [hD_eq]
    exact hFD₀⟩

end ChamberComplex
