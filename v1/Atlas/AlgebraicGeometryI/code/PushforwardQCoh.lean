/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Lemma24

/-- Lemma 24 (local case): on any affine open `U ⊆ Y`, the restriction of the
pushforward `f_*F` of a quasicoherent sheaf `F` on `X` is quasicoherent. -/
theorem pushforward_over_affineOpen_isQuasicoherent
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) [F.IsQuasicoherent]
    (U : Y.affineOpens) :
    (((Scheme.Modules.pushforward f).obj F).over (U : Y.Opens)).IsQuasicoherent := by
  sorry

/-- The collection of affine opens of `Y` covers the whole space in the Grothendieck
topology of opens. -/
lemma affineOpens_coversTop (Y : Scheme.{u}) :
    (Opens.grothendieckTopology Y).CoversTop
      (fun (U : Y.affineOpens) => (U : TopologicalSpace.Opens Y)) := by
  intro V x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact ⟨W, homOfLE hWV, ⟨⟨W, hW⟩, ⟨𝟙 _⟩⟩, hxW⟩

set_option maxHeartbeats 800000 in
/-- Lemma 24 (global): the pushforward `f_*F` along a morphism of schemes `f : X → Y`
of a quasicoherent `F` on `X` is again quasicoherent. This is obtained by gluing the
local case over the affine cover of `Y`. -/
theorem pushforward_isQuasicoherent
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent := by

  haveI := fun (U : Y.affineOpens) =>
    pushforward_over_affineOpen_isQuasicoherent f F U

  exact SheafOfModules.IsQuasicoherent.of_coversTop
    ((Scheme.Modules.pushforward f).obj F)
    (fun (U : Y.affineOpens) => (U : TopologicalSpace.Opens Y))
    (affineOpens_coversTop Y)

/-- Instance form of Lemma 24: pushforward preserves quasicoherence, so the typeclass
search can pick it up automatically. -/
instance pushforward_isQuasicoherent_inst
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
  pushforward_isQuasicoherent f F

/-- Affine-to-affine specialisation: for `f : X → Y` between affine schemes,
pushforward of a quasicoherent sheaf is quasicoherent. -/
theorem pushforward_isQuasicoherent_affine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
  pushforward_isQuasicoherent f F

/-- For an affine morphism `f : X → Y`, pushforward of a quasicoherent sheaf is
quasicoherent. -/
theorem pushforward_isQuasicoherent_of_affineHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
  pushforward_isQuasicoherent f F

end Lemma24

end
