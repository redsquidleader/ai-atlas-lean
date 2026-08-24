/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fin.Basic

namespace Proposition22_7


noncomputable def Obj : Type := by sorry

noncomputable def Weight : Type := by sorry

noncomputable def Funct : Type := by sorry

noncomputable def FObj : Funct → Obj → Obj := by sorry

noncomputable def VermaModule : Weight → Obj := by sorry

noncomputable def ProjectiveCover : Weight → Obj := by sorry

noncomputable def rho : Weight := by sorry

noncomputable def IsProjectiveFunctor : Funct → Prop := by sorry

noncomputable def IsIndecomposableObj : Obj → Prop := by sorry

noncomputable def IsProjectiveObj : Obj → Prop := by sorry

noncomputable def IsIndecomposable : Funct → Prop := by sorry

noncomputable def IsDominant : Weight → Prop := by sorry

noncomputable def FactorsThroughBlock : Funct → Weight → Prop := by sorry

noncomputable def IsDirectSumDecomp (F : Funct) {n : ℕ} (F_i : Fin n → Funct) : Prop := by sorry

noncomputable def IsDirectSumDecompObj (M : Obj) {n : ℕ} (summands : Fin n → Obj) : Prop := by sorry

noncomputable def ObjIso : Obj → Obj → Prop := by sorry

theorem krullSchmidt (M : Obj) :
    ∃ (n : ℕ) (summands : Fin n → Obj),
      IsDirectSumDecompObj M summands ∧
      (∀ i, IsIndecomposableObj (summands i)) := by sorry

theorem corollary_22_6_ii (F : Funct) (hF : IsProjectiveFunctor F)
    (lam : Weight) (n : ℕ) (summands : Fin n → Obj)
    (hDecomp : IsDirectSumDecompObj (FObj F (VermaModule lam)) summands) :
    ∃ (F_i : Fin n → Funct),
      (∀ i, IsProjectiveFunctor (F_i i)) ∧
      (∀ i, ObjIso (FObj (F_i i) (VermaModule lam)) (summands i)) ∧
      IsDirectSumDecomp F F_i := by sorry

theorem indecomposable_transfer (F_i : Funct) (hFi : IsProjectiveFunctor F_i)
    (lam : Weight) (hEval : IsIndecomposableObj (FObj F_i (VermaModule lam))) :
    IsIndecomposable F_i := by sorry

theorem projective_functor_preserves_proj
    (F : Funct) (hF : IsProjectiveFunctor F) (M : Obj) (hM : IsProjectiveObj M) :
    IsProjectiveObj (FObj F M) := by sorry

theorem verma_projective_of_dominant (lam : Weight) (hDom : IsDominant lam) :
    IsProjectiveObj (VermaModule lam) := by sorry

theorem functor_indecomp_implies_module_indecomp
    (F : Funct) (hF : IsProjectiveFunctor F) (hIndecomp : IsIndecomposable F)
    (lam : Weight) : IsIndecomposableObj (FObj F (VermaModule lam)) := by sorry

theorem indecomposable_projective_is_cover
    (M : Obj) (hIndecomp : IsIndecomposableObj M) (hProj : IsProjectiveObj M) :
    ∃ (mu : Weight), ObjIso M (ProjectiveCover mu) := by sorry

theorem indecomp_of_iso (M N : Obj) (h : ObjIso M N) (hN : IsIndecomposableObj N) :
    IsIndecomposableObj M := by sorry

theorem proposition_22_7_i
    (F : Funct)
    (hF : IsProjectiveFunctor F)
    (lam : Weight) :
    ∃ (n : ℕ) (F_i : Fin n → Funct),
      (∀ i, IsProjectiveFunctor (F_i i)) ∧
      (∀ i, IsIndecomposable (F_i i)) ∧
      IsDirectSumDecomp F F_i := by

  obtain ⟨N, summands, hKS, hSummandsIndecomp⟩ := krullSchmidt (FObj F (VermaModule lam))

  obtain ⟨F_i, hFi_proj, hFi_eval, hFi_decomp⟩ :=
    corollary_22_6_ii F hF lam N summands hKS

  refine ⟨N, F_i, hFi_proj, fun i => ?_, hFi_decomp⟩

  apply indecomposable_transfer (F_i i) (hFi_proj i) lam
  exact indecomp_of_iso _ _ (hFi_eval i) (hSummandsIndecomp i)

theorem proposition_22_7_ii
    (F : Funct)
    (hF : IsProjectiveFunctor F)
    (hIndecomp : IsIndecomposable F)
    (lam : Weight)
    (hDom : IsDominant lam)
    (hBlock : FactorsThroughBlock F lam) :

    ∃ (mu : Weight), ObjIso (FObj F (VermaModule lam)) (ProjectiveCover mu) := by

  have hMproj : IsProjectiveObj (VermaModule lam) := verma_projective_of_dominant lam hDom

  have hFMproj : IsProjectiveObj (FObj F (VermaModule lam)) :=
    projective_functor_preserves_proj F hF (VermaModule lam) hMproj

  have hFMindecomp : IsIndecomposableObj (FObj F (VermaModule lam)) :=
    functor_indecomp_implies_module_indecomp F hF hIndecomp lam

  exact indecomposable_projective_is_cover (FObj F (VermaModule lam)) hFMindecomp hFMproj

end Proposition22_7
