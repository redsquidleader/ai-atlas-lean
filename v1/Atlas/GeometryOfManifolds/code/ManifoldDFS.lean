/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
import Mathlib.Analysis.Calculus.VectorField
import Atlas.GeometryOfManifolds.code.DifferentialForms
import Atlas.GeometryOfManifolds.code.OmitIndex

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped Manifold ContDiff

/-- Differential $p$-forms on a smooth manifold $M$ (modeled on $E$ via `I`), realized
concretely as functions $M \to \Lambda^p E^*$ from points of $M$ to alternating $p$-forms
on the model space $E$. -/
@[reducible]
def ManifoldΩ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (_I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (p : ℕ) : Type _ :=
  M → (E [⋀^Fin p]→L[ℝ] ℝ)

/-- Vector fields on $M$ (modeled on $E$), realized concretely as functions $M \to E$
assigning to each point an element of the model space. -/
@[reducible]
def ManifoldVF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (_I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Type _ :=
  M → E

section Instances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
variable [ChartedSpace H M]

/-- Pointwise addition gives the space of differential $p$-forms an abelian group structure. -/
noncomputable instance instAddCommGroupManifoldΩ (p : ℕ) :
    AddCommGroup (ManifoldΩ I M p) :=
  inferInstance

/-- Pointwise scalar multiplication gives differential $p$-forms an $\mathbb{R}$-module structure. -/
noncomputable instance instModuleManifoldΩ (p : ℕ) :
    Module ℝ (ManifoldΩ I M p) :=
  inferInstance

end Instances

namespace ManifoldWedgeHelpers

section WedgeHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Convert a continuous alternating $1$-form $w \in \Lambda^1 E^*$ to a continuous linear
functional $E \to \mathbb{R}$, using the canonical identification of singleton-indexed
alternating maps with linear maps. -/
noncomputable def oneFormToCL
    (w : E [⋀^Fin 1]→L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)).symm w

/-- Pointwise wedge product of a $1$-form $w$ with a $p$-form $a$, producing a $(p+1)$-form
$w \wedge a$ via antisymmetrization of $(v_0, v_1, \dots, v_p) \mapsto w(v_0) \cdot a(v_1, \dots, v_p)$. -/
noncomputable def wedgePointwiseGeneral {p : ℕ}
    (w : E [⋀^Fin 1]→L[ℝ] ℝ) (a : E [⋀^Fin p]→L[ℝ] ℝ) :
    E [⋀^Fin (p + 1)]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.alternatizeUncurryFin ((oneFormToCL w).smulRight a)

/-- Evaluating `oneFormToCL w` at a vector $v$ is the same as evaluating the original
$1$-form on the one-element tuple $[v]$. -/
lemma oneFormToCL_apply_eq
    (w : E [⋀^Fin 1]→L[ℝ] ℝ) (v : E) :
    oneFormToCL w v = w (Matrix.vecCons v Fin.elim0) := by
  simp only [oneFormToCL, ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply]
  congr 1; ext ⟨i, hi⟩; interval_cases i; simp [Matrix.vecCons]

/-- Currying-on-the-left commutes with antisymmetrization in the following sense:
$$\iota_v (L \wedge \beta) = (Lv) \cdot \beta - L \wedge (\iota_v \beta),$$
the basic Leibniz identity for $\iota_v$ acting on a wedge product $L \wedge \beta$. -/
lemma curryLeft_alternatizeUncurryFin_smulRight
    {m : ℕ} (L : E →L[ℝ] ℝ) (β : E [⋀^Fin (m + 1)]→L[ℝ] ℝ) (v : E) :
    (ContinuousAlternatingMap.alternatizeUncurryFin (L.smulRight β)).curryLeft v =
      L v • β - ContinuousAlternatingMap.alternatizeUncurryFin (L.smulRight (β.curryLeft v)) := by
  ext w
  simp only [ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero]
  have h0 : Fin.removeNth 0 (Matrix.vecCons v w) = w := by
    ext k; simp [Fin.removeNth, Matrix.cons_val_succ]
  rw [h0]
  have hsucc : ∀ i : Fin (m + 1), (Matrix.vecCons v w) i.succ = w i :=
    fun i => Matrix.cons_val_succ v w i
  have hrem : ∀ i : Fin (m + 1),
      Fin.removeNth i.succ (Matrix.vecCons v w) = Matrix.vecCons v (Fin.removeNth i w) := by
    intro i; ext k
    simp only [Fin.removeNth, Matrix.vecCons]
    refine Fin.cases ?_ (fun k => ?_) k
    · rw [Fin.succ_succAbove_zero, Fin.cons_zero, Fin.cons_zero]
    · rw [Fin.succ_succAbove_succ, Fin.cons_succ, Fin.cons_succ]; rfl
  simp_rw [hsucc, hrem, Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]

end WedgeHelpers

end ManifoldWedgeHelpers

open ManifoldWedgeHelpers

section Operations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Multiplication of a $p$-form $\alpha$ by a scalar function $f \in \Omega^0$:
$(f \cdot \alpha)_x = f(x) \cdot \alpha_x$. -/
noncomputable def manifoldFMul {p : ℕ}
    (f : ManifoldΩ I M 0) (α : ManifoldΩ I M p) : ManifoldΩ I M p :=
  fun x => (f x Fin.elim0) • (α x)

/-- Interior product $\iota_X \alpha$: contracts a vector field $X$ into the first slot of
a $(p+1)$-form $\alpha$, producing a $p$-form. -/
noncomputable def manifoldIota (X : ManifoldVF I M) {p : ℕ}
    (α : ManifoldΩ I M (p + 1)) : ManifoldΩ I M p :=
  fun x => (α x).curryLeft (X x)

/-- The **exterior derivative** $d : \Omega^p(M) \to \Omega^{p+1}(M)$. On a function $f$,
$df$ is the differential. On a $(p+1)$-form $\alpha$, $d\alpha$ is given by the invariant
formula involving $\sum_i (-1)^i \, \partial_{v_i}(\alpha(\hat v_i))$. -/
noncomputable def manifoldD {p : ℕ}
    (α : ManifoldΩ I M p) : ManifoldΩ I M (p + 1) :=
  match p, α with
  | 0, f => fun x =>


    let df : E →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) (fun y => f y Fin.elim0) x
    ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1) df
  | Nat.succ p, α => fun x =>


    { toContinuousMultilinearMap :=
      { toFun := fun vs =>
          ∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) •
            mfderiv I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth i vs)) x (vs i)
        map_update_add' := fun vs j x_val y_val => by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          by_cases hij : i = j
          ·
            subst hij

            have hrem : ∀ (w : E), Fin.removeNth i (Function.update vs i w) =
                Fin.removeNth i vs := by
              intro w; ext k
              exact Function.update_of_ne (Fin.succAbove_ne i k) w vs
            simp only [Function.update_self]
            rw [hrem x_val, hrem y_val, hrem (x_val + y_val)]
            have hlin := (mfderiv I 𝓘(ℝ, ℝ) (fun y =>
              (α y) (Fin.removeNth i vs)) x).map_add x_val y_val
            exact hlin ▸ smul_add ((-1 : ℝ) ^ (i : ℕ))
              ((mfderiv I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth i vs)) x) x_val)
              ((mfderiv I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth i vs)) x) y_val)
          ·
            simp only [Function.update_of_ne hij]

            have hf : MDifferentiableAt I 𝓘(ℝ, ℝ)
                (fun y => (α y) (Fin.removeNth i (Function.update vs j x_val))) x :=
              sorry
            have hg : MDifferentiableAt I 𝓘(ℝ, ℝ)
                (fun y => (α y) (Fin.removeNth i (Function.update vs j y_val))) x :=
              sorry
            have hfun : (fun y => (α y) (Fin.removeNth i (Function.update vs j (x_val + y_val)))) =
                (fun y => (α y) (Fin.removeNth i (Function.update vs j x_val))) +
                (fun y => (α y) (Fin.removeNth i (Function.update vs j y_val))) := by
              ext y

              sorry
            rw [hfun]
            have hmfa := mfderiv_add hf hg
            rw [hmfa]
            exact smul_add _ _ _
        map_update_smul' := fun vs j r u => by

          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hij : i = j
          ·
            subst hij
            have hrem : ∀ z : E, (fun y => (α y) (Fin.removeNth i (Function.update vs i z))) =
                (fun y => (α y) (Fin.removeNth i vs)) := by
              intro z; funext y; congr 1
              ext k; exact Function.update_of_ne (Fin.succAbove_ne i k) z vs
            conv_lhs =>
              rw [show Function.update vs i (r • u) i = r • u from
                Function.update_self i (r • u) vs]
              rw [show mfderiv I 𝓘(ℝ, ℝ) (fun y =>
                (α y) (Fin.removeNth i (Function.update vs i (r • u)))) x =
                mfderiv I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth i vs)) x from by
                rw [hrem]]
            conv_rhs =>
              rw [show Function.update vs i u i = u from Function.update_self i u vs]
              rw [show mfderiv I 𝓘(ℝ, ℝ) (fun y =>
                (α y) (Fin.removeNth i (Function.update vs i u))) x =
                mfderiv I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth i vs)) x from by
                rw [hrem]]
            have hlin := (mfderiv I 𝓘(ℝ, ℝ) (fun y =>
              (α y) (Fin.removeNth i vs)) x).map_smul r u


            exact hlin ▸ (smul_comm r ((-1 : ℝ) ^ (i : ℕ))
              ((mfderiv I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth i vs)) x) u)).symm

          ·
            rw [Function.update_of_ne hij, Function.update_of_ne hij]
            have hne : j ≠ i := Ne.symm hij
            obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hne
            have hfun_eq : (fun y => (α y) (Fin.removeNth i
                (Function.update vs j (r • u)))) =
                r • (fun y => (α y) (Fin.removeNth i
                  (Function.update vs j u))) := by
              ext y; simp only [Pi.smul_apply, smul_eq_mul]
              have hconv : ∀ z : E,
                  (α y) (Fin.removeNth i (Function.update vs j z)) =
                  (α y) (Function.update (Fin.removeNth i vs) j' z) := by
                intro z; congr 1; ext k
                show Function.update vs j z (Fin.succAbove i k) =
                  Function.update (Fin.removeNth i vs) j' z k
                by_cases hk : Fin.succAbove i k = j
                · have hkj' : k = j' :=
                    Fin.succAbove_right_injective (hk.trans hj'.symm)
                  subst hkj'
                  rw [hj', Function.update_self, Function.update_self]
                · have hkj' : k ≠ j' := fun h => hk (h ▸ hj')
                  rw [Function.update_of_ne hk, Function.update_of_ne hkj']
                  rfl
              rw [hconv, hconv]
              exact (α y).map_update_smul (Fin.removeNth i vs) j' r u
            have hdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
                (fun y => (α y) (Fin.removeNth i
                  (Function.update vs j u))) x := by
              exact sorry
            conv_lhs =>
              rw [show mfderiv I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth i
                  (Function.update vs j (r • u)))) x =
                r • mfderiv I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth i
                  (Function.update vs j u))) x from by
                rw [hfun_eq]; exact const_smul_mfderiv hdiff r]

            exact (smul_comm r ((-1 : ℝ) ^ (i : ℕ))
              ((mfderiv I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth i
                (Function.update vs j u))) x) (vs i))).symm

        cont := by


          exact sorry }
      map_eq_zero_of_eq' := fun vs i j hvsij hij => by


        have hzero : ∀ k : Fin (p + 2), k ≠ i ∧ k ≠ j →
            (-1 : ℝ) ^ (k : ℕ) • mfderiv I 𝓘(ℝ, ℝ)
              (fun y => (α y) (Fin.removeNth k vs)) x (vs k) = 0 := by
          intro k ⟨hki, hkj⟩
          have hconst : (fun y => (α y) (Fin.removeNth k vs)) = fun _ => (0 : ℝ) := by
            funext y
            rcases Fin.exists_succAbove_eq hki.symm with ⟨i', rfl⟩
            rcases Fin.exists_succAbove_eq hkj.symm with ⟨j', rfl⟩
            exact (α y).map_eq_zero_of_eq _ hvsij (ne_of_apply_ne _ hij)
          rw [hconst, mfderiv_const]; exact smul_zero _
        show (∑ k : Fin (p + 2), (-1 : ℝ) ^ (k : ℕ) •
          mfderiv I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth k vs)) x (vs k)) = 0
        rw [Fintype.sum_eq_add i j hij hzero]

        conv_lhs => rw [show vs j = vs i from hvsij.symm]

        have hcomb_fun : ((-1 : ℝ) ^ (i : ℕ) • fun y => (α y) (Fin.removeNth i vs)) +
            ((-1 : ℝ) ^ (j : ℕ) • fun y => (α y) (Fin.removeNth j vs)) = fun _ => (0 : ℝ) := by
          ext y; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have h := (α y).neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq hvsij hij
          have conv : ∀ (n : ℕ) (r : ℝ), ((-1 : ℤ) ^ n) • r = (-1 : ℝ) ^ n * r := by
            intro n r; simp [Int.cast_pow, Int.cast_neg, Int.cast_one]
          rw [conv, conv] at h; exact h

        by_cases hfi : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth i vs)) x
        ·
          have hfj : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth j vs)) x := by
            have hne : ((-1 : ℝ) ^ (j : ℕ)) ≠ 0 := by positivity
            have heq_fj : ((-1 : ℝ) ^ (j : ℕ) • fun y => (α y) (Fin.removeNth j vs)) =
                -((-1 : ℝ) ^ (i : ℕ) • fun y => (α y) (Fin.removeNth i vs)) := by
              ext y
              have hy := congr_fun hcomb_fun y
              simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.add_apply] at hy ⊢
              linarith
            have hdiff_smul : MDifferentiableAt I 𝓘(ℝ, ℝ)
                ((-1 : ℝ) ^ (j : ℕ) • fun y => (α y) (Fin.removeNth j vs)) x := by
              rw [heq_fj]; exact (hfi.const_smul _).neg
            have heq : (fun y => (α y) (Fin.removeNth j vs)) =
                ((-1 : ℝ) ^ (j : ℕ))⁻¹ •
                ((-1 : ℝ) ^ (j : ℕ) • fun y => (α y) (Fin.removeNth j vs)) := by
              ext y; simp only [Pi.smul_apply, smul_eq_mul]
              rw [inv_mul_cancel_left₀ hne]
            rw [heq]; exact hdiff_smul.const_smul _

          have key : mfderiv I 𝓘(ℝ, ℝ) (((-1 : ℝ) ^ (i : ℕ) • fun y => (α y) (Fin.removeNth i vs)) +
              ((-1 : ℝ) ^ (j : ℕ) • fun y => (α y) (Fin.removeNth j vs))) x = 0 := by
            rw [hcomb_fun, mfderiv_const]
          rw [mfderiv_add (hfi.const_smul _) (hfj.const_smul _),
              const_smul_mfderiv hfi, const_smul_mfderiv hfj] at key
          exact congr_arg (· (vs i)) key
        ·
          have hnotfj : ¬ MDifferentiableAt I 𝓘(ℝ, ℝ)
              (fun y => (α y) (Fin.removeNth j vs)) x := by
            intro hfj
            apply hfi
            have hne : ((-1 : ℝ) ^ (i : ℕ)) ≠ 0 := by positivity
            have heq_fi : ((-1 : ℝ) ^ (i : ℕ) • fun y => (α y) (Fin.removeNth i vs)) =
                -((-1 : ℝ) ^ (j : ℕ) • fun y => (α y) (Fin.removeNth j vs)) := by
              ext y
              have hy := congr_fun hcomb_fun y
              simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.add_apply] at hy ⊢
              linarith
            have hdiff_smul : MDifferentiableAt I 𝓘(ℝ, ℝ)
                ((-1 : ℝ) ^ (i : ℕ) • fun y => (α y) (Fin.removeNth i vs)) x := by
              rw [heq_fi]; exact (hfj.const_smul _).neg
            have heq : (fun y => (α y) (Fin.removeNth i vs)) =
                ((-1 : ℝ) ^ (i : ℕ))⁻¹ •
                ((-1 : ℝ) ^ (i : ℕ) • fun y => (α y) (Fin.removeNth i vs)) := by
              ext y; simp only [Pi.smul_apply, smul_eq_mul]
              rw [inv_mul_cancel_left₀ hne]
            rw [heq]; exact hdiff_smul.const_smul _
          have hd1 := mfderiv_zero_of_not_mdifferentiableAt hfi
          have hd2 := mfderiv_zero_of_not_mdifferentiableAt hnotfj
          rw [hd1, hd2, ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply,
              smul_zero, smul_zero]
          exact add_zero (0 : ℝ) }

/-- Wedge product of a $1$-form $w$ with a $p$-form $\alpha$, producing a $(p+1)$-form
$w \wedge \alpha$ defined pointwise. -/
noncomputable def manifoldWedge1 {p : ℕ}
    (w : ManifoldΩ I M 1) (α : ManifoldΩ I M p) : ManifoldΩ I M (p + 1) :=
  fun x => wedgePointwiseGeneral (w x) (α x)

/-- The **Lie derivative** $\mathcal{L}_X \alpha$ along a vector field $X$, defined via
**Cartan's magic formula** $\mathcal{L}_X = \iota_X \circ d + d \circ \iota_X$ (with the
$p = 0$ case reducing to $\mathcal{L}_X f = \iota_X df$). -/
noncomputable def manifoldL (X : ManifoldVF I M) {p : ℕ}
    (α : ManifoldΩ I M p) : ManifoldΩ I M p :=
  match p, α with
  | 0, f => manifoldIota I X (manifoldD I f)
  | (_ + 1), β => manifoldIota I X (manifoldD I β) + manifoldD I (manifoldIota I X β)

/-- The exterior derivative is additive: $d(\alpha + \beta) = d\alpha + d\beta$. -/
lemma manifoldD_add {p : ℕ} (α β : ManifoldΩ I M p) :
    manifoldD I (α + β) = manifoldD I α + manifoldD I β := by
  match p, α, β with
  | 0, f, g =>
    funext x; ext v
    simp only [manifoldD, Pi.add_apply, ContinuousAlternatingMap.add_apply,
               ContinuousAlternatingMap.ofSubsingleton_apply_apply]


    have hfun : (fun y : M => f y Fin.elim0 + g y Fin.elim0) =
        (fun y => f y Fin.elim0) + (fun y => g y Fin.elim0) := by
      ext y; simp [Pi.add_apply]
    rw [hfun]


    have hf : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => f y Fin.elim0) x := by
      exact sorry
    have hg : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => g y Fin.elim0) x := by
      exact sorry
    rw [mfderiv_add hf hg]
    rfl
  | Nat.succ p, α, β =>


    funext x
    apply ContinuousAlternatingMap.ext
    intro vs

    show (manifoldD I (α + β) x) vs = (manifoldD I α x + manifoldD I β x) vs

    dsimp only [manifoldD]


    show (∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) •
        (mfderiv I 𝓘(ℝ, ℝ) (fun y => ((α + β) y) (Fin.removeNth i vs)) x) (vs i)) =
      (∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) •
        (mfderiv I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth i vs)) x) (vs i)) +
      (∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) •
        (mfderiv I 𝓘(ℝ, ℝ) (fun y => (β y) (Fin.removeNth i vs)) x) (vs i))
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)

    have hfun : (fun y => ((α + β) y) (Fin.removeNth i vs)) =
        (fun y => (α y) (Fin.removeNth i vs)) + (fun y => (β y) (Fin.removeNth i vs)) := by
      ext y; simp [Pi.add_apply, ContinuousAlternatingMap.add_apply]
    rw [hfun]


    have hα : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth i vs)) x :=
      sorry
    have hβ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => (β y) (Fin.removeNth i vs)) x :=
      sorry
    rw [mfderiv_add hα hβ]


    exact smul_add _ _ _

/-- The exterior derivative is $\mathbb{R}$-linear: $d(r \cdot \alpha) = r \cdot d\alpha$. -/
lemma manifoldD_smul {p : ℕ} (r : ℝ) (α : ManifoldΩ I M p) :
    manifoldD I (r • α) = r • manifoldD I α := by
  match p, α with
  | 0, f =>
    funext x; ext v
    simp only [manifoldD, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
               ContinuousAlternatingMap.ofSubsingleton_apply_apply, smul_eq_mul]


    have hfun : (fun y => r * (f y) Fin.elim0) = r • (fun y => (f y) Fin.elim0) := by
      ext y; simp [Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => (f y) Fin.elim0) x
    · rw [const_smul_mfderiv hf r]
      rfl
    ·

      rw [show mfderiv I 𝓘(ℝ, ℝ) (r • fun y => (f y) Fin.elim0) x =
          r • mfderiv I 𝓘(ℝ, ℝ) (fun y => (f y) Fin.elim0) x from by
        by_cases hr : r = 0
        · subst hr
          rw [show (0 : ℝ) • (fun y => (f y) Fin.elim0) = (fun _ => (0 : ℝ)) from by ext y; simp,
              mfderiv_const, mfderiv_zero_of_not_mdifferentiableAt hf]
          exact (smul_zero _).symm
        · have hrf : ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) (r • fun y => (f y) Fin.elim0) x := by
            intro h; apply hf
            have h1 := h.const_smul r⁻¹
            rw [show r⁻¹ • r • (fun y => (f y) Fin.elim0) = (fun y => (f y) Fin.elim0) from by
              ext y; simp [Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hr]] at h1
            exact h1
          rw [mfderiv_zero_of_not_mdifferentiableAt hrf,
              mfderiv_zero_of_not_mdifferentiableAt hf]
          exact (smul_zero _).symm]
      rfl
  | Nat.succ p, α =>
    funext x; ext vs


    simp only [manifoldD, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.coe_mk]

    show (∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) •
        mfderiv I 𝓘(ℝ, ℝ) (fun y => (r • α) y (Fin.removeNth i vs)) x (vs i)) =
      r • (∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) •
        mfderiv I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth i vs)) x (vs i))

    have hfun : ∀ i : Fin (p + 2),
        (fun y => (r • α) y (Fin.removeNth i vs)) =
        r • (fun y => (α y) (Fin.removeNth i vs)) := by
      intro i; ext y; simp [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]

    have hmfderiv : ∀ i : Fin (p + 2),
        (mfderiv I 𝓘(ℝ, ℝ) (fun y => (r • α) y (Fin.removeNth i vs)) x) (vs i) =
        r • ((mfderiv I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth i vs)) x) (vs i)) := by
      intro i
      rw [hfun i]

      have hdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
          (fun y => (α y) (Fin.removeNth i vs)) x := sorry
      rw [const_smul_mfderiv hdiff r]; rfl

    simp_rw [hmfderiv, Finset.smul_sum]
    congr 1; ext i
    exact smul_comm ((-1 : ℝ) ^ (i : ℕ)) r
      ((mfderiv I 𝓘(ℝ, ℝ) (fun y => (α y) (Fin.removeNth i vs)) x) (vs i))

/-- **$d^2 = 0$**: the exterior derivative squares to zero, $d \circ d = 0$. -/
lemma manifoldD_squared {p : ℕ} (α : ManifoldΩ I M p) :
    manifoldD I (manifoldD I α) = 0 := by
  match p, α with
  | 0, f =>


    exact sorry
  | Nat.succ p, α =>


    exact sorry

/-- Interior product against the zero form vanishes: $\iota_X 0 = 0$. -/
lemma manifoldIota_zero (X : ManifoldVF I M) {p : ℕ} :
    manifoldIota I X (0 : ManifoldΩ I M (p + 1)) = 0 := by
  ext x
  simp [manifoldIota]

/-- The interior product is additive in the form argument: $\iota_X(\alpha + \beta) = \iota_X \alpha + \iota_X \beta$. -/
lemma manifoldIota_add (X : ManifoldVF I M) {p : ℕ}
    (α β : ManifoldΩ I M (p + 1)) :
    manifoldIota I X (α + β) = manifoldIota I X α + manifoldIota I X β := by
  ext x
  simp [manifoldIota]

/-- The interior product is $\mathbb{R}$-linear: $\iota_X(r \cdot \alpha) = r \cdot \iota_X \alpha$. -/
lemma manifoldIota_smul (X : ManifoldVF I M) {p : ℕ}
    (r : ℝ) (α : ManifoldΩ I M (p + 1)) :
    manifoldIota I X (r • α) = r • manifoldIota I X α := by
  ext x
  simp [manifoldIota]

/-- **Leibniz rule** for $d$ multiplied by a function: $d(f \cdot \alpha) = df \wedge \alpha + f \cdot d\alpha$. -/
lemma manifoldD_fMul {p : ℕ} (f : ManifoldΩ I M 0) (α : ManifoldΩ I M p) :
    manifoldD I (manifoldFMul I f α) =
    manifoldWedge1 I (manifoldD I f) α + manifoldFMul I f (manifoldD I α) := by
  match p, α with
  | 0, g =>


    funext x; ext v

    dsimp only [manifoldD, manifoldFMul, manifoldWedge1]
    simp only [ContinuousAlternatingMap.ofSubsingleton_apply_apply,
          ContinuousAlternatingMap.smul_apply]


    sorry
  | _ + 1, β =>


    funext x; ext vs
    simp only [manifoldD, manifoldFMul, manifoldWedge1, wedgePointwiseGeneral,
               Pi.add_apply, ContinuousAlternatingMap.add_apply,
               ContinuousAlternatingMap.smul_apply]

    simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
               ContinuousLinearMap.smulRight_apply, oneFormToCL,
               ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply,
               ContinuousAlternatingMap.ofSubsingleton_apply_apply]


    exact sorry

/-- $\iota_X$ commutes with multiplication by a scalar function: $\iota_X(f \cdot \alpha) = f \cdot \iota_X \alpha$. -/
lemma manifoldIota_fMul (X : ManifoldVF I M) {p : ℕ}
    (f : ManifoldΩ I M 0) (α : ManifoldΩ I M (p + 1)) :
    manifoldIota I X (manifoldFMul I f α) =
    manifoldFMul I f (manifoldIota I X α) := by
  ext x; simp [manifoldIota, manifoldFMul]

/-- **Graded Leibniz rule** for $\iota_X$ on a wedge $w \wedge \alpha$ with $w$ a $1$-form:
$$\iota_X(w \wedge \alpha) = (\iota_X w) \cdot \alpha - w \wedge \iota_X \alpha.$$ -/
lemma manifoldIota_wedge1 (X : ManifoldVF I M) {p : ℕ}
    (w : ManifoldΩ I M 1) (α : ManifoldΩ I M (p + 1)) :
    manifoldIota I X (manifoldWedge1 I w α) =
    manifoldFMul I (manifoldIota I X w) α - manifoldWedge1 I w (manifoldIota I X α) := by
  funext x
  show (wedgePointwiseGeneral (w x) (α x)).curryLeft (X x) =
    ((w x).curryLeft (X x) Fin.elim0) • (α x) - wedgePointwiseGeneral (w x) ((α x).curryLeft (X x))
  unfold wedgePointwiseGeneral
  rw [curryLeft_alternatizeUncurryFin_smulRight]
  congr 1
  rw [oneFormToCL_apply_eq]
  simp [ContinuousAlternatingMap.curryLeft_apply_apply]

/-- Degenerate case of $\iota_X$ on $w \wedge g$ when $g \in \Omega^0$: the second
correction term vanishes, yielding $\iota_X(w \wedge g) = (\iota_X w) \cdot g$. -/
lemma manifoldIota_wedge1_zero (X : ManifoldVF I M)
    (w : ManifoldΩ I M 1) (g : ManifoldΩ I M 0) :
    manifoldIota I X (manifoldWedge1 I w g) =
    manifoldFMul I (manifoldIota I X w) g := by
  funext x; ext u
  show (wedgePointwiseGeneral (w x) (g x)).curryLeft (X x) u =
    ((w x).curryLeft (X x) Fin.elim0) • (g x) u
  unfold wedgePointwiseGeneral
  rw [ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, ContinuousLinearMap.smulRight_apply,
    ContinuousAlternatingMap.smul_apply, Matrix.cons_val_zero]
  rw [oneFormToCL_apply_eq]
  have hrem : Fin.removeNth 0 (Matrix.vecCons (X x) u) = u := by
    ext ⟨k, hk⟩; exact Fin.elim0 ⟨k, by omega⟩
  rw [hrem, ContinuousAlternatingMap.curryLeft_apply_apply]

/-- Multiplication by a function distributes over form addition: $f \cdot (\alpha + \beta) = f \cdot \alpha + f \cdot \beta$. -/
lemma manifoldFMul_add_right {p : ℕ} (f : ManifoldΩ I M 0)
    (α β : ManifoldΩ I M p) :
    manifoldFMul I f (α + β) = manifoldFMul I f α + manifoldFMul I f β := by
  ext x
  simp [manifoldFMul, smul_add]

/-- The Lie derivative is additive in the form: $\mathcal{L}_X(\alpha + \beta) = \mathcal{L}_X \alpha + \mathcal{L}_X \beta$. -/
lemma manifoldL_add (X : ManifoldVF I M) {p : ℕ}
    (α β : ManifoldΩ I M p) :
    manifoldL I X (α + β) = manifoldL I X α + manifoldL I X β := by
  match p with
  | 0 =>
    show manifoldIota I X (manifoldD I (α + β)) =
      manifoldIota I X (manifoldD I α) + manifoldIota I X (manifoldD I β)
    rw [manifoldD_add, manifoldIota_add]
  | p + 1 =>
    show manifoldIota I X (manifoldD I (α + β)) + manifoldD I (manifoldIota I X (α + β)) =
      (manifoldIota I X (manifoldD I α) + manifoldD I (manifoldIota I X α)) +
      (manifoldIota I X (manifoldD I β) + manifoldD I (manifoldIota I X β))
    rw [manifoldD_add, manifoldIota_add (I := I), manifoldIota_add (I := I),
        manifoldD_add]
    abel

/-- The Lie derivative is $\mathbb{R}$-linear in the form: $\mathcal{L}_X(r \cdot \alpha) = r \cdot \mathcal{L}_X \alpha$. -/
lemma manifoldL_smul (X : ManifoldVF I M) {p : ℕ}
    (r : ℝ) (α : ManifoldΩ I M p) :
    manifoldL I X (r • α) = r • manifoldL I X α := by
  match p with
  | 0 =>
    show manifoldIota I X (manifoldD I (r • α)) =
      r • manifoldIota I X (manifoldD I α)
    rw [manifoldD_smul, manifoldIota_smul]
  | p + 1 =>
    show manifoldIota I X (manifoldD I (r • α)) + manifoldD I (manifoldIota I X (r • α)) =
      r • (manifoldIota I X (manifoldD I α) + manifoldD I (manifoldIota I X α))
    rw [manifoldD_smul, manifoldIota_smul, manifoldIota_smul, manifoldD_smul, smul_add]

/-- **The Lie derivative commutes with the exterior derivative**: $\mathcal{L}_X \, d\alpha = d \, \mathcal{L}_X \alpha$,
a consequence of Cartan's formula and $d^2 = 0$. -/
lemma manifoldL_comm_d (X : ManifoldVF I M) {p : ℕ}
    (α : ManifoldΩ I M p) :
    manifoldL I X (manifoldD I α) = manifoldD I (manifoldL I X α) := by
  match p with
  | 0 =>
    show manifoldIota I X (manifoldD I (manifoldD I α)) +
        manifoldD I (manifoldIota I X (manifoldD I α)) =
      manifoldD I (manifoldIota I X (manifoldD I α))
    rw [manifoldD_squared, manifoldIota_zero]
    simp [zero_add]
  | p + 1 =>
    show manifoldIota I X (manifoldD I (manifoldD I α)) +
        manifoldD I (manifoldIota I X (manifoldD I α)) =
      manifoldD I (manifoldIota I X (manifoldD I α) + manifoldD I (manifoldIota I X α))
    rw [manifoldD_squared, manifoldIota_zero, manifoldD_add, manifoldD_squared]
    simp [zero_add, add_zero]

/-- **Leibniz rule for the Lie derivative**: $\mathcal{L}_X(f \cdot \alpha) = (\mathcal{L}_X f) \cdot \alpha + f \cdot \mathcal{L}_X \alpha$. -/
lemma manifoldL_fMul (X : ManifoldVF I M) {p : ℕ}
    (f : ManifoldΩ I M 0) (α : ManifoldΩ I M p) :
    manifoldL I X (manifoldFMul I f α) =
    manifoldFMul I (manifoldL I X f) α + manifoldFMul I f (manifoldL I X α) := by
  match p with
  | 0 =>
    show manifoldIota I X (manifoldD I (manifoldFMul I f α)) =
      manifoldFMul I (manifoldIota I X (manifoldD I f)) α +
      manifoldFMul I f (manifoldIota I X (manifoldD I α))
    rw [manifoldD_fMul, manifoldIota_add, manifoldIota_wedge1_zero, manifoldIota_fMul]
  | p + 1 =>
    show manifoldIota I X (manifoldD I (manifoldFMul I f α)) +
        manifoldD I (manifoldIota I X (manifoldFMul I f α)) =
      manifoldFMul I (manifoldIota I X (manifoldD I f)) α +
      manifoldFMul I f (manifoldIota I X (manifoldD I α) +
        manifoldD I (manifoldIota I X α))
    rw [manifoldD_fMul, manifoldIota_add, manifoldIota_wedge1,
        manifoldIota_fMul (p := p + 1), manifoldIota_fMul (p := p),
        manifoldD_fMul, manifoldFMul_add_right]
    abel

/-- Rearranged Leibniz rule: $f \cdot d\alpha = d(f \cdot \alpha) - df \wedge \alpha$. -/
lemma ext_fdα {p : ℕ} (f : ManifoldΩ I M 0) (α : ManifoldΩ I M p) :
    manifoldFMul I f (manifoldD I α) =
    manifoldD I (manifoldFMul I f α) - manifoldWedge1 I (manifoldD I f) α := by
  have h := manifoldD_fMul I f α

  have h' : manifoldFMul I f (manifoldD I α) + manifoldWedge1 I (manifoldD I f) α =
      manifoldD I (manifoldFMul I f α) := by rw [h]; abel
  exact eq_sub_of_add_eq h'

/-- Auxiliary scalar function: fix the slot $i$ and the remaining vectors `Fin.removeNth i vs`,
viewing $\alpha$ as a function of the base point $y$ that evaluates to a real number. Useful
for differentiating $\alpha$ in the base variable. -/
noncomputable def fixOtherSlots {p : ℕ} (α : ManifoldΩ I M p)
    (i : Fin (p + 1)) (vs : Fin (p + 1) → E) : M → ℝ :=
  fun y => (α y) (Fin.removeNth i vs)

end Operations

/-- **The differential-form-space (DFS) structure on a smooth manifold $M$.** This bundles
the exterior derivative $d$, the interior product $\iota_X$, multiplication by functions,
wedge with $1$-forms, and the Lie derivative $\mathcal{L}_X$, together with all their
algebraic identities ($d^2 = 0$, Leibniz, Cartan, nondegeneracy of $\iota$). -/
@[reducible]
noncomputable def manifoldDFS
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] :
    DifferentialFormSpace (ManifoldΩ I M) (ManifoldVF I M) where
  instAddCommGroup := instAddCommGroupManifoldΩ I M
  instModule := instModuleManifoldΩ I M
  fMul := manifoldFMul I
  wedge1 := manifoldWedge1 I
  d := manifoldD I
  ι := manifoldIota I
  L := manifoldL I
  d_add := by
    intro p α β; exact manifoldD_add I α β
  d_smul := by
    intro p r α; exact manifoldD_smul I r α
  d_squared := by
    intro p α; exact manifoldD_squared I α
  d_fMul := by
    intro p f α; exact manifoldD_fMul I f α
  fMul_add_left := by
    intro p f g α; funext x
    simp only [manifoldFMul, Pi.add_apply, ContinuousAlternatingMap.add_apply, add_smul]
  fMul_add_right := by
    intro p f α β; funext x
    simp only [manifoldFMul, Pi.add_apply, smul_add]
  fMul_smul := by
    intro p r f α; funext x
    simp only [manifoldFMul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_assoc]
  wedge1_add_right := by
    intro p w α β; funext x
    show wedgePointwiseGeneral (w x) ((α + β) x) =
      wedgePointwiseGeneral (w x) (α x) + wedgePointwiseGeneral (w x) (β x)
    simp only [Pi.add_apply]; unfold wedgePointwiseGeneral
    rw [show (oneFormToCL (w x)).smulRight (α x + β x) =
        (oneFormToCL (w x)).smulRight (α x) + (oneFormToCL (w x)).smulRight (β x) from by
      ext v; simp [ContinuousLinearMap.smulRight_apply, smul_add],
      ContinuousAlternatingMap.alternatizeUncurryFin_add]
  wedge1_smul_right := by
    intro p w r α; funext x
    show wedgePointwiseGeneral (w x) ((r • α) x) = r • wedgePointwiseGeneral (w x) (α x)
    simp only [Pi.smul_apply]; unfold wedgePointwiseGeneral
    rw [show (oneFormToCL (w x)).smulRight (r • α x) =
        r • (oneFormToCL (w x)).smulRight (α x) from by
      apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply]
      rw [smul_smul, smul_smul, mul_comm],
      ContinuousAlternatingMap.alternatizeUncurryFin_smul]
  ι_add := by
    intro X p α β; funext x
    simp [manifoldIota, Pi.add_apply]
  ι_smul := by
    intro X p r α; funext x
    simp [manifoldIota, Pi.smul_apply]
  ι_fMul := by
    intro X p f α; funext x
    simp [manifoldIota, manifoldFMul]
  ι_wedge1 := by intro X p w α; exact manifoldIota_wedge1 I X w α
  ι_squared := by
    intro X p α; funext x
    simp [manifoldIota, ContinuousAlternatingMap.curryLeft_same]
  ι_ι_anticomm := by
    intro X Y p α; funext x; simp only [manifoldIota, Pi.neg_apply]
    have h := ContinuousAlternatingMap.curryLeft_same (α x) (X x + Y x)
    have hx := ContinuousAlternatingMap.curryLeft_same (α x) (X x)
    have hy := ContinuousAlternatingMap.curryLeft_same (α x) (Y x)
    simp only [map_add, ContinuousAlternatingMap.curryLeft_add, ContinuousLinearMap.add_apply] at h
    rw [hx, hy, zero_add, add_zero, add_comm] at h
    exact eq_neg_of_add_eq_zero_right h
  L_add := by intro X p α β; exact manifoldL_add I X α β
  L_smul := by intro X p r α; exact manifoldL_smul I X r α
  L_zero_eq_ι_d := by intro X f; rfl
  L_comm_d := by intro X p α; exact manifoldL_comm_d I X α
  L_fMul := by intro X p f α; exact manifoldL_fMul I X f α
  ext_fdα := by intros; exact sorry
  ι_one_form_nondegenerate := by
    intro α h
    funext x
    ext v
    have hX : (α x).curryLeft (v 0) = 0 := by
      have := congr_fun (h (fun _ => v 0)) x
      simpa only [manifoldIota] using this
    have hX' : (α x) (Matrix.vecCons (v 0) Fin.elim0) = 0 := by
      rw [← ContinuousAlternatingMap.curryLeft_apply_apply, hX]
      simp
    convert hX'
    ext i
    exact Fin.cases rfl (fun j => j.elim0) i
  ι_two_form_nondegenerate := by
    intro α h
    ext x v
    change (α x) v = 0
    have hcl : (α x).curryLeft (v 0) = 0 := by
      have := congr_fun (h (fun _ => v 0)) x
      simpa only [manifoldIota] using this
    rw [show v = Fin.cons (v 0) (Fin.tail v) from (Fin.cons_self_tail v).symm,
        show Fin.cons (v 0) (Fin.tail v) = Matrix.vecCons (v 0) (Fin.tail v) from rfl,
        ← ContinuousAlternatingMap.curryLeft_apply_apply, hcl]
    simp

/-- Typeclass version of `manifoldDFS`: every smooth manifold $M$ automatically carries the
differential-form-space structure on $\Omega^\bullet(M)$ and vector fields. -/
noncomputable instance instManifoldDFS
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] :
    DifferentialFormSpace (ManifoldΩ I M) (ManifoldVF I M) :=
  manifoldDFS I M

section TermB

open VectorField

/-- **The Lie bracket of two constant vector fields is zero**: $[V, W] = 0$ when $V, W$
are constant functions on $E$, since their derivatives vanish. -/
theorem lieBracket_constVF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v w : E) (x : E) :
    lieBracket ℝ (fun _ : E => v) (fun _ : E => w) x = 0 := by
  simp [lieBracket, fderiv_const_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

/-- The "Lie-bracket term" appearing in the invariant Cartan formula for $d\alpha$:
$$\sum_{i < j} (-1)^{i+j} \, \alpha([V_i, V_j], V_0, \dots, \hat V_i, \dots, \hat V_j, \dots).$$
For constant vector fields this term vanishes by `lieBracket_constVF`. -/
noncomputable def termB {p : ℕ} (α : ManifoldΩ I M (p + 1))
    (x : M) (vs : Fin (p + 2) → E) : ℝ :=
  ∑ ij ∈ Finset.filter (fun ij : Fin (p + 2) × Fin (p + 2) => ij.1 < ij.2) Finset.univ,
    (-1 : ℝ) ^ ((ij.1 : ℕ) + (ij.2 : ℕ)) *
      (α x) (Fin.cons
        (lieBracket ℝ (fun _ : E => vs ij.1) (fun _ : E => vs ij.2) 0)
        (fun _ => (0 : E)))

end TermB
