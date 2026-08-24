/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AnAlgorithmistsToolkit.code.BrunnMinkowski
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace BrunnMinkowskiInequality

open MeasureTheory Measure Pointwise


theorem brunn_minkowski_inequality
    {n : ℕ} (hn : 0 < n)
    (A B : Set (EuclideanSpace ℝ (Fin n)))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : 0 < volume A) (hB0 : 0 < volume B)
    (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤)
    (hABfin : volume (A + B) ≠ ⊤) :
    (volume (A + B)).toReal ^ ((1 : ℝ) / (n : ℝ)) ≥
    (volume A).toReal ^ ((1 : ℝ) / (n : ℝ)) + (volume B).toReal ^ ((1 : ℝ) / (n : ℝ)) := by sorry


theorem brunn_minkowski_equality_condition
    {n : ℕ} (hn : 0 < n)
    (A B : Set (EuclideanSpace ℝ (Fin n)))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : 0 < volume A) (hB0 : 0 < volume B)
    (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤)
    (hABfin : volume (A + B) ≠ ⊤) :
    (volume (A + B)).toReal ^ ((1 : ℝ) / (n : ℝ)) =
    (volume A).toReal ^ ((1 : ℝ) / (n : ℝ)) + (volume B).toReal ^ ((1 : ℝ) / (n : ℝ)) ↔
    ∃ (c : ℝ) (_ : c > 0) (v : EuclideanSpace ℝ (Fin n)),
      volume (symmDiff B (c • A + {v})) = 0 := by sorry

theorem brunn_minkowski_theorem
    {n : ℕ} (hn : 0 < n)
    (A B : Set (EuclideanSpace ℝ (Fin n)))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : 0 < volume A) (hB0 : 0 < volume B)
    (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤)
    (hABfin : volume (A + B) ≠ ⊤) :
    ((volume (A + B)).toReal ^ ((1 : ℝ) / (n : ℝ)) ≥
      (volume A).toReal ^ ((1 : ℝ) / (n : ℝ)) + (volume B).toReal ^ ((1 : ℝ) / (n : ℝ))) ∧
    ((volume (A + B)).toReal ^ ((1 : ℝ) / (n : ℝ)) =
      (volume A).toReal ^ ((1 : ℝ) / (n : ℝ)) + (volume B).toReal ^ ((1 : ℝ) / (n : ℝ)) ↔
      ∃ (c : ℝ) (_ : c > 0) (v : EuclideanSpace ℝ (Fin n)),
        volume (symmDiff B (c • A + {v})) = 0) :=
  ⟨brunn_minkowski_inequality hn A B hA hB hA0 hB0 hAfin hBfin hABfin,
   brunn_minkowski_equality_condition hn A B hA hB hA0 hB0 hAfin hBfin hABfin⟩

end BrunnMinkowskiInequality

namespace BrunnsTheorem

open MeasureTheory Set Pointwise
open scoped ENNReal NNReal

def parallelSlice {n : ℕ} (K : Set (Fin (n + 1) → ℝ)) (t : ℝ) : Set (Fin n → ℝ) :=
  {y : Fin n → ℝ | Fin.cons t y ∈ K}

noncomputable def sliceVolume {n : ℕ} (K : Set (Fin (n + 1) → ℝ)) (t : ℝ) : ℝ≥0∞ :=
  volume (parallelSlice K t)

noncomputable def brunnFunction (n : ℕ) (K : Set (Fin (n + 1) → ℝ)) (t : ℝ) : ℝ :=
  (sliceVolume K t).toReal ^ ((1 : ℝ) / (n : ℝ))

variable {n : ℕ}


theorem brunn_minkowski_superset_scaled (hn : 0 < n)
    (A B S : Set (Fin n → ℝ))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hsub : a • A + b • B ⊆ S) :
    (volume S).toReal ^ ((1 : ℝ) / (n : ℝ)) ≥
    a * (volume A).toReal ^ ((1 : ℝ) / (n : ℝ)) + b * (volume B).toReal ^ ((1 : ℝ) / (n : ℝ)) := by sorry

lemma slice_minkowski_subset (K : Set (Fin (n + 1) → ℝ)) (hK : Convex ℝ K)
    (r t : ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • (parallelSlice K r) + b • (parallelSlice K t) ⊆ parallelSlice K (a * r + b * t) := by
  intro z hz
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_add.mp hz
  obtain ⟨x, hx, hux⟩ := Set.mem_smul_set.mp hu
  obtain ⟨y, hy, hvy⟩ := Set.mem_smul_set.mp hv
  show Fin.cons (a * r + b * t) z ∈ K
  have key : a • (Fin.cons r x : Fin (n+1) → ℝ) + b • (Fin.cons t y : Fin (n+1) → ℝ) =
      (Fin.cons (a * r + b * t) (a • x + b • y) : Fin (n+1) → ℝ) := by
    funext i; refine Fin.cases ?_ ?_ i
    · simp [Pi.smul_apply, Pi.add_apply, Fin.cons_zero, smul_eq_mul]
    · intro j; simp [Pi.smul_apply, Pi.add_apply, Fin.cons_succ, smul_eq_mul]
  have hzeq : z = a • x + b • y := by
    rw [← hux, ← hvy] at huv; exact huv.symm
  rw [hzeq, ← key]; exact hK hx hy ha hb hab


theorem brunn_theorem
    (hn : 0 < n)
    (K : Set (Fin (n + 1) → ℝ))
    (hK : ConvexGeometry.IsConvexBody K) :
    ConcaveOn ℝ Set.univ (brunnFunction n K) := by
  constructor
  · exact convex_univ
  · intro r _ t _ a b ha hb hab
    simp only [smul_eq_mul]
    have hsub := slice_minkowski_subset K hK.convex r t a b ha hb hab
    have hbm := brunn_minkowski_superset_scaled hn
      (parallelSlice K r) (parallelSlice K t) (parallelSlice K (a * r + b * t))
      a b ha hb hab hsub
    unfold brunnFunction sliceVolume
    linarith

end BrunnsTheorem
