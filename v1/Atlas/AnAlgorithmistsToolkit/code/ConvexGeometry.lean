/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Atlas.AnAlgorithmistsToolkit.code.PolarBody
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Basic
import Mathlib.Topology.Defs.Basic

open Set
open scoped Pointwise

namespace ConvexGeometry

def IsConvexBody {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (C : Set E) : Prop :=
  Convex ℝ C ∧ IsCompact C ∧ (interior C).Nonempty

theorem IsConvexBody.convex {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {C : Set E} (h : IsConvexBody C) : Convex ℝ C :=
  h.1

theorem IsConvexBody.isCompact {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {C : Set E} (h : IsConvexBody C) : IsCompact C :=
  h.2.1

theorem IsConvexBody.interior_nonempty {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E]
    {C : Set E} (h : IsConvexBody C) : (interior C).Nonempty :=
  h.2.2

noncomputable abbrev minkowskiFunctional {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : Set E) (x : E) : ℝ :=
  gauge C x

open Pointwise in
def banachMazurAdmissible {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K L : Set E) : Set ℝ :=
  {d : ℝ | 0 < d ∧ ∃ T : E ≃ₗ[ℝ] E, T '' L ⊆ K ∧ K ⊆ d • (T '' L)}

noncomputable def banachMazurDist {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K L : Set E) : ℝ :=
  sInf (banachMazurAdmissible K L)

section JohnEllipsoid

open MeasureTheory

variable {n : ℕ}

def IsEllipsoid (E : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
    E = T '' Metric.closedBall 0 1

def IsOriginSymmetric (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x, x ∈ K ↔ -x ∈ K

def unitBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.closedBall 0 1

def IsMaxVolInscribedEllipsoid (E K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsEllipsoid E ∧ E ⊆ K ∧
    ∀ E' : Set (EuclideanSpace ℝ (Fin n)),
      IsEllipsoid E' → E' ⊆ K → volume E' ≤ volume E

def JohnConditions (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  unitBall n ⊆ K ∧
  ∃ (m : ℕ) (u : Fin m → EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ),
    (∀ i, ‖u i‖ = 1) ∧
    (∀ i, u i ∈ frontier K) ∧
    (∀ i, 0 < c i) ∧
    (∑ i, c i • u i = 0) ∧
    (∀ x : EuclideanSpace ℝ (Fin n),
      ∑ i, c i * (@inner ℝ _ _ x (u i)) ^ 2 = ‖x‖ ^ 2)

theorem john_conditions_imply_max_vol (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK_convex : Convex ℝ K) (hK_compact : IsCompact K)
    (hK_interior : (interior K).Nonempty)
    (hK_symm : IsOriginSymmetric K)
    (hJ : JohnConditions n K) :
    IsMaxVolInscribedEllipsoid (unitBall n) K ∧
    ∀ E, IsMaxVolInscribedEllipsoid E K → E = unitBall n := by sorry

theorem max_vol_implies_john_conditions (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK_convex : Convex ℝ K) (hK_compact : IsCompact K)
    (hK_interior : (interior K).Nonempty)
    (hK_symm : IsOriginSymmetric K)
    (hMax : IsMaxVolInscribedEllipsoid (unitBall n) K ∧
            ∀ E, IsMaxVolInscribedEllipsoid E K → E = unitBall n) :
    JohnConditions n K := by sorry

theorem john_ellipsoid_characterization (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK_convex : Convex ℝ K) (hK_compact : IsCompact K)
    (hK_interior : (interior K).Nonempty)
    (hK_symm : IsOriginSymmetric K) :
    (IsMaxVolInscribedEllipsoid (unitBall n) K ∧
     ∀ E, IsMaxVolInscribedEllipsoid E K → E = unitBall n) ↔
    JohnConditions n K := by
  constructor
  · exact max_vol_implies_john_conditions n K hK_convex hK_compact hK_interior hK_symm
  · exact john_conditions_imply_max_vol n K hK_convex hK_compact hK_interior hK_symm

end JohnEllipsoid

theorem separating_hyperplane {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    {K : Set E} {p : E}
    (hK : IsConvexBody K) (hp : p ∉ K) :
    ∃ (f : E →L[ℝ] ℝ) (u : ℝ), (∀ a ∈ K, f a < u) ∧ u < f p := by
  have hclosed : IsClosed K := hK.isCompact.isClosed
  have hconvex : Convex ℝ K := hK.convex
  obtain ⟨f, u, hlt, hgt⟩ := geometric_hahn_banach_closed_point hconvex hclosed hp
  exact ⟨f, u, hlt, hgt⟩

theorem john_theorem_containment (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK_convex : Convex ℝ K) (hK_compact : IsCompact K)
    (hK_interior : (interior K).Nonempty)
    (hK_symm : IsOriginSymmetric K) :
    ∃ T : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n),
      T '' (Metric.closedBall 0 1) ⊆ K ∧
      K ⊆ (Real.sqrt ↑n) • (T '' (Metric.closedBall 0 1)) := by sorry

theorem banachMazur_distance_ball (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK_convex : Convex ℝ K) (hK_compact : IsCompact K)
    (hK_interior : (interior K).Nonempty)
    (hK_symm : IsOriginSymmetric K) :
    banachMazurDist K (Metric.closedBall 0 1) ≤ Real.sqrt ↑n := by
  obtain ⟨T, hT_sub, hK_sub⟩ := john_theorem_containment n hn K hK_convex hK_compact
    hK_interior hK_symm
  unfold banachMazurDist
  apply csInf_le
  · exact ⟨0, fun _ h => le_of_lt h.1⟩
  · exact ⟨Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn), T, hT_sub, hK_sub⟩

def halfspacePolytope {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} (a : ι → E) : Set E :=
  { x : E | ∀ i, @inner ℝ E _ (a i) x ≤ 1 }

theorem polarBody_halfspacePolytope_eq_convexHull
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (a : ι → E)
    (hC : Bornology.IsBounded (halfspacePolytope a)) :
    polarBody (halfspacePolytope a) = convexHull ℝ (Set.range a) := by sorry

section ConeReplacementLemma

open MeasureTheory

noncomputable def volumeRatio {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (K L : Set α) : ENNReal :=
  μ (K ∩ L) / μ K

def posHalfSpace (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | 0 ≤ x 0}

def IsConeAligned {n : ℕ} (C : Set (Fin (n + 1) → ℝ)) : Prop :=
  ∃ (y : Fin (n + 1) → ℝ), 0 < y 0 ∧
    (∀ i : Fin (n + 1), i ≠ 0 → y i = 0) ∧
    (∃ Hpos Hneg : ℝ, 0 < Hpos ∧ 0 ≤ Hneg ∧ ∀ x ∈ C, -Hneg ≤ x 0 ∧ x 0 ≤ Hpos) ∧
    (∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (y + t • (x - y)) ∈ C)

theorem cone_with_prescribed_volumes (n : ℕ) (hn : 1 ≤ n)
    (v_total v_pos : ENNReal)
    (hv_total_pos : v_total ≠ 0)
    (hv_total_fin : v_total ≠ ⊤)
    (hv_pos_pos : v_pos ≠ 0)
    (hv_pos_le : v_pos ≤ v_total) :
    ∃ (C' : Set (Fin (n + 1) → ℝ)),
      IsConeAligned C' ∧
      volume C' = v_total ∧
      volume (C' ∩ posHalfSpace n) = v_pos ∧
      ∃ (L' : Set (Fin (n + 1) → ℝ)),
        L' ⊆ posHalfSpace n ∧
        ENNReal.ofReal (Real.exp (-1)) ≤ volumeRatio volume C' L' := by sorry

theorem lemma8_cone_construction (n : ℕ) (hn : 1 ≤ n)
    (K' : Set (Fin (n + 1) → ℝ))
    (hK' : IsConvexBody K')
    (hpos : MeasureTheory.volume K' ≠ 0)
    (hfin : MeasureTheory.volume K' ≠ ⊤)
    (hH_pos : ∃ x ∈ K', x 0 > 0)
    (hH_neg : ∃ x ∈ K', x 0 < 0)
    (hcentroid : 0 ≤ (∫ x in K', x 0 ∂MeasureTheory.volume)) :
    ∃ (C' : Set (Fin (n + 1) → ℝ)),
      IsConeAligned C' ∧
      MeasureTheory.volume C' = MeasureTheory.volume K' ∧
      MeasureTheory.volume (C' ∩ posHalfSpace n) =
        MeasureTheory.volume (K' ∩ posHalfSpace n) ∧
      ∃ (L' : Set (Fin (n + 1) → ℝ)),
        L' ⊆ posHalfSpace n ∧
        ENNReal.ofReal (Real.exp (-1)) ≤ volumeRatio volume C' L' := by

  have hv_pos_pos : volume (K' ∩ posHalfSpace n) ≠ 0 := by
    obtain ⟨a, ha_mem, ha_pos⟩ := hH_pos
    obtain ⟨c, hc_int⟩ := hK'.interior_nonempty

    have hD_pos : (0 : ℝ) < |c 0| + a 0 + 1 := by positivity
    have ht₀_pos : (0 : ℝ) < (|c 0| + 1) / (|c 0| + a 0 + 1) :=
      div_pos (by linarith [abs_nonneg (c 0)]) hD_pos
    have ht₀_lt : (|c 0| + 1) / (|c 0| + a 0 + 1) < 1 := by
      rw [div_lt_one hD_pos]; linarith
    set t₀ := (|c 0| + 1) / (|c 0| + a 0 + 1)
    have hp_int : (1 - t₀) • c + t₀ • a ∈ interior K' :=
      Convex.combo_interior_self_mem_interior hK'.convex hc_int ha_mem
        (by linarith : (0 : ℝ) < 1 - t₀) (le_of_lt ht₀_pos)
        (by linarith : 1 - t₀ + t₀ = 1)
    have hp_coord : (0 : ℝ) < ((1 - t₀) • c + t₀ • a) 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hne : (|c 0| + a 0 + 1) ≠ 0 := ne_of_gt hD_pos
      rw [show (1 - t₀) * c 0 + t₀ * a 0 =
        a 0 * (c 0 + |c 0| + 1) / (|c 0| + a 0 + 1) from by
          simp only [t₀]; field_simp; ring]
      apply div_pos _ hD_pos
      apply mul_pos ha_pos
      linarith [neg_abs_le (c 0)]

    have hne : (interior K' ∩ {x : Fin (n+1) → ℝ | 0 < x 0}).Nonempty :=
      ⟨_, hp_int, hp_coord⟩
    have hopen : IsOpen (interior K' ∩ {x : Fin (n+1) → ℝ | 0 < x 0}) :=
      isOpen_interior.inter (isOpen_lt continuous_const (continuous_apply 0))
    exact ne_of_gt (lt_of_lt_of_le (hopen.measure_pos volume hne)
      (measure_mono (fun x ⟨hx_int, hx_pos⟩ =>
        ⟨interior_subset hx_int, (le_of_lt hx_pos : (0 : ℝ) ≤ x 0)⟩)))
  have hv_pos_le : volume (K' ∩ posHalfSpace n) ≤ volume K' :=
    measure_mono Set.inter_subset_left
  exact cone_with_prescribed_volumes n hn (volume K') (volume (K' ∩ posHalfSpace n))
    hpos hfin hv_pos_pos hv_pos_le

end ConeReplacementLemma

end ConvexGeometry
