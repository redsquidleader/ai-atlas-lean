/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Field
import Atlas.BooleanFunctions.code.PCP
import Atlas.BooleanFunctions.code.MISBound

namespace UniqueGames

structure UniqueGame (V : Type*) (W : Type*) [DecidableEq V] [DecidableEq W] (k : ℕ) where
  edges : Finset (V × W)
  constraint : V → W → Equiv.Perm (Fin k)
  left_degree : ℕ
  right_degree : ℕ
  left_regular : ∀ v : V, (edges.filter (fun e => e.1 = v)).card = left_degree
  right_regular : ∀ w : W, (edges.filter (fun e => e.2 = w)).card = right_degree

structure Labeling (V : Type*) (W : Type*) (k : ℕ) where
  labelV : V → Fin k
  labelW : W → Fin k

def edgeSatisfied {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGame V W k) (labeling : Labeling V W k) (v : V) (w : W) : Prop :=
  game.constraint v w (labeling.labelV v) = labeling.labelW w

instance {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGame V W k) (labeling : Labeling V W k) (v : V) (w : W) :
    Decidable (edgeSatisfied game labeling v w) :=
  inferInstanceAs (Decidable (_ = _))

def numSatisfiedEdges {V : Type*} {W : Type*} {k : ℕ} [DecidableEq V] [DecidableEq W]
    (game : UniqueGame V W k) (labeling : Labeling V W k) : ℕ :=
  (game.edges.filter (fun p => edgeSatisfied game labeling p.1 p.2)).card

def numEdges {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGame V W k) : ℕ :=
  game.edges.card

noncomputable def fractionSatisfied {V : Type*} {W : Type*} {k : ℕ}
    [DecidableEq V] [DecidableEq W]
    (game : UniqueGame V W k) (labeling : Labeling V W k) : ℝ :=
  (numSatisfiedEdges game labeling : ℝ) / (numEdges game : ℝ)

noncomputable def value {V : Type*} {W : Type*} {k : ℕ}
    [DecidableEq V] [DecidableEq W]
    (game : UniqueGame V W k) : ℝ :=
  iSup (fun labeling : Labeling V W k => fractionSatisfied game labeling)

opaque IsPolyTimeUniqueGameReduction {numV numW : ℕ → ℕ} {k : ℕ} :
  (∀ (m : ℕ), PCP.BinaryString m → UniqueGame (Fin (numV m)) (Fin (numW m)) k) → Prop

def IsNPHardGapUniqueGame (k : ℕ) (c s : ℝ) : Prop :=
  ∀ (L : PCP.Language), PCP.InNP L →
    ∃ (numV numW : ℕ → ℕ) (reduce : ∀ (m : ℕ), PCP.BinaryString m → UniqueGame (Fin (numV m)) (Fin (numW m)) k),
      IsPolyTimeUniqueGameReduction reduce ∧
      (∀ (m : ℕ) (x : PCP.BinaryString m), x ∈ L m → value (reduce m x) ≥ c) ∧
      (∀ (m : ℕ) (x : PCP.BinaryString m), x ∉ L m → value (reduce m x) ≤ s)

structure NonBipartiteUniqueGame (X : Type*) [DecidableEq X] (k : ℕ) where
  edges : Finset (X × X)
  constraint : X → X → Equiv.Perm (Fin k)
  degree : ℕ
  regular : ∀ x : X, (edges.filter (fun e => e.1 = x)).card = degree

variable {X : Type*} [DecidableEq X] [Fintype X] {k : ℕ}

def NonBipartiteUniqueGame.edgesWithin (game : NonBipartiteUniqueGame X k)
    (X' : Finset X) : Finset (X × X) :=
  game.edges.filter (fun e => e.1 ∈ X' ∧ e.2 ∈ X')

def NonBipartiteUniqueGame.edgeSatisfiedBy (game : NonBipartiteUniqueGame X k)
    (A : X → Fin k) (e : X × X) : Prop :=
  game.constraint e.1 e.2 (A e.1) = A e.2

instance (game : NonBipartiteUniqueGame X k) (A : X → Fin k) (e : X × X) :
    Decidable (game.edgeSatisfiedBy A e) :=
  inferInstanceAs (Decidable (_ = _))

noncomputable def NonBipartiteUniqueGame.fractionSatisfiedWithin
    (game : NonBipartiteUniqueGame X k) (X' : Finset X) (A : X → Fin k) : ℝ :=
  ((game.edgesWithin X').filter (fun e => game.edgeSatisfiedBy A e)).card /
    (game.edgesWithin X').card

def NonBipartiteUniqueGame.edgeTSatisfiedBy (game : NonBipartiteUniqueGame X k)
    (A : X → Finset (Fin k)) (e : X × X) : Prop :=
  ∃ a ∈ A e.1, ∃ b ∈ A e.2, game.constraint e.1 e.2 a = b

instance (game : NonBipartiteUniqueGame X k) (A : X → Finset (Fin k)) (e : X × X) :
    Decidable (game.edgeTSatisfiedBy A e) :=
  inferInstanceAs (Decidable (∃ a ∈ A e.1, ∃ b ∈ A e.2, game.constraint e.1 e.2 a = b))

def IsTAssignment (A : X → Finset (Fin k)) (X' : Finset X) (t : ℕ) : Prop :=
  ∀ x ∈ X', (A x).card = t

noncomputable def NonBipartiteUniqueGame.fractionTSatisfiedWithin
    (game : NonBipartiteUniqueGame X k) (X' : Finset X)
    (A : X → Finset (Fin k)) : ℝ :=
  ((game.edgesWithin X').filter (fun e => game.edgeTSatisfiedBy A e)).card /
    (game.edgesWithin X').card

def StrongUGC_YES (game : NonBipartiteUniqueGame X k) (ε : ℝ) : Prop :=
  ∃ X' : Finset X,
    (X'.card : ℝ) ≥ (1 - ε) * ((Finset.univ : Finset X).card : ℝ) ∧
    ∃ A : X → Fin k, ∀ e ∈ game.edgesWithin X', game.edgeSatisfiedBy A e

def StrongUGC_NO (game : NonBipartiteUniqueGame X k) (ε : ℝ) (t : ℕ) : Prop :=
  ∀ X' : Finset X,
    (X'.card : ℝ) ≥ ε * ((Finset.univ : Finset X).card : ℝ) →
    ∀ A : X → Finset (Fin k), IsTAssignment A X' t →
      ∃ e ∈ game.edgesWithin X', ¬ game.edgeTSatisfiedBy A e

opaque IsPolyTimeNonBipartiteUGReduction {numX : ℕ → ℕ} {k : ℕ} :
  (∀ (m : ℕ), PCP.BinaryString m → NonBipartiteUniqueGame (Fin (numX m)) k) → Prop

def StrongUGC : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ k t : ℕ, ∀ (L : PCP.Language), PCP.InNP L →
      ∃ (numX : ℕ → ℕ) (reduce : ∀ (m : ℕ), PCP.BinaryString m → NonBipartiteUniqueGame (Fin (numX m)) k),
        IsPolyTimeNonBipartiteUGReduction reduce ∧
        (∀ (m : ℕ) (x : PCP.BinaryString m), x ∈ L m →
          StrongUGC_YES (reduce m x) ε) ∧
        (∀ (m : ℕ) (x : PCP.BinaryString m), x ∉ L m →
          StrongUGC_NO (reduce m x) ε t)

structure LabelCover (V : Type*) (W : Type*) (k l : ℕ) where
  edges : Finset (V × W)
  constraint : V → W → (Fin l → Fin k)

structure LabelCover.Labeling (V : Type*) (W : Type*) (k l : ℕ) where
  labelV : V → Fin k
  labelW : W → Fin l

def LabelCover.edgeSatisfied {V : Type*} {W : Type*} {k l : ℕ}
    (game : LabelCover V W k l) (labeling : LabelCover.Labeling V W k l)
    (v : V) (w : W) : Prop :=
  game.constraint v w (labeling.labelW w) = labeling.labelV v

instance {V : Type*} {W : Type*} {k l : ℕ}
    (game : LabelCover V W k l) (labeling : LabelCover.Labeling V W k l)
    (v : V) (w : W) :
    Decidable (game.edgeSatisfied labeling v w) :=
  inferInstanceAs (Decidable (_ = _))

def LabelCover.numSatisfiedEdges {V : Type*} {W : Type*} {k l : ℕ}
    [DecidableEq V] [DecidableEq W]
    (game : LabelCover V W k l) (labeling : LabelCover.Labeling V W k l) : ℕ :=
  (game.edges.filter (fun p => game.edgeSatisfied labeling p.1 p.2)).card

noncomputable def LabelCover.fractionSatisfied {V : Type*} {W : Type*} {k l : ℕ}
    [DecidableEq V] [DecidableEq W]
    (game : LabelCover V W k l) (labeling : LabelCover.Labeling V W k l) : ℝ :=
  (game.numSatisfiedEdges labeling : ℝ) / (game.edges.card : ℝ)

noncomputable def LabelCover.value {V : Type*} {W : Type*} {k l : ℕ}
    [DecidableEq V] [DecidableEq W]
    (game : LabelCover V W k l) : ℝ :=
  iSup (fun labeling : LabelCover.Labeling V W k l => game.fractionSatisfied labeling)

def LabelCover.IsUnique {V : Type*} {W : Type*} {k l : ℕ}
    (game : LabelCover V W k l) : Prop :=
  k = l ∧ ∀ v w, (⟨v, w⟩ : V × W) ∈ game.edges →
    Function.Bijective (game.constraint v w)

lemma fractionSatisfied_le_one {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGame V W k) (labeling : Labeling V W k) :
    fractionSatisfied game labeling ≤ 1 := by
  unfold fractionSatisfied numSatisfiedEdges numEdges
  by_cases h : (game.edges.card : ℝ) = 0
  · simp [h]
  · rw [div_le_one (by positivity : (0 : ℝ) < (game.edges.card : ℝ))]
    exact_mod_cast Finset.card_filter_le _ _

lemma bddAbove_fractionSatisfied {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGame V W k) :
    BddAbove (Set.range (fun labeling : Labeling V W k => fractionSatisfied game labeling)) :=
  ⟨1, fun _ ⟨lab, hlab⟩ => hlab ▸ fractionSatisfied_le_one game lab⟩

lemma fractionSatisfied_le_value {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGame V W k) (labeling : Labeling V W k) :
    fractionSatisfied game labeling ≤ value game :=
  le_ciSup (bddAbove_fractionSatisfied game) labeling

lemma fractionSatisfied_le_of_value_le {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W]
    {k : ℕ} (game : UniqueGame V W k) (δ : ℝ) (hval : value game ≤ δ)
    (labeling : Labeling V W k) :
    fractionSatisfied game labeling ≤ δ :=
  le_trans (fractionSatisfied_le_value game labeling) hval

end UniqueGames


theorem uniqueGamesConjecture :
  ∀ ε δ : ℝ, ε > 0 → δ > 0 → ∃ k : ℕ, UniqueGames.IsNPHardGapUniqueGame k (1 - ε) δ := by sorry

namespace MaxCut

open Finset

structure MaxCutInstance (V : Type*) [Fintype V] [DecidableEq V] where
  edges : Finset (V × V)
  symm : ∀ e ∈ edges, (e.2, e.1) ∈ edges

def numCutEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : MaxCutInstance V) (f : V → Bool) : ℕ :=
  (G.edges.filter (fun e => f e.1 ≠ f e.2)).card

noncomputable def cutFraction {V : Type*} [Fintype V] [DecidableEq V]
    (G : MaxCutInstance V) (f : V → Bool) : ℝ :=
  (numCutEdges G f : ℝ) / (G.edges.card : ℝ)

noncomputable def value {V : Type*} [Fintype V] [DecidableEq V]
    (G : MaxCutInstance V) : ℝ :=
  iSup (fun f : V → Bool => cutFraction G f)

noncomputable def goemansWilliamsonConstant : ℝ :=
  ⨅ θ ∈ Set.Ioo (0 : ℝ) Real.pi, (2 / Real.pi) * θ / (1 - Real.cos θ)

def IsPolyTimeMaxCutInstanceReduction {numVerts : ℕ → ℕ}
    (_ : ∀ (m : ℕ), PCP.BinaryString m → MaxCutInstance (Fin (numVerts m))) : Prop :=
  ∃ (steps : ℕ → ℕ), PCP.IsPolynomial steps ∧ ∀ (m : ℕ), numVerts m ≤ steps m

def IsNPHardGapMaxCut (c s : ℝ) : Prop :=
  ∀ (L : PCP.Language), PCP.InNP L →
    ∃ (numVerts : ℕ → ℕ) (reduce : ∀ (m : ℕ), PCP.BinaryString m → MaxCutInstance (Fin (numVerts m))),
      PCP.IsPolynomial numVerts ∧
      IsPolyTimeMaxCutInstanceReduction reduce ∧
      (∀ (m : ℕ) (x : PCP.BinaryString m), x ∈ L m → value (reduce m x) ≥ c) ∧
      (∀ (m : ℕ) (x : PCP.BinaryString m), x ∉ L m → value (reduce m x) ≤ s)

end MaxCut

opaque IsPolyTimeLongCodeReduction {numV numW k numVerts : ℕ} :
    (UniqueGames.UniqueGame (Fin numV) (Fin numW) k → MaxCut.MaxCutInstance (Fin numVerts)) → Prop


theorem isPolyTimeMaxCutReduction_of_compose {numV numW : ℕ → ℕ} {k : ℕ}
    {numVerts : ℕ → ℕ}
    (ugReduce : ∀ m, PCP.BinaryString m → UniqueGames.UniqueGame (Fin (numV m)) (Fin (numW m)) k)
    (mcReduce : ∀ m, UniqueGames.UniqueGame (Fin (numV m)) (Fin (numW m)) k →
      MaxCut.MaxCutInstance (Fin (numVerts m)))
    (hUG : UniqueGames.IsPolyTimeUniqueGameReduction ugReduce)
    (hMC : ∀ m, IsPolyTimeLongCodeReduction (mcReduce m)) :
    PCP.IsPolynomial numVerts ∧
    MaxCut.IsPolyTimeMaxCutInstanceReduction (fun m x => mcReduce m (ugReduce m x)) := by sorry


noncomputable def maxBalancedNoiseStab (ρ : ℝ) (δ : ℝ) (k : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ (f : (Fin k → Bool) → ℝ),
    (∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) ∧
    (∀ i : Fin k, (1 / (2 : ℝ) ^ k) *
      ∑ x : Fin k → Bool, (f x - f (Function.update x i (!x i))) ^ 2 / 4 ≤ δ) ∧
    ((1 / (2 : ℝ) ^ k) * ∑ x : Fin k → Bool, f x = 0) ∧
    s = (1 / (2 : ℝ) ^ k) * ∑ x : Fin k → Bool, f x *
      ((1 / (2 : ℝ) ^ k) * ∑ y : Fin k → Bool,
        (∏ i : Fin k, if x i = y i then 1 else ρ) * f y)}


noncomputable def longCodeReduce (_ρ : ℝ) (k numV numW : ℕ) :
    UniqueGames.UniqueGame (Fin numV) (Fin numW) k →
    MaxCut.MaxCutInstance (Fin (Fintype.card (Fin numV × (Fin k → Bool)))) := by
  classical
  intro game
  let VType := Fin numV × (Fin k → Bool)
  let eqv : VType ≃ Fin (Fintype.card VType) := Fintype.equivFin VType


  let fwd : Finset (Fin (Fintype.card VType) × Fin (Fintype.card VType)) :=
    game.edges.biUnion fun vw₁ =>
      game.edges.biUnion fun vw₂ =>
        if h : vw₁.2 = vw₂.2 then

          let σ : Equiv.Perm (Fin k) :=
            (game.constraint vw₂.1 vw₂.2).symm.trans (game.constraint vw₁.1 vw₁.2)
          (Finset.univ : Finset (Fin k → Bool)).image fun x =>
            (eqv (vw₁.1, x), eqv (vw₂.1, fun i => !(x (σ.symm i))))
        else ∅
  let bwd := fwd.image (fun p => (p.2, p.1))
  exact ⟨fwd ∪ bwd, by
    intro e he
    simp only [Finset.mem_union] at he ⊢
    rcases he with h | h
    · right; exact Finset.mem_image.mpr ⟨e, h, rfl⟩
    · left
      obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp h
      have heq : e = (p.2, p.1) := hpe.symm
      subst heq; exact hp⟩

theorem longCode_completeness (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1)
    (k numV numW : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (game : UniqueGames.UniqueGame (Fin numV) (Fin numW) k)
    (hgame : UniqueGames.value game ≥ 1 - δ) :
    MaxCut.value (longCodeReduce ρ k numV numW game) ≥ (1 - δ) * (1 + ρ) / 2 := by sorry

theorem high_influence_gives_good_labeling (k numV numW : ℕ) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (game : UniqueGames.UniqueGame (Fin numV) (Fin numW) k)
    (f : Fin numV × (Fin k → Bool) → Bool)
    (v : Fin numV) (i : Fin k)
    (h_high_inf : (1 / (2 : ℝ) ^ k) * ∑ x : Fin k → Bool,
        ((if f (v, x) then (1 : ℝ) else -1) -
         (if f (v, Function.update x i (!x i)) then (1 : ℝ) else -1)) ^ 2 / 4 > δ) :
    ∃ lab : UniqueGames.Labeling (Fin numV) (Fin numW) k,
      UniqueGames.fractionSatisfied game lab > δ := by sorry

theorem longCode_soundness (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1)
    (k numV numW : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (game : UniqueGames.UniqueGame (Fin numV) (Fin numW) k)
    (hgame : UniqueGames.value game ≤ δ) :
    MaxCut.value (longCodeReduce ρ k numV numW game) ≤ (1 + maxBalancedNoiseStab ρ δ k) / 2 := by sorry


theorem longCodeReduce_isPolyTime (ρ : ℝ) (k numV numW : ℕ) :
    IsPolyTimeLongCodeReduction (longCodeReduce ρ k numV numW) := by sorry

theorem longCode_construction_exists (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1)
    (k numV numW : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    ∃ (numVerts : ℕ)
      (reduce : UniqueGames.UniqueGame (Fin numV) (Fin numW) k →
        MaxCut.MaxCutInstance (Fin numVerts)),
      IsPolyTimeLongCodeReduction reduce ∧
      (∀ game, UniqueGames.value game ≥ 1 - δ →
        MaxCut.value (reduce game) ≥ (1 - δ) * (1 + ρ) / 2) ∧
      (∀ game, UniqueGames.value game ≤ δ →
        MaxCut.value (reduce game) ≤ (1 + maxBalancedNoiseStab ρ δ k) / 2) :=
  ⟨_, longCodeReduce ρ k numV numW, longCodeReduce_isPolyTime ρ k numV numW,
   fun game hg => longCode_completeness ρ hρ_pos hρ_lt k numV numW δ hδ_pos hδ_lt game hg,
   fun game hg => longCode_soundness ρ hρ_pos hρ_lt k numV numW δ hδ_pos hδ_lt game hg⟩


theorem longCode_MIS_stabBound (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1)
    (ε' : ℝ) (hε' : ε' > 0) :
    ∃ δ_MIS > 0, ∀ (k : ℕ) (δ : ℝ), 0 < δ → δ ≤ δ_MIS → δ < 1 →
      maxBalancedNoiseStab ρ δ k ≤ 1 - (2 / Real.pi) * Real.arccos ρ + ε' := by

  obtain ⟨δ_MIS, hδ_MIS_pos, hMIS⟩ := mis_combinatorial_bound ρ hρ_pos hρ_lt ε' hε'
  refine ⟨δ_MIS, hδ_MIS_pos, fun k δ hδ_pos hδ_le hδ_lt => ?_⟩

  unfold maxBalancedNoiseStab
  set S := {s : ℝ | ∃ (f : (Fin k → Bool) → ℝ),
    (∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) ∧
    (∀ i : Fin k, (1 / (2 : ℝ) ^ k) *
      ∑ x : Fin k → Bool, (f x - f (Function.update x i (!x i))) ^ 2 / 4 ≤ δ) ∧
    ((1 / (2 : ℝ) ^ k) * ∑ x : Fin k → Bool, f x = 0) ∧
    s = (1 / (2 : ℝ) ^ k) * ∑ x : Fin k → Bool, f x *
      ((1 / (2 : ℝ) ^ k) * ∑ y : Fin k → Bool,
        (∏ i : Fin k, if x i = y i then 1 else ρ) * f y)}
  by_cases hne : S.Nonempty
  ·
    apply csSup_le hne
    intro s hs
    obtain ⟨f, hbnd, hinf, hbal, hs_eq⟩ := hs
    rw [hs_eq]

    have hinf_MIS : ∀ i : Fin k, (1 / (2 : ℝ) ^ k) *
        ∑ x : Fin k → Bool, (f x - f (Function.update x i (!x i))) ^ 2 / 4 ≤ δ_MIS := fun i =>
      le_trans (hinf i) hδ_le
    exact hMIS k f hbnd hinf_MIS hbal
  ·
    have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty, Real.sSup_empty]
    have harccos_lt : Real.arccos ρ < Real.pi / 2 :=
      Real.arccos_lt_pi_div_two.mpr hρ_pos
    have h_frac : 2 / Real.pi * Real.arccos ρ < 1 := by
      have h1 : 2 / Real.pi * Real.arccos ρ < 2 / Real.pi * (Real.pi / 2) :=
        mul_lt_mul_of_pos_left harccos_lt (by positivity)
      linarith [show 2 / Real.pi * (Real.pi / 2) = 1 from by field_simp]
    linarith

theorem longCodeTest_bounds (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1)
    (ε : ℝ) (hε : ε > 0) :
    ∃ δ₀ > 0, ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ → δ < 1 → ∀ (k numV numW : ℕ),
      ∃ (numVerts : ℕ)
        (reduce : UniqueGames.UniqueGame (Fin numV) (Fin numW) k →
          MaxCut.MaxCutInstance (Fin numVerts)),
        IsPolyTimeLongCodeReduction reduce ∧
        (∀ game, UniqueGames.value game ≥ 1 - δ →
          MaxCut.value (reduce game) ≥ (1 - δ) * (1 + ρ) / 2) ∧
        (∀ game, UniqueGames.value game ≤ δ →
          MaxCut.value (reduce game) ≤ 1 - (1 / Real.pi) * Real.arccos ρ + ε) := by

  have hε2 : (0 : ℝ) < 2 * ε := by linarith
  obtain ⟨δ_MIS, hδ_MIS_pos, hMIS⟩ := longCode_MIS_stabBound ρ hρ_pos hρ_lt (2 * ε) hε2

  refine ⟨δ_MIS, hδ_MIS_pos, fun δ hδ_pos hδ_le hδ_lt k numV numW => ?_⟩

  obtain ⟨numVerts, reduce, hPolyTime, hComplete, hSoundRaw⟩ :=
    longCode_construction_exists ρ hρ_pos hρ_lt k numV numW δ hδ_pos hδ_lt
  refine ⟨numVerts, reduce, hPolyTime, hComplete, fun game hGame => ?_⟩

  have hMISbound := hMIS k δ hδ_pos hδ_le hδ_lt

  have hSoundGame := hSoundRaw game hGame


  have harith : (1 + (1 - 2 / Real.pi * Real.arccos ρ + 2 * ε)) / 2 =
      1 - (1 / Real.pi) * Real.arccos ρ + ε := by ring
  linarith

theorem longCodeReduction_maxcut (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1)
    (ε : ℝ) (hε : ε > 0) :
    ∃ δ > 0, ∀ (k numV numW : ℕ),
      ∃ (numVerts : ℕ)
        (reduce : UniqueGames.UniqueGame (Fin numV) (Fin numW) k →
          MaxCut.MaxCutInstance (Fin numVerts)),
        IsPolyTimeLongCodeReduction reduce ∧
        (∀ game, UniqueGames.value game ≥ 1 - δ →
          MaxCut.value (reduce game) ≥ 1/2 + ρ/2 - ε) ∧
        (∀ game, UniqueGames.value game ≤ δ →
          MaxCut.value (reduce game) ≤ 1 - (1 / Real.pi) * Real.arccos ρ + ε) := by

  obtain ⟨δ₀, hδ₀_pos, hBounds⟩ := longCodeTest_bounds ρ hρ_pos hρ_lt ε hε

  have hρ_sum : (1 : ℝ) + ρ > 0 := by linarith
  set δ := min δ₀ (min (2 * ε / (1 + ρ)) (1/2)) with hδ_def
  have hδ_pos : δ > 0 := by
    simp only [δ]
    exact lt_min hδ₀_pos (lt_min (by positivity) (by norm_num))
  have hδ_le_δ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδ_le_eps : δ ≤ 2 * ε / (1 + ρ) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_lt_one : δ < 1 :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by norm_num)

  have hComplete_arith : (1 - δ) * (1 + ρ) / 2 ≥ 1/2 + ρ/2 - ε := by
    have h1 : δ * (1 + ρ) ≤ 2 * ε := by
      have := mul_le_mul_of_nonneg_right hδ_le_eps (le_of_lt hρ_sum)
      rwa [div_mul_cancel₀] at this
      linarith
    nlinarith
  refine ⟨δ, hδ_pos, fun k numV numW => ?_⟩

  obtain ⟨numVerts, reduce, hPolyTime, hComplete_raw, hSound⟩ :=
    hBounds δ hδ_pos hδ_le_δ₀ hδ_lt_one k numV numW

  refine ⟨numVerts, reduce, hPolyTime, fun game hGame => ?_, hSound⟩

  calc MaxCut.value (reduce game)
      ≥ (1 - δ) * (1 + ρ) / 2 := hComplete_raw game hGame
    _ ≥ 1/2 + ρ/2 - ε := hComplete_arith


theorem ug_hardness_maxcut :
    (∀ ε δ : ℝ, ε > 0 → δ > 0 → ∃ k : ℕ, UniqueGames.IsNPHardGapUniqueGame k (1 - ε) δ) →
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ ε : ℝ, ε > 0 →
      MaxCut.IsNPHardGapMaxCut (1/2 + ρ/2 - ε) (1 - (1 / Real.pi) * Real.arccos ρ + ε) := by
  intro hUGC ρ hρ_pos hρ_lt ε hε

  obtain ⟨δ, hδ_pos, hLongCode⟩ := longCodeReduction_maxcut ρ hρ_pos hρ_lt ε hε

  obtain ⟨k, hGapUG⟩ := hUGC δ δ hδ_pos hδ_pos

  intro L hNP

  obtain ⟨numV, numW, ugReduce, hPolyUG, hCompleteUG, hSoundUG⟩ := hGapUG L hNP


  have hLC := fun m => hLongCode k (numV m) (numW m)

  let numVertsF : ℕ → ℕ := fun m => (hLC m).choose
  let mcReduceF : ∀ m, UniqueGames.UniqueGame (Fin (numV m)) (Fin (numW m)) k →
      MaxCut.MaxCutInstance (Fin (numVertsF m)) :=
    fun m => (hLC m).choose_spec.choose
  have hMCprops : ∀ m,
      IsPolyTimeLongCodeReduction (mcReduceF m) ∧
      (∀ game, UniqueGames.value game ≥ 1 - δ →
        MaxCut.value (mcReduceF m game) ≥ 1/2 + ρ/2 - ε) ∧
      (∀ game, UniqueGames.value game ≤ δ →
        MaxCut.value (mcReduceF m game) ≤ 1 - (1 / Real.pi) * Real.arccos ρ + ε) :=
    fun m => (hLC m).choose_spec.choose_spec

  have hCompose := isPolyTimeMaxCutReduction_of_compose ugReduce mcReduceF hPolyUG
      (fun m => (hMCprops m).1)
  refine ⟨numVertsF, fun m x => mcReduceF m (ugReduce m x), hCompose.1, hCompose.2, ?_, ?_⟩

  · intro m x hx
    exact (hMCprops m).2.1 (ugReduce m x) (hCompleteUG m x hx)

  · intro m x hx
    exact (hMCprops m).2.2 (ugReduce m x) (hSoundUG m x hx)


theorem ug_hardness_maxcut_of_ugc
    (hUGC : ∀ ε δ : ℝ, ε > 0 → δ > 0 → ∃ k : ℕ, UniqueGames.IsNPHardGapUniqueGame k (1 - ε) δ) :
  ∀ ε : ℝ, ε > 0 → MaxCut.IsNPHardGapMaxCut (1 - ε) (MaxCut.goemansWilliamsonConstant + ε) := by sorry
