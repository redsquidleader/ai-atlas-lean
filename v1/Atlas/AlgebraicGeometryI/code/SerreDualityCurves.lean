/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves
import Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Atlas.AlgebraicGeometryI.code.SerreDualityLinear
import Atlas.AlgebraicGeometryI.code.SerreDualityGeneral
import Atlas.AlgebraicGeometryI.code.ResidueSum
import Atlas.AlgebraicGeometryI.code.DedekindCurve

noncomputable section

namespace SerreDualityCurves

open CanonicalSheafCurves RiemannRochCurves SerreDualityP1
open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology


section ResidueMap

variable (k : Type*) [Field k]

/-- The residue map `(ℤ →₀ k) →ₗ[k] k` sending a Laurent polynomial to its
coefficient at index `-1`. -/
def residueMap : (ℤ →₀ k) →ₗ[k] k where
  toFun f := f (-1)
  map_add' f g := Finsupp.add_apply f g (-1)
  map_smul' c f := Finsupp.smul_apply c f (-1)

/-- Unfolds `residueMap` to the coefficient at index `-1`. -/
@[simp]
theorem residueMap_apply (f : ℤ →₀ k) : residueMap k f = f (-1) := rfl

/-- The residue of a single-term Laurent polynomial concentrated at index `-1` is its coefficient. -/
theorem residueMap_single_neg_one (a : k) :
    residueMap k (Finsupp.single (-1 : ℤ) a) = a :=
  Finsupp.single_eq_same

/-- Single-term Laurent polynomials concentrated at any index other than `-1`
have residue zero. -/
theorem residueMap_single_ne (n : ℤ) (hn : n ≠ -1) (a : k) :
    residueMap k (Finsupp.single n a) = 0 :=
  Finsupp.single_eq_of_ne (Ne.symm hn)

end ResidueMap


section ExactForms

variable (k : Type*) [Field k]

/-- Coefficient of the formal derivative: `(d/dz f)(m) = (m+1) · f(m+1)`. -/
def derivCoeff (f : ℤ →₀ k) (m : ℤ) : k :=
  (↑(m + 1) : k) * f (m + 1)

/-- The `(-1)`-coefficient of a formal derivative vanishes (the prefactor `0 · f(0)` is zero). -/
theorem derivCoeff_neg_one (f : ℤ →₀ k) :
    derivCoeff k f (-1) = 0 := by
  simp [derivCoeff]

/-- The residue of an exact differential `d(a · z^n) = n · a · z^{n-1}` vanishes. -/
theorem residue_of_exact_zero (n : ℤ) (a : k) :
    residueMap k (Finsupp.single (n - 1) ((↑n : k) * a)) = 0 := by
  by_cases h : n - 1 = -1
  ·
    have hn : n = 0 := by omega
    subst hn; simp
  ·
    exact residueMap_single_ne k (n - 1) h ((↑n : k) * a)

/-- The residue annihilates exact forms: formal derivatives have vanishing `-1`-coefficient. -/
theorem residue_annihilates_derivs (f : ℤ →₀ k) :
    derivCoeff k f (-1) = 0 :=
  derivCoeff_neg_one k f

end ExactForms


section ResiduePairing

variable (k : Type*) [Field k]

/-- The residue pairing `⟨f, g⟩ = ∑ i f(i) · g(-1 - i)`, which extracts
the `-1`-coefficient of the convolution product. -/
def residuePairing (f g : ℤ →₀ k) : k :=
  ∑ i ∈ f.support, f i * g (-1 - i)

/-- The residue pairing on single-term Laurent polynomials: equals `a · b`
when `i + j = -1` and `0` otherwise. -/
theorem residuePairing_single (i j : ℤ) (a b : k) :
    residuePairing k (Finsupp.single i a) (Finsupp.single j b) =
    if i + j = -1 then a * b else 0 := by
  unfold residuePairing
  by_cases ha : a = 0
  · simp [ha, Finsupp.single_zero, Finsupp.support_zero]
  · rw [Finsupp.support_single_ne_zero _ ha, Finset.sum_singleton, Finsupp.single_eq_same]
    by_cases hij : i + j = -1
    · have hj : j = -1 - i := by omega
      simp only [hij, ↓reduceIte]
      rw [hj, show (Finsupp.single (-1 - i) b : ℤ →₀ k) (-1 - i) = b from
        Finsupp.single_eq_same]
    · simp only [hij, ↓reduceIte]
      have hne : (-1 - i : ℤ) ≠ j := by omega
      rw [show (Finsupp.single j b : ℤ →₀ k) (-1 - i) = 0 from
        Finsupp.single_eq_of_ne hne]
      ring

/-- Symmetry of the residue pairing on single-term Laurent polynomials. -/
theorem residuePairing_single_comm (i j : ℤ) (a b : k) :
    residuePairing k (Finsupp.single i a) (Finsupp.single j b) =
    residuePairing k (Finsupp.single j b) (Finsupp.single i a) := by
  rw [residuePairing_single, residuePairing_single]
  by_cases h : i + j = -1
  · have : j + i = -1 := by linarith
    simp [h, this, mul_comm]
  · have : j + i ≠ -1 := by omega
    simp [h, this]

end ResiduePairing


section GeneralCurves

/-- Rank-1 Euler-characteristic form of Serre duality on a smooth complete curve:
`χ(O(d)) + χ(O(K - d)) = 0`. -/
theorem serre_duality_chi_rank1 (C : SmoothCompleteCurve) (d : ℤ) :
    C.χ (1, d) + C.χ (1, C.degK - d) = 0 := by
  rw [chi_eq_rr C 1 d, chi_eq_rr C 1 (C.degK - d)]
  have hK := deg_canonical_eq_2g_sub_2 C
  linarith

/-- Serre duality applied to `O ↔ K`: `χ(O) + χ(K) = 0`. -/
theorem serre_duality_chi_O_K (C : SmoothCompleteCurve) :
    C.χ (1, 0) + C.χ (1, C.degK) = 0 := by
  have := serre_duality_chi_rank1 C 0
  simp at this
  exact this

/-- General rank-`r` Euler-characteristic form of Serre duality on a smooth
complete curve: `χ(E) + χ(E∨ ⊗ K) = 0` numerically. -/
theorem serre_duality_chi_rank_r (C : SmoothCompleteCurve) (r d : ℤ) :
    C.χ (r, d) + C.χ (r, r * C.degK - d) = 0 := by
  rw [chi_eq_rr C r d, chi_eq_rr C r (r * C.degK - d)]
  have hK := deg_canonical_eq_2g_sub_2 C
  rw [hK]; ring

/-- Numerical Serre duality from the χ-identity: given Riemann–Roch and the
duality `h⁰(E) = h¹(E∨ ⊗ K)`, conclude `h¹(E) = h⁰(E∨ ⊗ K)`. -/
theorem serre_duality_numerical_from_chi (C : SmoothCompleteCurve)
    (d h0E h1E h0EK h1EK : ℤ)
    (hRR_E : h0E - h1E = C.χ (1, d))
    (hRR_EK : h0EK - h1EK = C.χ (1, C.degK - d))
    (hSD : h0E = h1EK) :
    h1E = h0EK := by
  have hsum := serre_duality_chi_rank1 C d
  linarith

end GeneralCurves


section LocallyFreeSheaf

/-- Numerical model of a locally free sheaf on a curve `C`: tracks rank and degree. -/
@[ext]
structure LocallyFreeSheaf (C : SmoothCompleteCurve) where
  rk : ℕ
  deg : ℤ


/-- The K-theory class of a locally free sheaf is the pair `(rank, degree) ∈ ℤ × ℤ`. -/
def LocallyFreeSheaf.K0class {C : SmoothCompleteCurve}
    (E : LocallyFreeSheaf C) : ℤ × ℤ := (↑E.rk, E.deg)

/-- The Euler characteristic `χ(E) = h⁰(E) - h¹(E)` of a locally free sheaf,
computed from its rank and degree via Riemann–Roch. -/
def LocallyFreeSheaf.chi {C : SmoothCompleteCurve}
    (E : LocallyFreeSheaf C) : ℤ := C.χ E.K0class

/-- The Serre dual `E∨ ⊗ K` at the level of `(rank, degree)`: same rank,
degree replaced by `rank · deg K − deg E`. -/
def LocallyFreeSheaf.serreDual {C : SmoothCompleteCurve}
    (E : LocallyFreeSheaf C) : LocallyFreeSheaf C where
  rk := E.rk
  deg := ↑E.rk * C.degK - E.deg

/-- Unfolds the degree of the Serre dual. -/
theorem LocallyFreeSheaf.serreDual_deg {C : SmoothCompleteCurve}
    (E : LocallyFreeSheaf C) :
    E.serreDual.deg = ↑E.rk * C.degK - E.deg := rfl

/-- Serre duality at the level of Euler characteristics: `χ(E) + χ(E∨ ⊗ K) = 0`. -/
theorem LocallyFreeSheaf.serre_duality_chi {C : SmoothCompleteCurve}
    (E : LocallyFreeSheaf C) :
    E.chi + E.serreDual.chi = 0 := by
  show C.χ (↑E.rk, E.deg) + C.χ (↑E.rk, ↑E.rk * C.degK - E.deg) = 0
  exact serre_duality_chi_rank_r C ↑E.rk E.deg

/-- Serre duality is an involution at the numerical level: `(E∨ ⊗ K)∨ ⊗ K = E`. -/
theorem LocallyFreeSheaf.serreDual_serreDual {C : SmoothCompleteCurve}
    (E : LocallyFreeSheaf C) :
    E.serreDual.serreDual = E := by
  ext <;> simp [serreDual]

/-- The line bundle of a given degree. -/
def LocallyFreeSheaf.ofIdeal (C : SmoothCompleteCurve) (deg : ℤ) :
    LocallyFreeSheaf C where
  rk := 1
  deg := deg

/-- The structure sheaf `O_C` as a locally free sheaf of rank `1` and degree `0`. -/
def LocallyFreeSheaf.structureSheaf (C : SmoothCompleteCurve) :
    LocallyFreeSheaf C where
  rk := 1
  deg := 0

/-- The canonical bundle `K_C` as a locally free sheaf of rank `1` and degree `deg K`. -/
def LocallyFreeSheaf.canonical (C : SmoothCompleteCurve) :
    LocallyFreeSheaf C where
  rk := 1
  deg := C.degK

/-- Standalone alias for the structure sheaf of `C`. -/
def structureSheaf (C : SmoothCompleteCurve) : LocallyFreeSheaf C where
  rk := 1
  deg := 0

/-- Standalone alias for the canonical sheaf of `C`. -/
def canonicalSheaf (C : SmoothCompleteCurve) : LocallyFreeSheaf C where
  rk := 1
  deg := C.degK

/-- The Serre dual of `O_C` is `K_C` numerically. -/
theorem structureSheaf_serreDual (C : SmoothCompleteCurve) :
    (structureSheaf C).serreDual = canonicalSheaf C := by
  ext <;> simp [structureSheaf, canonicalSheaf, LocallyFreeSheaf.serreDual]

/-- Serre duality for `O ↔ K`: `χ(O) + χ(K) = 0`. -/
theorem serre_duality_O_K (C : SmoothCompleteCurve) :
    (structureSheaf C).chi + (canonicalSheaf C).chi = 0 := by
  rw [← structureSheaf_serreDual]
  exact (structureSheaf C).serre_duality_chi

end LocallyFreeSheaf


section P1Verification

open RiemannRoch in
/-- Serre duality on `ℙ¹` at the level of dimensions: `dim H¹(O(n)) = dim H⁰(O(-2 - n))`. -/
theorem serre_duality_P1_dimension (k : Type) [Field k] (n : ℤ) :
    RiemannRoch.dimH1 k n = RiemannRoch.dimH0 k (-2 - n) :=
  RiemannRoch.serre_duality_P1 k n

/-- The projective line `ℙ¹` as a smooth complete curve of genus `0`. -/
def P1Curve : SmoothCompleteCurve := mkCurve 0

/-- `ℙ¹` has genus zero. -/
theorem P1Curve_genus : P1Curve.g = 0 := rfl

/-- The degree of the canonical divisor on `ℙ¹` is `-2`. -/
theorem P1Curve_degK : P1Curve.degK = -2 := by
  simp [P1Curve, mkCurve]

/-- The line bundle `O_{ℙ¹}(n)` on `ℙ¹` as a numerical locally free sheaf. -/
def O_P1 (n : ℤ) : LocallyFreeSheaf P1Curve where
  rk := 1
  deg := n

/-- The Serre dual of `O_{ℙ¹}(n)` is `O_{ℙ¹}(-2 - n)`. -/
theorem O_P1_serreDual (n : ℤ) : (O_P1 n).serreDual = O_P1 (-2 - n) := by
  ext
  · simp [O_P1, LocallyFreeSheaf.serreDual]
  · simp [O_P1, LocallyFreeSheaf.serreDual, P1Curve_degK]

/-- Numerical Serre duality on `ℙ¹`: `χ(O(n)) + χ(O(-2 - n)) = 0`. -/
theorem chi_O_P1_duality (n : ℤ) :
    (O_P1 n).chi + (O_P1 (-2 - n)).chi = 0 := by
  rw [← O_P1_serreDual]
  exact (O_P1 n).serre_duality_chi

/-- Riemann–Roch on `ℙ¹`: `χ(O(n)) = n + 1`. -/
theorem chi_O_P1 (n : ℤ) : (O_P1 n).chi = n + 1 := by
  show P1Curve.χ (1, n) = n + 1
  rw [chi_eq_rr P1Curve 1 n, P1Curve_genus]
  ring

variable (k : Type) [Field k]

/-- Serre duality on `ℙ¹` (nonempty version): for `n < -1`, the quotient
`(ℤ →₀ k) / (NonNeg ⊔ AtMost n)` is linearly equivalent to `CechH⁰(-2 - n)`. -/
theorem serre_duality_P1_via_shift (n : ℤ) (hn : n < -1) :
    Nonempty (((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) ≃ₗ[k]
      ↥(CechH0 k (-2 - n))) :=
  ⟨SerreDualityP1.serre_duality_P1 k n hn⟩

/-- Serre duality on `ℙ¹` at the dimension level: for `n < -1`,
`dim H¹(O(n)) = dim H⁰(O(-2 - n))`. -/
theorem serre_duality_P1_finrank_eq (n : ℤ) (hn : n < -1) :
    Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) =
    Module.finrank k ↥(CechH0 k (-2 - n)) :=
  SerreDualityP1.serre_duality_finrank k n hn

end P1Verification


section ResidueConnection

variable (k : Type*) [Field k]

/-- The residue pairing of `a · z^i` with `g` equals `a · g(-1 - i)`. -/
theorem residuePairing_via_shift (i : ℤ) (a : k) (g : ℤ →₀ k) :
    residuePairing k (Finsupp.single i a) g = a * g (residueShift i) := by
  unfold residuePairing residueShift
  by_cases ha : a = 0
  · simp [ha, Finsupp.single_zero, Finsupp.support_zero]
  · rw [Finsupp.support_single_ne_zero _ ha, Finset.sum_singleton, Finsupp.single_eq_same]

/-- The shift `i ↦ -1 - i` sends `[0, n]` bijectively onto `[-1 - n, -1]`,
showing the pairing matches degrees of one side with degrees of the dual side. -/
theorem residue_shift_is_pairing_bijection (n : ℤ) :
    residueShift '' (Set.Icc 0 n) = Set.Icc (-1 - n) (-1) := by
  ext x
  simp only [Set.mem_image, Set.mem_Icc, residueShift]
  constructor
  · rintro ⟨y, ⟨hy0, hyn⟩, rfl⟩; constructor <;> omega
  · intro ⟨hx_lb, hx_ub⟩
    exact ⟨-1 - x, ⟨by omega, by omega⟩, by omega⟩

end ResidueConnection


section TheoremStatement

/-- The combined Serre duality and Riemann–Roch statement on a smooth complete curve:
`χ(O(d)) + χ(O(K - d)) = 0` and `χ(O(d)) = d + 1 − g`. -/
theorem serre_duality_theorem (C : SmoothCompleteCurve) (d : ℤ) :
    C.χ (1, d) + C.χ (1, C.degK - d) = 0 ∧
    C.χ (1, d) = d + 1 - C.g :=
  ⟨serre_duality_chi_rank1 C d, by rw [chi_eq_rr C 1 d]; ring⟩

/-- Arithmetic genus equals geometric genus: combining Riemann–Roch for `O` and `K`
with the Serre duality `h⁰(O) = h¹(K)` yields `g_a = g_m`. -/
theorem genus_arithmetic_eq_geometric (C : SmoothCompleteCurve)
    (ga gm h0_O h1_O h0_K h1_K : ℤ)
    (_hh0_O : h0_O = 1)
    (hga : ga = h1_O)
    (hgm : gm = h0_K)
    (hRR_O : h0_O - h1_O = C.χ (1, 0))
    (hRR_K : h0_K - h1_K = C.χ (1, C.degK))
    (hSD : h0_O = h1_K)
    : ga = gm := by
  have hchi := serre_duality_chi C
  linarith

/-- Numerical Serre duality, both directions: assuming `h⁰(E) = h¹(E∨ ⊗ K)`
yields the reverse `h¹(E) = h⁰(E∨ ⊗ K)`. -/
theorem serre_duality_both_directions (C : SmoothCompleteCurve) (d : ℤ)
    (h0_E h1_E h0_EK h1_EK : ℤ)
    (hRR_E : h0_E - h1_E = C.χ (1, d))
    (hRR_EK : h0_EK - h1_EK = C.χ (1, C.degK - d))
    (hSD_0 : h0_E = h1_EK)
    : h1_E = h0_EK := by
  have hchi := serre_duality_chi_rank1 C d
  linarith

end TheoremStatement


section Applications

/-- Riemann–Roch in Serre form: `h⁰(D) − h⁰(K − D) = d + 1 − g`. -/
theorem riemann_roch_serre_form_general (C : SmoothCompleteCurve) (d : ℤ)
    (h0_D h0_KD : ℤ)
    (hRR : h0_D - h0_KD = C.χ (1, d))
    : h0_D - h0_KD = d + 1 - C.g := by
  rw [chi_eq_rr C 1 d] at hRR; linarith

/-- Riemann's inequality: `h⁰(D) ≥ d + 1 − g`, derived from Riemann–Roch
and the non-negativity of `h¹`. -/
theorem riemann_inequality_from_RR (C : SmoothCompleteCurve) (d h0 h1 : ℤ)
    (hh1_nn : h1 ≥ 0)
    (hRR : h0 - h1 = d + 1 - C.g) :
    h0 ≥ d + 1 - C.g := by linarith

/-- The degree of the canonical divisor is `2g - 2`. -/
theorem deg_K_from_serre_duality (C : SmoothCompleteCurve) :
    C.degK = 2 * C.g - 2 :=
  deg_canonical_eq_2g_sub_2 C

end Applications


section DedekindBridge

/-- Rank-1 Serre duality χ-identity transported to a `DedekindCurve`. -/
theorem serre_duality_chi_rank1_dedekind {k : Type*} [Field k]
    (C : DedekindCurve k) (d : ℤ) :
    C.toSmoothCompleteCurve.χ (1, d) +
    C.toSmoothCompleteCurve.χ (1, C.toSmoothCompleteCurve.degK - d) = 0 :=
  serre_duality_chi_rank1 C.toSmoothCompleteCurve d

/-- Rank-`r` Serre duality χ-identity transported to a `DedekindCurve`. -/
theorem serre_duality_chi_rank_r_dedekind {k : Type*} [Field k]
    (C : DedekindCurve k) (r d : ℤ) :
    C.toSmoothCompleteCurve.χ (r, d) +
    C.toSmoothCompleteCurve.χ (r, r * C.toSmoothCompleteCurve.degK - d) = 0 :=
  serre_duality_chi_rank_r C.toSmoothCompleteCurve r d

/-- Serre duality for `O ↔ K` on a `DedekindCurve`. -/
theorem serre_duality_canonical_h0_dedekind {k : Type*} [Field k]
    (C : DedekindCurve k) :
    C.toSmoothCompleteCurve.χ (1, 0) +
    C.toSmoothCompleteCurve.χ (1, C.toSmoothCompleteCurve.degK) = 0 :=
  serre_duality_chi C.toSmoothCompleteCurve

end DedekindBridge

end SerreDualityCurves

end
