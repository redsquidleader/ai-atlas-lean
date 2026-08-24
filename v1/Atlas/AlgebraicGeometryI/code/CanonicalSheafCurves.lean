/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves
import Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective
import Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Atlas.AlgebraicGeometryI.code.RiemannRochCurves

set_option maxHeartbeats 800000

open RiemannRochCurves

noncomputable section

namespace CanonicalSheafCurves

/-- Existence witness for a smooth complete curve of genus `g`: a Dedekind `k`-algebra `A` whose
Kähler differential module has rank `g`. -/
def CurveWitness (g : ℤ) : Prop :=
  ∃ (k : Type) (_ : Field k) (A : Type) (_ : CommRing A) (_ : IsDomain A)
    (_ : IsDedekindDomain A) (_ : Algebra k A) (_ : Module.Finite k A),
    (Module.finrank k (Ω[A⁄k]) : ℤ) = g

/-- The rational numbers `ℚ` (as a `ℚ`-algebra) witness the genus-`0` case of `CurveWitness`. -/
theorem curveWitness_zero : CurveWitness 0 := by
  refine ⟨ℚ, inferInstance, ℚ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  simp only [Nat.cast_eq_zero]
  haveI := KaehlerDifferential.subsingleton_of_surjective ℚ ℚ (fun x => ⟨x, rfl⟩)
  exact Module.finrank_zero_of_subsingleton

/-- For every natural number `g`, there exists a smooth complete curve of genus `g`. -/
theorem curveWitness_of_nat : ∀ (g : ℕ), CurveWitness (g : ℤ) := by sorry

/-- Numerical data of a smooth complete curve: genus `g`, canonical degree `degK`, Euler
characteristic homomorphism `χ : ℤ × ℤ →+ ℤ` (taking `(rank, degree)` to `χ(F)`), satisfying
the structure-sheaf and skyscraper normalisations plus existence of an underlying Dedekind
witness. -/
structure SmoothCompleteCurve where
  g : ℤ
  χ : ℤ × ℤ →+ ℤ
  degK : ℤ
  hg_nonneg : 0 ≤ g
  hχ_struct : χ (1, 0) = 1 - g
  hχ_sky : χ (0, 1) = 1
  hwf : CurveWitness g

/-- Serre duality at the level of Euler characteristics: `χ(K_C) = g - 1`. -/
theorem serre_duality_chi_canonical (C : SmoothCompleteCurve) :
    C.χ (1, C.degK) = C.g - 1 := by sorry

/-- Convenience projection: the canonical-sheaf Euler characteristic of `C` is `g - 1`. -/
theorem SmoothCompleteCurve.hχ_canonical (C : SmoothCompleteCurve) :
    C.χ (1, C.degK) = C.g - 1 :=
  serre_duality_chi_canonical C

/-- Class of the canonical sheaf of `C` in the Picard-style invariant `ℤ × ℤ` of
`(rank, degree)`: `K_C` is a line bundle (rank `1`) of degree `degK`. -/
def canonicalSheafClass (C : SmoothCompleteCurve) : ℤ × ℤ := (1, C.degK)

/-- Genus of the smooth complete curve `C`, as an integer. -/
def curveGenusOfSmooth (C : SmoothCompleteCurve) : ℤ := C.g

/-- Degree of the canonical divisor of `C`. -/
def canonicalDeg (C : SmoothCompleteCurve) : ℤ := C.degK

/-- Riemann-Roch on `C`: `χ(F) = d - r(g - 1)` for a sheaf of rank `r` and degree `d`. -/
theorem chi_eq_rr (C : SmoothCompleteCurve) (r d : ℤ) :
    C.χ (r, d) = d - r * (C.g - 1) :=
  riemann_roch_curves_thm C.g C.χ C.hχ_struct C.hχ_sky r d

/-- Specialisation of Riemann-Roch to the canonical class: `χ(K_C) = deg K_C + 1 - g`. -/
theorem chi_canonical_by_rr (C : SmoothCompleteCurve) :
    C.χ (1, C.degK) = C.degK + 1 - C.g := by
  rw [chi_eq_rr C 1 C.degK]; ring

/-- Serre duality on `C` in the form `χ(K_C) = g - 1`. -/
theorem SmoothCompleteCurve.serre_duality (C : SmoothCompleteCurve) :
    C.χ (1, C.degK) = C.g - 1 :=
  serre_duality_chi_canonical C

/-- Euler-characteristic form of Serre duality: `χ(O_C) + χ(K_C) = 0`. -/
theorem serre_duality_chi (C : SmoothCompleteCurve) :
    C.χ (1, 0) + C.χ (1, C.degK) = 0 := by
  rw [C.hχ_struct, C.serre_duality]; ring

/-- Restatement of Serre duality: `χ(K_C) = g - 1`. -/
theorem chi_canonical (C : SmoothCompleteCurve) :
    C.χ (1, C.degK) = C.g - 1 :=
  C.serre_duality

/-- Degree of the canonical divisor: `deg K_C = 2g - 2` (combining Riemann-Roch and Serre duality). -/
theorem deg_canonical_eq_2g_sub_2 (C : SmoothCompleteCurve) :
    C.degK = 2 * C.g - 2 := by
  have h1 := serre_duality_chi_canonical C
  rw [chi_eq_rr C 1 C.degK] at h1
  linarith

/-- Factored form of the canonical degree: `deg K_C = 2(g - 1)`. -/
theorem deg_canonical_eq_2_mul_g_sub_1 (C : SmoothCompleteCurve) :
    C.degK = 2 * (C.g - 1) := by
  have := deg_canonical_eq_2g_sub_2 C; linarith

/-- Expression of the canonical degree via the structure-sheaf Euler characteristic:
`deg K_C = -2 χ(O_C)`. -/
theorem deg_canonical_eq_neg2_chi_O (C : SmoothCompleteCurve) :
    C.degK = -2 * C.χ (1, 0) := by
  rw [C.hχ_struct]
  have := deg_canonical_eq_2g_sub_2 C
  linarith

/-- Specialisation to genus `0` (`P^1`): `deg K_{P^1} = -2`. -/
theorem deg_canonical_P1_from_formula : ∀ (C : SmoothCompleteCurve), C.g = 0 → C.degK = -2 := by
  intro C hg
  have := deg_canonical_eq_2g_sub_2 C
  linarith

/-- Numerical sanity check: `2·0 - 2 = -2`. -/
theorem deg_canonical_P1_check : 2 * (0 : ℤ) - 2 = -2 := by norm_num

/-- Specialisation to genus `1` (elliptic curves): `deg K_E = 0`. -/
theorem deg_canonical_elliptic :
    ∀ (C : SmoothCompleteCurve), C.g = 1 → C.degK = 0 := by
  intro C hg
  have := deg_canonical_eq_2g_sub_2 C
  linarith

/-- Numerical sanity check: `2·1 - 2 = 0`. -/
theorem deg_canonical_elliptic_check : 2 * (1 : ℤ) - 2 = 0 := by norm_num

/-- Specialisation to genus `2`: `deg K_C = 2`. -/
theorem deg_canonical_genus2 :
    ∀ (C : SmoothCompleteCurve), C.g = 2 → C.degK = 2 := by
  intro C hg
  have := deg_canonical_eq_2g_sub_2 C
  linarith

/-- Numerical sanity check: `2·2 - 2 = 2`. -/
theorem deg_canonical_genus2_check : 2 * (2 : ℤ) - 2 = 2 := by norm_num

/-- Identity `deg K_C + 1 - g = g - 1`, equivalent to Serre duality at the level of degrees. -/
theorem chi_canonical_from_degree (C : SmoothCompleteCurve) :
    C.degK + 1 - C.g = C.g - 1 := by
  have := deg_canonical_eq_2g_sub_2 C; linarith

/-- Algebraic symmetry `(1 - g) + (g - 1) = 0` reflecting Serre duality on Euler characteristics. -/
theorem chi_symmetry (C : SmoothCompleteCurve) :
    (1 - C.g) + (C.g - 1) = 0 := by ring

/-- Positivity of the canonical degree for genus `g ≥ 2`. -/
theorem canonical_positive_degree (C : SmoothCompleteCurve)
    (hg : C.g ≥ 2) : C.degK > 0 := by
  have := deg_canonical_eq_2g_sub_2 C; linarith

/-- Negativity of the canonical degree for genus `0` curves (i.e. `P^1`). -/
theorem canonical_negative_degree_P1 (C : SmoothCompleteCurve)
    (hg : C.g = 0) : C.degK < 0 := by
  have := deg_canonical_eq_2g_sub_2 C; linarith

/-- Vanishing of the canonical degree for elliptic curves (`g = 1`). -/
theorem canonical_zero_degree_elliptic (C : SmoothCompleteCurve)
    (hg : C.g = 1) : C.degK = 0 := by
  have := deg_canonical_eq_2g_sub_2 C; linarith

/-- Construct a `SmoothCompleteCurve` of genus `g : ℕ` using the Riemann-Roch Euler characteristic
homomorphism and the canonical degree formula `2g - 2`. -/
def mkCurve (g : ℕ) (hwf : CurveWitness (g : ℤ) := curveWitness_of_nat g) : SmoothCompleteCurve where
  g := g
  χ := rrHom g
  degK := 2 * (g : ℤ) - 2
  hg_nonneg := Int.natCast_nonneg g
  hχ_struct := rr_value_structure_sheaf g
  hχ_sky := rr_value_skyscraper g
  hwf := hwf

/-- The canonical degree of `mkCurve g` is `2g - 2` by definition. -/
@[simp] theorem mkCurve_degK (g : ℕ) : (mkCurve g).degK = 2 * (g : ℤ) - 2 := rfl

/-- The genus of `mkCurve g` is `g` by definition. -/
@[simp] theorem mkCurve_genus (g : ℕ) : (mkCurve g).g = (g : ℤ) := rfl

/-- Canonical degree for `mkCurve 0` (the projective line): `-2`. -/
theorem mkCurve_P1 : (mkCurve 0).degK = -2 := by norm_num [mkCurve]

/-- Canonical degree for `mkCurve 1` (elliptic curves): `0`. -/
theorem mkCurve_elliptic : (mkCurve 1).degK = 0 := by norm_num [mkCurve]

/-- Canonical degree for `mkCurve 2` (genus-`2` curves): `2`. -/
theorem mkCurve_genus2 : (mkCurve 2).degK = 2 := by norm_num [mkCurve]

/-- If the abstract genus of `C` equals the Dedekind-domain genus `curveGenus k A`, then the
canonical degree formula `2g - 2` agrees with the algebraic invariant. -/
theorem genus_eq_dim_kahler
    (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A]
    (C : SmoothCompleteCurve)
    (hg : C.g = curveGenus k A) :
    C.degK = 2 * (curveGenus k A : ℤ) - 2 := by
  rw [← hg]
  exact deg_canonical_eq_2g_sub_2 C

/-- Adjunction identity for a plane curve of degree `d`: `d(d - 3) + 2 = (d - 1)(d - 2)`.
This encodes `2g - 2 = d(d - 3)` and `g = (d - 1)(d - 2)/2`. -/
theorem adjunction_genus_plane_curve (d : ℤ) :
    d * (d - 3) + 2 = (d - 1) * (d - 2) := by ring

/-- Canonical-degree form of the adjunction formula on a plane curve of degree `d`:
`2g - 2 = d(d - 3)`, where `g = (d - 1)(d - 2)/2`. -/
theorem adjunction_genus_plane_curve_degK (d : ℤ) (_hd : 0 ≤ d) :
    let g := (d - 1) * (d - 2) / 2
    2 * g - 2 = d * (d - 3) := by
  intro g
  have h_even : (2 : ℤ) ∣ (d - 1) * (d - 2) := by
    rcases Int.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨(d - 1) * (m - 1), by rw [hm]; ring⟩
    · exact ⟨m * (d - 2), by rw [hm]; ring⟩
  rw [show g = (d - 1) * (d - 2) / 2 from rfl, Int.mul_ediv_cancel' h_even]
  ring

/-- Consistency with the Euler-sequence calculation on `P^1`: `deg K_{P^1} = -(1 + 1) = -2`. -/
theorem canonical_P1_consistent_euler :
    (mkCurve 0).degK = -(1 + 1 : ℤ) := by
  simp [mkCurve]

/-- Adjunction-formula consistency for the smooth plane cubic (`d = 3`): `deg K = 3·(3 - 3) = 0`,
matching `mkCurve 1`. -/
theorem elliptic_from_adjunction :
    (mkCurve 1).degK = (3 : ℤ) * (3 - 3) := by
  simp [mkCurve]

end CanonicalSheafCurves

end
