/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves
import Atlas.AlgebraicGeometryI.code.CohomologyP1
import Atlas.AlgebraicGeometryI.code.RiemannRoch
import Atlas.AlgebraicGeometryI.code.RiemannRochCurves
import Atlas.AlgebraicGeometryI.code.TateCechInfra
import Atlas.AlgebraicGeometryI.code.DedekindCurve

open RiemannRochCurves CanonicalSheafCurves CohomologyP1 RiemannRoch

noncomputable section

namespace GenusConstruction


/-- Euler characteristic of the structure sheaf on `P^1` via Čech: `χ(O_{P^1}) = 1`. -/
theorem chi_P1_struct_from_cech (k : Type) [Field k] :
    (dimH0 k 0 : ℤ) - (dimH1 k 0 : ℤ) = 1 := by
  have h := riemann_roch_P1 k 0
  linarith

/-- Euler characteristic of the canonical sheaf on `P^1`: `χ(ω_{P^1}) = -1`. -/
theorem chi_P1_canonical_from_cech (k : Type) [Field k] :
    (dimH0 k (-2) : ℤ) - (dimH1 k (-2) : ℤ) = -1 := by
  have h := riemann_roch_P1 k (-2)
  linarith

/-- The Čech computation of `χ(O_{P^1})` matches the value predicted by the Riemann-Roch map. -/
theorem chi_P1_struct_eq_rrHom (k : Type) [Field k] :
    (dimH0 k 0 : ℤ) - (dimH1 k 0 : ℤ) = rrHom 0 (1, 0) := by
  rw [rr_value_structure_sheaf]
  exact chi_P1_struct_from_cech k

/-- The Čech computation of `χ(ω_{P^1})` matches the Riemann-Roch prediction for genus `0`. -/
theorem chi_P1_canonical_eq_rrHom (k : Type) [Field k] :
    (dimH0 k (-2) : ℤ) - (dimH1 k (-2) : ℤ) = rrHom 0 (1, -2) := by
  rw [rrHom_apply]
  exact chi_P1_canonical_from_cech k


/-- The smooth complete curve `P^1` packaged from Čech data: genus `0`, canonical degree `-2`,
Euler characteristic given by the Riemann-Roch homomorphism. -/
def P1CurveFromCech (_k : Type) [Field _k] : SmoothCompleteCurve where
  g := 0
  χ := rrHom 0
  degK := -2
  hg_nonneg := le_refl 0
  hχ_struct := rr_value_structure_sheaf 0
  hχ_sky := rr_value_skyscraper 0
  hwf := curveWitness_zero

/-- The genus of `P1CurveFromCech k` is `0`. -/
theorem P1CurveFromCech_genus (k : Type) [Field k] :
    (P1CurveFromCech k).g = 0 := rfl

/-- The canonical degree of `P1CurveFromCech k` is `-2`. -/
theorem P1CurveFromCech_degK (k : Type) [Field k] :
    (P1CurveFromCech k).degK = -2 := rfl

/-- `P1CurveFromCech k` agrees with the abstract genus-0 curve `mkCurve 0`. -/
theorem P1CurveFromCech_eq_mkCurve (k : Type) [Field k] :
    P1CurveFromCech k = mkCurve 0 := by


  show P1CurveFromCech k = mkCurve 0
  unfold P1CurveFromCech mkCurve
  congr 1


/-- Validation: the Riemann-Roch value of `O_{P^1}` on `P1CurveFromCech` matches the Čech result. -/
theorem P1_chi_struct_validated (k : Type) [Field k] :
    (P1CurveFromCech k).χ (1, 0) =
      (dimH0 k 0 : ℤ) - (dimH1 k 0 : ℤ) := by
  rw [chi_P1_struct_from_cech k]
  exact (P1CurveFromCech k).hχ_struct

/-- Validation: the Riemann-Roch value of `ω_{P^1}` matches the Čech-computed Euler characteristic. -/
theorem P1_chi_canonical_validated (k : Type) [Field k] :
    (P1CurveFromCech k).χ (1, (P1CurveFromCech k).degK) =
      (dimH0 k (-2) : ℤ) - (dimH1 k (-2) : ℤ) := by
  rw [chi_P1_canonical_from_cech k]
  exact (P1CurveFromCech k).hχ_canonical

/-- `h^0(O_{P^1}) = 1`: the structure sheaf has a one-dimensional global section space. -/
theorem P1_H0_struct_from_cech (k : Type) [Field k] :
    dimH0 k 0 = 1 := by
  have := dimH0_nonneg k 0
  simpa using this

/-- `h^1(O_{P^1}) = 0`: the arithmetic genus of `P^1` is zero. -/
theorem P1_H1_struct_from_cech (k : Type) [Field k] :
    dimH1 k 0 = 0 := by
  have := dimH1_nonneg k 0
  simpa using this

/-- `h^0(ω_{P^1}) = 0`: the canonical bundle on `P^1` has no global sections. -/
theorem P1_H0_canonical_from_cech (k : Type) [Field k] :
    dimH0 k (-2) = 0 :=
  canonical_bundle_P1_H0 k

/-- `h^1(ω_{P^1}) = 1`: dual to global sections of `O_{P^1}` via Serre duality. -/
theorem P1_H1_canonical_from_cech (k : Type) [Field k] :
    dimH1 k (-2) = 1 :=
  canonical_bundle_P1_H1 k


/-- A smooth complete curve constructed from a finite-dimensional Dedekind algebra `A` over `k`:
genus is the curve genus of `A`, canonical degree is `2g - 2`, and Euler characteristic is the
Riemann-Roch homomorphism. -/
def curveFromDedekind (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] :
    SmoothCompleteCurve where
  g := curveGenus k A
  χ := rrHom (curveGenus k A)
  degK := 2 * (curveGenus k A : ℤ) - 2
  hg_nonneg := Int.natCast_nonneg (curveGenus k A)
  hχ_struct := rr_value_structure_sheaf (curveGenus k A)
  hχ_sky := rr_value_skyscraper (curveGenus k A)
  hwf := curveWitness_of_nat (curveGenus k A)

/-- Genus of `curveFromDedekind k A` is the Dedekind-curve genus. -/
theorem curveFromDedekind_genus (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] :
    (curveFromDedekind k A).g = curveGenus k A := rfl

/-- Canonical degree of `curveFromDedekind k A` is `2g - 2`. -/
theorem curveFromDedekind_degK (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] :
    (curveFromDedekind k A).degK = 2 * (curveGenus k A : ℤ) - 2 := rfl

/-- `curveFromDedekind k A` coincides with the abstract genus-`g` curve `mkCurve g`. -/
theorem curveFromDedekind_eq_mkCurve (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] :
    curveFromDedekind k A = mkCurve (curveGenus k A) := by
  simp only [curveFromDedekind, mkCurve]


section DedekindBridge

/-- Bridge: the smooth complete curve constructed from a Dedekind curve agrees with
its packaged `toSmoothCompleteCurve`. -/
theorem curveFromDedekind_eq_toSmoothCompleteCurve {k : Type*} [Field k]
    (C : DedekindCurve k) :
    curveFromDedekind k C.A = C.toSmoothCompleteCurve := by

  have hchi : C.cohChi = rrHom (C.ddGenus : ℤ) :=
    additive_homs_eq_of_generators_eq C.cohChi (rrHom (C.ddGenus : ℤ))
      (by rw [C.cohChi_struct_eq, rr_value_structure_sheaf])
      (by rw [C.cohChi_sky_eq, rr_value_skyscraper])
  simp only [curveFromDedekind, DedekindCurve.toSmoothCompleteCurve,
    DedekindCurve.ddGenus, DedekindCurve.degK, curveGenus]
  congr 1
  exact hchi.symm

/-- The Dedekind genus equals the genus of the corresponding `curveFromDedekind`. -/
theorem ddGenus_eq_curveFromDedekind_genus {k : Type*} [Field k]
    (C : DedekindCurve k) :
    (C.ddGenus : ℤ) = (curveFromDedekind k C.A).g := by
  simp [curveFromDedekind, DedekindCurve.ddGenus, curveGenus]

/-- Canonical degrees agree across the Dedekind bridge. -/
theorem curveFromDedekind_degK_eq_dedekind {k : Type*} [Field k]
    (C : DedekindCurve k) :
    (curveFromDedekind k C.A).degK = C.toSmoothCompleteCurve.degK := by
  rw [curveFromDedekind_eq_toSmoothCompleteCurve]

end DedekindBridge

end GenusConstruction

end
