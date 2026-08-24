# Investigation: Can Mathlib's Meromorphic API Replace the Bridge Axiom?

## Task: l14-residue-theorem-via-mathlib

### Conclusion: **No.** Mathlib does not have a residue theorem and its meromorphic API cannot replace the bridge axiom.

---

## What Mathlib HAS

### Meromorphic function API (`Mathlib.Analysis.Meromorphic.*`)
- `MeromorphicAt f x` — f is meromorphic at point x (defined over any nontrivially normed field)
- `MeromorphicOn f U` — f is meromorphic on set U (pointwise definition)
- `meromorphicOrderAt f x : WithTop ℤ` — order of f at x
- `meromorphicTrailingCoeffAt f x : E` — trailing coefficient
- `MeromorphicOn.divisor f U : locallyFinsuppWithin U ℤ` — divisor
- Factorized rational functions, normal forms

### Jensen's Formula (`Mathlib.Analysis.Complex.JensenFormula`)
- `MeromorphicOn.circleAverage_log_norm` — relates `circleAverage (log ‖f ·‖)` to the divisor
- This is about **real-valued circle averages of log-norms**, NOT about complex-valued contour integrals `∮ f dz`

### Circle integral API (`Mathlib.Analysis.Complex.CauchyIntegral`)
- `circleIntegral_eq_of_differentiable_on_annulus_off_countable` — **concentric** circles only
- `circleIntegral_eq_zero_of_differentiable_on_off_countable` — Cauchy's theorem (integral = 0 for holomorphic)
- `circleIntegral.integral_sub_center_inv` — ∮ (z-c)⁻¹ dz = 2πi
- `circleIntegral.integral_sub_zpow_of_ne` — ∮ (z-w)^n dz = 0 for n ≠ -1

---

## What Mathlib LACKS

1. **No residue theorem** — no result of the form `∮ f dz = 2πi · Σ Res(f, aⱼ)`
2. **No `Complex.residue` definition** — no definition of residue as `(2πi)⁻¹ ∮ f dz`
3. **No non-concentric contour deformation** — Mathlib's circle integral API only handles concentric annuli (same center for inner/outer circles). The key gap is:
   - Given `∮_{C(c,R)} f` with singularities at `a₁,...,aₙ` (possibly `aⱼ ≠ c`),
   - Mathlib CANNOT show this equals `Σⱼ ∮_{C(aⱼ,rⱼ)} f`
   - This is exactly what `circleIntegral_eq_sum_of_singularities_bridge` provides
4. **No winding number API** for circle contours
5. **No argument principle** relating ∮ f'/f to zeros minus poles

---

## Why the bridge axiom is necessary

The `residue_theorem` proof chain is:

```
residue_theorem
  ↓ uses
circleIntegral_eq_sum_of_singularities
  ↓ for n ≥ 1, uses
circleIntegral_eq_sum_of_singularities_bridge  (AXIOM)
```

The core mathematical content is **contour deformation for non-concentric circles**:
when singularity `aⱼ` is at a different point than the center `c` of the big circle, we need to deform the contour from `C(c,R)` to `C(aⱼ,rⱼ)`. This requires:

1. Piecewise-smooth contours (bridges connecting the circles)
2. Cauchy's theorem for arbitrary simply connected domains
3. A limiting argument as bridge width → 0

Mathlib only has Cauchy's theorem for circles (`circleIntegral_eq_zero_of_differentiable_on_off_countable`), not for general simply connected domains or piecewise-smooth contours. Therefore, the bridge axiom cannot be eliminated using current Mathlib.

---

## Recommendation

The bridge axiom `circleIntegral_eq_sum_of_singularities_bridge` should remain as-is. It is a mathematically correct statement that captures the essential gap between Mathlib's current API and the residue theorem. The current proof structure is sound:

- Base case (n=0): proved from Cauchy's theorem ✓
- Inductive case (n≥1): uses bridge axiom (justified by textbook construction) ✓
- `residue_theorem`: clean proof using contour deformation + definition unfolding ✓
