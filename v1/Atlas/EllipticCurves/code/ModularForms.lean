/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.FermatsLastTheorem
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Analytic.Order
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Dimension.Finrank

open scoped CongruenceSubgroup MatrixGroups ModularForm Topology Manifold

noncomputable section

section WeakModularForms

/-- A weak modular form of weight `k` for a subgroup `Γ ≤ GL(2, ℝ)`: a slash-invariant
function on the upper half plane that is holomorphic (`MDiff`), but without any
condition on growth at the cusps. -/
structure WeakModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) extends
    SlashInvariantForm Γ k where
  holo' : MDiff (⇑toSlashInvariantForm)

end WeakModularForms

section ModularForms

/-- Modular forms of weight `k` for the full modular group `SL(2, ℤ) = Γ(1)`. -/
abbrev ModularFormForSL2Z (k : ℤ) := ModularForm (Γ(1) : Subgroup SL(2, ℤ)) k

/-- Forgetful map: every modular form for `SL(2, ℤ)` is in particular a weak modular
form (we drop the boundedness-at-cusps condition). -/
def ModularFormForSL2Z.toWeakModularForm {k : ℤ} (f : ModularFormForSL2Z k) :
    WeakModularForm (Γ(1) : Subgroup SL(2, ℤ)) k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'

end ModularForms

section CongruenceSubgroups

/-- Modular forms of weight `k` for the congruence subgroup `Γ₀(N) ≤ SL(2, ℤ)`. -/
abbrev ModularFormGamma0 (N : ℕ) (k : ℤ) :=
  ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k

/-- Weak modular forms of weight `k` for `Γ₀(N)` (holomorphic and slash-invariant,
without cuspidal growth condition). -/
abbrev WeakModularFormGamma0 (N : ℕ) (k : ℤ) :=
  WeakModularForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k

end CongruenceSubgroups

section CuspForms

/-- Cusp forms of weight `k` for the full modular group `SL(2, ℤ) = Γ(1)` (modular
forms vanishing at every cusp). -/
abbrev CuspFormForSL2Z (k : ℤ) := CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k

/-- Cusp forms of weight `k` for the congruence subgroup `Γ₀(N) ≤ SL(2, ℤ)`. -/
abbrev CuspFormGamma0 (N : ℕ) (k : ℤ) :=
  CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k

/-- A cusp form for `SL(2, ℤ)` is in particular a modular form (vanishing at cusps
implies boundedness at cusps). -/
def CuspFormForSL2Z.toModularFormForSL2Z {k : ℤ} (f : CuspFormForSL2Z k) :
    ModularFormForSL2Z k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f hc

/-- A cusp form for `SL(2, ℤ)` is in particular a weak modular form (drop both the
boundedness and vanishing conditions at cusps). -/
def CuspFormForSL2Z.toWeakModularForm {k : ℤ} (f : CuspFormForSL2Z k) :
    WeakModularForm (Γ(1) : Subgroup SL(2, ℤ)) k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'

end CuspForms

namespace FLT

/-- The Taylor–Wiles theorem: every semistable elliptic curve over `ℚ` is modular. -/
theorem taylor_wiles_modularity
    (E : EllipticCurveOverQ)
    (hss : IsSemistable E) :
    IsModularEllipticCurve E := by sorry

/-- The Breuil–Conrad–Diamond–Taylor theorem extending Taylor–Wiles: every elliptic
curve over `ℚ` is modular. -/
theorem bcdt_modularity
    (E : EllipticCurveOverQ) :
    IsModularEllipticCurve E := by sorry

/-- The Modularity Theorem for elliptic curves over `ℚ`: every elliptic curve over
the rationals is modular. -/
theorem modularity_theorem
    (E : EllipticCurveOverQ) :
    IsModularEllipticCurve E := by sorry

end FLT

namespace MinimalModel

/-- Predicate stating that an integral Weierstrass model `W` is a model for the
rational Weierstrass curve `E`, i.e. there is a `ℚ`-rational change of variables
taking `W` (viewed over `ℚ`) to `E`. -/
def IsModelFor (E : WeierstrassCurve.Affine ℚ) (W : WeierstrassCurve.Affine ℤ) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange ℚ,
    C • (W.map (Int.castRingHom ℚ)) = E

/-- Structure encoding that `W` is a minimal integral model for `E`: it is a model
for `E` and its discriminant divides that of every other integral model of `E`. -/
structure IsMinimalModel (E : WeierstrassCurve.Affine ℚ)
    (W : WeierstrassCurve.Affine ℤ) : Prop where
  is_model_for : IsModelFor E W
  discriminant_dvd : ∀ W' : WeierstrassCurve.Affine ℤ, IsModelFor E W' → W.Δ ∣ W'.Δ

/-- The minimal discriminant of a rational Weierstrass curve: the discriminant of
its minimal integral model. -/
noncomputable def minimalDiscriminant : WeierstrassCurve.Affine ℚ → ℤ := by sorry

/-- The minimal discriminant of a rational Weierstrass curve is nonzero. -/
theorem minimalDiscriminant_ne_zero (E : WeierstrassCurve.Affine ℚ) :
    minimalDiscriminant E ≠ 0 := by sorry

/-- The minimal discriminant of `E` divides the discriminant of any integral
Weierstrass model of `E`. -/
theorem minimalDiscriminant_dvd (E : WeierstrassCurve.Affine ℚ)
    (W : WeierstrassCurve.Affine ℤ) (hW : IsModelFor E W) :
    minimalDiscriminant E ∣ W.Δ := by sorry

/-- The (chosen) minimal integral Weierstrass model of a rational Weierstrass
curve. -/
noncomputable def minimalModel : WeierstrassCurve.Affine ℚ → WeierstrassCurve.Affine ℤ := by sorry

end MinimalModel

namespace EllipticCurveReduction

open MinimalModel

/-- The four possible reduction types of an elliptic curve at a prime:
good reduction, split multiplicative reduction, nonsplit multiplicative reduction,
or additive reduction. -/
inductive ReductionType where
  | good : ReductionType
  | splitMultiplicative : ReductionType
  | nonsplitMultiplicative : ReductionType
  | additive : ReductionType
  deriving DecidableEq, Repr

/-- The reduction type of an elliptic curve `E` over `ℚ` at the prime `p`, computed
from the reduction of its minimal model modulo `p`. -/
noncomputable def reductionTypeAt (E : WeierstrassCurve.Affine ℚ) (p : ℕ) :
    ReductionType := by
  classical
  exact
    let W := minimalModel E
    let Wp := W.map (Int.castRingHom (ZMod p))
    if Wp.Δ ≠ 0 then ReductionType.good
    else if Wp.c₄ = 0 then ReductionType.additive
    else if IsSquare (-Wp.c₆ * Wp.c₄⁻¹ : ZMod p) then ReductionType.splitMultiplicative
    else ReductionType.nonsplitMultiplicative

/-- The local conductor exponent of an elliptic curve at a prime, giving the
power of that prime appearing in the global conductor. -/
noncomputable def conductorExponent : WeierstrassCurve.Affine ℚ → ℕ → ℕ := by sorry

/-- At a prime of good reduction, the conductor exponent is `0`. -/
theorem conductorExponent_good {E : WeierstrassCurve.Affine ℚ} {p : ℕ}
    (h : reductionTypeAt E p = ReductionType.good) :
    conductorExponent E p = 0 := by sorry

/-- At a prime of split multiplicative reduction, the conductor exponent is `1`. -/
theorem conductorExponent_splitMult {E : WeierstrassCurve.Affine ℚ} {p : ℕ}
    (h : reductionTypeAt E p = ReductionType.splitMultiplicative) :
    conductorExponent E p = 1 := by sorry

/-- At a prime of nonsplit multiplicative reduction, the conductor exponent is `1`. -/
theorem conductorExponent_nonsplitMult {E : WeierstrassCurve.Affine ℚ} {p : ℕ}
    (h : reductionTypeAt E p = ReductionType.nonsplitMultiplicative) :
    conductorExponent E p = 1 := by sorry

/-- At a prime `p > 3` of additive reduction, the conductor exponent is `2`. -/
theorem conductorExponent_additive {E : WeierstrassCurve.Affine ℚ} {p : ℕ}
    (hp : p > 3) (h : reductionTypeAt E p = ReductionType.additive) :
    conductorExponent E p = 2 := by sorry

/-- The conductor of an elliptic curve over `ℚ`: the product over primes dividing
the minimal discriminant of `p` raised to the local conductor exponent. -/
noncomputable def conductor (E : WeierstrassCurve.Affine ℚ) : ℕ :=
  ∏ p ∈ (minimalDiscriminant E).natAbs.primeFactors, p ^ conductorExponent E p

/-- The conductor of an elliptic curve over `ℚ` is positive. -/
theorem conductor_pos (E : WeierstrassCurve.Affine ℚ) : 0 < conductor E := by sorry

end EllipticCurveReduction

namespace EllipticCurve

open EllipticCurveReduction in
/-- An elliptic curve over `ℚ` is semistable if it has good or multiplicative
(but never additive) reduction at every prime. -/
def IsSemiStable (E : WeierstrassCurve.Affine ℚ) : Prop :=
  ∀ (p : ℕ), Nat.Prime p → reductionTypeAt E p ≠ ReductionType.additive

open EllipticCurveReduction in
/-- If at every bad prime the reduction of `E` is split or nonsplit multiplicative
(so that the local exponent is `1`), the conductor is simply the squarefree
product of those primes. -/
theorem conductor_semistable (E : WeierstrassCurve.Affine ℚ)
    (h : ∀ p ∈ (MinimalModel.minimalDiscriminant E).natAbs.primeFactors,
      reductionTypeAt E p = ReductionType.splitMultiplicative ∨
      reductionTypeAt E p = ReductionType.nonsplitMultiplicative) :
    EllipticCurveReduction.conductor E = ∏ p ∈ (MinimalModel.minimalDiscriminant E).natAbs.primeFactors, p := by
  unfold EllipticCurveReduction.conductor
  apply Finset.prod_congr rfl
  intro p hp
  rcases h p hp with hsplit | hnsplit
  · rw [conductorExponent_splitMult hsplit, pow_one]
  · rw [conductorExponent_nonsplitMult hnsplit, pow_one]

open EllipticCurveReduction in
/-- A semistable elliptic curve has squarefree conductor. -/
theorem conductor_squarefree_of_semistable {E : WeierstrassCurve.Affine ℚ}
    (h : IsSemiStable E) : Squarefree (EllipticCurveReduction.conductor E) := by sorry

open EllipticCurveReduction in
/-- An elliptic curve with squarefree conductor is semistable. -/
theorem semistable_of_conductor_squarefree {E : WeierstrassCurve.Affine ℚ}
    (h : Squarefree (EllipticCurveReduction.conductor E)) : IsSemiStable E := by sorry

open EllipticCurveReduction in
/-- Characterisation: an elliptic curve over `ℚ` is semistable iff its conductor
is squarefree. -/
theorem conductor_squarefree_iff_semistable (E : WeierstrassCurve.Affine ℚ) :
    Squarefree (EllipticCurveReduction.conductor E) ↔ IsSemiStable E :=
  ⟨semistable_of_conductor_squarefree, conductor_squarefree_of_semistable⟩

end EllipticCurve

namespace EllipticCurveLFunction

open Complex Polynomial EllipticCurveReduction

/-- The trace of Frobenius of `E` at the prime `p`: at primes of good reduction
it equals `p + 1 − #E(𝔽_p)`, and at primes of bad reduction it takes the
conventional values `0` (additive), `1` (split multiplicative), or `−1`
(nonsplit multiplicative). -/
noncomputable def traceOfFrobenius (E : WeierstrassCurve.Affine ℚ) (p : ℕ) : ℤ :=
  match reductionTypeAt E p with
  | .good =>
    if hp : Nat.Prime p then
      haveI : Fact (Nat.Prime p) := ⟨hp⟩
      haveI : NeZero p := NeZero.of_pos hp.pos


      let affineCount : ℕ :=
        ((Finset.univ : Finset ((ZMod p) × (ZMod p))).filter fun xy =>
          xy.2 ^ 2 + (E.a₁ : ZMod p) * xy.1 * xy.2 + (E.a₃ : ZMod p) * xy.2 =
            xy.1 ^ 3 + (E.a₂ : ZMod p) * xy.1 ^ 2 + (E.a₄ : ZMod p) * xy.1 +
              (E.a₆ : ZMod p)).card


      (p : ℤ) + 1 - (↑affineCount + 1)
    else 0
  | .additive => 0
  | .splitMultiplicative => 1
  | .nonsplitMultiplicative => -1

/-- The local character `χ(p)`: equals `1` at primes of good reduction and `0`
at primes of bad reduction. -/
noncomputable def chi (E : WeierstrassCurve.Affine ℚ) (p : ℕ) : ℤ :=
  if reductionTypeAt E p = ReductionType.good then 1 else 0

/-- The local L-polynomial at `p`: `1 − a_p X + p X²` at primes of good reduction,
and `1`, `1 − X`, or `1 + X` at primes of additive, split multiplicative, or
nonsplit multiplicative reduction respectively. -/
noncomputable def localLPolynomial (E : WeierstrassCurve.Affine ℚ) (p : ℕ) :
    Polynomial ℤ :=
  match reductionTypeAt E p with
  | ReductionType.good =>
      1 - C (traceOfFrobenius E p) * X + C (p : ℤ) * X ^ 2
  | ReductionType.additive => 1
  | ReductionType.splitMultiplicative => 1 - X
  | ReductionType.nonsplitMultiplicative => 1 + X

/-- The local Euler factor at `p` and complex variable `s`: the reciprocal of the
local L-polynomial evaluated at `p^{-s}`. -/
noncomputable def localEulerFactor (E : WeierstrassCurve.Affine ℚ) (p : ℕ)
    (s : ℂ) : ℂ :=
  (Polynomial.aeval ((p : ℂ) ^ (-s)) (localLPolynomial E p))⁻¹

/-- The (Hasse–Weil) L-function of an elliptic curve over `ℚ`, defined as the
Euler product of local factors over all primes. -/
noncomputable def LFunction (E : WeierstrassCurve.Affine ℚ) (s : ℂ) : ℂ :=
  tprod (fun (p : Nat.Primes) => localEulerFactor E p.val s)

/-- At a prime of additive reduction, the trace of Frobenius is `0`. -/
theorem traceOfFrobenius_additive {E : WeierstrassCurve.Affine ℚ} {p : ℕ}
    (h : reductionTypeAt E p = ReductionType.additive) :
    traceOfFrobenius E p = 0 := by
  unfold traceOfFrobenius; rw [h]

/-- At a prime of split multiplicative reduction, the trace of Frobenius is `1`. -/
theorem traceOfFrobenius_splitMult {E : WeierstrassCurve.Affine ℚ} {p : ℕ}
    (h : reductionTypeAt E p = ReductionType.splitMultiplicative) :
    traceOfFrobenius E p = 1 := by
  unfold traceOfFrobenius; rw [h]

/-- At a prime of nonsplit multiplicative reduction, the trace of Frobenius is
`-1`. -/
theorem traceOfFrobenius_nonsplitMult {E : WeierstrassCurve.Affine ℚ} {p : ℕ}
    (h : reductionTypeAt E p = ReductionType.nonsplitMultiplicative) :
    traceOfFrobenius E p = -1 := by
  unfold traceOfFrobenius; rw [h]

/-- At any prime of bad reduction, the trace of Frobenius lies in `{0, 1, -1}`. -/
theorem traceOfFrobenius_bad_mem {E : WeierstrassCurve.Affine ℚ} {p : ℕ}
    (h : reductionTypeAt E p ≠ ReductionType.good) :
    traceOfFrobenius E p ∈ ({0, 1, -1} : Set ℤ) := by
  rcases hrt : reductionTypeAt E p with _ | _ | _ | _
  · exact absurd hrt h
  · simp [traceOfFrobenius_splitMult hrt]
  · simp [traceOfFrobenius_nonsplitMult hrt]
  · simp [traceOfFrobenius_additive hrt]

/-- The Euler product defining the L-function converges (as an unordered product)
for `Re(s) > 3/2`. -/
theorem LFunction_converges (E : WeierstrassCurve.Affine ℚ) (s : ℂ)
    (hs : 3 / 2 < s.re) :
    HasProd (fun (p : Nat.Primes) => localEulerFactor E p.val s)
      (LFunction E s) := by sorry

/-- The local zeta function of `E` at `p` as a rational function in `T`: the
local L-polynomial divided by `(1 − T)(1 − pT)`. -/
noncomputable def zetaFunction (E : WeierstrassCurve.Affine ℚ) (p : ℕ)
    (T : ℂ) : ℂ :=
  (Polynomial.aeval T (localLPolynomial E p) : ℂ) / ((1 - T) * (1 - (p : ℂ) * T))

/-- The number of `𝔽_{p^n}`-points on the reduction of `E` modulo `p`. -/
noncomputable def pointCountOverExtension (E : WeierstrassCurve.Affine ℚ) (p : ℕ)
    (n : ℕ) : ℕ := by sorry

/-- At a prime of good reduction, the local zeta function admits an exponential
expression in terms of the point counts over extensions of `𝔽_p`. -/
theorem zetaFunction_eq (E : WeierstrassCurve.Affine ℚ) (p : ℕ)
    (hp : Nat.Prime p)
    (hgood : reductionTypeAt E p = ReductionType.good)
    (T : ℂ) (hT1 : T ≠ 1) (hTp : T ≠ (p : ℂ)⁻¹) :
    zetaFunction E p T =
      Complex.exp (∑' n : ℕ,
        if n = 0 then 0
        else (pointCountOverExtension E p n : ℂ) * T ^ n / (n : ℂ)) := by sorry

/-- Hasse bound: at a prime of good reduction, `a_p² ≤ 4p`, equivalently
`|a_p| ≤ 2√p`. -/
theorem hasse_bound (E : WeierstrassCurve.Affine ℚ) (p : ℕ)
    (hp : Nat.Prime p)
    (hgood : reductionTypeAt E p = ReductionType.good) :
    (traceOfFrobenius E p) ^ 2 ≤ 4 * (p : ℤ) := by sorry

end EllipticCurveLFunction

namespace NewformQExpansion

open EllipticCurveLFunction EllipticCurveReduction

/-- An integral, normalized weight-2 newform: a level `N` together with integer
Fourier coefficients `a_n` with `a_0 = 0` and `a_1 = 1`. -/
structure IntegralWeight2Newform where
  level : ℕ+
  coeffs : ℕ → ℤ
  coeffs_zero : coeffs 0 = 0
  coeffs_one : coeffs 1 = 1

/-- The integer Fourier coefficients of the (conjectural) weight-2 newform
attached to the elliptic curve `E`. -/
noncomputable def qExpansionCoeffs (E : WeierstrassCurve.Affine ℚ) : ℕ → ℤ := by sorry

/-- At every prime `p`, the `p`-th q-expansion coefficient of `E` agrees with the
trace of Frobenius `a_p(E)`. -/
theorem qExpansionCoeffs_prime (E : WeierstrassCurve.Affine ℚ) (p : ℕ)
    (hp : Nat.Prime p) :
    qExpansionCoeffs E p = traceOfFrobenius E p := by sorry

/-- Eichler–Shimura–Carayol: every integral normalized weight-2 newform `f` arises
as the q-expansion of an elliptic curve `E` over `ℚ` of conductor `f.level`. -/
theorem eichler_shimura_carayol
    (f : IntegralWeight2Newform) :
    ∃ E : WeierstrassCurve.Affine ℚ,
      conductor E = f.level ∧
      ∀ n : ℕ, qExpansionCoeffs E n = f.coeffs n := by sorry

/-- Variant of Eichler–Shimura–Carayol at primes: every integral normalized
weight-2 newform comes from an elliptic curve whose traces of Frobenius match
the newform's prime coefficients. -/
theorem eichler_shimura_carayol_traceOfFrobenius
    (f : IntegralWeight2Newform) :
    ∃ E : WeierstrassCurve.Affine ℚ,
      conductor E = f.level ∧
      ∀ p : ℕ, Nat.Prime p →
        traceOfFrobenius E p = f.coeffs p := by
  obtain ⟨E, hcond, hcoeffs⟩ := eichler_shimura_carayol f
  exact ⟨E, hcond, fun p hp => by rw [← qExpansionCoeffs_prime E p hp, hcoeffs p]⟩

end NewformQExpansion

namespace ModularEllipticCurve

open EllipticCurveLFunction EllipticCurveReduction NewformQExpansion

/-- An elliptic curve `E` over `ℚ` is modular if there exists an integral
weight-2 newform whose Fourier coefficients agree with the q-expansion
coefficients of `E`. -/
def IsModular (E : WeierstrassCurve.Affine ℚ) : Prop :=
  ∃ f : IntegralWeight2Newform,
    ∀ n : ℕ, qExpansionCoeffs E n = f.coeffs n

/-- A modular elliptic curve `E` is associated with a newform whose level equals
the conductor of `E`. -/
theorem isModular_level_eq_conductor (E : WeierstrassCurve.Affine ℚ)
    (hmod : IsModular E) :
    ∃ f : IntegralWeight2Newform,
      (f.level : ℕ) = conductor E ∧
      ∀ n : ℕ, qExpansionCoeffs E n = f.coeffs n := by sorry

end ModularEllipticCurve

namespace ModularityTheorem

open EllipticCurveLFunction EllipticCurveReduction NewformQExpansion ModularEllipticCurve

/-- The L-function of a newform: the Dirichlet L-series with coefficients
`a_n ∈ ℂ`. -/
noncomputable def newformLFunction
    (f : IntegralWeight2Newform) (s : ℂ) : ℂ :=
  LSeries (fun n => (f.coeffs n : ℂ)) s

/-- An elliptic curve `E` has a modular L-function if its L-function equals
that of some newform whose level matches the conductor of `E`. -/
def IsModularLFunction (E : WeierstrassCurve.Affine ℚ) : Prop :=
  ∃ f : IntegralWeight2Newform,
    (f.level : ℕ) = conductor E ∧
    ∀ s : ℂ, LFunction E s = newformLFunction f s

/-- The L-function of an elliptic curve agrees with the Dirichlet L-series formed
from its q-expansion coefficients. -/
theorem LFunction_eq_LSeries_qExpansionCoeffs (E : WeierstrassCurve.Affine ℚ) :
    ∀ s : ℂ, LFunction E s = LSeries (fun n => (qExpansionCoeffs E n : ℂ)) s := by sorry

/-- If the q-expansion coefficients of `E` agree with those of a newform `f`,
then their L-functions agree. -/
theorem LFunction_eq_of_coeffs_eq (E : WeierstrassCurve.Affine ℚ)
    (f : IntegralWeight2Newform)
    (hcoeffs : ∀ n : ℕ, qExpansionCoeffs E n = f.coeffs n) :
    ∀ s : ℂ, LFunction E s = newformLFunction f s := by
  intro s
  rw [LFunction_eq_LSeries_qExpansionCoeffs]
  unfold newformLFunction
  congr 1
  funext n
  rw [hcoeffs]

/-- Converse: if the L-functions of `E` and a newform `f` agree, then so do
their coefficients. -/
theorem coeffs_eq_of_LFunction_eq (E : WeierstrassCurve.Affine ℚ)
    (f : IntegralWeight2Newform)
    (hL : ∀ s : ℂ, LFunction E s = newformLFunction f s) :
    ∀ n : ℕ, qExpansionCoeffs E n = f.coeffs n := by sorry

/-- The two notions of modularity (coefficient-level and L-function-level)
coincide. -/
theorem isModular_iff_isModularLFunction (E : WeierstrassCurve.Affine ℚ) :
    IsModular E ↔ IsModularLFunction E := by
  constructor
  · intro hmod
    obtain ⟨f, hlevel, hcoeffs⟩ := isModular_level_eq_conductor E hmod
    exact ⟨f, hlevel, LFunction_eq_of_coeffs_eq E f hcoeffs⟩
  · rintro ⟨f, _, hL⟩
    exact ⟨f, coeffs_eq_of_LFunction_eq E f hL⟩

/-- Modularity theorem (coefficient form): every elliptic curve over `ℚ` is
modular at the level of Fourier coefficients. -/
theorem modularity_theorem_coeffs
    (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] :
    IsModular E := by sorry

/-- Modularity theorem (L-function form): every elliptic curve over `ℚ` has a
newform with matching L-function. -/
theorem modularity_theorem_LFunction
    (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] :
    IsModularLFunction E :=
  (isModular_iff_isModularLFunction E).mp (modularity_theorem_coeffs E)

end ModularityTheorem

open ModularEllipticCurve in
/-- Global statement of the modularity theorem in the namespace's preferred form:
every elliptic curve over `ℚ` is modular. -/
theorem every_ellipticCurve_isModular
    (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] :
    IsModular E :=
  ModularityTheorem.modularity_theorem_coeffs E

namespace FaltingsTate

open EllipticCurveLFunction EllipticCurveReduction

/-- Predicate stating that `p` is a prime of good reduction for both `E₁` and
`E₂`. -/
def IsCommonGoodPrime (E₁ E₂ : WeierstrassCurve.Affine ℚ) (p : ℕ) : Prop :=
  Nat.Prime p ∧
  reductionTypeAt E₁ p = ReductionType.good ∧
  reductionTypeAt E₂ p = ReductionType.good

/-- Faltings–Tate isogeny theorem: if `E₁` and `E₂` have matching traces of
Frobenius at all but finitely many common good primes, then they are
isogenous. -/
theorem faltings_tate
    (E₁ E₂ : WeierstrassCurve.Affine ℚ)
    (h : {p : ℕ | IsCommonGoodPrime E₁ E₂ p ∧
            traceOfFrobenius E₁ p ≠ traceOfFrobenius E₂ p}.Finite) :
    Isogeny.IsIsogenous E₁ E₂ := by sorry

end FaltingsTate

namespace IsogenyLFunction

open EllipticCurveLFunction EllipticCurveReduction

/-- Isogenous elliptic curves have the same trace of Frobenius at every prime. -/
theorem isogenous_traceOfFrobenius_eq
    (E₁ E₂ : WeierstrassCurve.Affine ℚ)
    (h : Isogeny.IsIsogenous E₁ E₂)
    (p : ℕ) :
    traceOfFrobenius E₁ p = traceOfFrobenius E₂ p := by sorry

/-- Isogenous elliptic curves have the same reduction type at every prime. -/
theorem isogenous_reductionTypeAt_eq
    (E₁ E₂ : WeierstrassCurve.Affine ℚ)
    (h : Isogeny.IsIsogenous E₁ E₂)
    (p : ℕ) :
    reductionTypeAt E₁ p = reductionTypeAt E₂ p := by sorry

/-- Isogenous elliptic curves have equal L-functions. -/
theorem isogenous_LFunction_eq
    (E₁ E₂ : WeierstrassCurve.Affine ℚ)
    (h : Isogeny.IsIsogenous E₁ E₂) :
    LFunction E₁ = LFunction E₂ := by
  ext s
  unfold LFunction
  congr 1
  ext ⟨p, hp⟩
  unfold localEulerFactor
  congr 1
  unfold localLPolynomial
  rw [isogenous_reductionTypeAt_eq E₁ E₂ h p,
      isogenous_traceOfFrobenius_eq E₁ E₂ h p]

/-- If two elliptic curves have the same L-function, then their traces of
Frobenius agree at every prime. -/
theorem sameLFunction_traceOfFrobenius_eq
    (E₁ E₂ : WeierstrassCurve.Affine ℚ)
    (h : LFunction E₁ = LFunction E₂)
    (p : ℕ) :
    traceOfFrobenius E₁ p = traceOfFrobenius E₂ p := by sorry

/-- Two elliptic curves over `ℚ` are isogenous iff they have the same
L-function. -/
theorem isogenous_iff_same_LFunction
    (E₁ E₂ : WeierstrassCurve.Affine ℚ) :
    Isogeny.IsIsogenous E₁ E₂ ↔ LFunction E₁ = LFunction E₂ := by
  constructor
  · exact isogenous_LFunction_eq E₁ E₂
  · intro hL
    exact FaltingsTate.faltings_tate E₁ E₂ (by
      apply Set.Finite.subset (Set.finite_empty)
      intro p ⟨hgood, hne⟩
      exact absurd (sameLFunction_traceOfFrobenius_eq E₁ E₂ hL p) hne)

/-- Isogenous elliptic curves have equal conductor. -/
theorem isogenous_conductor_eq
    (E₁ E₂ : WeierstrassCurve.Affine ℚ)
    (h : Isogeny.IsIsogenous E₁ E₂) :
    conductor E₁ = conductor E₂ := by sorry

/-- Two elliptic curves are isogenous iff there are only finitely many common
good primes at which their traces of Frobenius differ. -/
theorem isogenous_iff_matching_traces
    (E₁ E₂ : WeierstrassCurve.Affine ℚ) :
    Isogeny.IsIsogenous E₁ E₂ ↔
      {p : ℕ | FaltingsTate.IsCommonGoodPrime E₁ E₂ p ∧
        traceOfFrobenius E₁ p ≠ traceOfFrobenius E₂ p}.Finite := by
  constructor
  · intro h
    apply Set.Finite.subset (Set.finite_empty)
    intro p ⟨_, hne⟩
    exact absurd (isogenous_traceOfFrobenius_eq E₁ E₂ h p) hne
  · exact FaltingsTate.faltings_tate E₁ E₂

/-- Combined characterisation: isogeny is equivalent to equality of L-functions
together with matching traces at almost all common good primes. -/
theorem isogenous_iff_same_LFunction_iff_matching_traces
    (E₁ E₂ : WeierstrassCurve.Affine ℚ) :
    Isogeny.IsIsogenous E₁ E₂ ↔ LFunction E₁ = LFunction E₂ ∧
      {p : ℕ | FaltingsTate.IsCommonGoodPrime E₁ E₂ p ∧
        traceOfFrobenius E₁ p ≠ traceOfFrobenius E₂ p}.Finite := by
  constructor
  · intro h
    exact ⟨(isogenous_iff_same_LFunction E₁ E₂).mp h,
           (isogenous_iff_matching_traces E₁ E₂).mp h⟩
  · intro ⟨_, htraces⟩
    exact (isogenous_iff_matching_traces E₁ E₂).mpr htraces

end IsogenyLFunction

open EllipticCurveLFunction EllipticCurveReduction in
/-- Global re-statement: two elliptic curves over `ℚ` are isogenous iff they
have the same L-function. -/
theorem isogeny_iff_same_LFunction
    (E₁ E₂ : WeierstrassCurve.Affine ℚ) :
    Isogeny.IsIsogenous E₁ E₂ ↔ EllipticCurveLFunction.LFunction E₁ = EllipticCurveLFunction.LFunction E₂ :=
  IsogenyLFunction.isogenous_iff_same_LFunction E₁ E₂

namespace HeckeOperatorProperties

open Complex

/-- A complex lattice `Λ ⊂ ℂ`: a pair of complex periods `ω₁, ω₂` that are
ℝ-linearly independent. -/
@[ext]
structure ComplexLattice where
  ω₁ : ℂ
  ω₂ : ℂ
  indep : LinearIndependent ℝ ![ω₁, ω₂]

/-- The free abelian group on the set of complex lattices, viewed as the divisor
group of lattices. -/
abbrev DivL := FreeAbelianGroup ComplexLattice

/-- Coercion of a positive natural number `n` to a nonzero complex unit. -/
noncomputable def pnatToComplexUnits (n : ℕ+) : ℂˣ :=
  Units.mk0 (n : ℂ) (by exact_mod_cast n.ne_zero)

/-- The action of a nonzero complex scalar `l` on a complex lattice, scaling
both periods. -/
noncomputable def scaleLattice (l : ℂˣ) (L : ComplexLattice) : ComplexLattice where
  ω₁ := (l : ℂ) * L.ω₁
  ω₂ := (l : ℂ) * L.ω₂
  indep := by
    have hl : (l : ℂ) ≠ 0 := Units.ne_zero l
    let f : ℂ →ₗ[ℝ] ℂ := {
      toFun := fun x => (l : ℂ) * x
      map_add' := fun a b => by ring
      map_smul' := fun r x => Algebra.mul_smul_comm r (l : ℂ) x
    }
    have hf_ker : f.ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro x hx
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk] at hx
      exact (mul_eq_zero.mp hx).resolve_left hl
    have heq : ![(l : ℂ) * L.ω₁, (l : ℂ) * L.ω₂] = f ∘ ![L.ω₁, L.ω₂] := by
      ext i; fin_cases i <;> simp [f]
    rw [heq]
    exact L.indep.map' f hf_ker

/-- The Hecke operator `T_n` acting on the free abelian group of lattices: sends
each lattice to the formal sum of its index-`n` sublattices. -/
noncomputable def heckeT (n : ℕ+) : Module.End ℤ DivL := by sorry

/-- The Hecke operator at `n = 1` is the identity. -/
theorem heckeT_one : heckeT 1 = 1 := by sorry

/-- The homothety operator `R_l`: the ℤ-linear extension of the scaling action
on lattices by the scalar `l ∈ ℂˣ`. -/
noncomputable def homothetyR (l : ℂˣ) : Module.End ℤ DivL :=
  (FreeAbelianGroup.map (scaleLattice l)).toIntLinearMap

/-- Scalings compose by multiplication of scalars. -/
lemma scaleLattice_comp (l mu : ℂˣ) :
    scaleLattice l ∘ scaleLattice mu = scaleLattice (l * mu) := by
  funext L
  simp only [Function.comp, scaleLattice]
  ext <;> simp [Units.val_mul, mul_assoc]

/-- The Hecke operator `T_n` commutes with every homothety `R_l`. -/
theorem hecke_commutes_homothety (n : ℕ+) (l : ℂˣ) :
    heckeT n * homothetyR l = homothetyR l * heckeT n := by sorry

/-- Homotheties multiply: `R_l ∘ R_μ = R_{lμ}`. -/
theorem homothety_mul (l mu : ℂˣ) :
    homothetyR l * homothetyR mu = homothetyR (l * mu) := by
  ext x
  show (FreeAbelianGroup.map (scaleLattice l)) ((FreeAbelianGroup.map (scaleLattice mu)) x) =
    (FreeAbelianGroup.map (scaleLattice (l * mu))) x
  rw [← FreeAbelianGroup.map_comp_apply, scaleLattice_comp]

/-- Multiplicativity of Hecke operators on coprime indices: `T_{mn} = T_m ∘ T_n`
when `gcd(m, n) = 1`. -/
theorem hecke_multiplicative (m n : ℕ+) (h : Nat.Coprime m.val n.val) :
    heckeT (m * n) = heckeT m * heckeT n := by sorry

/-- The finite set of index-`n` sublattices of a given lattice `L`. -/
noncomputable def SubL (n : ℕ+) (L : ComplexLattice) : Finset ComplexLattice := by sorry

/-- Defining identity for the Hecke operator: `T_n` sends a basis lattice to the
formal sum of its index-`n` sublattices. -/
theorem heckeT_of (n : ℕ+) (L : ComplexLattice) :
    heckeT n (FreeAbelianGroup.of L) =
      (SubL n L).sum (fun L' => FreeAbelianGroup.of L') := by sorry

/-- The composition `T_{p^{r+1}} ∘ T_p` applied to a lattice unfolds to a double
sum over sublattices counting pairs `(L', L'')`. -/
theorem heckeT_comp_counts_pairs (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (L : ComplexLattice) :
    let pp : ℕ+ := ⟨p, hp.pos⟩
    (heckeT (pp ^ (r + 1)) * heckeT pp) (FreeAbelianGroup.of L) =
      ((SubL pp L).sum fun L' =>
        (SubL (pp ^ (r + 1)) L').sum fun L'' =>
          FreeAbelianGroup.of L'') := by sorry

/-- The double sum decomposition: pairs `(L', L'')` of nested sublattices split
into index-`p^{r+2}` sublattices of `L` plus a `p`-multiplied correction term
from scaled index-`p^r` sublattices. -/
theorem pair_decomposition (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (L : ComplexLattice) :
    let pp : ℕ+ := ⟨p, hp.pos⟩
    ((SubL pp L).sum fun L' =>
      (SubL (pp ^ (r + 1)) L').sum fun L'' =>
        FreeAbelianGroup.of L'') =
      (SubL (pp ^ (r + 2)) L).sum (fun L'' => FreeAbelianGroup.of L'') +
        (p : ℤ) • ((SubL (pp ^ r) L).sum fun L''' =>
          FreeAbelianGroup.of (scaleLattice (pnatToComplexUnits pp) L''')) := by sorry

/-- Recurrence for Hecke operators at prime powers:
`T_{p^{r+2}} = T_{p^{r+1}} T_p − p · T_{p^r} R_p`. -/
theorem hecke_prime_power_recurrence (p : ℕ) (hp : Nat.Prime p) (r : ℕ) :
    let pp : ℕ+ := ⟨p, hp.pos⟩
    heckeT (pp ^ (r + 2)) =
      heckeT (pp ^ (r + 1)) * heckeT pp -
        (p : ℤ) • (heckeT (pp ^ r) * homothetyR (pnatToComplexUnits pp)) := by sorry

/-- The generating set for the Hecke algebra (on divisors of lattices): all
prime Hecke operators `T_p` and all prime homotheties `R_p`. -/
def heckeGenerators : Set (Module.End ℤ DivL) :=
  {x | ∃ (p : ℕ) (hp : Nat.Prime p),
    x = heckeT ⟨p, hp.pos⟩ ∨ x = homothetyR (pnatToComplexUnits ⟨p, hp.pos⟩)}

/-- Hecke operators at distinct primes commute, deduced from multiplicativity on
coprime indices. -/
lemma heckeT_prime_comm (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    heckeT ⟨p, hp.pos⟩ * heckeT ⟨q, hq.pos⟩ =
      heckeT ⟨q, hq.pos⟩ * heckeT ⟨p, hp.pos⟩ := by
  by_cases hpq : p = q
  · subst hpq; rfl
  · have hcoprime : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr (fun h => hpq (hq.eq_one_or_self_of_dvd p h |>.resolve_left hp.one_lt.ne'))
    have h1 := hecke_multiplicative ⟨p, hp.pos⟩ ⟨q, hq.pos⟩ hcoprime
    have h2 := hecke_multiplicative ⟨q, hq.pos⟩ ⟨p, hp.pos⟩ hcoprime.symm
    rw [← h1, ← h2]
    congr 1
    exact mul_comm (⟨p, hp.pos⟩ : ℕ+) ⟨q, hq.pos⟩

/-- Pairwise commutativity of the generating Hecke operators: any two generators
in `heckeGenerators` commute. -/
lemma heckeGenerators_comm : ∀ x ∈ heckeGenerators, ∀ y ∈ heckeGenerators,
    x * y = y * x := by
  intro x ⟨p, hp, hx⟩ y ⟨q, hq, hy⟩

  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  ·
    exact heckeT_prime_comm p q hp hq
  ·
    exact hecke_commutes_homothety ⟨p, hp.pos⟩ (pnatToComplexUnits ⟨q, hq.pos⟩)
  ·
    exact (hecke_commutes_homothety ⟨q, hq.pos⟩ (pnatToComplexUnits ⟨p, hp.pos⟩)).symm
  ·
    rw [homothety_mul, homothety_mul]
    congr 1
    exact mul_comm _ _

/-- The subring of `End ℤ DivL` generated by the Hecke operators and homotheties
is commutative. -/
@[reducible] def heckeSubringCommRing : CommRing (Subring.closure heckeGenerators) :=
  Subring.closureCommRingOfComm heckeGenerators_comm

/-- Every prime-power Hecke operator `T_{p^r}` lies in the subring generated by
prime Hecke operators and homotheties. -/
lemma heckeT_prime_power_mem_closure (p : ℕ) (hp : Nat.Prime p) (r : ℕ) :
    (heckeT (⟨p, hp.pos⟩ ^ r) : Module.End ℤ DivL) ∈ Subring.closure heckeGenerators := by
  induction r using Nat.strongRecOn with
  | ind r ihr =>
  match r with
  | 0 =>
    simp only [pow_zero]
    rw [heckeT_one]
    exact (Subring.closure heckeGenerators).one_mem
  | 1 =>
    simp only [pow_one]
    exact Subring.subset_closure ⟨p, hp, Or.inl rfl⟩
  | r + 2 =>
    rw [hecke_prime_power_recurrence p hp r]
    apply (Subring.closure heckeGenerators).sub_mem
    · exact (Subring.closure heckeGenerators).mul_mem
        (ihr (r + 1) (by omega))
        (Subring.subset_closure ⟨p, hp, Or.inl rfl⟩)
    ·
      exact (Subring.closure heckeGenerators).zsmul_mem
        ((Subring.closure heckeGenerators).mul_mem
          (ihr r (by omega))
          (Subring.subset_closure ⟨p, hp, Or.inr rfl⟩))
        (p : ℤ)

/-- For every positive `n`, the Hecke operator `T_n` lies in the subring
generated by `heckeGenerators`, by reduction to prime powers and
multiplicativity. -/
theorem heckeT_mem_closure (n : ℕ+) :
    (heckeT n : Module.End ℤ DivL) ∈ Subring.closure heckeGenerators := by

  suffices h : ∀ (m : ℕ) (hm : 0 < m),
      (heckeT ⟨m, hm⟩ : Module.End ℤ DivL) ∈ Subring.closure heckeGenerators by
    exact h n.val n.pos
  intro m

  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; omega
  | one =>
    intro hm
    have h1 : (⟨1, hm⟩ : ℕ+) = 1 := rfl
    simp only [h1]
    exact heckeT_one ▸ (Subring.closure heckeGenerators).one_mem

  | prime_pow p r hp hr =>
    intro hm
    have heq : (⟨p ^ r, hm⟩ : ℕ+) = ⟨p, hp.pos⟩ ^ r := by
      exact Subtype.ext (by simp)
    simp only [heq]
    exact heckeT_prime_power_mem_closure p hp r
  | coprime a b ha hb hcop iha ihb =>
    intro hm
    have hap : 0 < a := by omega
    have hbp : 0 < b := by omega
    have hmem_a := iha hap
    have hmem_b := ihb hbp
    have heq : (⟨a * b, hm⟩ : ℕ+) = ⟨a, hap⟩ * ⟨b, hbp⟩ :=
      Subtype.ext (by simp)
    simp only [heq]
    exact hecke_multiplicative ⟨a, hap⟩ ⟨b, hbp⟩ hcop ▸
      (Subring.closure heckeGenerators).mul_mem hmem_a hmem_b

end HeckeOperatorProperties

namespace HeckeMultiplicativity

open Complex

/-- The Hecke operator `T_n` acting on modular forms of weight `k` for
`SL(2, ℤ)`. -/
noncomputable def heckeT_MF (k : ℤ) (n : ℕ+) : Module.End ℂ (ModularFormForSL2Z k) := by sorry

/-- The homothety operator `R_l` acting on modular forms of weight `k` for
`SL(2, ℤ)`. -/
noncomputable def homothetyR_MF (k : ℤ) (l : ℂˣ) : Module.End ℂ (ModularFormForSL2Z k) := by sorry

/-- On modular forms of weight `k`, the homothety by a prime `p` acts as
multiplication by the scalar `p^{k-2}`. -/
theorem homothetyR_MF_scalar (k : ℤ) (p : ℕ) (hp : Nat.Prime p) :
    let pp : ℕ+ := ⟨p, hp.pos⟩
    homothetyR_MF k (Units.mk0 (pp : ℂ) (by exact_mod_cast pp.ne_zero)) =
      ((p : ℂ) ^ (k - 2)) • (1 : Module.End ℂ (ModularFormForSL2Z k)) := by sorry

/-- Multiplicativity of Hecke operators on modular forms at coprime indices,
inherited from the lattice version. -/
theorem hecke_multiplicative_MF_from_lattice (k : ℤ) (m n : ℕ+)
    (h : Nat.Coprime m.val n.val) :
    heckeT_MF k (m * n) = heckeT_MF k m * heckeT_MF k n := by sorry

/-- The prime-power Hecke recurrence on modular forms in the form involving the
homothety operator `R_p`. -/
theorem hecke_prime_power_recurrence_MF_with_R (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (r : ℕ) :
    let pp : ℕ+ := ⟨p, hp.pos⟩
    heckeT_MF k (pp ^ (r + 2)) =
      heckeT_MF k (pp ^ (r + 1)) * heckeT_MF k pp -
        (p : ℂ) • (heckeT_MF k (pp ^ r) *
          homothetyR_MF k (Units.mk0 (pp : ℂ) (by exact_mod_cast pp.ne_zero))) := by sorry

/-- Multiplicativity of Hecke operators on modular forms at coprime indices. -/
theorem hecke_multiplicative_MF (k : ℤ) (m n : ℕ+)
    (h : Nat.Coprime m.val n.val) :
    heckeT_MF k (m * n) = heckeT_MF k m * heckeT_MF k n :=
  hecke_multiplicative_MF_from_lattice k m n h

/-- The scalar form of the prime-power Hecke recurrence on weight-`k` modular
forms: `T_{p^{r+2}} = T_{p^{r+1}} T_p − p^{k-1} T_{p^r}`. -/
theorem hecke_prime_power_recurrence_MF (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (r : ℕ) :
    let pp : ℕ+ := ⟨p, hp.pos⟩
    heckeT_MF k (pp ^ (r + 2)) =
      heckeT_MF k (pp ^ (r + 1)) * heckeT_MF k pp -
        ((p : ℂ) ^ (k - 1)) • heckeT_MF k (pp ^ r) := by
  intro pp
  rw [hecke_prime_power_recurrence_MF_with_R k p hp r]
  congr 1

  rw [homothetyR_MF_scalar k p hp]

  simp only [mul_smul_comm, mul_one]

  rw [smul_smul]
  congr 1
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [← zpow_one_add₀ hp0]
  congr 1
  omega

end HeckeMultiplicativity

namespace GaloisRepresentation

open EllipticCurveReduction EllipticCurveLFunction

/-- The absolute Galois group of `ℚ`, `Gal(ℚ̄/ℚ)`. -/
noncomputable def AbsGaloisGroupQ : Type := by sorry

/-- Group structure on the absolute Galois group of `ℚ`. -/
noncomputable instance AbsGaloisGroupQ.instGroup : Group AbsGaloisGroupQ := by sorry

attribute [instance] AbsGaloisGroupQ.instGroup

/-- A choice of Frobenius element in `Gal(ℚ̄/ℚ)` for the prime `p`. -/
noncomputable def frobeniusElement (p : ℕ) : AbsGaloisGroupQ := by sorry

/-- The `ℓ`-adic Galois representation `ρ_{E, ℓ} : Gal(ℚ̄/ℚ) → GL₂(ℤ_ℓ)`
associated to an elliptic curve `E`, arising from the Tate module. -/
noncomputable def ladicGaloisRep (E : WeierstrassCurve.Affine ℚ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    AbsGaloisGroupQ →* GL (Fin 2) ℤ_[ℓ] := by sorry

/-- Reduction `GL₂(ℤ_ℓ) → GL₂(𝔽_ℓ)` modulo `ℓ`. -/
noncomputable def reductionModL (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    GL (Fin 2) ℤ_[ℓ] →* GL (Fin 2) (ZMod ℓ) :=
  Matrix.GeneralLinearGroup.map PadicInt.toZMod

/-- The mod-`ℓ` Galois representation attached to `E`: the composition of the
`ℓ`-adic representation with reduction modulo `ℓ`. -/
noncomputable def modLGaloisRep (E : WeierstrassCurve.Affine ℚ) (ℓ : ℕ)
    [Fact (Nat.Prime ℓ)] : AbsGaloisGroupQ →* GL (Fin 2) (ZMod ℓ) :=
  (reductionModL ℓ).comp (ladicGaloisRep E ℓ)

/-- At a prime `p` of good reduction, the trace of Frobenius on the `ℓ`-adic
Galois representation of `E` equals the integer trace of Frobenius `a_p(E)`
viewed in `ℤ_ℓ`. -/
theorem trace_ladicGaloisRep_frobenius
    (E : WeierstrassCurve.Affine ℚ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (p : ℕ) (hp : Nat.Prime p)
    (hgood : reductionTypeAt E p = ReductionType.good) :
    (↑(ladicGaloisRep E ℓ (frobeniusElement p)) : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]).trace =
      (traceOfFrobenius E p : ℤ_[ℓ]) := by sorry

end GaloisRepresentation

end

namespace NewformDefinition

open Complex Asymptotics Filter

/-- A formal Dirichlet series, wrapping a sequence of complex coefficients. -/
structure DirichletSeries where
  coeffs : ℕ → ℂ

/-- The value at `s` of a Dirichlet series, defined as the L-series of its
coefficient sequence. -/
noncomputable def DirichletSeries.eval (L : DirichletSeries) (s : ℂ) : ℂ :=
  LSeries L.coeffs s

/-- Summability of a Dirichlet series at `s`: the underlying L-series sum is
summable. -/
def DirichletSeries.summable (L : DirichletSeries) (s : ℂ) : Prop :=
  LSeriesSummable L.coeffs s

/-- Unfolding lemma: the `eval` of a Dirichlet series is definitionally the
L-series of its coefficients. -/
@[simp]
theorem DirichletSeries.eval_eq (L : DirichletSeries) (s : ℂ) :
    L.eval s = LSeries L.coeffs s := rfl

/-- The Dirichlet series summability predicate unfolds to L-series
summability. -/
theorem DirichletSeries.summable_iff (L : DirichletSeries) (s : ℂ) :
    L.summable s ↔ LSeriesSummable L.coeffs s := Iff.rfl

/-- If the coefficients are `O(n^σ)` at infinity, the Dirichlet series is
summable at every `s` with `Re(s) > σ + 1`. -/
theorem DirichletSeries.summable_of_isBigO_rpow (L : DirichletSeries) {σ : ℝ} {s : ℂ}
    (hs : σ + 1 < s.re)
    (hO : L.coeffs =O[atTop] fun n : ℕ => (n : ℝ) ^ σ) :
    L.summable s := by
  apply LSeriesSummable_of_isBigO_rpow (x := σ + 1) hs
  simp only [add_sub_cancel_right]
  exact hO

/-- Under the same `O(n^σ)` hypothesis on coefficients, the Dirichlet series is
differentiable on the half-plane `Re(s) > σ + 1`. -/
theorem DirichletSeries.differentiableOn_of_isBigO_rpow (L : DirichletSeries) {σ : ℝ}
    (hO : L.coeffs =O[atTop] fun n : ℕ => (n : ℝ) ^ σ) :
    DifferentiableOn ℂ L.eval {s | σ + 1 < s.re} := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  have hab : LSeries.abscissaOfAbsConv L.coeffs ≤ σ + 1 :=
    LSeries.abscissaOfAbsConv_le_of_isBigO_rpow hO
  have hlt : LSeries.abscissaOfAbsConv L.coeffs < ↑s.re := by
    exact lt_of_le_of_lt hab (by exact_mod_cast hs)
  exact (LSeries_hasDerivAt hlt).differentiableAt

end NewformDefinition

namespace WeakBSD

open EllipticCurveLFunction Complex

/-- The arithmetic rank of an elliptic curve over `ℚ`: the ℤ-rank of its
Mordell–Weil group modulo torsion. -/
noncomputable def arithmeticRank (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] : ℕ :=
  Module.finrank ℤ (E.Point ⧸ AddCommGroup.torsion E.Point)

/-- The arithmetic rank is realised by an additive isomorphism
`E(ℚ)/tors ≃ ℤ^{rank}`. -/
theorem arithmeticRank_spec (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] :
    Nonempty ((E.Point ⧸ AddCommGroup.torsion E.Point) ≃+ (Fin (arithmeticRank E) → ℤ)) := by sorry

/-- The analytic continuation of the L-function of `E` to a function defined on
all of `ℂ`. -/
noncomputable def LFunction_ext (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] : ℂ → ℂ := by sorry

/-- The extended L-function `L_E` is differentiable on all of `ℂ`. -/
theorem LFunction_ext_differentiable (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] :
    Differentiable ℂ (LFunction_ext E) := by sorry

/-- The analytic rank of an elliptic curve over `ℚ`: the order of vanishing of
its extended L-function at `s = 1`. -/
noncomputable def analyticRank (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] : ℕ :=
  analyticOrderNatAt (LFunction_ext E) 1

/-- Specification of the analytic rank: `L_E(s) = (s-1)^{rank_an} · g(s)` with
`g` differentiable and `g(1) ≠ 0`. -/
theorem analyticRank_spec (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] :
    ∃ (g : ℂ → ℂ), Differentiable ℂ g ∧ g 1 ≠ 0 ∧
      ∀ s : ℂ, LFunction_ext E s = (s - 1) ^ (analyticRank E) * g s := by sorry

/-- The weak form of the Birch–Swinnerton-Dyer conjecture: the arithmetic and
analytic ranks of an elliptic curve over `ℚ` coincide. -/
theorem weakBSD (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] :
  arithmeticRank E = analyticRank E := by sorry

end WeakBSD

namespace HeckeAnalyticContinuation

open Complex

/-- Data for a cusp form: weight, level, and complex Fourier coefficients with
`a_0 = 0`. -/
structure CuspFormData where
  weight : ℕ
  level : ℕ+
  coeffs : ℕ → ℂ
  coeffs_zero : coeffs 0 = 0

/-- The L-function attached to a cusp form's coefficient data: the Dirichlet
L-series of its coefficients. -/
noncomputable def CuspFormData.LFunction (f : CuspFormData) (s : ℂ) : ℂ :=
  LSeries f.coeffs s

/-- The completed L-function of a cusp form:
`Λ(f, s) = N^{s/2} (2π)^{-s} Γ(s) L(f, s)`. -/
noncomputable def CuspFormData.completedLFunction (f : CuspFormData) (s : ℂ) : ℂ :=
  (f.level : ℂ) ^ (s / 2) * (2 * ↑Real.pi : ℂ) ^ (-s) * Gamma s * f.LFunction s

/-- Hecke's theorem: the L-function attached to a cusp form admits an entire
extension `L_ext` to `ℂ` that agrees with the Dirichlet series on the region
of summability and satisfies the functional equation
`Λ(s) = ε · Λ(k - s)` with sign `ε ∈ {±1}`. -/
theorem hecke_analytic_continuation_and_functional_equation (f : CuspFormData) :
    ∃ (L_ext : ℂ → ℂ),

      Differentiable ℂ L_ext ∧

      (∀ s : ℂ, LSeriesSummable f.coeffs s → L_ext s = LSeries f.coeffs s) ∧

      (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        ∀ s : ℂ,
          (f.level : ℂ) ^ (s / 2) * (2 * ↑Real.pi : ℂ) ^ (-s) *
            Gamma s * L_ext s =
          ε * ((f.level : ℂ) ^ (((f.weight : ℂ) - s) / 2) *
               (2 * ↑Real.pi : ℂ) ^ (-((f.weight : ℂ) - s)) *
               Gamma ((f.weight : ℂ) - s) * L_ext ((f.weight : ℂ) - s))) := by sorry

end HeckeAnalyticContinuation

namespace EulerProductNewform

open Complex HeckeAnalyticContinuation

/-- Data for a normalized newform: cusp-form data together with the
normalization `a_1 = 1`. -/
structure NewformData extends CuspFormData where
  coeffs_one : toCuspFormData.coeffs 1 = 1

/-- The principal Dirichlet character of conductor `N` at the prime `p`: equals
`0` if `p | N` and `1` otherwise. -/
noncomputable def principalDirichletChar (N : ℕ+) (p : ℕ) : ℂ :=
  if p ∣ (N : ℕ) then 0 else 1

/-- The local Euler factor of a newform at the prime `p`:
`(1 - a_p p^{-s} + χ(p) p^{k-1} p^{-2s})^{-1}`. -/
noncomputable def localEulerFactor (f : NewformData) (p : ℕ) (s : ℂ) : ℂ :=
  (1 - f.coeffs p * (p : ℂ) ^ (-s) +
    principalDirichletChar f.level p * (p : ℂ) ^ ((f.weight : ℤ) - 1) *
      (p : ℂ) ^ (-2 * s))⁻¹

/-- The Euler product of a newform: the (unordered) product over primes of the
local Euler factors. -/
noncomputable def eulerProduct (f : NewformData) (s : ℂ) : ℂ :=
  tprod (fun (p : Nat.Primes) => localEulerFactor f p.val s)

/-- The L-function of a newform, as a Dirichlet series in its Fourier
coefficients. -/
noncomputable def NewformData.LFunction (f : NewformData) (s : ℂ) : ℂ :=
  LSeries f.coeffs s

/-- The L-function of a newform admits an Euler product expansion over primes. -/
theorem euler_product_newform (f : NewformData) (s : ℂ) :
    f.LFunction s = eulerProduct f s := by sorry

end EulerProductNewform

namespace ParityConjecture

open WeakBSD

/-- The root number `w(E) ∈ {±1}` of an elliptic curve over `ℚ`: the sign in
the functional equation of its L-function. -/
noncomputable def rootNumber (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] : ℤ := by sorry

/-- The root number of an elliptic curve is `±1`. -/
theorem rootNumber_sq (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] :
    rootNumber E = 1 ∨ rootNumber E = -1 := by sorry

/-- Parity conjecture: the root number `w(E)` equals `(−1)^{rank(E)}`,
expressing that the parity of the arithmetic rank matches the sign of the
functional equation. -/
theorem parityConjecture (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] :
  rootNumber E = (-1 : ℤ) ^ arithmeticRank E := by sorry

end ParityConjecture

namespace PeterssonInnerProduct

open Complex MeasureTheory
open scoped CongruenceSubgroup MatrixGroups ModularForm

/-- Cusp forms of weight `k` for the congruence subgroup `Γ₀(N) ≤ SL(2, ℤ)`. -/
abbrev CuspFormGamma0 (N : ℕ) (k : ℤ) :=
  CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k

/-- The Hecke operator `T_n` acting on weight-`k` modular forms for
`SL(2, ℤ)`. -/
noncomputable def heckeOnModularForms (k : ℤ) (n : ℕ+) :
    ModularFormForSL2Z k →ₗ[ℂ] ModularFormForSL2Z k := by sorry

/-- The Hecke operator `T_n` acting on weight-`k` cusp forms for `SL(2, ℤ)`. -/
noncomputable def heckeOnCuspForms (k : ℤ) (n : ℕ+) :
    CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k →ₗ[ℂ]
    CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k := by sorry

/-- A fundamental domain in the upper half plane for the action of a congruence
subgroup `Γ ≤ SL(2, ℤ)`. -/
noncomputable def fundamentalDomain (Γ : Subgroup SL(2, ℤ)) : Set UpperHalfPlane := by sorry

/-- The Petersson inner product on cusp forms (Definition 24.18): integrates
`f(τ) · conj(g(τ)) · y^{k-2}` over a fundamental domain for `Γ`. -/
noncomputable def peterssonInnerProduct (Γ : Subgroup SL(2, ℤ)) (k : ℤ)
    (f g : CuspForm Γ k) : ℂ :=
  ∫ τ : UpperHalfPlane in fundamentalDomain Γ,
    f τ * starRingEnd ℂ (g τ) * (↑(τ.im) : ℂ) ^ (k - 2)

/-- The Petersson inner product is Hermitian: `⟨f, g⟩ = conj(⟨g, f⟩)`. -/
theorem peterssonInnerProduct_conj_symm (Γ : Subgroup SL(2, ℤ)) (k : ℤ)
    (f g : CuspForm Γ k) :
    peterssonInnerProduct Γ k f g = starRingEnd ℂ (peterssonInnerProduct Γ k g f) := by sorry

/-- The Petersson inner product is additive in its first argument. -/
theorem peterssonInnerProduct_add_left (Γ : Subgroup SL(2, ℤ)) (k : ℤ)
    (f₁ f₂ g : CuspForm Γ k) :
    peterssonInnerProduct Γ k (f₁ + f₂) g =
      peterssonInnerProduct Γ k f₁ g + peterssonInnerProduct Γ k f₂ g := by sorry

/-- The Petersson inner product is `ℂ`-linear in its first argument. -/
theorem peterssonInnerProduct_smul_left (Γ : Subgroup SL(2, ℤ)) (k : ℤ)
    (c : ℂ) (f g : CuspForm Γ k) :
    peterssonInnerProduct Γ k (c • f) g =
      c * peterssonInnerProduct Γ k f g := by sorry

/-- Positivity: the real part of `⟨f, f⟩` is nonnegative. -/
theorem peterssonInnerProduct_nonneg (Γ : Subgroup SL(2, ℤ)) (k : ℤ)
    (f : CuspForm Γ k) :
    0 ≤ (peterssonInnerProduct Γ k f f).re := by sorry

/-- `⟨f, f⟩` is real: its imaginary part vanishes. -/
theorem peterssonInnerProduct_self_im (Γ : Subgroup SL(2, ℤ)) (k : ℤ)
    (f : CuspForm Γ k) :
    (peterssonInnerProduct Γ k f f).im = 0 := by sorry

/-- Definiteness: `⟨f, f⟩ = 0` iff `f = 0`. -/
theorem peterssonInnerProduct_eq_zero_iff (Γ : Subgroup SL(2, ℤ)) (k : ℤ)
    (f : CuspForm Γ k) :
    peterssonInnerProduct Γ k f f = 0 ↔ f = 0 := by sorry

/-- The Hecke operator `T_n` acting on cusp forms for `Γ₀(N)`, defined when
`gcd(n, N) = 1`. -/
noncomputable def heckeOnCuspFormsGamma0 (N : ℕ) (k : ℤ) (n : ℕ+)
    (hn : Nat.Coprime (n : ℕ) N) :
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k →ₗ[ℂ]
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k := by sorry

/-- Hecke operators on `Γ₀(N)` at indices coprime to `N` are self-adjoint
with respect to the Petersson inner product. -/
theorem hecke_self_adjoint (N : ℕ) (k : ℤ) (n : ℕ+)
    (hn : Nat.Coprime (n : ℕ) N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k) :
    peterssonInnerProduct (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k
      (heckeOnCuspFormsGamma0 N k n hn f) g =
    peterssonInnerProduct (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k
      f (heckeOnCuspFormsGamma0 N k n hn g) := by sorry

end PeterssonInnerProduct

namespace SpectralTheorem

open LinearMap IsSymmetric Module.End

/-- Spectral theorem for a family of commuting symmetric operators: the family
admits a joint eigenspace decomposition, i.e. the joint eigenspaces give an
internal direct sum decomposition of the whole space. -/
theorem spectral_theorem_commuting_symmetric
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    {ι : Type*} [DecidableEq (ι → 𝕜)] {T : ι → E →ₗ[𝕜] E}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Function.onFun Commute T)) :
    DirectSum.IsInternal (fun χ : ι → 𝕜 ↦ ⨅ j, eigenspace (T j) (χ j)) :=
  LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hT hC

/-- Spectral theorem (supremum version): the supremum of joint eigenspaces of a
commuting family of symmetric operators is the whole space. -/
theorem spectral_theorem_commuting_symmetric_iSup
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    {ι : Type*} {T : ι → E →ₗ[𝕜] E}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Function.onFun Commute T)) :
    ⨆ χ : ι → 𝕜, ⨅ i, eigenspace (T i) (χ i) = ⊤ :=
  iSup_iInf_eq_top_of_commute hT hC

/-- Spectral theorem for a commuting pair of symmetric operators: the joint
eigenspaces `Eig_A(α) ∩ Eig_B(β)` form an internal direct sum decomposition. -/
theorem directSum_isInternal_commuting_pair
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    DirectSum.IsInternal
      (fun (i : 𝕜 × 𝕜) ↦ (eigenspace A i.2 ⊓ eigenspace B i.1)) :=
  directSum_isInternal_of_commute hA hB hAB

end SpectralTheorem

namespace LFunctionAnalyticContinuation

open Complex EllipticCurveLFunction EllipticCurveReduction NewformQExpansion ModularityTheorem HeckeAnalyticContinuation

/-- The normalized (completed) L-function of an elliptic curve over `ℚ`:
`N^{s/2} (2π)^{-s} Γ(s) L(E, s)`. -/
noncomputable def normalizedLFunction (E : WeierstrassCurve.Affine ℚ) (s : ℂ) : ℂ :=
  (conductor E : ℂ) ^ (s / 2) * (2 * ↑Real.pi : ℂ) ^ (-s) * Gamma s * LFunction E s

/-- Convert an integral weight-2 newform to abstract cusp-form data (weight `2`,
same level, coefficients embedded in `ℂ`). -/
noncomputable def cuspFormDataOfNewform (f : IntegralWeight2Newform) : CuspFormData where
  weight := 2
  level := f.level
  coeffs := fun n => (f.coeffs n : ℂ)
  coeffs_zero := by simp [f.coeffs_zero]

/-- The L-function of an elliptic curve over `ℚ` extends to an entire function on
`ℂ` agreeing with `L(E, s)` on the region of summability and satisfies the
functional equation `Λ(s) = w · Λ(2 - s)` with sign `w ∈ {±1}`. -/
theorem analytic_continuation_and_functional_equation
    (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] :
    ∃ (L_ext : ℂ → ℂ),

      Differentiable ℂ L_ext ∧

      (∀ s : ℂ, LSeriesSummable (fun n => (qExpansionCoeffs E n : ℂ)) s →
        L_ext s = LFunction E s) ∧

      (∃ w : ℤ, (w = 1 ∨ w = -1) ∧
        ∀ s : ℂ,
          (conductor E : ℂ) ^ (s / 2) * (2 * ↑Real.pi : ℂ) ^ (-s) *
            Gamma s * L_ext s =
          w * ((conductor E : ℂ) ^ (((2 : ℂ) - s) / 2) *
               (2 * ↑Real.pi : ℂ) ^ (-((2 : ℂ) - s)) *
               Gamma ((2 : ℂ) - s) * L_ext ((2 : ℂ) - s))) := by

  obtain ⟨f, hlevel, hcoeffs⟩ := ModularEllipticCurve.isModular_level_eq_conductor E (modularity_theorem_coeffs E)

  let g : CuspFormData := cuspFormDataOfNewform f

  obtain ⟨L_ext, hentire, hagree, ⟨ε, hε_sign, hfe⟩⟩ :=
    hecke_analytic_continuation_and_functional_equation g

  refine ⟨L_ext, hentire, ?_, ⟨ε, hε_sign, ?_⟩⟩
  ·
    intro s hs
    have hcoeffs_eq : (fun n => (qExpansionCoeffs E n : ℂ)) = g.coeffs := by
      funext n; simp only [g, cuspFormDataOfNewform]; rw [hcoeffs]
    have hs' : LSeriesSummable g.coeffs s := by rwa [← hcoeffs_eq]
    rw [hagree s hs', LFunction_eq_LSeries_qExpansionCoeffs E s]
    simp only [LSeries]
    congr 1
    funext n
    simp only [LSeries.term]
    split
    · rfl
    · congr 1; simp only [g, cuspFormDataOfNewform]; rw [hcoeffs]
  ·
    intro s
    have hfe_s := hfe s
    simp only [g, cuspFormDataOfNewform] at hfe_s
    have hlevel_eq : (f.level : ℂ) = (conductor E : ℂ) := by exact_mod_cast hlevel
    rw [hlevel_eq] at hfe_s
    convert hfe_s using 2

end LFunctionAnalyticContinuation

namespace ModularForm

open scoped CongruenceSubgroup MatrixGroups ModularForm

/-- Cusp forms of weight `k` for an arbitrary subgroup `Γ ≤ SL(2, ℤ)`. -/
abbrev CuspFormForSubgroup (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :=
  CuspForm Γ k

end ModularForm

namespace HeckeEigenformBasis

open Complex
open scoped CongruenceSubgroup MatrixGroups ModularForm

/-- The `n`-th q-expansion coefficient `a_n(f)` of a weight-`k` cusp form for
`SL(2, ℤ)`. -/
noncomputable def qExpCoeff (k : ℤ) :
    CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k → ℕ → ℂ := by sorry

/-- For each fixed `n`, the map `f ↦ a_n(f)` is `ℂ`-linear. -/
theorem qExpCoeff_linear (k : ℤ) (n : ℕ) :
    IsLinearMap ℂ (fun f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k => qExpCoeff k f n) := by sorry

/-- A cusp form is determined by its q-expansion: if every coefficient vanishes
then the form itself is zero. -/
theorem qExpCoeff_injective (k : ℤ)
    (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k)
    (h : ∀ n, qExpCoeff k f n = 0) : f = 0 := by sorry

/-- A cusp form has zero constant term in its q-expansion: `a_0(f) = 0`. -/
theorem qExpCoeff_zero (k : ℤ)
    (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k) :
    qExpCoeff k f 0 = 0 := by sorry

/-- Corollary 24.15: for any cusp form `f ∈ S_k(Γ₀(1))` and integers `m, n` with
`gcd(m, n) = 1`, the Hecke operator satisfies `a_m(T_n f) = a_{mn}(f)`. -/
theorem corollary_24_15 (k : ℤ) (m : ℕ) (n : ℕ+)
    (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k)
    (hcop : Nat.Coprime m n) :
    qExpCoeff k (PeterssonInnerProduct.heckeOnCuspForms k n f) m = qExpCoeff k f (m * n) := by sorry

/-- Hecke operators on cusp forms commute with each other. -/
theorem hecke_commute_on_cuspforms (k : ℤ) (m n : ℕ+) :
    PeterssonInnerProduct.heckeOnCuspForms k m ∘ₗ PeterssonInnerProduct.heckeOnCuspForms k n =
    PeterssonInnerProduct.heckeOnCuspForms k n ∘ₗ PeterssonInnerProduct.heckeOnCuspForms k m := by sorry

/-- The space `S_k(SL(2, ℤ))` of cusp forms is finite-dimensional over `ℂ`. -/
theorem instFiniteDimensional_CuspForm_SL2Z (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k) := by sorry

/-- A cusp form is a Hecke eigenform if it is nonzero and is an eigenvector of
every Hecke operator `T_n`. -/
def IsEigenform (k : ℤ) (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k) : Prop :=
  f ≠ 0 ∧ ∀ n : ℕ+, ∃ ev : ℂ, PeterssonInnerProduct.heckeOnCuspForms k n f = ev • f

/-- A Hecke eigenform is normalized if its first Fourier coefficient is `1`. -/
def IsNormalizedEigenform (k : ℤ) (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k) : Prop :=
  IsEigenform k f ∧ qExpCoeff k f 1 = 1

/-- For an eigenvector `f` of `T_n` with eigenvalue `ev`, we have
`a_n(f) = ev · a_1(f)`. -/
theorem eigenvalue_determines_coeffs (k : ℤ)
    (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k)
    (n : ℕ+) (ev : ℂ) (hev : PeterssonInnerProduct.heckeOnCuspForms k n f = ev • f) :
    qExpCoeff k f n = ev * qExpCoeff k f 1 := by
  have h15 := corollary_24_15 k 1 n f (Nat.coprime_one_left n)
  simp only [one_mul] at h15
  rw [hev] at h15
  rw [show qExpCoeff k (ev • f) 1 = ev * qExpCoeff k f 1
    from (qExpCoeff_linear k 1).map_smul ev f] at h15
  exact h15.symm

/-- The first Fourier coefficient `a_1(f)` of a Hecke eigenform is nonzero. -/
theorem eigenform_a1_ne_zero (k : ℤ)
    (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k)
    (hf : IsEigenform k f) :
    qExpCoeff k f 1 ≠ 0 := by
  intro h_a1_zero
  apply hf.1
  apply qExpCoeff_injective k f
  intro n
  by_cases hn : n = 0
  · subst hn; exact qExpCoeff_zero k f
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨ev_n, hev_n⟩ := hf.2 ⟨n, hn_pos⟩
    have := eigenvalue_determines_coeffs k f ⟨n, hn_pos⟩ ev_n hev_n
    rw [h_a1_zero, mul_zero] at this
    exact this

/-- Two Hecke eigenforms with the same system of eigenvalues differ by a scalar
multiple (eigenspaces in the joint decomposition are one-dimensional). -/
theorem eigenspace_one_dimensional (k : ℤ)
    (f g : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k)
    (hf : IsEigenform k f) (hg : IsEigenform k g)
    (hsame : ∀ n : ℕ+, ∀ ev₁ ev₂ : ℂ,
      PeterssonInnerProduct.heckeOnCuspForms k n f = ev₁ • f →
      PeterssonInnerProduct.heckeOnCuspForms k n g = ev₂ • g →
      ev₁ = ev₂) :
    ∃ c : ℂ, g = c • f := by
  have ha1f := eigenform_a1_ne_zero k f hf
  refine ⟨qExpCoeff k g 1 / qExpCoeff k f 1, ?_⟩

  apply eq_of_sub_eq_zero
  apply qExpCoeff_injective k (g - (qExpCoeff k g 1 / qExpCoeff k f 1) • f)
  intro n

  have hlin_n := qExpCoeff_linear k n
  have hsub := hlin_n.map_sub g ((qExpCoeff k g 1 / qExpCoeff k f 1) • f)
  have hsmul := hlin_n.map_smul (qExpCoeff k g 1 / qExpCoeff k f 1) f
  simp only [hsub, hsmul, smul_eq_mul]
  by_cases hn : n = 0
  · subst hn; simp [qExpCoeff_zero]
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn

    obtain ⟨evf, hevf⟩ := hf.2 ⟨n, hn_pos⟩
    obtain ⟨evg, hevg⟩ := hg.2 ⟨n, hn_pos⟩

    have hev_eq := hsame ⟨n, hn_pos⟩ evf evg hevf hevg

    have hf_coeff := eigenvalue_determines_coeffs k f ⟨n, hn_pos⟩ evf hevf
    have hg_coeff := eigenvalue_determines_coeffs k g ⟨n, hn_pos⟩ evg hevg

    change qExpCoeff k g n - _ = 0
    rw [show qExpCoeff k g n = evg * qExpCoeff k g 1 from hg_coeff,
        show qExpCoeff k f n = evf * qExpCoeff k f 1 from hf_coeff,
        hev_eq]
    have ha1f' := ha1f
    field_simp
    ring

/-- For a normalized eigenform `f`, the Hecke eigenvalue at `n` equals the
Fourier coefficient `a_n(f)`. -/
theorem eigenvalue_eq_coeff_of_normalized (k : ℤ)
    (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k)
    (hf : IsNormalizedEigenform k f)
    (n : ℕ+) (ev : ℂ) (hev : PeterssonInnerProduct.heckeOnCuspForms k n f = ev • f) :
    ev = qExpCoeff k f n := by
  have := eigenvalue_determines_coeffs k f n ev hev
  rw [hf.2, mul_one] at this
  exact this.symm

/-- The space of cusp forms is spanned by Hecke eigenforms: there exists a
finite family of (linearly independent) eigenforms whose span is the whole
space. -/
theorem eigenform_spanning (k : ℤ) :
    ∃ (ι : Type) (_ : Fintype ι)
      (B : ι → CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k),

      (∀ i, IsEigenform k (B i)) ∧

      (LinearIndependent ℂ B) ∧

      (⊤ ≤ Submodule.span ℂ (Set.range B)) := by sorry

/-- Every Hecke eigenform admits a normalization to a normalized eigenform: a
nonzero scalar multiple with `a_1 = 1`. -/
theorem eigenform_normalize (k : ℤ)
    (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k)
    (hf : IsEigenform k f) :
    ∃ g : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k,
      IsNormalizedEigenform k g ∧ ∃ c : ℂ, c ≠ 0 ∧ g = c • f := by
  have ha1 := eigenform_a1_ne_zero k f hf
  refine ⟨(qExpCoeff k f 1)⁻¹ • f, ⟨?_, ?_⟩, (qExpCoeff k f 1)⁻¹, inv_ne_zero ha1, rfl⟩
  ·
    constructor
    · intro h
      apply hf.1
      have h0 : (qExpCoeff k f 1)⁻¹ • f = 0 := h
      have : f = qExpCoeff k f 1 • ((qExpCoeff k f 1)⁻¹ • f) := by
        rw [smul_smul, mul_inv_cancel₀ ha1, one_smul]
      rw [h0, smul_zero] at this
      exact this
    · intro n
      obtain ⟨ev, hev⟩ := hf.2 n
      exact ⟨ev, by rw [map_smul, hev, smul_comm]⟩
  ·
    rw [show qExpCoeff k ((qExpCoeff k f 1)⁻¹ • f) 1 =
          (qExpCoeff k f 1)⁻¹ * qExpCoeff k f 1
      from (qExpCoeff_linear k 1).map_smul _ f]
    exact inv_mul_cancel₀ ha1

/-- The space of cusp forms admits a basis of normalized Hecke eigenforms. -/
theorem eigenform_basis (k : ℤ) :
    ∃ (ι : Type) (_ : Fintype ι)
      (B : ι → CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k),

      (∀ i, IsNormalizedEigenform k (B i)) ∧

      (LinearIndependent ℂ B) ∧

      (⊤ ≤ Submodule.span ℂ (Set.range B)) := by
  obtain ⟨ι, hfin, B₀, hef, hli, hspan⟩ := eigenform_spanning k

  have hN : ∀ i, ∃ g : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k,
      IsNormalizedEigenform k g ∧ ∃ c : ℂ, c ≠ 0 ∧ g = c • B₀ i :=
    fun i => eigenform_normalize k (B₀ i) (hef i)
  choose B hB using hN
  have hBnorm : ∀ i, IsNormalizedEigenform k (B i) := fun i => (hB i).1
  have hBrel : ∀ i, ∃ c : ℂ, c ≠ 0 ∧ B i = c • B₀ i := fun i => (hB i).2
  choose c hc using hBrel
  have hc_ne : ∀ i, c i ≠ 0 := fun i => (hc i).1
  have hc_eq : ∀ i, B i = c i • B₀ i := fun i => (hc i).2
  refine ⟨ι, hfin, B, hBnorm, ?_, ?_⟩
  ·

    rw [linearIndependent_iff'] at hli ⊢
    intro s g hg i hi
    have hrewrite : ∀ j ∈ s, g j • B j = (g j * c j) • B₀ j := by
      intro j _
      rw [hc_eq j, smul_smul]
    have hsum : ∑ j ∈ s, (g j * c j) • B₀ j = 0 := by
      calc ∑ j ∈ s, (g j * c j) • B₀ j
          = ∑ j ∈ s, g j • B j := (Finset.sum_congr rfl hrewrite).symm
        _ = 0 := hg
    have := hli s (fun j => g j * c j) hsum i hi
    exact (mul_eq_zero.mp this).elim id (fun h => absurd h (hc_ne i))
  ·
    calc ⊤ ≤ Submodule.span ℂ (Set.range B₀) := hspan
      _ ≤ Submodule.span ℂ (Set.range B) := by
        apply Submodule.span_le.mpr
        intro f hf
        obtain ⟨i, rfl⟩ := hf
        have hci := hc_ne i

        have : B₀ i = (c i)⁻¹ • B i := by
          rw [hc_eq i, smul_smul, inv_mul_cancel₀ hci, one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end HeckeEigenformBasis

namespace HeckeEigenvalueTheorem

open scoped CongruenceSubgroup MatrixGroups ModularForm
open Complex

/-- The `n`-th Fourier coefficient of a weight-`k` cusp form for `SL(2, ℤ)`. -/
noncomputable def fourierCoeff (k : ℤ) :
    CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k → ℕ → ℂ := by sorry

/-- The 0-th Fourier coefficient of a cusp form vanishes. -/
theorem fourierCoeff_zero (k : ℤ)
    (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k) :
    fourierCoeff k f 0 = 0 := by sorry

/-- Fourier coefficients are additive: `a_n(f + g) = a_n(f) + a_n(g)`. -/
theorem fourierCoeff_add (k : ℤ)
    (f g : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k) (n : ℕ) :
    fourierCoeff k (f + g) n = fourierCoeff k f n + fourierCoeff k g n := by sorry

/-- Fourier coefficients are `ℂ`-homogeneous: `a_n(c · f) = c · a_n(f)`. -/
theorem fourierCoeff_smul (k : ℤ)
    (c : ℂ) (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k) (n : ℕ) :
    fourierCoeff k (c • f) n = c * fourierCoeff k f n := by sorry

/-- Cusp forms are determined by their full q-expansion: if all Fourier
coefficients agree, the cusp forms are equal. -/
theorem fourierCoeff_ext (k : ℤ)
    (f g : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k) :
    (∀ n, fourierCoeff k f n = fourierCoeff k g n) → f = g := by sorry

/-- Theorem 24.14: for any cusp form `f ∈ S_k(Γ₀(1))` and prime `p`,
`a_n(T_p f) = a_{np}(f)` if `p ∤ n`, otherwise
`a_n(T_p f) = a_{np}(f) + p^{k-1} a_{n/p}(f)`. -/
theorem hecke_prime_fourierCoeff (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k) (n : ℕ) :
    fourierCoeff k (PeterssonInnerProduct.heckeOnCuspForms k ⟨p, hp.pos⟩ f) n =
      fourierCoeff k f (n * p) +
        if p ∣ n then (p : ℂ) ^ (k - 1) * fourierCoeff k f (n / p) else 0 := by sorry

/-- The "non-dividing" case of Theorem 24.14: when `p ∤ n`,
`a_n(T_p f) = a_{np}(f)`. -/
theorem hecke_prime_fourierCoeff_not_dvd (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k) (n : ℕ)
    (hnd : ¬ (p ∣ n)) :
    fourierCoeff k (PeterssonInnerProduct.heckeOnCuspForms k ⟨p, hp.pos⟩ f) n =
      fourierCoeff k f (n * p) := by
  rw [hecke_prime_fourierCoeff k p hp f n, if_neg hnd, add_zero]

/-- The "dividing" case of Theorem 24.14: when `p ∣ n`,
`a_n(T_p f) = a_{np}(f) + p^{k-1} a_{n/p}(f)`. -/
theorem hecke_prime_fourierCoeff_dvd (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k) (n : ℕ)
    (hd : p ∣ n) :
    fourierCoeff k (PeterssonInnerProduct.heckeOnCuspForms k ⟨p, hp.pos⟩ f) n =
      fourierCoeff k f (n * p) + (p : ℂ) ^ (k - 1) * fourierCoeff k f (n / p) := by
  rw [hecke_prime_fourierCoeff k p hp f n, if_pos hd]

end HeckeEigenvalueTheorem

namespace HeckeCoeffRelation

open scoped CongruenceSubgroup MatrixGroups ModularForm
open Complex HeckeEigenvalueTheorem PeterssonInnerProduct

/-- The Hecke operator at `n = 1` is the identity on cusp forms. -/
theorem heckeOnCuspForms_one (k : ℤ) :
    heckeOnCuspForms k 1 = LinearMap.id := by sorry

/-- Multiplicativity of Hecke operators on cusp forms at coprime indices:
`T_{mn} = T_m ∘ T_n` when `gcd(m, n) = 1`. -/
theorem heckeOnCuspForms_multiplicative (k : ℤ) (m n : ℕ+)
    (h : Nat.Coprime m.val n.val) :
    heckeOnCuspForms k (m * n) = (heckeOnCuspForms k m).comp (heckeOnCuspForms k n) := by sorry

/-- Prime-power recurrence for Hecke operators on cusp forms:
`T_{p^{r+2}} = T_{p^{r+1}} ∘ T_p − p^{k-1} · T_{p^r}`. -/
theorem heckeOnCuspForms_prime_power_recurrence (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (r : ℕ) :
    let pp : ℕ+ := ⟨p, hp.pos⟩
    heckeOnCuspForms k (pp ^ (r + 2)) =
      (heckeOnCuspForms k (pp ^ (r + 1))).comp (heckeOnCuspForms k pp) -
        ((p : ℂ) ^ (k - 1)) • heckeOnCuspForms k (pp ^ r) := by sorry

/-- Fourier coefficients are subtractive: `a_n(f - g) = a_n(f) - a_n(g)`. -/
lemma fourierCoeff_sub (k : ℤ) (f g : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k) (n : ℕ) :
    fourierCoeff k (f - g) n = fourierCoeff k f n - fourierCoeff k g n := by
  have : f - g = f + (-1 : ℂ) • g := by
    simp [sub_eq_add_neg]
  rw [this, fourierCoeff_add, fourierCoeff_smul]
  ring

/-- For a prime `p` coprime to `m`, the Hecke action on Fourier coefficients
specialises to `a_m(T_p f) = a_{mp}(f)`. -/
theorem hecke_fourierCoeff_coprime_prime (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k) (m : ℕ)
    (hcop : Nat.Coprime m p) :
    fourierCoeff k (heckeOnCuspForms k ⟨p, hp.pos⟩ f) m =
      fourierCoeff k f (m * p) := by
  exact hecke_prime_fourierCoeff_not_dvd k p hp f m
    (hp.coprime_iff_not_dvd.mp (Nat.Coprime.symm hcop))

/-- Iteration to prime powers: for `m` coprime to the prime `p`, the action of
`T_{p^r}` on Fourier coefficients satisfies `a_m(T_{p^r} f) = a_{m p^r}(f)`. -/
theorem hecke_fourierCoeff_coprime_prime_power (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (m : ℕ) (hcop : Nat.Coprime m p) :
    ∀ (r : ℕ) (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k),
    fourierCoeff k (heckeOnCuspForms k (⟨p, hp.pos⟩ ^ r) f) m =
      fourierCoeff k f (m * p ^ r) := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ihr =>
  intro f
  match r with
  | 0 =>
    simp only [pow_zero, mul_one]
    rw [heckeOnCuspForms_one, LinearMap.id_apply]
  | 1 =>
    simp only [pow_one]
    exact hecke_fourierCoeff_coprime_prime k p hp f m hcop
  | r + 2 =>
    rw [heckeOnCuspForms_prime_power_recurrence k p hp r]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [fourierCoeff_sub, fourierCoeff_smul]

    rw [ihr (r + 1) (by omega) (heckeOnCuspForms k ⟨p, hp.pos⟩ f)]

    rw [ihr r (by omega) f]

    have hdvd : p ∣ m * p ^ (r + 1) := ⟨m * p ^ r, by ring⟩
    rw [hecke_prime_fourierCoeff_dvd k p hp f (m * p ^ (r + 1)) hdvd]

    have h1 : m * p ^ (r + 1) * p = m * p ^ (r + 2) := by ring
    have h2 : m * p ^ (r + 1) / p = m * p ^ r := by
      rw [show m * p ^ (r + 1) = m * p ^ r * p from by ring]
      exact Nat.mul_div_cancel _ hp.pos
    rw [h1, h2]
    ring

/-- General statement of Corollary 24.15 (coprime version): for `gcd(m, n) = 1`,
`a_m(T_n f) = a_{mn}(f)`. -/
theorem hecke_fourierCoeff_coprime (k : ℤ)
    (n : ℕ+) :
    ∀ (m : ℕ) (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k)
    (_ : Nat.Coprime m n),
    fourierCoeff k (heckeOnCuspForms k n f) m =
      fourierCoeff k f (m * n) := by

  suffices h : ∀ (j : ℕ) (hj : 0 < j) (m : ℕ)
      (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k) (hcj : Nat.Coprime m j),
      fourierCoeff k (heckeOnCuspForms k ⟨j, hj⟩ f) m =
        fourierCoeff k f (m * j) by
    intro m f hcop_mn
    exact h n.val n.pos m f hcop_mn
  intro j
  induction j using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; omega
  | one =>
    intro _ m f _
    simp only [mul_one]
    rw [show (⟨1, (by omega : 0 < 1)⟩ : ℕ+) = (1 : ℕ+) from rfl,
        heckeOnCuspForms_one, LinearMap.id_apply]
  | prime_pow p r hp hr =>
    intro hj m f hcj
    have hcop_mp : Nat.Coprime m p :=
      hcj.coprime_dvd_right ⟨p ^ (r - 1), by
        cases r with
        | zero => simp at hr
        | succ r => simp [pow_succ, mul_comm]⟩
    have heq : (⟨p ^ r, hj⟩ : ℕ+) = ⟨p, hp.pos⟩ ^ r := by
      exact Subtype.ext (by simp)
    rw [heq]
    exact hecke_fourierCoeff_coprime_prime_power k p hp m hcop_mp r f
  | coprime a b ha hb hcop_ab iha ihb =>
    intro hj m f hcj
    have hap : 0 < a := by omega
    have hbp : 0 < b := by omega
    have hcop_ma : Nat.Coprime m a := hcj.coprime_dvd_right (Dvd.intro b rfl)
    have hcop_mb : Nat.Coprime m b := hcj.coprime_dvd_right (Dvd.intro_left a rfl)

    have hmult : heckeOnCuspForms k ⟨a * b, hj⟩ =
        (heckeOnCuspForms k ⟨a, hap⟩).comp (heckeOnCuspForms k ⟨b, hbp⟩) := by
      have heq : (⟨a * b, hj⟩ : ℕ+) = ⟨a, hap⟩ * ⟨b, hbp⟩ := Subtype.ext (by simp)
      rw [heq]
      exact heckeOnCuspForms_multiplicative k ⟨a, hap⟩ ⟨b, hbp⟩ hcop_ab
    rw [hmult, LinearMap.comp_apply]

    rw [iha hap m (heckeOnCuspForms k ⟨b, hbp⟩ f) hcop_ma]

    have hcop_mab : Nat.Coprime (m * a) b :=
      hcop_mb.mul_left hcop_ab
    rw [ihb hbp (m * a) f hcop_mab]
    ring_nf

/-- Specialisation of Corollary 24.15 at `m = 1`: `a_1(T_n f) = a_n(f)`. -/
theorem hecke_fourierCoeff_one (k : ℤ)
    (f : CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k) (n : ℕ+) :
    fourierCoeff k (heckeOnCuspForms k n f) 1 =
      fourierCoeff k f n := by
  have h := hecke_fourierCoeff_coprime k n 1 f (Nat.coprime_one_left n)
  simp only [one_mul] at h
  exact h

end HeckeCoeffRelation

namespace ModularFormDimension

open scoped CongruenceSubgroup MatrixGroups ModularForm

/-- The number `ν₂(Γ)` of elliptic points of order `2` for `Γ ≤ SL(2, ℤ)`. -/
noncomputable def nu2 (Γ : Subgroup SL(2, ℤ)) : ℕ := by sorry

/-- The number `ν₃(Γ)` of elliptic points of order `3` for `Γ ≤ SL(2, ℤ)`. -/
noncomputable def nu3 (Γ : Subgroup SL(2, ℤ)) : ℕ := by sorry

/-- The number `ν_∞(Γ)` of cusps of `Γ ≤ SL(2, ℤ)`. -/
noncomputable def nuInfty (Γ : Subgroup SL(2, ℤ)) : ℕ := by sorry

/-- The genus `g(Γ)` of the modular curve `Γ\ℍ^*`. -/
noncomputable def genus (Γ : Subgroup SL(2, ℤ)) : ℕ := by sorry

/-- The space of modular forms `M_k(Γ)` is finite-dimensional over `ℂ`. -/
theorem modularForm_finiteDimensional_ax (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :
    FiniteDimensional ℂ (ModularForm Γ k) := by sorry

/-- Instance form: the space of modular forms `M_k(Γ)` is finite-dimensional
over `ℂ`. -/
noncomputable instance modularForm_finiteDimensional (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :
    FiniteDimensional ℂ (ModularForm Γ k) := modularForm_finiteDimensional_ax Γ k

/-- The space of cusp forms `S_k(Γ)` is finite-dimensional over `ℂ`. -/
theorem cuspForm_finiteDimensional_ax (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :
    FiniteDimensional ℂ (CuspForm Γ k) := by sorry

/-- Instance form: the space of cusp forms `S_k(Γ)` is finite-dimensional over
`ℂ`. -/
noncomputable instance cuspForm_finiteDimensional (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :
    FiniteDimensional ℂ (CuspForm Γ k) := cuspForm_finiteDimensional_ax Γ k

/-- `M_0(Γ) ≅ ℂ` (constants): the space of weight-`0` modular forms is
`1`-dimensional. -/
theorem dim_modularForm_zero (Γ : Subgroup SL(2, ℤ)) :
    Module.finrank ℂ (ModularForm Γ 0) = 1 := by sorry

/-- There are no nonzero cusp forms of weight `0`: `S_0(Γ) = 0`. -/
theorem dim_cuspForm_zero (Γ : Subgroup SL(2, ℤ)) :
    Module.finrank ℂ (CuspForm Γ 0) = 0 := by sorry

/-- Dimension formula for `M_k(Γ)` for even positive `k`, in terms of the genus,
the elliptic point counts, and the number of cusps. -/
theorem dim_modularForm_even (Γ : Subgroup SL(2, ℤ)) (k : ℕ)
    (hk_pos : 0 < k) (hk_even : Even k) :
    (Module.finrank ℂ (ModularForm Γ (k : ℤ)) : ℤ) =
      ((k : ℤ) - 1) * ((genus Γ : ℤ) - 1) + (k / 4 : ℤ) * (nu2 Γ : ℤ) +
        (k / 3 : ℤ) * (nu3 Γ : ℤ) + (k / 2 : ℤ) * (nuInfty Γ : ℤ) := by sorry

/-- Dimension formula for `S_k(Γ)` for even `k > 2`, with cusp contribution
`(k/2 − 1)`. -/
theorem dim_cuspForm_even_gt2 (Γ : Subgroup SL(2, ℤ)) (k : ℕ)
    (hk_gt2 : 2 < k) (hk_even : Even k) :
    (Module.finrank ℂ (CuspForm Γ (k : ℤ)) : ℤ) =
      ((k : ℤ) - 1) * ((genus Γ : ℤ) - 1) + (k / 4 : ℤ) * (nu2 Γ : ℤ) +
        (k / 3 : ℤ) * (nu3 Γ : ℤ) + ((k : ℤ) / 2 - 1) * (nuInfty Γ : ℤ) := by sorry

/-- Dimension formula in weight `2`: `dim S_2(Γ) = g(Γ)`. -/
theorem dim_cuspForm_weight2 (Γ : Subgroup SL(2, ℤ)) :
    Module.finrank ℂ (CuspForm Γ 2) = genus Γ := by sorry

end ModularFormDimension

namespace HeckeNewformDecomposition

open Complex
open scoped CongruenceSubgroup MatrixGroups ModularForm

/-- The new subspace `S_k^{new}(Γ₀(N))` of cusp forms of weight `k` and level
`N`, complementary to the old subspace coming from divisors of `N`. -/
noncomputable def NewSubspaceCuspForm (N : ℕ) (k : ℤ) : Type := by sorry

/-- Additive group structure on the new subspace of cusp forms. -/
noncomputable instance NewSubspaceCuspForm.instAddCommGroup (N : ℕ) (k : ℤ) :
    AddCommGroup (NewSubspaceCuspForm N k) := by sorry

/-- Anonymous instance: additive group structure on the new subspace of cusp
forms. -/
noncomputable instance (N : ℕ) (k : ℤ) : AddCommGroup (NewSubspaceCuspForm N k) :=
  NewSubspaceCuspForm.instAddCommGroup N k

/-- Complex vector space structure on the new subspace of cusp forms. -/
noncomputable instance NewSubspaceCuspForm.instModule (N : ℕ) (k : ℤ) :
    Module ℂ (NewSubspaceCuspForm N k) := by sorry

/-- Anonymous instance: complex vector space structure on the new subspace of
cusp forms. -/
noncomputable instance (N : ℕ) (k : ℤ) : Module ℂ (NewSubspaceCuspForm N k) :=
  NewSubspaceCuspForm.instModule N k

/-- The new subspace `S_k^{new}(Γ₀(N))` is finite-dimensional over `ℂ`. -/
theorem NewSubspaceCuspForm.instFiniteDimensional (N : ℕ) (k : ℤ) :
    FiniteDimensional ℂ (NewSubspaceCuspForm N k) := by sorry

/-- Anonymous instance: the new subspace `S_k^{new}(Γ₀(N))` is
finite-dimensional over `ℂ`. -/
noncomputable instance (N : ℕ) (k : ℤ) : FiniteDimensional ℂ (NewSubspaceCuspForm N k) :=
  NewSubspaceCuspForm.instFiniteDimensional N k

/-- The inclusion of the new subspace into the full space of cusp forms for
`Γ₀(N)`. -/
noncomputable def NewSubspaceCuspForm.incl (N : ℕ) (k : ℤ) :
    NewSubspaceCuspForm N k →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k := by sorry

/-- The inclusion of the new subspace into the full space of cusp forms is
injective. -/
theorem NewSubspaceCuspForm.incl_injective (N : ℕ) (k : ℤ) :
    Function.Injective (NewSubspaceCuspForm.incl N k) := by sorry

/-- Hecke operators `T_n` restrict to endomorphisms of the new subspace. -/
noncomputable def heckeOnNewSubspace (N : ℕ) (k : ℤ) (n : ℕ+) :
    NewSubspaceCuspForm N k →ₗ[ℂ] NewSubspaceCuspForm N k := by sorry

/-- The `n`-th q-expansion coefficient of an element of the new subspace. -/
noncomputable def qExpCoeffNew (N : ℕ) (k : ℤ) :
    NewSubspaceCuspForm N k → ℕ → ℂ := by sorry

/-- For each `n`, the map `f ↦ a_n(f)` on the new subspace is `ℂ`-linear. -/
theorem qExpCoeffNew_linear (N : ℕ) (k : ℤ) (n : ℕ) :
    IsLinearMap ℂ (fun f : NewSubspaceCuspForm N k => qExpCoeffNew N k f n) := by sorry

/-- An element of the new subspace is determined by its q-expansion: if every
coefficient vanishes, the form itself is zero. -/
theorem qExpCoeffNew_injective (N : ℕ) (k : ℤ)
    (f : NewSubspaceCuspForm N k)
    (h : ∀ n, qExpCoeffNew N k f n = 0) : f = 0 := by sorry

/-- The constant term `a_0` of any element of the new subspace vanishes. -/
theorem qExpCoeffNew_zero (N : ℕ) (k : ℤ)
    (f : NewSubspaceCuspForm N k) :
    qExpCoeffNew N k f 0 = 0 := by sorry

/-- A new-subspace eigenform: a nonzero element that is an eigenvector of every
Hecke operator restricted to the new subspace. -/
def IsEigenformNew (N : ℕ) (k : ℤ) (f : NewSubspaceCuspForm N k) : Prop :=
  f ≠ 0 ∧ ∀ n : ℕ+, ∃ ev : ℂ, heckeOnNewSubspace N k n f = ev • f

/-- A newform of level `N` and weight `k`: a new-subspace eigenform with first
Fourier coefficient equal to `1`. -/
def IsNewform (N : ℕ) (k : ℤ) (f : NewSubspaceCuspForm N k) : Prop :=
  IsEigenformNew N k f ∧ qExpCoeffNew N k f 1 = 1

/-- For a newform, every Hecke eigenvalue is equal to the corresponding Fourier
coefficient. -/
theorem eigenvalue_eq_coeff_new (N : ℕ) (k : ℤ)
    (f : NewSubspaceCuspForm N k)
    (hf : IsNewform N k f)
    (n : ℕ+) (ev : ℂ) (hev : heckeOnNewSubspace N k n f = ev • f) :
    ev = qExpCoeffNew N k f n := by sorry

/-- Newform basis theorem: the new subspace `S_k^{new}(Γ₀(N))` admits a
canonical basis of newforms, each a Hecke eigenvector with eigenvalues equal to
its Fourier coefficients, with corresponding one-dimensional eigenlines, and
uniquely determined by its q-expansion. -/
theorem newform_basis (N : ℕ) (k : ℤ) :
    ∃ (ι : Type) (_ : Fintype ι)
      (B : ι → NewSubspaceCuspForm N k),

      (∀ i, IsNewform N k (B i)) ∧

      (LinearIndependent ℂ B) ∧

      (⊤ ≤ Submodule.span ℂ (Set.range B)) ∧

      (∀ i (n : ℕ+),
        heckeOnNewSubspace N k n (B i) = (qExpCoeffNew N k (B i) n) • (B i)) ∧

      (∀ i, Module.finrank ℂ (Submodule.span ℂ ({B i} : Set (NewSubspaceCuspForm N k))) = 1) ∧

      (∀ i j, (∀ n : ℕ, qExpCoeffNew N k (B i) n = qExpCoeffNew N k (B j) n) → i = j) := by sorry

end HeckeNewformDecomposition
