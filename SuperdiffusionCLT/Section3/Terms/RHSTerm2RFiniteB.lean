/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2RBounds
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsF
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Analytic
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2RField
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2KmnBounds
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementPthMoment
public import SuperdiffusionCLT.Probability.OrliczPower
public import SuperdiffusionCLT.Frozen.Section3.WBasicRegbounds

/-!
# The response-field finiteness of `l.RHS.term2`

## Report first

This module discharges the finiteness hypothesis on `R` in `l.RHS.term2`
(the clause `hfinR` of its term-2 assembly): the finiteness of the annealed squared
`L̲²(cu_m)` norm of
`R = (k_{L'} − k_ℓ) ∇w`, together with the norm half of the printed display
`e.RHS.term2.R.bounds`.

The route is the printed derivation "Combining this with
`e.nablaw.Lt` and the product rule", and **both** of its inputs are theorems
needing no hypothesis beyond `d` and `2 ≤ d`:

* `Frozen.Section2.streamIncrement_scale_estimates`, used through the
  normalized moment display
  `isBigOWith_gammaSigma_finiteShellIncrementPthMoment` at `p = 4`;
* `Frozen.Section3.w_basic_regbounds` (`e.nablaw.Lt`), used through its first
  clause at the amplitude `C|p| h^{1/2}`.

The one structural point is that the *sample-measurability* of the response
density `ω ↦ ‖∇w(ω)‖_{L̲⁴(cu_m)}` — which a route through the cube densities would carry
as a hypothesis `hWGa`, and which is not proved anywhere in the development — is **not needed**.
Hölder `(4,4) → 2` on the cube bounds the transported field by
`‖k_{L'} − k_ℓ‖_{L̲⁴} · ‖∇w‖_{L̲⁴}`; the second factor is then dominated
pointwise in the sample by the *measurable* tail witness `Z` of
`w_basic_regbounds`, and Cauchy–Schwarz `(2,2)` in the sample is applied with the
measurable pair `(ofReal ∘ Z_K, ofReal ∘ Z_W)` instead of the pair of cube norms.
Every step is therefore a computation on measurable functions.

## Main results

* `annealed_ofReal_pow_ne_top_of_gammaSigma` — a one-sided `Γ_σ` tail gives finiteness
  of the annealed integral of `ENNReal.ofReal Y ^ n`, with no positivity condition on the
  amplitude (through `IsBigOWith.mono_scale` at `max K 1`);
* `lintegral_sq_ne_top_of_tails` — the Cauchy–Schwarz step in the sample with
  one **non-measurable** factor;
* `term2_hfinR` — `hfinR` with **no** carried hypothesis beyond the standing
  shell laws, `d`, `2 ≤ d`, the scale ordering, and `w` with its defining
  `IsDirichletResponse` property.

## References

* The paper: `l.RHS.term2`, `e.RHS.term2.R.bounds`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Probability
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Finiteness from a one-sided `Γ_σ` tail -/

/-- **Finiteness of an annealed moment from a one-sided `Γ_σ` tail.**  At every
natural exponent `n ≥ 1` the annealed integral of `(ENNReal.ofReal ∘ Y)ⁿ` is
finite, because the growth display gives `Integrable (Y ^ p)` for
`p = n`. -/
theorem lintegral_ofReal_pow_ne_top_of_isBigOWith_gammaSigma {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
    {sigma K : ℝ} (hsigma : 0 < sigma) (hK : 0 < K) {Y : Omega → ℝ}
    (hYnn : ∀ omega : Omega, 0 ≤ Y omega) (hYm : AEMeasurable Y mu)
    (hY : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y K)
    {n : ℕ} (hn : 1 ≤ n) :
    (∫⁻ omega : Omega, ENNReal.ofReal (Y omega) ^ n ∂mu) ≠ ⊤ := by
  have hp : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp0 : (0 : ℝ) ≤ (n : ℝ) := le_trans zero_le_one hp
  have hgrowth := IndependentSums.hasGammaMomentGrowthWith_of_isBigOWith_gammaSigma
    (μ := mu) (Y := Y) (K := K) (σ := sigma) hsigma hK hYnn hYm hY
  have hstep := (IndependentSums.hasGammaMomentGrowthWith_iff_of_nonneg
    (μ := mu) (σ := sigma) (M := IndependentSums.gammaMomentConst sigma * K)
    (Y := Y) hYnn).1 hgrowth hp
  obtain ⟨hint, -⟩ := hstep
  have hcongr : (fun omega : Omega => ENNReal.ofReal (Y omega) ^ n) =
      fun omega : Omega => ENNReal.ofReal (Y omega ^ (n : ℝ)) := by
    funext omega
    have h1 : ENNReal.ofReal (Y omega) ^ n = ENNReal.ofReal (Y omega) ^ (n : ℝ) :=
      (ENNReal.rpow_natCast (ENNReal.ofReal (Y omega)) n).symm
    have h2 : ENNReal.ofReal (Y omega) ^ (n : ℝ) = ENNReal.ofReal (Y omega ^ (n : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (hYnn omega) hp0
    exact h1.trans h2
  rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hYnn omega) (n : ℝ))]
  exact ENNReal.ofReal_ne_top

/-- **Amplitude-unconstrained finiteness from a one-sided `Γ_σ` tail.**  The
same conclusion as `lintegral_ofReal_pow_ne_top_of_isBigOWith_gammaSigma`, with
no side condition on the amplitude `K`: monotonicity of `IsBigOWith` in the
amplitude (`IsBigOWith.mono_scale`) replaces `K` by `max K 1`, which is
positive.  This is the form in which the printed amplitudes of `e.nablaw.Lt`
enter, where `K = C|p| h^{1/2}` and the positivity of `C` and of `|p|` would
otherwise have to be extracted separately. -/
theorem annealed_ofReal_pow_ne_top_of_gammaSigma {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {sigma : ℝ} (hsigma : 0 < sigma)
    {Y : Omega → ℝ} (hYnn : ∀ omega : Omega, 0 ≤ Y omega) (hYm : AEMeasurable Y mu)
    (K : ℝ) (hY : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y K)
    {n : ℕ} (hn : 1 ≤ n) :
    (∫⁻ omega : Omega, ENNReal.ofReal (Y omega) ^ n ∂mu) ≠ ⊤ :=
  lintegral_ofReal_pow_ne_top_of_isBigOWith_gammaSigma hsigma
    (lt_of_lt_of_le zero_lt_one (le_max_right K 1)) hYnn hYm
    (hY.mono_scale (le_max_left K 1)) hn

/-! ## Elementary `ℝ≥0∞` comparisons -/

/-- The fourth root step: `x ^ 4 ≤ y` implies `x ^ 2 ≤ y ^ (1/2)`. -/
private theorem sq_le_rpow_half_of_pow_four_le {x y : ℝ≥0∞} (h : x ^ (4 : ℕ) ≤ y) :
    x ^ (2 : ℕ) ≤ y ^ ((1 : ℝ) / 2) := by
  have hbase : (x ^ (4 : ℕ)) ^ ((1 : ℝ) / 2) = (x ^ (4 : ℝ)) ^ ((1 : ℝ) / 2) :=
    congrArg (fun t : ℝ≥0∞ => t ^ ((1 : ℝ) / 2)) (ENNReal.rpow_natCast x 4).symm
  have h2 : x ^ (2 : ℝ) = (x ^ (4 : ℝ)) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_mul]
    norm_num
  calc x ^ (2 : ℕ) = x ^ (2 : ℝ) := (ENNReal.rpow_natCast x 2).symm
    _ = (x ^ (4 : ℝ)) ^ ((1 : ℝ) / 2) := h2
    _ = (x ^ (4 : ℕ)) ^ ((1 : ℝ) / 2) := hbase.symm
    _ ≤ y ^ ((1 : ℝ) / 2) := ENNReal.rpow_le_rpow h (by norm_num)

/-- The square-root envelope: `y ^ (1/2) ≤ 1 + y` for every `y : ℝ≥0∞`. -/
private theorem rpow_half_le_one_add (y : ℝ≥0∞) : y ^ ((1 : ℝ) / 2) ≤ 1 + y := by
  rcases le_total y 1 with h | h
  · have h1 : y ^ ((1 : ℝ) / 2) ≤ (1 : ℝ≥0∞) ^ ((1 : ℝ) / 2) :=
      ENNReal.rpow_le_rpow h (by norm_num)
    rw [ENNReal.one_rpow] at h1
    exact h1.trans le_self_add
  · have h1 : y ^ ((1 : ℝ) / 2) ≤ y ^ (1 : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_le h (by norm_num)
    rw [ENNReal.rpow_one] at h1
    exact h1.trans le_add_self

/-! ## Cauchy-Schwarz with one non-measurable factor -/

/-- **Finiteness of an annealed `L²` root from two `Γ`-tails.**  A nonnegative
quantity `N` dominated pointwise by a product `A · B` has finite annealed second
moment as soon as `A²` and `B²` are dominated by the `ofReal` of two measurable
witnesses with finite moments — **no measurability of `A` or `B` is required**.

The route is the elementary domination `A²B² ≤ (1 + Z_K) Z_W²` (from
`A ^ 4 ≤ ofReal Z_K` through `sq_le_rpow_half_of_pow_four_le` and
`rpow_half_le_one_add`), followed by Cauchy-Schwarz `(2,2)` in the sample on the
two **measurable** factors `ofReal ∘ Z_K` and `(ofReal ∘ Z_W)²`.  This avoids
the sample-measurability of a cube `L̲⁴` norm of the response density, which the
section hypotheses do not give: the density is replaced by its measurable tail
witness. -/
theorem lintegral_sq_ne_top_of_tails {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {N A B : Omega → ℝ≥0∞} {ZK ZW : Omega → ℝ}
    (hZKm : AEMeasurable ZK mu) (hZWm : AEMeasurable ZW mu)
    (hN : ∀ omega : Omega, N omega ≤ A omega * B omega)
    (hA4 : ∀ omega : Omega, A omega ^ (4 : ℕ) ≤ ENNReal.ofReal (ZK omega))
    (hBle : ∀ omega : Omega, B omega ≤ ENNReal.ofReal (ZW omega))
    (hZK2 : (∫⁻ omega : Omega, ENNReal.ofReal (ZK omega) ^ (2 : ℕ) ∂mu) ≠ ⊤)
    (hZW2 : (∫⁻ omega : Omega, ENNReal.ofReal (ZW omega) ^ (2 : ℕ) ∂mu) ≠ ⊤)
    (hZW4 : (∫⁻ omega : Omega, ENNReal.ofReal (ZW omega) ^ (4 : ℕ) ∂mu) ≠ ⊤) :
    (∫⁻ omega : Omega, N omega ^ (2 : ℕ) ∂mu) ≠ ⊤ := by
  have hX : AEMeasurable (fun omega : Omega => ENNReal.ofReal (ZK omega)) mu :=
    hZKm.ennreal_ofReal
  have hY : AEMeasurable (fun omega : Omega => ENNReal.ofReal (ZW omega)) mu :=
    hZWm.ennreal_ofReal
  have hY2 : AEMeasurable (fun omega : Omega => ENNReal.ofReal (ZW omega) ^ (2 : ℕ)) mu :=
    hY.pow_const 2
  have hpoint : ∀ omega : Omega, N omega ^ (2 : ℕ) ≤
      ENNReal.ofReal (ZW omega) ^ (2 : ℕ) +
        ENNReal.ofReal (ZK omega) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ) := by
    intro omega
    have hA2 : A omega ^ (2 : ℕ) ≤ 1 + ENNReal.ofReal (ZK omega) :=
      (sq_le_rpow_half_of_pow_four_le (hA4 omega)).trans (rpow_half_le_one_add _)
    have hB2 : B omega ^ (2 : ℕ) ≤ ENNReal.ofReal (ZW omega) ^ (2 : ℕ) :=
      pow_le_pow_left' (hBle omega) 2
    have hmul : A omega ^ (2 : ℕ) * B omega ^ (2 : ℕ) ≤
        (1 + ENNReal.ofReal (ZK omega)) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ) :=
      mul_le_mul' hA2 hB2
    have hdist : (1 + ENNReal.ofReal (ZK omega)) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ) =
        ENNReal.ofReal (ZW omega) ^ (2 : ℕ) +
          ENNReal.ofReal (ZK omega) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ) := by
      rw [add_mul, one_mul]
    calc N omega ^ (2 : ℕ) ≤ (A omega * B omega) ^ (2 : ℕ) := pow_le_pow_left' (hN omega) 2
      _ = A omega ^ (2 : ℕ) * B omega ^ (2 : ℕ) := mul_pow _ _ 2
      _ ≤ (1 + ENNReal.ofReal (ZK omega)) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ) := hmul
      _ = ENNReal.ofReal (ZW omega) ^ (2 : ℕ) +
            ENNReal.ofReal (ZK omega) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ) := hdist
  have hconj : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    exact ⟨by norm_num, by norm_num⟩
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq mu hconj hX hY2
  have hg4 : (∫⁻ omega : Omega,
        (fun o : Omega => ENNReal.ofReal (ZW o) ^ (2 : ℕ)) omega ^ (2 : ℝ) ∂mu) =
      ∫⁻ omega : Omega, ENNReal.ofReal (ZW omega) ^ (4 : ℕ) ∂mu := by
    refine lintegral_congr fun omega => ?_
    show (ENNReal.ofReal (ZW omega) ^ (2 : ℕ)) ^ (2 : ℝ) =
      ENNReal.ofReal (ZW omega) ^ (4 : ℕ)
    have h1 : (ENNReal.ofReal (ZW omega) ^ (2 : ℕ)) ^ (2 : ℝ) =
        (ENNReal.ofReal (ZW omega) ^ (2 : ℝ)) ^ (2 : ℝ) :=
      congrArg (fun t : ℝ≥0∞ => t ^ (2 : ℝ))
        (ENNReal.rpow_natCast (ENNReal.ofReal (ZW omega)) 2).symm
    have h2 : (ENNReal.ofReal (ZW omega) ^ (2 : ℝ)) ^ (2 : ℝ) =
        ENNReal.ofReal (ZW omega) ^ (4 : ℕ) := by
      rw [← ENNReal.rpow_mul,
        show (2 : ℝ) * 2 = (4 : ℝ) by norm_num]
      exact ENNReal.rpow_natCast (ENNReal.ofReal (ZW omega)) 4
    exact h1.trans h2
  have hf2 : (∫⁻ omega : Omega,
        (fun o : Omega => ENNReal.ofReal (ZK o)) omega ^ (2 : ℝ) ∂mu) =
      ∫⁻ omega : Omega, ENNReal.ofReal (ZK omega) ^ (2 : ℕ) ∂mu := by
    refine lintegral_congr fun omega => ?_
    show ENNReal.ofReal (ZK omega) ^ (2 : ℝ) = ENNReal.ofReal (ZK omega) ^ (2 : ℕ)
    exact ENNReal.rpow_natCast (ENNReal.ofReal (ZK omega)) 2
  have hXY : (∫⁻ omega : Omega, ENNReal.ofReal (ZK omega) *
        ENNReal.ofReal (ZW omega) ^ (2 : ℕ) ∂mu) ≤
      (∫⁻ omega : Omega, ENNReal.ofReal (ZK omega) ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) *
        (∫⁻ omega : Omega, ENNReal.ofReal (ZW omega) ^ (4 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) := by
    refine hholder.trans (le_of_eq ?_)
    rw [hf2, hg4]
  have hsplit : (∫⁻ omega : Omega, ENNReal.ofReal (ZW omega) ^ (2 : ℕ) +
        ENNReal.ofReal (ZK omega) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ) ∂mu) =
      (∫⁻ omega : Omega, ENNReal.ofReal (ZW omega) ^ (2 : ℕ) ∂mu) +
        ∫⁻ omega : Omega, ENNReal.ofReal (ZK omega) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ) ∂mu :=
    lintegral_add_left' hY2 _
  have hmain : (∫⁻ omega : Omega, N omega ^ (2 : ℕ) ∂mu) ≤
      (∫⁻ omega : Omega, ENNReal.ofReal (ZW omega) ^ (2 : ℕ) ∂mu) +
        (∫⁻ omega : Omega, ENNReal.ofReal (ZK omega) ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) *
          (∫⁻ omega : Omega, ENNReal.ofReal (ZW omega) ^ (4 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) := by
    refine (lintegral_mono hpoint).trans ?_
    rw [hsplit]
    exact add_le_add le_rfl hXY
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hZW2, ENNReal.mul_ne_top ?_ ?_⟩) hmain
  · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hZK2
  · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hZW4

/-! ## `hfinR` with no response-density clause -/

/-- **`hfinR` with no carried response-density hypothesis.**

The transported field `R = (k_{L'} − k_ℓ) ∇w` has a finite annealed
squared `L̲²(cu_m)` norm, with **no** hypothesis beyond the standing shell laws
`ShellLawPrefix`, `ShellLawJ1Restriction`, `ShellLawJ2`, `ShellLawJ3`, `ShellLawJ4`, the
dimension hypotheses `d` and `2 ≤ d`, the scale ordering `ScalesOrdering S`, and
the response `w` with its defining property `IsDirichletResponse`.

The three witnesses of the proof are named:

* `KN omega x = ‖(k_{L'} − k_ℓ)(x)‖_op` — the operator norm of the canonical
  stream increment `finiteShellIncrement omega S.ell S.LPrime`, the density `K`
  of the printed product rule;
* `ZW omega = |Z omega|` — the absolute value of the **measurable** tail witness
  `Z` of the first clause of
  `Frozen.Section3.w_basic_regbounds` (`e.nablaw.Lt`), i.e. the `Γ₂` witness for
  `‖∇w‖_{L̲⁸(cu_m)}`;
* `ZK omega = ⨍_{cu_m} ‖(k_{L'} − k_ℓ)(x)‖_op⁴ dx` — the normalized cube average
  of the fourth power of `KN`, the `Γ_{1/2}` witness of the stream
  increment moment display `e.kmn.bounds`
  (`isBigOWith_gammaSigma_finiteShellIncrementPthMoment` at `p = 4`).

The route is the same product rule as the printed derivation —
Hölder `(4,4) → 2` on the cube, then Cauchy–Schwarz `(2,2)` in the sample — but
the sample pairing is applied to the two **measurable** witnesses `ofReal ∘ ZK`
and `ofReal ∘ ZW` rather than to the two cube norms.  The cube Hölder step
(`cubeLpENorm_two_le_mul_four`) is the only place where the two densities
appear, and it needs no measurability in `omega`: it is a pointwise inequality
per sample.  Consequently a clause `hWGa` —
sample-measurability of the cube `L̲⁴` norm of `ω ↦ ‖∇w(ω)‖` — is **not needed**.

The one cube-`L̲⁴` domination used is
`cubeLpENorm_four_le_ofReal_volumeAverage` at the continuous field
`matrixOperatorNorm ∘ finiteShellIncrement omega S.ell S.LPrime`, whose
`omega`-measurability is
`aemeasurable_volumeAverage_rpow_matrixOperatorNorm_finiteShellIncrement`; the
response density `‖∇w‖` enters only through
`cubeLpENorm_mono_exponent` from its `L̲⁸(cu_m)` clause, whose `omega`-
measurability is likewise not required. -/
theorem term2_hfinR (d : ℕ) [NeZero d] (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (e : Vec d) (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                (coefficientCutoff nu omega S.ell).toCoeffField y)
              ((w omega).toH1Function.grad y)) ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ := by
  -- the scale ordering: `ℓ < L'` so that the increment is a genuine shell sum
  have hnm : S.ell < S.LPrime := by
    have h1 := hSorder.ell_lt_ellPrime
    have h2 := hSorder.ellPrime_lt_m
    have h3 : S.LPrime = S.m + 2 * S.a := S.LPrime_eq
    omega
  -- the response anchor `e.nablaw.Lt`, first clause
  obtain ⟨Cwb, _hCwb, hClauses⟩ :=
    SuperdiffusionCLT.Frozen.Section3.w_basic_regbounds d hd
  obtain ⟨hGradClause, -⟩ := hClauses nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he
    (testVector nu S.LPrime P S.n e) rfl w hw
  obtain ⟨Zw, hZwm, hZwO, hZwdom⟩ := hGradClause
  -- the increment witness `ZK` and its finiteness
  have hZKm : AEMeasurable (fun omega : ShellSeq d =>
      volumeAverage (cubeSet (originCube d (S.m : ℤ))) (fun x : Vec d =>
        matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) ^ (4 : ℝ)))
      P.toMeasure :=
    aemeasurable_volumeAverage_rpow_matrixOperatorNorm_finiteShellIncrement P S.ell S.LPrime
      (by norm_num : (0 : ℝ) ≤ (4 : ℝ)) (originCube d (S.m : ℤ))
  have hZKnn : ∀ omega : ShellSeq d, 0 ≤ volumeAverage (cubeSet (originCube d (S.m : ℤ)))
      (fun x : Vec d =>
        matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) ^ (4 : ℝ)) :=
    fun omega => SuperdiffusionCLT.Section2.Norms.volumeAverage_cubeSet_nonneg _
      (fun x => Real.rpow_nonneg (matrixOperatorNorm_nonneg _) 4)
  have hprov := isBigOWith_gammaSigma_finiteShellIncrementPthMoment (P := P) hPrefix hJ2 hJ3 hJ4
    (p := (4 : ℝ)) (by norm_num) hnm (originCube d (S.m : ℤ))
  rw [show ((2 : ℝ) / 4) = ((1 : ℝ) / 2) from by norm_num] at hprov
  have hZK2 : (∫⁻ omega : ShellSeq d,
      ENNReal.ofReal (volumeAverage (cubeSet (originCube d (S.m : ℤ))) (fun x : Vec d =>
        matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) ^ (4 : ℝ))) ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ :=
    annealed_ofReal_pow_ne_top_of_gammaSigma (mu := P.toMeasure) (sigma := ((1 : ℝ) / 2))
      (by norm_num) hZKnn hZKm _
      (by simpa only using hprov) (by norm_num : 1 ≤ 2)
  -- the response witness and its two finitenesses
  have hZwnn : ∀ omega : ShellSeq d, 0 ≤ |Zw omega| := fun omega => abs_nonneg _
  have hZwabsm : AEMeasurable (fun omega : ShellSeq d => |Zw omega|) P.toMeasure :=
    Measurable.comp_aemeasurable continuous_abs.measurable hZwm.aemeasurable
  have hZw2 : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (|Zw omega|) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤ :=
    annealed_ofReal_pow_ne_top_of_gammaSigma (mu := P.toMeasure) (sigma := 2)
      (by norm_num) hZwnn hZwabsm _ hZwO (by norm_num : 1 ≤ 2)
  have hZw4 : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (|Zw omega|) ^ (4 : ℕ) ∂P.toMeasure) ≠ ⊤ :=
    annealed_ofReal_pow_ne_top_of_gammaSigma (mu := P.toMeasure) (sigma := 2)
      (by norm_num) hZwnn hZwabsm _ hZwO (by norm_num : 1 ≤ 4)
  have hZw2' : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (Zw omega) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤ :=
    ne_top_of_le_ne_top hZw2 (lintegral_mono fun omega =>
      pow_le_pow_left' (ENNReal.ofReal_le_ofReal (le_abs_self _)) 2)
  have hZw4' : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (Zw omega) ^ (4 : ℕ) ∂P.toMeasure) ≠ ⊤ :=
    ne_top_of_le_ne_top hZw4 (lintegral_mono fun omega =>
      pow_le_pow_left' (ENNReal.ofReal_le_ofReal (le_abs_self _)) 4)
  -- cube measurability of the response density `|∇w|`
  have hWGhm : ∀ omega : ShellSeq d, AEStronglyMeasurable
      (hilbertifyVecField ((w omega).toH1Function.grad))
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
    intro omega
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact (memHilbertVectorL2_hilbertifyVecField
      ((w omega).toH1Function.grad_memVectorL2)).aestronglyMeasurable.smul_measure _
  have hWGm : ∀ omega : ShellSeq d, AEStronglyMeasurable
      (fun x : Vec d => vecNorm ((w omega).toH1Function.grad x))
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
    intro omega
    have h1 := hWGhm omega
    rw [show (fun x : Vec d => vecNorm ((w omega).toH1Function.grad x)) =
        (fun x : Vec d => ‖hilbertifyVecField ((w omega).toH1Function.grad) x‖) from
      funext fun x => (norm_hilbertifyVecField_apply _ x).symm]
    exact h1.norm
  -- the pointwise `L̲⁸ ⊆ L̲⁴` domination of the response density by `ZW`
  have hBle : ∀ omega : ShellSeq d, cubeLpENorm (originCube d (S.m : ℤ)) 4
      (fun x : Vec d => vecNorm ((w omega).toH1Function.grad x)) ≤ ENNReal.ofReal (Zw omega) := by
    intro omega
    refine (cubeLpENorm_mono_exponent (originCube d (S.m : ℤ))
      (show (4 : ℝ≥0∞) ≤ 8 by norm_num) (hWGm omega)).trans ?_
    rw [cubeLpENorm_vecNorm_eq_vecCubeLpENorm _ _ _ (hWGhm omega)]
    exact hZwdom omega
  -- the fourth-power domination of the increment density by `ZK`
  have hA4 : ∀ omega : ShellSeq d, cubeLpENorm (originCube d (S.m : ℤ)) 4
      (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x)) ^
        (4 : ℕ) ≤ ENNReal.ofReal (volumeAverage (cubeSet (originCube d (S.m : ℤ)))
      (fun x : Vec d =>
        matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) ^ (4 : ℝ))) :=
    fun omega => cubeLpENorm_four_le_ofReal_volumeAverage (originCube d (S.m : ℤ))
      (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x))
      (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x))
      (fun x => matrixOperatorNorm_nonneg _)
      ((continuous_matrixOperatorNorm_finiteShellIncrement omega S.ell S.LPrime).aestronglyMeasurable)
      (fun x => le_rfl)
      (fun x => matrixOperatorNorm_nonneg _)
      (continuous_matrixOperatorNorm_finiteShellIncrement omega S.ell S.LPrime)
  -- Hölder `(4,4) → 2` on the cube at the canonical increment density
  have hN : ∀ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
      (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
          (coefficientCutoff nu omega S.ell).toCoeffField y)
        ((w omega).toH1Function.grad y)) ≤
      cubeLpENorm (originCube d (S.m : ℤ)) 4
          (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x)) *
        cubeLpENorm (originCube d (S.m : ℤ)) 4
          (fun x : Vec d => vecNorm ((w omega).toH1Function.grad x)) := by
    intro omega
    have h := cubeLpENorm_two_le_mul_four (Q := originCube d (S.m : ℤ))
      (f := hilbertifyVecField (fun y : Vec d => matVecMul
        ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
          (coefficientCutoff nu omega S.ell).toCoeffField y)
        ((w omega).toH1Function.grad y)))
      (u := fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x))
      (v := fun x : Vec d => vecNorm ((w omega).toH1Function.grad x))
      (fun x => matrixOperatorNorm_nonneg _) (fun x => vecNorm_nonneg _)
      ((continuous_matrixOperatorNorm_finiteShellIncrement omega S.ell S.LPrime).aestronglyMeasurable)
      (hWGm omega)
      (aestronglyMeasurable_hilbertifyVecField_matVecMul
        ((continuous_coefficientCutoff_apply nu omega S.LPrime).sub
          (continuous_coefficientCutoff_apply nu omega S.ell)) (hWGhm omega))
      (fun x => by
        have hpt := vecNorm_matVecMul_coefficientCutoff_sub_le nu S.LPrime S.ell omega
          ((w omega).toH1Function.grad) x
        rw [coefficientCutoff_toCoeffField_sub_streamCutoff nu omega S.ell S.LPrime x,
          ← finiteShellIncrement_apply_eq_streamCutoff_sub omega hnm.le x] at hpt
        rw [norm_hilbertifyVecField_apply,
          coefficientCutoff_toCoeffField_sub_streamCutoff nu omega S.ell S.LPrime x,
          ← finiteShellIncrement_apply_eq_streamCutoff_sub omega hnm.le x]
        exact hpt)
    simpa only [vecCubeLpENorm] using h
  -- Cauchy-Schwarz in the sample on the two measurable witnesses
  exact lintegral_sq_ne_top_of_tails (mu := P.toMeasure)
    (N := fun omega : ShellSeq d => vecCubeLpENorm (originCube d (S.m : ℤ)) 2
      (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
          (coefficientCutoff nu omega S.ell).toCoeffField y) ((w omega).toH1Function.grad y)))
    (A := fun omega : ShellSeq d => cubeLpENorm (originCube d (S.m : ℤ)) 4
      (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x)))
    (B := fun omega : ShellSeq d => cubeLpENorm (originCube d (S.m : ℤ)) 4
      (fun x : Vec d => vecNorm ((w omega).toH1Function.grad x)))
    (ZK := fun omega : ShellSeq d => volumeAverage (cubeSet (originCube d (S.m : ℤ)))
      (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) ^ (4 : ℝ)))
    (ZW := Zw) hZKm hZwm.aemeasurable hN hA4 hBle hZK2 hZw2' hZw4'

end

end SuperdiffusionCLT.Section3.Terms
