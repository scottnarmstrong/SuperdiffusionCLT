/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT1
public import SuperdiffusionCLT.Probability.OrliczTriangle
public import SuperdiffusionCLT.Probability.OrliczProduct
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Probability.ConditionalGammaTailShell

/-!
# The two printed moment averages of the first summand `T1`
`localizationAverage_T1_of_grid` reduces the
first printed summand of `e.localization.average.oneshot` to exactly two carried
`Γ` bounds, its hypotheses `hD2bound` and `hB2bound`:

* the **second-moment average** of the localization error,
  `avsum_z D_z² = O_{Γ_{1/2}}(Cν⁻⁴3^{-2(ℓ-n)})`, whose per-cube input
  is `D_z ≤ O_{Γ_1}(Cν⁻²3^{-(ℓ-n)})`;
* the **fourth-moment average** of the perturbed gauge vectors,
  `avsum_z |bfA_ℓ^{1/2}(z+cu_n)G_{-h_z}P|⁴ = O_{Γ_{1/4}}(Cν⁻²((1∨ℓ)²+(L-ℓ)²)|P|⁴)`,
  whose per-cube inputs
  are `Y_z² ≤ O_{Γ_{1/2}}(C)` and
  `R_z ≤ O_{Γ_{1/2}}(Cν⁻²((1∨ℓ)²+(L-ℓ)²)|P|⁴)`, with
  `Y_z := |bfE_ℓ^{-1/2}bfA_ℓ(z+cu_n)bfE_ℓ^{-1/2}|` and
  `R_z := |bfE_ℓ^{1/2}G_{-h_z}P|⁴`.

## Main results

Both averages are derived here from their printed per-cube inputs, so the two
hypotheses of `localizationAverage_T1_of_grid` are no longer opaque: what remains
are the per-cube `Γ` bounds themselves.

* `localizationAverageT1CubeAmplitude`: the per-cube amplitude `Cν⁻²3^{-(ℓ-n)}`.
* `localizationAverageT1_secondMoment_of_cube_bounds`: from per-cube
  `D_z = O_{Γ_1}(Cν⁻²3^{-(ℓ-n)})`, nonnegativity, measurability, and
  the vanishing at `L = ℓ`, the normalized average of the squares is
  `O_{Γ_{1/2}}(γ_{1/2}C²ν⁻⁴3^{-2(ℓ-n)})` --- the printed display
  with its constant named.  The two steps are the printed ones: the power rule
  `e.powerofGammasigma` at `p = 2` (available as
  `Probability.isBigO_gammaSigma_rpow_fwd`) followed by the generalized triangle
  inequality `e.Gamma.sigma.triangle` in its *normalized* finite-average form
  (`IndependentSums.isBigO_finsetAverage_of_isBigO_gammaSigma`, whose
  constant at `σ = 1/2` is `gammaTriangleConst (1/2)`).
* `localizationAverageT1_fourthMoment_of_factor_bounds`: from the printed
  per-cube bounds on `Y_z²` and `R_z`, the pointwise domination
  `|bfA_ℓ^{1/2}(z+cu_n)G_{-h_z}P|⁴ ≤ Y_z² R_z`, nonnegativity and
  measurability, the normalized average of the fourth powers is `O_{Γ_{1/4}}` at
  the product amplitude.  Here the printed route conditions on `F_>` and uses the
  conditional generalized triangle inequality before the
  multiplication property `e.multGammasig`; the two factors of
  *each* summand are separately bounded, so the multiplication property
  (which needs no independence of its two factors) applies per cube, and the
  normalized finite-average triangle inequality at `σ = 1/4` performs the sum.
  The index is the printed `1/4` and the amplitude the printed one.

## Why no conditioning is needed here

An end-to-end conditional tool, such as the one that closed the concentration residual of `T2`,
would require each summand to be measurable for the coordinate family *complementary* to the
conditioning one.  Neither summand here is: `D_z²` is a functional of the whole
finite shell increment `(k_L − k_ℓ)`, and the fourth-power summand
`|bfA_ℓ^{1/2}(z+cu_n)G_{-h_z}P|⁴` is a *product* `Y_z² R_z` of a lower-coordinate
and an upper-coordinate factor, so it is measurable for neither family alone.
Such a tool therefore does not apply, and the concentration route is not needed: the
printed per-cube bounds already carry the `Γ` rates, and the multiplication
property performs the combine.

## The `ν` power of the first summand

`localizationAverageEnvelopeT1` carries `ν⁻³`, and that is what the paper states:
`Cν⁻³` appears in the display `e.localization.average.oneshot`, whose first summand is
`1_{L>ℓ}L3^{-(ℓ-n)}`, and again in the conclusion of the Cauchy--Schwarz
step.  The two intermediate amplitudes carry `ν⁻⁴` and `ν⁻²`,
whose geometric mean is `ν⁻³`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## The degenerate tail bound -/

/-- A random variable that vanishes pointwise obeys every `Γ_σ` tail bound at
amplitude `0`. -/
private theorem isBigO_gammaSigma_of_forall_eq_zero
    {mu : MeasureTheory.Measure (ShellSeq d)} {X : ShellSeq d → ℝ} {sigma : ℝ}
    (hX : ∀ omega, X omega = 0) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma) X 0 := by
  intro t _ht
  have hset : IndependentSums.upperTailEvent (fun omega : ShellSeq d => |X omega|) (0 * t) =
      (∅ : Set (ShellSeq d)) := by
    ext omega
    simp only [IndependentSums.mem_upperTailEvent, Set.mem_empty_iff_false, zero_mul, hX omega,
      abs_zero, lt_self_iff_false]
  rw [hset]
  rw [MeasureTheory.Measure.real, measure_empty, ENNReal.toReal_zero]
  exact inv_nonneg.mpr (by
    simpa only [IndependentSums.gammaSigma_apply] using (Real.exp_pos (t ^ sigma)).le)

/-! ## The per-cube amplitude of the localization error -/

/-- The per-cube amplitude of the localization error,
`Cν⁻²3^{-(ℓ-n)}`: the right-hand side of the pointwise estimate
`D_z ≤ O_{Γ_1}(Cν⁻²3^{-(ℓ-n)})` obtained from the deterministic comparison
`e.localization.average.Dz` by stationarity and
`e.nabla.kmn.Linfty`. -/
noncomputable def localizationAverageT1CubeAmplitude (C nu : ℝ) (l n : ℕ) : ℝ :=
  C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ))

/-- The per-cube amplitude of the localization error is positive. -/
theorem localizationAverageT1CubeAmplitude_pos {C nu : ℝ} (hC : 0 < C) (hnu : 0 < nu)
    (l n : ℕ) : 0 < localizationAverageT1CubeAmplitude C nu l n := by
  unfold localizationAverageT1CubeAmplitude
  exact mul_pos (mul_pos hC (Real.rpow_pos_of_pos hnu _))
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _)

/-! ## `(Cν⁻²3^{-(ℓ-n)})²` is the printed second-moment amplitude -/

/-- `(x^{-2})² = x^{-4}` for `x > 0`. -/
private theorem rpow_neg_two_sq_moments {x : ℝ} (hx : 0 < x) :
    (x ^ (-(2 : ℝ))) ^ 2 = x ^ (-(4 : ℝ)) := by
  rw [sq, ← Real.rpow_add hx, show -(2 : ℝ) + -(2 : ℝ) = -(4 : ℝ) by norm_num]

/-- `(x^{-a})² = x^{-(2a)}` for `x > 0`. -/
private theorem rpow_neg_sq_moments {x : ℝ} (hx : 0 < x) (a : ℝ) :
    (x ^ (-a)) ^ 2 = x ^ (-(2 * a)) := by
  rw [sq, ← Real.rpow_add hx, show -a + -a = -(2 * a) by ring]

/-- The square of the per-cube amplitude of the localization error is the printed
second-moment amplitude at the squared constant `C²`. -/
theorem localizationAverageT1CubeAmplitude_sq {C nu : ℝ} (hnu : 0 < nu) (l n : ℕ) :
    localizationAverageT1CubeAmplitude C nu l n ^ 2 =
      localizationAverageT1SecondAmplitude (C ^ 2) nu l n := by
  unfold localizationAverageT1CubeAmplitude localizationAverageT1SecondAmplitude
  rw [mul_pow, mul_pow, rpow_neg_two_sq_moments hnu,
    rpow_neg_sq_moments (by norm_num : (0 : ℝ) < 3)]

/-- A multiple of the square of the per-cube amplitude is the printed
second-moment amplitude at the corresponding multiple of the squared constant. -/
theorem localizationAverageT1SecondMoment_amplitude_eq {C nu : ℝ} (hnu : 0 < nu) (l n : ℕ)
    {K : ℝ} :
    K * localizationAverageT1CubeAmplitude C nu l n ^ 2 =
      localizationAverageT1SecondAmplitude (K * C ^ 2) nu l n := by
  rw [localizationAverageT1CubeAmplitude_sq hnu l n]
  unfold localizationAverageT1SecondAmplitude
  ring

/-! ## The second-moment average -/

/-- **The printed second-moment average of the localization error**, derived from
its per-cube input.  Let `Dd i` be the localization error `D_i` at the `i`-th cube
of the grid, pointwise nonnegative, measurable, and vanishing identically when
`L = ℓ`.  If each `D_i = O_{Γ_1}(Cν⁻²3^{-(ℓ-n)})`, then

`avsum_{i} D_i² = O_{Γ_{1/2}}(γ_{1/2}C²ν⁻⁴3^{-2(ℓ-n)})`

with `γ_{1/2} = gammaTriangleConst (1/2)`, which is the printed display
at the named constant.  The two printed steps are the power rule
`e.powerofGammasigma` at `p = 2` and the generalized triangle inequality
`e.Gamma.sigma.triangle` over the grid, in the normalized finite-average form that
carries the printed normalisation `N⁻¹` of `avsum`.

The hypotheses are exactly the printed input: the per-cube `Γ_1` bound
(`e.nabla.kmn.Linfty`), the nonnegativity and measurability of the
`D_i`, and the printed vanishing at `L = ℓ`.  The carriers `D_z`, `bfA_ℓ`, `h_z`
of `D_i` do not enter here, so `Dd` enters as a named family. -/
theorem localizationAverageT1_secondMoment_of_cube_bounds {C nu : ℝ} (hC : 0 < C)
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (l L n : ℕ)
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (Dd : ι → ShellSeq d → ℝ)
    (hDdnn : ∀ i ∈ s, ∀ omega, 0 ≤ Dd i omega)
    (hDdmeas : ∀ i ∈ s, Measurable (Dd i))
    (hDdzero : ¬ l < L → ∀ i ∈ s, ∀ omega, Dd i omega = 0)
    (hDd : ∀ i ∈ s, IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (Dd i) (localizationAverageT1CubeAmplitude C nu l n)) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 2))
      (fun omega => (s.card : ℝ)⁻¹ * ∑ i ∈ s, Dd i omega ^ 2)
      (localizationAverageT1SecondAmplitude
        (IndependentSums.gammaTriangleConst ((1 : ℝ) / 2) * C ^ 2) nu l n) := by
  by_cases hlL : l < L
  · have hApos : 0 < localizationAverageT1CubeAmplitude C nu l n :=
      localizationAverageT1CubeAmplitude_pos hC hnu l n
    have hsq : ∀ i ∈ s, IndependentSums.IsBigO P.toMeasure
        (IndependentSums.gammaSigma ((1 : ℝ) / 2))
        (fun omega => Dd i omega ^ 2) (localizationAverageT1CubeAmplitude C nu l n ^ 2) :=
      fun i hi => by
        have h := SuperdiffusionCLT.Probability.isBigO_gammaSigma_rpow_fwd
          (mu := P.toMeasure) (X := Dd i) (K := localizationAverageT1CubeAmplitude C nu l n)
          (σ := 1) (p := 2) (by norm_num) hApos.le (hDdnn i hi) (hDd i hi)
        simpa only [Real.rpow_two] using h
    have havg := IndependentSums.isBigO_finsetAverage_of_isBigO_gammaSigma
      (μ := P.toMeasure) s (σ := (1 : ℝ) / 2) (by norm_num) hs
      (fun i hi => pow_pos hApos 2) hsq (fun i hi => (hDdmeas i hi).pow_const 2)
    have hcard : (s.card : ℝ) ≠ 0 := by
      simp only [Nat.cast_ne_zero]
      exact Finset.card_ne_zero.mpr hs
    have hsum : ∑ i ∈ s, localizationAverageT1CubeAmplitude C nu l n ^ 2 =
        (s.card : ℝ) * localizationAverageT1CubeAmplitude C nu l n ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcardmul : (s.card : ℝ)⁻¹ *
        ((s.card : ℝ) * localizationAverageT1CubeAmplitude C nu l n ^ 2) =
        localizationAverageT1CubeAmplitude C nu l n ^ 2 := by
      rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
    have hAmp : IndependentSums.gammaTriangleConst ((1 : ℝ) / 2) *
          ((s.card : ℝ)⁻¹ * ∑ i ∈ s, localizationAverageT1CubeAmplitude C nu l n ^ 2) =
        localizationAverageT1SecondAmplitude
          (IndependentSums.gammaTriangleConst ((1 : ℝ) / 2) * C ^ 2) nu l n := by
      rw [hsum, hcardmul]
      exact localizationAverageT1SecondMoment_amplitude_eq hnu l n
    rw [hAmp] at havg
    exact havg
  · have hzero : ∀ omega, (s.card : ℝ)⁻¹ * ∑ i ∈ s, Dd i omega ^ 2 = 0 := by
      intro omega
      rw [Finset.sum_eq_zero (fun i hi => by rw [hDdzero hlL i hi omega]; norm_num), mul_zero]
    refine (isBigO_gammaSigma_of_forall_eq_zero (mu := P.toMeasure) (sigma := (1 : ℝ) / 2)
      hzero).mono_scale ?_
    exact localizationAverageT1SecondAmplitude_nonneg
      (mul_nonneg (IndependentSums.gammaTriangleConst_pos).le (sq_nonneg C)) hnu.le l n

/-! ## The fourth-moment average -/

/-- The printed per-cube amplitude of the fourth moment,
`Cν⁻²((1∨ℓ)² + (L-ℓ)²)|P|⁴`, is strictly positive as soon as `Pvec ≠ 0`: it is
exactly `localizationAverageT1FourthAmplitude`. -/
theorem localizationAverageT1FourthAmplitude_pos {C nu : ℝ} (hC : 0 < C) (hnu : 0 < nu)
    (l L : ℕ) {Pvec : BlockVec d} (hdot : 0 < blockVecDot Pvec Pvec) :
    0 < localizationAverageT1FourthAmplitude C nu l L Pvec := by
  unfold localizationAverageT1FourthAmplitude
  refine mul_pos (mul_pos (mul_pos hC (Real.rpow_pos_of_pos hnu _)) ?_) (pow_pos hdot 2)
  exact add_pos_of_pos_of_nonneg
    (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) (l : ℝ))) 2) (sq_nonneg _)

/-- **The printed fourth-moment average of the perturbed gauge vectors**, derived
from its per-cube inputs.  Let

* `Ysq i` be `Y_i² = |bfE_ℓ^{-1/2}bfA_ℓ(i+cu_n)bfE_ℓ^{-1/2}|²`, with the printed
  per-cube bound `Y_i² = O_{Γ_{1/2}}(KY)` (from
  `e.Enaught.vs.A.and.Ahom`),
* `R i` be `R_i = |bfE_ℓ^{1/2}G_{-h_i}P|⁴`, with the printed per-cube bound
  `R_i = O_{Γ_{1/2}}(CR ν⁻²((1∨ℓ)²+(L-ℓ)²)|P|⁴)` (from
  `e.jk.spatialavg`, `p.concentration`, `e.Enaught.mixing`),
* `Bd i` be `|bfA_ℓ^{1/2}(i+cu_n)G_{-h_i}P|²`, dominated pointwise by the product
  `Y_i² R_i`,

all pointwise nonnegative, with `Bd` measurable.  If `Pvec ≠ 0` (so the printed
amplitude is strictly positive) — or, in the degenerate case `Pvec = 0` (where the
amplitude vanishes), if the `Bd i` vanish identically — then

`avsum_i |bfA_ℓ^{1/2}(i+cu_n)G_{-h_i}P|⁴ = O_{Γ_{1/4}}(Cν⁻²((1∨ℓ)²+(L-ℓ)²)|P|⁴)`

at the constant `gammaTriangleConst (1/4) * orliczProductConst (1/2) (1/2) * (KY * CR)`,
with `B2 = avsum_i Bd i²` the normalized average.  The index is the printed `1/4`
and the amplitude the printed one.

The printed route conditions on `F_> = σ(j_r : r > ℓ)` and applies the conditional
generalized triangle inequality to the weighted average before the
multiplication property.  Because *each* summand factorises as a
product of a lower-coordinate and an upper-coordinate factor, the
multiplication property `Probability.isBigO_gammaSigma_mul` — which does not
require independence of its two factors — applies per cube, and the normalized
finite-average triangle inequality at `σ = 1/4` performs the sum; the result has
the printed index and amplitude.  The conditioning itself is not needed for the
rate; the conditional-layer variant below carries the printed conditional per-cube
bounds instead. -/
theorem localizationAverageT1_fourthMoment_of_factor_bounds {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (l L : ℕ) (Pvec : BlockVec d)
    {KY CR : ℝ} (hKY : 0 < KY) (hCR : 0 < CR)
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (Ysq R Bd : ι → ShellSeq d → ℝ)
    (hYnn : ∀ i ∈ s, ∀ omega, 0 ≤ Ysq i omega)
    (hRnn : ∀ i ∈ s, ∀ omega, 0 ≤ R i omega)
    (hBdmeas : ∀ i ∈ s, Measurable (Bd i))
    (hdom : ∀ i ∈ s, ∀ omega, Bd i omega ^ 2 ≤ Ysq i omega * R i omega)
    (hBdzero : blockVecDot Pvec Pvec = 0 → ∀ i ∈ s, ∀ omega, Bd i omega = 0)
    (hY : ∀ i ∈ s, IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 2))
      (Ysq i) KY)
    (hR : ∀ i ∈ s, IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 2))
      (R i) (localizationAverageT1FourthAmplitude CR nu l L Pvec)) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 4))
      (fun omega => (s.card : ℝ)⁻¹ * ∑ i ∈ s, Bd i omega ^ 2)
      (localizationAverageT1FourthAmplitude
        (IndependentSums.gammaTriangleConst ((1 : ℝ) / 4) *
          SuperdiffusionCLT.Probability.orliczProductConst ((1 : ℝ) / 2) ((1 : ℝ) / 2) *
          (KY * CR)) nu l L Pvec) := by
  by_cases hdot : blockVecDot Pvec Pvec = 0
  · have hzero : ∀ omega, (s.card : ℝ)⁻¹ * ∑ i ∈ s, Bd i omega ^ 2 = 0 := by
      intro omega
      rw [Finset.sum_eq_zero (fun i hi => by rw [hBdzero hdot i hi omega]; norm_num), mul_zero]
    refine (isBigO_gammaSigma_of_forall_eq_zero (mu := P.toMeasure) (sigma := (1 : ℝ) / 4)
      hzero).mono_scale ?_
    exact localizationAverageT1FourthAmplitude_nonneg
      (mul_nonneg (mul_nonneg (IndependentSums.gammaTriangleConst_pos).le
        (SuperdiffusionCLT.Probability.orliczProductConst_pos _ _).le)
        (mul_pos hKY hCR).le) hnu.le l L Pvec
  · have hAmpPos : 0 < localizationAverageT1FourthAmplitude CR nu l L Pvec :=
      localizationAverageT1FourthAmplitude_pos hCR hnu l L
        (lt_of_le_of_ne (SuperdiffusionCLT.Section2.Carriers.blockVecDot_self_nonneg Pvec)
          (Ne.symm hdot))
    have hprod : ∀ i ∈ s, IndependentSums.IsBigO P.toMeasure
        (IndependentSums.gammaSigma ((1 : ℝ) / 4))
        (fun omega => Bd i omega ^ 2)
        (SuperdiffusionCLT.Probability.orliczProductConst ((1 : ℝ) / 2) ((1 : ℝ) / 2) *
          (KY * localizationAverageT1FourthAmplitude CR nu l L Pvec)) := by
      intro i hi
      have hmul := SuperdiffusionCLT.Probability.isBigO_gammaSigma_mul
        (mu := P.toMeasure) (X₁ := Ysq i) (X₂ := R i) (A₁ := KY)
        (A₂ := localizationAverageT1FourthAmplitude CR nu l L Pvec)
        (σ₁ := (1 : ℝ) / 2) (σ₂ := (1 : ℝ) / 2) (by norm_num) (by norm_num)
        hKY.le hAmpPos.le (hY i hi) (hR i hi)
      rw [show (1 : ℝ) / 2 * ((1 : ℝ) / 2) / ((1 : ℝ) / 2 + (1 : ℝ) / 2) = (1 : ℝ) / 4
        by norm_num] at hmul
      refine hmul.of_abs_le (fun omega => ?_)
      rw [abs_of_nonneg (sq_nonneg (Bd i omega)),
        abs_of_nonneg (mul_nonneg (hYnn i hi omega) (hRnn i hi omega))]
      exact hdom i hi omega
    have havg := IndependentSums.isBigO_finsetAverage_of_isBigO_gammaSigma
      (μ := P.toMeasure) s (σ := (1 : ℝ) / 4) (by norm_num) hs
      (fun i hi => mul_pos
        (SuperdiffusionCLT.Probability.orliczProductConst_pos _ _) (mul_pos hKY hAmpPos))
      hprod (fun i hi => (hBdmeas i hi).pow_const 2)
    have hcard : (s.card : ℝ) ≠ 0 := by
      simp only [Nat.cast_ne_zero]
      exact Finset.card_ne_zero.mpr hs
    have hsum : ∑ i ∈ s, SuperdiffusionCLT.Probability.orliczProductConst ((1 : ℝ) / 2)
          ((1 : ℝ) / 2) * (KY * localizationAverageT1FourthAmplitude CR nu l L Pvec) =
        (s.card : ℝ) * (SuperdiffusionCLT.Probability.orliczProductConst ((1 : ℝ) / 2)
          ((1 : ℝ) / 2) * (KY * localizationAverageT1FourthAmplitude CR nu l L Pvec)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcardmul : (s.card : ℝ)⁻¹ *
        ((s.card : ℝ) * (SuperdiffusionCLT.Probability.orliczProductConst ((1 : ℝ) / 2)
          ((1 : ℝ) / 2) * (KY * localizationAverageT1FourthAmplitude CR nu l L Pvec))) =
        SuperdiffusionCLT.Probability.orliczProductConst ((1 : ℝ) / 2) ((1 : ℝ) / 2) *
          (KY * localizationAverageT1FourthAmplitude CR nu l L Pvec) := by
      rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
    have hAmp : IndependentSums.gammaTriangleConst ((1 : ℝ) / 4) *
          ((s.card : ℝ)⁻¹ * ∑ i ∈ s,
            SuperdiffusionCLT.Probability.orliczProductConst ((1 : ℝ) / 2) ((1 : ℝ) / 2) *
              (KY * localizationAverageT1FourthAmplitude CR nu l L Pvec)) =
        localizationAverageT1FourthAmplitude
          (IndependentSums.gammaTriangleConst ((1 : ℝ) / 4) *
            SuperdiffusionCLT.Probability.orliczProductConst ((1 : ℝ) / 2) ((1 : ℝ) / 2) *
            (KY * CR)) nu l L Pvec := by
      rw [hsum, hcardmul]
      unfold localizationAverageT1FourthAmplitude
      ring
    rw [hAmp] at havg
    exact havg

/-! ## The printed conditional per-cube bounds -/

end SuperdiffusionCLT.Section2.Localization
