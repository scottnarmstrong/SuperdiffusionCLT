/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Moment bounds for a general AK.HC weak-Orlicz tail class

This file proves the AK.HC Theorem 6.1 port's package A3, item (1): for a
**general** Orlicz function `Ψ : ℝ → ℝ` — not only the stretched-exponential
`gammaSigma` class already handled elsewhere in this development
(`Homogenization.Probability.IndependentSums.PsiCalculus`'s `AdmissiblePsi`) —
satisfying

* the normalization `∀ t ≥ 0, 1 ≤ Ψ t`, and
* the AK.HC growth condition, exactly the shape carried by the
  `(P3')` block of `SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`
  (both clauses match verbatim, `Psi`/`PsiS`):
  `∀ p, 1 < p → p ≤ pΨ → ∀ t s, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ K ^ (3 * ⌈p⌉₊ ^ 2) * (Ψ (t * s) / Ψ t)`,

a random variable `X` with `IsBigO P Ψ X A`
(`Homogenization.IndependentSums.IsBigO`, i.e. `P[|X| > tA] ≤ Ψ(t)⁻¹` for
every `t ≥ 1`) has finite moments

`E |X| ^ q ≤ (p / (p - q)) * K ^ (3 * ⌈p⌉₊ ^ 2) * A ^ q`

for every `1 ≤ q < p ≤ pΨ`.

## Proof strategy

The growth condition, evaluated at the fixed argument `t := 1` together with
the normalization `1 ≤ Ψ 1`, turns into a bare power-law tail bound

`(Ψ s)⁻¹ ≤ K ^ (3 * ⌈p⌉₊ ^ 2) * s ^ (-p)`  for `s ≥ 1`

(`akhc_inv_psi_le_of_growth`). This is the only place the normalization is
used, and it needs no monotonicity hypothesis on `Ψ` at all: the AK.HC
`StrictMonoOn Psi (Set.Ici 0)` hypothesis of `(P3')` is never consulted here.
Composed with `IsBigO P Ψ X A` this gives the Pareto-type tail bound
`P[|X| > At] ≤ K ^ (3 * ⌈p⌉₊ ^ 2) * t ^ (-p)` for `t ≥ 1`, and the moment
bound is then the elementary layer-cake computation for a power-law tail
(`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul` split at `t = A`,
with `MeasureTheory.integral_Ioi_rpow_of_lt` evaluating the tail integral).

## Without the normalization

[AK] requires `Ψ : ℝ₊ → [1, ∞)`, so the `(P3')` block must carry this normalization: the
example `Ψ(t) := ε t ^ p`, `ε → 0`, shows that the statement fails without it. The statement
`SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3` therefore includes exactly
`∀ t, 0 ≤ t → 1 ≤ Psi t` (and the same for `PsiS`), so the normalized case
proved in this file matches its hypotheses; no
un-normalized corollary is needed. Tracing the proof below,
`1 ≤ Ψ 1` is used only once, to discard the factor `Ψ 1` from
`Ψ s / Ψ 1 ≤ Ψ s`; dropping it while keeping only `0 < Ψ 1` (still needed to
divide) would carry an *extra*, uncontrolled factor `(Ψ 1)⁻¹` through the
whole argument, which that example sends to `∞`. That is exactly why the
uniform constant `(p / (p - q)) K ^ (3⌈p⌉₊²)` genuinely needs the
normalization, not merely `0 < Ψ 1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Carrier

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Step 1: the growth condition forces a Pareto-type lower bound on `Ψ` -/

/-- The AK.HC growth condition, evaluated at `t := 1` and combined with the
normalization `1 ≤ Ψ 1`, is exactly a power-law lower bound for `Ψ` on
`[1, ∞)`. This is the only place `1 ≤ Ψ t` (at `t = 1`) is used; no
monotonicity hypothesis on `Ψ` is needed. -/
theorem akhc_inv_psi_le_of_growth
    {Ψ : ℝ → ℝ} {K pPsi : ℝ} (hK : 1 ≤ K)
    (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Ψ t)
    (hGrowth : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ K ^ (3 * ⌈p⌉₊ ^ 2) * (Ψ (t * s) / Ψ t))
    {p : ℝ} (hp : 1 < p) (hpPsi : p ≤ pPsi) {s : ℝ} (hs : 1 ≤ s) :
    (Ψ s)⁻¹ ≤ K ^ (3 * ⌈p⌉₊ ^ 2) * s ^ (-p) := by
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  set Kp : ℝ := K ^ (3 * ⌈p⌉₊ ^ 2) with hKp_def
  have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
  have hPsi1 : 1 ≤ Ψ 1 := hPsiOne 1 zero_le_one
  have hPsi1_pos : 0 < Ψ 1 := lt_of_lt_of_le zero_lt_one hPsi1
  have hPsis : 1 ≤ Ψ s := hPsiOne s hs0
  have hPsis_nonneg : 0 ≤ Ψ s := le_trans zero_le_one hPsis
  have hKp_pos : 0 < Kp := by
    rw [hKp_def]; positivity
  have hKp_nonneg : 0 ≤ Kp := hKp_pos.le
  have hstep := hGrowth p hp hpPsi 1 s (le_refl 1) hs
  rw [one_mul] at hstep
  -- `Ψ s / Ψ 1 ≤ Ψ s` since `1 ≤ Ψ 1` and `0 ≤ Ψ s`.
  have hratio_le : Ψ s / Ψ 1 ≤ Ψ s := by
    rw [div_le_iff₀ hPsi1_pos]
    nlinarith only [hPsis_nonneg, hPsi1]
  have hsp_le : s ^ p ≤ Kp * Ψ s := hstep.trans (mul_le_mul_of_nonneg_left hratio_le hKp_nonneg)
  have hsp_pos : 0 < s ^ p := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hs) p
  have hdiv : s ^ p / Kp ≤ Ψ s := (div_le_iff₀ hKp_pos).2 (by linarith only [hsp_le])
  have hdiv_pos : 0 < s ^ p / Kp := div_pos hsp_pos hKp_pos
  have hinv : (Ψ s)⁻¹ ≤ (s ^ p / Kp)⁻¹ := inv_anti₀ hdiv_pos hdiv
  have hrw : (s ^ p / Kp)⁻¹ = Kp * s ^ (-p) := by
    rw [inv_div, div_eq_mul_inv, ← Real.rpow_neg hs0]
  rwa [hrw] at hinv

/-! ### Step 2: the layer-cake moment bound -/

/-- The layer-cake computation behind item (1) of package A3, in `lintegral`
form: for `X` with `IsBigO P Ψ X A` under the AK.HC growth condition and the
normalization `1 ≤ Ψ`, the `q`-th absolute moment of `X` is controlled, for
every `1 ≤ q < p ≤ pΨ`, by the constant `(p / (p - q)) K ^ (3⌈p⌉₊²) A ^ q`.
The proof splits the layer-cake integral at `t = A`: below `A` the trivial
bound `P[·] ≤ 1` is used, and above `A` the Pareto tail bound
`akhc_inv_psi_le_of_growth` is used together with `hX`. -/
private theorem akhc_abs_rpow_lintegral_le_of_isBigO
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ψ : ℝ → ℝ} {C : ℝ} (hC_one_le : 1 ≤ C)
    {p : ℝ} (hTail : ∀ s : ℝ, 1 ≤ s → (Ψ s)⁻¹ ≤ C * s ^ (-p))
    {X : Ω → ℝ} {A : ℝ} (hA : 0 < A) (hXm : Measurable X)
    (hX : IsBigO P Ψ X A)
    {q : ℝ} (hq1 : 1 ≤ q) (hqp : q < p) :
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ q) ∂P ≤
      ENNReal.ofReal ((p / (p - q)) * C * A ^ q) := by
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC_one_le
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hpq_pos : 0 < p - q := by linarith only [hqp]
  have hp : 1 < p := lt_of_le_of_lt hq1 hqp
  -- The tail bound for `X`, at the natural scale `t := |X|/A`.
  have hTailX : ∀ t : ℝ, 1 ≤ t →
      P.real (upperTailEvent (fun ω => |X ω|) (A * t)) ≤ C * t ^ (-p) := by
    intro t ht
    exact (hX ht).trans (hTail t ht)
  -- Re-expressed at the genuine scale `t ≥ A` (no rescaling by `A` needed at
  -- the call site).
  have hTailGen : ∀ t : ℝ, A ≤ t →
      P.real {a : Ω | t < |X a|} ≤ C * A ^ p * t ^ (-p) := by
    intro t htA
    have hst : 1 ≤ t / A := by
      rw [le_div_iff₀ hA]; linarith only [htA]
    have h1 := hTailX (t / A) hst
    have heq : A * (t / A) = t := by field_simp
    rw [heq] at h1
    have htpos : 0 < t := lt_of_lt_of_le hA htA
    have hdiv : (t / A) ^ (-p) = A ^ p * t ^ (-p) := by
      calc
        (t / A) ^ (-p) = t ^ (-p) / A ^ (-p) := by
          rw [Real.div_rpow htpos.le hA.le]
        _ = t ^ (-p) / (A ^ p)⁻¹ := by rw [Real.rpow_neg hA.le]
        _ = t ^ (-p) * A ^ p := by rw [div_eq_mul_inv, inv_inv]
        _ = A ^ p * t ^ (-p) := by ring
    rw [hdiv] at h1
    have hrearrange : C * (A ^ p * t ^ (-p)) = C * A ^ p * t ^ (-p) := by ring
    rwa [hrearrange] at h1
  have hTail1 : ∀ t : ℝ, P {a : Ω | t < |X a|} ≤ (1 : ENNReal) := by
    intro t
    calc P {a : Ω | t < |X a|} ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  -- The layer cake identity.
  have hLayer := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
    (μ := P) (f := fun ω => |X ω|)
    (Filter.Eventually.of_forall fun ω => abs_nonneg (X ω))
    ((continuous_abs.measurable.comp hXm).aemeasurable) (p := q) hq_pos
  rw [hLayer]
  have hUnion : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) A ∪ Set.Ioi A := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
    constructor
    · intro hx
      by_cases hxA : x ≤ A
      · exact Or.inl ⟨hx, hxA⟩
      · exact Or.inr (lt_of_not_ge hxA)
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · exact lt_trans hA hx
  have hsplit :
      ∫⁻ t in Set.Ioi (0 : ℝ), P {a : Ω | t < |X a|} * ENNReal.ofReal (t ^ (q - 1)) =
        (∫⁻ t in Set.Ioc (0 : ℝ) A, P {a : Ω | t < |X a|} * ENNReal.ofReal (t ^ (q - 1)))
          + ∫⁻ t in Set.Ioi A, P {a : Ω | t < |X a|} * ENNReal.ofReal (t ^ (q - 1)) := by
    rw [hUnion]
    exact MeasureTheory.lintegral_union measurableSet_Ioi
      (Set.disjoint_left.2 fun x (hx : x ∈ Set.Ioc (0 : ℝ) A) => not_lt.mpr hx.2)
  rw [hsplit]
  -- Part 1: the contribution of `t ∈ (0, A]`.
  have hf1 : IntegrableOn (fun t : ℝ => t ^ (q - 1)) (Set.Ioc (0 : ℝ) A) volume := by
    have hii : IntervalIntegrable (fun t : ℝ => t ^ (q - 1)) volume 0 A :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith only [hq1] : (-1 : ℝ) < q - 1)
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hA.le] at hii
  have hnn1 : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) A)] fun t : ℝ => t ^ (q - 1) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  have hval1 : ∫ t : ℝ in Set.Ioc (0 : ℝ) A, t ^ (q - 1) = A ^ q / q := by
    rw [← intervalIntegral.integral_of_le hA.le,
      integral_rpow (r := q - 1) (Or.inl (by linarith only [hq1] : (-1 : ℝ) < q - 1))]
    have hexp : q - 1 + 1 = q := by ring
    rw [hexp, Real.zero_rpow (by linarith only [hq_pos] : q ≠ 0)]
    ring
  have hP1 : ∫⁻ t in Set.Ioc (0 : ℝ) A, P {a : Ω | t < |X a|} * ENNReal.ofReal (t ^ (q - 1)) ≤
      ENNReal.ofReal (A ^ q / q) := by
    refine le_trans (lintegral_mono_ae
      (g := fun t : ℝ => ENNReal.ofReal (t ^ (q - 1)))
      (Filter.Eventually.of_forall fun t => ?_)) ?_
    · calc P {a : Ω | t < |X a|} * ENNReal.ofReal (t ^ (q - 1)) ≤
          1 * ENNReal.ofReal (t ^ (q - 1)) :=
        mul_le_mul_of_nonneg_right (hTail1 t) (by positivity)
      _ = ENNReal.ofReal (t ^ (q - 1)) := one_mul _
    · rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := volume.restrict (Set.Ioc (0 : ℝ) A)) hf1 hnn1]
      exact ENNReal.ofReal_le_ofReal hval1.le
  -- Part 2: the contribution of `t ∈ (A, ∞)`.
  have hf2 : IntegrableOn (fun t : ℝ => t ^ (q - 1 - p)) (Set.Ioi A) volume :=
    integrableOn_Ioi_rpow_of_lt (by linarith only [hqp] : q - 1 - p < -1) hA
  have hnn2 : 0 ≤ᵐ[volume.restrict (Set.Ioi A)] fun t : ℝ => t ^ (q - 1 - p) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (lt_trans hA ht).le _
  have hval2 : ∫ t : ℝ in Set.Ioi A, t ^ (q - 1 - p) = A ^ (q - p) / (p - q) := by
    rw [integral_Ioi_rpow_of_lt (by linarith only [hqp] : q - 1 - p < -1) hA]
    have hexp : q - 1 - p + 1 = q - p := by ring
    rw [hexp, show p - q = -(q - p) by ring, div_neg, neg_div]
  have hpoint2 : ∀ t ∈ Set.Ioi A,
      P {a : Ω | t < |X a|} * ENNReal.ofReal (t ^ (q - 1)) ≤
        ENNReal.ofReal (C * A ^ p * t ^ (q - 1 - p)) := by
    intro t htA
    have htA' : A ≤ t := htA.le
    have htpos : 0 < t := lt_trans hA htA
    have htail_ne_top : P {a : Ω | t < |X a|} ≠ ⊤ := by finiteness
    have heq : P {a : Ω | t < |X a|} = ENNReal.ofReal (P.real {a : Ω | t < |X a|}) := by
      simp [Measure.real, htail_ne_top]
    have htail : P.real {a : Ω | t < |X a|} ≤ C * A ^ p * t ^ (-p) := hTailGen t htA'
    have h1 : P {a : Ω | t < |X a|} ≤ ENNReal.ofReal (C * A ^ p * t ^ (-p)) := by
      rw [heq]; exact ENNReal.ofReal_le_ofReal htail
    calc P {a : Ω | t < |X a|} * ENNReal.ofReal (t ^ (q - 1)) ≤
        ENNReal.ofReal (C * A ^ p * t ^ (-p)) * ENNReal.ofReal (t ^ (q - 1)) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ENNReal.ofReal (C * A ^ p * t ^ (-p) * t ^ (q - 1)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (C * A ^ p * t ^ (q - 1 - p)) := by
        congr 1
        rw [mul_assoc, ← Real.rpow_add htpos]
        ring_nf
  have hP2 : ∫⁻ t in Set.Ioi A, P {a : Ω | t < |X a|} * ENNReal.ofReal (t ^ (q - 1)) ≤
      ENNReal.ofReal (C * A ^ p * (A ^ (q - p) / (p - q))) := by
    refine le_trans (setLIntegral_mono' measurableSet_Ioi hpoint2) ?_
    have hIntegrable :
        Integrable (fun t : ℝ => C * A ^ p * t ^ (q - 1 - p))
          (volume.restrict (Set.Ioi A)) := by
      simpa [IntegrableOn] using hf2.const_mul (C * A ^ p)
    have hnn2' :
        0 ≤ᵐ[volume.restrict (Set.Ioi A)] fun t : ℝ => C * A ^ p * t ^ (q - 1 - p) := by
      filter_upwards [hnn2] with t ht
      exact mul_nonneg (by positivity) ht
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntegrable hnn2']
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [MeasureTheory.integral_const_mul, hval2]
  -- Combine both parts, restoring the outer factor `ENNReal.ofReal q` from
  -- the layer-cake identity.
  have hAprod : A ^ p * A ^ (q - p) = A ^ q := by
    rw [← Real.rpow_add hA]
    congr 1
    ring
  have hApow_nonneg : (0 : ℝ) ≤ A ^ q := by positivity
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hpq_ne : p - q ≠ 0 := ne_of_gt hpq_pos
  have hq_term : q * (A ^ q / q) = A ^ q := by field_simp
  have hsecond : q * (C * A ^ p * (A ^ (q - p) / (p - q))) = C * A ^ q * (q / (p - q)) := by
    have hrearrange : C * A ^ p * (A ^ (q - p) / (p - q)) = C * (A ^ p * A ^ (q - p)) / (p - q) := by
      ring
    rw [hrearrange, hAprod]
    ring
  have hpdecomp : (p / (p - q)) * C * A ^ q = C * A ^ q + C * A ^ q * (q / (p - q)) := by
    field_simp
    ring
  have hreal :
      q * (A ^ q / q) + q * (C * A ^ p * (A ^ (q - p) / (p - q))) ≤
        (p / (p - q)) * C * A ^ q := by
    rw [hq_term, hsecond, hpdecomp]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hC_one_le) hApow_nonneg]
  calc ENNReal.ofReal q *
      ((∫⁻ t in Set.Ioc (0 : ℝ) A, P {a : Ω | t < |X a|} * ENNReal.ofReal (t ^ (q - 1)))
        + ∫⁻ t in Set.Ioi A, P {a : Ω | t < |X a|} * ENNReal.ofReal (t ^ (q - 1)))
      ≤ ENNReal.ofReal q *
          (ENNReal.ofReal (A ^ q / q) +
            ENNReal.ofReal (C * A ^ p * (A ^ (q - p) / (p - q)))) :=
        mul_le_mul_of_nonneg_left (add_le_add hP1 hP2) zero_le
    _ = ENNReal.ofReal (q * (A ^ q / q) + q * (C * A ^ p * (A ^ (q - p) / (p - q)))) := by
        rw [mul_add, ← ENNReal.ofReal_mul hq_pos.le, ← ENNReal.ofReal_mul hq_pos.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((p / (p - q)) * C * A ^ q) := ENNReal.ofReal_le_ofReal hreal

/-- Package A3, item (1) (integrability half): under the AK.HC growth
condition and the normalization `1 ≤ Ψ`, a random variable with
`IsBigO P Ψ X A` has a finite `q`-th absolute moment for every
`1 ≤ q < p ≤ pΨ`. -/
theorem akhc_integrable_abs_rpow_of_isBigO
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ψ : ℝ → ℝ} {K pPsi : ℝ} (hK : 1 ≤ K)
    (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Ψ t)
    (hGrowth : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ K ^ (3 * ⌈p⌉₊ ^ 2) * (Ψ (t * s) / Ψ t))
    {X : Ω → ℝ} {A : ℝ} (hA : 0 < A) (hXm : Measurable X)
    (hX : IsBigO P Ψ X A)
    {p q : ℝ} (hp : 1 < p) (hpPsi : p ≤ pPsi) (hq1 : 1 ≤ q) (hqp : q < p) :
    Integrable (fun ω => |X ω| ^ q) P := by
  have hC_one_le : 1 ≤ K ^ (3 * ⌈p⌉₊ ^ 2) := one_le_pow₀ hK
  have hbound := akhc_abs_rpow_lintegral_le_of_isBigO hC_one_le
    (fun s hs => akhc_inv_psi_le_of_growth hK hPsiOne hGrowth hp hpPsi hs) hA hXm hX hq1 hqp
  have hpowm : AEMeasurable (fun ω => |X ω| ^ q) P :=
    (continuous_abs.measurable.comp hXm).aemeasurable.pow measurable_const.aemeasurable
  refine ⟨hpowm.aestronglyMeasurable, ?_⟩
  have hnn : 0 ≤ᵐ[P] fun ω => |X ω| ^ q :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnn]
  exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top

/-- Package A3, item (1): the AK.HC moment bound. For a general Orlicz
function `Ψ` satisfying the normalization `1 ≤ Ψ` and the AK.HC growth
condition (exactly the `(P3')` shape of
`akhc_weakerP3`), a random variable `X` with `IsBigO P Ψ X A` satisfies,
for every `1 ≤ q < p ≤ pΨ`,

`E |X| ^ q ≤ (p / (p - q)) * K ^ (3 ⌈p⌉₊²) * A ^ q`.

This is the exact shape requested by package A3 with `C(q, p) := p / (p - q)`.
Every hypothesis is carried explicitly; the only fact about `Ψ` consumed
beyond the growth condition is the normalization `1 ≤ Ψ` (see the module
docstring for what would be lost without it). -/
theorem akhc_moment_le_of_isBigO
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ψ : ℝ → ℝ} {K pPsi : ℝ} (hK : 1 ≤ K)
    (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Ψ t)
    (hGrowth : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ K ^ (3 * ⌈p⌉₊ ^ 2) * (Ψ (t * s) / Ψ t))
    {X : Ω → ℝ} {A : ℝ} (hA : 0 < A) (hXm : Measurable X)
    (hX : IsBigO P Ψ X A)
    {p q : ℝ} (hp : 1 < p) (hpPsi : p ≤ pPsi) (hq1 : 1 ≤ q) (hqp : q < p) :
    ∫ ω, |X ω| ^ q ∂P ≤ (p / (p - q)) * K ^ (3 * ⌈p⌉₊ ^ 2) * A ^ q := by
  have hnn : 0 ≤ᵐ[P] fun ω => |X ω| ^ q :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hpowm : AEMeasurable (fun ω => |X ω| ^ q) P :=
    (continuous_abs.measurable.comp hXm).aemeasurable.pow measurable_const.aemeasurable
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hC_one_le : 1 ≤ K ^ (3 * ⌈p⌉₊ ^ 2) := one_le_pow₀ hK
  have hbound := akhc_abs_rpow_lintegral_le_of_isBigO hC_one_le
    (fun s hs => akhc_inv_psi_le_of_growth hK hPsiOne hGrowth hp hpPsi hs) hA hXm hX hq1 hqp
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hpowm.aestronglyMeasurable]
  have hpq_pos : 0 < p - q := by linarith only [hqp]
  have hbound_nonneg : (0 : ℝ) ≤ (p / (p - q)) * K ^ (3 * ⌈p⌉₊ ^ 2) * A ^ q := by positivity
  have hfin : ∫⁻ ω, ENNReal.ofReal (|X ω| ^ q) ∂P < (⊤ : ENNReal) :=
    lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hto := (ENNReal.toReal_le_toReal hfin.ne ENNReal.ofReal_ne_top).2 hbound
  simpa [hbound_nonneg] using hto

end

end SuperdiffusionCLT.AKHC61.Carrier

