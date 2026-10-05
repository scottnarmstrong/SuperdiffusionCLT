/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.OrliczTriangle
public import SuperdiffusionCLT.Probability.OrliczTriangleSmallIndex

/-!
# The infinite generalized triangle inequality for `O_{Γ_σ}`

This module proves the passage to the limit over partial sums that turns the
finite sum rule of the library into the infinite version of Lemma
`l.Gamma.sigma.triangle` of the paper, whose display `e.Gamma.sigma.triangle` reads: for a
nonnegative summable sequence `{a_k}` and random variables `X_k = O_{Γ_σ}(a_k)`,

`∑_k X_k ≤ O_{Γ_σ}((1 + C σ⁻¹ 1_{σ < 1}) ∑_k a_k)`,

and whose printed proof passes from the finite triangle to the infinite sum
by a passage to the limit over the partial sums. It is the countable-union bound step
needed wherever the paper sums an `O_{Γ_σ}` estimate over infinitely many scales:
the shell sums consumed by Proposition `p.concentration` and its union
bound. It is also the step that any assembly of the infinite
multiscale depth sums needs: each depth of the depth sum carries a `Γ_σ` tail at a
summable geometric weight `3^{-sj}`, and the honest form of the depth sum is infinite —
truncating it leaves a non-vanishing tail, because the spatial-average display
does not vanish below the shell scale and only the weight makes the sum converge.

## What is proved here, and what is not

The library provides the finite-family sum rule
`Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma`
(`Homogenization/Probability/IndependentSums/Triangle.lean`) with the explicit prefactor
`gammaTriangleConst σ = 4 * gammaGrowthConst σ ^ (12 : ℝ)`, valid for every `0 < σ`.
`Probability/OrliczTriangle.lean` evaluates that prefactor on `1 ≤ σ` (the universal
number `16384`) and `Probability/OrliczTriangleSmallIndex.lean` on `0 < σ ≤ 1`
(the explicit `4 * (2 / σ) ^ (12 / σ)`).

The passage to the limit over the partial sums is what this module adds. It requires no
independence and no assumption of almost-sure summability: for `∑'` the pointwise value
of a divergent series is `0` (`tsum_eq_zero_of_not_summable`), so the tail event of the
series sees only the points at which the series converges, and at such a point the
partial sums converge to the sum. The conclusion is therefore stated without an
almost-sure summability hypothesis; a consumer who has one simply ignores it.

The printed prefactor `1 + C σ⁻¹ 1_{σ < 1}` — in particular the value `1` on `σ ≥ 1` —
is **not** obtained: it is the external node `ext.AKMBook.triangle.sigma.at.least.one`
on `σ ≥ 1` and the node `l.Gamma.sigma.triangle#quasi-triangle-inequality` on
`0 < σ < 1` (see the module docstrings of `Probability/OrliczTriangle.lean` and
`Probability/OrliczTriangleSmallIndex.lean`). What is proved is the same statement with
the prefactor of the library in place of the printed one, separately on each range.

## Main results

The public surface is exactly the following six declarations.

* `measureReal_absTailEvent_eq_zero_of_amplitude_eq_zero`: a `Γ_σ`-tailed variable of
  amplitude `0` vanishes almost surely; the tail bound is used at `t → ∞`.
* `isBigO_gammaSigma_range_sum`: the finite-family sum rule for partial sums over
  `Finset.range N`, with amplitudes that are only nonnegative (the finite
  rules require strictly positive amplitudes; a vanishing amplitude forces the
  corresponding summand to vanish almost surely, so the sum splits).
* `isBigO_gammaSigma_tsum_aux`: the passage to the limit over partial sums: if every
  partial sum `∑_{k < N} X k` is `O_{Γ_σ}(C * ∑_{k < N} A k)` with the same `C ≥ 0`,
  then `∑' X k = O_{Γ_σ}(C * ∑' A k)`. No `0 < σ` is needed at this level; it is
  carried by the finite rule that discharges the partial-sum hypothesis.
* `isBigO_gammaSigma_tsum`: the infinite sum rule, from the per-summand tails:
  `∑' X_k = O_{Γ_σ}(gammaTriangleConst σ * ∑' A_k)` for `0 < σ`.
* `isBigO_gammaSigma_tsum_of_one_le`: the same with the universal prefactor `16384`
  on the range `1 ≤ σ`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Probability

open MeasureTheory
open Homogenization

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## A `Γ_σ`-tailed variable of amplitude zero -/

/-- A `Γ_σ`-tailed variable of amplitude `0` vanishes almost surely in the sense that
`μ.real {|X| > 0} = 0`: the tail bound `μ.real {|X| > 0} ≤ exp (-(t ^ σ))` holds for
every `t ≥ 1`, and `exp (-(t ^ σ)) → 0` along `t → ∞` because `σ > 0`. This is the
amplitude-zero degeneration of the tail relation that the passage to the limit over
partial sums needs: partial sums with vanishing amplitudes contribute nothing. -/
theorem measureReal_absTailEvent_eq_zero_of_amplitude_eq_zero {mu : Measure Omega}
    [IsFiniteMeasure mu] {sigma : ℝ} (hsigma : 0 < sigma) {X : Omega → ℝ}
    (hX : IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma) X 0) :
    mu.real (IndependentSums.absTailEvent X 0) = 0 := by
  have hle : ∀ t : ℝ, 1 ≤ t →
      mu.real (IndependentSums.absTailEvent X 0) ≤ Real.exp (-(t ^ sigma)) := by
    intro t ht
    have h := IndependentSums.isBigO_gammaSigma_iff.mp hX ht
    simpa using h
  have hzero : Filter.Tendsto (fun t : ℝ => Real.exp (-(t ^ sigma))) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => t ^ sigma) Filter.atTop Filter.atTop :=
      tendsto_rpow_atTop hsigma
    have h2 : Filter.Tendsto (fun u : ℝ => Real.exp (-u)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    simpa only [Function.comp_def] using h2.comp h1
  have hnonneg : 0 ≤ mu.real (IndependentSums.absTailEvent X 0) := by
    positivity
  refine le_antisymm ?_ hnonneg
  refine le_of_tendsto_of_tendsto tendsto_const_nhds hzero ?_
  exact Filter.eventually_atTop.2 ⟨1, fun t ht => hle t ht⟩

/-! ## The finite sum rule for partial sums with nonnegative amplitudes -/

/-- The finite-family sum rule for the partial sums of an `ℕ`-indexed family over
`Finset.range N`, with amplitudes that are only nonnegative: given a finite-family sum
rule `hstep` with prefactor `C ≥ 0` for strictly positive amplitudes, and
`X i = O_{Γ_σ}(A i)` with `A k ≥ 0` on the range, the partial sum
`∑_{k < N} X k` satisfies `O_{Γ_σ}(C * ∑_{k < N} A k)`.

The only additional ingredient over `hstep` is the treatment of vanishing amplitudes: a
`Γ_σ`-tailed variable of amplitude `0` vanishes almost surely, so the partial sum splits
into the strictly-positive-amplitude part, to which `hstep` applies, and an almost
surely vanishing part. This is the amplitude-nonnegativity degeneration that the
passage to the limit over partial sums needs, since the amplitudes of an infinite
summable family are not bounded below by a positive number. -/
theorem isBigO_gammaSigma_range_sum {mu : Measure Omega} [IsFiniteMeasure mu]
    {sigma : ℝ} (hsigma : 0 < sigma) {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    {X : ℕ → Omega → ℝ} {A : ℕ → ℝ}
    (hstep : ∀ s : Finset ℕ, s.Nonempty → (∀ i ∈ s, 0 < A i) →
      (∀ i ∈ s, IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma) (X i) (A i)) →
      (∀ i ∈ s, Measurable (X i)) →
      IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
        (fun omega => ∑ i ∈ s, X i omega) (C * ∑ i ∈ s, A i))
    (hApos : ∀ k ∈ Finset.range N, 0 ≤ A k)
    (hmeas : ∀ k, Measurable (X k))
    (hX : ∀ k, IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma) (X k) (A k)) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (fun omega => ∑ k ∈ Finset.range N, X k omega) (C * ∑ k ∈ Finset.range N, A k) := by
  classical
  rw [IndependentSums.isBigO_gammaSigma_iff]
  intro t ht
  set s : Finset ℕ := (Finset.range N).filter (fun k => 0 < A k) with hs_def
  set z : Finset ℕ := (Finset.range N).filter (fun k => ¬ 0 < A k) with hz_def
  have hsA : ∀ i ∈ s, 0 < A i := fun i hi => (Finset.mem_filter.mp hi).2
  have hzA : ∀ i ∈ z, A i = 0 := by
    intro i hi
    have h1 : 0 ≤ A i := hApos i (Finset.mem_filter.mp hi).1
    have h2 : ¬ 0 < A i := (Finset.mem_filter.mp hi).2
    linarith only [h1, h2]
  set G : Set Omega := ⋃ i ∈ z, IndependentSums.absTailEvent (X i) 0 with hG_def
  have hGnull : mu.real G = 0 := by
    have hle : mu.real G ≤ ∑ i ∈ z, mu.real (IndependentSums.absTailEvent (X i) 0) :=
      measureReal_biUnion_finset_le _ _
    have hzero : ∑ i ∈ z, mu.real (IndependentSums.absTailEvent (X i) 0) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      have hX0 : IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma) (X i) 0 := by
        simpa only [hzA i hi] using hX i
      exact measureReal_absTailEvent_eq_zero_of_amplitude_eq_zero hsigma hX0
    have hnonneg : 0 ≤ mu.real G := by positivity
    linarith only [hle, hzero, hnonneg]
  have hsplit : ∀ omega : Omega,
      ∑ k ∈ Finset.range N, X k omega = ∑ i ∈ s, X i omega + ∑ i ∈ z, X i omega := by
    intro omega
    rw [Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun k => 0 < A k)
      (fun k => X k omega)]
  have hzsum : ∀ omega ∉ G, ∑ i ∈ z, X i omega = 0 := by
    intro omega homega
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hmem : omega ∉ IndependentSums.absTailEvent (X i) 0 := fun hmem =>
      homega (Set.mem_biUnion hi hmem)
    have hlt : ¬ 0 < |X i omega| := by
      simpa only [IndependentSums.mem_absTailEvent] using hmem
    have habs : |X i omega| = 0 := by linarith only [abs_nonneg (X i omega), hlt]
    rw [abs_eq_zero] at habs
    exact habs
  have hkey : IndependentSums.absTailEvent
      (fun omega => ∑ k ∈ Finset.range N, X k omega) ((C * ∑ k ∈ Finset.range N, A k) * t) ⊆
      G ∪ IndependentSums.absTailEvent
        (fun omega => ∑ i ∈ s, X i omega) ((C * ∑ i ∈ s, A i) * t) := by
    intro omega homega
    by_cases hG : omega ∈ G
    · exact Or.inl hG
    · have hz := hzsum omega hG
      simp only [IndependentSums.mem_absTailEvent] at homega ⊢
      rw [hsplit omega, hz, add_zero] at homega
      have hamp : ∑ i ∈ s, A i ≤ ∑ k ∈ Finset.range N, A k :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => (Finset.mem_filter.mp hi).1)
          (fun i hi hne => by
            have h2 : ¬ 0 < A i := fun hlt => hne (Finset.mem_filter.mpr ⟨hi, hlt⟩)
            linarith only [hApos i hi, h2])
      have hthr : (C * ∑ i ∈ s, A i) * t ≤ (C * ∑ k ∈ Finset.range N, A k) * t :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hamp hC) (le_trans zero_le_one ht)
      exact Or.inr (lt_of_le_of_lt hthr homega)
  have hbound : mu.real (IndependentSums.absTailEvent
      (fun omega => ∑ i ∈ s, X i omega) ((C * ∑ i ∈ s, A i) * t)) ≤
      Real.exp (-(t ^ sigma)) := by
    rcases s.eq_empty_or_nonempty with hse | hsn
    · have hfun : (fun omega => ∑ i ∈ s, X i omega) = fun _ : Omega => (0 : ℝ) := by
        rw [hse]
        simp
      have hamp : (C * ∑ i ∈ s, A i) * t = 0 := by
        rw [hse]
        simp
      have hempty : IndependentSums.absTailEvent (fun _ : Omega => (0 : ℝ)) 0 = ∅ := by
        ext omega
        simp [IndependentSums.mem_absTailEvent]
      rw [hfun, hamp, hempty, measureReal_empty]
      exact Real.exp_nonneg (-(t ^ sigma))
    · have hstep' := hstep s hsn hsA (fun i _ => hX i) (fun i _ => hmeas i)
      exact IndependentSums.isBigO_gammaSigma_iff.mp hstep' ht
  have hmain : mu.real (IndependentSums.absTailEvent
      (fun omega => ∑ k ∈ Finset.range N, X k omega) ((C * ∑ k ∈ Finset.range N, A k) * t)) ≤
      mu.real G + mu.real (IndependentSums.absTailEvent
        (fun omega => ∑ i ∈ s, X i omega) ((C * ∑ i ∈ s, A i) * t)) :=
    (measureReal_mono hkey).trans (measureReal_union_le _ _)
  rw [hGnull, zero_add] at hmain
  exact hmain.trans hbound

/-! ## The infinite sum rule -/

/-- **The passage to the limit over partial sums**: if every partial sum
`∑_{k < N} X k` is `O_{Γ_σ}(C * ∑_{k < N} A k)` with the same prefactor `C ≥ 0`, then
the infinite sum `∑' X k` is `O_{Γ_σ}(C * ∑' A k)`.

No assumption is made on the pointwise convergence of the series: where
`∑' X k ω` diverges its value is `0` (`tsum_eq_zero_of_not_summable`), so the tail event
of the series sees only the points of convergence, and at such a point the partial sums
converge to the sum, so the point eventually belongs to all the tail events of the
partial sums with indices `M + k`. The measure argument uses only continuity from below
for the directed family of those "eventual tail" events; no measurability of the sum is
involved. -/
theorem isBigO_gammaSigma_tsum_aux {mu : Measure Omega} [IsFiniteMeasure mu]
    {sigma : ℝ} {C : ℝ} (hC : 0 ≤ C)
    {X : ℕ → Omega → ℝ} {A : ℕ → ℝ} (hA : Summable A) (hApos : ∀ k, 0 ≤ A k)
    (hpart : ∀ N : ℕ, IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (fun omega => ∑ k ∈ Finset.range N, X k omega) (C * ∑ k ∈ Finset.range N, A k)) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (fun omega => ∑' k, X k omega) (C * ∑' k, A k) := by
  rw [IndependentSums.isBigO_gammaSigma_iff]
  intro t ht
  have hAinftypos : 0 ≤ ∑' k, A k := tsum_nonneg hApos
  have hTpos : 0 ≤ (C * ∑' k, A k) * t :=
    mul_nonneg (mul_nonneg hC hAinftypos) (le_trans zero_le_one ht)
  -- the bound at the series amplitude for every partial sum
  have hbound : ∀ N : ℕ, mu.real (IndependentSums.absTailEvent
      (fun omega => ∑ k ∈ Finset.range N, X k omega) ((C * ∑' k, A k) * t)) ≤
      Real.exp (-(t ^ sigma)) := by
    intro N
    have h1 := IndependentSums.isBigO_gammaSigma_iff.mp (hpart N) ht
    have hamp : ∑ k ∈ Finset.range N, A k ≤ ∑' k, A k :=
      hA.sum_le_tsum (Finset.range N) (fun k _ => hApos k)
    have hmono : IndependentSums.absTailEvent
        (fun omega => ∑ k ∈ Finset.range N, X k omega) ((C * ∑' k, A k) * t) ⊆
        IndependentSums.absTailEvent
          (fun omega => ∑ k ∈ Finset.range N, X k omega)
          ((C * ∑ k ∈ Finset.range N, A k) * t) :=
      IndependentSums.absTailEvent_mono_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hamp hC)
          (le_trans zero_le_one ht))
    exact (measureReal_mono hmono).trans h1
  -- the "eventual" sets: all the tail events of the partial sums with index `M + k`
  set F : ℕ → Set Omega := fun M => {omega : Omega |
    ∀ k : ℕ, omega ∈ IndependentSums.absTailEvent
      (fun omega' => ∑ k' ∈ Finset.range (M + k), X k' omega') ((C * ∑' k', A k') * t)}
  have hdir : Directed (· ⊆ ·) F := by
    intro i j
    refine ⟨max i j, fun ω hω => ?_, fun ω hω => ?_⟩
    · intro k
      have hle : i ≤ max i j := le_max_left i j
      have hmem := hω (max i j - i + k)
      rw [show (i : ℕ) + (max i j - i + k) = max i j + k from by
        rw [← add_assoc, Nat.add_sub_cancel' hle]] at hmem
      exact hmem
    · intro k
      have hle : j ≤ max i j := le_max_right i j
      have hmem := hω (max i j - j + k)
      rw [show (j : ℕ) + (max i j - j + k) = max i j + k from by
        rw [← add_assoc, Nat.add_sub_cancel' hle]] at hmem
      exact hmem
  have hsub : IndependentSums.absTailEvent
      (fun omega => ∑' k, X k omega) ((C * ∑' k, A k) * t) ⊆ ⋃ M, F M := by
    intro ω hω
    by_cases hsum : Summable fun k => X k ω
    · have hconv : Filter.Tendsto (fun N : ℕ => |∑ k ∈ Finset.range N, X k ω|)
        Filter.atTop (nhds |∑' k, X k ω|) := (Summable.hasSum hsum).tendsto_sum_nat.abs
      have hlt : (C * ∑' k, A k) * t < |∑' k, X k ω| := by
        simpa only [IndependentSums.mem_absTailEvent] using hω
      have hev : ∀ᶠ N : ℕ in Filter.atTop,
          (C * ∑' k, A k) * t < |∑ k ∈ Finset.range N, X k ω| :=
        hconv.eventually_const_lt hlt
      obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
      refine Set.mem_iUnion.2 ⟨M, fun k => ?_⟩
      exact hM (M + k) (Nat.le_add_right M k)
    · have hzero : ∑' k, X k ω = 0 :=
        tsum_eq_zero_of_not_summable hsum
      simp only [IndependentSums.mem_absTailEvent, hzero, abs_zero] at hω
      linarith only [hω, hTpos]
  -- the measure chain
  have hfin : ∀ s : Set Omega, mu s ≠ ⊤ := fun s => measure_ne_top mu s
  have hstep1 : mu (IndependentSums.absTailEvent
      (fun omega => ∑' k, X k omega) ((C * ∑' k, A k) * t)) ≤
      ENNReal.ofReal (Real.exp (-(t ^ sigma))) := by
    refine le_trans (measure_mono hsub) ?_
    rw [hdir.measure_iUnion]
    refine iSup_le fun M => ?_
    have h1 : F M ⊆ IndependentSums.absTailEvent
        (fun omega => ∑ k' ∈ Finset.range (M + 0), X k' omega)
        ((C * ∑' k', A k') * t) := fun ω hω => hω 0
    rw [Nat.add_zero] at h1
    exact (measure_mono h1).trans (by
      rw [← MeasureTheory.ofReal_measureReal (hfin _)]
      exact ENNReal.ofReal_le_ofReal (hbound M))
  calc mu.real (IndependentSums.absTailEvent
      (fun omega => ∑' k, X k omega) ((C * ∑' k, A k) * t))
      = (mu (IndependentSums.absTailEvent
        (fun omega => ∑' k, X k omega) ((C * ∑' k, A k) * t))).toReal :=
        MeasureTheory.measureReal_def mu _
    _ ≤ (ENNReal.ofReal (Real.exp (-(t ^ sigma)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hstep1
    _ = Real.exp (-(t ^ sigma)) := ENNReal.toReal_ofReal (Real.exp_nonneg _)

/-! ## The infinite sum rule from the per-summand tails -/

/-- **The infinite generalized triangle inequality for `O_{Γ_σ}`**: for `0 < σ`,
nonnegative summable amplitudes `A k` and measurable `X k` with
`X k = O_{Γ_σ}(A k)` for every `k`,

`∑' k, X k = O_{Γ_σ}(gammaTriangleConst σ * ∑' k, A k)`.

The prefactor is the upstream triangle constant
`gammaTriangleConst σ = 4 * gammaGrowthConst σ ^ (12 : ℝ)`; the printed prefactor
`1 + C σ⁻¹ 1_{σ < 1}` of the display `e.Gamma.sigma.triangle` is smaller
and is the external input named in the module docstring.

No almost-sure summability of the series `fun k => X k ω` is assumed: where the series
diverges its pointwise value is `0` (`tsum_eq_zero_of_not_summable`), and the passage
to the limit `isBigO_gammaSigma_tsum_aux` handles that branch. -/
theorem isBigO_gammaSigma_tsum {mu : Measure Omega} [IsFiniteMeasure mu]
    {sigma : ℝ} (hsigma : 0 < sigma) {X : ℕ → Omega → ℝ} {A : ℕ → ℝ}
    (hA : Summable A) (hApos : ∀ k, 0 ≤ A k)
    (hmeas : ∀ k, Measurable (X k))
    (hbigO : ∀ k, IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (X k) (A k)) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (fun omega => ∑' k, X k omega)
      (IndependentSums.gammaTriangleConst sigma * ∑' k, A k) := by
  have h2 : (0 : ℝ) ≤ IndependentSums.gammaGrowthConst sigma := by
    have hmax : (2 : ℝ) ≤ IndependentSums.gammaGrowthConst sigma := by
      simp only [IndependentSums.gammaGrowthConst]
      exact le_max_left _ _
    linarith only [hmax]
  have hC0 : (0 : ℝ) ≤ IndependentSums.gammaTriangleConst sigma := by
    simp only [IndependentSums.gammaTriangleConst]
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.rpow_nonneg h2 _)
  refine isBigO_gammaSigma_tsum_aux
    (C := IndependentSums.gammaTriangleConst sigma) hC0 hA hApos (fun N => ?_)
  exact isBigO_gammaSigma_range_sum hsigma hC0
    (fun s hsn hsA hXs hmeasS =>
      IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
        (μ := mu) (s := s) (X := X) (a := A) (σ := sigma) hsigma hsn hsA hXs hmeasS)
    (fun k _ => hApos k) hmeas hbigO

/-- The infinite sum rule on the range `σ ≥ 1` of the paper: with
`gammaTriangleConst σ = 16384` on this range (`gammaTriangleConst_eq_of_one_le`),
the conclusion of `isBigO_gammaSigma_tsum` reads

`∑' k, X k = O_{Γ_σ}(16384 * ∑' k, A k)`.

The printed prefactor on this range is `1`; the improvement to `1` is the external
node `ext.AKMBook.triangle.sigma.at.least.one`, not used and not proved here. -/
theorem isBigO_gammaSigma_tsum_of_one_le {mu : Measure Omega} [IsFiniteMeasure mu]
    {sigma : ℝ} (hsigma : 1 ≤ sigma) {X : ℕ → Omega → ℝ} {A : ℕ → ℝ}
    (hA : Summable A) (hApos : ∀ k, 0 ≤ A k)
    (hmeas : ∀ k, Measurable (X k))
    (hbigO : ∀ k, IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (X k) (A k)) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (fun omega => ∑' k, X k omega) (16384 * ∑' k, A k) := by
  have hpos : (0 : ℝ) < sigma := lt_of_lt_of_le zero_lt_one hsigma
  have h := isBigO_gammaSigma_tsum (mu := mu) (X := X) (A := A) hpos hA hApos hmeas hbigO
  rwa [gammaTriangleConst_eq_of_one_le hsigma] at h

end SuperdiffusionCLT.Probability