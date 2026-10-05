/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch05.Theorems.Section57.MinimalScaleTail
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockE

/-!
# The random minimal scale of the "Moreover" block

In the proof of `l.ellip.k.scales.estimates` (see `e.mathcal.K.int`): for
`δ ∈ (0,1)` and `σ > 0` the paper sets

`K_σ := 3^3 ∨ sup { 3^{m+1} : m ∈ ℕ, X_m > ½ δ m^σ }`,

where `X_m` is the four-term observable of `e.Xm.deff`, and proves
the tail `log K_σ ≤ O_{Γ_{2σ}}(C₁ (C₂ δ^{-1} σ^{-1})^{1/σ})` of
`e.mathcal.K.int` by a union bound over the scales above `N_σ m`.

## The carrier

`Homogenization.Book.Ch05.Section57.quenchedMinimalScale N0 Bad` is exactly
this construction: `3 ^ (first M ≥ N0 above which no `Bad K` occurs)`, with the
value `3 ^ N0` on the exceptional set where no such `M` exists. With
`N0 = 3` and `Bad m = { X_m > ½ δ m^σ }` it is the print's `K_σ`, and
`3 ^ 3 = 27` is the print's floor. What that definition does **not** provide, and what
this module adds, is:

* the measurability of the scale (`measurable_quenchedMinimalScale`), which the
  "Moreover" block demands of `Kfun`;
* the `Γ_{2σ}` tail of the **logarithm** of the scale
  (`isBigO_gammaSigma_log_quenchedMinimalScale`). The library
  lemma `isBigO_quenchedMinimalScale_of_badTailEvent_bound` is a `Γ_η` tail of the
  scale itself and needs a doubly exponential bad-tail input
  `exp(-(3^{N-N0}/B)^η)`; the minimal scale of this block has only the
  lognormal-type tail `exp(-(N/B)^{2σ})`, which is precisely a `Γ_{2σ}` tail of
  `log K_σ`.

## The scales that matter are at least three

The guard is `Kfun ω ≤ 3^m`, and `27 ≤ Kfun ω`, so only `m ≥ 3` occurs.
This is the print's own remark "If `3^m ≥ K_σ`, then `m ≥ 3`", which is what
makes `1 ≤ A log(B m)` available in the logarithmic-window clause.

## Main definitions and results

* `measurableSet_goodTailFrom`, `goodTailFrom_mono`,
  `measurableSet_hasGoodTailFrom`, `le_quenchedMinimalScaleIndex`,
  `quenchedMinimalScaleIndex_le_iff`, `measurable_quenchedMinimalScaleIndex`,
  `measurable_quenchedMinimalScale`: the measurability layer.
* `log_quenchedMinimalScale`, `isBigO_gammaSigma_log_quenchedMinimalScale`: the
  `Γ_{2σ}` tail of `log K_σ` from a lognormal-type bad-tail bound.
* `badTailEvent_eq_iUnion`, `measure_badTailEvent_le_tsum`: the union bound over the
  scales above `N`.
* `ae_hasGoodTailFrom_of_expTail`: the exceptional set of the construction is
  null under the same bad-tail bound.
* `moreoverBadEvent`, `moreoverMinimalScale`: the print's `K_σ` for a family of
  envelopes `X`.
* `le_moreoverMinimalScale`, `measurable_moreoverMinimalScale`,
  `three_le_of_moreoverMinimalScale_le`,
  `moreoverEnvelope_le_of_moreoverMinimalScale_le`: the floor `27`, the
  measurability, the scale restriction `m ≥ 3`, and the smallness of the
  envelope on `{K_σ ≤ 3^m}`.
* `measureReal_moreoverBadEvent_le`: the per-scale estimate `e.Xm.boundiu` from a
  uniform `Γ₂` amplitude of the envelopes.
* `one_lt_log_three`, `coarseAverage_le_of_moreoverMinimalScale_le`: the
  clause `e.yet.another.minscale.icandoit`, in the exact
  carrier of the "Moreover" block.

## What is proved elsewhere

The chain from the per-scale estimate to the hypothesis of
`isBigO_gammaSigma_log_quenchedMinimalScale` needs one further step, the
geometric summation, which is carried out in `IncrementMoreoverBlockG`: from

`mu.real (Bad K) ≤ exp (-(δ K^σ / (2 A))^2)` for `2 A ≤ δ K^σ`

together with `measure_badTailEvent_le_tsum`, one has to produce

`∀ N : ℕ, B ≤ (N : ℝ) →
   mu.real (badTailEvent Bad N) ≤ exp (-(((N : ℝ) / B) ^ (2 * σ)))`

for a suitable `B`. The printed route splits `a K^{2σ}` into
`½ a N^{2σ} + ½ a K^{2σ}` and bounds `∑_{K ≥ 0} exp(-½ a K^{2σ})` by a constant
through `exp u ≥ u^n / n!` with `n ≈ 2 σ^{-1}` and `∑_{K ≥ 1} K^{-2} ≤ 2`; the
resulting `B` is of order `(σ^{-1} δ^{-1})^{1/σ}`, which is the print's
`C₁ (C₂ δ^{-1} σ^{-1})^{1/σ}`. `IncrementMoreoverBlockG` proves this summation in
the exact shape this module consumes.

## References

* `e.Xm.deff`, `e.mathcal.K.int`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Estimates
namespace Stream

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open Homogenization.Book.Ch05.Section57
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal

noncomputable section

/-! ## Measurability of the abstract minimal scale -/

section Abstract

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The good-tail event above a scale is a countable intersection of
complements of bad events. -/
theorem measurableSet_goodTailFrom {Bad : ℕ → Set Omega}
    (hBad : ∀ K : ℕ, MeasurableSet (Bad K)) (k : ℕ) :
    MeasurableSet {omega : Omega | goodTailFrom Bad k omega} := by
  have hset : {omega : Omega | goodTailFrom Bad k omega}
      = ⋂ K : ℕ, {omega : Omega | k ≤ K → omega ∉ Bad K} := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, goodTailFrom]
  rw [hset]
  refine MeasurableSet.iInter fun K => ?_
  by_cases hk : k ≤ K
  · have : {omega : Omega | k ≤ K → omega ∉ Bad K} = (Bad K)ᶜ := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, hk, forall_const]
    rw [this]
    exact (hBad K).compl
  · have : {omega : Omega | k ≤ K → omega ∉ Bad K} = Set.univ := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro hcon
      exact absurd hcon hk
    rw [this]
    exact MeasurableSet.univ

omit [MeasurableSpace Omega] in
/-- The good-tail events increase with the scale. -/
theorem goodTailFrom_mono {Bad : ℕ → Set Omega} {k k' : ℕ} (hk : k ≤ k')
    {omega : Omega} (h : goodTailFrom Bad k omega) :
    goodTailFrom Bad k' omega :=
  fun K hK => h K (le_trans hk hK)

/-- The event that some scale has a good tail. -/
theorem measurableSet_hasGoodTailFrom {Bad : ℕ → Set Omega}
    (hBad : ∀ K : ℕ, MeasurableSet (Bad K)) (N0 : ℕ) :
    MeasurableSet {omega : Omega | hasGoodTailFrom N0 Bad omega} := by
  have hset : {omega : Omega | hasGoodTailFrom N0 Bad omega}
      = ⋃ M : ℕ, {omega : Omega | goodTailFrom Bad (N0 + M) omega} := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hasGoodTailFrom]
    constructor
    · rintro ⟨M, hM0, hM⟩
      exact ⟨M - N0, by rwa [Nat.add_sub_cancel' hM0]⟩
    · rintro ⟨M, hM⟩
      exact ⟨N0 + M, Nat.le_add_right _ _, hM⟩
  rw [hset]
  exact MeasurableSet.iUnion fun M => measurableSet_goodTailFrom hBad _

omit [MeasurableSpace Omega] in
/-- The minimal-scale index is never below its floor. -/
theorem le_quenchedMinimalScaleIndex (N0 : ℕ) (Bad : ℕ → Set Omega)
    (omega : Omega) : N0 ≤ quenchedMinimalScaleIndex N0 Bad omega := by
  classical
  by_cases hgood : hasGoodTailFrom N0 Bad omega
  · exact (quenchedMinimalScaleIndex_spec hgood).1
  · simp only [quenchedMinimalScaleIndex, hgood, dite_eq_right, not_false_iff,
      le_refl]

omit [MeasurableSpace Omega] in
/-- **The sublevel sets of the minimal-scale index.** Above the floor, the
index is at most `n` exactly when the tail above `n` is good, or when no good
tail exists at all. -/
theorem quenchedMinimalScaleIndex_le_iff {N0 : ℕ} {Bad : ℕ → Set Omega} {n : ℕ}
    (hn : N0 ≤ n) (omega : Omega) :
    quenchedMinimalScaleIndex N0 Bad omega ≤ n ↔
      (goodTailFrom Bad n omega ∨ ¬ hasGoodTailFrom N0 Bad omega) := by
  classical
  by_cases hgood : hasGoodTailFrom N0 Bad omega
  · simp only [hgood, not_true, or_false]
    constructor
    · intro hle
      exact goodTailFrom_mono hle (quenchedMinimalScaleIndex_spec hgood).2
    · intro hg
      exact quenchedMinimalScaleIndex_le_of_goodTail hn hg
  · simp only [hgood, not_false_iff, or_true, iff_true]
    simp only [quenchedMinimalScaleIndex, hgood, dite_eq_right, not_false_iff]
    exact hn

/-- **The minimal-scale index is measurable** whenever the bad events are. -/
theorem measurable_quenchedMinimalScaleIndex {Bad : ℕ → Set Omega}
    (hBad : ∀ K : ℕ, MeasurableSet (Bad K)) (N0 : ℕ) :
    Measurable (quenchedMinimalScaleIndex N0 Bad) := by
  classical
  have hsub : ∀ n : ℕ,
      MeasurableSet {omega : Omega | quenchedMinimalScaleIndex N0 Bad omega ≤ n} := by
    intro n
    by_cases hn : N0 ≤ n
    · have hset : {omega : Omega | quenchedMinimalScaleIndex N0 Bad omega ≤ n}
          = {omega : Omega | goodTailFrom Bad n omega} ∪
            {omega : Omega | hasGoodTailFrom N0 Bad omega}ᶜ := by
        ext omega
        simpa only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff] using
          quenchedMinimalScaleIndex_le_iff (Bad := Bad) hn omega
      rw [hset]
      exact (measurableSet_goodTailFrom hBad n).union
        (measurableSet_hasGoodTailFrom hBad N0).compl
    · have hset : {omega : Omega | quenchedMinimalScaleIndex N0 Bad omega ≤ n}
          = (∅ : Set Omega) := by
        ext omega
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hle
        exact hn (le_trans (le_quenchedMinimalScaleIndex N0 Bad omega) hle)
      rw [hset]
      exact MeasurableSet.empty
  refine measurable_to_countable' fun n => ?_
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · have hset : quenchedMinimalScaleIndex N0 Bad ⁻¹' {n}
        = {omega : Omega | quenchedMinimalScaleIndex N0 Bad omega ≤ n} := by
      ext omega
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
        hn0, Nat.le_zero]
    rw [hset]
    exact hsub n
  · have hset : quenchedMinimalScaleIndex N0 Bad ⁻¹' {n}
        = {omega : Omega | quenchedMinimalScaleIndex N0 Bad omega ≤ n} \
          {omega : Omega | quenchedMinimalScaleIndex N0 Bad omega ≤ n - 1} := by
      ext omega
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff,
        Set.mem_ofPred_eq]
      omega
    rw [hset]
    exact (hsub n).diff (hsub (n - 1))

/-- **The minimal scale is measurable** whenever the bad events are. -/
theorem measurable_quenchedMinimalScale {Bad : ℕ → Set Omega}
    (hBad : ∀ K : ℕ, MeasurableSet (Bad K)) (N0 : ℕ) :
    Measurable (quenchedMinimalScale N0 Bad) := by
  have hcomp : quenchedMinimalScale N0 Bad
      = (fun n : ℕ => (3 : ℝ) ^ n) ∘ quenchedMinimalScaleIndex N0 Bad := rfl
  rw [hcomp]
  exact (measurable_from_top).comp (measurable_quenchedMinimalScaleIndex hBad N0)

omit [MeasurableSpace Omega] in
/-- The logarithm of the triadic minimal scale is its index times `log 3`. -/
theorem log_quenchedMinimalScale (N0 : ℕ) (Bad : ℕ → Set Omega)
    (omega : Omega) :
    Real.log (quenchedMinimalScale N0 Bad omega) =
      (quenchedMinimalScaleIndex N0 Bad omega : ℝ) * Real.log 3 := by
  rw [quenchedMinimalScale, Real.log_pow]

/-- **The `Γ_{2σ}` tail of the logarithm of the minimal scale** from a
lognormal-type bad-tail bound. This is the mechanism of `e.mathcal.K.int`: the print's union bound
produces `P[log K_σ > (log 3) N] ≤ exp(-c (N/B)^{2σ})`, which is exactly a
`Γ_{2σ}` tail of `log K_σ` at amplitude `2 B log 3`. The factor `2` is the
triadic rounding loss of the floor `⌊2 B t⌋`. -/
theorem isBigO_gammaSigma_log_quenchedMinimalScale
    {mu : Measure Omega} [IsFiniteMeasure mu] {N0 : ℕ} {Bad : ℕ → Set Omega}
    {B sigma : ℝ} (hsigma : 0 < sigma) (hB : (N0 : ℝ) + 1 ≤ B)
    (htail : ∀ N : ℕ, B ≤ (N : ℝ) →
      mu.real (badTailEvent Bad N) ≤
        Real.exp (-(((N : ℝ) / B) ^ (2 * sigma)))) :
    IsBigO mu (gammaSigma (2 * sigma))
      (fun omega => Real.log (quenchedMinimalScale N0 Bad omega))
      (2 * B * Real.log 3) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hN0 : (0 : ℝ) ≤ (N0 : ℝ) := Nat.cast_nonneg N0
  have hB1 : (1 : ℝ) ≤ B := by linarith only [hB, hN0]
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  rw [IsBigO, isBigOWith_gammaSigma_iff]
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hBt : (1 : ℝ) ≤ B * t := one_le_mul_of_one_le_of_one_le hB1 ht
  set N : ℕ := ⌊2 * B * t⌋₊ with hNdef
  have hNle : ((N : ℕ) : ℝ) ≤ 2 * B * t := by
    rw [hNdef]
    exact Nat.floor_le (by positivity)
  have hNgt : 2 * B * t - 1 < ((N : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (2 * B * t)
    rw [← hNdef] at this
    linarith only [this]
  have hBtN : B * t ≤ ((N : ℕ) : ℝ) := by linarith only [hNgt, hBt]
  have hN0N : N0 ≤ N := by
    have hcast : ((N0 : ℕ) : ℝ) < ((N : ℕ) : ℝ) := by
      have hBB : B ≤ B * t := le_mul_of_one_le_right hBpos.le ht
      linarith only [hBtN, hBB, hB]
    exact le_of_lt (by exact_mod_cast hcast)
  have hsubset :
      upperTailEvent
          (fun omega => |Real.log (quenchedMinimalScale N0 Bad omega)|)
          (2 * B * Real.log 3 * t) ⊆ badTailEvent Bad N := by
    intro omega homega
    have habs : |Real.log (quenchedMinimalScale N0 Bad omega)| =
        (quenchedMinimalScaleIndex N0 Bad omega : ℝ) * Real.log 3 := by
      rw [log_quenchedMinimalScale, abs_of_nonneg]
      positivity
    have hlt : 2 * B * Real.log 3 * t <
        (quenchedMinimalScaleIndex N0 Bad omega : ℝ) * Real.log 3 := by
      rw [← habs]
      exact homega
    have hidx : 2 * B * t < (quenchedMinimalScaleIndex N0 Bad omega : ℝ) := by
      refine lt_of_mul_lt_mul_right ?_ hlog3.le
      rw [show 2 * B * t * Real.log 3 = 2 * B * Real.log 3 * t by ring]
      exact hlt
    have hNidx : N < quenchedMinimalScaleIndex N0 Bad omega := by
      have : ((N : ℕ) : ℝ) < (quenchedMinimalScaleIndex N0 Bad omega : ℝ) :=
        lt_of_le_of_lt hNle hidx
      exact_mod_cast this
    exact mem_badTailEvent_of_lt_quenchedMinimalScaleIndex hN0N hNidx
  calc mu.real
        (upperTailEvent
          (fun omega => |Real.log (quenchedMinimalScale N0 Bad omega)|)
          (2 * B * Real.log 3 * t))
      ≤ mu.real (badTailEvent Bad N) := measureReal_mono hsubset
    _ ≤ Real.exp (-(((N : ℝ) / B) ^ (2 * sigma))) := by
        refine htail N ?_
        have hBB : B ≤ B * t := le_mul_of_one_le_right hBpos.le ht
        linarith only [hBtN, hBB]
    _ ≤ Real.exp (-(t ^ (2 * sigma))) := by
        refine Real.exp_le_exp.2 (neg_le_neg ?_)
        refine Real.rpow_le_rpow ht0 ?_ (by linarith only [hsigma])
        rw [le_div_iff₀ hBpos]
        linarith only [hBtN]

/-! ### The union bound over the scales -/

omit [MeasurableSpace Omega] in
/-- The bad tail above `N` is the union of the bad events at the scales
`N, N+1, …`. -/
theorem badTailEvent_eq_iUnion (Bad : ℕ → Set Omega) (N : ℕ) :
    badTailEvent Bad N = ⋃ j : ℕ, Bad (N + j) := by
  ext omega
  simp only [badTailEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨K, hK, hmem⟩
    exact ⟨K - N, by rwa [Nat.add_sub_cancel' hK]⟩
  · rintro ⟨j, hj⟩
    exact ⟨N + j, Nat.le_add_right _ _, hj⟩

/-- **The union bound over the scales above `N`** in `ℝ≥0∞`, with no hypothesis. -/
theorem measure_badTailEvent_le_tsum {mu : Measure Omega}
    (Bad : ℕ → Set Omega) (N : ℕ) :
    mu (badTailEvent Bad N) ≤ ∑' j : ℕ, mu (Bad (N + j)) := by
  rw [badTailEvent_eq_iUnion]
  exact measure_iUnion_le _

/-! ### The almost-sure existence of a good tail -/

/-- **The exceptional set is null** when the bad tails decay. This is the
hypothesis under which the `∀ᵐ` quantifier of the "Moreover" block absorbs the samples
where no scale has a good tail. -/
theorem ae_hasGoodTailFrom_of_expTail
    {mu : Measure Omega} [IsFiniteMeasure mu] {N0 : ℕ} {Bad : ℕ → Set Omega}
    {B sigma : ℝ} (hsigma : 0 < sigma) (hB : 0 < B)
    (htail : ∀ N : ℕ, B ≤ (N : ℝ) →
      mu.real (badTailEvent Bad N) ≤
        Real.exp (-(((N : ℝ) / B) ^ (2 * sigma)))) :
    ∀ᵐ omega ∂mu, hasGoodTailFrom N0 Bad omega := by
  refine ae_hasGoodTailFrom fun eps heps => ?_
  set c : ℝ := max 0 (-Real.log eps) with hc
  have hc0 : 0 ≤ c := le_max_left _ _
  have htwo : 0 < 2 * sigma := by linarith only [hsigma]
  set r : ℝ := (c + 1) ^ (2 * sigma)⁻¹ with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by linarith only [hc0]) _
  set N : ℕ := max N0 ⌈B * r + B⌉₊ with hN
  refine ⟨N, le_max_left _ _, ?_⟩
  have hNge' : B * r + B ≤ (N : ℝ) := by
    refine le_trans (Nat.le_ceil (B * r + B)) ?_
    exact_mod_cast Nat.cast_le.2 (le_max_right N0 ⌈B * r + B⌉₊)
  have hNge : B * r ≤ (N : ℝ) := by linarith only [hNge', hB]
  have hNB : B ≤ (N : ℝ) := by
    have : 0 ≤ B * r := mul_nonneg hB.le hr0
    linarith only [hNge', this]
  have hratio : r ≤ (N : ℝ) / B := by
    rw [le_div_iff₀ hB]
    linarith only [hNge]
  have hpow : c + 1 ≤ ((N : ℝ) / B) ^ (2 * sigma) := by
    have hbase : (c + 1) = r ^ (2 * sigma) := by
      rw [hr, ← Real.rpow_mul (by linarith only [hc0] : (0:ℝ) ≤ c + 1),
        inv_mul_cancel₀ (ne_of_gt htwo), Real.rpow_one]
    rw [hbase]
    exact Real.rpow_le_rpow hr0 hratio htwo.le
  have hlog : -(((N : ℝ) / B) ^ (2 * sigma)) ≤ Real.log eps := by
    have hcle : -Real.log eps ≤ c := le_max_right _ _
    linarith only [hpow, hcle, hc0]
  calc mu.real (badTailEvent Bad N)
      ≤ Real.exp (-(((N : ℝ) / B) ^ (2 * sigma))) := htail N hNB
    _ ≤ Real.exp (Real.log eps) := Real.exp_le_exp.2 hlog
    _ = eps := Real.exp_log heps

end Abstract

/-! ## The minimal scale of the "Moreover" block -/

section Moreover

variable {d : ℕ}

/-- The bad event of the print's construction: the envelope `X_m`
exceeds half of `δ m^σ`. -/
def moreoverBadEvent (X : ℕ → ShellSeq d → ℝ) (delta sigma : ℝ) (m : ℕ) :
    Set (ShellSeq d) :=
  {omega | delta * (m : ℝ) ^ sigma / 2 < X m omega}

theorem measurableSet_moreoverBadEvent {X : ℕ → ShellSeq d → ℝ}
    (hX : ∀ m : ℕ, Measurable (X m)) (delta sigma : ℝ) (m : ℕ) :
    MeasurableSet (moreoverBadEvent X delta sigma m) :=
  measurableSet_lt measurable_const (hX m)

/-- **The random scale `K_σ` of `e.mathcal.K.int`**: `3 ^ 3` joined with the
first triadic scale beyond which the envelope never again exceeds
`½ δ m^σ`. -/
def moreoverMinimalScale (X : ℕ → ShellSeq d → ℝ) (delta sigma : ℝ) :
    ShellSeq d → ℝ :=
  quenchedMinimalScale 3 (moreoverBadEvent X delta sigma)

theorem measurable_moreoverMinimalScale {X : ℕ → ShellSeq d → ℝ}
    (hX : ∀ m : ℕ, Measurable (X m)) (delta sigma : ℝ) :
    Measurable (moreoverMinimalScale X delta sigma) :=
  measurable_quenchedMinimalScale
    (fun K => measurableSet_moreoverBadEvent hX delta sigma K) 3

/-- **The print's floor `K_σ ≥ 27`**. -/
theorem le_moreoverMinimalScale (X : ℕ → ShellSeq d → ℝ) (delta sigma : ℝ)
    (omega : ShellSeq d) :
    (27 : ℝ) ≤ moreoverMinimalScale X delta sigma omega := by
  have hidx : 3 ≤ quenchedMinimalScaleIndex 3 (moreoverBadEvent X delta sigma)
      omega := le_quenchedMinimalScaleIndex _ _ _
  calc (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) := by norm_num
    _ ≤ (3 : ℝ) ^ quenchedMinimalScaleIndex 3 (moreoverBadEvent X delta sigma)
          omega := pow_le_pow_right₀ (by norm_num) hidx
    _ = moreoverMinimalScale X delta sigma omega := rfl

/-- **Only the scales `m ≥ 3` are constrained** by the guard
`K_σ ≤ 3^m`; this is the print's own remark. -/
theorem three_le_of_moreoverMinimalScale_le {X : ℕ → ShellSeq d → ℝ}
    {delta sigma : ℝ} {omega : ShellSeq d} {m : ℕ}
    (hm : moreoverMinimalScale X delta sigma omega ≤ (3 : ℝ) ^ m) : 3 ≤ m := by
  have h27 : (3 : ℝ) ^ (3 : ℕ) ≤ (3 : ℝ) ^ m := by
    calc (3 : ℝ) ^ (3 : ℕ) = 27 := by norm_num
      _ ≤ moreoverMinimalScale X delta sigma omega :=
          le_moreoverMinimalScale X delta sigma omega
      _ ≤ (3 : ℝ) ^ m := hm
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h27

/-- **The smallness of the envelope above the minimal scale**: on the
full-measure event that some scale has a good tail, `K_σ ≤ 3^m` forces
`X_m ≤ ½ δ m^σ`. This is the print's remark after the definition of `K_σ`. -/
theorem moreoverEnvelope_le_of_moreoverMinimalScale_le {X : ℕ → ShellSeq d → ℝ}
    {delta sigma : ℝ} {omega : ShellSeq d}
    (hgood : hasGoodTailFrom 3 (moreoverBadEvent X delta sigma) omega) {m : ℕ}
    (hm : moreoverMinimalScale X delta sigma omega ≤ (3 : ℝ) ^ m) :
    X m omega ≤ delta * (m : ℝ) ^ sigma / 2 := by
  have hidx : quenchedMinimalScaleIndex 3 (moreoverBadEvent X delta sigma)
      omega ≤ m := quenchedMinimalScaleIndex_le_of_scale_le_pow hm
  have hnot : omega ∉ moreoverBadEvent X delta sigma m :=
    not_mem_bad_of_quenchedMinimalScaleIndex_le hgood hidx le_rfl
  exact not_lt.1 hnot

/-- **The per-scale estimate `e.Xm.boundiu`**: a `Γ₂` envelope of
amplitude `A` puts the bad event at scale `m` below
`exp(-(δ m^σ / 2A)^2)`, as soon as `δ m^σ ≥ 2A`. The threshold is the print's
`N_σ = ⌈(C σ^{-1} δ^{-1})^{1/σ}⌉`. -/
theorem measureReal_moreoverBadEvent_le {mu : Measure (ShellSeq d)}
    [IsFiniteMeasure mu] {X : ℕ → ShellSeq d → ℝ} {A delta sigma : ℝ}
    (hA : 0 < A) (hX : ∀ m : ℕ, IsBigO mu (gammaSigma 2) (X m) A) {m : ℕ}
    (hm : 2 * A ≤ delta * (m : ℝ) ^ sigma) :
    mu.real (moreoverBadEvent X delta sigma m) ≤
      Real.exp (-((delta * (m : ℝ) ^ sigma / (2 * A)) ^ (2 : ℝ))) := by
  set t : ℝ := delta * (m : ℝ) ^ sigma / (2 * A) with ht
  have h2A : (0 : ℝ) < 2 * A := by linarith only [hA]
  have ht1 : (1 : ℝ) ≤ t := by
    rw [ht, le_div_iff₀ h2A]
    linarith only [hm]
  have hAt : A * t = delta * (m : ℝ) ^ sigma / 2 := by
    rw [ht]
    field_simp
  have hbig := hX m
  rw [IsBigO, isBigOWith_gammaSigma_iff] at hbig
  have hsubset : moreoverBadEvent X delta sigma m ⊆
      upperTailEvent (fun omega => |X m omega|) (A * t) := by
    intro omega homega
    have hlt : delta * (m : ℝ) ^ sigma / 2 < X m omega := homega
    show A * t < |X m omega|
    rw [hAt]
    exact lt_of_lt_of_le hlt (le_abs_self _)
  exact le_trans (measureReal_mono hsubset) (hbig ht1)

/-! ## The logarithmic-window clause -/

/-- `1 < log 3`, the inequality behind the print's `h ≤ 2 A log(B m)`. -/
theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
  have := Real.exp_one_lt_d9
  linarith only [this]

/-- **The clause `e.yet.another.minscale.icandoit`**,
in the exact carrier of the "Moreover" block: above the minimal scale every coarse
average of `k - (k)_{cu_m}` over a sub-cube of the logarithmic window is at
most `A log(B m) δ m^σ`.

The only property of the envelope family `X` used is `hwindow`, which says that
`X_m` dominates the fourth term of `e.Xm.deff`, `h^{-1}` times the joint
scale-and-centre maximum of `IncrementMoreoverBlockD`. -/
theorem coarseAverage_le_of_moreoverMinimalScale_le {X : ℕ → ShellSeq d → ℝ}
    {delta sigma : ℝ} (hdelta : 0 < delta) {omega : ShellSeq d}
    (hgood : hasGoodTailFrom 3 (moreoverBadEvent X delta sigma) omega)
    (hwindow : ∀ m h : ℕ, 0 < h → h ≤ m →
      ((h : ℝ))⁻¹ * centeredScaleCubeMax h m omega ≤ X m omega)
    {m : ℕ}
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k))
    (hm : moreoverMinimalScale X delta sigma omega ≤ (3 : ℝ) ^ m)
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) {n : ℕ}
    (hn1 : (m : ℤ) - ⌈A * Real.log (B * (m : ℝ))⌉ ≤ (n : ℤ)) (hn2 : n ≤ m)
    {Q : TriadicCube d} (hQscale : Q.scale = (n : ℤ))
    (hQmem : cubeCenter Q ∈ cubeSet (originCube d (m : ℤ))) :
    matrixOperatorNorm
        (volumeAverageMat (cubeSet Q)
          (centeredStreamField omega (cubeSet (originCube d (m : ℤ))))) ≤
      A * Real.log (B * (m : ℝ)) * delta * (m : ℝ) ^ sigma := by
  have hm3 : 3 ≤ m := three_le_of_moreoverMinimalScale_le hm
  set L : ℝ := A * Real.log (B * (m : ℝ)) with hL
  have hm3R : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
  have hBm : (3 : ℝ) ≤ B * (m : ℝ) := by nlinarith only [hB, hm3R]
  have hlog : (1 : ℝ) < Real.log (B * (m : ℝ)) :=
    lt_of_lt_of_le one_lt_log_three
      (Real.log_le_log (by norm_num) hBm)
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hL]
    nlinarith only [hA, hlog]
  set h : ℕ := max 1 (m - n) with hh
  have hh0 : 0 < h := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hhm : h ≤ m := by
    rw [hh]
    omega
  have hwin : m - h ≤ n := by
    rw [hh]
    omega
  have hle1 := matrixOperatorNorm_volumeAverageMat_centeredStreamField_le_scaleMax
    omega hwin hn2 hQscale hQmem hsum
  have hXle := moreoverEnvelope_le_of_moreoverMinimalScale_le hgood hm
  have hmax : ((h : ℝ))⁻¹ * centeredScaleCubeMax h m omega ≤
      delta * (m : ℝ) ^ sigma / 2 :=
    le_trans (hwindow m h hh0 hhm) hXle
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh0
  have hmax' : centeredScaleCubeMax h m omega ≤
      (h : ℝ) * (delta * (m : ℝ) ^ sigma / 2) := by
    have := mul_le_mul_of_nonneg_left hmax hhR.le
    rwa [← mul_assoc, mul_inv_cancel₀ hhR.ne', one_mul] at this
  have hceil : (((m - n : ℕ) : ℝ)) ≤ L + 1 := by
    have hz : ((m - n : ℕ) : ℤ) ≤ ⌈L⌉ := by omega
    have hzR : (((m - n : ℕ) : ℤ) : ℝ) ≤ ((⌈L⌉ : ℤ) : ℝ) := by exact_mod_cast hz
    have hlt : ((⌈L⌉ : ℤ) : ℝ) < L + 1 := Int.ceil_lt_add_one L
    push_cast at hzR
    linarith only [hzR, hlt]
  have hhL : ((h : ℝ)) ≤ 2 * L := by
    rw [hh]
    have hcast : ((max 1 (m - n) : ℕ) : ℝ) = max (1 : ℝ) ((m - n : ℕ) : ℝ) := by
      push_cast
      rfl
    rw [hcast]
    exact max_le (by linarith only [hL1]) (by linarith only [hceil, hL1])
  have hpow : (0 : ℝ) ≤ (m : ℝ) ^ sigma :=
    Real.rpow_nonneg (Nat.cast_nonneg m) sigma
  calc matrixOperatorNorm
        (volumeAverageMat (cubeSet Q)
          (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))))
      ≤ centeredScaleCubeMax h m omega := hle1
    _ ≤ (h : ℝ) * (delta * (m : ℝ) ^ sigma / 2) := hmax'
    _ ≤ (2 * L) * (delta * (m : ℝ) ^ sigma / 2) := by
        refine mul_le_mul_of_nonneg_right hhL ?_
        positivity
    _ = L * delta * (m : ℝ) ^ sigma := by ring

end Moreover

end

end Stream
end Estimates
end Section2
end SuperdiffusionCLT
