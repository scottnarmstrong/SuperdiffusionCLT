/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.PSeries
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockF

/-!
# The geometric summation of the "Moreover" block

In the proof of `e.mathcal.K.int`, the union bound over the
scales above the threshold turns the per-scale estimate
`P[X_K > ½ δ K^σ] ≤ exp(-(δ K^σ / 2A)²)` of `measureReal_moreoverBadEvent_le`
into the bad-tail estimate

`∀ N, B ≤ N → P[badTailEvent Bad N] ≤ exp(-(N/B)^{2σ})`,

which is the exact hypothesis of `isBigO_gammaSigma_log_quenchedMinimalScale`.

## The summation

Write `c := δ² / (4 A²)` and `η := 2 σ`, so that the per-scale bound is
`exp(-c K^η)`. The elementary inequality `t^η ≥ 1 + η log t` for `t ≥ 1` gives,
for every `K ≥ N`,

`c K^η = (c N^η) (K/N)^η ≥ u + u η log (K/N)`,  `u := c N^η`,

hence `exp(-c K^η) ≤ exp(-u) (K/N)^{-u η}`. As soon as `u η ≥ 2` the exponent
may be relaxed to `-2`, and `∑_{K ≥ N} (N/K)² ≤ 2 N` by `sum_Ioo_inv_sq_le`.
This is `tsum_exp_neg_mul_rpow_le`:

`∑_{K ≥ N} exp(-c K^η) ≤ 2 N exp(-u)`.

The remaining step is the comparison `2 N exp(-u) ≤ exp(-u/Θ)`, which after
taking logarithms is `log 2 + log N + u/Θ ≤ u`. The tangent-line bound
`log x ≤ x/T + log T - 1` at `T := 3/(c η)` converts `log N` into `u/3` plus a
`c`-dependent constant, and the value

`Θ := 3 + 2/η + (3/η) max(0, log (3/(c η)))`

absorbs everything. The scale is `B := (Θ/c)^{1/η}`, for which
`(N/B)^η = u/Θ`.

## The size of the scale

With `η = 2 σ` and `c = δ²/(4 A²)` the scale is

`B = (2 A δ⁻¹ √Θ)^{1/σ}`,  `Θ = 3 + σ⁻¹ + (3/(2σ)) max(0, log (6 A² δ⁻² σ⁻¹))`,

which is the print's `N_σ = (C σ⁻¹ δ⁻¹)^{1/σ}` **up to the factor `√Θ`**. That
factor is not an artefact of this route: the union bound applied to the
per-scale estimates is saturated when the bad events are disjoint, and
`∑_{K ≥ N} exp(-c K^η) ≥ e^{-1} exp(-c N^η) · #{K : c K^η ≤ c N^η + 1}`, whose
last factor is of order `N / (c N^η η)`. Requiring the sum to be at most
`exp(-(N/B)^η)` at the smallest admissible `N` therefore forces
`c B^η ≳ log B`, that is `Θ ≳ (2/η) log B = σ⁻¹ log(2 A δ⁻¹ √Θ)`; at `σ = 1`
this makes `B ≳ 2 A δ⁻¹ √(log(2 A δ⁻¹))`, which exceeds `C₂ δ⁻¹ σ⁻¹` for every
fixed `C₂` once `δ` is small enough. The printed amplitude
`C₁ (C₂ δ⁻¹ σ⁻¹)^{1/σ}` with `C₁, C₂` depending only on `d` and `s` is
therefore **not** reachable from the per-scale estimates alone; the honest
amplitude is `2 (log 3) (2 A δ⁻¹ √Θ)^{1/σ}`. The printed shape follows only under an extra side
condition on `(δ, σ)`, which is not proved here.

## Main definitions and results

* `expTailTheta`, `expTailScale`: the constant `Θ` and the scale `B`.
* `tsum_inv_sq_shift_le`: `∑_{K ≥ N} K⁻² ≤ 2/N`.
* `tsum_exp_neg_mul_rpow_le`: `∑_{K ≥ N} exp(-c K^η) ≤ 2 N exp(-c N^η)`.
* `tsum_exp_neg_mul_rpow_le_exp_neg_div`: the summation in the shape the union
  bound consumes.
* `measureReal_badTailEvent_moreoverBadEvent_le`: the exact hypothesis of
  `isBigO_gammaSigma_log_quenchedMinimalScale`.
* `isBigO_gammaSigma_log_moreoverMinimalScale`: the `Γ_{2σ}` tail of
  `log K_σ` at the amplitude `2 (log 3) B`.

## References

* `e.mathcal.K.int`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Estimates
namespace Stream

open Homogenization MeasureTheory
open Homogenization.Book.Ch05.Section57
open Homogenization.IndependentSums
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal

noncomputable section

/-! ## The inverse-square tail -/

/-- The shifted inverse-square series is summable. -/
theorem summable_inv_sq_shift (N : ℕ) :
    Summable fun j : ℕ => (((N + j : ℕ) : ℝ) ^ 2)⁻¹ := by
  have hbase : Summable fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ :=
    Real.summable_nat_pow_inv.2 (by norm_num)
  have := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) N).2 hbase
  simpa only [Nat.cast_add, add_comm] using this

/-- The tail of the inverse-square series above a positive integer. -/
theorem tsum_inv_sq_shift_le {N : ℕ} (hN : 1 ≤ N) :
    ∑' j : ℕ, (((N + j : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 / (N : ℝ) := by
  refine (summable_inv_sq_shift N).tsum_le_of_sum_le fun s => ?_
  obtain ⟨n, hn⟩ : ∃ n : ℕ, s ⊆ Finset.range n :=
    ⟨s.sup id + 1, fun i hi => Finset.mem_range.2
      (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))⟩
  have hstep : ∑ j ∈ s, (((N + j : ℕ) : ℝ) ^ 2)⁻¹ ≤
      ∑ j ∈ Finset.range n, (((N + j : ℕ) : ℝ) ^ 2)⁻¹ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hn fun j _ _ => by positivity
  refine le_trans hstep ?_
  have hrange : ∑ j ∈ Finset.range n, (((N + j : ℕ) : ℝ) ^ 2)⁻¹ =
      ∑ i ∈ Finset.Ico N (N + n), ((i : ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
  rw [hrange]
  have hsub : Finset.Ico N (N + n) ⊆ Finset.Ioo (N - 1) (N + n) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_Ioo]
    exact ⟨by omega, hi.2⟩
  have hmono : ∑ i ∈ Finset.Ico N (N + n), ((i : ℝ) ^ 2)⁻¹ ≤
      ∑ i ∈ Finset.Ioo (N - 1) (N + n), ((i : ℝ) ^ 2)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
  refine le_trans hmono ?_
  have hcast : (((N - 1 : ℕ) : ℝ) + 1) = (N : ℝ) := by
    have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      have := Nat.cast_sub (R := ℝ) hN
      simpa using this
    rw [this]
    ring
  have hbound := sum_Ioo_inv_sq_le (α := ℝ) (N - 1) (N + n)
  rwa [hcast] at hbound

/-! ## The summation of the stretched-exponential tail -/

/-- **The per-scale comparison.** For `K ≥ N ≥ 1` and `c N^η η ≥ 2`, the
elementary bound `t^η ≥ 1 + η log t` at `t = K/N` turns the stretched
exponential into an inverse square. -/
theorem exp_neg_mul_rpow_le_inv_sq {c eta : ℝ} (hc : 0 < c)
    {N K : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K)
    (hp : 2 ≤ c * (N : ℝ) ^ eta * eta) :
    Real.exp (-(c * (K : ℝ) ^ eta)) ≤
      Real.exp (-(c * (N : ℝ) ^ eta)) * ((N : ℝ) ^ 2 * ((K : ℝ) ^ 2)⁻¹) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hKR : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hN hNK
  set t : ℝ := (K : ℝ) / (N : ℝ) with ht
  have ht0 : (0 : ℝ) < t := div_pos hKR hNR
  have ht1 : (1 : ℝ) ≤ t := by
    rw [ht, le_div_iff₀ hNR, one_mul]
    exact_mod_cast hNK
  have hKtN : (K : ℝ) = t * (N : ℝ) := by
    rw [ht]
    field_simp
  set u : ℝ := c * (N : ℝ) ^ eta with hu
  have hupos : 0 < u := mul_pos hc (Real.rpow_pos_of_pos hNR eta)
  set p : ℝ := u * eta with hpdef
  have hp2 : (2 : ℝ) ≤ p := by
    rw [hpdef, hu]
    exact hp
  have hKpow : c * (K : ℝ) ^ eta = u * t ^ eta := by
    rw [hKtN, Real.mul_rpow ht0.le hNR.le, hu]
    ring
  have htail : (1 : ℝ) + eta * Real.log t ≤ t ^ eta := by
    rw [Real.rpow_def_of_pos ht0]
    have := Real.add_one_le_exp (eta * Real.log t)
    have hcomm : Real.log t * eta = eta * Real.log t := by ring
    rw [hcomm]
    linarith only [this]
  have hlower : u + p * Real.log t ≤ c * (K : ℝ) ^ eta := by
    rw [hKpow, hpdef]
    have := mul_le_mul_of_nonneg_left htail hupos.le
    nlinarith only [this, hupos]
  have hstep1 : Real.exp (-(c * (K : ℝ) ^ eta)) ≤
      Real.exp (-u) * t ^ (-p) := by
    have hmono : Real.exp (-(c * (K : ℝ) ^ eta)) ≤
        Real.exp (-(u + p * Real.log t)) :=
      Real.exp_le_exp.2 (by linarith only [hlower])
    refine le_trans hmono (le_of_eq ?_)
    rw [Real.rpow_def_of_pos ht0, ← Real.exp_add]
    congr 1
    ring
  have hstep2 : t ^ (-p) ≤ t ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by linarith only [hp2])
  have hstep3 : t ^ (-(2 : ℝ)) = (N : ℝ) ^ 2 * ((K : ℝ) ^ 2)⁻¹ := by
    have hsq : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast t 2]
      norm_num
    rw [Real.rpow_neg ht0.le, hsq, ht, div_pow]
    field_simp
  calc Real.exp (-(c * (K : ℝ) ^ eta))
      ≤ Real.exp (-u) * t ^ (-p) := hstep1
    _ ≤ Real.exp (-u) * t ^ (-(2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep2 (Real.exp_pos _).le
    _ = Real.exp (-(c * (N : ℝ) ^ eta)) * ((N : ℝ) ^ 2 * ((K : ℝ) ^ 2)⁻¹) := by
        rw [hstep3, hu]

/-- The stretched-exponential series is summable above the exponent
threshold. -/
theorem summable_exp_neg_mul_rpow_shift {c eta : ℝ} (hc : 0 < c) {N : ℕ}
    (hN : 1 ≤ N) (hp : 2 ≤ c * (N : ℝ) ^ eta * eta) :
    Summable fun j : ℕ => Real.exp (-(c * (((N + j : ℕ)) : ℝ) ^ eta)) := by
  have hterm : ∀ j : ℕ, Real.exp (-(c * (((N + j : ℕ)) : ℝ) ^ eta)) ≤
      (Real.exp (-(c * (N : ℝ) ^ eta)) * (N : ℝ) ^ 2) *
        ((((N + j : ℕ)) : ℝ) ^ 2)⁻¹ := by
    intro j
    have := exp_neg_mul_rpow_le_inv_sq hc hN (Nat.le_add_right N j) hp
    rw [mul_assoc]
    exact this
  exact Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hterm
    ((summable_inv_sq_shift N).mul_left _)

/-- **The summation of the stretched-exponential tail.** -/
theorem tsum_exp_neg_mul_rpow_le {c eta : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (hp : 2 ≤ c * (N : ℝ) ^ eta * eta) :
    ∑' j : ℕ, Real.exp (-(c * (((N + j : ℕ)) : ℝ) ^ eta)) ≤
      2 * (N : ℝ) * Real.exp (-(c * (N : ℝ) ^ eta)) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set E : ℝ := Real.exp (-(c * (N : ℝ) ^ eta)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hterm : ∀ j : ℕ, Real.exp (-(c * (((N + j : ℕ)) : ℝ) ^ eta)) ≤
      (E * (N : ℝ) ^ 2) * ((((N + j : ℕ)) : ℝ) ^ 2)⁻¹ := by
    intro j
    have := exp_neg_mul_rpow_le_inv_sq hc hN (Nat.le_add_right N j) hp
    rw [mul_assoc]
    exact this
  have hmaj : Summable fun j : ℕ =>
      (E * (N : ℝ) ^ 2) * ((((N + j : ℕ)) : ℝ) ^ 2)⁻¹ :=
    (summable_inv_sq_shift N).mul_left _
  have hsummable : Summable fun j : ℕ =>
      Real.exp (-(c * (((N + j : ℕ)) : ℝ) ^ eta)) :=
    summable_exp_neg_mul_rpow_shift hc hN hp
  calc ∑' j : ℕ, Real.exp (-(c * (((N + j : ℕ)) : ℝ) ^ eta))
      ≤ ∑' j : ℕ, (E * (N : ℝ) ^ 2) * ((((N + j : ℕ)) : ℝ) ^ 2)⁻¹ :=
        hsummable.tsum_le_tsum hterm hmaj
    _ = (E * (N : ℝ) ^ 2) * ∑' j : ℕ, ((((N + j : ℕ)) : ℝ) ^ 2)⁻¹ :=
        tsum_mul_left
    _ ≤ (E * (N : ℝ) ^ 2) * (2 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (tsum_inv_sq_shift_le hN)
          (by positivity)
    _ = 2 * (N : ℝ) * E := by field_simp

/-! ## The scale of the summation -/

/-- The constant `Θ(c, η) = 3 + 2/η + (3/η) max(0, log (3/(c η)))` of the
summation. -/
def expTailTheta (c eta : ℝ) : ℝ :=
  3 + 2 / eta + 3 / eta * max 0 (Real.log (3 / (c * eta)))

/-- The scale `B(c, η) = (Θ/c)^{1/η}` of the summation. -/
def expTailScale (c eta : ℝ) : ℝ :=
  (expTailTheta c eta / c) ^ eta⁻¹

theorem three_le_expTailTheta {c eta : ℝ} (heta : 0 < eta) :
    (3 : ℝ) ≤ expTailTheta c eta := by
  have h1 : 0 < 2 / eta := by positivity
  have h2 : 0 ≤ 3 / eta * max 0 (Real.log (3 / (c * eta))) := by
    have : (0 : ℝ) ≤ max 0 (Real.log (3 / (c * eta))) := le_max_left _ _
    positivity
  rw [expTailTheta]
  linarith only [h1, h2]

theorem expTailTheta_pos {c eta : ℝ} (heta : 0 < eta) :
    0 < expTailTheta c eta :=
  lt_of_lt_of_le (by norm_num) (three_le_expTailTheta (c := c) heta)

/-- The constant `Θ` is large enough that `Θ η ≥ 2`, which is the exponent
condition of `exp_neg_mul_rpow_le_inv_sq`. -/
theorem two_le_expTailTheta_mul {c eta : ℝ} (heta : 0 < eta) :
    (2 : ℝ) ≤ expTailTheta c eta * eta := by
  have h1 : 2 / eta * eta = 2 := by field_simp
  have h2 : (0 : ℝ) ≤ 3 * eta := by positivity
  have h3 : 0 ≤ 3 / eta * max 0 (Real.log (3 / (c * eta))) * eta := by
    have : (0 : ℝ) ≤ max 0 (Real.log (3 / (c * eta))) := le_max_left _ _
    positivity
  rw [expTailTheta, add_mul, add_mul]
  linarith only [h1, h2, h3]

theorem expTailScale_pos {c eta : ℝ} (hc : 0 < c) (heta : 0 < eta) :
    0 < expTailScale c eta :=
  Real.rpow_pos_of_pos (div_pos (expTailTheta_pos (c := c) heta) hc) _

/-- The defining property of the scale: `B^η = Θ/c`. -/
theorem expTailScale_rpow {c eta : ℝ} (hc : 0 < c) (heta : 0 < eta) :
    expTailScale c eta ^ eta = expTailTheta c eta / c := by
  rw [expTailScale, ← Real.rpow_mul
    (le_of_lt (div_pos (expTailTheta_pos (c := c) heta) hc)),
    inv_mul_cancel₀ (ne_of_gt heta), Real.rpow_one]

/-! ## The summation in the shape the union bound consumes -/

/-- **The geometric summation of the union bound.** Above the scale
`B = (Θ/c)^{1/η}` the tail of the stretched-exponential series is at most
`exp(-(N/B)^η)`. -/
theorem tsum_exp_neg_mul_rpow_le_exp_neg_div {c eta : ℝ} (hc : 0 < c)
    (heta : 0 < eta) {N : ℕ} (hNB : expTailScale c eta ≤ (N : ℝ)) :
    ∑' j : ℕ, Real.exp (-(c * (((N + j : ℕ)) : ℝ) ^ eta)) ≤
      Real.exp (-(((N : ℝ) / expTailScale c eta) ^ eta)) := by
  set B : ℝ := expTailScale c eta with hB
  set Th : ℝ := expTailTheta c eta with hTh
  have hThpos : 0 < Th := expTailTheta_pos (c := c) heta
  have hTh3 : (3 : ℝ) ≤ Th := three_le_expTailTheta (c := c) heta
  have hBpos : 0 < B := expTailScale_pos hc heta
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hBpos hNB
  have hN1 : 1 ≤ N := by
    by_contra hcon
    have : N = 0 := by omega
    rw [this] at hNpos
    simp only [Nat.cast_zero, lt_irrefl] at hNpos
  set u : ℝ := c * (N : ℝ) ^ eta with hu
  have hupos : 0 < u := mul_pos hc (Real.rpow_pos_of_pos hNpos eta)
  have hBrpow : B ^ eta = Th / c := expTailScale_rpow hc heta
  have huTh : Th ≤ u := by
    have hmono : B ^ eta ≤ (N : ℝ) ^ eta :=
      Real.rpow_le_rpow hBpos.le hNB heta.le
    rw [hBrpow] at hmono
    have := mul_le_mul_of_nonneg_left hmono hc.le
    rw [mul_div_cancel₀ _ (ne_of_gt hc)] at this
    exact this
  have hp : (2 : ℝ) ≤ c * (N : ℝ) ^ eta * eta := by
    have h1 : Th * eta ≤ u * eta :=
      mul_le_mul_of_nonneg_right huTh heta.le
    have h2 := two_le_expTailTheta_mul (c := c) heta
    rw [← hTh] at h2
    rw [← hu]
    linarith only [h1, h2]
  have hsum := tsum_exp_neg_mul_rpow_le (c := c) (eta := eta) hc hN1 hp
  refine le_trans hsum ?_
  have hdiv : ((N : ℝ) / B) ^ eta = u / Th := by
    rw [Real.div_rpow hNpos.le hBpos.le, hBrpow, hu]
    field_simp
  rw [hdiv]
  -- the logarithmic comparison
  have hlogT : Real.log ((N : ℝ) ^ eta * (c * eta / 3)) ≤
      (N : ℝ) ^ eta * (c * eta / 3) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hsplit : Real.log ((N : ℝ) ^ eta * (c * eta / 3)) =
      eta * Real.log (N : ℝ) - Real.log (3 / (c * eta)) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hNpos]
    have hinv : c * eta / 3 = (3 / (c * eta))⁻¹ := by
      field_simp
    rw [hinv, Real.log_inv]
    ring
  have hval : (N : ℝ) ^ eta * (c * eta / 3) = u * eta / 3 := by
    rw [hu]; ring
  rw [hsplit, hval] at hlogT
  have hlogN : eta * Real.log (N : ℝ) ≤
      u * eta / 3 - 1 + Real.log (3 / (c * eta)) := by
    linarith only [hlogT]
  have hmaxge : Real.log (3 / (c * eta)) ≤ max 0 (Real.log (3 / (c * eta))) :=
    le_max_right _ _
  have huge : (3 : ℝ) + 2 / eta + 3 / eta * max 0 (Real.log (3 / (c * eta)))
      ≤ u := by
    rw [hTh, expTailTheta] at huTh
    exact huTh
  have hkey : Real.log (2 * (N : ℝ)) ≤ u - u / Th := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [this]
    have hmul : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log (N : ℝ) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)]
    have hdiv3 : u / Th ≤ u / 3 :=
      div_le_div_of_nonneg_left hupos.le (by norm_num) hTh3
    -- `eta * (log 2 + log N) ≤ eta * (2 u / 3)`
    have hstep : eta * Real.log (N : ℝ) + eta * Real.log 2 ≤ eta * (u * 2 / 3) := by
      have hA : eta * (3 + 2 / eta + 3 / eta * max 0 (Real.log (3 / (c * eta))))
          ≤ eta * u := mul_le_mul_of_nonneg_left huge heta.le
      have hB2 : eta * (2 / eta) = 2 := by field_simp
      have hC2 : eta * (3 / eta * max 0 (Real.log (3 / (c * eta))))
          = 3 * max 0 (Real.log (3 / (c * eta))) := by field_simp
      have hlog2eta : eta * Real.log 2 ≤ eta := by
        nlinarith only [hlog2, heta]
      have hmaxeta : eta * Real.log (3 / (c * eta)) ≤
          eta * max 0 (Real.log (3 / (c * eta))) :=
        mul_le_mul_of_nonneg_left hmaxge heta.le
      have hexpand : eta * (3 + 2 / eta + 3 / eta * max 0 (Real.log (3 / (c * eta))))
          = 3 * eta + 2 + 3 * max 0 (Real.log (3 / (c * eta))) := by
        field_simp
      rw [hexpand] at hA
      have hetalogN : eta * Real.log (N : ℝ) ≤
          u * eta / 3 - 1 + Real.log (3 / (c * eta)) := hlogN
      have hmax0 : (0 : ℝ) ≤ max 0 (Real.log (3 / (c * eta))) := le_max_left _ _
      have hetapos : 0 < eta := heta
      nlinarith only [hA, hetalogN, hlog2eta, hmaxge, hmax0, hetapos, hupos]
    have hfinal : Real.log 2 + Real.log (N : ℝ) ≤ u * 2 / 3 := by
      refine le_of_mul_le_mul_left ?_ heta
      linarith only [hstep]
    rw [hmul]
    linarith only [hfinal, hdiv3]
  have hexp : 2 * (N : ℝ) * Real.exp (-u) ≤ Real.exp (-(u / Th)) := by
    have h2N : (0 : ℝ) < 2 * (N : ℝ) := by positivity
    have hle : Real.exp (Real.log (2 * (N : ℝ))) * Real.exp (-u) ≤
        Real.exp (u - u / Th) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hkey) (Real.exp_pos _).le
    rw [Real.exp_log h2N, ← Real.exp_add] at hle
    have hsimp : u - u / Th + -u = -(u / Th) := by ring
    rwa [hsimp] at hle
  rw [← hu]
  exact hexp

/-! ## The bad-tail estimate of the "Moreover" block -/

section Moreover

variable {d : ℕ}

/-- **The scale `B` of the print's `N_σ`** for the "Moreover" block: the scale
of the summation at `c = δ²/(4 A²)` and `η = 2 σ`, that is
`B = (2 A δ⁻¹ √Θ)^{1/σ}`. -/
def moreoverTailScale (A delta sigma : ℝ) : ℝ :=
  expTailScale (delta ^ 2 / (4 * A ^ 2)) (2 * sigma)

theorem moreoverTailScale_pos {A delta sigma : ℝ} (hA : 0 < A) (hdelta : 0 < delta)
    (hsigma : 0 < sigma) : 0 < moreoverTailScale A delta sigma :=
  expTailScale_pos (by positivity) (by linarith only [hsigma])

/-- **The per-scale estimate in the normalization of the summation.** Above the
scale `B` the amplitude condition `2 A ≤ δ K^σ` of
`measureReal_moreoverBadEvent_le` holds, and its bound is exactly
`exp(-c K^{2σ})` with `c = δ²/(4 A²)`. -/
theorem measureReal_moreoverBadEvent_le_expTail {mu : Measure (ShellSeq d)}
    [IsFiniteMeasure mu] {X : ℕ → ShellSeq d → ℝ} {A delta sigma : ℝ}
    (hA : 0 < A) (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hX : ∀ m : ℕ, IsBigO mu (gammaSigma 2) (X m) A) {K : ℕ}
    (hK : moreoverTailScale A delta sigma ≤ (K : ℝ)) :
    mu.real (moreoverBadEvent X delta sigma K) ≤
      Real.exp (-(delta ^ 2 / (4 * A ^ 2) * (K : ℝ) ^ (2 * sigma))) := by
  set c : ℝ := delta ^ 2 / (4 * A ^ 2) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have heta : (0 : ℝ) < 2 * sigma := by linarith only [hsigma]
  have hBpos : 0 < moreoverTailScale A delta sigma :=
    moreoverTailScale_pos hA hdelta hsigma
  have hKpos : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le hBpos hK
  have hthree : (3 : ℝ) ≤ c * (K : ℝ) ^ (2 * sigma) := by
    have hmono : moreoverTailScale A delta sigma ^ (2 * sigma) ≤
        (K : ℝ) ^ (2 * sigma) := Real.rpow_le_rpow hBpos.le hK heta.le
    have hval : moreoverTailScale A delta sigma ^ (2 * sigma) =
        expTailTheta c (2 * sigma) / c := expTailScale_rpow hcpos heta
    rw [hval] at hmono
    have hmul := mul_le_mul_of_nonneg_left hmono hcpos.le
    rw [mul_div_cancel₀ _ (ne_of_gt hcpos)] at hmul
    exact le_trans (three_le_expTailTheta (c := c) heta) hmul
  have hpowid : ((K : ℝ) ^ sigma) ^ (2 : ℕ) = (K : ℝ) ^ (2 * sigma) := by
    rw [← Real.rpow_natCast ((K : ℝ) ^ sigma) 2, ← Real.rpow_mul hKpos.le]
    norm_num
    rw [mul_comm]
  have hid : (delta * (K : ℝ) ^ sigma / (2 * A)) ^ (2 : ℝ) =
      c * (K : ℝ) ^ (2 * sigma) := by
    rw [Real.rpow_two, div_pow, mul_pow, hpowid, hc]
    field_simp
    ring
  have hzsq : (1 : ℝ) ≤ (delta * (K : ℝ) ^ sigma / (2 * A)) ^ (2 : ℕ) := by
    rw [← Real.rpow_two, hid]
    linarith only [hthree]
  have hz0 : (0 : ℝ) ≤ delta * (K : ℝ) ^ sigma / (2 * A) := by
    have : (0 : ℝ) < (K : ℝ) ^ sigma := Real.rpow_pos_of_pos hKpos sigma
    positivity
  have hz1 : (1 : ℝ) ≤ delta * (K : ℝ) ^ sigma / (2 * A) := by
    nlinarith only [hzsq, hz0]
  have h2A : 2 * A ≤ delta * (K : ℝ) ^ sigma := by
    have h2Apos : (0 : ℝ) < 2 * A := by linarith only [hA]
    rw [le_div_iff₀ h2Apos, one_mul] at hz1
    exact hz1
  have hbound := measureReal_moreoverBadEvent_le hA hX h2A
  rwa [hid] at hbound

/-- **The bad-tail estimate of the union bound**, in the exact shape of the
hypothesis of `isBigO_gammaSigma_log_quenchedMinimalScale`. -/
theorem measureReal_badTailEvent_moreoverBadEvent_le {mu : Measure (ShellSeq d)}
    [IsFiniteMeasure mu] {X : ℕ → ShellSeq d → ℝ} {A delta sigma : ℝ}
    (hA : 0 < A) (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hX : ∀ m : ℕ, IsBigO mu (gammaSigma 2) (X m) A) {N : ℕ}
    (hN : moreoverTailScale A delta sigma ≤ (N : ℝ)) :
    mu.real (badTailEvent (moreoverBadEvent X delta sigma) N) ≤
      Real.exp (-(((N : ℝ) / moreoverTailScale A delta sigma) ^ (2 * sigma))) := by
  set c : ℝ := delta ^ 2 / (4 * A ^ 2) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have heta : (0 : ℝ) < 2 * sigma := by linarith only [hsigma]
  have hBpos : 0 < moreoverTailScale A delta sigma :=
    moreoverTailScale_pos hA hdelta hsigma
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hBpos hN
  have hN1 : 1 ≤ N := by
    by_contra hcon
    have hz : N = 0 := by omega
    rw [hz] at hNpos
    simp only [Nat.cast_zero, lt_irrefl] at hNpos
  have hp : (2 : ℝ) ≤ c * (N : ℝ) ^ (2 * sigma) * (2 * sigma) := by
    have hmono : moreoverTailScale A delta sigma ^ (2 * sigma) ≤
        (N : ℝ) ^ (2 * sigma) := Real.rpow_le_rpow hBpos.le hN heta.le
    have hval : moreoverTailScale A delta sigma ^ (2 * sigma) =
        expTailTheta c (2 * sigma) / c := expTailScale_rpow hcpos heta
    rw [hval] at hmono
    have hmul := mul_le_mul_of_nonneg_left hmono hcpos.le
    rw [mul_div_cancel₀ _ (ne_of_gt hcpos)] at hmul
    have := mul_le_mul_of_nonneg_right hmul heta.le
    exact le_trans (two_le_expTailTheta_mul (c := c) heta) this
  set f : ℕ → ℝ := fun j => Real.exp (-(c * (((N + j : ℕ)) : ℝ) ^ (2 * sigma)))
    with hf
  have hfsummable : Summable f := summable_exp_neg_mul_rpow_shift hcpos hN1 hp
  have hfnonneg : ∀ j : ℕ, 0 ≤ f j := fun j => (Real.exp_pos _).le
  have hterm : ∀ j : ℕ,
      mu (moreoverBadEvent X delta sigma (N + j)) ≤ ENNReal.ofReal (f j) := by
    intro j
    refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top mu _)
      (hfnonneg j)).2 ?_
    have hKN : moreoverTailScale A delta sigma ≤ ((N + j : ℕ) : ℝ) := by
      have : (N : ℝ) ≤ ((N + j : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_right N j
      linarith only [hN, this]
    exact measureReal_moreoverBadEvent_le_expTail hA hdelta hsigma hX hKN
  have hle_enn : mu (badTailEvent (moreoverBadEvent X delta sigma) N) ≤
      ENNReal.ofReal (∑' j : ℕ, f j) := by
    refine le_trans (measure_badTailEvent_le_tsum _ _) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg hfnonneg hfsummable]
    exact ENNReal.tsum_le_tsum hterm
  have hsum_nonneg : (0 : ℝ) ≤ ∑' j : ℕ, f j := tsum_nonneg hfnonneg
  have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle_enn
  rw [ENNReal.toReal_ofReal hsum_nonneg] at htoReal
  exact le_trans htoReal
    (tsum_exp_neg_mul_rpow_le_exp_neg_div hcpos heta hN)

/-! ### The `Γ_{2σ}` tail of `log K_σ` -/

/-- **The amplitude of the `Γ_{2σ}` tail of `log K_σ`**: the print's
`(log 3) N_σ`, with the triadic rounding factor `2` of
`isBigO_gammaSigma_log_quenchedMinimalScale` and the additive `4` that puts the
scale above the floor `N_0 + 1 = 4` of the construction. -/
def moreoverLogScaleAmplitude (A delta sigma : ℝ) : ℝ :=
  2 * (4 + moreoverTailScale A delta sigma) * Real.log 3

/-- The scale in the print's own shape: `B = (2 A δ⁻¹ √Θ)^{1/σ}`. -/
theorem moreoverTailScale_eq {A delta sigma : ℝ} (hA : 0 < A) (hdelta : 0 < delta)
    (hsigma : 0 < sigma) :
    moreoverTailScale A delta sigma =
      (2 * A * delta⁻¹ *
        Real.sqrt (expTailTheta (delta ^ 2 / (4 * A ^ 2)) (2 * sigma))) ^ sigma⁻¹ := by
  set c : ℝ := delta ^ 2 / (4 * A ^ 2) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have heta : (0 : ℝ) < 2 * sigma := by linarith only [hsigma]
  have hThpos : 0 < expTailTheta c (2 * sigma) := expTailTheta_pos (c := c) heta
  have hratio : (0 : ℝ) < expTailTheta c (2 * sigma) / c := div_pos hThpos hcpos
  have hsplit : (2 * sigma)⁻¹ = 2⁻¹ * sigma⁻¹ := by
    rw [mul_inv]
  have hsqrtc : Real.sqrt c = delta / (2 * A) := by
    rw [hc]
    rw [show delta ^ 2 / (4 * A ^ 2) = (delta / (2 * A)) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hbase : (expTailTheta c (2 * sigma) / c) ^ (2 : ℝ)⁻¹ =
      2 * A * delta⁻¹ * Real.sqrt (expTailTheta c (2 * sigma)) := by
    have hhalf : (expTailTheta c (2 * sigma) / c) ^ (2 : ℝ)⁻¹ =
        Real.sqrt (expTailTheta c (2 * sigma) / c) := by
      rw [Real.sqrt_eq_rpow]
      norm_num
    rw [hhalf, Real.sqrt_div' _ hcpos.le, hsqrtc]
    field_simp
  rw [moreoverTailScale, expTailScale, hsplit,
    Real.rpow_mul hratio.le, hbase]

/-- **The `Γ_{2σ}` tail of `log K_σ`** of `e.mathcal.K.int`, from a uniform `Γ₂`
amplitude `A` of the envelope family. -/
theorem isBigO_gammaSigma_log_moreoverMinimalScale {mu : Measure (ShellSeq d)}
    [IsFiniteMeasure mu] {X : ℕ → ShellSeq d → ℝ} {A delta sigma : ℝ}
    (hA : 0 < A) (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hX : ∀ m : ℕ, IsBigO mu (gammaSigma 2) (X m) A) :
    IsBigO mu (gammaSigma (2 * sigma))
      (fun omega => Real.log (moreoverMinimalScale X delta sigma omega))
      (moreoverLogScaleAmplitude A delta sigma) := by
  set B : ℝ := moreoverTailScale A delta sigma with hB
  have hBpos : 0 < B := moreoverTailScale_pos hA hdelta hsigma
  have hfloor : ((3 : ℕ) : ℝ) + 1 ≤ 4 + B := by
    push_cast
    linarith only [hBpos]
  have htail : ∀ N : ℕ, 4 + B ≤ (N : ℝ) →
      mu.real (badTailEvent (moreoverBadEvent X delta sigma) N) ≤
        Real.exp (-(((N : ℝ) / (4 + B)) ^ (2 * sigma))) := by
    intro N hN
    have hNB : B ≤ (N : ℝ) := by linarith only [hN]
    have hmain := measureReal_badTailEvent_moreoverBadEvent_le hA hdelta hsigma
      hX hNB
    refine le_trans hmain (Real.exp_le_exp.2 (neg_le_neg ?_))
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hdiv : (N : ℝ) / (4 + B) ≤ (N : ℝ) / B :=
      div_le_div_of_nonneg_left hNnn hBpos (by linarith only [hBpos])
    exact Real.rpow_le_rpow (by positivity) hdiv (by linarith only [hsigma])
  have hmain := isBigO_gammaSigma_log_quenchedMinimalScale
    (mu := mu) (N0 := 3) (Bad := moreoverBadEvent X delta sigma)
    (B := 4 + B) (sigma := sigma) hsigma hfloor htail
  exact hmain

/-- The tail at any larger amplitude. -/
theorem isBigO_gammaSigma_log_moreoverMinimalScale_of_le
    {mu : Measure (ShellSeq d)} [IsFiniteMeasure mu] {X : ℕ → ShellSeq d → ℝ}
    {A delta sigma theta : ℝ} (hA : 0 < A) (hdelta : 0 < delta)
    (hsigma : 0 < sigma) (hX : ∀ m : ℕ, IsBigO mu (gammaSigma 2) (X m) A)
    (hle : moreoverLogScaleAmplitude A delta sigma ≤ theta) :
    IsBigO mu (gammaSigma (2 * sigma))
      (fun omega => Real.log (moreoverMinimalScale X delta sigma omega))
      theta :=
  IsBigO.mono_scale (isBigO_gammaSigma_log_moreoverMinimalScale hA hdelta
    hsigma hX) hle

/-- **The exceptional set of the construction is null.** -/
theorem ae_hasGoodTailFrom_moreoverBadEvent {mu : Measure (ShellSeq d)}
    [IsFiniteMeasure mu] {X : ℕ → ShellSeq d → ℝ} {A delta sigma : ℝ}
    (hA : 0 < A) (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hX : ∀ m : ℕ, IsBigO mu (gammaSigma 2) (X m) A) (N0 : ℕ) :
    ∀ᵐ omega ∂mu, hasGoodTailFrom N0 (moreoverBadEvent X delta sigma) omega :=
  ae_hasGoodTailFrom_of_expTail (N0 := N0) hsigma
    (moreoverTailScale_pos hA hdelta hsigma)
    (fun _ hN => measureReal_badTailEvent_moreoverBadEvent_le hA hdelta hsigma
      hX hN)

end Moreover

end

end Stream
end Estimates
end Section2
end SuperdiffusionCLT
