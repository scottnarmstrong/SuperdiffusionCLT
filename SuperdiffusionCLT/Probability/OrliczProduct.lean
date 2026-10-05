/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.WeakOrlicz

/-!
# The multiplication rule for `O_{Gamma_sigma}` random variables

This module states Lemma `l.o.gamma2.mult` of the paper in the indexing of the paper, and
proves it directly from the tail definition, because no product rule for `IsBigOWith` /
`IsBigO` in the `gammaSigma` classes exists in the `CoarseGraining` library (its
`Homogenization/Probability/IndependentSums/` directory carries sum, maximum
and power rules — `isBigO_finset_sum_of_isBigO_gammaSigma`,
`isBigOWith_gammaSigma_finset_sup'` and the power rule
`isBigOWith_gammaSigma_rpow` — but no product rule).

The printed statement reads: for `sigma_1, sigma_2 in (0, oo)` and positive
random variables,

`X_1 <= O_{Gamma_{sigma_1}}(A_1)  and  X_2 <= O_{Gamma_{sigma_2}}(A_2)
  implies  X_1 X_2 <= O_{Gamma_{sigma_1 sigma_2 / (sigma_1 + sigma_2)}}(C A_1 A_2)`
(display `e.multGammasig`).

Here `X <= O_Psi(A)` is the tail relation `P[X > t A] <= Psi(t)⁻¹` for every
`t in [1, ∞)` and `Gamma_sigma(t) = exp(t ^ sigma)`.

## The constant

The constant `C` of display `e.multGammasig` is read as
`C(sigma_1, sigma_2)`, inside the scope of the binder "for every
`sigma_1, sigma_2 in (0, ∞)`"; no universal constant is asserted,
and the rule is stated for nonnegative random variables. The explicit value
recorded here is

`orliczProductConst sigma_1 sigma_2 = 2 ^ (sigma_1⁻¹ + sigma_2⁻¹)`,

which is positive and at least `2 ^ 0 = 1`.

## The proof

Fix `t >= 1` and write `sigma = sigma_1 sigma_2 / (sigma_1 + sigma_2)`,
`a = sigma / sigma_1 = sigma_2 / (sigma_1 + sigma_2)` and
`b = sigma / sigma_2 = sigma_1 / (sigma_1 + sigma_2)`, so that `a + b = 1`.
Split the product event at the two thresholds `c_1 t ^ a A_1` and
`c_2 t ^ b A_2` with `c_i = 2 ^ (sigma_i⁻¹)`:

`{X_1 X_2 > C A_1 A_2 t} ⊆ {X_1 > c_1 t ^ a A_1} ∪ {X_2 > c_2 t ^ b A_2}`,

because `c_1 c_2 = 2 ^ (sigma_1⁻¹ + sigma_2⁻¹) = C` and
`t ^ a t ^ b = t ^ (a + b) = t`. The union bound and the two tail hypotheses,
evaluated at the arguments `c_1 t ^ a >= 1` and `c_2 t ^ b >= 1`, give

`P <= exp(-(c_1 t ^ a) ^ sigma_1) + exp(-(c_2 t ^ b) ^ sigma_2)
    = 2 exp(-(2 t ^ sigma)) <= exp(-(t ^ sigma))`,

the last step because `t ^ sigma >= 1` and `2 = 1 + 1 <= exp 1
<= exp(t ^ sigma)`. The factor `2` in front of the tail is thus absorbed into
the exponent margin `2 t ^ sigma >= t ^ sigma`, which is what makes the
constant `C = 2 ^ (sigma_1⁻¹ + sigma_2⁻¹)` explicit rather than leaving an
unresolved multiplicative factor in front of the tail.

## Main results

* `orliczProductConst` and `orliczProductConst_pos`: the explicit constant
  `C(sigma_1, sigma_2) = 2 ^ (sigma_1⁻¹ + sigma_2⁻¹)` of display
  `e.multGammasig` and its positivity.
* `isBigOWith_gammaSigma_mul`: the printed rule in the one-sided sense
  `X_1 X_2 <= O_{Gamma_sigma}(C A_1 A_2)` of display `e.multGammasig`.
* `isBigO_gammaSigma_mul`: the symmetric sense, the form in which consumers
  apply the rule to signed quantities through absolute values.
-/

@[expose] public section

namespace SuperdiffusionCLT.Probability

open MeasureTheory
open Homogenization

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The explicit constant `C(sigma_1, sigma_2)` of the printed multiplication
rule (display `e.multGammasig`): it may depend on the two
indices, and the value recorded here is `2 ^ (sigma_1⁻¹ + sigma_2⁻¹)`. -/
noncomputable def orliczProductConst (sigma₁ sigma₂ : ℝ) : ℝ :=
  (2 : ℝ) ^ (sigma₁⁻¹ + sigma₂⁻¹)

/-- The constant of the multiplication rule is positive, for all real indices:
the base `2` is positive and a real power of a positive base is positive. -/
theorem orliczProductConst_pos (sigma₁ sigma₂ : ℝ) :
    0 < orliczProductConst sigma₁ sigma₂ := by
  have h₁ : (0 : ℝ) < 2 ^ sigma₁⁻¹ := Real.rpow_pos_of_pos zero_lt_two _
  have h₂ : (0 : ℝ) < 2 ^ sigma₂⁻¹ := Real.rpow_pos_of_pos zero_lt_two _
  dsimp [orliczProductConst]
  positivity

/-- The margin lemma that absorbs the union-bound factor `2`: for `u >= 1`,
`2 * exp(-2 u) <= exp(-u)`, because `2 = 1 + 1 <= exp 1 <= exp u`. -/
private theorem two_mul_exp_neg_two_mul_le_exp_neg {u : ℝ} (hu : 1 ≤ u) :
    (2 : ℝ) * Real.exp (-(2 * u)) ≤ Real.exp (-u) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp 1]
  have hmono : Real.exp 1 ≤ Real.exp u := Real.exp_le_exp.2 hu
  have htwo' : (2 : ℝ) ≤ Real.exp u := htwo.trans hmono
  calc (2 : ℝ) * Real.exp (-(2 * u))
      ≤ Real.exp u * Real.exp (-(2 * u)) :=
        mul_le_mul_of_nonneg_right htwo' (by positivity)
    _ = Real.exp (u + -(2 * u)) := (Real.exp_add u (-(2 * u))).symm
    _ = Real.exp (-u) := by rw [show u + -(2 * u) = -u by ring]

/-- The one-sided form of the printed multiplication property
`l.o.gamma2.mult`: if `X_1` and `X_2` satisfy the tail
bounds `X_1 <= O_{Gamma_{sigma_1}}(A_1)` and
`X_2 <= O_{Gamma_{sigma_2}}(A_2)`, then their product
satisfies

`X_1 X_2 <= O_{Gamma_{sigma_1 sigma_2 / (sigma_1 + sigma_2)}}
  (orliczProductConst sigma_1 sigma_2 * (A_1 A_2))`,

which is the display `e.multGammasig` with the explicit constant
`C(sigma_1, sigma_2) = 2 ^ (sigma_1⁻¹ + sigma_2⁻¹)` recorded here. The variables are
assumed nonnegative, as the reading of the printed "positive random variables";
the amplitudes are nonnegative as well, matching the
printed convention `A > 0`. -/
theorem isBigOWith_gammaSigma_mul {mu : Measure Omega} [IsFiniteMeasure mu]
    {X₁ X₂ : Omega → ℝ} {A₁ A₂ σ₁ σ₂ : ℝ}
    (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hX₁ : ∀ omega, 0 ≤ X₁ omega) (hX₂ : ∀ omega, 0 ≤ X₂ omega)
    (h₁ : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma σ₁) X₁ A₁)
    (h₂ : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma σ₂) X₂ A₂) :
    IndependentSums.IsBigOWith mu
      (IndependentSums.gammaSigma (σ₁ * σ₂ / (σ₁ + σ₂)))
      (fun omega => X₁ omega * X₂ omega)
      (orliczProductConst σ₁ σ₂ * (A₁ * A₂)) := by
  rw [IndependentSums.isBigOWith_gammaSigma_iff]
  intro t ht
  have hσ₁ne : σ₁ ≠ 0 := ne_of_gt hσ₁
  have hσ₂ne : σ₂ ≠ 0 := ne_of_gt hσ₂
  have hsumne : σ₁ + σ₂ ≠ 0 := ne_of_gt (add_pos hσ₁ hσ₂)
  set s : ℝ := σ₁ * σ₂ / (σ₁ + σ₂) with hs_def
  have hσ : 0 < s := div_pos (mul_pos hσ₁ hσ₂) (add_pos hσ₁ hσ₂)
  set a : ℝ := s / σ₁ with ha_def
  set b : ℝ := s / σ₂ with hb_def
  have hab : a + b = 1 := by
    rw [ha_def, hb_def, hs_def]
    field_simp
    ring
  have has : a * σ₁ = s := div_mul_cancel₀ s hσ₁ne
  have hbs : b * σ₂ = s := div_mul_cancel₀ s hσ₂ne
  -- the split thresholds `c_i t ^ (sigma / sigma_i)` with `c_i = 2 ^ sigma_i⁻¹`
  set c₁ : ℝ := (2 : ℝ) ^ (σ₁⁻¹) with hc₁_def
  set c₂ : ℝ := (2 : ℝ) ^ (σ₂⁻¹) with hc₂_def
  have hc₁pos : 0 < c₁ := Real.rpow_pos_of_pos zero_lt_two _
  have hc₂pos : 0 < c₂ := Real.rpow_pos_of_pos zero_lt_two _
  have hC : orliczProductConst σ₁ σ₂ = c₁ * c₂ := by
    rw [orliczProductConst, hc₁_def, hc₂_def, Real.rpow_add zero_lt_two]
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have ha_nonneg : 0 ≤ a := div_nonneg hσ.le hσ₁.le
  have hb_nonneg : 0 ≤ b := div_nonneg hσ.le hσ₂.le
  have ht_a_nonneg : 0 ≤ t ^ a := Real.rpow_nonneg ht0 a
  have ht_b_nonneg : 0 ≤ t ^ b := Real.rpow_nonneg ht0 b
  have ht0pos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hta : t ^ a * t ^ b = t := by
    rw [← Real.rpow_add ht0pos, hab, Real.rpow_one]
  have hts : 1 ≤ t ^ s := Real.one_le_rpow ht hσ.le
  have hc₁pow : c₁ ^ σ₁ = 2 := by
    rw [hc₁_def, ← Real.rpow_mul zero_le_two, inv_mul_cancel₀ hσ₁ne, Real.rpow_one]
  have hc₂pow : c₂ ^ σ₂ = 2 := by
    rw [hc₂_def, ← Real.rpow_mul zero_le_two, inv_mul_cancel₀ hσ₂ne, Real.rpow_one]
  have ht_pow_a : (t ^ a) ^ σ₁ = t ^ s := by
    rw [← Real.rpow_mul ht0, has]
  have ht_pow_b : (t ^ b) ^ σ₂ = t ^ s := by
    rw [← Real.rpow_mul ht0, hbs]
  have hpow₁ : (c₁ * t ^ a) ^ σ₁ = 2 * t ^ s := by
    rw [Real.mul_rpow hc₁pos.le ht_a_nonneg, hc₁pow, ht_pow_a]
  have hpow₂ : (c₂ * t ^ b) ^ σ₂ = 2 * t ^ s := by
    rw [Real.mul_rpow hc₂pos.le ht_b_nonneg, hc₂pow, ht_pow_b]
  -- the tail hypotheses at the two split thresholds, both arguments at least 1
  have harg₁ : 1 ≤ c₁ * t ^ a := by
    have h₁c : (1 : ℝ) ≤ c₁ := Real.one_le_rpow (by norm_num) (inv_nonneg.2 hσ₁.le)
    have h₁t : (1 : ℝ) ≤ t ^ a := Real.one_le_rpow ht ha_nonneg
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ c₁ * t ^ a := mul_le_mul h₁c h₁t (by positivity) hc₁pos.le
  have harg₂ : 1 ≤ c₂ * t ^ b := by
    have h₂c : (1 : ℝ) ≤ c₂ := Real.one_le_rpow (by norm_num) (inv_nonneg.2 hσ₂.le)
    have h₂t : (1 : ℝ) ≤ t ^ b := Real.one_le_rpow ht hb_nonneg
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ c₂ * t ^ b := mul_le_mul h₂c h₂t (by positivity) hc₂pos.le
  have ht₁ : mu.real (IndependentSums.upperTailEvent X₁ (A₁ * (c₁ * t ^ a)))
      ≤ Real.exp (-((c₁ * t ^ a) ^ σ₁)) :=
    IndependentSums.isBigOWith_gammaSigma_iff.1 h₁ harg₁
  have ht₂ : mu.real (IndependentSums.upperTailEvent X₂ (A₂ * (c₂ * t ^ b)))
      ≤ Real.exp (-((c₂ * t ^ b) ^ σ₂)) :=
    IndependentSums.isBigOWith_gammaSigma_iff.1 h₂ harg₂
  -- the product event is covered by the union of the two split events
  have hsubset :
      IndependentSums.upperTailEvent (fun omega => X₁ omega * X₂ omega)
        ((orliczProductConst σ₁ σ₂ * (A₁ * A₂)) * t) ⊆
        IndependentSums.upperTailEvent X₁ (A₁ * (c₁ * t ^ a)) ∪
          IndependentSums.upperTailEvent X₂ (A₂ * (c₂ * t ^ b)) := by
    intro omega homega
    rw [IndependentSums.mem_upperTailEvent] at homega
    by_cases hc : A₁ * (c₁ * t ^ a) < X₁ omega
    · exact Set.mem_union_left _ (IndependentSums.mem_upperTailEvent.2 hc)
    · have h1 : X₁ omega ≤ A₁ * (c₁ * t ^ a) := le_of_not_gt hc
      have h2 : A₂ * (c₂ * t ^ b) < X₂ omega := by
        by_contra hcon
        push Not at hcon
        have hthr₁ : 0 ≤ A₁ * (c₁ * t ^ a) :=
          mul_nonneg hA₁ (mul_nonneg hc₁pos.le ht_a_nonneg)
        have hthr₂ : 0 ≤ A₂ * (c₂ * t ^ b) :=
          mul_nonneg hA₂ (mul_nonneg hc₂pos.le ht_b_nonneg)
        refine homega.not_ge ?_
        have hprod : X₁ omega * X₂ omega ≤
            (A₁ * (c₁ * t ^ a)) * (A₂ * (c₂ * t ^ b)) := by
          nlinarith only [h1, hcon, hX₁ omega, hX₂ omega, hthr₁, hthr₂]
        calc X₁ omega * X₂ omega
            ≤ (A₁ * (c₁ * t ^ a)) * (A₂ * (c₂ * t ^ b)) := hprod
          _ = orliczProductConst σ₁ σ₂ * (A₁ * A₂) * t := by
              calc (A₁ * (c₁ * t ^ a)) * (A₂ * (c₂ * t ^ b))
                  = (A₁ * A₂) * (c₁ * c₂) * (t ^ a * t ^ b) := by ring
                _ = orliczProductConst σ₁ σ₂ * (A₁ * A₂) * t := by
                    rw [hC, hta]
                    ring
      exact Set.mem_union_right _ (IndependentSums.mem_upperTailEvent.2 h2)
  calc mu.real (IndependentSums.upperTailEvent (fun omega => X₁ omega * X₂ omega)
      ((orliczProductConst σ₁ σ₂ * (A₁ * A₂)) * t))
    ≤ mu.real (IndependentSums.upperTailEvent X₁ (A₁ * (c₁ * t ^ a))) +
        mu.real (IndependentSums.upperTailEvent X₂ (A₂ * (c₂ * t ^ b))) :=
      (measureReal_mono hsubset).trans (measureReal_union_le _ _)
  _ ≤ Real.exp (-((c₁ * t ^ a) ^ σ₁)) + Real.exp (-((c₂ * t ^ b) ^ σ₂)) :=
      add_le_add ht₁ ht₂
  _ ≤ Real.exp (-(2 * t ^ s)) + Real.exp (-(2 * t ^ s)) :=
      add_le_add (by rw [hpow₁]) (by rw [hpow₂])
  _ = (2 : ℝ) * Real.exp (-(2 * t ^ s)) := by ring
  _ ≤ Real.exp (-(t ^ s)) := two_mul_exp_neg_two_mul_le_exp_neg hts

/-- The printed multiplication property `l.o.gamma2.mult` in the sense in which consumers
apply it to signed quantities through absolute values: from
`|X_1| <= O_{Gamma_{sigma_1}}(A_1)` and `|X_2| <= O_{Gamma_{sigma_2}}(A_2)` it
follows that `|X_1 X_2| = |X_1| |X_2| <= O_{Gamma_{sigma_1 sigma_2 /
(sigma_1 + sigma_2)}}(orliczProductConst sigma_1 sigma_2 * (A_1 A_2))`, which
is the display `e.multGammasig` with the symmetric reading of the
`O` symbol of the paper. -/
theorem isBigO_gammaSigma_mul {mu : Measure Omega} [IsFiniteMeasure mu]
    {X₁ X₂ : Omega → ℝ} {A₁ A₂ σ₁ σ₂ : ℝ}
    (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (h₁ : IndependentSums.IsBigO mu (IndependentSums.gammaSigma σ₁) X₁ A₁)
    (h₂ : IndependentSums.IsBigO mu (IndependentSums.gammaSigma σ₂) X₂ A₂) :
    IndependentSums.IsBigO mu
      (IndependentSums.gammaSigma (σ₁ * σ₂ / (σ₁ + σ₂)))
      (fun omega => X₁ omega * X₂ omega)
      (orliczProductConst σ₁ σ₂ * (A₁ * A₂)) := by
  have habs : (fun omega => |X₁ omega * X₂ omega|) =
      fun omega => |X₁ omega| * |X₂ omega| :=
    funext fun omega => abs_mul _ _
  rw [IndependentSums.IsBigO, habs]
  exact isBigOWith_gammaSigma_mul hσ₁ hσ₂ hA₁ hA₂
    (fun omega => abs_nonneg _) (fun omega => abs_nonneg _) h₁ h₂

end SuperdiffusionCLT.Probability