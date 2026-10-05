/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Rescaling.Reparametrisation

/-!
# Asymptotics of the reparametrisation `delta = delta(ep)`

The proof of the invariance principle (Section 8) asserts that if
`delta ^ 2 * (8 * cstar * |log delta|) ^ (1/2) = ep ^ 2` then `delta -> 0` and
`ep * |log ep ^ 2| ^ (-1/4) / delta -> sqrt (2 * cstar ^ (1/2))`.  Existence of `delta` and
`delta -> 0` are in `Reparametrisation`.  Here:

* `repar_tendsto_ratio`: the limit, for any function `delta` solving the relation for small `ep`;
* `repar_comparison`: constants `c1, C1 > 0` with
  `c1 * ep * |log ep| ^ (-1/4) <= delta ep <= C1 * ep * |log ep| ^ (-1/4)` for small `ep`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Rescaling

open Filter Topology

noncomputable section

/-- The ratio `8 c L / (2 L - log (8 c L) / 2)` tends to `4 c` as `L -> infinity`. -/
theorem repar_tendsto_Q {cStar : ℝ} (hc : 0 < cStar) :
    Tendsto (fun L : ℝ => 8 * cStar * L / (2 * L - Real.log (8 * cStar * L) / 2)) atTop
      (𝓝 (4 * cStar)) := by
  have hlog : Tendsto (fun L : ℝ => Real.log L / L) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hconst : Tendsto (fun L : ℝ => Real.log (8 * cStar) / L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hg : Tendsto (fun L : ℝ => Real.log (8 * cStar * L) / L) atTop (𝓝 0) := by
    have := hconst.add hlog
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with L hL
    rw [Real.log_mul (by positivity) hL.ne']
    ring
  have hden : Tendsto (fun L : ℝ => 2 - Real.log (8 * cStar * L) / L / 2) atTop (𝓝 2) := by
    have := tendsto_const_nhds (x := (2 : ℝ)) |>.sub (hg.div_const 2)
    simpa using this
  have hQ := (tendsto_const_nhds (x := 8 * cStar)).div hden (by norm_num)
  have h2 : 8 * cStar / 2 = 4 * cStar := by ring
  rw [h2] at hQ
  refine hQ.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with L hL
  have hd : 2 - Real.log (8 * cStar * L) / L / 2 = (2 * L - Real.log (8 * cStar * L) / 2) / L := by
    field_simp
  simp only [Pi.div_apply]
  rw [hd, div_div_eq_mul_div]

/-- The closed form of `sqrt (2 * sqrt c)` as a fourth root of `4 c`. -/
theorem repar_limit_eq {cStar : ℝ} (hc : 0 < cStar) :
    (4 * cStar) ^ (1 / 4 : ℝ) = Real.sqrt (2 * Real.sqrt cStar) := by
  have h4 : 4 * cStar = (2 * Real.sqrt cStar) ^ (2 : ℕ) := by
    rw [mul_pow, Real.sq_sqrt hc.le]
    ring
  rw [h4, Real.sqrt_eq_rpow (2 * Real.sqrt cStar), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-- Pointwise identities for one solution of the relation: with `L = -log delta`,
`ep = delta * (8 c L) ^ (1/4)` and `|log ep ^ 2| = 2 L - log (8 c L) / 2`. -/
theorem repar_pointwise {cStar ep delta : ℝ} (hc : 0 < cStar) (hep : 0 < ep) (hep1 : ep < 1)
    (hd : delta ∈ Set.Ioo 0 (Real.exp (-(1 / 2 : ℝ))))
    (hrel : reparamScale cStar delta = ep ^ 2) :
    ep * |Real.log (ep ^ 2)| ^ (-(1 / 4 : ℝ)) / delta
      = (8 * cStar * (-Real.log delta) / (2 * (-Real.log delta)
          - Real.log (8 * cStar * (-Real.log delta)) / 2)) ^ (1 / 4 : ℝ) := by
  have hd0 : 0 < delta := hd.1
  have hl : Real.log delta < 0 := by
    have h := Real.log_lt_log hd0 hd.2
    rw [Real.log_exp] at h
    linarith only [h]
  set L := -Real.log delta with hL
  have hLpos : 0 < L := by linarith only [hl, hL]
  have h8 : 0 < 8 * cStar * L := by positivity
  have hrel' : delta ^ 2 * (8 * cStar * L) ^ (1 / 2 : ℝ) = ep ^ 2 := by
    rw [← hrel, reparamScale, abs_of_neg hl]
  have hfour : ep = delta * (8 * cStar * L) ^ (1 / 4 : ℝ) := by
    have h14 : ((8 * cStar * L) ^ (1 / 4 : ℝ)) ^ 2 = (8 * cStar * L) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h8.le]
      norm_num
    have hsq : (delta * (8 * cStar * L) ^ (1 / 4 : ℝ)) ^ 2 = ep ^ 2 := by
      rw [← hrel', mul_pow, h14]
    have hnn : 0 ≤ delta * (8 * cStar * L) ^ (1 / 4 : ℝ) := by positivity
    exact ((pow_left_inj₀ hep.le hnn two_ne_zero).1 hsq.symm)
  have hlogsq : Real.log (ep ^ 2) = -(2 * L - Real.log (8 * cStar * L) / 2) := by
    rw [← hrel', Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_rpow h8]
    have : Real.log delta = -L := by linarith only [hL]
    rw [this]
    push_cast
    ring
  have hneg : Real.log (ep ^ 2) < 0 := Real.log_neg (by positivity) (by nlinarith only [hep, hep1])
  have habs : |Real.log (ep ^ 2)| = 2 * L - Real.log (8 * cStar * L) / 2 := by
    rw [abs_of_neg hneg, hlogsq]
    ring
  have hApos : 0 < 2 * L - Real.log (8 * cStar * L) / 2 := by
    rw [← habs]
    exact abs_pos.2 hneg.ne
  rw [habs, Real.div_rpow h8.le hApos.le, hfour, Real.rpow_neg hApos.le]
  field_simp

/-- **The asymptotic relation.**  For any function `delta` of `ep` with values in
`(0, exp (-1/2))` solving `delta ^ 2 * (8 * cstar * |log delta|) ^ (1/2) = ep ^ 2` for all small
`ep`,
`ep * |log ep ^ 2| ^ (-1/4) / delta ep -> sqrt (2 * sqrt cstar)` as `ep -> 0+`. -/
theorem repar_tendsto_ratio {cStar : ℝ} (hc : 0 < cStar) {delta : ℝ → ℝ}
    (h : ∀ᶠ ep in 𝓝[>] (0 : ℝ), delta ep ∈ Set.Ioo 0 (Real.exp (-(1 / 2 : ℝ))) ∧
      reparamScale cStar (delta ep) = ep ^ 2) :
    Tendsto (fun ep : ℝ => ep * |Real.log (ep ^ 2)| ^ (-(1 / 4 : ℝ)) / delta ep) (𝓝[>] 0)
      (𝓝 (Real.sqrt (2 * Real.sqrt cStar))) := by
  have hd0 := repar_tendsto_zero hc h
  have hL : Tendsto (fun ep : ℝ => -Real.log (delta ep)) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp ((Real.tendsto_log_nhdsGT_zero).comp hd0)
  have hQ := ((repar_tendsto_Q hc).comp hL).rpow_const
    (p := (1 / 4 : ℝ)) (Or.inl (by positivity))
  rw [repar_limit_eq hc] at hQ
  refine hQ.congr' ?_
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
  filter_upwards [h, hmem] with ep hep hep1
  exact (repar_pointwise hc hep1.1 hep1.2 hep.1 hep.2).symm

/-- **Comparison with `ep |log ep| ^ (-1/4)`.**  There are `c1, C1 > 0` with
`c1 * (ep * |log ep| ^ (-1/4)) <= delta ep <= C1 * (ep * |log ep| ^ (-1/4))` for all small `ep`. -/
theorem repar_comparison {cStar : ℝ} (hc : 0 < cStar) {delta : ℝ → ℝ}
    (h : ∀ᶠ ep in 𝓝[>] (0 : ℝ), delta ep ∈ Set.Ioo 0 (Real.exp (-(1 / 2 : ℝ))) ∧
      reparamScale cStar (delta ep) = ep ^ 2) :
    ∃ c1 C1 : ℝ, 0 < c1 ∧ 0 < C1 ∧ ∀ᶠ ep in 𝓝[>] (0 : ℝ),
      c1 * (ep * |Real.log ep| ^ (-(1 / 4 : ℝ))) ≤ delta ep ∧
        delta ep ≤ C1 * (ep * |Real.log ep| ^ (-(1 / 4 : ℝ))) := by
  set κ := Real.sqrt (2 * Real.sqrt cStar) with hκ
  have hκpos : 0 < κ := Real.sqrt_pos.2 (by positivity)
  have hT := repar_tendsto_ratio hc h
  have hlo : ∀ᶠ ep in 𝓝[>] (0 : ℝ),
      κ / 2 < ep * |Real.log (ep ^ 2)| ^ (-(1 / 4 : ℝ)) / delta ep :=
    hT.eventually_const_lt (by linarith only [hκpos])
  have hhi : ∀ᶠ ep in 𝓝[>] (0 : ℝ),
      ep * |Real.log (ep ^ 2)| ^ (-(1 / 4 : ℝ)) / delta ep < 2 * κ :=
    hT.eventually_lt_const (by linarith only [hκpos])
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
  set a : ℝ := (2 : ℝ) ^ (-(1 / 4 : ℝ)) with ha
  have hapos : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨a / (2 * κ), 2 * a / κ, by positivity, by positivity, ?_⟩
  filter_upwards [h, hlo, hhi, hmem] with ep hep h1 h2 hep1
  have hd0 : 0 < delta ep := hep.1.1
  have hlogneg : Real.log ep < 0 := Real.log_neg hep1.1 hep1.2
  have hlog2 : |Real.log (ep ^ 2)| = 2 * |Real.log ep| := by
    rw [Real.log_pow, abs_of_neg hlogneg]
    push_cast
    rw [abs_of_neg (by linarith only [hlogneg])]
    ring
  have habsl : 0 < |Real.log ep| := abs_pos.2 hlogneg.ne
  set R := ep * |Real.log ep| ^ (-(1 / 4 : ℝ)) with hR
  have hRpos : 0 < R := mul_pos hep1.1 (Real.rpow_pos_of_pos habsl _)
  have hrat : ep * |Real.log (ep ^ 2)| ^ (-(1 / 4 : ℝ)) = a * R := by
    rw [hlog2, Real.mul_rpow (by norm_num) habsl.le, hR, ha]
    ring
  rw [hrat] at h1 h2
  rw [lt_div_iff₀ hd0] at h1
  rw [div_lt_iff₀ hd0] at h2
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith only [h2]
  · rw [div_mul_eq_mul_div, le_div_iff₀ hκpos]
    linarith only [h1]

/-- Witness: for `cstar = 1` a solution function exists, so the limit and the comparison apply. -/
example : ∃ c1 C1 : ℝ, 0 < c1 ∧ 0 < C1 := by
  obtain ⟨delta, h⟩ := repar_exists_fun (cStar := 1) one_pos
  obtain ⟨c1, C1, h1, h2, -⟩ := repar_comparison one_pos h
  exact ⟨c1, C1, h1, h2⟩

end

end SuperdiffusionCLT.Section8.Rescaling
