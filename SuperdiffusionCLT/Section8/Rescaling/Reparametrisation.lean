/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Rescaling.DilationMoments

/-!
# Existence of the reparametrisation `delta = delta(ep)`

The proof of the invariance principle (Section 8) chooses `delta = delta(ep)` by
`delta ^ 2 * (8 * cstar * |log delta|) ^ (1/2) = ep ^ 2`.  With `reparamScale` the left-hand side
(see `DilationMoments`), this file proves:

* `repar_exists`: for `0 < cstar` there is `ep0 > 0` such that every `0 < ep < ep0` has a
  solution `delta` in `(0, exp (-1/2))`, the interval on which `reparamScale` is strictly
  increasing, so the solution is unique there;
* `repar_exists_fun`: a function `delta` of `ep` solving the relation for all small `ep`;
* `repar_tendsto_zero`: any such function tends to `0` through positive values as `ep -> 0+`.

The asymptotic relation is in `Reparametrisation B`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Rescaling

open Filter Topology

noncomputable section

/-- On `(0, exp (-1/2))` the reparametrisation scale is a square root. -/
theorem repar_scale_eq_sqrt {cStar z : ℝ} (hlog : Real.log z < 0) :
    reparamScale cStar z = Real.sqrt (z ^ 4 * (8 * cStar * (-Real.log z))) := by
  rw [reparamScale, abs_of_neg hlog, ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (show (0 : ℝ) ≤ z ^ 4 by positivity), show z ^ 4 = (z ^ 2) ^ 2 by ring,
    Real.sqrt_sq (sq_nonneg z)]

/-- The reparametrisation scale is continuous away from `0`. -/
theorem repar_continuousOn {cStar : ℝ} :
    ContinuousOn (reparamScale cStar) {z : ℝ | z ≠ 0} := by
  unfold reparamScale
  refine (continuousOn_id.pow 2).mul (ContinuousOn.rpow_const ?_ (fun _ _ => Or.inr (by norm_num)))
  exact (continuousOn_const.mul (Real.continuousOn_log.abs)).mono (fun z hz => hz)

/-- The reparametrisation scale tends to `0` at `0+`. -/
theorem repar_tendsto_scale_zero {cStar : ℝ} :
    Tendsto (reparamScale cStar) (𝓝[>] 0) (𝓝 0) := by
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero (r := 4) (by norm_num)
  have h1 : Tendsto (fun z : ℝ => z ^ 4 * (8 * cStar * (-Real.log z))) (𝓝[>] 0) (𝓝 0) := by
    have h2 := hlog.const_mul (-(8 * cStar))
    rw [mul_zero] at h2
    refine h2.congr (fun z => ?_)
    have h4 : z ^ (4 : ℝ) = z ^ 4 := by exact_mod_cast Real.rpow_natCast z 4
    rw [h4]
    ring
  have h3 : Tendsto (fun z : ℝ => Real.sqrt (z ^ 4 * (8 * cStar * (-Real.log z))))
      (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    rwa [Real.sqrt_zero] at this
  refine h3.congr' ?_
  have hmem : Set.Ioo (0 : ℝ) (Real.exp (-(1 / 2 : ℝ))) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (Real.exp_pos _)
  filter_upwards [hmem] with z hz
  have hl : Real.log z < 0 := by
    have h := Real.log_lt_log hz.1 hz.2
    rw [Real.log_exp] at h
    linarith only [h]
  exact (repar_scale_eq_sqrt hl).symm

/-- The reparametrisation scale is positive on `(0, exp (-1/2))`. -/
theorem repar_scale_pos {cStar z : ℝ} (hc : 0 < cStar)
    (hz : z ∈ Set.Ioo 0 (Real.exp (-(1 / 2 : ℝ)))) : 0 < reparamScale cStar z := by
  have hl : Real.log z < 0 := by
    have h := Real.log_lt_log hz.1 hz.2
    rw [Real.log_exp] at h
    linarith only [h]
  rw [repar_scale_eq_sqrt hl]
  have h0 : 0 < z := hz.1
  have : 0 < -Real.log z := by linarith only [hl]
  exact Real.sqrt_pos.2 (by positivity)

/-- **Existence of the reparametrisation.**  For `0 < cstar` there is `ep0 > 0` such that for every
`0 < ep < ep0` some `delta` in `(0, exp (-1/2))` satisfies
`delta ^ 2 * (8 * cstar * |log delta|) ^ (1/2) = ep ^ 2`.  It is unique in that interval by
`strictMonoOn_reparamScale`. -/
theorem repar_exists {cStar : ℝ} (hc : 0 < cStar) :
    ∃ ep0 : ℝ, 0 < ep0 ∧ ∀ ep : ℝ, 0 < ep → ep < ep0 →
      ∃ delta ∈ Set.Ioo 0 (Real.exp (-(1 / 2 : ℝ))),
        reparamScale cStar delta = ep ^ 2 := by
  have hd1 : Real.exp (-1 : ℝ) < Real.exp (-(1 / 2 : ℝ)) := Real.exp_lt_exp.2 (by norm_num)
  have hd1m : Real.exp (-1 : ℝ) ∈ Set.Ioo 0 (Real.exp (-(1 / 2 : ℝ))) := ⟨Real.exp_pos _, hd1⟩
  have hpos := repar_scale_pos hc hd1m
  refine ⟨Real.sqrt (reparamScale cStar (Real.exp (-1))), Real.sqrt_pos.2 hpos, ?_⟩
  intro ep hep hlt
  have hsq : ep ^ 2 < reparamScale cStar (Real.exp (-1)) := by
    have := pow_lt_pow_left₀ hlt hep.le (two_ne_zero)
    rwa [Real.sq_sqrt hpos.le] at this
  have hev : ∀ᶠ z in 𝓝[>] (0 : ℝ), reparamScale cStar z < ep ^ 2 :=
    repar_tendsto_scale_zero.eventually_lt_const (by positivity)
  obtain ⟨a, ha1, ha2⟩ := ((hev.and (Ioo_mem_nhdsGT (Real.exp_pos (-1)))).exists)
  have hcont : ContinuousOn (reparamScale cStar) (Set.Icc a (Real.exp (-1))) :=
    repar_continuousOn.mono (fun z hz => (lt_of_lt_of_le ha2.1 hz.1).ne')
  obtain ⟨δ, hδ, hδeq⟩ := intermediate_value_Icc ha2.2.le hcont ⟨ha1.le, hsq.le⟩
  exact ⟨δ, ⟨lt_of_lt_of_le ha2.1 hδ.1, lt_of_le_of_lt hδ.2 hd1⟩, hδeq⟩

/-- A function `delta` of `ep` solving the reparametrisation relation for all small `ep`. -/
theorem repar_exists_fun {cStar : ℝ} (hc : 0 < cStar) :
    ∃ delta : ℝ → ℝ, ∀ᶠ ep in 𝓝[>] (0 : ℝ),
      delta ep ∈ Set.Ioo 0 (Real.exp (-(1 / 2 : ℝ))) ∧
        reparamScale cStar (delta ep) = ep ^ 2 := by
  obtain ⟨ep0, h0, h⟩ := repar_exists hc
  classical
  refine ⟨fun ep => if hep : 0 < ep ∧ ep < ep0 then (h ep hep.1 hep.2).choose else 1, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT h0] with ep hep
  have hep' : 0 < ep ∧ ep < ep0 := hep
  simp only [hep', and_self, ↓reduceDIte]
  exact (h ep hep'.1 hep'.2).choose_spec

/-- **Any solution of the relation tends to `0`.**  If `delta ep` lies in `(0, exp (-1/2))` and
solves the relation for all small `ep`, then `delta ep -> 0` through positive values. -/
theorem repar_tendsto_zero {cStar : ℝ} (hc : 0 < cStar) {delta : ℝ → ℝ}
    (h : ∀ᶠ ep in 𝓝[>] (0 : ℝ), delta ep ∈ Set.Ioo 0 (Real.exp (-(1 / 2 : ℝ))) ∧
      reparamScale cStar (delta ep) = ep ^ 2) :
    Tendsto delta (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, h.mono fun ep hep => hep.1.1⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · exact h.mono fun ep hep => lt_trans ha hep.1.1
  · set η := min (a / 2) (Real.exp (-1)) with hη
    have hηpos : 0 < η := lt_min (by linarith only [ha]) (Real.exp_pos _)
    have hηm : η ∈ Set.Ioo 0 (Real.exp (-(1 / 2 : ℝ))) :=
      ⟨hηpos, lt_of_le_of_lt (min_le_right _ _) (Real.exp_lt_exp.2 (by norm_num))⟩
    have hfp := repar_scale_pos hc hηm
    have hsq : Tendsto (fun ep : ℝ => ep ^ 2) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((continuous_pow 2).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have hev := hsq.eventually_lt_const hfp
    filter_upwards [h, hev] with ep hep hlt
    by_contra hge
    have hηle : η ≤ delta ep := by
      have : η < a := by linarith only [hηpos, min_le_left (a / 2) (Real.exp (-1)), ha]
      linarith only [not_lt.1 hge, this]
    have := (strictMonoOn_reparamScale hc).monotoneOn hηm hep.1 hηle
    rw [hep.2] at this
    linarith only [this, hlt]

/-- Witness: for `cstar = 1` the relation has a solution for every small `ep`. -/
example : ∃ ep0 : ℝ, 0 < ep0 ∧ ∀ ep : ℝ, 0 < ep → ep < ep0 →
    ∃ delta ∈ Set.Ioo 0 (Real.exp (-(1 / 2 : ℝ))), reparamScale 1 delta = ep ^ 2 :=
  repar_exists one_pos

end

end SuperdiffusionCLT.Section8.Rescaling
