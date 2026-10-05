/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import SuperdiffusionCLT.Probability.OrliczProduct
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers

/-!
# Capping a `Γ_{1/4}` product by a `Γ_{1/2}` crude bound

In the recentering step of `p.new.mixing.attempt` the parameterized mixing lemma is applied at
the random skew shift `h0 = -(k_{m'})_{cu_m}`. The localization error then contributes the product
`shom⁻¹ |h0|² · Z` of a `Γ₁` variable and a `Γ_{1/3}` variable, which the multiplication rule
`l.o.gamma2.mult` only places in `Γ_{1/4}`. The class `Γ_{1/3}` is recovered by capping with the
crude deep-scale bound, which holds for the same quantity in `Γ_{1/2}` with a polynomial
amplitude: the product controls the moderate tail and the crude bound controls the far tail.

* `srootNS_le_max_zero_add_min`: if `Φ ≤ T + B` and `Φ ≤ G`, then `Φ ≤ max T 0 + min B G`.
* `srootNS_isBigOWith_min_cap`: if `X = O_{Γ_{1/4}}(E)`, `G = O_{Γ_{1/2}}(D)` and `E D ≤ δ²`, then
  `min X G = O_{Γ_{1/3}}(δ)`.
* `srootNS_isBigOWith_min_mul_cap`: the same for `X = U V` with `U = O_{Γ₁}(A)`,
  `V = O_{Γ_{1/3}}(B)`, under `16 A B D ≤ δ²`.
* `srootNS_isBigO_min_mul_cap`: the absolute-value form for nonnegative variables.
* `srootNS_weighted_sum_cap_le`: the cap passes through a weighted sum with total weight at most
  one, so it is applied once to the whole near-scale sum.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory

noncomputable section

/-- Splitting a quantity bounded both by `T + B` and by a cap `G`. -/
theorem srootNS_le_max_zero_add_min {Φ T B G : ℝ} (h1 : Φ ≤ T + B) (h2 : Φ ≤ G) :
    Φ ≤ max T 0 + min B G := by
  rcases le_total B G with hBG | hGB
  · rw [min_eq_left hBG]
    linarith only [h1, le_max_left T 0]
  · rw [min_eq_right hGB]
    linarith only [h2, le_max_right T 0]

private theorem srootNS_le_rpow_inv_of_pow_le {u s : ℝ} {k : ℕ} (hk : k ≠ 0) (hu : 0 ≤ u)
    (hs : u ^ k ≤ s) : u ≤ s ^ ((k : ℝ)⁻¹) := by
  have h := Real.rpow_le_rpow (pow_nonneg hu k) hs (inv_nonneg.2 (Nat.cast_nonneg k))
  rwa [Real.pow_rpow_inv_natCast hu hk] at h

/-- **The cap.** A `Γ_{1/4}` variable at amplitude `E`, capped by a `Γ_{1/2}` variable at
amplitude `D`, is `Γ_{1/3}` at any amplitude `δ` with `E D ≤ δ²`. For `t ≥ 1` write
`u = t^{1/3}`: when `u E ≤ δ` the first tail at `δ t = E (δ t / E)` is at most
`exp(-(δ t / E)^{1/4}) ≤ exp(-u)`; otherwise `D ≤ u δ`, and the second tail at
`δ t = D (δ t / D)` is at most `exp(-(δ t / D)^{1/2}) ≤ exp(-u)`. -/
theorem srootNS_isBigOWith_min_cap {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X G : Ω → ℝ} {E D δ : ℝ} (hE : 0 < E) (hD : 0 < D) (hδ : 0 < δ)
    (hX : Homogenization.IndependentSums.IsBigOWith μ
      (Homogenization.IndependentSums.gammaSigma (1 / 4)) X E)
    (hG : Homogenization.IndependentSums.IsBigOWith μ
      (Homogenization.IndependentSums.gammaSigma (1 / 2)) G D)
    (hcap : E * D ≤ δ ^ 2) :
    Homogenization.IndependentSums.IsBigOWith μ
      (Homogenization.IndependentSums.gammaSigma (1 / 3)) (fun ω => min (X ω) (G ω)) δ := by
  rw [Homogenization.IndependentSums.isBigOWith_gammaSigma_iff]
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  set u : ℝ := t ^ ((1 : ℝ) / 3) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg ht0.le _
  have hu1 : 1 ≤ u := Real.one_le_rpow ht (by norm_num)
  have htu : t = u ^ 3 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    norm_num
  by_cases hcase : u * E ≤ δ
  · set s : ℝ := δ * t / E with hs
    have hs4 : u ^ 4 ≤ s := by
      rw [hs, le_div_iff₀ hE]
      have h : u ^ 4 * E = (u * E) * t := by rw [htu]; ring
      rw [h]
      exact mul_le_mul_of_nonneg_right hcase ht0.le
    have hs1 : 1 ≤ s := le_trans (one_le_pow₀ hu1) hs4
    have hus : u ≤ s ^ ((1 : ℝ) / 4) := by
      have h := srootNS_le_rpow_inv_of_pow_le (k := 4) (by norm_num) hu0 hs4
      have h4 : ((4 : ℕ) : ℝ)⁻¹ = (1 : ℝ) / 4 := by norm_num
      rwa [h4] at h
    have hEs : E * s = δ * t := by
      rw [hs]
      field_simp
    have hsub : Homogenization.IndependentSums.upperTailEvent (fun ω => min (X ω) (G ω)) (δ * t) ⊆
        Homogenization.IndependentSums.upperTailEvent X (E * s) := by
      intro ω hω
      simp only [Homogenization.IndependentSums.mem_upperTailEvent] at hω ⊢
      rw [hEs]
      exact lt_of_lt_of_le hω (min_le_left _ _)
    calc μ.real (Homogenization.IndependentSums.upperTailEvent (fun ω => min (X ω) (G ω)) (δ * t))
        ≤ μ.real (Homogenization.IndependentSums.upperTailEvent X (E * s)) := measureReal_mono hsub
      _ ≤ Real.exp (-(s ^ ((1 : ℝ) / 4))) :=
          Homogenization.IndependentSums.isBigOWith_gammaSigma_iff.1 hX hs1
      _ ≤ Real.exp (-u) := Real.exp_le_exp.2 (neg_le_neg hus)
  · have hlt : δ < u * E := lt_of_not_ge hcase
    have hDu : D ≤ u * δ := by
      have h1 : δ * δ ≤ δ * (u * E) := mul_le_mul_of_nonneg_left hlt.le hδ.le
      have h2 : E * D ≤ E * (u * δ) := by
        have hsq : δ ^ 2 = δ * δ := by ring
        have heq : δ * (u * E) = E * (u * δ) := by ring
        linarith only [hcap, h1, hsq, heq]
      exact le_of_mul_le_mul_left h2 hE
    set s : ℝ := δ * t / D with hs
    have hs2 : u ^ 2 ≤ s := by
      rw [hs, le_div_iff₀ hD]
      have h : δ * t = (u * δ) * u ^ 2 := by rw [htu]; ring
      rw [h, mul_comm (u ^ 2) D]
      exact mul_le_mul_of_nonneg_right hDu (sq_nonneg u)
    have hs1 : 1 ≤ s := le_trans (one_le_pow₀ hu1) hs2
    have hus : u ≤ s ^ ((1 : ℝ) / 2) := by
      have h := srootNS_le_rpow_inv_of_pow_le (k := 2) (by norm_num) hu0 hs2
      have h2 : ((2 : ℕ) : ℝ)⁻¹ = (1 : ℝ) / 2 := by norm_num
      rwa [h2] at h
    have hDs : D * s = δ * t := by
      rw [hs]
      field_simp
    have hsub : Homogenization.IndependentSums.upperTailEvent (fun ω => min (X ω) (G ω)) (δ * t) ⊆
        Homogenization.IndependentSums.upperTailEvent G (D * s) := by
      intro ω hω
      simp only [Homogenization.IndependentSums.mem_upperTailEvent] at hω ⊢
      rw [hDs]
      exact lt_of_lt_of_le hω (min_le_right _ _)
    calc μ.real (Homogenization.IndependentSums.upperTailEvent (fun ω => min (X ω) (G ω)) (δ * t))
        ≤ μ.real (Homogenization.IndependentSums.upperTailEvent G (D * s)) := measureReal_mono hsub
      _ ≤ Real.exp (-(s ^ ((1 : ℝ) / 2))) :=
          Homogenization.IndependentSums.isBigOWith_gammaSigma_iff.1 hG hs1
      _ ≤ Real.exp (-u) := Real.exp_le_exp.2 (neg_le_neg hus)

/-- The multiplication constant of `l.o.gamma2.mult` at the indices `1` and `1/3`. -/
theorem srootNS_orliczProductConst_one_third :
    SuperdiffusionCLT.Probability.orliczProductConst 1 (1 / 3) = 16 := by
  rw [SuperdiffusionCLT.Probability.orliczProductConst,
    show ((1 : ℝ)⁻¹ + (1 / 3 : ℝ)⁻¹) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- **The capped product.** For nonnegative `U = O_{Γ₁}(A)` and `V = O_{Γ_{1/3}}(B)`, the product
`U V` capped by `G = O_{Γ_{1/2}}(D)` is `O_{Γ_{1/3}}(δ)` as soon as `16 A B D ≤ δ²`. -/
theorem srootNS_isBigOWith_min_mul_cap {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {U V G : Ω → ℝ} {A B D δ : ℝ} (hA : 0 < A) (hB : 0 < B) (hD : 0 < D)
    (hδ : 0 < δ) (hU0 : ∀ ω, 0 ≤ U ω) (hV0 : ∀ ω, 0 ≤ V ω)
    (hU : Homogenization.IndependentSums.IsBigOWith μ
      (Homogenization.IndependentSums.gammaSigma 1) U A)
    (hV : Homogenization.IndependentSums.IsBigOWith μ
      (Homogenization.IndependentSums.gammaSigma (1 / 3)) V B)
    (hG : Homogenization.IndependentSums.IsBigOWith μ
      (Homogenization.IndependentSums.gammaSigma (1 / 2)) G D)
    (hcap : 16 * (A * B) * D ≤ δ ^ 2) :
    Homogenization.IndependentSums.IsBigOWith μ
      (Homogenization.IndependentSums.gammaSigma (1 / 3)) (fun ω => min (U ω * V ω) (G ω)) δ := by
  have hP := SuperdiffusionCLT.Probability.isBigOWith_gammaSigma_mul (σ₁ := 1)
    (σ₂ := 1 / 3) one_pos (by norm_num) hA.le hB.le hU0 hV0 hU hV
  rw [srootNS_orliczProductConst_one_third,
    show ((1 : ℝ) * (1 / 3) / (1 + 1 / 3)) = 1 / 4 by norm_num] at hP
  exact srootNS_isBigOWith_min_cap (X := fun ω => U ω * V ω) (by positivity) hD hδ hP hG hcap

/-- **The capped product, absolute-value form.** -/
theorem srootNS_isBigO_min_mul_cap {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {U V G : Ω → ℝ} {A B D δ : ℝ} (hA : 0 < A) (hB : 0 < B) (hD : 0 < D)
    (hδ : 0 < δ) (hU0 : ∀ ω, 0 ≤ U ω) (hV0 : ∀ ω, 0 ≤ V ω) (hG0 : ∀ ω, 0 ≤ G ω)
    (hU : Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma 1) U A)
    (hV : Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma (1 / 3)) V B)
    (hG : Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma (1 / 2)) G D)
    (hcap : 16 * (A * B) * D ≤ δ ^ 2) :
    Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma (1 / 3)) (fun ω => min (U ω * V ω) (G ω)) δ := by
  have hM0 : ∀ ω, 0 ≤ min (U ω * V ω) (G ω) := fun ω =>
    le_min (mul_nonneg (hU0 ω) (hV0 ω)) (hG0 ω)
  refine (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg hM0).1 ?_
  exact srootNS_isBigOWith_min_mul_cap hA hB hD hδ hU0 hV0
    ((SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg hU0).2 hU)
    ((SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg hV0).2 hV)
    ((SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg hG0).2 hG) hcap

/-- **The cap through a weighted sum.** With nonnegative weights of total mass at most one, a
family bounded termwise by `max T_l 0 + min B_l G`, with every `B_l ≤ Bmax` and `0 ≤ min Bmax G`,
sums to at most `∑ w_l max T_l 0 + min Bmax G`. -/
theorem srootNS_weighted_sum_cap_le (N : ℕ) {w Φ T B : ℕ → ℝ} {Bmax G : ℝ}
    (hw0 : ∀ l, 0 ≤ w l) (hw1 : ∑ l ∈ Finset.range N, w l ≤ 1)
    (hΦ : ∀ l ∈ Finset.range N, Φ l ≤ max (T l) 0 + min (B l) G)
    (hB : ∀ l ∈ Finset.range N, B l ≤ Bmax) (hcap0 : 0 ≤ min Bmax G) :
    ∑ l ∈ Finset.range N, w l * Φ l ≤
      ∑ l ∈ Finset.range N, w l * max (T l) 0 + min Bmax G := by
  have hterm : ∀ l ∈ Finset.range N,
      w l * Φ l ≤ w l * max (T l) 0 + w l * min Bmax G := by
    intro l hl
    have h1 : Φ l ≤ max (T l) 0 + min Bmax G :=
      (hΦ l hl).trans (add_le_add le_rfl (min_le_min_right G (hB l hl)))
    have h2 := mul_le_mul_of_nonneg_left h1 (hw0 l)
    linarith only [h2]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  have hlast : (∑ l ∈ Finset.range N, w l) * min Bmax G ≤ min Bmax G := by
    have := mul_le_mul_of_nonneg_right hw1 hcap0
    linarith only [this]
  linarith only [hsum, hlast]

/-! ## Satisfiability of the hypotheses -/

end

end SuperdiffusionCLT.Section4.MinimalScales
