/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmLNaughtGeLinear
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Pure arithmetic pieces of the bound `e.Theta.Lm.final.bound`
of the paper:

* `homogBelow_twoCalls_core`: the double application of [AK, Theorem 6.1], with
  the theorem's conclusion abstracted (`Θ`, `ω`, the startup-scale expression
  `BIG`, `Υ₁ = U`, `κ`). The first call is run with the smallness
  `ω_{m̃}² ≤ (8Υ₁)⁻¹`, so that `Θ_{L,n} - 1 ≤ 1/8 + 1/8`.
* `homogBelow_maxOne_rpow_le`: `(max 1 t)^{-6000} ≤ 2^{6000} m^{-3000}` once `m ≤ 2t`.
* `homogBelow_finalShape`: the item-6 rewrites into the printed shape, indicator included.
* `homogBelow_L_ge_of_lNaught` and `homogBelow_largeM_headroom`: threshold arithmetic. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

/-- **The double application of [AK, Theorem 6.1]**, abstracted. -/
theorem homogBelow_twoCalls_core
    (Θ ω : ℕ → ℝ) (BIG : ℕ → ℕ → ℝ) (U C61 κ : ℝ) (m2 m3 : ℕ) (hU : 0 < U)
    (hStep : ∀ m m0 : ℕ, max m2 m3 ≤ m → ω m ^ 2 ≤ U⁻¹ → BIG m m0 ≤ (m0 : ℝ) →
      ∀ n : ℕ, m + 4 * m0 ≤ n →
        Θ n - 1 ≤ U * ω m ^ 2 +
          C61 * (3 : ℝ) ^ (-(κ * ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ)))))
    (mt mt' m0 : ℕ)
    (hmt : max m2 m3 ≤ mt) (hmt' : max m2 m3 ≤ mt')
    (hSmall : ω mt ^ 2 ≤ (8 * U)⁻¹) (hSmall' : ω mt' ^ 2 ≤ U⁻¹)
    (hBig : BIG mt m0 ≤ (m0 : ℝ)) (hBig' : BIG mt' m0 ≤ (m0 : ℝ))
    (hE : C61 * (3 : ℝ) ^ (-(κ * (m0 : ℝ))) ≤ 1 / 8)
    (W : ℝ) (hSharp : Θ (mt + 5 * m0) - 1 ≤ 1 / 4 → ω mt' ^ 2 ≤ W) :
    Θ (mt' + 5 * m0) - 1 ≤ U * W + C61 * (3 : ℝ) ^ (-(κ * (m0 : ℝ))) := by
  have hgap : ∀ k : ℕ, (((k + 5 * m0 : ℕ) : ℝ) - (k : ℝ) - 4 * (m0 : ℝ)) = (m0 : ℝ) := by
    intro k; push_cast; ring
  have h8U : (8 * U)⁻¹ ≤ U⁻¹ := inv_anti₀ hU (by linarith only [hU])
  have hfirst := hStep mt m0 hmt (le_trans hSmall h8U) hBig (mt + 5 * m0) (by omega)
  rw [hgap] at hfirst
  have hUω : U * ω mt ^ 2 ≤ 1 / 8 := by
    have h := mul_le_mul_of_nonneg_left hSmall hU.le
    have he : U * (8 * U)⁻¹ = 1 / 8 := by field_simp
    linarith only [h, he]
  have hquarter : Θ (mt + 5 * m0) - 1 ≤ 1 / 4 := by linarith only [hfirst, hUω, hE]
  have hW := hSharp hquarter
  have hsecond := hStep mt' m0 hmt' hSmall' hBig' (mt' + 5 * m0) (by omega)
  rw [hgap] at hsecond
  have hUW : U * ω mt' ^ 2 ≤ U * W := mul_le_mul_of_nonneg_left hW hU.le
  linarith only [hsecond, hUW]

/-- `(max 1 t)^{-6000} ≤ 2^{6000} m^{-3000}` once `1 ≤ m ≤ 2t`. -/
theorem homogBelow_maxOne_rpow_le {t m : ℝ} (hm1 : 1 ≤ m) (hmt : m ≤ 2 * t) :
    (max 1 t) ^ (-(6000 : ℝ)) ≤ (2 : ℝ) ^ (6000 : ℝ) * m ^ (-(3000 : ℝ)) := by
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm1
  have hhalf : 0 < m / 2 := by positivity
  have hle : m / 2 ≤ max 1 t := le_trans (by linarith only [hmt]) (le_max_right _ _)
  have h1 : (max 1 t) ^ (-(6000 : ℝ)) ≤ (m / 2) ^ (-(6000 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hhalf hle (by norm_num)
  have h2 : (m / 2) ^ (-(6000 : ℝ)) = (2 : ℝ) ^ (6000 : ℝ) * m ^ (-(6000 : ℝ)) := by
    rw [Real.div_rpow hm0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [div_inv_eq_mul, mul_comm]
  have h3 : m ^ (-(6000 : ℝ)) ≤ m ^ (-(3000 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ (6000 : ℝ) := by positivity
  rw [h2] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_left h3 h2pos)

/-- **The final rewrites** (item 6): from `θ ≤ U·(A X σ⁻² + B (max 1 t)^{-6000}) + E` to the
printed shape of `e.Theta.Lm.final.bound`, indicator included. -/
theorem homogBelow_finalShape
    {θ U A B X s t E C Lr mr lg : ℝ}
    (hU : 0 ≤ U) (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 < s)
    (hθ : θ ≤ U * (A * X * s ^ (-(2 : ℝ)) + B * (max 1 t) ^ (-(6000 : ℝ))) + E)
    (hXY : X ≤ max 0 (Lr - mr + C * lg))
    (hm1 : 1 ≤ mr) (hmt : mr ≤ 2 * t)
    (hE : E ≤ mr ^ (-(3000 : ℝ)))
    (hC1 : U * A ≤ C) (hC2 : U * B * (2 : ℝ) ^ (6000 : ℝ) + 1 ≤ C) :
    θ ≤ C * s ^ (-(2 : ℝ)) * max 0 (Lr - mr + C * lg) *
          (if mr ≤ Lr + C * lg then (1 : ℝ) else 0) +
        C * mr ^ (-(3000 : ℝ)) := by
  have hind : max 0 (Lr - mr + C * lg) * (if mr ≤ Lr + C * lg then (1 : ℝ) else 0) =
      max 0 (Lr - mr + C * lg) := by
    split_ifs with h
    · exact mul_one _
    · have hneg : Lr - mr + C * lg ≤ 0 := by
        have h' := lt_of_not_ge h
        linarith only [h']
      rw [max_eq_left hneg, zero_mul]
  have hs2 : 0 ≤ s ^ (-(2 : ℝ)) := Real.rpow_nonneg hs.le _
  have hmp : 0 ≤ mr ^ (-(3000 : ℝ)) := Real.rpow_nonneg (by linarith only [hm1]) _
  have hpow := homogBelow_maxOne_rpow_le hm1 hmt
  have hT1 : U * (A * X * s ^ (-(2 : ℝ))) ≤ C * s ^ (-(2 : ℝ)) * max 0 (Lr - mr + C * lg) := by
    have hY0 : 0 ≤ max 0 (Lr - mr + C * lg) := le_max_left _ _
    have hUA : 0 ≤ U * A := mul_nonneg hU hA
    have h1 : U * A * X ≤ U * A * max 0 (Lr - mr + C * lg) :=
      mul_le_mul_of_nonneg_left hXY hUA
    have h2 : U * A * max 0 (Lr - mr + C * lg) ≤ C * max 0 (Lr - mr + C * lg) :=
      mul_le_mul_of_nonneg_right hC1 hY0
    have h3 := mul_le_mul_of_nonneg_right (le_trans h1 h2) hs2
    calc U * (A * X * s ^ (-(2 : ℝ))) = U * A * X * s ^ (-(2 : ℝ)) := by ring
      _ ≤ C * max 0 (Lr - mr + C * lg) * s ^ (-(2 : ℝ)) := h3
      _ = C * s ^ (-(2 : ℝ)) * max 0 (Lr - mr + C * lg) := by ring
  have hT2 : U * (B * (max 1 t) ^ (-(6000 : ℝ))) ≤
      U * B * (2 : ℝ) ^ (6000 : ℝ) * mr ^ (-(3000 : ℝ)) := by
    have hUB : 0 ≤ U * B := mul_nonneg hU hB
    have h := mul_le_mul_of_nonneg_left hpow hUB
    calc U * (B * (max 1 t) ^ (-(6000 : ℝ))) = U * B * (max 1 t) ^ (-(6000 : ℝ)) := by ring
      _ ≤ U * B * ((2 : ℝ) ^ (6000 : ℝ) * mr ^ (-(3000 : ℝ))) := h
      _ = U * B * (2 : ℝ) ^ (6000 : ℝ) * mr ^ (-(3000 : ℝ)) := by ring
  have hT3 : (U * B * (2 : ℝ) ^ (6000 : ℝ) + 1) * mr ^ (-(3000 : ℝ)) ≤
      C * mr ^ (-(3000 : ℝ)) := mul_le_mul_of_nonneg_right hC2 hmp
  have hind' : C * s ^ (-(2 : ℝ)) * max 0 (Lr - mr + C * lg) *
      (if mr ≤ Lr + C * lg then (1 : ℝ) else 0) = C * s ^ (-(2 : ℝ)) * max 0 (Lr - mr + C * lg) := by
    rw [mul_assoc, hind]
  rw [hind']
  have hsplit : U * (A * X * s ^ (-(2 : ℝ)) + B * (max 1 t) ^ (-(6000 : ℝ))) =
      U * (A * X * s ^ (-(2 : ℝ))) + U * (B * (max 1 t) ^ (-(6000 : ℝ))) := by ring
  rw [hsplit] at hθ
  have hexp : (U * B * (2 : ℝ) ^ (6000 : ℝ) + 1) * mr ^ (-(3000 : ℝ)) =
      U * B * (2 : ℝ) ^ (6000 : ℝ) * mr ^ (-(3000 : ℝ)) + mr ^ (-(3000 : ℝ)) := by ring
  linarith only [hθ, hT1, hT2, hT3, hE, hexp]

/-- `L ≥ N` from `L ≥ L₀(C, C M, …)` once `C` is past a threshold depending on `N`. -/
theorem homogBelow_L_ge_of_lNaught (N : ℝ) :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ C : ℝ, C1 ≤ C →
      ∀ M alpha cStar nu K : ℝ, 1 ≤ M → 0 ≤ alpha → alpha < 1 →
        0 < cStar → cStar ≤ 2 → 0 < nu → nu ≤ 1 → 0 ≤ K →
      ∀ L : ℕ,
        SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) →
        N ≤ (L : ℝ) := by
  obtain ⟨Clin, hClin1, hlin⟩ := homogBelow_lNaught_ge_linear
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hq : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) / 4 := by positivity
  refine ⟨max Clin (N / ((Real.log 2) ^ (12 : ℝ) / 4)), le_trans hClin1 (le_max_left _ _), ?_⟩
  intro C hC M alpha cStar nu K hM halpha0 halpha1 hcStar hcStar2 hnu hnu1 hK L hL
  have hC1 : (1 : ℝ) ≤ C := le_trans hClin1 (le_trans (le_max_left _ _) hC)
  have hCM : (1 : ℝ) ≤ C * M := by nlinarith only [hC1, hM]
  have hlinC := hlin C (le_trans (le_max_left _ _) hC) (C * M) hCM alpha halpha0 halpha1
    cStar hcStar hcStar2 nu hnu hnu1 K hK
  have hN : N ≤ (Real.log 2) ^ (12 : ℝ) / 4 * C := by
    have h := le_trans (le_max_right _ _) hC
    rw [div_le_iff₀ hq] at h
    linarith only [h]
  linarith only [hN, hlinC, hL]

/-- **Headroom in the `L² ≤ m` branch**: with `m₀ := ⌈C_b log² m⌉₊`,
`L + 10 m₀ + ⌈C_mix log L⌉₊ + 1 ≤ m` once `C` is past a threshold. -/
theorem homogBelow_largeM_headroom (Cb : ℝ) (hCb : 0 ≤ Cb) (Cmix : ℝ) (hCmix : 1 ≤ Cmix) :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ C : ℝ, C1 ≤ C →
      ∀ M alpha cStar nu K : ℝ, 1 ≤ M → 0 ≤ alpha → alpha < 1 →
        0 < cStar → cStar ≤ 2 → 0 < nu → nu ≤ 1 → 0 ≤ K →
      ∀ L m : ℕ,
        SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) →
        L ^ 2 ≤ m →
        L + 10 * ⌈Cb * Real.log (m : ℝ) ^ 2⌉₊ + ⌈Cmix * Real.log (L : ℝ)⌉₊ + 1 ≤ m := by
  obtain ⟨C1, hC1, hLN⟩ := homogBelow_L_ge_of_lNaught (160 * Cb + Cmix + 13)
  refine ⟨C1, hC1, ?_⟩
  intro C hC M alpha cStar nu K hM halpha0 halpha1 hcStar hcStar2 hnu hnu1 hK L m hL hLm
  have hLK := hLN C hC M alpha cStar nu K hM halpha0 halpha1 hcStar hcStar2 hnu hnu1 hK L hL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by linarith only [hLK, hCb, hCmix]
  have hLmR : (L : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast hLm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by nlinarith only [hL1, hLmR]
  set z : ℝ := Real.sqrt (m : ℝ) with hz
  set w : ℝ := Real.sqrt z with hw
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hzsq : z ^ 2 = (m : ℝ) := Real.sq_sqrt (by linarith only [hm1])
  have hwsq : w ^ 2 = z := Real.sq_sqrt hz0
  have hLz : (L : ℝ) ≤ z := (Real.le_sqrt (by linarith only [hL1]) (by linarith only [hm1])).2 hLmR
  have hw0 : 0 < w := by
    rw [hw]; apply Real.sqrt_pos.2; linarith only [hLz, hL1]
  have hlogm : Real.log (m : ℝ) = 4 * Real.log w := by
    have hm4 : (m : ℝ) = w ^ 4 := by
      rw [← hzsq, ← hwsq]; ring
    rw [hm4, Real.log_pow]; norm_num
  have hlogw : Real.log w ≤ w := by
    have h := Real.log_le_sub_one_of_pos hw0
    linarith only [h]
  have hlogw0 : 0 ≤ Real.log w := by
    have hmlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
    linarith only [hmlog, hlogm]
  have hlogm2 : Real.log (m : ℝ) ^ 2 ≤ 16 * z := by
    rw [hlogm, ← hwsq]
    have h := mul_le_mul hlogw hlogw hlogw0 hw0.le
    nlinarith only [h]
  have hlogL : Real.log (L : ℝ) ≤ (L : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by linarith only [hL1] : (0 : ℝ) < (L : ℝ))
    linarith only [h]
  have hlogL0 : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
  have hA0 : 0 ≤ Cb * Real.log (m : ℝ) ^ 2 := by positivity
  have hB0 : 0 ≤ Cmix * Real.log (L : ℝ) := by positivity
  have hceilA := Nat.ceil_lt_add_one hA0
  have hceilB := Nat.ceil_lt_add_one hB0
  have hAle : Cb * Real.log (m : ℝ) ^ 2 ≤ Cb * (16 * z) := mul_le_mul_of_nonneg_left hlogm2 hCb
  have hBle : Cmix * Real.log (L : ℝ) ≤ Cmix * z :=
    mul_le_mul_of_nonneg_left (le_trans hlogL hLz) (by linarith only [hCmix])
  have hzK : 160 * Cb + Cmix + 13 ≤ z := le_trans hLK hLz
  have hz1 : 1 ≤ z := by linarith only [hzK, hCb, hCmix]
  have hzz : (160 * Cb + Cmix + 13) * z ≤ z * z := mul_le_mul_of_nonneg_right hzK hz0
  have hreal : ((L + 10 * ⌈Cb * Real.log (m : ℝ) ^ 2⌉₊ + ⌈Cmix * Real.log (L : ℝ)⌉₊ + 1 : ℕ) :
      ℝ) < (m : ℝ) := by
    push_cast
    have hlt : (L : ℝ) + 10 * (⌈Cb * Real.log (m : ℝ) ^ 2⌉₊ : ℝ) +
        (⌈Cmix * Real.log (L : ℝ)⌉₊ : ℝ) + 1 < z ^ 2 := by
      nlinarith only [hceilA, hceilB, hAle, hBle, hLz, hzz, hz1]
    exact lt_of_lt_of_eq hlt hzsq
  exact_mod_cast hreal.le

/-- `N^{-p} ≤ 1/8` once `N ≥ 3` and `p ≥ 2`. -/
theorem homogBelow_rpow_neg_le_eighth {N p : ℝ} (hN : 3 ≤ N) (hp : 2 ≤ p) :
    N ^ (-p) ≤ 1 / 8 := by
  have hN1 : 1 ≤ N := by linarith only [hN]
  have h1 : N ^ (-p) ≤ N ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hp])
  have h2 : N ^ (-(2 : ℝ)) = (N ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by linarith only [hN]), Real.rpow_two]
  have h3 : (N ^ 2)⁻¹ ≤ (8 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by nlinarith only [hN])
  rw [h2] at h1
  rw [one_div]
  exact le_trans h1 h3

/-- `L^{-6000} ≤ m^{-3000}` once `0 < m ≤ L²`. -/
theorem homogBelow_rpow_sq_le {L m : ℝ} (hL : 0 ≤ L) (hm : 0 < m) (hmL : m ≤ L ^ 2) :
    L ^ (-(6000 : ℝ)) ≤ m ^ (-(3000 : ℝ)) := by
  have heq : L ^ (-(6000 : ℝ)) = (L ^ 2) ^ (-(3000 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hL]; norm_num
  rw [heq]
  exact Real.rpow_le_rpow_of_nonpos hm hmL (by norm_num)

/-- `(L - m̃')_+ ≤ max 0 (L - m + Z)` when `m = m̃' + k` and `k ≤ Z`. -/
theorem homogBelow_natSub_le_max {L m mt' k : ℕ} {Z : ℝ} (he : m = mt' + k) (hk : (k : ℝ) ≤ Z) :
    ((L - mt' : ℕ) : ℝ) ≤ max 0 ((L : ℝ) - (m : ℝ) + Z) := by
  rcases le_total L mt' with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]; exact le_max_left _ _
  · rw [Nat.cast_sub h]
    have hmR : (m : ℝ) = (mt' : ℝ) + (k : ℝ) := by rw [he]; push_cast; ring
    exact le_trans (by linarith only [hmR, hk]) (le_max_right _ _)

/-- `5 ⌈C_b log² L⌉₊ ≤ C log² L` once `L ≥ 3` and `5 C_b + 5 ≤ C`. -/
theorem homogBelow_five_m0_le {Cb C L : ℝ} (hCb : 0 ≤ Cb) (hL : 3 ≤ L) (hC : 5 * Cb + 5 ≤ C) :
    5 * (⌈Cb * Real.log L ^ 2⌉₊ : ℝ) ≤ C * Real.log L ^ (2 : ℝ) := by
  have hlog1 : 1 ≤ Real.log L := by
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hh := Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le he3 hL)
    rw [Real.log_exp] at hh
    exact hh.le
  have hsq1 : 1 ≤ Real.log L ^ 2 := by nlinarith only [hlog1]
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ Cb * Real.log L ^ 2 by positivity)
  rw [Real.rpow_two]
  have hC' : (5 * Cb + 5) * Real.log L ^ 2 ≤ C * Real.log L ^ 2 :=
    mul_le_mul_of_nonneg_right hC (by positivity)
  nlinarith only [hceil, hC', hsq1]

/-- Satisfiability of `homogBelow_twoCalls_core`'s hypotheses: `Θ ≡ 1`, `ω ≡ 0`, `BIG ≡ 0`,
`U = 1`, `C₆₁ = 0`. -/
example : (fun _ : ℕ => (1 : ℝ)) (0 + 5 * 0) - 1 ≤ 1 * 0 + 0 * (3 : ℝ) ^ (-(1 * ((0 : ℕ) : ℝ))) :=
  homogBelow_twoCalls_core (fun _ => 1) (fun _ => 0) (fun _ _ => 0) 1 0 1 0 0 one_pos
    (fun _ _ _ _ _ _ _ => by norm_num) 0 0 0 le_rfl le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) 0 (fun _ => by norm_num)

/-- Satisfiability of `homogBelow_finalShape`'s hypotheses. -/
example : (0 : ℝ) ≤ 1 * (1 : ℝ) ^ (-(2 : ℝ)) * max 0 ((1 : ℝ) - 1 + 1 * 0) *
      (if (1 : ℝ) ≤ 1 + 1 * 0 then (1 : ℝ) else 0) + 1 * (1 : ℝ) ^ (-(3000 : ℝ)) :=
  homogBelow_finalShape (θ := 0) (U := 0) (A := 0) (B := 0) (X := 0) (s := 1) (t := 1) (E := 0)
    (C := 1) (Lr := 1) (mr := 1) (lg := 0) le_rfl le_rfl le_rfl one_pos (by norm_num)
    (le_max_left _ _) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Satisfiability of `homogBelow_largeM_headroom` at `α = 0`, `M = 1`, `K = 0`, `c⋆ = 2`,
`ν = 1`: some `L` clears `L₀`, and `m = L²` meets `L² ≤ m`, so the conclusion is reached. -/
example : ∃ L m : ℕ, L + 10 * ⌈(1 : ℝ) * Real.log (m : ℝ) ^ 2⌉₊ +
    ⌈(1 : ℝ) * Real.log (L : ℝ)⌉₊ + 1 ≤ m := by
  obtain ⟨C1, _hC1, h⟩ := homogBelow_largeM_headroom 1 zero_le_one 1 le_rfl
  obtain ⟨L, hL⟩ := exists_nat_ge
    (SuperdiffusionCLT.Frozen.Section4.lNaught C1 (C1 * 1) 0 2 1 0)
  exact ⟨L, L ^ 2, h C1 le_rfl 1 0 2 1 0 le_rfl le_rfl one_pos two_pos le_rfl one_pos le_rfl
    le_rfl L (L ^ 2) hL le_rfl⟩

end SuperdiffusionCLT.Section4.HomogBelow
