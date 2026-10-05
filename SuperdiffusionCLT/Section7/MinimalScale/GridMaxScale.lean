/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxUnion

/-!
# One random scale controlling every grid maximum

**`exists_gridMax_scale`.** Suppose every translate `X0 y` has `log X0 y = O_{Γ_σ}(A)` with
`A ≥ 1`.  Then there is a single measurable scale `Xs`, not depending on `K`, with
`log Xs = O_{Γ_σ}(C A (1 + log A)^{1/σ})`, such that almost surely, for every `K` at least that
scale, `Xs ≤ 3^{n_K}` forces the maximum of `X0` over the grid `3^{n_K-3}ℤ^d ∩ {‖y‖_∞ ≤ 3^{K+2}}`
to be at most `3^{n_K}`.  Here `n_K = K - ⌈N log K⌉₊` and `C` depends only on `d, N, σ`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization
open scoped ENNReal

noncomputable section

theorem one_lt_log_three : 1 < Real.log 3 :=
  (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three

theorem log_three_le_two : Real.log 3 ≤ 2 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
  linarith only [this]


/-- The prefactor is polynomial in `A`. -/
theorem prefactor_le {A b Bc : ℝ} (hA : 1 ≤ A) (hb : 0 ≤ b) (hBc : 0 < Bc) :
    2 * (Bc * (Real.log 3 / (2 * A)) ^ (-(b + 2))) ≤
      Real.exp (Real.log (2 * Bc * 2 ^ (b + 2)) + (b + 2) * Real.log A) := by
  have hA0 : 0 < A := by linarith only [hA]
  have hl := one_lt_log_three
  have hq : (Real.log 3 / (2 * A)) ^ (-(b + 2)) = (2 * A / Real.log 3) ^ (b + 2) := by
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
    congr 1; rw [inv_div]
  have hle : (2 * A / Real.log 3) ^ (b + 2) ≤ (2 * A) ^ (b + 2) :=
    Real.rpow_le_rpow (by positivity) (div_le_self (by positivity) hl.le) (by linarith only [hb])
  have hexp : Real.exp (Real.log (2 * Bc * 2 ^ (b + 2)) + (b + 2) * Real.log A) =
      2 * Bc * 2 ^ (b + 2) * A ^ (b + 2) := by
    rw [Real.exp_add, Real.exp_log (by positivity), mul_comm (b + 2), Real.rpow_def_of_pos hA0]
  rw [hexp, hq]
  calc 2 * (Bc * (2 * A / Real.log 3) ^ (b + 2)) ≤ 2 * (Bc * (2 * A) ^ (b + 2)) := by gcongr
    _ = 2 * Bc * 2 ^ (b + 2) * A ^ (b + 2) := by
        rw [Real.mul_rpow (by norm_num) hA0.le]; ring

/-- The final real-variable inequality of the tail estimate. -/
theorem final_tail_real {σ A t L C W Λ b a ap kk mm : ℝ} (hσ : 0 < σ) (hA : 1 ≤ A) (ht : 1 ≤ t)
    (hL4 : 4 ≤ L) (hC0 : 0 ≤ C) (hLdef : L * t / (4 * A) = (C / 4) * (1 + Real.log A) ^ σ⁻¹ * t)
    (hadef : a = Real.log 3 / (2 * A)) (hkl : L * t / Real.log 3 - 1 ≤ kk) (hkm : kk ≤ mm)
    (hCW : 2 * W ≤ (C / 4) ^ σ) (hW : W = 1 + Λ + (b + 2)) (hΛ0 : 0 ≤ Λ) (hb : 0 ≤ b)
    (hap : ap ≤ Real.exp (Λ + (b + 2) * Real.log A)) :
    ap * Real.exp (-((a * mm) ^ σ / 2)) ≤ Real.exp (-(t ^ σ)) := by
  have hA0 : 0 < A := by linarith only [hA]
  have hl1 := one_lt_log_three
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have ha : 0 < a := by rw [hadef]; positivity
  have hLt4 : 4 ≤ L * t := by nlinarith only [hL4, ht]
  have hakey : a * (L * t / Real.log 3) = L * t / (2 * A) := by
    rw [hadef]; field_simp
  have hale : a ≤ 1 / A := by
    rw [hadef, div_le_div_iff₀ (by positivity) hA0]
    nlinarith only [log_three_le_two, hA0]
  have hLt4A : 1 / A ≤ L * t / (4 * A) := by
    rw [div_le_div_iff₀ hA0 (by positivity)]
    nlinarith only [hLt4, hA0]
  have hak : L * t / (4 * A) ≤ a * mm := by
    have h1 : a * (L * t / Real.log 3 - 1) ≤ a * kk := mul_le_mul_of_nonneg_left hkl ha.le
    have h2 : a * kk ≤ a * mm := mul_le_mul_of_nonneg_left hkm ha.le
    have h3 : L * t / (2 * A) = L * t / (4 * A) + L * t / (4 * A) := by ring
    have h4 : a * (L * t / Real.log 3 - 1) = L * t / (2 * A) - a := by
      rw [mul_sub, hakey]; ring
    linarith only [h1, h2, h3, h4, hale, hLt4A]
  have hpow : (L * t / (4 * A)) ^ σ = (C / 4) ^ σ * (1 + Real.log A) * t ^ σ := by
    rw [hLdef]
    have hC : 0 ≤ C / 4 := by linarith only [hC0]
    rw [Real.mul_rpow (by positivity) (by linarith only [ht]), Real.mul_rpow hC (by positivity),
      Real.rpow_inv_rpow (by linarith only [hlogA]) hσ.ne']
  have hs1 : 1 ≤ t ^ σ := Real.one_le_rpow ht hσ.le
  have hE : W * (1 + Real.log A) * t ^ σ ≤ (a * mm) ^ σ / 2 := by
    have h1 : (L * t / (4 * A)) ^ σ ≤ (a * mm) ^ σ := Real.rpow_le_rpow (by positivity) hak hσ.le
    rw [hpow] at h1
    have h2 : 2 * W * (1 + Real.log A) * t ^ σ ≤ (C / 4) ^ σ * (1 + Real.log A) * t ^ σ := by
      gcongr
    linarith only [h1, h2]
  have hnum : Λ + (b + 2) * Real.log A + t ^ σ ≤ W * (1 + Real.log A) * t ^ σ := by
    have hu : 0 ≤ Λ + (b + 2) := by linarith only [hΛ0, hb]
    have h1 : Λ + (b + 2) * Real.log A ≤ (Λ + (b + 2)) * (1 + Real.log A) := by nlinarith only [mul_nonneg hΛ0 hlogA, hb]
    have h2 : (Λ + (b + 2)) * (1 + Real.log A) ≤ (Λ + (b + 2)) * (1 + Real.log A) * t ^ σ := by
      have : 0 ≤ (Λ + (b + 2)) * (1 + Real.log A) := by positivity
      nlinarith only [mul_le_mul_of_nonneg_left hs1 this]
    have h3 : W * (1 + Real.log A) * t ^ σ = (Λ + (b + 2)) * (1 + Real.log A) * t ^ σ +
        (1 + Real.log A) * t ^ σ := by rw [hW]; ring
    have h4 : t ^ σ ≤ (1 + Real.log A) * t ^ σ := by nlinarith only [hlogA, hs1]
    linarith only [h1, h2, h3, h4]
  calc ap * Real.exp (-((a * mm) ^ σ / 2))
      ≤ Real.exp (Λ + (b + 2) * Real.log A) * Real.exp (-((a * mm) ^ σ / 2)) :=
        mul_le_mul_of_nonneg_right hap (Real.exp_pos _).le
    _ = Real.exp (Λ + (b + 2) * Real.log A - (a * mm) ^ σ / 2) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(t ^ σ)) := Real.exp_le_exp.2 (by linarith only [hnum, hE])

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The tail of the random scale. -/
theorem measureReal_scaleBadSup_gt_le (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℝ}
    (hN : 0 ≤ N) {σ A : ℝ} (hσ : 0 < σ) {X0 : Vec d → Ω → ℝ} (hX0 : ∀ y, Measurable (X0 y))
    (hA : 1 ≤ A)
    (hO : ∀ y, Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma σ) (fun ω => Real.log (X0 y ω)) A)
    {C₂ : ℝ} (hC₂ : 0 ≤ C₂)
    (hterm : ∀ (a : ℝ), 0 < a → ∀ K : ℕ, 1 ≤ K →
      (K : ℝ) ^ ((d : ℝ) * (N * Real.log 3)) * Real.exp (-((a * K) ^ σ)) ≤
        C₂ * a ^ (-((d : ℝ) * (N * Real.log 3) + 2)) * ((K : ℝ) ^ 2)⁻¹ *
          Real.exp (-((a * K) ^ σ / 2)))
    {K0 : ℕ} (h1 : 1 ≤ K0) (h2 : (4 * N + 2) ^ 2 ≤ (K0 : ℝ)) (h3 : 2 * A ≤ K0) (k : ℕ) :
    μ.real {ω | (3 : ℝ≥0∞) ^ k < scaleBadSup d N K0 X0 ω} ≤
      2 * ((1500 : ℝ) ^ d * C₂ * (Real.log 3 / (2 * A)) ^ (-((d : ℝ) * (N * Real.log 3) + 2))) *
        Real.exp (-((Real.log 3 / (2 * A) * (max K0 k : ℕ)) ^ σ / 2)) := by
  have hmax : (K0 : ℝ) ≤ (max K0 k : ℕ) := by exact_mod_cast le_max_left K0 k
  have := measureReal_badFrom_le μ hN hσ hX0 hA hO hC₂ hterm (max K0 k)
    (h1.trans (le_max_left _ _)) (h2.trans hmax) (h3.trans hmax)
  exact (measureReal_mono scaleBadSup_gt_subset (measure_ne_top _ _)).trans this

universe u

/-- **One scale for every grid maximum.** -/
theorem exists_gridMax_scale (d : ℕ) {N σ : ℝ} (hN : 0 ≤ N) (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X0 : Vec d → Ω → ℝ), (∀ y, Measurable (X0 y)) →
        ∀ A : ℝ, 1 ≤ A →
        (∀ y, Homogenization.IndependentSums.IsBigO μ
          (Homogenization.IndependentSums.gammaSigma σ) (fun ω => Real.log (X0 y ω)) A) →
        ∃ Xs : Ω → ℝ, Measurable Xs ∧
          Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma σ)
            (fun ω => Real.log (Xs ω)) (C * A * (1 + Real.log A) ^ σ⁻¹) ∧
          ∀ᵐ ω ∂μ, ∀ K : ℕ, C * A * (1 + Real.log A) ^ σ⁻¹ ≤ (K : ℝ) →
            Xs ω ≤ (3 : ℝ) ^ (nK N K) →
            X0max (fun y => X0 y ω) ((nK N K : ℤ) - 3) ((3 : ℝ) ^ (K + 2)) ≤ (3 : ℝ) ^ (nK N K) := by
  set b : ℝ := (d : ℝ) * (N * Real.log 3) with hbdef
  have hl1 := one_lt_log_three
  have hb : 0 ≤ b := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hN (by linarith only [hl1]))
  obtain ⟨C₂, hC₂, hterm⟩ := poly_mul_exp_le hσ b hb
  set Bc : ℝ := (1500 : ℝ) ^ d * C₂ with hBc
  have hBc1 : 1 ≤ Bc := by
    have : (1 : ℝ) ≤ 1500 ^ d := one_le_pow₀ (by norm_num)
    nlinarith only [this, hC₂, hBc]
  set Λ : ℝ := Real.log (2 * Bc * 2 ^ (b + 2)) with hΛ
  have hΛ0 : 0 ≤ Λ := by
    refine Real.log_nonneg ?_
    have : (1 : ℝ) ≤ 2 ^ (b + 2) := Real.one_le_rpow (by norm_num) (by linarith only [hb])
    nlinarith only [this, hBc1]
  set W : ℝ := 1 + Λ + (b + 2) with hW
  have hW1 : 1 ≤ W := by linarith only [hW, hΛ0, hb]
  refine ⟨4 + (4 * N + 2) ^ 2 + 4 * (2 * W) ^ σ⁻¹, ?_, ?_⟩
  · have : 0 ≤ (2 * W) ^ σ⁻¹ := Real.rpow_nonneg (by linarith only [hW1]) _
    linarith only [this, sq_nonneg (4 * N + 2)]
  intro Ω _ μ _ X0 hX0 A hA hO
  set C : ℝ := 4 + (4 * N + 2) ^ 2 + 4 * (2 * W) ^ σ⁻¹ with hC
  have hA0 : 0 < A := by linarith only [hA]
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hP : 1 ≤ (1 + Real.log A) ^ σ⁻¹ :=
    Real.one_le_rpow (by linarith only [hlogA]) (inv_nonneg.2 hσ.le)
  have hWpow : 0 ≤ (2 * W) ^ σ⁻¹ := Real.rpow_nonneg (by linarith only [hW1]) _
  have hC4 : 4 ≤ C := by nlinarith only [sq_nonneg (4 * N + 2), hWpow, hC]
  set L : ℝ := C * A * (1 + Real.log A) ^ σ⁻¹ with hL
  have hCA : C ≤ C * A := by nlinarith only [hC4, hA]
  have hCAL : C * A ≤ L := by
    rw [hL]; nlinarith only [hP, mul_nonneg (by linarith only [hC4] : (0:ℝ) ≤ C) hA0.le]
  have hL4 : 4 ≤ L := by linarith only [hC4, hCA, hCAL]
  have hL2A : 2 * A ≤ L := by nlinarith only [hC4, hA0, hCAL]
  have hLN : (4 * N + 2) ^ 2 ≤ L := by linarith only [hC, hWpow, hCA, hCAL]
  set K0 : ℕ := ⌈L⌉₊ with hK0
  have hLK0 : L ≤ (K0 : ℝ) := Nat.le_ceil L
  have hK01 : 1 ≤ K0 := by
    have : (0 : ℝ) < K0 := by linarith only [hLK0, hL4]
    exact_mod_cast this
  have hY := measurable_scaleBadSup N K0 hX0
  set a : ℝ := Real.log 3 / (2 * A) with hadef
  have ha : 0 < a := by positivity
  set ap : ℝ := 2 * (Bc * a ^ (-(b + 2))) with hap
  have hap0 : 0 ≤ ap := by positivity
  have hT : ∀ k : ℕ, μ.real {ω | (3 : ℝ≥0∞) ^ k < scaleBadSup d N K0 X0 ω} ≤
      ap * Real.exp (-((a * (max K0 k : ℕ)) ^ σ / 2)) := fun k =>
    measureReal_scaleBadSup_gt_le μ hN hσ hX0 hA hO (by linarith only [hC₂]) hterm hK01
      (hLN.trans hLK0) (hL2A.trans hLK0) k
  -- almost sure finiteness
  have hfin : ∀ᵐ ω ∂μ, scaleBadSup d N K0 X0 ω ≠ ⊤ := by
    have hz : μ.real {ω | scaleBadSup d N K0 X0 ω = ⊤} ≤ 0 := by
      refine ge_of_tendsto' (b := μ.real {ω | scaleBadSup d N K0 X0 ω = ⊤})
        (f := fun k : ℕ => ap * Real.exp (-((a * k) ^ σ / 2))) (a := 0) (x := Filter.atTop) ?_ fun k => ?_
      · have h1 : Filter.Tendsto (fun k : ℕ => (a * k) ^ σ / 2) Filter.atTop Filter.atTop :=
          ((tendsto_rpow_atTop hσ).comp
            (tendsto_natCast_atTop_atTop.const_mul_atTop ha)).atTop_div_const two_pos
        have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul ap
        simpa using this
      · refine (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)).trans
          ((hT k).trans ?_)
        · exact lt_of_lt_of_eq (ENNReal.pow_lt_top (by norm_num)) hω.symm
        · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hap0
          have hkm : (k : ℝ) ≤ (max K0 k : ℕ) := by exact_mod_cast le_max_right K0 k
          have : (a * k) ^ σ ≤ (a * (max K0 k : ℕ)) ^ σ :=
            Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hkm ha.le) hσ.le
          linarith only [this]
    have h0 : μ.real {ω | scaleBadSup d N K0 X0 ω = ⊤} = 0 :=
      le_antisymm hz measureReal_nonneg
    have := (measureReal_eq_zero_iff).1 h0
    exact measure_eq_zero_iff_ae_notMem.1 this
  refine ⟨fun ω => max 1 (scaleBadSup d N K0 X0 ω).toReal,
    measurable_const.max (ENNReal.measurable_toReal.comp hY), ?_, ?_⟩
  · rw [Homogenization.IndependentSums.isBigO_gammaSigma_iff]
    intro t ht
    set k : ℕ := ⌊L * t / Real.log 3⌋₊ with hk
    have hlt0 : 0 ≤ L * t / Real.log 3 := by positivity
    have hsub : Homogenization.IndependentSums.absTailEvent
        (fun ω => Real.log (max 1 (scaleBadSup d N K0 X0 ω).toReal)) (L * t) ⊆
        {ω | (3 : ℝ≥0∞) ^ k < scaleBadSup d N K0 X0 ω} := by
      intro ω hω
      rw [Homogenization.IndependentSums.mem_absTailEvent] at hω
      have hpos : (0 : ℝ) < max 1 (scaleBadSup d N K0 X0 ω).toReal :=
        lt_of_lt_of_le one_pos (le_max_left _ _)
      have hlog0 : 0 ≤ Real.log (max 1 (scaleBadSup d N K0 X0 ω).toReal) :=
        Real.log_nonneg (le_max_left _ _)
      rw [abs_of_nonneg hlog0] at hω
      have hexp := (Real.lt_log_iff_exp_lt hpos).1 hω
      have h3k : (3 : ℝ) ^ k ≤ Real.exp (L * t) := by
        have hkl : (k : ℝ) * Real.log 3 ≤ L * t := by
          have := Nat.floor_le hlt0
          rw [le_div_iff₀ (by linarith only [hl1])] at this
          exact this
        calc (3 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 3) := by
              rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
          _ ≤ Real.exp (L * t) := Real.exp_le_exp.2 hkl
      have hlt := h3k.trans_lt hexp
      have h1k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
      rcases lt_max_iff.1 hlt with h | h
      · exact absurd h (not_lt.2 h1k)
      · have hne : scaleBadSup d N K0 X0 ω ≠ ⊤ := by
          intro htop
          rw [htop] at h
          simp at h
          linarith only [h, h1k]
        have := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hne).2 h
        rwa [ENNReal.ofReal_pow (by norm_num), show ENNReal.ofReal 3 = 3 by simp] at this
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans ((hT k).trans ?_)
    have hkl : L * t / Real.log 3 - 1 ≤ (k : ℝ) := by
      have := Nat.lt_floor_add_one (L * t / Real.log 3)
      linarith only [this]
    have hkm : (k : ℝ) ≤ (max K0 k : ℕ) := by exact_mod_cast le_max_right K0 k
    have hCW : 2 * W ≤ (C / 4) ^ σ := by
      have h1 : (2 * W) ^ σ⁻¹ ≤ C / 4 := by rw [hC]; linarith only [hWpow, sq_nonneg (4 * N + 2)]
      calc 2 * W = ((2 * W) ^ σ⁻¹) ^ σ := (Real.rpow_inv_rpow (by linarith only [hW1]) hσ.ne').symm
        _ ≤ (C / 4) ^ σ := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith only [hW1]) _) h1 hσ.le
    have hapexp : ap ≤ Real.exp (Λ + (b + 2) * Real.log A) :=
      prefactor_le (b := b) (Bc := Bc) hA hb (by linarith only [hBc1])
    exact final_tail_real hσ hA ht hL4 (by linarith only [hC4]) (by rw [hL]; field_simp) hadef hkl hkm hCW hW hΛ0 hb hapexp
  · filter_upwards [hfin] with ω hω K hK hXs
    have hKK0 : K0 ≤ K := Nat.ceil_le.2 (hL ▸ hK)
    by_contra hcon
    have hbad : ω ∈ badK d N X0 K := by
      by_contra hnb
      exact hcon (X0max_le_of_not_mem_badK hnb)
    have h1 := le_scaleBadSup hKK0 hbad
    have h2 : ((3 : ℝ≥0∞) ^ (nK N K + 1)).toReal ≤ (scaleBadSup d N K0 X0 ω).toReal :=
      ENNReal.toReal_mono hω h1
    have h3 : ((3 : ℝ≥0∞) ^ (nK N K + 1)).toReal = (3 : ℝ) ^ (nK N K + 1) := by
      rw [ENNReal.toReal_pow]; norm_num
    rw [h3] at h2
    have h4 : (3 : ℝ) ^ (nK N K + 1) ≤ max 1 (scaleBadSup d N K0 X0 ω).toReal :=
      h2.trans (le_max_right _ _)
    have h5 : (3 : ℝ) ^ (nK N K) < (3 : ℝ) ^ (nK N K + 1) :=
      pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self _)
    linarith only [h4, h5, hXs]

/-- Witness: the non-law hypotheses of `exists_gridMax_scale` are satisfiable (constant translates
`X0 y = 1` on a one-point probability space, `A = 1`). -/
example (d : ℕ) (σ : ℝ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X0 : Vec d → Ω → ℝ), (∀ y, Measurable (X0 y)) ∧
      ∀ y, Homogenization.IndependentSums.IsBigO μ
        (Homogenization.IndependentSums.gammaSigma σ) (fun ω => Real.log (X0 y ω)) 1 := by
  refine ⟨Unit, inferInstance, Measure.dirac (), inferInstance, fun _ _ => 1,
    fun _ => measurable_const, fun y => ?_⟩
  rw [Homogenization.IndependentSums.isBigO_gammaSigma_iff]
  intro t ht
  have : Homogenization.IndependentSums.absTailEvent (fun _ : Unit => Real.log ((fun _ _ => (1 : ℝ)) y ())) (1 * t) = ∅ := by
    ext ω
    simp only [Homogenization.IndependentSums.mem_absTailEvent, Real.log_one, abs_zero,
      Set.mem_empty_iff_false, iff_false, not_lt]
    linarith only [ht]
  rw [this]
  simpa using (Real.exp_pos (-t ^ σ)).le

end

end SuperdiffusionCLT.Section7
