/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.MinimalScale.RootScalesC
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Scalar inputs of the large-scale Hölder theorem

* `hr_scale_tail`: the tail of `C₀ 3^{m⋆}` of the minimal-scale argument, with the constant
  independent of the probability measure.
* `hr_small_delta`: `k^{-β} log k ≤ c` for large `k`.
* `hr_sigma_window`: `a/2 √m ≤ σ̄_m ≤ 3a/2 √m` from the sharp asymptotic of `σ̄_m`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory

/-- **Transfer of the tail of `f` to a scale `W` with `log W ≤ a f + b₀`.** -/
theorem hr_transfer (Ω : Type*) [MeasurableSpace Ω] {a A b0 B σ : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hb0 : 0 ≤ b0) (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (W f : Ω → ℝ),
      (∀ ω, Real.log (W ω) ≤ a * f ω + b0) →
      (∀ t : ℝ, 1 ≤ t → μ.real {ω | A * t < f ω} ≤ B * Real.exp (-(t ^ σ))) →
      ∀ t : ℝ, 1 ≤ t →
        μ.real {ω | t ≤ W ω} ≤ C * Real.exp (-(C⁻¹ * (Real.log t) ^ σ)) := by
  have haA : 0 < 4 * a * A := by positivity
  set T1 : ℝ := 4 * (b0 + a * A) with hT1
  have hT1pos : 0 < T1 := by positivity
  refine ⟨max (max 1 B) (max (Real.exp (T1 ^ σ)) ((4 * a * A) ^ σ)), le_trans (le_max_left _ _)
    (le_max_left _ _), fun μ _ W f hlog hT t ht => ?_⟩
  set C := max (max 1 B) (max (Real.exp (T1 ^ σ)) ((4 * a * A) ^ σ)) with hC
  have hC1 : 1 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCB : B ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCe : Real.exp (T1 ^ σ) ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCa : (4 * a * A) ^ σ ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC1
  have hu0 : 0 ≤ Real.log t := Real.log_nonneg ht
  by_cases hcase : Real.log t ≤ T1
  · have h1 : μ.real {ω | t ≤ W ω} ≤ 1 := measureReal_le_one
    have h2 : (Real.log t) ^ σ ≤ T1 ^ σ := Real.rpow_le_rpow hu0 hcase hσ.le
    have h3 : C⁻¹ * (Real.log t) ^ σ ≤ T1 ^ σ := by
      have hp : 0 ≤ (Real.log t) ^ σ := Real.rpow_nonneg hu0 σ
      have : C⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC1
      calc C⁻¹ * (Real.log t) ^ σ ≤ 1 * (Real.log t) ^ σ :=
            mul_le_mul_of_nonneg_right this hp
        _ ≤ T1 ^ σ := by linarith only [h2]
    have h4 : Real.exp (-(T1 ^ σ)) ≤ Real.exp (-(C⁻¹ * (Real.log t) ^ σ)) :=
      Real.exp_le_exp.2 (by linarith only [h3])
    have h5 : 1 ≤ C * Real.exp (-(T1 ^ σ)) := by
      have : Real.exp (T1 ^ σ) * Real.exp (-(T1 ^ σ)) = 1 := by
        rw [← Real.exp_add]; simp
      calc (1 : ℝ) = Real.exp (T1 ^ σ) * Real.exp (-(T1 ^ σ)) := this.symm
        _ ≤ C * Real.exp (-(T1 ^ σ)) :=
          mul_le_mul_of_nonneg_right hCe (Real.exp_pos _).le
    calc μ.real {ω | t ≤ W ω} ≤ 1 := h1
      _ ≤ C * Real.exp (-(T1 ^ σ)) := h5
      _ ≤ C * Real.exp (-(C⁻¹ * (Real.log t) ^ σ)) := mul_le_mul_of_nonneg_left h4 hC0.le
  · push Not at hcase
    set u := Real.log t with hu
    have hupos : 0 < u := lt_of_lt_of_le hT1pos hcase.le
    set s := u / (4 * a * A) with hs
    have hs1 : 1 ≤ s := by
      rw [hs, le_div_iff₀ haA]
      have : 4 * a * A ≤ T1 := by rw [hT1]; linarith only [hb0]
      linarith only [this, hcase]
    have hsub : {ω | t ≤ W ω} ⊆ {ω | A * s < f ω} := by
      intro ω hω
      have h1 : u ≤ Real.log (W ω) := Real.log_le_log (by linarith only [ht]) hω
      have h2 := hlog ω
      have h3 : 4 * b0 ≤ T1 := by rw [hT1]; nlinarith only [ha, hA]
      have hAs : A * s = u / (4 * a) := by
        rw [hs]; field_simp
      show A * s < f ω
      rw [hAs, div_lt_iff₀ (by positivity)]
      nlinarith only [h1, h2, h3, hcase, ha, hupos]
    have h6 := (measureReal_mono hsub).trans (hT s hs1)
    have h7 : s ^ σ = u ^ σ / (4 * a * A) ^ σ := by
      rw [hs]; exact Real.div_rpow hupos.le haA.le σ
    have hpw : 0 < (4 * a * A) ^ σ := Real.rpow_pos_of_pos haA σ
    have h8 : C⁻¹ * u ^ σ ≤ s ^ σ := by
      rw [h7, inv_mul_eq_div]
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hupos.le σ) hpw hCa
    calc μ.real {ω | t ≤ W ω} ≤ B * Real.exp (-(s ^ σ)) := h6
      _ ≤ C * Real.exp (-(C⁻¹ * u ^ σ)) :=
        mul_le_mul hCB (Real.exp_le_exp.2 (by linarith only [h8])) (Real.exp_pos _).le hC0.le


/-- **Tail of the Hölder-root scale, uniformly in the law.** -/
theorem hr_scale_tail (Ω : Type*) [MeasurableSpace Ω] {Λ ρ σ N₀ L C₀ : ℝ} (hΛ : 0 < Λ)
    (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hN : 0 ≤ N₀) (hL : 0 ≤ L) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X₀ : Ω → ℝ),
      (∀ ω, 1 ≤ X₀ ω) →
      Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
        (fun ω => Real.log (X₀ ω)) Λ →
      ∀ t : ℝ, 1 ≤ t →
        μ.real {ω | t ≤ C₀ * (3 : ℝ) ^ ms_star N₀ L (X₀ ω)} ≤
          C * Real.exp (-(C⁻¹ * (Real.log t) ^ σ)) := by
  have hC0 : 0 < C₀ := by linarith only [hC₀]
  have hb : 0 ≤ Real.log C₀ + 2 * (ms_j0 N₀ + 2 * L + 2) := by
    have : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀
    have : (0 : ℝ) ≤ ms_j0 N₀ := by positivity
    positivity
  obtain ⟨C, hC1, hC⟩ := hr_transfer Ω (a := 2) (A := Λ)
    (b0 := Real.log C₀ + 2 * (ms_j0 N₀ + 2 * L + 2)) (B := 1) (σ := σ) (by norm_num) hΛ hb hσ
  refine ⟨C, hC1, fun μ _ X₀ hX hO => ?_⟩
  have hT := ms_tail_mono_exp μ hσρ (ms_tail_of_isBigO hO) zero_le_one
  refine hC μ (fun ω => C₀ * (3 : ℝ) ^ ms_star N₀ L (X₀ ω)) (fun ω => |Real.log (X₀ ω)|)
    (fun ω => ?_) hT
  have hb' := ms_star_le_bound (L := L) hN hL (hX ω)
  have h1 : Real.log (C₀ * (3 : ℝ) ^ ms_star N₀ L (X₀ ω)) =
      Real.log C₀ + (ms_star N₀ L (X₀ ω) : ℝ) * Real.log 3 := by
    rw [Real.log_mul hC0.ne' (by positivity), Real.log_pow]
  have h2 : Real.log (X₀ ω) ≤ |Real.log (X₀ ω)| := le_abs_self _
  show Real.log (C₀ * (3 : ℝ) ^ ms_star N₀ L (X₀ ω)) ≤ 2 * |Real.log (X₀ ω)| + _
  linarith only [h1, hb', h2]

/-- `log k` is eventually below `ε √k`. -/
theorem hr_log_le_sqrt {ε : ℝ} (hε : 0 < ε) : ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
    Real.log (k : ℝ) ^ (2 : ℝ) ≤ ε * Real.sqrt k := by
  have h := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 2)).def hε
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually h)
  refine ⟨max k0 1, fun k hk => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (le_max_right k0 1).trans hk
  have h1 := hk0 k ((le_max_left _ _).trans hk)
  have hl : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith only [hk1]) _),
    ← Real.sqrt_eq_rpow] at h1
  exact h1

/-- `k^{-β} log k ≤ c` for large `k`. -/
theorem hr_small_delta {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : ∃ k0 : ℕ, 1 ≤ k0 ∧ ∀ k : ℕ, k0 ≤ k →
    (k : ℝ) ^ (-β) * Real.log (k : ℝ) ≤ c := by
  have h := (isLittleO_log_rpow_atTop hβ).def hc
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually h)
  refine ⟨max k0 1, le_max_right _ _, fun k hk => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (le_max_right k0 1).trans hk
  have h1 := hk0 k ((le_max_left _ _).trans hk)
  have hl : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  rw [Real.norm_of_nonneg hl, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith only [hk1]) _)] at h1
  rw [Real.rpow_neg (by linarith only [hk1]), inv_mul_eq_div, div_le_iff₀
    (Real.rpow_pos_of_pos (by linarith only [hk1]) _)]
  linarith only [h1, mul_comm c ((k : ℝ) ^ β)]

/-- From the sharp asymptotic of `σ̄_m` to a two-sided bound by `√m`. -/
theorem hr_sigma_window {cs K Cs : ℝ} (hcs : 0 < cs) (hCs : 1 ≤ Cs) :
    ∃ a : ℝ, 0 < a ∧ ∃ m1 : ℕ, 1 ≤ m1 ∧ ∀ m : ℕ, m1 ≤ m → ∀ s : ℝ,
      |s - (2 * cs * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
        Cs * cs⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K) →
      a / 2 * Real.sqrt m ≤ s ∧ s ≤ 3 * a / 2 * Real.sqrt m := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set a : ℝ := Real.sqrt (2 * cs * Real.log 3) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
  set ε : ℝ := a * cs / (4 * Cs) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨k0, hk0⟩ := hr_log_le_sqrt hε0
  refine ⟨a, ha0, max (max k0 1) ⌈(|K| / ε) ^ 2⌉₊, le_trans (le_max_right _ _) (le_max_left _ _),
    fun m hm s hs => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by
    exact_mod_cast (le_max_right k0 1).trans ((le_max_left _ _).trans hm)
  have hlog := hk0 m ((le_max_left _ _).trans ((le_max_left _ _).trans hm))
  have hsq : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hK : K ≤ ε * Real.sqrt m := by
    have h1 : (|K| / ε) ^ 2 ≤ (m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hm)
    have h2 : |K| / ε ≤ Real.sqrt m := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ |K| / ε)]
      exact Real.sqrt_le_sqrt h1
    have h3 : |K| ≤ ε * Real.sqrt m := by
      rw [div_le_iff₀ hε0] at h2; linarith only [h2, mul_comm ε (Real.sqrt m)]
    exact (le_abs_self K).trans h3
  have hq : (2 * cs * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2) = a * Real.sqrt m := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity)]
  rw [hq] at hs
  have hbound : Cs * cs⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K) ≤ a / 2 * Real.sqrt m := by
    have h1 : Real.log (m : ℝ) ^ (2 : ℝ) + K ≤ 2 * ε * Real.sqrt m := by
      linarith only [hlog, hK]
    have hpos : 0 ≤ Cs * cs⁻¹ := by positivity
    calc Cs * cs⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K) ≤ Cs * cs⁻¹ * (2 * ε * Real.sqrt m) :=
          mul_le_mul_of_nonneg_left h1 hpos
      _ = a / 2 * Real.sqrt m := by
          rw [hε]; field_simp; norm_num
  have h2 := (abs_le.1 (hs.trans hbound))
  constructor <;> linarith only [h2.1, h2.2]

/-- Ratio of `shom` at two scales. -/
theorem hr_ratio {a : ℝ} (ha : 0 < a) {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) {sk sm : ℝ}
    (h1 : a / 2 * Real.sqrt k ≤ sk) (h2 : sm ≤ 3 * a / 2 * Real.sqrt m) :
    sm ≤ 3 * (1 + ((m : ℝ) - k)) * sk := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm' : (k : ℝ) ≤ m := by exact_mod_cast hkm
  set j : ℝ := (m : ℝ) - k with hj
  have hj0 : 0 ≤ j := by linarith only [hkm', hj]
  have hm : (m : ℝ) ≤ k * (1 + j) ^ 2 := by
    nlinarith only [hk1, hj0, hj, mul_nonneg hj0 (by linarith only [hk1] : (0 : ℝ) ≤ k)]
  have hs : Real.sqrt m ≤ Real.sqrt k * (1 + j) := by
    calc Real.sqrt m ≤ Real.sqrt (k * (1 + j) ^ 2) := Real.sqrt_le_sqrt hm
      _ = Real.sqrt k * (1 + j) := by
        rw [Real.sqrt_mul (by linarith only [hk1]), Real.sqrt_sq (by linarith only [hj0])]
  have hk0 : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  have : 3 * a / 2 * Real.sqrt m ≤ 3 * a / 2 * (Real.sqrt k * (1 + j)) :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h3 : 3 * (1 + j) * (a / 2 * Real.sqrt k) ≤ 3 * (1 + j) * sk :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith only [h2, this, h3]

/-- The source term at scale `k` is controlled by the source term at scale `m ≥ k`. -/
theorem hr_F_bound {γ : ℝ} (hγ1 : γ ≤ 1) {k m : ℕ} (hkm : k ≤ m) {sk sm : ℝ}
    (hsk : 0 < sk) (hsm : 0 < sm) (hr : sm ≤ 3 * (1 + ((m : ℝ) - k)) * sk) :
    sk⁻¹ * (3 : ℝ) ^ (2 * (k : ℝ)) ≤
      3 * (3 : ℝ) ^ (-γ * ((m : ℝ) - k)) * (sm⁻¹ * (3 : ℝ) ^ (2 * (m : ℝ))) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
  have e1 : (3 : ℝ) ^ (2 * ((k + j : ℕ) : ℝ)) =
      (3 : ℝ) ^ (2 * (k : ℝ)) * (3 : ℝ) ^ (2 * (j : ℝ)) := by
    rw [← Real.rpow_add (by norm_num)]; congr 1; push_cast; ring
  have e2 : ((k + j : ℕ) : ℝ) - k = j := by push_cast; ring
  rw [e1, e2]
  rw [e2] at hr
  have hinv : sk⁻¹ ≤ 3 * (1 + (j : ℝ)) * sm⁻¹ := by
    have e : sk⁻¹ = sm⁻¹ * sm * sk⁻¹ := by field_simp
    have e' : 3 * (1 + (j : ℝ)) * sm⁻¹ = sm⁻¹ * (3 * (1 + (j : ℝ)) * sk) * sk⁻¹ := by field_simp
    rw [e, e']
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr (inv_pos.2 hsm).le)
      (inv_pos.2 hsk).le
  have hj3 : (1 + (j : ℝ)) ≤ (3 : ℝ) ^ (j : ℝ) := by
    rw [Real.rpow_natCast]
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 2 by norm_num) j
    norm_num at this
    nlinarith only [this, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj4 : (3 : ℝ) ^ (j : ℝ) ≤ (3 : ℝ) ^ (-γ * (j : ℝ)) * (3 : ℝ) ^ (2 * (j : ℝ)) := by
    rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith only [hγ1, hj0])
  have h3 : 0 < (3 : ℝ) ^ (2 * (k : ℝ)) := by positivity
  have hsm' : 0 < sm⁻¹ := inv_pos.2 hsm
  calc sk⁻¹ * (3 : ℝ) ^ (2 * (k : ℝ)) ≤ 3 * (1 + (j : ℝ)) * sm⁻¹ * (3 : ℝ) ^ (2 * (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hinv h3.le
    _ ≤ 3 * ((3 : ℝ) ^ (-γ * (j : ℝ)) * (3 : ℝ) ^ (2 * (j : ℝ))) * sm⁻¹ *
          (3 : ℝ) ^ (2 * (k : ℝ)) := by
        have := mul_le_mul_of_nonneg_left (hj3.trans hj4) (by norm_num : (0 : ℝ) ≤ 3)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hsm'.le) h3.le
    _ = _ := by ring

/-- Satisfiability of `hr_scale_tail`: the Dirac law with `X₀ ≡ 1`. -/
example {Ω : Type*} [MeasurableSpace Ω] (ω₀ : Ω) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      (MeasureTheory.Measure.dirac ω₀).real
        {ω | t ≤ (1 : ℝ) * (3 : ℝ) ^ ms_star 1 1 ((fun _ : Ω => (1 : ℝ)) ω)} ≤
        C * Real.exp (-(C⁻¹ * (Real.log t) ^ (1 / 2 : ℝ))) := by
  obtain ⟨C, hC1, hC⟩ := hr_scale_tail Ω (Λ := 1) (ρ := 1) (σ := 1 / 2) (N₀ := 1) (L := 1)
    (C₀ := 1) one_pos (by norm_num) (by norm_num) zero_le_one zero_le_one le_rfl
  refine ⟨C, hC1, fun t ht => hC (MeasureTheory.Measure.dirac ω₀) (fun _ => (1 : ℝ))
    (fun _ => le_rfl) ?_ t ht⟩
  rw [Homogenization.IndependentSums.isBigO_gammaSigma_iff]
  intro t ht
  have h : Homogenization.IndependentSums.absTailEvent (fun _ : Ω => Real.log (1 : ℝ)) (1 * t) =
      ∅ := by
    ext ω
    simp only [Homogenization.IndependentSums.mem_absTailEvent, Real.log_one, abs_zero,
      Set.mem_empty_iff_false, iff_false, not_lt]
    linarith only [ht]
  rw [h]
  simp only [measureReal_empty]
  exact (Real.exp_pos _).le

/-- Satisfiability of `hr_ratio` and `hr_F_bound`: constant `shom ≡ 1`. -/
example : (1 : ℝ) ≤ 3 * (1 + (((1 : ℕ) : ℝ) - ((1 : ℕ) : ℝ))) * 1 :=
  hr_ratio (a := 2) (by norm_num) (le_refl 1) (le_refl 1) (by simp) (by simp)

example : (1 : ℝ)⁻¹ * (3 : ℝ) ^ (2 * ((0 : ℕ) : ℝ)) ≤
    3 * (3 : ℝ) ^ (-(1 / 2 : ℝ) * (((0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ))) *
      ((1 : ℝ)⁻¹ * (3 : ℝ) ^ (2 * ((0 : ℕ) : ℝ))) :=
  hr_F_bound (γ := 1 / 2) (by norm_num) (le_refl 0) one_pos one_pos (by simp)

end SuperdiffusionCLT.Section7
