/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2ComparisonD

/-!
# From local cube bounds to a global `L^p` bound (abstract form)

Display `e.Dir.new.term.one`.  A countable
family of pairwise disjoint measurable cells `Q i` of volume `a`, each contained in a larger cell
`P i` of volume `b`, with the cells `P i` lying in `W` with total overlap `m`.  If a function `g`
is bounded on `Q i` by `α` times the normalized `L²` average of `v` over `P i` plus `β` times the
normalized `L^p` average of `w` over `P i` (`p < 2`), and vanishes off `⋃ Q i` on `S`, then its
`L^p(S)` norm is bounded by the global norms of `v` and `w` on `W`:
`‖g‖_{L^p(S)} ≤ α c^{1/2} |S|^{1/p-1/2} ‖v‖_{L²(W)} + β c^{1/p} ‖w‖_{L^p(W)}`, `c = a m / b`.

* `Section7.l2b_local_global`.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The normalized local average `(b⁻¹ ∫_P v^r)^{1/r}`. -/
noncomputable def l2b_avg (b : ℝ≥0∞) (P : Set (Vec d)) (v : Vec d → ℝ≥0∞) (r : ℝ) : ℝ≥0∞ :=
  (b⁻¹ * ∫⁻ x in P, v x ^ r) ^ (1 / r)

/-- The step function equal to `e i` on `Q i`. -/
noncomputable def l2b_step {ι : Type*} (Q : ι → Set (Vec d)) (e : ι → ℝ≥0∞) (x : Vec d) :
    ℝ≥0∞ :=
  ∑' i, (Q i).indicator (fun _ => e i) x

section Step

variable {ι : Type*} {Q : ι → Set (Vec d)} {e : ι → ℝ≥0∞}

theorem l2b_step_of_mem (hQ : Pairwise (Function.onFun Disjoint Q)) {j : ι} {x : Vec d}
    (hx : x ∈ Q j) : l2b_step Q e x = e j := by
  unfold l2b_step
  rw [tsum_eq_single j]
  · simp [hx]
  · intro i hi
    have : x ∉ Q i := fun h => (Set.disjoint_left.1 (hQ hi) h) hx
    simp [this]

theorem l2b_step_of_notMem {x : Vec d} (hx : ∀ i, x ∉ Q i) : l2b_step Q e x = 0 := by
  unfold l2b_step
  simp [hx]

theorem l2b_step_rpow (hQ : Pairwise (Function.onFun Disjoint Q)) {r : ℝ} (hr : 0 < r)
    (x : Vec d) :
    l2b_step Q e x ^ r = ∑' i, (Q i).indicator (fun _ => e i ^ r) x := by
  by_cases h : ∃ j, x ∈ Q j
  · obtain ⟨j, hj⟩ := h
    rw [l2b_step_of_mem hQ hj, tsum_eq_single j]
    · simp [hj]
    · intro i hi
      have : x ∉ Q i := fun h => (Set.disjoint_left.1 (hQ hi) h) hj
      simp [this]
  · push Not at h
    rw [l2b_step_of_notMem h, ENNReal.zero_rpow_of_pos hr]
    simp [h]

theorem l2b_step_measurable [Countable ι] (hQm : ∀ i, MeasurableSet (Q i)) : Measurable (l2b_step Q e) := by
  unfold l2b_step
  exact Measurable.tsum fun i => measurable_const.indicator (hQm i)

theorem l2b_lintegral_step_rpow [Countable ι] (hQm : ∀ i, MeasurableSet (Q i))
    (hQ : Pairwise (Function.onFun Disjoint Q)) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, l2b_step Q e x ^ r = ∑' i, e i ^ r * volume (Q i) := by
  simp_rw [l2b_step_rpow hQ hr]
  rw [lintegral_tsum fun i => (measurable_const.indicator (hQm i)).aemeasurable]
  refine tsum_congr fun i => ?_
  rw [lintegral_indicator (hQm i), setLIntegral_const]

/-- Hölder on `S`: the `L^p(S)` norm of a step function is at most its `L²` norm times
`|S|^{1/p-1/2}`. -/
theorem l2b_step_Lp_le [Countable ι] (hQm : ∀ i, MeasurableSet (Q i))
    (hQ : Pairwise (Function.onFun Disjoint Q)) {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2)
    (S : Set (Vec d)) :
    (∫⁻ x in S, l2b_step Q e x ^ p) ^ (1 / p) ≤
      (∑' i, e i ^ (2 : ℝ) * volume (Q i)) ^ (1 / (2 : ℝ)) * volume S ^ (1 / p - 1 / 2) := by
  have hp0 : 0 < p := by linarith only [hp1]
  have hθ : 0 < 1 / p - 1 / 2 := by
    have : 1 / 2 < 1 / p := by
      rw [div_lt_div_iff₀ (by norm_num) hp0]; linarith only [hp2]
    linarith only [this]
  set r : ℝ := (1 / p - 1 / 2)⁻¹ with hr
  have hr1 : 1 / r = 1 / p - 1 / 2 := by rw [hr, one_div, inv_inv]
  have hpq : p < 2 := hp2
  have hpqr : 1 / p = 1 / 2 + 1 / r := by rw [hr1]; ring
  have hf : AEMeasurable (l2b_step Q e) (volume.restrict S) :=
    (l2b_step_measurable (e := e) hQm).aemeasurable
  have hg : AEMeasurable (fun _ : Vec d => (1 : ℝ≥0∞)) (volume.restrict S) :=
    measurable_const.aemeasurable
  have h := ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hp0 hpq hpqr (volume.restrict S) hf hg
  have h1 : ∀ a : Vec d, (l2b_step Q e * fun _ : Vec d => (1 : ℝ≥0∞)) a = l2b_step Q e a := by
    intro a; simp
  simp_rw [h1] at h
  have hr0 : 0 < r := by rw [hr]; exact inv_pos.2 hθ
  have h2 : (∫⁻ a, (fun _ : Vec d => (1 : ℝ≥0∞)) a ^ r ∂volume.restrict S) = volume S := by
    simp [ENNReal.one_rpow]
  rw [h2, hr1] at h
  refine h.trans (mul_le_mul' ?_ le_rfl)
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  calc ∫⁻ a in S, l2b_step Q e a ^ (2 : ℝ) ≤ ∫⁻ a, l2b_step Q e a ^ (2 : ℝ) :=
        setLIntegral_le_lintegral _ _
    _ = ∑' i, e i ^ (2 : ℝ) * volume (Q i) := l2b_lintegral_step_rpow hQm hQ (by norm_num)

/-- The `L^p(S)` norm of a step function is at most its `L^p` norm. -/
theorem l2b_step_Lp_le_self [Countable ι] (hQm : ∀ i, MeasurableSet (Q i))
    (hQ : Pairwise (Function.onFun Disjoint Q)) {p : ℝ} (hp : 0 < p) (S : Set (Vec d)) :
    (∫⁻ x in S, l2b_step Q e x ^ p) ^ (1 / p) ≤ (∑' i, e i ^ p * volume (Q i)) ^ (1 / p) := by
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  calc ∫⁻ a in S, l2b_step Q e a ^ p ≤ ∫⁻ a, l2b_step Q e a ^ p :=
        setLIntegral_le_lintegral _ _
    _ = _ := l2b_lintegral_step_rpow hQm hQ hp

end Step

variable {ι : Type*}

/-- The sum over the cells of the local averages to the power `r` is bounded by the global
integral, with the overlap `m`. -/
theorem l2b_sum_avg_le [Countable ι] {Q P : ι → Set (Vec d)} {W : Set (Vec d)} {a b m : ℝ≥0∞}
    (ha : ∀ i, volume (Q i) = a)
    (hov : ∀ h : Vec d → ℝ≥0∞, ∑' i, ∫⁻ x in P i, h x ≤ m * ∫⁻ x in W, h x)
    (v : Vec d → ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    ∑' i, (l2b_avg b (P i) v r) ^ r * volume (Q i) ≤
      a * m * b⁻¹ * ∫⁻ x in W, v x ^ r := by
  have h1 : ∀ i, (l2b_avg b (P i) v r) ^ r * volume (Q i) =
      a * b⁻¹ * ∫⁻ x in P i, v x ^ r := by
    intro i
    unfold l2b_avg
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr.ne', ENNReal.rpow_one, ha i]
    ring
  simp_rw [h1]
  rw [ENNReal.tsum_mul_left]
  calc a * b⁻¹ * ∑' i, ∫⁻ x in P i, v x ^ r ≤ a * b⁻¹ * (m * ∫⁻ x in W, v x ^ r) :=
        mul_le_mul' le_rfl (hov _)
    _ = a * m * b⁻¹ * ∫⁻ x in W, v x ^ r := by ring

/-- `‖α f‖_{L^p(S)} = α ‖f‖_{L^p(S)}`. -/
theorem l2b_lintegral_const_mul_rpow {p : ℝ} (hp : 0 < p) {α : ℝ≥0∞} {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) (S : Set (Vec d)) :
    (∫⁻ x in S, (α * f x) ^ p) ^ (1 / p) = α * (∫⁻ x in S, f x ^ p) ^ (1 / p) := by
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [lintegral_const_mul _ (hf.pow_const p), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- **Local-to-global bound** (abstract form). -/
theorem l2b_local_global [Countable ι] {Q P : ι → Set (Vec d)} (hQm : ∀ i, MeasurableSet (Q i))
    (hQ : Pairwise (Function.onFun Disjoint Q)) {W S : Set (Vec d)} (hS : MeasurableSet S)
    {a b m : ℝ≥0∞} (ha : ∀ i, volume (Q i) = a)
    (hov : ∀ h : Vec d → ℝ≥0∞, ∑' i, ∫⁻ x in P i, h x ≤ m * ∫⁻ x in W, h x)
    (v w : Vec d → ℝ≥0∞) {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) {α β : ℝ≥0∞} {g : Vec d → ℝ≥0∞}
    (hg : ∀ i, ∀ x ∈ Q i, g x ≤ α * l2b_avg b (P i) v 2 + β * l2b_avg b (P i) w p)
    (hg0 : ∀ x ∈ S, (∀ i, x ∉ Q i) → g x = 0) :
    (∫⁻ x in S, g x ^ p) ^ (1 / p) ≤
      α * (a * m * b⁻¹) ^ (1 / (2 : ℝ)) * volume S ^ (1 / p - 1 / 2) *
          (∫⁻ x in W, v x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) +
        β * (a * m * b⁻¹) ^ (1 / p) * (∫⁻ x in W, w x ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith only [hp1]
  set ee : ι → ℝ≥0∞ := fun i => l2b_avg b (P i) v 2 with hee
  set ff : ι → ℝ≥0∞ := fun i => l2b_avg b (P i) w p with hff
  have hmeas1 : Measurable (l2b_step Q ee) := l2b_step_measurable hQm
  have hmeas2 : Measurable (l2b_step Q ff) := l2b_step_measurable hQm
  have hle : ∀ x ∈ S, g x ≤ α * l2b_step Q ee x + β * l2b_step Q ff x := by
    intro x hx
    by_cases h : ∃ j, x ∈ Q j
    · obtain ⟨j, hj⟩ := h
      rw [l2b_step_of_mem hQ hj, l2b_step_of_mem hQ hj]
      exact hg j x hj
    · push Not at h
      rw [hg0 x hx h]; exact zero_le
  have h1 : (∫⁻ x in S, g x ^ p) ^ (1 / p) ≤
      (∫⁻ x in S, (α * l2b_step Q ee x + β * l2b_step Q ff x) ^ p) ^ (1 / p) := by
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    exact setLIntegral_mono' hS fun x hx => ENNReal.rpow_le_rpow (hle x hx) hp0.le
  have h2 := ENNReal.lintegral_Lp_add_le (μ := volume.restrict S)
    (f := fun x => α * l2b_step Q ee x) (g := fun x => β * l2b_step Q ff x)
    (hmeas1.const_mul α).aemeasurable (hmeas2.const_mul β).aemeasurable hp1
  refine h1.trans (h2.trans (add_le_add ?_ ?_))
  · rw [l2b_lintegral_const_mul_rpow hp0 hmeas1]
    have h3 := l2b_step_Lp_le (e := ee) hQm hQ hp1 hp2 S
    have h4 : ∑' i, ee i ^ (2 : ℝ) * volume (Q i) ≤ a * m * b⁻¹ * ∫⁻ x in W, v x ^ (2 : ℝ) :=
      l2b_sum_avg_le ha hov v (by norm_num)
    calc α * (∫⁻ x in S, l2b_step Q ee x ^ p) ^ (1 / p)
        ≤ α * ((∑' i, ee i ^ (2 : ℝ) * volume (Q i)) ^ (1 / (2 : ℝ)) * volume S ^ (1 / p - 1 / 2)) :=
          mul_le_mul' le_rfl h3
      _ ≤ α * ((a * m * b⁻¹ * ∫⁻ x in W, v x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            volume S ^ (1 / p - 1 / 2)) :=
          mul_le_mul' le_rfl (mul_le_mul' (ENNReal.rpow_le_rpow h4 (by norm_num)) le_rfl)
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]; ring
  · rw [l2b_lintegral_const_mul_rpow hp0 hmeas2]
    have h3 := l2b_step_Lp_le_self (e := ff) hQm hQ hp0 S
    have h4 : ∑' i, ff i ^ p * volume (Q i) ≤ a * m * b⁻¹ * ∫⁻ x in W, w x ^ p :=
      l2b_sum_avg_le ha hov w hp0
    calc β * (∫⁻ x in S, l2b_step Q ff x ^ p) ^ (1 / p)
        ≤ β * (∑' i, ff i ^ p * volume (Q i)) ^ (1 / p) := mul_le_mul' le_rfl h3
      _ ≤ β * (a * m * b⁻¹ * ∫⁻ x in W, w x ^ p) ^ (1 / p) :=
          mul_le_mul' le_rfl (ENNReal.rpow_le_rpow h4 (by positivity))
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]; ring

end SuperdiffusionCLT.Section7
