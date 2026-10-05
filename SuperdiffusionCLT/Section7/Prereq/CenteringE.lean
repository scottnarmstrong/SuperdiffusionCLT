/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CenteringD

@[expose] public section

open scoped Pointwise
open scoped Matrix.Norms.L2Operator

/-!
# Centring: the pairing of the stream matrix with the indicator of a dilated domain

The field `κ x = k (3^m x)` on the unit cube, read through the triadic filtration of the unit cube,
has generation increments controlled by the window clause (via the dictionary of
`Section7.kc3_cellavg_dilate`), and its oscillation inside a unit-scale cell is controlled by the
oscillation of `k` over `□_m`.  The pairing inequality of the filtration then bounds the difference
`(k)_{3^m W} - (k)_{□_m}`.

## Main results

* `Section7.kc3_incr_bound`: the generation increments of `κ` are at most `D t` almost everywhere.
* `Section7.kc3_remainder_bound`: `|κ - E_m κ| ≤ R` on the unit cube.
* `Section7.kc3_avg_diff_eq`: the difference of averages is the pairing divided by `|W|`.
-/

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization Homogenization.Book.Ch02

variable {d : ℕ}

/-- A cell of positive measure contains a point of the unit cube. -/
theorem kc3_exists_of_measure_ne_zero {t : ℕ} {n : Fin d → ℤ} (h : (kc2_μ d) (kc2_cell t n) ≠ 0) :
    ∃ x ∈ kc2_Q0 d, kc2_proj t x = n := by
  by_contra hne
  push Not at hne
  apply h
  rw [kc2_μ, Measure.restrict_apply (kc2_cell_measurable t n)]
  refine measure_mono_null (fun x hx => ?_) (measure_empty (μ := (volume : Measure (Vec d))))
  exact absurd hx.1 (fun h1 => hne x hx.2 h1)

/-- **The generation increments of `κ`.** -/
theorem kc3_incr_bound {k : Vec d → Mat d} {m : ℕ} {σ : ℝ} (hm : 2 ≤ m)
    (hwin : ∀ A B : ℝ, 1 ≤ A → 1 ≤ B → ∀ n : ℕ, (m : ℤ) - ⌈A * Real.log (B * (m : ℝ))⌉ ≤ (n : ℤ) →
      n ≤ m → ∀ Q : TriadicCube d, Q.scale = (n : ℤ) →
        cubeCenter Q ∈ cubeSet (originCube d (m : ℤ)) →
          matrixOperatorNorm (volumeAverageMat (cubeSet Q) k) ≤
            A * Real.log (B * (m : ℝ)) * (1 / 2 : ℝ) * (m : ℝ) ^ σ)
    (i j : Fin d) (hκ : Integrable (fun x => k ((3 : ℝ) ^ m • x) i j) (kc2_μ d)) {t : ℕ}
    (ht : t + 1 ≤ m) :
    ∀ᵐ x ∂(kc2_μ d), |kc2_incr (kc2_μ d) (kc2_sig d) (fun x => k ((3 : ℝ) ^ m • x) i j) t x| ≤
      (max (Real.log (m : ℝ)) (t : ℝ) + max (Real.log (m : ℝ)) ((t + 1 : ℕ) : ℝ)) * (1 / 2 : ℝ) *
        (m : ℝ) ^ σ := by
  refine kc2_incr_bound_of_cells hκ t _ fun n hn => ?_
  obtain ⟨x, hx, hxn⟩ := kc3_exists_of_measure_ne_zero hn
  have hx' : ∃ y ∈ kc2_Q0 d, kc2_proj t y = fun i => n i / 3 :=
    ⟨x, hx, by rw [kc2_proj_succ t x, hxn]⟩
  rw [kc3_cellavg_dilate m (t + 1) ⟨x, hx, hxn⟩ (fun y => k y i j),
    kc3_cellavg_dilate m t hx' (fun y => k y i j)]
  exact kc1_child_parent_bound hm hwin ht (kc3_cube_mem_descendants m t _ hx')
    (kc3_child_mem m t n) i j


/-- An average over a set of positive finite volume of a function within `R` of `a` is within `R`
of `a`. -/
theorem kc3_abs_avg_sub_le {A : Set (Vec d)} {f : Vec d → ℝ} {a R : ℝ}
    (hpos : 0 < (volume A).toReal) (hint : IntegrableOn f A) (h : ∀ y ∈ A, |f y - a| ≤ R) :
    |volumeAverage A f - a| ≤ R := by
  have hfin : volume A < ⊤ := lt_top_iff_ne_top.2 fun h0 => by simp [h0] at hpos
  have hfm : IsFiniteMeasure (volume.restrict A) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have h1 : ∫ y in A, (f y - a) = (∫ y in A, f y) - (volume A).toReal * a := by
    rw [integral_sub hint (integrable_const a), setIntegral_const, smul_eq_mul]
    rfl
  have h2 := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (Vec d))) (s := A)
    (f := fun y => f y - a) hfin (C := R) (fun y hy => by simpa only [Real.norm_eq_abs] using h y hy)
  rw [Real.norm_eq_abs, h1] at h2
  have hv : (volume A).toReal ≠ 0 := hpos.ne'
  have e : volumeAverage A f - a =
      (volume A).toReal⁻¹ * ((∫ y in A, f y) - (volume A).toReal * a) := by
    unfold volumeAverage
    field_simp
  rw [e, abs_mul, abs_of_pos (inv_pos.2 hpos)]
  calc (volume A).toReal⁻¹ * |(∫ y in A, f y) - (volume A).toReal * a|
      ≤ (volume A).toReal⁻¹ * (R * (volume A).toReal) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hpos).le
        simpa only [Measure.real] using h2
    _ = R := by field_simp

/-- A cell of `□_m` of generation `t` has positive volume. -/
theorem kc3_cell_vol_pos (m t : ℕ) {n : Fin d → ℤ} (hn : ∃ x ∈ kc2_Q0 d, kc2_proj t x = n) :
    0 < (volume (kc2_cell t n ∩ kc2_Q0 d)).toReal := by
  have h := kc3_toReal_smul (d := d) (c := (3 : ℝ) ^ m) (by positivity) (kc2_cell t n ∩ kc2_Q0 d)
  rw [← kc3_cube_eq_smul m t hn, volume_cubeSet_toReal] at h
  have hp := cubeVolume_pos (kc3_cube d m t n)
  have hc : (0 : ℝ) < ((3 : ℝ) ^ m) ^ d := by positivity
  by_contra hle
  have : (volume (kc2_cell t n ∩ kc2_Q0 d)).toReal = 0 :=
    le_antisymm (not_lt.1 hle) ENNReal.toReal_nonneg
  rw [this, mul_zero] at h
  linarith only [h, hp]

/-- **The remainder `κ - E_m κ`.** -/
theorem kc3_remainder_bound {k : Vec d → Mat d} {m : ℕ} (i j : Fin d)
    (hκ : Integrable (fun x => k ((3 : ℝ) ^ m • x) i j) (kc2_μ d)) {R0 : ℝ}
    (hosc : ∀ x ∈ cubeSet (originCube d (m : ℤ)), ∀ y ∈ cubeSet (originCube d (m : ℤ)),
      |k x i j - k y i j| ≤ R0) :
    ∀ᵐ x ∂(kc2_μ d), |k ((3 : ℝ) ^ m • x) i j -
        ((kc2_μ d)[(fun x => k ((3 : ℝ) ^ m • x) i j) | kc2_sig d m]) x| ≤ R0 := by
  refine kc2_remainder_bound_of_cells hκ m R0 fun x hx => ?_
  have hn : ∃ y ∈ kc2_Q0 d, kc2_proj m y = kc2_proj m x := ⟨x, hx, rfl⟩
  rw [kc3_cellavg_eq]
  have hxA : x ∈ kc2_cell m (kc2_proj m x) ∩ kc2_Q0 d := ⟨rfl, hx⟩
  have hQ : IntegrableOn (fun x => k ((3 : ℝ) ^ m • x) i j) (kc2_Q0 d) := hκ
  have hint : IntegrableOn (fun x => k ((3 : ℝ) ^ m • x) i j)
      (kc2_cell m (kc2_proj m x) ∩ kc2_Q0 d) :=
    hQ.mono_set Set.inter_subset_right
  have hmem : ∀ y ∈ kc2_Q0 d, (3 : ℝ) ^ m • y ∈ cubeSet (originCube d (m : ℤ)) := fun y hy => by
    rw [← kc3_smul_Q0]; exact Set.smul_mem_smul_set hy
  have := kc3_abs_avg_sub_le (kc3_cell_vol_pos m m hn) hint
    (a := k ((3 : ℝ) ^ m • x) i j) (R := R0) fun y hy => hosc _ (hmem y hy.2) _ (hmem x hx)
  rw [abs_sub_comm]
  exact this


/-- **Difference of averages as a pairing.** -/
theorem kc3_avg_diff_eq (k : Vec d → Mat d) (m : ℕ) (i j : Fin d) {W : Set (Vec d)}
    (hWm : MeasurableSet W) (hWQ : W ⊆ kc2_Q0 d) (hv : 0 < (volume W).toReal) :
    volumeAverage ((3 : ℝ) ^ m • W) (fun y => k y i j) -
        volumeAverage (cubeSet (originCube d (m : ℤ))) (fun y => k y i j) =
      (volume W).toReal⁻¹ *
        (∫ x, k ((3 : ℝ) ^ m • x) i j * W.indicator (fun _ => (1 : ℝ)) x ∂(kc2_μ d) -
          (∫ x, k ((3 : ℝ) ^ m • x) i j ∂(kc2_μ d)) * (volume W).toReal) := by
  have hc : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  rw [← kc3_smul_Q0, kc3_volumeAverage_smul hc, kc3_volumeAverage_smul hc]
  have h1 : ∫ x, k ((3 : ℝ) ^ m • x) i j * W.indicator (fun _ => (1 : ℝ)) x ∂(kc2_μ d) =
      ∫ x in W, k ((3 : ℝ) ^ m • x) i j := by
    have : (fun x => k ((3 : ℝ) ^ m • x) i j * W.indicator (fun _ => (1 : ℝ)) x) =
        W.indicator (fun x => k ((3 : ℝ) ^ m • x) i j) := by
      funext x
      by_cases hx : x ∈ W <;> simp [hx]
    rw [this, integral_indicator hWm, kc2_μ, Measure.restrict_restrict hWm,
      Set.inter_eq_left.2 hWQ]
  rw [h1]
  unfold volumeAverage
  rw [kc2_volume_Q0, kc2_μ]
  simp only [ENNReal.toReal_one, inv_one, one_mul]
  field_simp


/-- The arithmetic of the weighted sum with `r = 1/3`. -/
theorem kc3_sum_bound {m : ℕ} (hm : 2 ≤ m) {σ ε Cd : ℝ} (hε : 0 < ε) (hCd : 0 ≤ Cd) :
    ∑ t ∈ Finset.range m,
        ((max (Real.log (m : ℝ)) (t : ℝ) + max (Real.log (m : ℝ)) ((t + 1 : ℕ) : ℝ)) *
            (1 / 2 : ℝ) * (m : ℝ) ^ σ) * (Cd * (1 / 3 : ℝ) ^ t) ≤
      Cd * (((1 - 1 / 3 : ℝ)⁻¹ + ((1 - 1 / 3 : ℝ)⁻¹) ^ 2) * ((1 + ε⁻¹) * (m : ℝ) ^ (σ + ε))) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hL : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith only [hmR])
  have hM : 0 ≤ (m : ℝ) ^ σ := Real.rpow_nonneg (by linarith only [hmR]) σ
  have hr1 : (1 / 3 : ℝ) < 1 := by norm_num
  have h1 := kc1_weighted_sum (L := Real.log (m : ℝ)) (r := 1 / 3) (Cg := Cd) (δ := 1 / 2)
    (M := (m : ℝ) ^ σ) (W := fun t => Cd * (1 / 3 : ℝ) ^ t) (m := m) hL (by norm_num) hr1 hCd
    (by positivity) (fun t => ⟨by positivity, le_rfl⟩)
  have h2 := kc1_const_le hL hr1
  have h3 := kc1_log_absorb hm (σ := σ) hε
  have hrr : 0 ≤ (1 - 1 / 3 : ℝ)⁻¹ + ((1 - 1 / 3 : ℝ)⁻¹) ^ 2 :=
    add_nonneg (by norm_num) (sq_nonneg _)
  refine h1.trans ?_
  calc Cd * (1 / 2 * (m : ℝ) ^ σ) *
        ((2 * Real.log (m : ℝ) + 1) / (1 - 1 / 3) + 2 * (1 / 3) / (1 - 1 / 3) ^ 2)
      ≤ Cd * (1 / 2 * (m : ℝ) ^ σ) *
        (2 * ((1 - 1 / 3 : ℝ)⁻¹ + ((1 - 1 / 3 : ℝ)⁻¹) ^ 2) * (1 + Real.log (m : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Cd * (((1 - 1 / 3 : ℝ)⁻¹ + ((1 - 1 / 3 : ℝ)⁻¹) ^ 2) *
          ((1 + Real.log (m : ℝ)) * (m : ℝ) ^ σ)) := by ring
    _ ≤ Cd * (((1 - 1 / 3 : ℝ)⁻¹ + ((1 - 1 / 3 : ℝ)⁻¹) ^ 2) * ((1 + ε⁻¹) * (m : ℝ) ^ (σ + ε))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hrr) hCd


/-- **Centring at one scale, deterministic form.** If the window clause holds at scale `m ≥ 2` for the
continuous field `k`, `k` oscillates by at most `R0` (in the entry `(i, j)`) over `□_m`, and
`W ⊆ [-1/2, 1/2)^d` is open with `v₀ ≤ |W|` and increments of `1_W` of size `Cd (1/3)^t`, then
the averages of `k_{ij}` over `3^m W` and over `□_m` differ by at most
`v₀⁻¹ (Cd (15/4) (1 + ε⁻¹) m^{σ+ε} + R0 Cd 3^{-m})`. -/
theorem kc3_centering_core {k : Vec d → Mat d} (i j : Fin d)
    (hk : Continuous fun x => k x i j) {m : ℕ} (hm : 2 ≤ m)
    {σ ε : ℝ} (hε : 0 < ε)
    (hwin : ∀ A B : ℝ, 1 ≤ A → 1 ≤ B → ∀ n : ℕ, (m : ℤ) - ⌈A * Real.log (B * (m : ℝ))⌉ ≤ (n : ℤ) →
      n ≤ m → ∀ Q : TriadicCube d, Q.scale = (n : ℤ) →
        cubeCenter Q ∈ cubeSet (originCube d (m : ℤ)) →
          matrixOperatorNorm (volumeAverageMat (cubeSet Q) k) ≤
            A * Real.log (B * (m : ℝ)) * (1 / 2 : ℝ) * (m : ℝ) ^ σ)
    {R0 : ℝ}
    (hosc : ∀ x ∈ cubeSet (originCube d (m : ℤ)), ∀ y ∈ cubeSet (originCube d (m : ℤ)),
      |k x i j - k y i j| ≤ R0)
    {W : Set (Vec d)} (hW : IsOpen W) (hWQ : W ⊆ kc2_Q0 d) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hv : v₀ ≤ (volume W).toReal) {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hinc : ∀ t : ℕ, ∫ x, |kc2_incr (kc2_μ d) (kc2_sig d) (W.indicator (fun _ => (1 : ℝ))) t x|
      ∂(kc2_μ d) ≤ Cd * (1 / 3 : ℝ) ^ t)
    (hrem : ∫ x, |W.indicator (fun _ => (1 : ℝ)) x -
      ((kc2_μ d)[W.indicator (fun _ => (1 : ℝ)) | kc2_sig d m]) x| ∂(kc2_μ d) ≤
        Cd * (1 / 3 : ℝ) ^ m) :
    |volumeAverage ((3 : ℝ) ^ m • W) (fun y => k y i j) -
        volumeAverage (cubeSet (originCube d (m : ℤ))) (fun y => k y i j)| ≤
      v₀⁻¹ * (Cd * (((1 - 1 / 3 : ℝ)⁻¹ + ((1 - 1 / 3 : ℝ)⁻¹) ^ 2) *
        ((1 + ε⁻¹) * (m : ℝ) ^ (σ + ε))) + R0 * (Cd * (1 / 3 : ℝ) ^ m)) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hL : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith only [hmR])
  have hmem : ∀ y ∈ kc2_Q0 d, (3 : ℝ) ^ m • y ∈ cubeSet (originCube d (m : ℤ)) := fun y hy => by
    rw [← kc3_smul_Q0]; exact Set.smul_mem_smul_set hy
  have h0Q : (0 : Vec d) ∈ kc2_Q0 d := by
    rw [kc2_mem_Q0]
    intro i
    simp only [Pi.zero_apply]
    constructor <;> norm_num
  have h0 := hmem 0 h0Q
  have hR0 : 0 ≤ R0 := by
    have := hosc _ h0 _ h0
    simpa using this
  have hcont : Continuous (fun x : Vec d => k ((3 : ℝ) ^ m • x) i j) := by
    exact hk.comp (continuous_const_smul _)
  have hbd : ∀ᵐ x ∂(kc2_μ d), ‖k ((3 : ℝ) ^ m • x) i j‖ ≤ |k ((3 : ℝ) ^ m • 0) i j| + R0 := by
    rw [kc2_μ, ae_restrict_iff' kc2_Q0_measurable]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have := hosc _ (hmem x hx) _ h0
    rw [Real.norm_eq_abs]
    have h2 := abs_sub_abs_le_abs_sub (k ((3 : ℝ) ^ m • x) i j) (k ((3 : ℝ) ^ m • (0 : Vec d)) i j)
    linarith only [h2, this]
  have hκ2 : MemLp (fun x : Vec d => k ((3 : ℝ) ^ m • x) i j) 2 (kc2_μ d) :=
    MemLp.of_bound hcont.aestronglyMeasurable _ hbd
  have hκ := hκ2.integrable (by norm_num)
  have hD : ∀ t < m, ∀ᵐ x ∂(kc2_μ d), |kc2_incr (kc2_μ d) (kc2_sig d)
      (fun x => k ((3 : ℝ) ^ m • x) i j) t x| ≤
      (max (Real.log (m : ℝ)) (t : ℝ) + max (Real.log (m : ℝ)) ((t + 1 : ℕ) : ℝ)) * (1 / 2 : ℝ) *
        (m : ℝ) ^ σ := fun t ht => kc3_incr_bound hm hwin i j hκ ht
  have hR := kc3_remainder_bound i j hκ hosc
  have hpair := kc2_pairing_sup_indicator hW hWQ hκ2 m _ R0 hD hR
  have hvpos : 0 < (volume W).toReal := lt_of_lt_of_le hv₀ hv
  rw [kc3_avg_diff_eq k m i j hW.measurableSet hWQ hvpos, abs_mul, abs_of_pos (inv_pos.2 hvpos)]
  have hM : 0 ≤ (m : ℝ) ^ σ := Real.rpow_nonneg (by linarith only [hmR]) σ
  have hsum : ∑ t ∈ Finset.range m,
      ((max (Real.log (m : ℝ)) (t : ℝ) + max (Real.log (m : ℝ)) ((t + 1 : ℕ) : ℝ)) *
        (1 / 2 : ℝ) * (m : ℝ) ^ σ) *
        ∫ x, |kc2_incr (kc2_μ d) (kc2_sig d) (W.indicator (fun _ => (1 : ℝ))) t x| ∂(kc2_μ d) ≤
      ∑ t ∈ Finset.range m,
      ((max (Real.log (m : ℝ)) (t : ℝ) + max (Real.log (m : ℝ)) ((t + 1 : ℕ) : ℝ)) *
        (1 / 2 : ℝ) * (m : ℝ) ^ σ) * (Cd * (1 / 3 : ℝ) ^ t) := by
    refine Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hinc t) ?_
    have h1 : 0 ≤ max (Real.log (m : ℝ)) (t : ℝ) := le_trans hL (le_max_left _ _)
    have h2 : 0 ≤ max (Real.log (m : ℝ)) ((t + 1 : ℕ) : ℝ) := le_trans hL (le_max_left _ _)
    positivity
  have hbound : |∫ x, k ((3 : ℝ) ^ m • x) i j * W.indicator (fun _ => (1 : ℝ)) x ∂(kc2_μ d) -
        (∫ x, k ((3 : ℝ) ^ m • x) i j ∂(kc2_μ d)) * (volume W).toReal| ≤
      Cd * (((1 - 1 / 3 : ℝ)⁻¹ + ((1 - 1 / 3 : ℝ)⁻¹) ^ 2) * ((1 + ε⁻¹) * (m : ℝ) ^ (σ + ε))) +
        R0 * (Cd * (1 / 3 : ℝ) ^ m) :=
    hpair.trans (add_le_add (hsum.trans (kc3_sum_bound hm hε hCd))
      (mul_le_mul_of_nonneg_left hrem hR0))
  calc (volume W).toReal⁻¹ * _ ≤ (volume W).toReal⁻¹ * (Cd * (((1 - 1 / 3 : ℝ)⁻¹ +
        ((1 - 1 / 3 : ℝ)⁻¹) ^ 2) * ((1 + ε⁻¹) * (m : ℝ) ^ (σ + ε))) +
        R0 * (Cd * (1 / 3 : ℝ) ^ m)) := mul_le_mul_of_nonneg_left hbound (inv_pos.2 hvpos).le
    _ ≤ v₀⁻¹ * _ := by
        refine mul_le_mul_of_nonneg_right (inv_anti₀ hv₀ hv) ?_
        have : 0 ≤ Cd * (((1 - 1 / 3 : ℝ)⁻¹ + ((1 - 1 / 3 : ℝ)⁻¹) ^ 2) *
            ((1 + ε⁻¹) * (m : ℝ) ^ (σ + ε))) := by positivity
        have h3 : 0 ≤ R0 * (Cd * (1 / 3 : ℝ) ^ m) := by positivity
        linarith only [this, h3]


/-! ### The unit-scale oscillation from the pointwise growth clause -/

/-- The constant of the growth clause at scale `m`. -/
noncomputable def kc3_aconst (d : ℕ) (σ C0 : ℝ) : ℝ :=
  Real.sqrt (max C0 0) * (Real.log 9 + Real.log (1 + d)) ^ (1 + σ)

theorem kc3_aconst_nonneg (d : ℕ) (σ C0 : ℝ) : 0 ≤ kc3_aconst d σ C0 := by
  unfold kc3_aconst
  have h1 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ Real.log (1 + (d : ℝ)) := Real.log_nonneg (by simp)
  positivity

/-- **Growth at the scale `m`.** If `‖Φ x‖² ≤ C0 (log (K² + |x|²))^{2(1+σ)}` for all `x` and
`27 ≤ K ≤ 3^m`, then `‖Φ x‖ ≤ a m^{1+σ}` on `□_m`. -/
theorem kc3_growth_on_cube {Φ : Vec d → Mat d} {K C0 σ : ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hK27 : 27 ≤ K) (hKm : K ≤ (3 : ℝ) ^ m)
    (hg : ∀ x : Vec d, matrixOperatorNorm (Φ x) ^ 2 ≤
      C0 * Real.log (K ^ 2 + vecNormSq x) ^ (2 * (1 + σ)))
    (hσ : 0 ≤ σ) {x : Vec d} (hx : x ∈ cubeSet (originCube d (m : ℤ))) :
    matrixOperatorNorm (Φ x) ≤ kc3_aconst d σ C0 * (m : ℝ) ^ (1 + σ) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by linarith only [hmR]
  rw [mem_cubeSet_originCube_iff] at hx
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (m : ℤ) := by positivity
  have h3' : (3 : ℝ) ^ (m : ℤ) = (3 : ℝ) ^ m := zpow_natCast _ _
  have hxi : ∀ i, x i * x i ≤ ((3 : ℝ) ^ m) ^ 2 := fun i => by
    obtain ⟨a, b⟩ := hx i
    rw [h3'] at a b
    have : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
    nlinarith only [a, b, this]
  have hnorm : vecNormSq x ≤ (d : ℝ) * ((3 : ℝ) ^ m) ^ 2 := by
    unfold vecNormSq vecDot
    calc ∑ i, x i * x i ≤ ∑ _i : Fin d, ((3 : ℝ) ^ m) ^ 2 := Finset.sum_le_sum fun i _ => hxi i
      _ = _ := by simp
  have hK2 : K ^ 2 ≤ ((3 : ℝ) ^ m) ^ 2 := by
    have : 0 ≤ K := by linarith only [hK27]
    exact pow_le_pow_left₀ this hKm 2
  have hsum : K ^ 2 + vecNormSq x ≤ (1 + (d : ℝ)) * ((3 : ℝ) ^ m) ^ 2 := by
    nlinarith only [hnorm, hK2]
  have hpos : 1 ≤ K ^ 2 + vecNormSq x := by
    have h0 : 0 ≤ vecNormSq x := by
      unfold vecNormSq vecDot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    nlinarith only [hK27, h0]
  have hlog0 : 0 ≤ Real.log (K ^ 2 + vecNormSq x) := Real.log_nonneg hpos
  set a₁ : ℝ := Real.log 9 + Real.log (1 + d) with ha₁
  have hl9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hld : 0 ≤ Real.log (1 + (d : ℝ)) := Real.log_nonneg (by simp)
  have ha0 : 0 ≤ a₁ := add_nonneg hl9 hld
  have hlog : Real.log (K ^ 2 + vecNormSq x) ≤ a₁ * (m : ℝ) := by
    have h1 := Real.log_le_log (by linarith only [hpos]) hsum
    have h2 : Real.log ((1 + (d : ℝ)) * ((3 : ℝ) ^ m) ^ 2) =
        Real.log (1 + d) + (m : ℝ) * Real.log 9 := by
      have e9 : ((3 : ℝ) ^ m) ^ 2 = (9 : ℝ) ^ m := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [Real.log_mul (by positivity) (by positivity), e9, Real.log_pow]
    rw [h2] at h1
    nlinarith only [h1, hld, hmR]
  have hpow : Real.log (K ^ 2 + vecNormSq x) ^ (2 * (1 + σ)) ≤ (a₁ * (m : ℝ)) ^ (2 * (1 + σ)) :=
    Real.rpow_le_rpow hlog0 hlog (by linarith only [hσ])
  have hT : 0 ≤ (a₁ * (m : ℝ)) ^ (1 + σ) := Real.rpow_nonneg (mul_nonneg ha0 hm0) _
  have hsq : (a₁ * (m : ℝ)) ^ (2 * (1 + σ)) = ((a₁ * (m : ℝ)) ^ (1 + σ)) ^ 2 := by
    rw [mul_comm 2, Real.rpow_mul (mul_nonneg ha0 hm0)]
    exact_mod_cast Real.rpow_natCast ((a₁ * (m : ℝ)) ^ (1 + σ)) 2
  have hmax : matrixOperatorNorm (Φ x) ^ 2 ≤ max C0 0 * ((a₁ * (m : ℝ)) ^ (1 + σ)) ^ 2 := by
    have h1 := hg x
    have h2 : C0 * Real.log (K ^ 2 + vecNormSq x) ^ (2 * (1 + σ)) ≤
        max C0 0 * (a₁ * (m : ℝ)) ^ (2 * (1 + σ)) := by
      calc C0 * Real.log (K ^ 2 + vecNormSq x) ^ (2 * (1 + σ))
          ≤ max C0 0 * Real.log (K ^ 2 + vecNormSq x) ^ (2 * (1 + σ)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hlog0 _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
    rw [hsq] at h2
    exact h1.trans h2
  have hnn : 0 ≤ matrixOperatorNorm (Φ x) := matrixOperatorNorm_nonneg (Φ x)
  calc matrixOperatorNorm (Φ x)
      = Real.sqrt (matrixOperatorNorm (Φ x) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (max C0 0 * ((a₁ * (m : ℝ)) ^ (1 + σ)) ^ 2) := Real.sqrt_le_sqrt hmax
    _ = Real.sqrt (max C0 0) * (a₁ * (m : ℝ)) ^ (1 + σ) := by
        rw [Real.sqrt_mul (le_max_right _ _), Real.sqrt_sq hT]
    _ = kc3_aconst d σ C0 * (m : ℝ) ^ (1 + σ) := by
        rw [Real.mul_rpow ha0 hm0, kc3_aconst, mul_assoc]


/-! ### Matrix form, and dilates of one fixed domain -/

/-- Operator norm from entries. -/
theorem kc3_opnorm_of_entries {A : Mat d} {B : ℝ} (h : ∀ i j, |A i j| ≤ B) :
    matrixOperatorNorm A ≤ (d : ℝ) ^ 2 * B := by
  refine (matrixOperatorNorm_le_matrixFrobeniusNorm A).trans
    ((matrixFrobeniusNorm_le_sum_abs_entries A).trans ?_)
  calc ∑ i : Fin d, ∑ j : Fin d, |A i j| ≤ ∑ _i : Fin d, ∑ _j : Fin d, B :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = (d : ℝ) ^ 2 * B := by simp; ring

/-- Weakening the data of the uniform class. -/
theorem kc3_unif_mono {U : Set (Vec d)} {r M₁ M₂ D r' M₂' D' : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) (hr' : 0 < r') (hr : r' ≤ r) (hM : M₂ ≤ M₂')
    (hD : D ≤ D') : IsUniformC11Domain U r' M₁ M₂' D' := by
  obtain ⟨ho, -, hd, hch⟩ := h
  exact ⟨ho, hr', fun x hx y hy => (hd x hx y hy).trans hD,
    fun x hx => (hch x hx).mono hr le_rfl hM⟩

/-- Dilates of a fixed domain by `λ ∈ (1/3, 1]` lie in one class. -/
theorem kc3_unif_smul {U : Set (Vec d)} {r M₁ M₂ D : ℝ} (h : IsUniformC11Domain U r M₁ M₂ D)
    {lam : ℝ} (hl0 : 1 / 3 < lam) (hl1 : lam ≤ 1) :
    IsUniformC11Domain (lam • U) (r / 3) M₁ (3 * |M₂|) (max D 0) := by
  have hl : 0 < lam := by linarith only [hl0]
  have hr : 0 < r := h.2.1
  refine kc3_unif_mono (h.smul hl) (by positivity) (by nlinarith only [hl0, hr]) ?_ ?_
  · have h1 : M₂ / lam ≤ |M₂| / lam := div_le_div_of_nonneg_right (le_abs_self _) hl.le
    have h2 : |M₂| / lam ≤ 3 * |M₂| := by
      rw [div_le_iff₀ hl]
      nlinarith only [hl0, abs_nonneg M₂]
    exact h1.trans h2
  · rcases le_total D 0 with hD | hD
    · rw [max_eq_right hD]; nlinarith only [hD, hl]
    · rw [max_eq_left hD]; nlinarith only [hD, hl1]

/-- Dilates by `λ ∈ (0, 1]` of a subset of the unit cube stay in the unit cube. -/
theorem kc3_smul_subset_Q0 {U : Set (Vec d)} (hU : U ⊆ kc2_Q0 d) {lam : ℝ} (hl0 : 0 < lam)
    (hl1 : lam ≤ 1) : lam • U ⊆ kc2_Q0 d := by
  rintro _ ⟨u, hu, rfl⟩
  rw [kc2_mem_Q0]
  intro i
  obtain ⟨a, b⟩ := kc2_mem_Q0.1 (hU hu) i
  simp only [Pi.smul_apply, smul_eq_mul]
  constructor
  · rcases le_total 0 (u i) with h | h
    · nlinarith only [mul_nonneg hl0.le h]
    · nlinarith only [a, hl1, h, mul_nonneg hl0.le (neg_nonneg.2 h)]
  · rcases le_total 0 (u i) with h | h
    · nlinarith only [b, hl1, h, mul_nonneg hl0.le h]
    · nlinarith only [mul_nonneg hl0.le (neg_nonneg.2 h)]

end SuperdiffusionCLT.Section7
