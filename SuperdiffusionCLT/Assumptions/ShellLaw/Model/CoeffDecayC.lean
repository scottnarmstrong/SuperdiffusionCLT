/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.CoeffDecayB
public import Mathlib.Analysis.PSeries

/-!
# Uniform decay, support and summability of the kernel coefficients

## Main results

* `exists_norm_iteratedFDeriv_cellKernelCoeff_le`: the decay
  `‖iteratedFDeriv ℝ i (fun x ↦ cellKernelCoeff c x p) x‖ ≤ C / (1 + cellFreqNorm p) ^ N`,
  `i ≤ 2`, with `C` depending only on `d` and `N`.
* `cellKernelCoeff_eq_zero_of_one_le_abs_sub`, `iteratedFDeriv_cellKernelCoeff_eq_zero`: the
  coefficient of the cell centred at `c` and all its `x`-derivatives vanish away from `c`.
* `cellsNear`, `cellKernelCoeff_eq_zero_of_not_mem_cellsNear`: the finitely many cells `k / 2`
  that contribute at a given point.
* `exists_summable_bound_iteratedFDeriv_cellKernelCoeff`: a summable dominating sequence over
  the frame index, uniform in `c` and `x`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization Set Real MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The first two derivatives of the coefficient -/

theorem nv_norm_fderiv_Q_le (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) {B : ℝ}
    (hB : ∀ (j : Fin d) (y : Vec d), |nv_Q p (nv_dir (Pi.single j 1) (radialBump d)) y| ≤ B)
    (y : Vec d) : ‖fderiv ℝ (nv_Q p (radialBump d)) y‖ ≤ d * B := by
  refine (nv_norm_le_sum_single _).trans ?_
  calc ∑ j : Fin d, ‖fderiv ℝ (nv_Q p (radialBump d)) y (Pi.single j 1)‖
      ≤ ∑ _j : Fin d, B := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [nv_fderiv_Q_apply p radialBump_hasCompactSupport
          (radialBump_contDiff.of_le (by exact_mod_cast le_top)) y, Real.norm_eq_abs]
        exact hB j y
    _ = d * B := by simp

theorem nv_norm_iteratedFDeriv_two_Q_le (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) {B : ℝ}
    (hB : ∀ (j k : Fin d) (y : Vec d),
      |nv_Q p (nv_dir (Pi.single j 1) (nv_dir (Pi.single k 1) (radialBump d))) y| ≤ B)
    (y : Vec d) : ‖iteratedFDeriv ℝ 2 (nv_Q p (radialBump d)) y‖ ≤ d * (d * B) := by
  have h1 : ‖iteratedFDeriv ℝ 2 (nv_Q p (radialBump d)) y‖
      = ‖fderiv ℝ (fderiv ℝ (nv_Q p (radialBump d))) y‖ := by
    rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 1), norm_iteratedFDeriv_one]
  rw [h1]
  refine (nv_norm_le_sum_single _).trans ?_
  calc ∑ j : Fin d, ‖fderiv ℝ (fderiv ℝ (nv_Q p (radialBump d))) y (Pi.single j 1)‖
      ≤ ∑ _j : Fin d, (d * B) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        refine (nv_norm_le_sum_single _).trans ?_
        calc ∑ k : Fin d, ‖fderiv ℝ (fderiv ℝ (nv_Q p (radialBump d))) y (Pi.single j 1)
              (Pi.single k 1)‖
            ≤ ∑ _k : Fin d, B := by
              refine Finset.sum_le_sum fun k _ ↦ ?_
              rw [nv_fderiv_fderiv_Q_apply p radialBump_hasCompactSupport radialBump_contDiff,
                Real.norm_eq_abs]
              exact hB j k y
          _ = d * B := by simp
    _ = d * (d * B) := by simp

/-- **Uniform decay of the kernel coefficients and their first two `x`-derivatives.** For every
`N` there is a constant `C`, depending only on `d` and `N`, such that for all cell centres `c`,
points `x` and frame indices `p`, and `i ≤ 2`,
`‖iteratedFDeriv ℝ i (fun x ↦ cellKernelCoeff c x p) x‖ ≤ C / (1 + cellFreqNorm p) ^ N`. -/
theorem exists_norm_iteratedFDeriv_cellKernelCoeff_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c x : Vec d) (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)), ∀ i ≤ 2,
      ‖iteratedFDeriv ℝ i (fun x ↦ cellKernelCoeff c x p) x‖ ≤ C / (1 + cellFreqNorm p) ^ N := by
  obtain ⟨Mw, hMw0, hw⟩ := cellWeight_exists_bound_iteratedFDeriv (d := d) N
  obtain ⟨M, hM0, hM⟩ := nv_bump_bounds (d := d) N
  have hK : 0 ≤ nv_K d N Mw M := by unfold nv_K; positivity
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  refine ⟨(1 + d + d ^ 2) * nv_K d N Mw M, by positivity, fun c x p i hi ↦ ?_⟩
  have hD : 0 < (1 + cellFreqNorm p) ^ N :=
    pow_pos (by linarith only [cellFreqNorm_nonneg p]) N
  have hQ : ∀ {h : Vec d → ℝ}, ContDiff ℝ (N : WithTop ℕ∞) h →
      (∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M) → ∀ y,
      |nv_Q p h y| ≤ nv_K d N Mw M / (1 + cellFreqNorm p) ^ N :=
    fun hh hMh y ↦ (le_div_iff₀ hD).2 (nv_abs_Q_mul_pow_le hw hh hMh p y)
  have he : ∀ j : Fin d, ‖(Pi.single j 1 : Vec d)‖ ≤ 1 := fun j ↦ by
    rw [Pi.norm_single, norm_one]
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (radialBump d) := radialBump_contDiff
  have hb1 : ∀ j : Fin d, ∀ y, |nv_Q p (nv_dir (Pi.single j 1) (radialBump d)) y|
      ≤ nv_K d N Mw M / (1 + cellFreqNorm p) ^ N := fun j y ↦
    hQ (nv_contDiff_of_top (nv_contDiff_dir hψ _) N) (fun i hi y ↦
      (nv_norm_iteratedFDeriv_dir_top_le _ (he j) hψ i y).trans (hM (i + 1) (by omega) y)) y
  have hb2 : ∀ j k : Fin d, ∀ y,
      |nv_Q p (nv_dir (Pi.single j 1) (nv_dir (Pi.single k 1) (radialBump d))) y|
      ≤ nv_K d N Mw M / (1 + cellFreqNorm p) ^ N := fun j k y ↦
    hQ (nv_contDiff_of_top (nv_contDiff_dir (nv_contDiff_dir hψ _) _) N) (fun i hi y ↦
      ((nv_norm_iteratedFDeriv_dir_top_le _ (he j) (nv_contDiff_dir hψ _) i y).trans
        ((nv_norm_iteratedFDeriv_dir_top_le _ (he k) hψ (i + 1) y).trans
          (hM (i + 1 + 1) (by omega) y)))) y
  have hshift : iteratedFDeriv ℝ i (fun x ↦ cellKernelCoeff c x p) x
      = iteratedFDeriv ℝ i (nv_Q p (radialBump d)) (x - c) := by
    have : (fun x ↦ cellKernelCoeff c x p) = fun x ↦ nv_Q p (radialBump d) (x - c) := by
      funext x; exact cellKernelCoeff_eq_nv_Q c x p
    rw [this, iteratedFDeriv_comp_sub]
  rw [hshift]
  set T : ℝ := nv_K d N Mw M / (1 + cellFreqNorm p) ^ N with hT
  have hT0 : 0 ≤ T := div_nonneg hK hD.le
  have hCT : (1 + d + d ^ 2) * nv_K d N Mw M / (1 + cellFreqNorm p) ^ N
      = (1 + d + d ^ 2) * T := by rw [hT]; ring
  rw [hCT]
  have hsq : 0 ≤ (d : ℝ) ^ 2 := sq_nonneg _
  interval_cases i
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    have := hQ (nv_contDiff_of_top radialBump_contDiff N) (fun i hi y ↦ hM i (by omega) y) (x - c)
    refine this.trans ?_
    nlinarith only [hT0, hd, hsq]
  · rw [norm_iteratedFDeriv_one]
    refine (nv_norm_fderiv_Q_le p hb1 _).trans ?_
    nlinarith only [hT0, hd, hsq]
  · refine (nv_norm_iteratedFDeriv_two_Q_le p hb2 _).trans ?_
    nlinarith only [hT0, hd, hsq]

/-! ## Support -/

/-- The coefficient of the cell centred at `c` vanishes unless `|x i - c i| < 1` for all `i`. -/
theorem cellKernelCoeff_eq_zero_of_one_le_abs_sub {c x : Vec d} {i : Fin d}
    (h : 1 ≤ |x i - c i|) (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) : cellKernelCoeff c x p = 0 := by
  unfold cellKernelCoeff cellCoeff
  have hz : (fun u ↦ cellTrig p u * (cellWeight d u * radialBump d (x - c - u)))
      = fun _ ↦ (0 : ℝ) := by
    funext u
    by_cases hw : cellWeight d u = 0
    · rw [hw, zero_mul, mul_zero]
    by_cases hψ : radialBump d (x - c - u) = 0
    · rw [hψ, mul_zero, mul_zero]
    exfalso
    have h1 := abs_lt_half_of_cellWeight_ne_zero hw i
    have h2 := abs_lt_half_of_radialBump_ne_zero hψ i
    have h3 : x i - c i = (x - c - u) i + u i := by simp
    have h4 : |x i - c i| ≤ |(x - c - u) i| + |u i| := by
      rw [h3]; exact abs_add_le _ _
    linarith only [h, h1, h2, h4]
  rw [hz]
  simp

/-- The set of points `x` at which some coordinate of `x - c` is beyond `1` is open. -/
theorem nv_isOpen_far (c : Vec d) : IsOpen {x : Vec d | ∃ i, 1 < |x i - c i|} := by
  have : {x : Vec d | ∃ i, 1 < |x i - c i|} = ⋃ i, {x : Vec d | 1 < |x i - c i|} := by
    ext x; simp
  rw [this]
  exact isOpen_iUnion fun i ↦
    isOpen_lt continuous_const
      (continuous_abs.comp ((continuous_apply i).sub continuous_const))

/-- All `x`-derivatives of the coefficient vanish on the open set where some coordinate of
`x - c` exceeds `1` in absolute value. -/
theorem iteratedFDeriv_cellKernelCoeff_eq_zero {c x : Vec d} (hx : ∃ i, 1 < |x i - c i|)
    (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x ↦ cellKernelCoeff c x p) x = 0 := by
  have hev : (fun x ↦ cellKernelCoeff c x p) =ᶠ[nhds x] fun _ ↦ (0 : ℝ) :=
    Filter.eventually_of_mem ((nv_isOpen_far c).mem_nhds hx) fun y hy ↦ by
      obtain ⟨i, hi⟩ := hy
      exact cellKernelCoeff_eq_zero_of_one_le_abs_sub hi.le p
  have := Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℝ) (s := Set.univ)
    (f₁ := fun x ↦ cellKernelCoeff c x p) (f := fun _ ↦ (0 : ℝ)) (x := x)
    (by rwa [nhdsWithin_univ]) hev.eq_of_nhds n
  simpa only [iteratedFDerivWithin_univ, iteratedFDeriv_fun_zero, Pi.zero_apply] using this

/-! ## Counting the cells that matter at a point -/

/-- The cells `k / 2` that can contribute at `x`: in each coordinate, the four integers
`⌊2 x i⌋ - 1, …, ⌊2 x i⌋ + 2`. -/
def cellsNear (x : Vec d) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i ↦ Finset.Icc (⌊2 * x i⌋ - 1) (⌊2 * x i⌋ + 2)

theorem card_cellsNear (x : Vec d) : (cellsNear x).card = 4 ^ d := by
  unfold cellsNear
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc]
  have : ∀ i : Fin d, (⌊2 * x i⌋ + 2 + 1 - (⌊2 * x i⌋ - 1)).toNat = 4 := fun i ↦ by omega
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Locality in the cell index.** The coefficient of the cell `k / 2` vanishes at `x` unless `k`
lies in the set `cellsNear x` of at most `4 ^ d` elements. -/
theorem cellKernelCoeff_eq_zero_of_not_mem_cellsNear {x : Vec d} {k : Fin d → ℤ}
    (hk : k ∉ cellsNear x) (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) :
    cellKernelCoeff (fun i ↦ (k i : ℝ) / 2) x p = 0 := by
  by_contra hne
  refine hk (Fintype.mem_piFinset.2 fun i ↦ ?_)
  have hlt : |x i - (k i : ℝ) / 2| < 1 :=
    lt_of_not_ge fun h ↦ hne (cellKernelCoeff_eq_zero_of_one_le_abs_sub (i := i) h p)
  have h2 := abs_lt.1 hlt
  have f0 := Int.floor_le (2 * x i)
  have f1 := Int.lt_floor_add_one (2 * x i)
  rw [Finset.mem_Icc]
  constructor
  · have : ((⌊2 * x i⌋ : ℤ) : ℝ) - 2 < (k i : ℝ) := by linarith only [h2.2, f0]
    have h3 : ((⌊2 * x i⌋ - 2 : ℤ) : ℝ) < (k i : ℝ) := by push_cast; exact this
    have := Int.cast_lt.1 h3
    omega
  · have : (k i : ℝ) < ((⌊2 * x i⌋ : ℤ) : ℝ) + 3 := by linarith only [h2.1, f1]
    have h3 : (k i : ℝ) < ((⌊2 * x i⌋ + 3 : ℤ) : ℝ) := by push_cast; exact this
    have := Int.cast_lt.1 h3
    omega

/-! ## Summability over the frame index -/

theorem nv_summable_int_sq : Summable fun n : ℤ ↦ (((1 : ℝ) + |(n : ℝ)|) ^ 2)⁻¹ := by
  have h : Summable fun n : ℕ ↦ (((1 : ℝ) + |((n : ℤ) : ℝ)|) ^ 2)⁻¹ := by
    have h2 : Summable fun n : ℕ ↦ (((n : ℝ)) ^ 2)⁻¹ := Real.summable_nat_pow_inv.2 (by norm_num)
    have := (summable_nat_add_iff 1).2 h2
    refine this.congr fun n ↦ ?_
    simp only [Nat.cast_add, Nat.cast_one, Int.cast_natCast, Nat.abs_cast]
    rw [add_comm]
  refine Summable.of_nat_of_neg h ?_
  refine h.congr fun n ↦ ?_
  simp

theorem nv_summable_prod {f : ℤ → ℝ} (hf0 : ∀ n, 0 ≤ f n) (hf : Summable f) :
    ∀ n : ℕ, Summable fun m : Fin n → ℤ ↦ ∏ i, f (m i)
  | 0 => Summable.of_finite
  | n + 1 => by
    have ih := nv_summable_prod hf0 hf n
    have hm := hf.mul_of_nonneg ih hf0 fun m ↦ Finset.prod_nonneg fun i _ ↦ hf0 _
    refine ((Fin.consEquiv (fun _ : Fin (n + 1) ↦ ℤ)).summable_iff
      (f := fun m : Fin (n + 1) → ℤ ↦ ∏ i, f (m i))).1 ?_
    refine hm.congr fun q ↦ ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ]

theorem nv_summable_inv_pow : Summable fun m : Fin d → ℤ ↦
    ((1 + ∑ i, |((m i : ℤ) : ℝ)|) ^ (2 * d))⁻¹ := by
  refine Summable.of_nonneg_of_le (fun m ↦ ?_) (fun m ↦ ?_)
    (nv_summable_prod (f := fun n : ℤ ↦ (((1 : ℝ) + |(n : ℝ)|) ^ 2)⁻¹)
      (fun n ↦ by positivity) nv_summable_int_sq d)
  · positivity
  · have hS : 0 ≤ ∑ i, |((m i : ℤ) : ℝ)| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hle : ∏ i, ((1 : ℝ) + |((m i : ℤ) : ℝ)|) ^ 2 ≤ (1 + ∑ i, |((m i : ℤ) : ℝ)|) ^ (2 * d) := by
      calc ∏ i, ((1 : ℝ) + |((m i : ℤ) : ℝ)|) ^ 2
          ≤ ∏ _i : Fin d, (1 + ∑ i, |((m i : ℤ) : ℝ)|) ^ 2 := by
            refine Finset.prod_le_prod₀ (fun i _ ↦ by positivity) fun i _ ↦ ?_
            refine pow_le_pow_left₀ (by positivity) ?_ 2
            have := Finset.single_le_sum (f := fun i ↦ |((m i : ℤ) : ℝ)|)
              (fun i _ ↦ abs_nonneg _) (Finset.mem_univ i)
            linarith only [this]
        _ = (1 + ∑ i, |((m i : ℤ) : ℝ)|) ^ (2 * d) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
    have hpos : 0 < ∏ i, ((1 : ℝ) + |((m i : ℤ) : ℝ)|) ^ 2 :=
      Finset.prod_pos fun i _ ↦ by positivity
    rw [Finset.prod_inv_distrib]
    exact inv_anti₀ hpos hle

/-- **Summable domination over the frame index, uniform in the cell and the point.** For `i ≤ 2`
there is a summable sequence `b` on the frame index with
`‖iteratedFDeriv ℝ i (fun x ↦ cellKernelCoeff c x p) x‖ ≤ b p` for all `c`, `x`, `p`. -/
theorem exists_summable_bound_iteratedFDeriv_cellKernelCoeff :
    ∃ b : ((Fin d → ℤ) ⊕ (Fin d → ℤ)) → ℝ, Summable b ∧ (∀ p, 0 ≤ b p) ∧
      ∀ (c x : Vec d) (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)), ∀ i ≤ 2,
        ‖iteratedFDeriv ℝ i (fun x ↦ cellKernelCoeff c x p) x‖ ≤ b p := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_iteratedFDeriv_cellKernelCoeff_le (d := d) (2 * d)
  refine ⟨fun p ↦ C / (1 + cellFreqNorm p) ^ (2 * d), ?_, fun p ↦ ?_, hC⟩
  · have hs : Summable fun m : Fin d → ℤ ↦ C / (1 + ∑ i, |((m i : ℤ) : ℝ)|) ^ (2 * d) := by
      simpa only [div_eq_mul_inv] using (nv_summable_inv_pow (d := d)).mul_left C
    exact (hs.hasSum.sum (f := fun p : (Fin d → ℤ) ⊕ (Fin d → ℤ) ↦
      C / (1 + cellFreqNorm p) ^ (2 * d)) hs.hasSum).summable
  · exact div_nonneg hC0 (pow_nonneg (by linarith only [cellFreqNorm_nonneg p]) _)

/-! ## Satisfiability witness -/

/-- For `d = 2` the estimate is not vacuous: the decay holds with `N = 4`, and some coefficient of
the kernel at the origin is nonzero. -/
example : (∃ C : ℝ, 0 ≤ C ∧ ∀ (c x : Vec 2) (p : (Fin 2 → ℤ) ⊕ (Fin 2 → ℤ)), ∀ i ≤ 2,
      ‖iteratedFDeriv ℝ i (fun x ↦ cellKernelCoeff c x p) x‖ ≤ C / (1 + cellFreqNorm p) ^ 4) ∧
    ∃ p : (Fin 2 → ℤ) ⊕ (Fin 2 → ℤ), cellKernelCoeff (0 : Vec 2) 0 p ≠ 0 := by
  refine ⟨exists_norm_iteratedFDeriv_cellKernelCoeff_le 4, ?_⟩
  by_contra hall
  push Not at hall
  have h := hasSum_cellKernelCoeff_mul (0 : Vec 2) 0 0
  have h0 : HasSum (fun p : (Fin 2 → ℤ) ⊕ (Fin 2 → ℤ) ↦
      cellKernelCoeff (0 : Vec 2) 0 p * cellKernelCoeff 0 0 p) 0 := by
    simpa only [hall, mul_zero] using hasSum_zero
  have := h.unique h0
  have hpos := cellKernel_integral_pos (0 : Vec 2)
  simp only [zero_sub] at this hpos
  linarith only [this, hpos]

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
