/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DecayEstimateE
public import SuperdiffusionCLT.Section7.Root.HolderBallCubeD

@[expose] public section

open MeasureTheory Homogenization SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- The normalised `L²` norm of `f` over `S`, as a real number. -/
noncomputable def linfL2b_nl2 (S : Set (Vec d)) (f : Vec d → ℝ) : ℝ :=
  Real.sqrt ((∫ x in S, f x ^ 2) / (volume S).toReal)

theorem linfL2b_nl2_nonneg (S : Set (Vec d)) (f : Vec d → ℝ) : 0 ≤ linfL2b_nl2 S f :=
  Real.sqrt_nonneg _

theorem linfL2b_nl2_sq {S : Set (Vec d)} (hv : 0 < (volume S).toReal) (f : Vec d → ℝ) :
    (volume S).toReal * linfL2b_nl2 S f ^ 2 = ∫ x in S, f x ^ 2 := by
  unfold linfL2b_nl2
  rw [Real.sq_sqrt (div_nonneg (integral_nonneg fun x => sq_nonneg _) hv.le)]
  field_simp

theorem linfL2b_lpBar_eq {S : Set (Vec d)} (hS : volume S ≠ ⊤) (hv : 0 < (volume S).toReal)
    {F : Vec d → ℝ} (hF : MemLp F 2 (volume.restrict S)) :
    lpBar S 2 F = ENNReal.ofReal (linfL2b_nl2 S F) :=
  decayEst_lpBar_real hS hv hF

/-- Monotonicity in the set, with the volume ratio. -/
theorem linfL2b_nl2_mono {A S : Set (Vec d)} (hAS : A ⊆ S) (hS : volume S ≠ ⊤)
    (hv : 0 < (volume A).toReal) {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict S)) :
    linfL2b_nl2 A f ≤ Real.sqrt ((volume S).toReal / (volume A).toReal) * linfL2b_nl2 S f := by
  have hvS : 0 < (volume S).toReal := lt_of_lt_of_le hv (ENNReal.toReal_mono hS (measure_mono hAS))
  have h := h1_integral_sq_mono hAS hf hS 0
  simp only [sub_zero] at h
  unfold linfL2b_nl2
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_iff₀ hv]
  have e : (volume S).toReal / (volume A).toReal * ((∫ x in S, f x ^ 2) / (volume S).toReal) *
      (volume A).toReal = ∫ x in S, f x ^ 2 := by
    field_simp
  rw [e]; exact h

theorem linfL2b_nl2_sq_eq {A : Set (Vec d)} (hA : volume A ≠ ⊤) (hv : 0 < (volume A).toReal)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict A)) :
    linfL2b_nl2 A u ^ 2 = h1_l2 A u ^ 2 + h1_avg A u ^ 2 := by
  have h := h1_var_eq hu hA hv 0
  simp only [sub_zero] at h
  have h1 := linfL2b_nl2_sq hv u
  have h2 := h1_l2_sq (u := u) hv
  have : (volume A).toReal * linfL2b_nl2 A u ^ 2 =
      (volume A).toReal * (h1_l2 A u ^ 2 + h1_avg A u ^ 2) := by
    rw [h1, h, ← h2]; ring
  exact mul_left_cancel₀ hv.ne' this

theorem linfL2b_avg_abs_le {A : Set (Vec d)} (hA : volume A ≠ ⊤) (hv : 0 < (volume A).toReal)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict A)) :
    |h1_avg A u| ≤ linfL2b_nl2 A u := by
  have hsq : h1_avg A u ^ 2 ≤ linfL2b_nl2 A u ^ 2 := by
    rw [linfL2b_nl2_sq_eq hA hv hu]; nlinarith only [sq_nonneg (h1_l2 A u)]
  exact abs_le.2 (abs_le_of_sq_le_sq' hsq (linfL2b_nl2_nonneg _ _))

theorem linfL2b_nl2_le_add {A : Set (Vec d)} (hA : volume A ≠ ⊤) (hv : 0 < (volume A).toReal)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict A)) :
    linfL2b_nl2 A u ≤ h1_l2 A u + |h1_avg A u| := by
  have h := linfL2b_nl2_sq_eq hA hv hu
  have h1 : 0 ≤ h1_l2 A u := Real.sqrt_nonneg _
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  rw [h, ← sq_abs (h1_avg A u)]
  nlinarith only [h1, abs_nonneg (h1_avg A u)]

/-! ### Euclidean geometry -/

theorem linfL2b_vecDot_le (x y : Vec d) : vecDot x y ≤ eucNorm x * eucNorm y := by
  have h := sq_vecDot_le_vecNormSq_mul_vecNormSq x y
  have e : (eucNorm x * eucNorm y) ^ 2 = vecNormSq x * vecNormSq y := by
    rw [mul_pow, eucNorm_sq, eucNorm_sq]
  have h' : vecDot x y ^ 2 ≤ (eucNorm x * eucNorm y) ^ 2 := by rw [e]; exact h
  exact (abs_le_of_sq_le_sq' h' (mul_nonneg (eucNorm_nonneg x) (eucNorm_nonneg y))).2

theorem linfL2b_euc_add (x y : Vec d) : eucNorm (x + y) ≤ eucNorm x + eucNorm y := by
  have hexp : vecNormSq (x + y) = vecNormSq x + 2 * vecDot x y + vecNormSq y := by
    unfold vecNormSq vecDot
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]
    ring
  have h1 := linfL2b_vecDot_le x y
  have hx := eucNorm_sq x
  have hy := eucNorm_sq y
  have hxy := eucNorm_sq (x + y)
  have h0 := eucNorm_nonneg x
  have h0' := eucNorm_nonneg y
  have : eucNorm (x + y) ^ 2 ≤ (eucNorm x + eucNorm y) ^ 2 := by
    rw [hxy, hexp, ← hx, ← hy]; nlinarith only [h1]
  exact (abs_le_of_sq_le_sq' this (by positivity)).2

theorem linfL2b_euc_smul (c : ℝ) (x : Vec d) : eucNorm (c • x) = |c| * eucNorm x := by
  unfold eucNorm
  rw [vecNormSq_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem linfL2b_norm_le_euc (z : Vec d) : ‖z‖ ≤ eucNorm z := by
  refine (pi_norm_le_iff_of_nonneg (eucNorm_nonneg z)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  refine Real.abs_le_sqrt ?_
  unfold vecNormSq vecDot
  have := Finset.single_le_sum (f := fun j => z j * z j) (fun j _ => mul_self_nonneg (z j))
    (Finset.mem_univ i)
  simpa [sq] using this

theorem linfL2b_euc_le_norm (z : Vec d) : eucNorm z ≤ Real.sqrt d * ‖z‖ := by
  have h := h1_vecNormSq_le (z := z) (τ := ‖z‖) (fun i => by
    have := norm_le_pi_norm z i
    rwa [Real.norm_eq_abs] at this)
  unfold eucNorm
  calc Real.sqrt (vecNormSq z) ≤ Real.sqrt (d * ‖z‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt d * ‖z‖ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (norm_nonneg z)]

theorem linfL2b_mem_euclidBall {r : ℝ} (hr : 0 < r) {x : Vec d} :
    x ∈ euclidBall (d := d) r ↔ eucNorm x < r := by
  rw [mem_euclidBall]
  unfold eucNorm
  exact (Real.sqrt_lt' hr).symm

/-! ### Lattice cells -/

/-- The telescoping of averages along an increasing chain of sets. -/
theorem linfL2b_chain_abs {T : ℕ → Set (Vec d)} {u : Vec d → ℝ} {θ : ℕ → ℝ} {K : ℝ}
    (hmono : ∀ t, T t ⊆ T (t + 1)) (hfin : ∀ t, volume (T t) ≠ ⊤)
    (hpos : ∀ t, 0 < (volume (T t)).toReal)
    (hL2 : ∀ t, MemLp u 2 (volume.restrict (T t)))
    (hK : ∀ t, (volume (T (t + 1))).toReal ≤ K * (volume (T t)).toReal) {N : ℕ}
    (hosc : ∀ t, t < N → h1_l2 (T (t + 1)) u ≤ θ t) :
    ∀ t, t ≤ N → |h1_avg (T 0) u - h1_avg (T t) u| ≤
      Real.sqrt K * ∑ s ∈ Finset.range t, θ s := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have ih' := ih (by omega)
    have hstep := h1_avg_sub_le (hmono t) (hL2 (t + 1)) (hfin (t + 1)) (hpos t)
    have hr : Real.sqrt ((volume (T (t + 1))).toReal / (volume (T t)).toReal) ≤ Real.sqrt K := by
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_iff₀ (hpos t)]; exact hK t
    have hl : 0 ≤ h1_l2 (T (t + 1)) u := Real.sqrt_nonneg _
    have hθ := hosc t (by omega)
    have h3 : |h1_avg (T t) u - h1_avg (T (t + 1)) u| ≤ Real.sqrt K * θ t := by
      calc _ ≤ Real.sqrt ((volume (T (t + 1))).toReal / (volume (T t)).toReal) *
            h1_l2 (T (t + 1)) u := hstep
        _ ≤ Real.sqrt K * θ t := mul_le_mul hr hθ hl (Real.sqrt_nonneg _)
    rw [Finset.sum_range_succ, mul_add]
    calc |h1_avg (T 0) u - h1_avg (T (t + 1)) u|
        = |(h1_avg (T 0) u - h1_avg (T t) u) + (h1_avg (T t) u - h1_avg (T (t + 1)) u)| := by
          ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add ih' h3)

theorem linfL2b_geom_sum (t : ℕ) : ∑ s ∈ Finset.range t, (3 : ℝ) ^ s ≤ (3 : ℝ) ^ t / 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith only [ih]

theorem linfL2b_eLpNorm_two_eq {μ : Measure (Vec d)} {f : Vec d → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, f x ^ 2 ∂μ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have hint : ∫ x, ‖f x‖ ^ (2 : ℝ≥0∞).toReal ∂μ = ∫ x, f x ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat]
    rw [Real.rpow_two, sq_abs]
  rw [hint]
  congr 1
  simp only [ENNReal.toReal_ofNat]
  rw [Real.sqrt_eq_rpow]
  norm_num

end SuperdiffusionCLT.Section8
