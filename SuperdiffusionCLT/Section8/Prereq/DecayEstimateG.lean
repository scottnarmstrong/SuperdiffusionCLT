/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DecayEstimateF

@[expose] public section

namespace SuperdiffusionCLT.Section8

noncomputable section

/-!
# Chaining of the annular `L^∞` bounds

Real-variable part of the chaining step in the proof of `l.decay.estimate.Linfty`: almost
everywhere oscillation bounds `C₁ s^{-β} T` on the
annuli `V_s = {s/2 < |x| < s}` for `s₀ ≤ s ≤ 2R/3`, and an anchor bound `C₂ R^{-β} T` on
`{R/3 < |x| < R}`, give the bound `C₃ r^{-β} T` on `B_R \ B_r`.  The means of overlapping annuli
are compared at a common point, and the induction over the scales `(3/2)^n` closes because of the
factor `(3/2)^{-β} < 1`.
-/

section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open scoped Pointwise ENNReal

variable {d : ℕ}

theorem decayEst_ann_mono {a b a' b' : ℝ} (ha' : 0 ≤ a') (hb : 0 ≤ b) (h1 : a' ≤ a) (h2 : b ≤ b') :
    decayEst_ann (d := d) a b ⊆ decayEst_ann a' b' := by
  intro x hx
  refine ⟨?_, ?_⟩
  · have := pow_le_pow_left₀ ha' h1 2
    linarith only [hx.1, this]
  · have h3 : b ^ 2 ≤ b' ^ 2 := pow_le_pow_left₀ hb h2 2
    linarith only [hx.2, h3]

theorem decayEst_ann_measure_pos [NeZero d] {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    0 < volume (decayEst_ann (d := d) a b) := by
  have i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  refine (decayEst_ann_isOpen a b).measure_pos volume ⟨((a + b) / 2) • basisVec i0, ?_, ?_⟩
  · rw [vecNormSq_smul, vecNormSq_basisVec, mul_one]
    nlinarith only [ha, hab]
  · rw [vecNormSq_smul, vecNormSq_basisVec, mul_one]
    nlinarith only [ha, hab]

/-- The mean over a set of positive finite measure is bounded by an almost everywhere bound. -/
theorem decayEst_avg_abs_le {V : Set (Vec d)} (hV : volume V ≠ ⊤) (hv : 0 < (volume V).toReal)
    {u : Vec d → ℝ} {M : ℝ} (h : ∀ᵐ x ∂volume.restrict V, |u x| ≤ M) :
    |h1_avg V u| ≤ M := by
  have h1 := norm_setIntegral_le_of_norm_le_const_ae (μ := volume) (f := u) hV.lt_top
    (by simpa only [Real.norm_eq_abs] using h)
  rw [Real.norm_eq_abs] at h1
  unfold h1_avg
  rw [abs_div, abs_of_pos hv, div_le_iff₀ hv]
  simpa [Measure.real, mul_comm] using h1

/-- Means over two overlapping annuli differ by at most the sum of the oscillation bounds. -/
theorem decayEst_avg_overlap [NeZero d] {u : Vec d → ℝ} {s s' M M' : ℝ} (hs : 0 < s)
    (hss' : s ≤ s') (hs'2 : s' ≤ 3 * s / 2)
    (h : ∀ᵐ x ∂volume.restrict (decayEst_ann (d := d) (s / 2) s),
      |u x - h1_avg (decayEst_ann (s / 2) s) u| ≤ M)
    (h' : ∀ᵐ x ∂volume.restrict (decayEst_ann (d := d) (s' / 2) s'),
      |u x - h1_avg (decayEst_ann (s' / 2) s') u| ≤ M') :
    |h1_avg (decayEst_ann (d := d) (s / 2) s) u - h1_avg (decayEst_ann (s' / 2) s') u| ≤ M + M' := by
  set S : Set (Vec d) := decayEst_ann (3 * s / 4) s with hS
  have h1 : S ⊆ decayEst_ann (d := d) (s / 2) s :=
    decayEst_ann_mono (by positivity) hs.le (by linarith only [hs]) le_rfl
  have h2 : S ⊆ decayEst_ann (d := d) (s' / 2) s' :=
    decayEst_ann_mono (by linarith only [hs, hss']) (by linarith only [hs, hss']) (by linarith only [hs'2]) hss'
  have hpos : 0 < volume S := decayEst_ann_measure_pos (by positivity) (by linarith only [hs])
  have hne : (ae (volume.restrict S)).NeBot :=
    ae_neBot.2 (by rw [Ne, Measure.restrict_eq_zero]; exact hpos.ne')
  have hA := ae_restrict_of_ae_restrict_of_subset h1 h
  have hB := ae_restrict_of_ae_restrict_of_subset h2 h'
  obtain ⟨x, hx1, hx2⟩ := (hA.and hB).exists
  have := abs_sub_le (h1_avg (decayEst_ann (d := d) (s / 2) s) u) (u x)
    (h1_avg (decayEst_ann (s' / 2) s') u)
  rw [abs_sub_comm (h1_avg (decayEst_ann (d := d) (s / 2) s) u) (u x)] at this
  linarith only [this, hx1, hx2]


theorem decayEst_ann_vol_ne_top {a b : ℝ} (hb : 0 < b) :
    volume (decayEst_ann (d := d) a b) ≠ ⊤ :=
  ne_top_of_le_ne_top (volume_euclidBall_ne_top hb) (measure_mono (decayEst_ann_subset _ _))

theorem decayEst_ann_volT_pos [NeZero d] {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    0 < (volume (decayEst_ann (d := d) a b)).toReal :=
  ENNReal.toReal_pos (decayEst_ann_measure_pos ha hab).ne'
    (decayEst_ann_vol_ne_top (lt_of_le_of_lt ha hab))

theorem decayEst_scale_rpow {β t : ℝ} (ht : 0 < t) :
    (3 * t / 2) ^ (-β) = (3 / 2 : ℝ) ^ (-β) * t ^ (-β) := by
  rw [show 3 * t / 2 = 3 / 2 * t by ring, Real.mul_rpow (by norm_num) ht.le]

/-- **The chain.** -/
theorem decayEst_chain [NeZero d] {u : Vec d → ℝ} {R r s₀ β T C₁ C₂ : ℝ} (hβ : 0 < β)
    (hT : 0 ≤ T) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hr : 0 < r) (hrR : r ≤ R)
    (hs₀pos : 0 < s₀) (hs₀ : s₀ ≤ 7 * r / 4)
    (hosc : ∀ s : ℝ, s₀ ≤ s → s ≤ 2 * R / 3 →
      ∀ᵐ x ∂volume.restrict (decayEst_ann (d := d) (s / 2) s),
        |u x - h1_avg (decayEst_ann (s / 2) s) u| ≤ C₁ * s ^ (-β) * T)
    (hanch : ∀ᵐ x ∂volume.restrict (decayEst_ann (d := d) (R / 3) R),
      |u x| ≤ C₂ * R ^ (-β) * T) :
    ∀ᵐ x ∂volume.restrict (euclidBall (d := d) R \ euclidBall r),
      |u x| ≤ (C₂ + C₁ + (C₂ + 2 * C₁ + 2 * C₁ / (1 - (3 / 2 : ℝ) ^ (-β)))) * r ^ (-β) * T := by
  set q : ℝ := (3 / 2 : ℝ) ^ (-β) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hβ])
  set A : ℝ := C₂ + 2 * C₁ + 2 * C₁ / (1 - q) with hA
  have hRpos : 0 < R := lt_of_lt_of_le hr hrR
  have hAnn : 0 ≤ 2 * C₁ / (1 - q) := by
    have : 0 < 1 - q := by linarith only [hq1]
    positivity
  have hAA : C₂ + 2 * C₁ ≤ A := by linarith only [hA, hAnn]
  have hA0 : 0 ≤ A := by linarith only [hAA, hC₁, hC₂]
  have hAq : C₁ * (1 + q) ≤ A * (1 - q) := by
    have hne : (1 - q) ≠ 0 := (sub_pos.2 hq1).ne'
    have h1 : 2 * C₁ / (1 - q) * (1 - q) = 2 * C₁ := by field_simp
    have h2 : A * (1 - q) = (C₂ + 2 * C₁) * (1 - q) + 2 * C₁ := by
      rw [hA, add_mul, h1]
    nlinarith only [h2, hC₁, hC₂, hq1, hq0]
  -- the mean on an annulus
  set P : ℝ → Prop := fun s => |h1_avg (decayEst_ann (d := d) (s / 2) s) u| ≤ A * s ^ (-β) * T
    with hP
  -- the base
  have hbase : |h1_avg (decayEst_ann (d := d) ((2 * R / 3) / 2) (2 * R / 3)) u| ≤
      C₂ * R ^ (-β) * T := by
    have hsub : decayEst_ann (d := d) ((2 * R / 3) / 2) (2 * R / 3) ⊆ decayEst_ann (R / 3) R :=
      decayEst_ann_mono (by positivity) (by positivity) (by linarith only []) (by linarith only [hRpos])
    exact decayEst_avg_abs_le (decayEst_ann_vol_ne_top (by positivity))
      (decayEst_ann_volT_pos (by positivity) (by linarith only [hRpos]))
      (ae_restrict_of_ae_restrict_of_subset hsub hanch)
  have hdirect : ∀ s : ℝ, s₀ ≤ s → 4 * R / 9 ≤ s → s ≤ 2 * R / 3 → P s := by
    intro s hs0 hs1 hs2
    have hspos : 0 < s := lt_of_lt_of_le hs₀pos hs0
    have hov := decayEst_avg_overlap (u := u) hspos hs2 (by linarith only [hs1])
      (hosc s hs0 hs2) (hosc (2 * R / 3) (hs0.trans hs2) le_rfl)
    have hs'pos : 0 < 2 * R / 3 := by positivity
    have e1 : R ^ (-β) ≤ s ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos hspos (by linarith only [hs2, hRpos]) (by linarith only [hβ])
    have e2 : (2 * R / 3) ^ (-β) ≤ s ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos hspos hs2 (by linarith only [hβ])
    have h3 := abs_add_le (h1_avg (decayEst_ann (d := d) ((2 * R / 3) / 2) (2 * R / 3)) u)
      (h1_avg (decayEst_ann (d := d) (s / 2) s) u -
        h1_avg (decayEst_ann (d := d) ((2 * R / 3) / 2) (2 * R / 3)) u)
    rw [add_sub_cancel] at h3
    have h4 : C₂ * R ^ (-β) * T ≤ C₂ * s ^ (-β) * T := by gcongr
    have h5 : C₁ * (2 * R / 3) ^ (-β) * T ≤ C₁ * s ^ (-β) * T := by gcongr
    have h6 : (C₂ + 2 * C₁) * s ^ (-β) * T ≤ A * s ^ (-β) * T := by
      have : 0 ≤ s ^ (-β) * T := by positivity
      nlinarith only [hAA, this]
    show |h1_avg (decayEst_ann (d := d) (s / 2) s) u| ≤ A * s ^ (-β) * T
    linarith only [h3, hbase, hov, h4, h5, h6]
  have hstep : ∀ s : ℝ, s₀ ≤ s → 3 * s / 2 ≤ 2 * R / 3 → P (3 * s / 2) → P s := by
    intro s hs0 hs1 hP'
    have hspos : 0 < s := lt_of_lt_of_le hs₀pos hs0
    have hs2 : s ≤ 2 * R / 3 := by linarith only [hs1, hspos]
    have hov := decayEst_avg_overlap (u := u) hspos (by linarith only [hspos]) le_rfl
      (hosc s hs0 hs2) (hosc (3 * s / 2) (by linarith only [hs0, hspos]) hs1)
    have h3 := abs_add_le (h1_avg (decayEst_ann (d := d) ((3 * s / 2) / 2) (3 * s / 2)) u)
      (h1_avg (decayEst_ann (d := d) (s / 2) s) u -
        h1_avg (decayEst_ann (d := d) ((3 * s / 2) / 2) (3 * s / 2)) u)
    rw [add_sub_cancel] at h3
    have hsc := decayEst_scale_rpow (β := β) hspos
    have hpos : 0 ≤ s ^ (-β) * T := by positivity
    have hP'' : |h1_avg (decayEst_ann (d := d) ((3 * s / 2) / 2) (3 * s / 2)) u| ≤
        A * q * (s ^ (-β) * T) := by
      have := hP'
      simp only [hP] at this
      rw [hsc] at this
      linarith only [this]
    have hov' : |h1_avg (decayEst_ann (d := d) (s / 2) s) u -
        h1_avg (decayEst_ann (d := d) ((3 * s / 2) / 2) (3 * s / 2)) u| ≤
        C₁ * (1 + q) * (s ^ (-β) * T) := by
      have := hov
      rw [hsc] at this
      linarith only [this]
    have h7 : A * q * (s ^ (-β) * T) + C₁ * (1 + q) * (s ^ (-β) * T) ≤ A * (s ^ (-β) * T) := by
      nlinarith only [hAq, hpos]
    show |h1_avg (decayEst_ann (d := d) (s / 2) s) u| ≤ A * s ^ (-β) * T
    linarith only [h3, hP'', hov', h7]
  have hQ : ∀ n : ℕ, ∀ s : ℝ, s₀ ≤ s → s ≤ 2 * R / 3 → 2 * R / 3 ≤ (3 / 2 : ℝ) ^ n * s → P s := by
    intro n
    induction n with
    | zero =>
      intro s hs0 hs1 hs2
      rw [pow_zero, one_mul] at hs2
      exact hdirect s hs0 (by linarith only [hs2, hRpos]) hs1
    | succ n ih =>
      intro s hs0 hs1 hs2
      by_cases hs4 : 4 * R / 9 ≤ s
      · exact hdirect s hs0 hs4 hs1
      · have hspos : 0 < s := lt_of_lt_of_le hs₀pos hs0
        push Not at hs4
        refine hstep s hs0 (by linarith only [hs4]) (ih (3 * s / 2)
          (by linarith only [hs0, hspos]) (by linarith only [hs4]) ?_)
        rw [pow_succ] at hs2
        linarith only [hs2]
  -- the final covering
  set C₃ : ℝ := C₂ + C₁ + A with hC₃
  set D : Set (Vec d) := euclidBall (d := d) R \ euclidBall r with hD
  have hrneg : r ^ (-β) ≥ R ^ (-β) :=
    Real.rpow_le_rpow_of_nonpos hr hrR (by linarith only [hβ])
  have hr0 : 0 ≤ r ^ (-β) * T := by positivity
  set D1 : Set (Vec d) := D ∩ {x | (R / 3) ^ 2 < vecNormSq x} with hD1
  set D2 : Set (Vec d) := D ∩ {x | ¬ (R / 3) ^ 2 < vecNormSq x} with hD2
  have hDsplit : D = D1 ∪ D2 := by
    ext x
    simp only [hD1, hD2, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  rw [hDsplit, ae_restrict_union_iff]
  refine ⟨?_, ?_⟩
  · have hsub : D1 ⊆ decayEst_ann (d := d) (R / 3) R := fun x hx => ⟨hx.2, hx.1.1⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hanch] with x hx
    have h1 : C₂ * R ^ (-β) * T ≤ C₂ * r ^ (-β) * T := by gcongr
    have h2 : C₂ * r ^ (-β) * T ≤ C₃ * r ^ (-β) * T := by
      nlinarith only [hC₃, hA0, hC₁, hr0]
    linarith only [hx, h1, h2]
  · -- the covering of the inner part
    set sn : ℕ → ℝ := fun n => 7 * r * (3 / 2 : ℝ) ^ n / 4 with hsn
    set E : ℕ → Set (Vec d) := fun n => D2 ∩ decayEst_ann (sn n / 2) (sn n) with hE
    have hcov : D2 ⊆ ⋃ n, E n := by
      intro x hx
      have hxr : r ^ 2 ≤ vecNormSq x := not_lt.1 hx.1.2
      set e : ℝ := Real.sqrt (vecNormSq x) with he
      have he2 : e ^ 2 = vecNormSq x := Real.sq_sqrt (vecNormSq_nonneg x)
      have hre : r ≤ e := (Real.le_sqrt' hr).2 hxr
      obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := e / r) (y := (3 / 2 : ℝ))
        (by rw [le_div_iff₀ hr]; linarith only [hre]) (by norm_num)
      have hpn : (0 : ℝ) < (3 / 2 : ℝ) ^ n := by positivity
      have hn1' : (3 / 2 : ℝ) ^ n * r ≤ e := by
        rwa [le_div_iff₀ hr] at hn1
      have hn2' : e < (3 / 2 : ℝ) ^ (n + 1) * r := by
        rwa [div_lt_iff₀ hr] at hn2
      rw [pow_succ] at hn2'
      refine Set.mem_iUnion.2 ⟨n, hx, ?_, ?_⟩
      · show (sn n / 2) ^ 2 < vecNormSq x
        rw [← he2]
        have : sn n / 2 < e := by
          have : 0 < (3 / 2 : ℝ) ^ n * r := by positivity
          simp only [hsn]
          nlinarith only [hn1', this]
        exact pow_lt_pow_left₀ this (by simp only [hsn]; positivity) (by norm_num)
      · show vecNormSq x < sn n ^ 2
        rw [← he2]
        have : e < sn n := by
          have : 0 < (3 / 2 : ℝ) ^ n * r := by positivity
          simp only [hsn]
          nlinarith only [hn2', this]
        exact pow_lt_pow_left₀ this (by positivity) (by norm_num)
    have hall : ∀ n : ℕ, ∀ᵐ x ∂volume.restrict (E n), |u x| ≤ C₃ * r ^ (-β) * T := by
      intro n
      have hsn_ge : 7 * r / 4 ≤ sn n := by
        simp only [hsn]
        have : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
        nlinarith only [this, hr]
      have hsnpos : 0 < sn n := by linarith only [hsn_ge, hr]
      by_cases hn : sn n ≤ 2 * R / 3
      · have hos := hosc (sn n) (hs₀.trans hsn_ge) hn
        have hsub : E n ⊆ decayEst_ann (d := d) (sn n / 2) (sn n) := fun x hx => hx.2
        obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (2 * R / 3 / sn n) (by norm_num : (1 : ℝ) < 3 / 2)
        have hPm : P (sn n) := hQ m (sn n) (hs₀.trans hsn_ge) hn (by
          rw [div_lt_iff₀ hsnpos] at hm
          linarith only [hm])
        have hrs : sn n ^ (-β) ≤ r ^ (-β) :=
          Real.rpow_le_rpow_of_nonpos hr (by linarith only [hsn_ge, hr]) (by linarith only [hβ])
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hos] with x hx
        have h1 : |u x| ≤ |u x - h1_avg (decayEst_ann (d := d) (sn n / 2) (sn n)) u| +
            |h1_avg (decayEst_ann (d := d) (sn n / 2) (sn n)) u| := by
          have := abs_add_le (u x - h1_avg (decayEst_ann (d := d) (sn n / 2) (sn n)) u)
            (h1_avg (decayEst_ann (d := d) (sn n / 2) (sn n)) u)
          simpa using this
        have h2 : |h1_avg (decayEst_ann (d := d) (sn n / 2) (sn n)) u| ≤
            A * sn n ^ (-β) * T := hPm
        have h3 : (C₁ + A) * sn n ^ (-β) * T ≤ (C₁ + A) * r ^ (-β) * T := by gcongr
        have h4 : (C₁ + A) * r ^ (-β) * T ≤ C₃ * r ^ (-β) * T := by
          nlinarith only [hC₃, hC₂, hr0]
        linarith only [h1, h2, hx, h3, h4]
      · have : E n = ∅ := by
          refine Set.eq_empty_iff_forall_notMem.2 fun x hx => hn ?_
          have h1 : vecNormSq x ≤ (R / 3) ^ 2 := not_lt.1 hx.1.2
          have h2 : (sn n / 2) ^ 2 < vecNormSq x := hx.2.1
          have h3 : (sn n / 2) ^ 2 < (R / 3) ^ 2 := lt_of_lt_of_le h2 h1
          have := lt_of_pow_lt_pow_left₀ 2 (by positivity) h3
          linarith only [this]
        rw [this]
        simp
    have := (ae_restrict_iUnion_iff E _).2 hall
    exact ae_restrict_of_ae_restrict_of_subset hcov this

end

/-!
# Arithmetic of the dual `L²` constant

The constant `K` of the dual `L²` bound, with the Hölder and Poincaré coefficients inserted, is
at most a fixed multiple of `(ρ/a)^{γ + d/2} a b (log)^{-1/2}`.
-/

section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open scoped Pointwise ENNReal

variable {d : ℕ}

theorem decayEst_sqrt_vol_ratio [NeZero d] {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    Real.sqrt ((volume (euclidBall (d := d) ρ)).toReal / (volume (euclidBall (d := d) a)).toReal) =
      (ρ / a) ^ ((d : ℝ) / 2) := by
  have hΩ := decayEst_volT_ball_pos (d := d) one_pos
  have hΩ' := hΩ.ne'
  have ha' := ha.ne'
  rw [decayEst_volT_ball hρ, decayEst_volT_ball ha,
    show ρ ^ d * (volume (euclidBall (d := d) 1)).toReal /
        (a ^ d * (volume (euclidBall (d := d) 1)).toReal) = (ρ / a) ^ d by
      rw [div_pow]; field_simp, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem decayEst_rpow_neg_le {L x : ℝ} (hL : 0 < L) (hx : L ≤ x) (p : ℝ) (hp : 0 ≤ p) :
    x ^ (-p) ≤ L ^ (-p) :=
  Real.rpow_le_rpow_of_nonpos hL hx (by linarith only [hp])


/-- The dual constant is at most a multiple of `(ρ/a)^{γ+d/2} a b Lg^{-1/2}`. -/
theorem decayEst_K_bound [NeZero d] {γ ν cs CH CP ρ aa bb Lg : ℝ} (hν : 0 < ν) (hcs : 0 < cs)
    (hCH : 0 ≤ CH) (hCP : 0 ≤ CP) (hρ : 0 < ρ) (hρa : ρ ≤ aa) (hab : aa ≤ bb) (hLg1 : 1 ≤ Lg)
    (hLg : Lg ≤ Real.log aa) :
    (CH * (ρ / aa) ^ γ) *
        Real.sqrt ((volume (euclidBall (d := d) ρ)).toReal /
          (volume (euclidBall (d := d) aa)).toReal) *
        (CP * aa * cs ^ (-(1 / 4 : ℝ)) * Real.sqrt ν * Real.log aa ^ (-(1 / 4 : ℝ))) *
        ((CP * bb * cs ^ (-(1 / 4 : ℝ)) * Real.sqrt ν * Real.log bb ^ (-(1 / 4 : ℝ))) / ν +
          Real.sqrt ((CP * bb ^ 2 * ν⁻¹ * Real.log bb ^ (-(100 : ℝ))) / ν)) ≤
      (CH * CP * (CP * cs ^ (-(1 / 4 : ℝ)) * Real.sqrt ν / ν + Real.sqrt CP / ν) *
          cs ^ (-(1 / 4 : ℝ)) * Real.sqrt ν) *
        (ρ / aa) ^ (γ + (d : ℝ) / 2) * (aa * bb) * Lg ^ (-(1 / 2 : ℝ)) := by
  have haa : 0 < aa := lt_of_lt_of_le hρ hρa
  have hbb : 0 < bb := lt_of_lt_of_le haa hab
  have hLg0 : 0 < Lg := by linarith only [hLg1]
  have hlogaa : Lg ≤ Real.log bb :=
    hLg.trans (Real.log_le_log haa hab)
  set Λ : ℝ := Lg ^ (-(1 / 4 : ℝ)) with hΛ
  have hΛ0 : 0 ≤ Λ := Real.rpow_nonneg hLg0.le _
  have hΛ2 : Λ * Λ = Lg ^ (-(1 / 2 : ℝ)) := by
    rw [hΛ, ← Real.rpow_add hLg0]
    norm_num
  have e1 : Real.log aa ^ (-(1 / 4 : ℝ)) ≤ Λ := decayEst_rpow_neg_le hLg0 hLg _ (by norm_num)
  have e2 : Real.log bb ^ (-(1 / 4 : ℝ)) ≤ Λ := decayEst_rpow_neg_le hLg0 hlogaa _ (by norm_num)
  have e3 : Real.log bb ^ (-(100 : ℝ)) ≤ Lg ^ (-(1 / 2 : ℝ)) := by
    have h1 := decayEst_rpow_neg_le hLg0 hlogaa 100 (by norm_num)
    have h2 : Lg ^ (-(100 : ℝ)) ≤ Lg ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hLg1 (by norm_num)
    exact h1.trans h2
  set c4 : ℝ := cs ^ (-(1 / 4 : ℝ)) with hc4
  have hc40 : 0 ≤ c4 := Real.rpow_nonneg hcs.le _
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsCP : 0 ≤ Real.sqrt CP := Real.sqrt_nonneg _
  have hθ : (ρ / aa) ^ γ * (ρ / aa) ^ ((d : ℝ) / 2) = (ρ / aa) ^ (γ + (d : ℝ) / 2) :=
    (Real.rpow_add (by positivity) _ _).symm
  rw [decayEst_sqrt_vol_ratio hρ haa]
  have hlogb0 : 0 ≤ Real.log bb ^ (-(100 : ℝ)) := Real.rpow_nonneg (by linarith only [hLg1, hlogaa]) _
  -- the Poincaré factors
  have hA1 : CP * aa * c4 * Real.sqrt ν * Real.log aa ^ (-(1 / 4 : ℝ)) ≤
      CP * aa * c4 * Real.sqrt ν * Λ := by gcongr
  have hbeta : Real.sqrt ((CP * bb ^ 2 * ν⁻¹ * Real.log bb ^ (-(100 : ℝ))) / ν) ≤
      Real.sqrt CP * bb * ν⁻¹ * Λ := by
    have hsq : (Real.sqrt CP * bb * ν⁻¹ * Λ) ^ 2 =
        CP * bb ^ 2 * ν⁻¹ * (ν⁻¹ * Lg ^ (-(1 / 2 : ℝ))) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hCP, sq Λ, hΛ2]
      ring
    have h1 : (CP * bb ^ 2 * ν⁻¹ * Real.log bb ^ (-(100 : ℝ))) / ν ≤
        (Real.sqrt CP * bb * ν⁻¹ * Λ) ^ 2 := by
      have hnn : 0 ≤ CP * bb ^ 2 * ν⁻¹ * ν⁻¹ := by positivity
      calc (CP * bb ^ 2 * ν⁻¹ * Real.log bb ^ (-(100 : ℝ))) / ν
          = (CP * bb ^ 2 * ν⁻¹ * ν⁻¹) * Real.log bb ^ (-(100 : ℝ)) := by
            rw [div_eq_mul_inv]; ring
        _ ≤ (CP * bb ^ 2 * ν⁻¹ * ν⁻¹) * Lg ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left e3 hnn
        _ = _ := by rw [hsq]; ring
    calc _ ≤ Real.sqrt ((Real.sqrt CP * bb * ν⁻¹ * Λ) ^ 2) := Real.sqrt_le_sqrt h1
      _ = _ := Real.sqrt_sq (by positivity)
  have hA2 : (CP * bb * c4 * Real.sqrt ν * Real.log bb ^ (-(1 / 4 : ℝ))) / ν +
      Real.sqrt ((CP * bb ^ 2 * ν⁻¹ * Real.log bb ^ (-(100 : ℝ))) / ν) ≤
      (CP * c4 * Real.sqrt ν / ν + Real.sqrt CP / ν) * bb * Λ := by
    have h1 : (CP * bb * c4 * Real.sqrt ν * Real.log bb ^ (-(1 / 4 : ℝ))) / ν ≤
        (CP * bb * c4 * Real.sqrt ν * Λ) / ν :=
      div_le_div_of_nonneg_right (by gcongr) hν.le
    calc _ ≤ (CP * bb * c4 * Real.sqrt ν * Λ) / ν + Real.sqrt CP * bb * ν⁻¹ * Λ :=
          add_le_add h1 hbeta
      _ = _ := by field_simp
  have hmain : (CH * (ρ / aa) ^ γ) * (ρ / aa) ^ ((d : ℝ) / 2) *
      (CP * aa * c4 * Real.sqrt ν * Real.log aa ^ (-(1 / 4 : ℝ))) *
      ((CP * bb * c4 * Real.sqrt ν * Real.log bb ^ (-(1 / 4 : ℝ))) / ν +
        Real.sqrt ((CP * bb ^ 2 * ν⁻¹ * Real.log bb ^ (-(100 : ℝ))) / ν)) ≤
      (CH * (ρ / aa) ^ γ) * (ρ / aa) ^ ((d : ℝ) / 2) *
      (CP * aa * c4 * Real.sqrt ν * Λ) *
      ((CP * c4 * Real.sqrt ν / ν + Real.sqrt CP / ν) * bb * Λ) := by
    have hpos2 : 0 ≤ CP * c4 * Real.sqrt ν / ν + Real.sqrt CP / ν := by positivity
    have hlb : 0 ≤ Real.log bb := by linarith only [hLg1, hlogaa]
    have hrb := Real.rpow_nonneg hlb (-(1 / 4 : ℝ))
    have hA2nn : 0 ≤ (CP * bb * c4 * Real.sqrt ν * Real.log bb ^ (-(1 / 4 : ℝ))) / ν +
        Real.sqrt ((CP * bb ^ 2 * ν⁻¹ * Real.log bb ^ (-(100 : ℝ))) / ν) := by positivity
    have hra : 0 ≤ Real.log aa ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_nonneg (by linarith only [hLg1, hLg]) _
    have hqq : 0 ≤ (CH * (ρ / aa) ^ γ) * (ρ / aa) ^ ((d : ℝ) / 2) := by positivity
    calc _ ≤ (CH * (ρ / aa) ^ γ) * (ρ / aa) ^ ((d : ℝ) / 2) *
          (CP * aa * c4 * Real.sqrt ν * Λ) *
          ((CP * bb * c4 * Real.sqrt ν * Real.log bb ^ (-(1 / 4 : ℝ))) / ν +
            Real.sqrt ((CP * bb ^ 2 * ν⁻¹ * Real.log bb ^ (-(100 : ℝ))) / ν)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA1 hqq) hA2nn
      _ ≤ _ := mul_le_mul_of_nonneg_left hA2
          (mul_nonneg hqq (by positivity))
  refine hmain.trans (le_of_eq ?_)
  rw [← hθ]
  have : Λ * Λ = Lg ^ (-(1 / 2 : ℝ)) := hΛ2
  rw [← this]
  ring

end

end

end SuperdiffusionCLT.Section8
