/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.LinftyL2BdryB
public import SuperdiffusionCLT.Section7.Linfty.Cover
public import SuperdiffusionCLT.Section7.Lipschitz.Carriers
public import SuperdiffusionCLT.Section7.Prereq.WellPosedB
public import SuperdiffusionCLT.Section7.Prereq.WhitneyLocalD
public import SuperdiffusionCLT.Section7.Analytic.Change.SkewShift
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.OneStepDatumZeroTrace

/-!
# Boundary `L^∞`-`L²` estimate: the real form of the fine-grid boundary Lipschitz estimate
-/

@[expose] public section

open MeasureTheory Homogenization SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem linfL2c_shiftCube_eq (y : Vec d) (n : ℕ) :
    shiftCube y (n : ℤ) = Metric.ball y ((3 : ℝ) ^ n / 2) := hr_shiftCube_eq y n

theorem linfL2c_cube_mono (y : Vec d) {n k : ℕ} (h : n ≤ k) :
    shiftCube y (n : ℤ) ⊆ shiftCube y (k : ℤ) := by
  rw [linfL2c_shiftCube_eq, linfL2c_shiftCube_eq]
  exact Metric.ball_subset_ball (by
    have : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) h
    linarith only [this])

theorem linfL2c_vol_cube_ne_top (y : Vec d) (n : ℕ) : volume (shiftCube y (n : ℤ)) ≠ ⊤ := by
  rw [hr_shiftCube_eq]; exact h1_vol_cube_ne_top y n

/-- Conversion of the normalised-norm inequalities of the boundary estimate to real numbers. -/
theorem linfL2c_enn_real {Q q : Set (Vec d)} {F : Vec d → ℝ} {C : ℝ} (hC : 0 ≤ C) {n m' : ℕ}
    (hQfin : volume Q ≠ ⊤) (hvQ : 0 < (volume Q).toReal) (hFQ : MemLp F 2 (volume.restrict Q))
    (hqQ : q ⊆ Q) (hqfin : volume q ≠ ⊤) (hvq : 0 < (volume q).toReal) :
    (ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) * lpBar q 2 (fun x => F x - h1_avg q F) ≤
        ENNReal.ofReal (C * (3 : ℝ) ^ (-(m' : ℝ))) *
          (lpBar Q 2 (fun x => F x - h1_avg Q F) + lpBar Q 2 (fun x => F x - 0)) →
      h1_l2 q F ≤ C * ((3 : ℝ) ^ n / (3 : ℝ) ^ m') * (h1_l2 Q F + linfL2b_nl2 Q F)) ∧
    (ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) * lpBar q 2 (fun x => F x - 0) ≤
        ENNReal.ofReal (C * (3 : ℝ) ^ (-(m' : ℝ))) *
          (lpBar Q 2 (fun x => F x - h1_avg Q F) + lpBar Q 2 (fun x => F x - 0)) →
      linfL2b_nl2 q F ≤ C * ((3 : ℝ) ^ n / (3 : ℝ) ^ m') * (h1_l2 Q F + linfL2b_nl2 Q F)) := by
  have hFq : MemLp F 2 (volume.restrict q) := hFQ.mono_measure (Measure.restrict_mono hqQ le_rfl)
  have hosc := hr_lpBar_eq hQfin hvQ hFQ
  have hoscq := hr_lpBar_eq hqfin hvq hFq
  simp only [sub_zero]
  have hnrmQ := linfL2b_lpBar_eq hQfin hvQ hFQ
  have hnrmq := linfL2b_lpBar_eq hqfin hvq hFq
  have h3n : (0 : ℝ) ≤ (3 : ℝ) ^ (-(n : ℝ)) := by positivity
  have hRR : ENNReal.ofReal (C * (3 : ℝ) ^ (-(m' : ℝ))) *
      (ENNReal.ofReal (h1_l2 Q F) + ENNReal.ofReal (linfL2b_nl2 Q F)) =
      ENNReal.ofReal (C * (3 : ℝ) ^ (-(m' : ℝ)) * (h1_l2 Q F + linfL2b_nl2 Q F)) := by
    have h2 : 0 ≤ h1_l2 Q F := Real.sqrt_nonneg _
    rw [← ENNReal.ofReal_add h2 (linfL2b_nl2_nonneg _ _),
      ← ENNReal.ofReal_mul (by positivity)]
  have hcoef : (3 : ℝ) ^ (-(n : ℝ)) * ((3 : ℝ) ^ n) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]; simp
  have hcoef2 : C * (3 : ℝ) ^ (-(m' : ℝ)) * (3 : ℝ) ^ n = C * ((3 : ℝ) ^ n / (3 : ℝ) ^ m') := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]; ring
  have hR0 : 0 ≤ C * (3 : ℝ) ^ (-(m' : ℝ)) * (h1_l2 Q F + linfL2b_nl2 Q F) := by
    have := linfL2b_nl2_nonneg Q F
    have h2 : 0 ≤ h1_l2 Q F := Real.sqrt_nonneg _
    positivity
  have key : ∀ {a : ℝ}, 0 ≤ a → ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) * ENNReal.ofReal a ≤
      ENNReal.ofReal (C * (3 : ℝ) ^ (-(m' : ℝ)) * (h1_l2 Q F + linfL2b_nl2 Q F)) →
      a ≤ C * ((3 : ℝ) ^ n / (3 : ℝ) ^ m') * (h1_l2 Q F + linfL2b_nl2 Q F) := by
    intro a ha hle
    rw [← ENNReal.ofReal_mul h3n, ENNReal.ofReal_le_ofReal_iff hR0] at hle
    calc a = ((3 : ℝ) ^ n) * ((3 : ℝ) ^ (-(n : ℝ)) * a) := by
          rw [← mul_assoc, mul_comm ((3 : ℝ) ^ n), hcoef]; ring
      _ ≤ ((3 : ℝ) ^ n) * (C * (3 : ℝ) ^ (-(m' : ℝ)) * (h1_l2 Q F + linfL2b_nl2 Q F)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = _ := by rw [← hcoef2]; ring
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hoscq, hosc, hnrmQ, hRR] at h
    exact key (Real.sqrt_nonneg _) h
  · rw [hnrmq, hosc, hnrmQ, hRR] at h
    exact key (linfL2b_nl2_nonneg _ _) h

/-- **The real form of the boundary estimate.** -/
theorem linfL2c_lip_real [NeZero d] {U : Set (Vec d)} {nu : ℝ} {omega : ShellSeq d}
    {P : ProbabilityMeasure (ShellSeq d)} {A s : ℕ} {B E C Lhat : ℝ} {X : ShellSeq d → ℝ}
    (hω :
        ∀ m n m' : ℕ, n < m' → m' ≤ m → m ≤ m' + A →
          (m' : ℝ) - B * Real.log (m' : ℝ) ≤ (n : ℝ) → Lhat ≤ (n : ℝ) → X omega ≤ (3 : ℝ) ^ n →
          ∀ t : ℝ, (3 : ℝ) ^ m' ≤ t → t ≤ (3 : ℝ) ^ m →
          ∀ z ∈ gridPts d ((n : ℤ) - s) ((3 : ℝ) ^ (m + 2)), z ∈ t • U →
          ∀ (f g : Vec d → ℝ), ContDiff ℝ 2 g →
          ∀ u : H1Function (shiftCube z (m' : ℤ) ∩ t • U),
            IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega)
              (shiftCube z (m' : ℤ) ∩ t • U) u f (fun _ => 0) →
            LocalizedZeroTraceFunctionOn (shiftCube z (m' : ℤ) ∩ t • U)
              (shiftCube z (m' : ℤ)) (fun x => u.toFun x - g x) →
            ∀ R : ℝ≥0∞,
              R = ENNReal.ofReal (C * (3 : ℝ) ^ (-(m' : ℝ))) *
                  (lpBar (shiftCube z (m' : ℤ) ∩ t • U) 2
                      (fun x => u.toFun x - ⨍ w in shiftCube z (m' : ℤ) ∩ t • U, u.toFun w) +
                    lpBar (shiftCube z (m' : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x)) +
                ENNReal.ofReal (C * (sigmaBarInfinite nu m P)⁻¹ * (3 : ℝ) ^ m') *
                  eLpNorm f ⊤ (volume.restrict (shiftCube z (m' : ℤ) ∩ t • U)) +
                ENNReal.ofReal (C * ((m' : ℝ) - (n : ℝ))) *
                  eLpNorm (fun x => ‖fderiv ℝ g x‖) ⊤ (volume.restrict (shiftCube z (m' : ℤ))) +
                ENNReal.ofReal (C * (m : ℝ) ^ (-E) * (3 : ℝ) ^ m') *
                  eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ g) x‖) ⊤
                    (volume.restrict (shiftCube z (m' : ℤ))) →
            -- e.Dir.new.C01.boundary, with the oscillation kept on the left
            ENNReal.ofReal ((Real.sqrt (sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => eucNorm (u.grad x)) +
                ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2
                    (fun x => u.toFun x - ⨍ w in shiftCube z (n : ℤ) ∩ t • U, u.toFun w) ≤ R ∧
              -- on a cube that meets the boundary, the solution itself is flat relative to `g`
              (¬ shiftCube z (n : ℤ) ⊆ t • U →
                ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x) ≤ R))
    {m n m' : ℕ} (hn : n < m') (hm1 : m' ≤ m) (hm2 : m ≤ m' + A)
    (hB : (m' : ℝ) - B * Real.log (m' : ℝ) ≤ (n : ℝ)) (hL : Lhat ≤ (n : ℝ))
    (hX : X omega ≤ (3 : ℝ) ^ n) {t : ℝ} (ht1 : (3 : ℝ) ^ m' ≤ t) (ht2 : t ≤ (3 : ℝ) ^ m)
    {z : Vec d} (hz : z ∈ gridPts d ((n : ℤ) - s) ((3 : ℝ) ^ (m + 2))) (hzt : z ∈ t • U)
    (hC : 0 ≤ C) (w : H1Function (shiftCube z (m' : ℤ) ∩ t • U))
    (hw : IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega)
      (shiftCube z (m' : ℤ) ∩ t • U) w (fun _ => 0) (fun _ => 0))
    (hzero : LocalizedZeroTraceFunctionOn (shiftCube z (m' : ℤ) ∩ t • U)
      (shiftCube z (m' : ℤ)) w.toFun)
    (hvq : 0 < (volume (shiftCube z (n : ℤ) ∩ t • U)).toReal)
    (hvQ : 0 < (volume (shiftCube z (m' : ℤ) ∩ t • U)).toReal) :
    h1_l2 (shiftCube z (n : ℤ) ∩ t • U) w.toFun ≤
        C * ((3 : ℝ) ^ n / (3 : ℝ) ^ m') *
          (h1_l2 (shiftCube z (m' : ℤ) ∩ t • U) w.toFun +
            linfL2b_nl2 (shiftCube z (m' : ℤ) ∩ t • U) w.toFun) ∧
      (¬ shiftCube z (n : ℤ) ⊆ t • U →
        linfL2b_nl2 (shiftCube z (n : ℤ) ∩ t • U) w.toFun ≤
          C * ((3 : ℝ) ^ n / (3 : ℝ) ^ m') *
            (h1_l2 (shiftCube z (m' : ℤ) ∩ t • U) w.toFun +
              linfL2b_nl2 (shiftCube z (m' : ℤ) ∩ t • U) w.toFun)) := by
  have hg : ContDiff ℝ 2 (fun _ : Vec d => (0 : ℝ)) := contDiff_const
  have h := hω m n m' hn hm1 hm2 hB hL hX t ht1 ht2 z hz hzt (fun _ => 0) (fun _ => 0) hg w hw
    (by simpa using hzero) _ rfl
  have e1 : eLpNorm (fun _ : Vec d => (0 : ℝ)) ⊤
      (volume.restrict (shiftCube z (m' : ℤ) ∩ t • U)) = 0 := eLpNorm_zero
  have h1 : fderiv ℝ (fun _ : Vec d => (0 : ℝ)) = fun _ => (0 : Vec d →L[ℝ] ℝ) :=
    fderiv_fun_const (𝕜 := ℝ) (0 : ℝ)
  have h2 : fderiv ℝ (fun _ : Vec d => (0 : Vec d →L[ℝ] ℝ)) = 0 :=
    fderiv_fun_const (𝕜 := ℝ) (0 : Vec d →L[ℝ] ℝ)
  have e2 : eLpNorm (fun x : Vec d => ‖fderiv ℝ (fun _ : Vec d => (0 : ℝ)) x‖) ⊤
      (volume.restrict (shiftCube z (m' : ℤ))) = 0 := by
    have : (fun x : Vec d => ‖fderiv ℝ (fun _ : Vec d => (0 : ℝ)) x‖) = fun _ => 0 := by
      funext x; rw [h1]; exact norm_zero
    rw [this]; exact eLpNorm_zero
  have e3 : eLpNorm (fun x : Vec d => ‖fderiv ℝ (fderiv ℝ (fun _ : Vec d => (0 : ℝ))) x‖) ⊤
      (volume.restrict (shiftCube z (m' : ℤ))) = 0 := by
    have : (fun x : Vec d => ‖fderiv ℝ (fderiv ℝ (fun _ : Vec d => (0 : ℝ))) x‖) = fun _ => 0 := by
      funext x; rw [h1, h2]; exact ContinuousLinearMap.opNorm_zero
    rw [this]; exact eLpNorm_zero
  rw [e1, e2, e3] at h
  simp only [mul_zero, add_zero, hr_avg_eq] at h
  have hQfin : volume (shiftCube z (m' : ℤ) ∩ t • U) ≠ ⊤ :=
    ne_top_of_le_ne_top (linfL2c_vol_cube_ne_top z m') (measure_mono Set.inter_subset_left)
  have hqfin : volume (shiftCube z (n : ℤ) ∩ t • U) ≠ ⊤ :=
    ne_top_of_le_ne_top (linfL2c_vol_cube_ne_top z n) (measure_mono Set.inter_subset_left)
  have hqQ : shiftCube z (n : ℤ) ∩ t • U ⊆ shiftCube z (m' : ℤ) ∩ t • U :=
    Set.inter_subset_inter_left _ (linfL2c_cube_mono z hn.le)
  have gen := linfL2c_enn_real (F := w.toFun) (n := n) (m' := m') hC hQfin hvQ w.memL2 hqQ hqfin hvq
  exact ⟨gen.1 (le_trans le_add_self h.1), fun hnc => gen.2 (h.2 hnc)⟩

/-! ### Geometry -/

theorem linfL2c_ann_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) {x : Vec d} :
    x ∈ decayEst_ann (d := d) a b ↔ a < eucNorm x ∧ eucNorm x < b := by
  unfold decayEst_ann eucNorm
  rw [Set.mem_ofPred_eq, Real.lt_sqrt ha, Real.sqrt_lt' hb]

/-- A cube around a point near `x` stays inside the annulus. -/
theorem linfL2c_cube_in_ann {R : ℝ} (hR : 0 < R) {x w y : Vec d} {j : ℕ} {ρ : ℝ}
    (hx : R / 3 < eucNorm x) (hxw : ‖x - w‖ ≤ ρ)
    (hρ : Real.sqrt d * (ρ + (3 : ℝ) ^ j / 2) ≤ R / 12) (hy : y ∈ shiftCube w (j : ℤ))
    (hyS : y ∈ euclidBall (d := d) R) : y ∈ decayEst_ann (d := d) (R / 4) R := by
  rw [linfL2c_ann_iff (by positivity) hR]
  rw [linfL2c_shiftCube_eq, Metric.mem_ball, dist_eq_norm] at hy
  refine ⟨?_, (linfL2b_mem_euclidBall hR).1 hyS⟩
  have h1 : eucNorm x ≤ eucNorm y + eucNorm (x - y) := by
    have := linfL2b_euc_add (x - y) y
    rwa [sub_add_cancel, add_comm] at this
  have h2 : eucNorm (x - y) ≤ Real.sqrt d * ‖x - y‖ := linfL2b_euc_le_norm _
  have h3 : ‖x - y‖ ≤ ‖x - w‖ + ‖y - w‖ := by
    have : x - y = (x - w) - (y - w) := by abel
    rw [this]; exact norm_sub_le _ _
  have h4 : ‖x - y‖ ≤ ρ + (3 : ℝ) ^ j / 2 := by linarith only [h3, hxw, hy]
  have h5 : Real.sqrt d * ‖x - y‖ ≤ Real.sqrt d * (ρ + (3 : ℝ) ^ j / 2) :=
    mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
  linarith only [h1, h2, h5, hρ, hx]

/-- A lattice point of the fine grid near a point of the dilated domain. -/
theorem linfL2c_cover_pt {U : Set (Vec d)} {s : ℕ} {c : ℝ}
    (hcov : ∀ (t : ℝ) (n : ℕ), 0 < t → (3 : ℝ) ^ n ≤ c * t → ∀ x ∈ t • U,
      ∃ k : Fin d → ℤ, (fun i => (3 : ℝ) ^ ((n : ℤ) - s) * (k i : ℝ)) ∈ t • U ∧
        ‖x - (fun i => (3 : ℝ) ^ ((n : ℤ) - s) * (k i : ℝ))‖ ≤ (3 : ℝ) ^ n)
    (e i : ℕ) {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M) (hc : (3 : ℝ) ^ i ≤ c * t)
    (hMt : ∀ w ∈ t • U, ∀ k : Fin d, |w k| ≤ M) {x : Vec d} (hx : x ∈ t • U) :
    ∃ w ∈ gridPts d (((i + e + 2 : ℕ) : ℤ) - ((s + e + 2 : ℕ) : ℤ)) M, w ∈ t • U ∧
      ‖x - w‖ ≤ (3 : ℝ) ^ i := by
  obtain ⟨k, hk, hkx⟩ := hcov t i ht hc x hx
  refine ⟨_, ?_, hk, hkx⟩
  rw [mem_gridPts hM]
  refine ⟨k, fun l => ?_, fun l => hMt _ hk l⟩
  congr 2
  push_cast
  ring

/-- The oscillation and the norm on a subset are controlled by those on a larger set. -/
theorem linfL2c_Q_to_Wa {Q Wa : Set (Vec d)} (hQ : Q ⊆ Wa) (hW : volume Wa ≠ ⊤)
    (hvQ : 0 < (volume Q).toReal) {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict Wa))
    {V1 : ℝ} (hV1 : (volume Wa).toReal / (volume Q).toReal ≤ V1) :
    h1_l2 Q u + linfL2b_nl2 Q u ≤ Real.sqrt V1 * (h1_l2 Wa u + linfL2b_nl2 Wa u) := by
  have h1 := h1_l2_le hQ hu hW hvQ
  have h2 := linfL2b_nl2_mono hQ hW hvQ hu
  have hs : Real.sqrt ((volume Wa).toReal / (volume Q).toReal) ≤ Real.sqrt V1 :=
    Real.sqrt_le_sqrt hV1
  have hD : 0 ≤ h1_l2 Wa u := Real.sqrt_nonneg _
  have hY : 0 ≤ linfL2b_nl2 Wa u := linfL2b_nl2_nonneg _ _
  have h3 := mul_le_mul_of_nonneg_right hs hD
  have h4 := mul_le_mul_of_nonneg_right hs hY
  nlinarith only [h1, h2, h3, h4]

/-- **The boundary estimate in terms of the annulus.** The oscillation (and, on cells that meet
the boundary, the norm) of the solution on a cell of the fine grid is at most `E₁ 3^{j-m'}` times
the oscillation plus the norm on the annulus. -/
theorem linfL2c_lip_wa [NeZero d] {U : Set (Vec d)} {nu : ℝ} {omega : ShellSeq d}
    {P : ProbabilityMeasure (ShellSeq d)} {A s : ℕ} {B E C Lhat : ℝ} {X : ShellSeq d → ℝ}
    (hω :
        ∀ m n m' : ℕ, n < m' → m' ≤ m → m ≤ m' + A →
          (m' : ℝ) - B * Real.log (m' : ℝ) ≤ (n : ℝ) → Lhat ≤ (n : ℝ) → X omega ≤ (3 : ℝ) ^ n →
          ∀ t : ℝ, (3 : ℝ) ^ m' ≤ t → t ≤ (3 : ℝ) ^ m →
          ∀ z ∈ gridPts d ((n : ℤ) - s) ((3 : ℝ) ^ (m + 2)), z ∈ t • U →
          ∀ (f g : Vec d → ℝ), ContDiff ℝ 2 g →
          ∀ u : H1Function (shiftCube z (m' : ℤ) ∩ t • U),
            IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega)
              (shiftCube z (m' : ℤ) ∩ t • U) u f (fun _ => 0) →
            LocalizedZeroTraceFunctionOn (shiftCube z (m' : ℤ) ∩ t • U)
              (shiftCube z (m' : ℤ)) (fun x => u.toFun x - g x) →
            ∀ R : ℝ≥0∞,
              R = ENNReal.ofReal (C * (3 : ℝ) ^ (-(m' : ℝ))) *
                  (lpBar (shiftCube z (m' : ℤ) ∩ t • U) 2
                      (fun x => u.toFun x - ⨍ w in shiftCube z (m' : ℤ) ∩ t • U, u.toFun w) +
                    lpBar (shiftCube z (m' : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x)) +
                ENNReal.ofReal (C * (sigmaBarInfinite nu m P)⁻¹ * (3 : ℝ) ^ m') *
                  eLpNorm f ⊤ (volume.restrict (shiftCube z (m' : ℤ) ∩ t • U)) +
                ENNReal.ofReal (C * ((m' : ℝ) - (n : ℝ))) *
                  eLpNorm (fun x => ‖fderiv ℝ g x‖) ⊤ (volume.restrict (shiftCube z (m' : ℤ))) +
                ENNReal.ofReal (C * (m : ℝ) ^ (-E) * (3 : ℝ) ^ m') *
                  eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ g) x‖) ⊤
                    (volume.restrict (shiftCube z (m' : ℤ))) →
            -- e.Dir.new.C01.boundary, with the oscillation kept on the left
            ENNReal.ofReal ((Real.sqrt (sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => eucNorm (u.grad x)) +
                ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2
                    (fun x => u.toFun x - ⨍ w in shiftCube z (n : ℤ) ∩ t • U, u.toFun w) ≤ R ∧
              -- on a cube that meets the boundary, the solution itself is flat relative to `g`
              (¬ shiftCube z (n : ℤ) ⊆ t • U →
                ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x) ≤ R))
    (hC : 0 ≤ C) {R : ℝ} (hR : 0 < R) (hS : (2 * R) • U = euclidBall (d := d) R)
    (u0 : H1Function (euclidBall (d := d) R)) {m m' nb : ℕ} (hm1 : m' ≤ m) (hm2 : m ≤ m' + A)
    (hBn : (m' : ℝ) - B * Real.log (m' : ℝ) ≤ (nb : ℝ)) (hLn : Lhat ≤ (nb : ℝ))
    (hXn : X omega ≤ (3 : ℝ) ^ nb) (ht1 : (3 : ℝ) ^ m' ≤ 2 * R) (ht2 : 2 * R ≤ (3 : ℝ) ^ m)
    {cd V1 : ℝ} (hcd : 0 < cd) (hV10 : 0 ≤ V1)
    (hdens : ∀ j : ℕ, j ≤ m' → ∀ w ∈ euclidBall (d := d) R,
      ENNReal.ofReal (cd * ((3 : ℝ) ^ j) ^ d) ≤
        volume (shiftCube w (j : ℤ) ∩ euclidBall (d := d) R))
    (hV1 : (volume (decayEst_ann (d := d) (R / 4) R)).toReal ≤
      V1 * (cd * ((3 : ℝ) ^ m') ^ d))
    (hgeo : Real.sqrt d * ((3 : ℝ) ^ m' + (3 : ℝ) ^ m' / 2) ≤ R / 12)
    (hwR : ∀ (V : Set (Vec d)) (hV : IsOpen V) (hVS : V ⊆ euclidBall (d := d) R),
      V ⊆ decayEst_ann (d := d) (R / 8) R →
      IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega) V (u0.restrict hV hVS)
        (fun _ => 0) (fun _ => 0))
    (hz0 : ∀ (w : Vec d) (j : ℕ), LocalizedZeroTraceFunctionOn
      (shiftCube w (j : ℤ) ∩ euclidBall (d := d) R) (shiftCube w (j : ℤ)) u0.toFun) :
    ∀ j : ℕ, nb ≤ j → j < m' → ∀ w ∈ gridPts d ((j : ℤ) - (s : ℤ)) ((3 : ℝ) ^ (m + 2)),
      w ∈ euclidBall (d := d) R →
      (∃ x ∈ decayEst_ann (d := d) (R / 3) R, ‖x - w‖ ≤ (3 : ℝ) ^ m') →
      h1_l2 (shiftCube w (j : ℤ) ∩ euclidBall (d := d) R) u0.toFun ≤
          (C * Real.sqrt V1) * ((3 : ℝ) ^ j / (3 : ℝ) ^ m') *
            (h1_l2 (decayEst_ann (d := d) (R / 4) R) u0.toFun +
              linfL2b_nl2 (decayEst_ann (d := d) (R / 4) R) u0.toFun) ∧
        (¬ shiftCube w (j : ℤ) ⊆ euclidBall (d := d) R →
          linfL2b_nl2 (shiftCube w (j : ℤ) ∩ euclidBall (d := d) R) u0.toFun ≤
            (C * Real.sqrt V1) * ((3 : ℝ) ^ j / (3 : ℝ) ^ m') *
              (h1_l2 (decayEst_ann (d := d) (R / 4) R) u0.toFun +
                linfL2b_nl2 (decayEst_ann (d := d) (R / 4) R) u0.toFun)) := by
  intro j hj hjm w hw hwS ⟨x, hxA, hxw⟩
  have hSo : IsOpen (euclidBall (d := d) R) := isOpen_euclidBall R
  have hxR : R / 3 < eucNorm x := ((linfL2c_ann_iff (a := R / 3) (b := R) (by positivity) hR).1 hxA).1
  have hWafin : volume (decayEst_ann (d := d) (R / 4) R) ≠ ⊤ :=
    ne_top_of_le_ne_top (h1_vol_ball_ne_top hR) (measure_mono (decayEst_ann_subset _ _))
  have hu2 := u0.memL2
  -- the big cube lies in the annulus
  have hQA : shiftCube w (m' : ℤ) ∩ euclidBall (d := d) R ⊆ decayEst_ann (d := d) (R / 4) R :=
    fun y hy => linfL2c_cube_in_ann hR hxR hxw hgeo hy.1 hy.2
  have hQA8 : shiftCube w (m' : ℤ) ∩ euclidBall (d := d) R ⊆ decayEst_ann (d := d) (R / 8) R := by
    intro y hy
    have h1 := hQA hy
    rw [linfL2c_ann_iff (by positivity) hR] at h1 ⊢
    exact ⟨by linarith only [h1.1, hR], h1.2⟩
  have hQo : IsOpen (shiftCube w (m' : ℤ) ∩ euclidBall (d := d) R) := (rc_isOpen_shiftCube w _).inter hSo
  have hQo' : IsOpen (shiftCube w (m' : ℤ) ∩ (2 * R) • U) := by rw [hS]; exact hQo
  have hQS' : shiftCube w (m' : ℤ) ∩ (2 * R) • U ⊆ euclidBall (d := d) R := by
    rw [hS]; exact Set.inter_subset_right
  have hQ8' : shiftCube w (m' : ℤ) ∩ (2 * R) • U ⊆ decayEst_ann (d := d) (R / 8) R := by
    rw [hS]; exact hQA8
  have hwS' := hwR _ hQo' hQS' hQ8'
  have hzz : LocalizedZeroTraceFunctionOn (shiftCube w (m' : ℤ) ∩ (2 * R) • U)
      (shiftCube w (m' : ℤ)) u0.toFun := by rw [hS]; exact hz0 w m'
  have hvolS : ∀ i : ℕ, i ≤ m' → 0 < (volume (shiftCube w (i : ℤ) ∩ euclidBall (d := d) R)).toReal := by
    intro i hi
    have h := hdens i hi w hwS
    have hfin : volume (shiftCube w (i : ℤ) ∩ euclidBall (d := d) R) ≠ ⊤ :=
      ne_top_of_le_ne_top (h1_vol_ball_ne_top hR) (measure_mono Set.inter_subset_right)
    have := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_ofReal (by positivity)] at this
    exact lt_of_lt_of_le (by positivity) this
  have hvQ := hvolS m' le_rfl
  have hvq := hvolS j hjm.le
  have hlip := linfL2c_lip_real (U := U) (nu := nu) (omega := omega) (P := P) (A := A) (s := s)
    (B := B) (E := E) (C := C) (Lhat := Lhat) (X := X) hω hjm hm1 hm2
    (hBn.trans (by exact_mod_cast hj)) (hLn.trans (by exact_mod_cast hj))
    (hXn.trans (pow_le_pow_right₀ (by norm_num) hj)) ht1 ht2 hw
    (by rw [hS]; exact hwS) hC
    (u0.restrict hQo' hQS') hwS' hzz
    (by rw [hS]; exact hvq) (by rw [hS]; exact hvQ)
  obtain ⟨hA, hC'⟩ := hlip
  have e : (u0.restrict hQo' hQS').toFun = u0.toFun := rfl
  rw [e, hS] at hA hC'
  have hratio : (volume (decayEst_ann (d := d) (R / 4) R)).toReal /
      (volume (shiftCube w (m' : ℤ) ∩ euclidBall (d := d) R)).toReal ≤ V1 := by
    rw [div_le_iff₀ hvQ]
    have h := hdens m' le_rfl w hwS
    have hfin : volume (shiftCube w (m' : ℤ) ∩ euclidBall (d := d) R) ≠ ⊤ :=
      ne_top_of_le_ne_top (h1_vol_ball_ne_top hR) (measure_mono Set.inter_subset_right)
    have h2 := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_ofReal (by positivity)] at h2
    calc _ ≤ V1 * (cd * ((3 : ℝ) ^ m') ^ d) := hV1
      _ ≤ V1 * (volume (shiftCube w (m' : ℤ) ∩ euclidBall (d := d) R)).toReal :=
          mul_le_mul_of_nonneg_left h2 hV10
  have hQW := linfL2c_Q_to_Wa hQA hWafin hvQ
    (hu2.mono_measure (Measure.restrict_mono (decayEst_ann_subset _ _) le_rfl)) hratio
  have hcoef : 0 ≤ C * ((3 : ℝ) ^ j / (3 : ℝ) ^ m') := by positivity
  have hfin2 := mul_le_mul_of_nonneg_left hQW hcoef
  refine ⟨?_, fun hnc => ?_⟩
  · calc _ ≤ _ := hA
      _ ≤ C * ((3 : ℝ) ^ j / (3 : ℝ) ^ m') * (Real.sqrt V1 * _) := hfin2
      _ = _ := by ring
  · calc _ ≤ _ := hC' hnc
      _ ≤ C * ((3 : ℝ) ^ j / (3 : ℝ) ^ m') * (Real.sqrt V1 * _) := hfin2
      _ = _ := by ring

/-- A function of `H¹₀` of a ball has the localized zero trace on every cell. -/
theorem linfL2c_zero_trace {R : ℝ} (u : H10Function (euclidBall (d := d) R)) (w : Vec d)
    (j : ℕ) : LocalizedZeroTraceFunctionOn (shiftCube w (j : ℤ) ∩ euclidBall (d := d) R)
      (shiftCube w (j : ℤ)) u.toH1Function.toFun := by
  intro η hη hηc hηsub
  exact SuperdiffusionCLT.Section8.Common.ExcessDecay.memH10_mul_of_tsupport_subset
    (isOpen_euclidBall R) (rc_isOpen_shiftCube w _) ⟨u, rfl⟩ hη hηc hηsub

/-- **Almost surely, a weak solution of the recentred field is one of the centred field.** -/
theorem linfL2c_weak_centred [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega ∂P.toMeasure, ∀ (m : ℕ) {R : ℝ}, 0 < R →
      ∀ (u0 : H1Function (euclidBall (d := d) R)),
      (∀ (V : Set (Vec d)) (hV : IsOpen V) (hVS : V ⊆ euclidBall (d := d) R),
        V ⊆ decayEst_ann (d := d) (R / 8) R →
        IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega) V (u0.restrict hV hVS)
          (fun _ => 0) (fun _ => 0)) →
      ∀ (V : Set (Vec d)) (hV : IsOpen V) (hVS : V ⊆ euclidBall (d := d) R),
        V ⊆ decayEst_ann (d := d) (R / 8) R →
        IsWeakSolutionOn (fun x => nu • (1 : Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
            (cubeSet (originCube d (m : ℤ))) x) V (u0.restrict hV hVS) (fun _ => 0)
          (fun _ => 0) := by
  filter_upwards [ae_isWeakSolutionOn_centered_iff_recentered hJ3 nu,
    w0_ae_isElliptic_bounded hJ3 hnu] with omega h1 h2 m R hR u0 hw V hV hVS hVA
  have hbd : Bornology.IsBounded (euclidBall (d := d) R) :=
    (Metric.isBounded_closedBall (x := (0 : Vec d)) (r := R)).subset fun x hx => by
      rw [mem_closedBall_zero_iff]
      exact ((linfL2b_norm_le_euc x).trans ((linfL2b_mem_euclidBall hR).1 hx).le)
  obtain ⟨Lam, hEll⟩ := h2 (euclidBall (d := d) R) hbd (measurableSet_euclidBall R)
  have hEllV := wh2_isEllipticFieldOn_mono hV.measurableSet hVS hEll
  have hflux := memVectorL2_matVecMul_of_isEllipticFieldOn hEllV (u0.restrict hV hVS).grad_memVectorL2
  have hfin : volume V ≠ ⊤ :=
    ne_top_of_le_ne_top (h1_vol_ball_ne_top hR) (measure_mono hVS)
  have : IsFiniteMeasure (volumeMeasureOn V) := by
    simpa [volumeMeasureOn] using (isFiniteMeasure_restrict.mpr hfin)
  exact (h1 m hV this (u0.restrict hV hVS) (fun _ => 0) (fun _ => 0) hflux).2 (hw V hV hVS hVA)

theorem linfL2c_eucNorm_single [NeZero d] {ρ : ℝ} (hρ : 0 < ρ) :
    eucNorm (Pi.single (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d) ρ : Vec d) = ρ := by
  unfold eucNorm vecNormSq vecDot
  have : ∑ j : Fin d, (Pi.single (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d) ρ : Vec d) j *
      (Pi.single (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d) ρ : Vec d) j = ρ ^ 2 := by
    rw [Finset.sum_eq_single (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d)]
    · simp [sq]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb]; simp
    · simp
  rw [this, Real.sqrt_sq hρ.le]

/-- **A cell of the fine grid that meets the boundary**, near the sphere. -/
theorem linfL2c_cut_cell [NeZero d] {R : ℝ} {sL e nc : ℕ} {Mg : ℝ} (hR : 0 < R)
    (hcovS : ∀ i : ℕ, i + e + 2 ≤ nc → ∀ x ∈ euclidBall (d := d) R,
      ∃ w ∈ gridPts d (((i + e + 2 : ℕ) : ℤ) - (sL : ℤ)) Mg, w ∈ euclidBall (d := d) R ∧
        ‖x - w‖ ≤ (3 : ℝ) ^ i)
    (hnc : e + 2 ≤ nc) (h3e : 8 * (d : ℝ) ≤ (3 : ℝ) ^ e) (hsm : (3 : ℝ) ^ nc ≤ R) :
    ∃ z0 ∈ gridPts d ((nc : ℤ) - (sL : ℤ)) Mg, z0 ∈ euclidBall (d := d) R ∧
      ¬ shiftCube z0 (nc : ℤ) ⊆ euclidBall (d := d) R ∧
      ∃ x ∈ decayEst_ann (d := d) (R / 3) R, ‖x - z0‖ ≤ (3 : ℝ) ^ nc := by
  set L : ℝ := (3 : ℝ) ^ nc with hL
  have hLpos : 0 < L := by positivity
  set ρ : ℝ := R - L / 8 with hρ
  have hρpos : 0 < ρ := by linarith only [hsm, hLpos, hR, hρ]
  set x0 : Vec d := Pi.single (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d) ρ with hx0
  have hx0n : eucNorm x0 = ρ := linfL2c_eucNorm_single hρpos
  have hx0A : x0 ∈ decayEst_ann (d := d) (R / 3) R := by
    rw [linfL2c_ann_iff (by positivity) hR, hx0n]
    constructor <;> linarith only [hsm, hLpos, hR, hρ]
  have hx0S : x0 ∈ euclidBall (d := d) R := by
    rw [linfL2b_mem_euclidBall hR, hx0n]; linarith only [hsm, hLpos, hR, hρ]
  obtain ⟨z0, hz0g, hz0S, hz0d⟩ := hcovS (nc - (e + 2)) (by omega) x0 hx0S
  have e1 : nc - (e + 2) + e + 2 = nc := by omega
  rw [e1] at hz0g
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hsd : Real.sqrt d ≤ d := by
    calc Real.sqrt d ≤ Real.sqrt ((d : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith only [hd1])
      _ = d := Real.sqrt_sq (by linarith only [hd1])
  have h3i : (3 : ℝ) ^ (nc - (e + 2)) * ((3 : ℝ) ^ e * 9) = L := by
    rw [hL, show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num, ← pow_add, ← pow_add]; congr 1
  have h3ip : 0 < (3 : ℝ) ^ (nc - (e + 2)) := by positivity
  have hdiff : eucNorm (x0 - z0) ≤ L / 72 := by
    have h1 := linfL2b_euc_le_norm (x0 - z0)
    have h2 : Real.sqrt d * ‖x0 - z0‖ ≤ Real.sqrt d * (3 : ℝ) ^ (nc - (e + 2)) :=
      mul_le_mul_of_nonneg_left hz0d (Real.sqrt_nonneg _)
    have h3 : Real.sqrt d * (3 : ℝ) ^ (nc - (e + 2)) ≤ d * (3 : ℝ) ^ (nc - (e + 2)) :=
      mul_le_mul_of_nonneg_right hsd h3ip.le
    have h4 : (d : ℝ) * (3 : ℝ) ^ (nc - (e + 2)) ≤ L / 72 := by
      have : (d : ℝ) * (72 * (3 : ℝ) ^ (nc - (e + 2))) ≤ (3 : ℝ) ^ e * 9 * (3 : ℝ) ^ (nc - (e + 2)) := by
        nlinarith only [h3e, h3ip]
      nlinarith only [this, h3i, h3ip]
    linarith only [h1, h2, h3, h4]
  have hz0n : R - L / 8 - L / 72 ≤ eucNorm z0 := by
    have := linfL2b_euc_add (x0 - z0) z0
    rw [sub_add_cancel] at this
    linarith only [this, hdiff, hx0n, hρ]
  have hz0pos : 0 < eucNorm z0 := by linarith only [hz0n, hsm, hLpos]
  refine ⟨z0, hz0g, hz0S, ?_, x0, hx0A, ?_⟩
  · intro hsub
    set c : ℝ := L / 4 / eucNorm z0 with hc
    have hcpos : 0 < c := by positivity
    have hyc : z0 + c • z0 = (1 + c) • z0 := by module
    have hyn : eucNorm (z0 + c • z0) = eucNorm z0 + L / 4 := by
      rw [hyc, linfL2b_euc_smul, abs_of_pos (by linarith only [hcpos])]
      rw [hc]; field_simp
    have hyin : z0 + c • z0 ∈ shiftCube z0 (nc : ℤ) := by
      rw [linfL2c_shiftCube_eq, Metric.mem_ball, dist_eq_norm]
      have : z0 + c • z0 - z0 = c • z0 := by abel
      rw [this]
      refine lt_of_le_of_lt (linfL2b_norm_le_euc _) ?_
      rw [linfL2b_euc_smul, abs_of_pos hcpos, hc]
      have : L / 4 / eucNorm z0 * eucNorm z0 = L / 4 := by field_simp
      rw [this, ← hL]; linarith only [hLpos]
    have := hsub hyin
    rw [linfL2b_mem_euclidBall hR, hyn] at this
    linarith only [this, hz0n, hsm, hLpos]
  · exact hz0d.trans (pow_le_pow_right₀ (by norm_num) (by omega))

end SuperdiffusionCLT.Section8
