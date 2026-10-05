/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2InteriorB
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApi
public import SuperdiffusionCLT.Section7.Prereq.L2ComparisonB
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Interior
public import SuperdiffusionCLT.Section7.Root.InteriorApprox
public import SuperdiffusionCLT.Section7.Prereq.LinftyReduction
public import Homogenization.Sobolev.MatchedPair.ScaledPoincare

/-!
# Interior De Giorgi step for the `L^∞` homogenization estimate

On the cube `z + cu_{n+1}` the mean-subtracted solution is bounded on the half cube by the De
Giorgi `L^∞`-`L²` estimate (applied to `±(v - c₀)`); the mean-zero Poincaré inequality bounds the
`L²` norm by the gradient, and the mollification error `v - η_n ∗ v` on the cell `z + □_n` is
controlled by the `L¹` oscillation on the cube (the sup-ball of radius `3^n` around a point of the
cell lies in the cube up to a null set).
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem linf_dgi_volume (z : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    volume (axisCube z L) = ENNReal.ofReal (L ^ d) := by
  have h : volume (axisCube z L) = ∏ i, ENNReal.ofReal ((z i + L) - z i) := by
    rw [axisCube, Real.volume_pi_Ioo]
  rw [h]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hL]

/-- Mean-zero Poincaré on a cube in the normalized form. -/
theorem linf_dgi_poincare (z : Vec d) {L : ℝ} (hL : 0 < L) (v : H1Function (axisCube z L))
    {Gb : ℝ} (hGb : 0 ≤ Gb)
    (hG : lpBar (axisCube z L) 2 (fun x => eucNorm (v.grad x)) ≤ ENNReal.ofReal Gb) :
    eLpNorm (v.subAverage.toFun) 2 (volume.restrict (axisCube z L)) ≤
      ENNReal.ofReal (L ^ ((d : ℝ) / 2) * (unitMeanZeroPoincareConst d * d * L * Gb)) := by
  have hvol : volume (axisCube z L) = ENNReal.ofReal (L ^ d) := linf_dgi_volume z hL.le
  have hfin : volume (axisCube z L) ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  have : IsFiniteMeasure (volumeMeasureOn (axisCube z L)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfin⟩
  have raw := scaled_meanZero_poincare z hL v
  have hgm : AEStronglyMeasurable (fun x => v.grad x) (volume.restrict (axisCube z L)) :=
    (aemeasurable_pi_iff.2 fun i => (v.gradMemL2 i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hEm : AEStronglyMeasurable (fun x => eucNorm (v.grad x)) (volume.restrict (axisCube z L)) := by
    have hc : Continuous (fun y : Vec d => eucNorm y) := by
      unfold eucNorm vecNormSq vecDot
      fun_prop
    exact hc.comp_aestronglyMeasurable hgm
  set E := eLpNorm (fun x => eucNorm (v.grad x)) 2 (volume.restrict (axisCube z L)) with hE
  have hEeq := ia_lpBar_eq_mul (U := (axisCube z L)) (p := 2) (by norm_num) (by norm_num) hfin
    (fun x => eucNorm (v.grad x)) hEm
  have hsq : ((volume (axisCube z L)) ^ (1 / (2 : ℝ≥0∞).toReal)) = ENNReal.ofReal (L ^ ((d : ℝ) / 2)) := by
    rw [hvol]
    simp only [ENNReal.toReal_ofNat]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    have : (L ^ d) ^ (1 / 2 : ℝ) = L ^ ((d : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
      ring_nf
    rw [this]
  have hEle : E ≤ ENNReal.ofReal (L ^ ((d : ℝ) / 2) * Gb) := by
    rw [hE, hEeq, hsq, ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' le_rfl hG
  have hEne : E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEle
  have hEreal : E.toReal ≤ L ^ ((d : ℝ) / 2) * Gb := by
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hEle
  have hcoord : ∀ i, (eLpNorm (fun x => v.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal ≤ E.toReal := by
    intro i
    refine ENNReal.toReal_mono hEne (eLpNorm_mono_ae (v.gradMemL2 i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_))
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (show 0 ≤ eucNorm (v.grad x) from Real.sqrt_nonneg _)]
    unfold eucNorm
    refine Real.abs_le_sqrt ?_
    unfold vecNormSq vecDot
    calc v.grad x i ^ 2 = v.grad x i * v.grad x i := sq _
      _ ≤ ∑ j, v.grad x j * v.grad x j :=
        Finset.single_le_sum (f := fun j => v.grad x j * v.grad x j)
          (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
  have hsum : ∑ i : Fin d, (eLpNorm (fun x => v.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal ≤
      d * E.toReal := by
    calc _ ≤ ∑ _i : Fin d, E.toReal := Finset.sum_le_sum fun i _ => hcoord i
      _ = _ := by simp
  have hP := unitMeanZeroPoincareConst_nonneg d
  have hreal : (eLpNorm v.subAverage.toFun 2 (volumeMeasureOn (axisCube z L))).toReal ≤
      L ^ ((d : ℝ) / 2) * (unitMeanZeroPoincareConst d * d * L * Gb) := by
    refine raw.trans ?_
    calc unitMeanZeroPoincareConst d * L * ∑ i : Fin d,
          (eLpNorm (fun x => v.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal
        ≤ unitMeanZeroPoincareConst d * L * (d * E.toReal) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ unitMeanZeroPoincareConst d * L * (d * (L ^ ((d : ℝ) / 2) * Gb)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEreal (by positivity))
            (by positivity)
      _ = _ := by ring
  have hne : eLpNorm v.subAverage.toFun 2 (volume.restrict (axisCube z L)) ≠ ⊤ :=
    v.subAverage.memL2.eLpNorm_ne_top
  exact (ENNReal.le_ofReal_iff_toReal_le hne (by positivity)).2 hreal

/-- Negating a weak solution negates the right-hand side. -/
theorem linf_dgi_neg {a : CoeffField d} {U : Set (Vec d)} {u : H1Function U} {f : Vec d → ℝ}
    (h : IsWeakSolutionOn a U u f (fun _ => 0)) :
    IsWeakSolutionOn a U (-u) (fun x => -f x) (fun _ => 0) := by
  intro φ
  have h1 := h φ
  have hg : (-u).grad = fun x => -u.grad x := by
    funext x
    simp
  rw [hg]
  simp only [matVecMul_neg, vecDot_neg_left, MeasureTheory.integral_neg, neg_mul, vecDot_zero_left,
    integral_zero, add_zero] at h1 ⊢
  rw [h1]

/-- The two-sided sup bound on the half cube from the one-sided De Giorgi estimate. -/
theorem linf_dgi_one_sided {C0 : ℝ} {lam Lam : ℝ} (z : Vec d) {L F Bb : ℝ} (hL : 0 < L)
    (hF : 0 ≤ F) (hBb : 0 ≤ Bb) (hlam : 0 < lam)
    (hpos : 0 ≤ C0 * (Lam / lam) ^ deGiorgiPower d) (f' : Vec d → ℝ)
    (w : H1Function (axisCube z L))
    (hfm : AEStronglyMeasurable f' (volume.restrict (axisCube z L)))
    (hf : ∀ᵐ x ∂volume.restrict (axisCube z L), |f' x| ≤ F)
    (hw : eLpNorm w.toFun 2 (volume.restrict (axisCube z L)) ≤
      ENNReal.ofReal (L ^ ((d : ℝ) / 2) * Bb))
    (hmain : eLpNorm (fun x => max (w.toFun x) 0) ⊤ (volume.restrict (halfCube z L)) ≤
        ENNReal.ofReal (C0 * (Lam / lam) ^ deGiorgiPower d) *
          (ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) *
              eLpNorm (fun x => max (w.toFun x) 0) 2 (volume.restrict (axisCube z L)) +
            ENNReal.ofReal (L ^ 2 / lam) * eLpNorm f' ⊤ (volume.restrict (axisCube z L)) +
            ENNReal.ofReal (L / lam) *
              eLpNorm (fun x => eucNorm ((fun _ : Vec d => (0 : Vec d)) x)) ⊤
                (volume.restrict (axisCube z L)))) :
    ∀ᵐ x ∂volume.restrict (halfCube z L),
      max (w.toFun x) 0 ≤ C0 * (Lam / lam) ^ deGiorgiPower d * (Bb + L ^ 2 / lam * F) := by
  have hwm : AEStronglyMeasurable w.toFun (volume.restrict (axisCube z L)) :=
    w.memL2.aestronglyMeasurable
  have hmaxm : AEStronglyMeasurable (fun x => max (w.toFun x) 0) (volume.restrict (axisCube z L)) :=
    (hwm.aemeasurable.max aemeasurable_const).aestronglyMeasurable
  have e1 : eLpNorm (fun x => max (w.toFun x) 0) 2 (volume.restrict (axisCube z L)) ≤
      ENNReal.ofReal (L ^ ((d : ℝ) / 2) * Bb) := by
    refine le_trans (eLpNorm_mono_ae hmaxm (Filter.Eventually.of_forall fun x => ?_)) hw
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have e2 : eLpNorm f' ⊤ (volume.restrict (axisCube z L)) ≤ ENNReal.ofReal F := by
    rw [eLpNorm_exponent_top hfm]
    exact eLpNormEssSup_le_of_ae_bound (by simpa only [Real.norm_eq_abs] using hf)
  have e3 : eLpNorm (fun x => eucNorm ((fun _ : Vec d => (0 : Vec d)) x)) ⊤
      (volume.restrict (axisCube z L)) = 0 := by
    have : (fun x => eucNorm ((fun _ : Vec d => (0 : Vec d)) x)) = fun _ => (0 : ℝ) := by
      funext x
      simp [eucNorm, vecNormSq, vecDot]
    rw [this]
    exact eLpNorm_zero
  have hL' : ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) * ENNReal.ofReal (L ^ ((d : ℝ) / 2) * Bb) =
      ENNReal.ofReal Bb := by
    have h1 : L ^ (-(d : ℝ) / 2) * L ^ ((d : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hL, show -(d : ℝ) / 2 + d / 2 = 0 by ring, Real.rpow_zero]
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, h1, one_mul]
  have hbound : eLpNorm (fun x => max (w.toFun x) 0) ⊤ (volume.restrict (halfCube z L)) ≤
      ENNReal.ofReal (C0 * (Lam / lam) ^ deGiorgiPower d * (Bb + L ^ 2 / lam * F)) := by
    refine hmain.trans ?_
    rw [ENNReal.ofReal_mul hpos, e3, mul_zero, add_zero]
    refine mul_le_mul' le_rfl ?_
    calc _ ≤ ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) * ENNReal.ofReal (L ^ ((d : ℝ) / 2) * Bb) +
          ENNReal.ofReal (L ^ 2 / lam) * ENNReal.ofReal F := by gcongr
      _ = _ := by
        rw [hL', ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hBb (by positivity)]
  have hmax2 : AEStronglyMeasurable (fun x => max (w.toFun x) 0) (volume.restrict (halfCube z L)) :=
    hmaxm.mono_measure (Measure.restrict_mono (halfCube_subset z L) le_rfl)
  rw [eLpNorm_exponent_top hmax2] at hbound
  have hB : 0 ≤ C0 * (Lam / lam) ^ deGiorgiPower d * (Bb + L ^ 2 / lam * F) :=
    mul_nonneg hpos (by positivity)
  filter_upwards [enorm_ae_le_eLpNormEssSup (fun x => max (w.toFun x) 0)
    (volume.restrict (halfCube z L))] with x hx
  have h3 := hx.trans hbound
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (le_max_right _ _)] at h3
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 h3

theorem linf_dgi_kernel_integral {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} :
    ∫ w, a16_kernel d h η w = ∫ w, η w := by
  unfold a16_kernel
  rw [integral_const_mul, MeasureTheory.Measure.integral_comp_smul_of_nonneg
    (volume : Measure (Vec d)) η h⁻¹ (hR := inv_nonneg.2 hh.le)]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- The mollification of the zero extension of `u` at `x` differs from `c` by at most
`A h^{-d}` times the `L¹` distance of `u` to `c` on `Q`, when the sup-ball of radius `h` around
`x` lies in `Q` up to a null set. -/
theorem linf_dgi_moll_sub {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} {A : ℝ} (hηc : Continuous η)
    (hA : ∀ w, |η w| ≤ A) (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {Q : Set (Vec d)} (hQm : MeasurableSet Q)
    {x : Vec d} (hball : ∀ᵐ w ∂(volume : Measure (Vec d)), w ∈ Metric.closedBall x h → w ∈ Q)
    {u : Vec d → ℝ} {c : ℝ} (hu : IntegrableOn (fun w => u w - c) Q) :
    |l2a_moll d h η (Q.indicator u) x - c| ≤ A * (h⁻¹) ^ d * ∫ w in Q, |u w - c| := by
  set k : Vec d → ℝ := fun w => a16_kernel d h η (x - w) with hk
  have hk0 : ∀ w, 0 ≤ k w := fun w =>
    mul_nonneg (pow_nonneg (inv_nonneg.2 hh.le) _) (hη0 _)
  have hkz : ∀ w, w ∉ Metric.closedBall x h → k w = 0 := by
    intro w hw
    rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hw
    have : h < ‖x - w‖ := by rwa [← norm_neg, neg_sub]
    exact l2a_kernel_eq_zero_of_norm hh hηs this
  have hkb : ∀ w, k w ≤ A * (h⁻¹) ^ d := fun w =>
    (le_abs_self _).trans (a16_kernel_abs_le hh hA _)
  have hkc : Continuous k := (a16_kernel_continuous hηc).comp (continuous_const.sub continuous_id)
  have hkcs : HasCompactSupport k :=
    (l2a_kernel_compact hh hηs).comp_homeomorph (Homeomorph.subLeft x)
  have hkI : Integrable k := hkc.integrable_of_hasCompactSupport hkcs
  have hkint : ∫ w, k w = 1 := by
    have := integral_sub_left_eq_self (fun t => a16_kernel d h η t) (volume : Measure (Vec d)) x
    rw [hk]
    simp only
    rw [this, linf_dgi_kernel_integral hh, hη1]
  set g : Vec d → ℝ := fun w => k w * Q.indicator (fun w => u w - c) w with hg
  have hind : Integrable (Q.indicator (fun w => u w - c)) := (integrable_indicator_iff hQm).2 hu
  have hgI : Integrable g := by
    refine Integrable.mono' (hind.norm.const_mul (A * (h⁻¹) ^ d)) ?_ (Filter.Eventually.of_forall
      fun w => ?_)
    · exact hkc.aestronglyMeasurable.mul hind.aestronglyMeasurable
    · simp only [hg, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hk0 w)]
      exact mul_le_mul_of_nonneg_right (hkb w) (abs_nonneg _)
  have hmoll : l2a_moll d h η (Q.indicator u) x = (∫ w, g w) + c := by
    unfold l2a_moll
    have hae : (fun y => a16_kernel d h η (x - y) * Q.indicator u y) =ᵐ[volume]
        fun w => g w + c * k w := by
      filter_upwards [hball] with w hw
      by_cases hwQ : w ∈ Q
      · simp only [hg, hk, Set.indicator_of_mem hwQ]
        ring
      · have : k w = 0 := hkz w (fun hc => hwQ (hw hc))
        simp only [hg, Set.indicator_of_notMem hwQ, this, mul_zero, add_zero]
    rw [integral_congr_ae hae, integral_add hgI (hkI.const_mul c), integral_const_mul, hkint,
      mul_one]
  rw [hmoll, add_sub_cancel_right]
  have hnorm : ‖∫ w, g w‖ ≤ ∫ w, A * (h⁻¹) ^ d * |Q.indicator (fun w => u w - c) w| := by
    refine norm_integral_le_of_norm_le (hind.norm.const_mul (A * (h⁻¹) ^ d)) ?_
    refine Filter.Eventually.of_forall fun w => ?_
    simp only [hg, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hk0 w)]
    exact mul_le_mul_of_nonneg_right (hkb w) (abs_nonneg _)
  rw [Real.norm_eq_abs] at hnorm
  refine hnorm.trans (le_of_eq ?_)
  rw [integral_const_mul]
  congr 1
  have : (fun w => |Q.indicator (fun w => u w - c) w|) = Q.indicator (fun w => |u w - c|) := by
    funext w
    by_cases hw : w ∈ Q <;> simp [hw]
  rw [this, integral_indicator hQm]

theorem linf_dgi_null_coord (i : Fin d) (c : ℝ) : volume {w : Vec d | w i = c} = 0 := by
  classical
  have : {w : Vec d | w i = c} = Set.pi Set.univ (Function.update (fun _ => (Set.univ : Set ℝ)) i ({c} : Set ℝ)) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h j
      by_cases hj : j = i
      · subst hj; simpa using h
      · simp [Function.update_of_ne hj]
    · intro h
      simpa using h i
  rw [this, volume_pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- For `x` in the cell `y + □_n`, the closed sup-ball of radius `3^n` lies in the cube
`y + cu_{n+1}` up to a null set. -/
theorem linf_dgi_ball_ae (n : ℕ) (y : Vec d) {x : Vec d} (hx : x ∈ l2b_cell y n) :
    ∀ᵐ w ∂(volume : Measure (Vec d)),
      w ∈ Metric.closedBall x ((3 : ℝ) ^ n) → w ∈ shiftCube y ((n : ℤ) + 1) := by
  have hnull : volume (⋃ i : Fin d, {w : Vec d | w i = y i - (3 : ℝ) ^ n * (3 / 2)}) = 0 :=
    (measure_iUnion_null fun i => linf_dgi_null_coord i _)
  have hn : (0 : ℝ) < 3 ^ n := by positivity
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with w hw hwb
  rw [rc_mem_shiftCube]
  intro i
  have h3 : (3 : ℝ) ^ ((n : ℤ) + 1) = 3 * 3 ^ n := by
    rw [zpow_add_one₀ (by norm_num), zpow_natCast, mul_comm]
  rw [h3]
  have hb : |w i - x i| ≤ 3 ^ n := by
    have := (dist_pi_le_iff hn.le).1 (Metric.mem_closedBall.1 hwb) i
    rwa [Real.dist_eq] at this
  rw [abs_le] at hb
  have hxi := (l2b_mem_cell.1 hx) i
  have hne : w i ≠ y i - (3 : ℝ) ^ n * (3 / 2) := fun h => hw (Set.mem_iUnion.2 ⟨i, h⟩)
  rw [abs_lt]
  have hlow : y i - (3 : ℝ) ^ n * (3 / 2) ≤ w i := by linarith only [hb.1, hxi.1]
  constructor
  · rcases lt_or_eq_of_le hlow with h | h
    · linarith only [h]
    · exact absurd h.symm hne
  · linarith only [hb.2, hxi.2]

theorem linf_dgi_sub_apply (z : Vec d) {L : ℝ} (v : H1Function (axisCube z L))
    [IsFiniteMeasure (volumeMeasureOn (axisCube z L))] (x : Vec d) :
    v.subAverage.toFun x = v.toFun x - integralAverage (axisCube z L) v := by
  have := H1Function.subAverage_apply v x
  exact this

/-- The `L¹` norm of a function on the cube by its `L²` norm. -/
theorem linf_dgi_l1_le (z : Vec d) {L : ℝ} (hL : 0 < L) {w : Vec d → ℝ}
    (hw : MemLp w 2 (volume.restrict (axisCube z L))) {B : ℝ}
    (hB : eLpNorm w 2 (volume.restrict (axisCube z L)) ≤ ENNReal.ofReal (L ^ ((d : ℝ) / 2) * B))
    (hB0 : 0 ≤ B) :
    ∫ x in axisCube z L, |w x| ≤ L ^ d * B := by
  have hvol : volume (axisCube z L) = ENNReal.ofReal (L ^ d) := linf_dgi_volume z hL.le
  have hfin : IsFiniteMeasure (volume.restrict (axisCube z L)) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.ofReal_lt_top⟩
  have hint : Integrable w (volume.restrict (axisCube z L)) := hw.integrable one_le_two
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num)
    hw.aestronglyMeasurable
  rw [Measure.restrict_apply_univ, hvol] at h1
  have hsq : ENNReal.ofReal (L ^ d) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) =
      ENNReal.ofReal (L ^ ((d : ℝ) / 2)) := by
    simp only [ENNReal.toReal_one, ENNReal.toReal_ofNat]
    rw [show (1 : ℝ) / 1 - 1 / 2 = 1 / 2 by norm_num,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    have : (L ^ d) ^ (1 / 2 : ℝ) = L ^ ((d : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
      ring_nf
    rw [this]
  rw [hsq] at h1
  have h2 : eLpNorm w 1 (volume.restrict (axisCube z L)) ≤ ENNReal.ofReal (L ^ d * B) := by
    refine h1.trans ?_
    calc _ ≤ ENNReal.ofReal (L ^ ((d : ℝ) / 2) * B) * ENNReal.ofReal (L ^ ((d : ℝ) / 2)) :=
          mul_le_mul' hB le_rfl
      _ = ENNReal.ofReal (L ^ ((d : ℝ) / 2) * B * L ^ ((d : ℝ) / 2)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ = _ := by
        congr 1
        have : L ^ ((d : ℝ) / 2) * L ^ ((d : ℝ) / 2) = L ^ d := by
          rw [← Real.rpow_add hL, add_halves, Real.rpow_natCast]
        calc L ^ ((d : ℝ) / 2) * B * L ^ ((d : ℝ) / 2) =
            (L ^ ((d : ℝ) / 2) * L ^ ((d : ℝ) / 2)) * B := by ring
          _ = _ := by rw [this]
  have h3 : ENNReal.ofReal (∫ x in axisCube z L, ‖w x‖) = eLpNorm w 1 (volume.restrict (axisCube z L)) := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hint, eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable]
  rw [← h3] at h2
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
  simpa only [Real.norm_eq_abs] using this

/-- The interior De Giorgi step on an axis cube of side `3h`, for a set `E` of points whose
`h`-ball lies in the cube up to a null set. -/
theorem linf_dgi_core (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {lam Lam : ℝ} {a : CoeffField d} (z : Vec d) {h L : ℝ}, 0 < h → L = 3 * h → 0 < lam →
      IsEllipticFieldOn lam Lam (axisCube z L) a →
      ∀ {E : Set (Vec d)}, MeasurableSet E → E ⊆ halfCube z L →
      (∀ x ∈ E, ∀ᵐ w ∂(volume : Measure (Vec d)),
        w ∈ Metric.closedBall x h → w ∈ axisCube z L) →
      ∀ {η : Vec d → ℝ} {Bη : ℝ}, Continuous η → (∀ w, |η w| ≤ Bη) → (∀ w, 0 ≤ η w) →
        ∫ w, η w = 1 → (∀ w, (∃ i, 1 < |w i|) → η w = 0) →
      ∀ (f : Vec d → ℝ) (v : H1Function (axisCube z L)),
        IsWeakSolutionOn a (axisCube z L) v f (fun _ => 0) →
      ∀ {F Gb : ℝ}, 0 ≤ F → 0 ≤ Gb →
        AEStronglyMeasurable f (volume.restrict (axisCube z L)) →
        (∀ᵐ x ∂volume.restrict (axisCube z L), |f x| ≤ F) →
        lpBar (axisCube z L) 2 (fun x => eucNorm (v.grad x)) ≤ ENNReal.ofReal Gb →
        ∀ᵐ x ∂volume.restrict E,
          |v.toFun x - l2a_moll d h η ((axisCube z L).indicator v.toFun) x| ≤
            C * (1 + Bη) * (Lam / lam) ^ deGiorgiPower d * (h * Gb + h ^ 2 / lam * F) := by
  obtain ⟨C0, hC0, H⟩ := deGiorgi_interior_bound hd
  set P := unitMeanZeroPoincareConst d with hP
  have hP0 : 0 ≤ P := unitMeanZeroPoincareConst_nonneg d
  refine ⟨(C0 + 3 ^ d) * (3 * P * d + 9), by positivity, ?_⟩
  intro lam Lam a z h L hh hL3 hlam hEll E hEm hEsub hEball η Bη hηc hηb hη0 hη1 hηs f v hv F Gb hF hGb hfm hf
    hG
  have hL : 0 < L := by rw [hL3]; positivity
  have hvol : volume (axisCube z L) = ENNReal.ofReal (L ^ d) := linf_dgi_volume z hL.le
  have hfinQ : volume (axisCube z L) ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  have hfm' : IsFiniteMeasure (volumeMeasureOn (axisCube z L)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfinQ⟩
  have hx0 : (fun i => z i + L / 2) ∈ axisCube z L := by
    simp only [axisCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
    intro i
    constructor <;> linarith only [hL]
  obtain ⟨-, hlamLam, -, -⟩ := hEll.2 _ hx0
  have hq : 1 ≤ Lam / lam := by rw [le_div_iff₀ hlam]; linarith only [hlamLam]
  have hqpos : 0 < Lam / lam := lt_of_lt_of_le one_pos hq
  have hR1 : 1 ≤ (Lam / lam) ^ deGiorgiPower d := by
    refine Real.one_le_rpow hq ?_
    unfold deGiorgiPower
    have h2 := two_lt_sobStar hd
    have : 0 < 1 - 2 / sobStar d := by
      have : 2 / sobStar d < 1 := by
        rw [div_lt_one (by linarith only [h2])]; exact h2
      linarith only [this]
    exact (inv_pos.2 this).le
  have hR0 : 0 ≤ (Lam / lam) ^ deGiorgiPower d := by linarith only [hR1]
  set R := (Lam / lam) ^ deGiorgiPower d with hRdef
  set u1 := v.subAverage with hu1
  set c₀ := integralAverage (axisCube z L) v with hc₀
  have hu1fun : ∀ x, u1.toFun x = v.toFun x - c₀ := fun x => linf_dgi_sub_apply z v x
  have hu1w : IsWeakSolutionOn a (axisCube z L) u1 f (fun _ => 0) := by
    intro φ
    have := hv φ
    simpa only [hu1, H1Function.grad_subAverage] using this
  set Bb : ℝ := P * d * L * Gb with hBb
  have hBb0 : 0 ≤ Bb := by positivity
  have hw1 : eLpNorm u1.toFun 2 (volume.restrict (axisCube z L)) ≤
      ENNReal.ofReal (L ^ ((d : ℝ) / 2) * Bb) := linf_dgi_poincare z hL v hGb hG
  have hw2 : eLpNorm (-u1).toFun 2 (volume.restrict (axisCube z L)) ≤
      ENNReal.ofReal (L ^ ((d : ℝ) / 2) * Bb) := by
    have : (-u1).toFun = fun x => -u1.toFun x := by funext x; simp
    rw [this]
    exact (eLpNorm_neg u1.toFun 2 _).le.trans hw1
  have hgm0 : AEStronglyMeasurable (fun _ : Vec d => (0 : Vec d))
      (volume.restrict (axisCube z L)) := aestronglyMeasurable_const
  have hfn : ∀ᵐ x ∂volume.restrict (axisCube z L), |-f x| ≤ F := by
    filter_upwards [hf] with x hx; rwa [abs_neg]
  have hpos : 0 ≤ C0 * R := by positivity
  have r1 := linf_dgi_one_sided z hL hF hBb0 hlam hpos f u1 hfm hf hw1
    (H z hL hEll f (fun _ => 0) hgm0 u1 hu1w)
  have r2 := linf_dgi_one_sided z hL hF hBb0 hlam hpos (fun x => -f x) (-u1) hfm.neg hfn hw2
    (H z hL hEll (fun x => -f x) (fun _ => 0) hgm0 (-u1) (linf_dgi_neg hu1w))
  have hsup : ∀ᵐ x ∂volume.restrict E, |v.toFun x - c₀| ≤ C0 * R * (Bb + L ^ 2 / lam * F) := by
    refine ae_restrict_of_ae_restrict_of_subset hEsub ?_
    filter_upwards [r1, r2] with x h1 h2
    have hneg : (-u1).toFun x = -u1.toFun x := by simp
    rw [hneg] at h2
    rw [← hu1fun]
    exact abs_le.2 ⟨by linarith only [le_max_left (-u1.toFun x) 0, h2],
      le_trans (le_max_left _ _) h1⟩
  have hl1 : ∫ x in axisCube z L, |u1.toFun x| ≤ L ^ d * Bb :=
    linf_dgi_l1_le z hL u1.memL2 hw1 hBb0
  have hQm : MeasurableSet (axisCube z L) := (isOpen_axisCube z L).measurableSet
  have hu1int : IntegrableOn (fun w => v.toFun w - c₀) (axisCube z L) := by
    have : IsFiniteMeasure (volume.restrict (axisCube z L)) := hfm'
    have h := u1.memL2.integrable one_le_two
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    exact hu1fun x
  filter_upwards [hsup, ae_restrict_mem hEm] with x hx hxE
  have hBη : 0 ≤ Bη := (abs_nonneg _).trans (hηb 0)
  have hm := linf_dgi_moll_sub hh hηc hηb hη0 hη1 hηs hQm (hEball x hxE) hu1int
  have hint_eq : ∫ w in axisCube z L, |v.toFun w - c₀| = ∫ w in axisCube z L, |u1.toFun w| := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hu1fun]
  rw [hint_eq] at hm
  have hhd : (h⁻¹) ^ d * L ^ d = 3 ^ d := by
    rw [← mul_pow, hL3]
    congr 1
    field_simp
  have hm2 : |l2a_moll d h η ((axisCube z L).indicator v.toFun) x - c₀| ≤ Bη * 3 ^ d * Bb := by
    refine hm.trans ?_
    calc Bη * (h⁻¹) ^ d * ∫ w in axisCube z L, |u1.toFun w|
        ≤ Bη * (h⁻¹) ^ d * (L ^ d * Bb) :=
          mul_le_mul_of_nonneg_left hl1 (by positivity)
      _ = Bη * ((h⁻¹) ^ d * L ^ d) * Bb := by ring
      _ = _ := by rw [hhd]
  have hsplit : |v.toFun x - l2a_moll d h η ((axisCube z L).indicator v.toFun) x| ≤
      |v.toFun x - c₀| + |l2a_moll d h η ((axisCube z L).indicator v.toFun) x - c₀| := by
    have := abs_add_le (v.toFun x - c₀) (c₀ - l2a_moll d h η ((axisCube z L).indicator v.toFun) x)
    rw [abs_sub_comm c₀] at this
    simpa using this
  have hX : 0 ≤ h * Gb := by positivity
  have hY : 0 ≤ h ^ 2 / lam * F := by positivity
  have hBbh : Bb = 3 * P * d * (h * Gb) := by rw [hBb, hL3]; ring
  have hLh : L ^ 2 / lam * F = 9 * (h ^ 2 / lam * F) := by rw [hL3]; ring
  have hk0 : 0 ≤ 3 * P * d + 9 := by positivity
  have h3d : 0 ≤ (3 : ℝ) ^ d := by positivity
  rw [hLh, hBbh] at hx
  rw [hBbh] at hm2
  have hRX : 0 ≤ R * (h * Gb + h ^ 2 / lam * F) := by positivity
  calc |v.toFun x - l2a_moll d h η ((axisCube z L).indicator v.toFun) x|
      ≤ C0 * R * (3 * P * d * (h * Gb) + 9 * (h ^ 2 / lam * F)) +
        Bη * 3 ^ d * (3 * P * d * (h * Gb)) := hsplit.trans (add_le_add hx hm2)
    _ ≤ (C0 + 3 ^ d) * (3 * P * d + 9) * (1 + Bη) * R * (h * Gb + h ^ 2 / lam * F) := by
        have t1 : C0 * R * (3 * P * d * (h * Gb) + 9 * (h ^ 2 / lam * F)) ≤
            C0 * (3 * P * d + 9) * R * (h * Gb + h ^ 2 / lam * F) := by
          have : 3 * P * d * (h * Gb) + 9 * (h ^ 2 / lam * F) ≤
              (3 * P * d + 9) * (h * Gb + h ^ 2 / lam * F) := by
            have : 0 ≤ 3 * P * d * (h ^ 2 / lam * F) := by positivity
            have : 0 ≤ 9 * (h * Gb) := by positivity
            nlinarith only [this, ‹0 ≤ 3 * P * d * (h ^ 2 / lam * F)›]
          calc _ ≤ C0 * R * ((3 * P * d + 9) * (h * Gb + h ^ 2 / lam * F)) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
        have t2 : Bη * 3 ^ d * (3 * P * d * (h * Gb)) ≤
            Bη * 3 ^ d * (3 * P * d + 9) * R * (h * Gb + h ^ 2 / lam * F) := by
          have e1 : 3 * P * d * (h * Gb) ≤ (3 * P * d + 9) * (h * Gb + h ^ 2 / lam * F) := by
            nlinarith only [hX, hY, hk0, hP0, mul_nonneg hk0 hY]
          have e2 : (3 * P * d + 9) * (h * Gb + h ^ 2 / lam * F) ≤
              (3 * P * d + 9) * (R * (h * Gb + h ^ 2 / lam * F)) := by
            refine mul_le_mul_of_nonneg_left ?_ hk0
            nlinarith only [hR1, hX, hY]
          calc Bη * 3 ^ d * (3 * P * d * (h * Gb)) ≤
              Bη * 3 ^ d * ((3 * P * d + 9) * (R * (h * Gb + h ^ 2 / lam * F))) :=
                mul_le_mul_of_nonneg_left (e1.trans e2) (by positivity)
            _ = _ := by ring
        have t3 : C0 * (3 * P * d + 9) * R * (h * Gb + h ^ 2 / lam * F) ≤
            C0 * (3 * P * d + 9) * (1 + Bη) * R * (h * Gb + h ^ 2 / lam * F) := by
          have : 0 ≤ C0 * (3 * P * d + 9) * (R * (h * Gb + h ^ 2 / lam * F)) := by positivity
          nlinarith only [this, hBη]
        nlinarith only [t1, t2, t3, mul_nonneg hBη (mul_nonneg (mul_nonneg hC0.le hk0) hRX),
          mul_nonneg (mul_nonneg h3d hk0) hRX, mul_nonneg hBη (mul_nonneg (mul_nonneg h3d hk0) hRX)]
    _ = _ := by ring

/-- **Interior De Giorgi step**: on the cell `z + □_n`, `z ∈ 3^n ℤ^d`,
`|v - η_n ∗ v|` is bounded by the gradient on `z + □_{n+1}` with the ellipticity ratio. -/
theorem linf_dg_interior [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {lam Lam : ℝ} {a : CoeffField d} (n : ℕ) (k : Fin d → ℤ), 0 < lam →
      IsEllipticFieldOn lam Lam (shiftCube (l2b_pt n k) ((n : ℤ) + 1)) a →
      ∀ {η : Vec d → ℝ} {Bη : ℝ}, Continuous η → (∀ w, |η w| ≤ Bη) → (∀ w, 0 ≤ η w) →
        ∫ w, η w = 1 → (∀ w, (∃ i, 1 < |w i|) → η w = 0) →
      ∀ (f : Vec d → ℝ) (v : H1Function (shiftCube (l2b_pt n k) ((n : ℤ) + 1))),
        IsWeakSolutionOn a (shiftCube (l2b_pt n k) ((n : ℤ) + 1)) v f (fun _ => 0) →
      ∀ {F Gb : ℝ}, 0 ≤ F → 0 ≤ Gb →
        AEStronglyMeasurable f (volume.restrict (shiftCube (l2b_pt n k) ((n : ℤ) + 1))) →
        (∀ᵐ x ∂volume.restrict (shiftCube (l2b_pt n k) ((n : ℤ) + 1)), |f x| ≤ F) →
        lpBar (shiftCube (l2b_pt n k) ((n : ℤ) + 1)) 2 (fun x => eucNorm (v.grad x)) ≤
          ENNReal.ofReal Gb →
        ∀ᵐ x ∂volume.restrict (l2b_cell (l2b_pt n k) n),
          |v.toFun x - l2a_moll d ((3 : ℝ) ^ n) η
              ((shiftCube (l2b_pt n k) ((n : ℤ) + 1)).indicator v.toFun) x| ≤
            C * (1 + Bη) * (Lam / lam) ^ deGiorgiPower d *
              ((3 : ℝ) ^ n * Gb + ((3 : ℝ) ^ n) ^ 2 / lam * F) := by
  obtain ⟨C, hC, hmain⟩ := linf_dgi_core hd
  refine ⟨C, hC, ?_⟩
  intro lam Lam a n k hlam hEll η Bη hηc hηb hη0 hη1 hηs f v hv F Gb hF hGb hfm hf hG
  have hS := rc_shiftCube_eq_axisCube (l2b_pt n k) ((n : ℤ) + 1)
  have hball : ∀ x ∈ l2b_cell (l2b_pt n k) n, ∀ᵐ w ∂(volume : Measure (Vec d)),
      w ∈ Metric.closedBall x ((3 : ℝ) ^ n) → w ∈ shiftCube (l2b_pt n k) ((n : ℤ) + 1) :=
    fun x hx => linf_dgi_ball_ae n _ hx
  have h3 : (3 : ℝ) ^ ((n : ℤ) + 1) = 3 * (3 : ℝ) ^ n := by
    rw [zpow_add_one₀ (by norm_num), zpow_natCast, mul_comm]
  have hsub : l2b_cell (l2b_pt n k) n ⊆
      halfCube (fun i => l2b_pt n k i - (3 : ℝ) ^ ((n : ℤ) + 1) / 2) ((3 : ℝ) ^ ((n : ℤ) + 1)) := by
    intro x hx
    have hxi := l2b_mem_cell.1 hx
    simp only [halfCube, axisCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo,
      Pi.add_apply]
    intro i
    have := hxi i
    rw [h3]
    constructor <;> linarith only [this.1, this.2, (by positivity : (0 : ℝ) < 3 ^ n)]
  generalize shiftCube (l2b_pt n k) ((n : ℤ) + 1) = S at *
  subst hS
  exact hmain _ (by positivity) h3 hlam hEll (l2b_cell_measurable _ _) hsub hball hηc hηb hη0 hη1
    hηs f v hv hF hGb hfm hf hG

/-- Satisfiability: the zero solution on the cube `cu_1` with identity coefficients, zero right-hand
side and the standard bump profile meets every non-law hypothesis of `linf_dg_interior`. -/
example : ∃ (η : Vec 2 → ℝ) (Bη : ℝ), Continuous η ∧ (∀ w, |η w| ≤ Bη) ∧ (∀ w, 0 ≤ η w) ∧
    ∫ w, η w = 1 ∧ (∀ w, (∃ i, 1 < |w i|) → η w = 0) ∧
    ∀ᵐ x ∂volume.restrict (l2b_cell (l2b_pt 0 (0 : Fin 2 → ℤ)) 0),
      |(0 : H1Function (shiftCube (l2b_pt 0 (0 : Fin 2 → ℤ)) (((0 : ℕ) : ℤ) + 1))).toFun x -
          l2a_moll 2 ((3 : ℝ) ^ 0) η
            ((shiftCube (l2b_pt 0 (0 : Fin 2 → ℤ)) (((0 : ℕ) : ℤ) + 1)).indicator
              (0 : H1Function (shiftCube (l2b_pt 0 (0 : Fin 2 → ℤ)) (((0 : ℕ) : ℤ) + 1))).toFun) x| ≤
        (linf_dg_interior (d := 2) le_rfl).choose * (1 + Bη) * ((1 : ℝ) / 1) ^ deGiorgiPower 2 *
          ((3 : ℝ) ^ 0 * 0 + ((3 : ℝ) ^ 0) ^ 2 / 1 * 0) := by
  obtain ⟨B, hB⟩ := (li1_bump_contDiff 2).continuous.bounded_above_of_compact_support
    (li1_bump_compact 2)
  refine ⟨li1_bump 2, B, (li1_bump_contDiff 2).continuous, fun w => ?_, li1_bump_nonneg 2,
    li1_bump_integral 2, ?_, ?_⟩
  · simpa only [Real.norm_eq_abs] using hB w
  · rintro w ⟨i, hi⟩
    by_contra hne
    have h1 := li1_bump_norm_lt hne
    have h2 : |w i| ≤ ‖w‖ := by simpa using norm_le_pi_norm w i
    linarith only [h1, h2, hi]
  · have hSm := rc_measurableSet_shiftCube (l2b_pt 0 (0 : Fin 2 → ℤ)) (((0 : ℕ) : ℤ) + 1)
    have hEll : IsEllipticFieldOn (1 : ℝ) 1 (shiftCube (l2b_pt 0 (0 : Fin 2 → ℤ)) (((0 : ℕ) : ℤ) + 1))
        (fun _ => (1 : Mat 2)) :=
      ⟨measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ =>
        Measurable.ite hSm measurable_const measurable_const,
        fun _ _ => Homogenization.isEllipticMatrix_one_one le_rfl⟩
    have hz : IsWeakSolutionOn (fun _ => (1 : Mat 2))
        (shiftCube (l2b_pt 0 (0 : Fin 2 → ℤ)) (((0 : ℕ) : ℤ) + 1))
        (0 : H1Function (shiftCube (l2b_pt 0 (0 : Fin 2 → ℤ)) (((0 : ℕ) : ℤ) + 1)))
        (fun _ => 0) (fun _ => 0) := by
      intro φ
      have h0 : ∀ x, (0 : H1Function (shiftCube (l2b_pt 0 (0 : Fin 2 → ℤ)) (((0 : ℕ) : ℤ) + 1))).grad x
          = 0 := fun _ => rfl
      simp [vecDot, matVecMul, h0]
    exact (linf_dg_interior (d := 2) le_rfl).choose_spec.2 0 0 one_pos hEll
      (li1_bump_contDiff 2).continuous (fun w => by simpa only [Real.norm_eq_abs] using hB w)
      (li1_bump_nonneg 2) (li1_bump_integral 2) (by
        rintro w ⟨i, hi⟩
        by_contra hne
        have h1 := li1_bump_norm_lt hne
        have h2 : |w i| ≤ ‖w‖ := by simpa using norm_le_pi_norm w i
        linarith only [h1, h2, hi]) (fun _ => 0) 0 hz le_rfl le_rfl aestronglyMeasurable_const
      (Filter.Eventually.of_forall fun x => by simp) (by
        have : (fun x => eucNorm ((0 : H1Function (shiftCube (l2b_pt 0 (0 : Fin 2 → ℤ))
            (((0 : ℕ) : ℤ) + 1))).grad x)) = fun _ => (0 : ℝ) := by
          funext x
          simp [eucNorm, vecNormSq, vecDot, show ∀ y, (0 : H1Function (shiftCube (l2b_pt 0
            (0 : Fin 2 → ℤ)) (((0 : ℕ) : ℤ) + 1))).grad y = 0 from fun _ => rfl]
        rw [this]
        simp [lpBar])

end SuperdiffusionCLT.Section7
