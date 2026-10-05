/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Sobolev
public import SuperdiffusionCLT.Section7.Prereq.L2BoundaryC
public import Homogenization.Sobolev.CubeEmbedding.GagliardoNirenbergSobolevFiniteP
public import Mathlib.Order.CompletePartialOrder

/-!
# The Sobolev inequality `W^{1,p}_0 ⊂ L^q` for `H¹₀` functions of a bounded set

For `v ∈ H¹₀(W)` with `W` bounded, `1 < p < d`, `q⁻¹ = p⁻¹ - d⁻¹`:
`‖v‖_{L^q(W)} ≤ C Σ_i ‖∂_i v‖_{L^p(W)}`, with `C` depending only on `(d, p)`.  The proof applies
the Gagliardo-Nirenberg-Sobolev inequality to the smooth compactly supported approximants and
passes to the limit with Fatou's lemma along an almost everywhere convergent subsequence.  The
normalized form on a set `W` reads `‖v‖_{L̲^q(W)} ≤ C d |W|^{1/d} ‖∇v‖_{L̲^p(W)}`.
-/

@[expose] public section

open MeasureTheory Filter Homogenization
open scoped ENNReal NNReal Topology

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem l2d_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp

theorem l2d_one_le_top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

/-- The operator norm of a linear functional on `Vec d` (sup norm) is at most the sum of the
absolute values of its coordinates. -/
theorem l2d_norm_fderiv_le (L : Vec d →L[ℝ] ℝ) : ‖L‖ ≤ ∑ i, |L (basisVec i)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => abs_nonneg _)
    fun x => ?_
  have hx : x = ∑ i, x i • basisVec i := by
    funext j
    simp [basisVec, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, Real.norm_eq_abs]
  calc |∑ i, x i * L (basisVec i)| ≤ ∑ i, |x i * L (basisVec i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖x‖ * |L (basisVec i)| := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm x i) (abs_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The Gagliardo-Nirenberg-Sobolev inequality for a smooth function with compact support in `W`,
in terms of the coordinate derivatives on `W`. -/
theorem l2d_gns_step (hd : 0 < d) (p q : FiniteLpExponent) (hp : p.exponent.toReal < d)
    (hpq : q.exponent.toReal⁻¹ = p.exponent.toReal⁻¹ - (d : ℝ)⁻¹) {W : Set (Vec d)}
    {a : Vec d → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ W) :
    eLpNorm a q.exponent (volume.restrict W) ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec d)) p.exponent.toNNReal : ℝ≥0∞) *
        ∑ i : Fin d, eLpNorm (fun x => fderiv ℝ a x (basisVec i)) p.exponent
          (volume.restrict W) := by
  have ha1 : ContDiff ℝ 1 a := ha.of_le l2d_one_le_top
  have h := gns_contDiff_compactSupport_finiteLp hd p q hp hpq ha1 hc
  have hsupp : Function.support a ⊆ W := (subset_tsupport a).trans hs
  rw [eLpNorm_restrict_eq_of_support_subset ha.continuous.aestronglyMeasurable hsupp]
  refine h.trans (mul_le_mul_right ?_ _)
  have hder : Continuous (fderiv ℝ a) := ha.continuous_fderiv l2d_top_ne_zero
  have hg : ∀ i : Fin d, Continuous fun x => fderiv ℝ a x (basisVec i) := fun i =>
    hder.clm_apply continuous_const
  calc eLpNorm (fderiv ℝ a) p.exponent volume
      ≤ eLpNorm (fun x => ∑ i, ‖fderiv ℝ a x (basisVec i)‖) p.exponent volume := by
        refine eLpNorm_mono hder.aestronglyMeasurable fun x => ?_
        have h0 : 0 ≤ ∑ i, ‖fderiv ℝ a x (basisVec i)‖ :=
          Finset.sum_nonneg fun i _ => norm_nonneg _
        rw [Real.norm_of_nonneg h0]
        simpa only [Real.norm_eq_abs] using l2d_norm_fderiv_le (fderiv ℝ a x)
    _ = eLpNorm (∑ i, fun x => ‖fderiv ℝ a x (basisVec i)‖) p.exponent volume := by
        congr 1
        funext x
        simp [Finset.sum_apply]
    _ ≤ ∑ i, eLpNorm (fun x => ‖fderiv ℝ a x (basisVec i)‖) p.exponent volume :=
        eLpNorm_sum_le p.one_lt.le
    _ = ∑ i, eLpNorm (fun x => fderiv ℝ a x (basisVec i)) p.exponent volume :=
        Finset.sum_congr rfl fun i _ => eLpNorm_norm _ (hg i).aestronglyMeasurable
    _ = ∑ i, eLpNorm (fun x => fderiv ℝ a x (basisVec i)) p.exponent (volume.restrict W) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [eLpNorm_restrict_eq_of_support_subset (hg i).aestronglyMeasurable]
        intro x hx
        refine hs (support_fderiv_subset ℝ ?_)
        intro h0
        exact hx (by simp [h0])

/-- **Sobolev inequality for `H¹₀(W)` with the gradient measured in `L^p`.** -/
theorem l2d_sobolev_H10 (hd : 0 < d) (p q : FiniteLpExponent) (hp2 : p.exponent ≤ 2)
    (hp : p.exponent.toReal < d)
    (hpq : q.exponent.toReal⁻¹ = p.exponent.toReal⁻¹ - (d : ℝ)⁻¹) {W : Set (Vec d)}
    (hWb : Bornology.IsBounded W) (v : H10Function W) :
    eLpNorm v.toH1Function.toFun q.exponent (volume.restrict W) ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec d)) p.exponent.toNNReal : ℝ≥0∞) *
        ∑ i : Fin d, eLpNorm (fun x => v.toH1Function.grad x i) p.exponent
          (volume.restrict W) := by
  set μ : Measure (Vec d) := volume.restrict W with hμ
  set Cg : ℝ≥0∞ :=
    (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec d)) p.exponent.toNNReal : ℝ≥0∞)
    with hCg
  have hμfin : μ Set.univ < ⊤ := by
    rw [hμ, Measure.restrict_apply_univ]; exact hWb.measure_lt_top
  set c : ℝ≥0∞ := μ Set.univ ^ (1 / p.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal) with hc
  have hcfin : c ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hμfin.ne
    have : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [this]
    have h2 : p.exponent.toReal ≤ 2 := by
      have := ENNReal.toReal_mono (by simp) hp2
      simpa using this
    have hp0 : 0 < p.exponent.toReal :=
      ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne
    have : 1 / 2 ≤ 1 / p.exponent.toReal := one_div_le_one_div_of_le hp0 h2
    linarith only [this]
  set a : ℕ → Vec d → ℝ := v.approx with ha
  set g : ℕ → Fin d → Vec d → ℝ := fun n i x => fderiv ℝ (a n) x (basisVec i) with hg
  have hstep : ∀ n, eLpNorm (a n) q.exponent μ ≤ Cg * ∑ i, eLpNorm (g n i) p.exponent μ :=
    fun n => l2d_gns_step hd p q hp hpq (v.approx_smooth n) (v.approx_hasCompactSupport n)
      (v.approx_support_subset n)
  have hgm : ∀ n i, AEStronglyMeasurable (g n i) μ := fun n i =>
    ((((v.approx_smooth n).continuous_fderiv l2d_top_ne_zero).clm_apply
      continuous_const)).aestronglyMeasurable
  have hvg : ∀ i, AEStronglyMeasurable (fun x => v.toH1Function.grad x i) μ := fun i =>
    (v.toH1Function.gradMemL2 i).aestronglyMeasurable
  have hvm : AEStronglyMeasurable v.toH1Function.toFun μ :=
    v.toH1Function.memL2.aestronglyMeasurable
  -- the gradient error in `L^p`
  set e : ℕ → ℝ≥0∞ := fun n => ∑ i, eLpNorm (fun x => g n i x - v.toH1Function.grad x i) 2 μ
    with he
  have hgp : ∀ n i, eLpNorm (g n i) p.exponent μ ≤
      eLpNorm (fun x => v.toH1Function.grad x i) p.exponent μ +
        eLpNorm (fun x => g n i x - v.toH1Function.grad x i) 2 μ * c := by
    intro n i
    have h1 : eLpNorm (g n i) p.exponent μ ≤
        eLpNorm (fun x => g n i x - v.toH1Function.grad x i) p.exponent μ +
          eLpNorm (fun x => v.toH1Function.grad x i) p.exponent μ := by
      have : g n i = (fun x => g n i x - v.toH1Function.grad x i) +
          fun x => v.toH1Function.grad x i := by
        funext x; simp
      conv_lhs => rw [this]
      exact eLpNorm_add_le p.one_lt.le
    have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := p.exponent) (q := 2)
      (μ := μ) hp2 ((hgm n i).sub (hvg i))
    rw [add_comm]
    exact h1.trans (add_le_add_left h2 _)
  have hn : ∀ n, eLpNorm (a n) q.exponent μ ≤
      Cg * ∑ i, (eLpNorm (fun x => v.toH1Function.grad x i) p.exponent μ +
        eLpNorm (fun x => g n i x - v.toH1Function.grad x i) 2 μ * c) := fun n =>
    (hstep n).trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => hgp n i))
  -- convergence of the gradient errors
  have hge : ∀ i, Tendsto (fun n => eLpNorm (fun x => g n i x - v.toH1Function.grad x i) 2 μ)
      atTop (𝓝 0) := fun i => v.tendsto_approx_grad i
  have hlim : Tendsto (fun n => Cg * ∑ i, (eLpNorm (fun x => v.toH1Function.grad x i)
        p.exponent μ + eLpNorm (fun x => g n i x - v.toH1Function.grad x i) 2 μ * c))
      atTop (𝓝 (Cg * ∑ i, eLpNorm (fun x => v.toH1Function.grad x i) p.exponent μ)) := by
    have h1 : ∀ i, Tendsto (fun n => eLpNorm (fun x => v.toH1Function.grad x i) p.exponent μ +
        eLpNorm (fun x => g n i x - v.toH1Function.grad x i) 2 μ * c) atTop
        (𝓝 (eLpNorm (fun x => v.toH1Function.grad x i) p.exponent μ)) := by
      intro i
      have := ((ENNReal.Tendsto.mul_const (hge i) (Or.inr hcfin)).const_add
        (eLpNorm (fun x => v.toH1Function.grad x i) p.exponent μ))
      simpa using this
    have h2 := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ => h1 i
    exact ENNReal.Tendsto.const_mul h2 (Or.inr (by simp [hCg]))
  -- an almost everywhere convergent subsequence
  have hconv : Tendsto (fun n => eLpNorm (a n - v.toH1Function.toFun) 2 μ) atTop (𝓝 0) :=
    v.tendsto_approx
  have hmeas : TendstoInMeasure μ a atTop v.toH1Function.toFun :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hconv
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have ham : ∀ n, AEStronglyMeasurable (a (ns n)) μ := fun n =>
    ((v.approx_smooth (ns n)).continuous).aestronglyMeasurable
  have hF := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := q.exponent) ham v.toH1Function.toFun hvm hae
  refine hF.trans ?_
  have hlim' := hlim.comp hns.tendsto_atTop
  rw [← hlim'.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun n => hn (ns n))

/-- The exponent condition `2 ≤ q` with `q⁻¹ = p⁻¹ - d⁻¹` makes the normalized Sobolev inequality
land in `L̲²`. -/
theorem l2d_sobolev_norm (hd : 2 ≤ d) {p q : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) (hpd : p < d)
    (hq : q⁻¹ = p⁻¹ - (d : ℝ)⁻¹) (hq2 : 2 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {W : Set (Vec d)}, MeasurableSet W → Bornology.IsBounded W →
      volume W ≠ 0 → ∀ v : H10Function W,
        lpBar W 2 v.toH1Function.toFun ≤
          ENNReal.ofReal C * (volume W ^ (1 / (d : ℝ)) * lpBar W (ENNReal.ofReal p) v.toH1Function.grad) := by
  have hd0 : 0 < d := by omega
  have hq1 : 1 ≤ q := by linarith only [hq2]
  let P : FiniteLpExponent := ⟨ENNReal.ofReal p, by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hp1])).2 hp1,
    ENNReal.ofReal_lt_top⟩
  let Q : FiniteLpExponent := ⟨ENNReal.ofReal q, by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hq2])).2 (by linarith only [hq2]),
    ENNReal.ofReal_lt_top⟩
  have hPr : P.exponent.toReal = p := ENNReal.toReal_ofReal (by linarith only [hp1])
  have hQr : Q.exponent.toReal = q := ENNReal.toReal_ofReal (by linarith only [hq2])
  have hP2 : P.exponent ≤ 2 := by
    show ENNReal.ofReal p ≤ 2
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hp2
  set Cg : ℝ≥0 := SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec d)) P.exponent.toNNReal
    with hCg
  refine ⟨(Cg : ℝ) * d, by positivity, ?_⟩
  intro W hWm hWb hW0 v
  have hWt : volume W ≠ ⊤ := hWb.measure_lt_top.ne
  have hS := l2d_sobolev_H10 hd0 P Q hP2 (by rw [hPr]; exact_mod_cast hpd)
    (by rw [hPr, hQr]; exact hq) hWb v
  have hvm : AEStronglyMeasurable v.toH1Function.toFun (volume.restrict W) :=
    v.toH1Function.memL2.aestronglyMeasurable
  have hgm := l2c_aesm_grad v.toH1Function
  -- the sum of the coordinate norms
  have hcoord : ∑ i : Fin d, eLpNorm (fun x => v.toH1Function.grad x i) P.exponent
      (volume.restrict W) ≤ d * eLpNorm v.toH1Function.grad P.exponent (volume.restrict W) := by
    calc ∑ i : Fin d, eLpNorm (fun x => v.toH1Function.grad x i) P.exponent (volume.restrict W)
        ≤ ∑ _i : Fin d, eLpNorm v.toH1Function.grad P.exponent (volume.restrict W) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact eLpNorm_mono (f := fun x => v.toH1Function.grad x i) (v.toH1Function.gradMemL2 i).aestronglyMeasurable fun x =>
            norm_le_pi_norm (v.toH1Function.grad x) i
      _ = d * eLpNorm v.toH1Function.grad P.exponent (volume.restrict W) := by simp
  -- from `L̲²` to `L̲^q`
  have hprob : ((volume W)⁻¹ • volume.restrict W) Set.univ = 1 := by
    simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hW0 hWt
  have h2q : lpBar W 2 v.toH1Function.toFun ≤ lpBar W (ENNReal.ofReal q) v.toH1Function.toFun := by
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 2) (q := ENNReal.ofReal q)
      (μ := (volume W)⁻¹ • volume.restrict W)
      (by rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
          exact ENNReal.ofReal_le_ofReal hq2)
      (hvm.smul_measure _)
    rw [hprob, ENNReal.one_rpow, mul_one] at this
    exact this
  refine h2q.trans ?_
  rw [l2c_lpBar_eq hq1 hvm, l2c_lpBar_eq hp1.le hgm]
  have hS' : eLpNorm v.toH1Function.toFun (ENNReal.ofReal q) (volume.restrict W) ≤
      (Cg : ℝ≥0∞) * (d * eLpNorm v.toH1Function.grad (ENNReal.ofReal p) (volume.restrict W)) :=
    hS.trans (mul_le_mul' le_rfl hcoord)
  have hexp : (volume W)⁻¹ ^ (1 / q) = volume W ^ (1 / (d : ℝ)) * (volume W)⁻¹ ^ (1 / p) := by
    rw [ENNReal.inv_rpow, ENNReal.inv_rpow, ← ENNReal.rpow_neg, ← ENNReal.rpow_neg,
      ← ENNReal.rpow_add _ _ hW0 hWt]
    congr 1
    rw [one_div, one_div, one_div, hq]
    ring
  rw [hexp]
  calc volume W ^ (1 / (d : ℝ)) * (volume W)⁻¹ ^ (1 / p) *
        eLpNorm v.toH1Function.toFun (ENNReal.ofReal q) (volume.restrict W)
      ≤ volume W ^ (1 / (d : ℝ)) * (volume W)⁻¹ ^ (1 / p) *
        ((Cg : ℝ≥0∞) * (d * eLpNorm v.toH1Function.grad (ENNReal.ofReal p) (volume.restrict W))) :=
        mul_le_mul' le_rfl hS'
    _ = _ := by
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_natCast]
        ring

/-- Satisfiability: the exponent hypotheses hold for `d = 2`, `p = 6/5`, `q = 3`. -/
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ {W : Set (Vec 2)}, MeasurableSet W → Bornology.IsBounded W →
    volume W ≠ 0 → ∀ v : H10Function W,
      lpBar W 2 v.toH1Function.toFun ≤
        ENNReal.ofReal C * (volume W ^ (1 / ((2 : ℕ) : ℝ)) *
          lpBar W (ENNReal.ofReal (6 / 5)) v.toH1Function.grad) :=
  l2d_sobolev_norm (d := 2) le_rfl (p := 6 / 5) (q := 3) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end SuperdiffusionCLT.Section7
