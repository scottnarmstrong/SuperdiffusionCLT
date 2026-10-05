/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.GradientScale

/-!
# The measurable random scale controls the gradient

Pathwise, whenever `U₁` and `U₂` are finite and the derivative series is summable on the cubes,
`‖∇k(x)‖ ≤ G (1 + log (2 + |x|))`.  The Gaussian tails of `U₁`, `U₂` make them finite almost
surely and give `G` the tail `P[G > t] ≤ 8 exp(-(t/a)²)` for `t ≥ a`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section6
open scoped Matrix.Norms.Elementwise ENNReal

noncomputable section

variable {d : ℕ}

/-- A random variable whose extended-real tail is Gaussian is almost surely finite. -/
theorem gradScale_ae_ne_top {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {U : Ω → ℝ≥0∞}
    (h : ∀ t : ℝ, 1 ≤ t → μ {omega | ENNReal.ofReal t < U omega} ≤
      ENNReal.ofReal (4 * Real.exp (-(t ^ 2)))) :
    ∀ᵐ omega ∂μ, U omega ≠ ⊤ := by
  rw [ae_iff]
  have hb : ∀ n : ℕ, μ {omega | ¬ U omega ≠ ⊤} ≤
      ENNReal.ofReal (4 * Real.exp (-(((n : ℝ) + 1) ^ 2))) := by
    intro n
    refine le_trans (measure_mono fun omega homega => ?_)
      (h ((n : ℝ) + 1) (by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
    have hU : U omega = ⊤ := not_not.1 homega
    show ENNReal.ofReal ((n : ℝ) + 1) < U omega
    rw [hU]
    exact ENNReal.ofReal_lt_top
  have ht : Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ 2)) atTop atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h1 : Tendsto (fun n : ℕ => 4 * Real.exp (-(((n : ℝ) + 1) ^ 2))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul 4
    simpa only [mul_zero, Function.comp_def] using this
  have h2 := (ENNReal.tendsto_ofReal h1)
  rw [ENNReal.ofReal_zero] at h2
  exact le_antisymm (ge_of_tendsto' h2 hb) zero_le

/-- The geometric remainder of the derivative series above the cube scale, with a random
factor `B` on the cube norms. -/
theorem gradScale_norm_tail_deriv_le (omega : ShellSeq d) (m : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (m : ℤ))) {B : ℝ}
    (hscale : ∀ k : ℕ, m + 1 ≤ k →
      ShellField.shellCubeDerivNorm k (omega k) ≤ B * shellDerivTailScale ^ k) :
    ‖∑' i : ℕ, ShellField.deriv (omega (i + (m + 1))) x‖ ≤
      Real.sqrt d * B * (1 - shellDerivTailScale)⁻¹ := by
  have hgeo : HasSum (fun i : ℕ => shellDerivTailScale ^ i) (1 - shellDerivTailScale)⁻¹ :=
    hasSum_geometric_of_lt_one shellDerivTailScale_nonneg shellDerivTailScale_lt_one
  have hterm : ∀ i : ℕ, ‖ShellField.deriv (omega (i + (m + 1))) x‖ ≤
      Real.sqrt d * B * shellDerivTailScale ^ i := by
    intro i
    have hxk : x ∈ openCubeSet (originCube d ((i + (m + 1) : ℕ) : ℤ)) :=
      openCubeSet_originCube_subset (by omega) hx
    have h1 := (fieldReg_norm_le_sqrt_mul_mdn (ShellField.deriv (omega (i + (m + 1))) x)).trans
      (mul_le_mul_of_nonneg_left
        (ShellField.matrixDerivativeNorm_deriv_le_shellCubeDerivNorm _ _ hxk) (Real.sqrt_nonneg _))
    have h2 := hscale (i + (m + 1)) (by omega)
    have hB : 0 ≤ B := by
      have h0 : 0 ≤ ShellField.shellCubeDerivNorm (i + (m + 1)) (omega (i + (m + 1))) :=
        ShellField.shellCubeDerivNorm_nonneg _ _
      have hp : 0 < shellDerivTailScale ^ (i + (m + 1)) :=
        pow_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num))) _
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_neg_of_pos hneg hp
      linarith only [h0, h2, this]
    have h3 : shellDerivTailScale ^ (i + (m + 1)) ≤ shellDerivTailScale ^ i := by
      rw [pow_add]
      exact mul_le_of_le_one_right (pow_nonneg shellDerivTailScale_nonneg i)
        (pow_le_one₀ shellDerivTailScale_nonneg shellDerivTailScale_lt_one.le)
    have h4 : B * shellDerivTailScale ^ (i + (m + 1)) ≤ B * shellDerivTailScale ^ i :=
      mul_le_mul_of_nonneg_left h3 hB
    calc ‖ShellField.deriv (omega (i + (m + 1))) x‖ ≤ _ := h1
      _ ≤ Real.sqrt d * (B * shellDerivTailScale ^ i) :=
        mul_le_mul_of_nonneg_left (h2.trans h4) (Real.sqrt_nonneg _)
      _ = _ := by ring
  have h := tsum_of_norm_bounded (hgeo.mul_left (Real.sqrt d * B)) hterm
  exact h

theorem gradScale_env_nonneg (omega : ShellSeq d) (m : ℕ) : 0 ≤ gradScale_env omega m :=
  add_nonneg (shellDerivLargeCubeSupBound_nonneg 0 m omega)
    (shellDerivLargeCubeSumSupBound_nonneg 0 m m omega)

/-- The envelope is dominated by `c₀ (m+1) U₁`. -/
theorem gradScale_env_le {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    {omega : ShellSeq d} (hU : gradScale_U1 omega ≠ ⊤) (m : ℕ) :
    gradScale_env omega m ≤ gradScale_c0 d * ((m : ℝ) + 1) * (gradScale_U1 omega).toReal := by
  have hc0 := gradScale_c0_pos hPrefix
  have hpos : 0 < gradScale_c0 d * ((m : ℝ) + 1) :=
    mul_pos hc0 (by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have h1 : ENNReal.ofReal (gradScale_env omega m / (gradScale_c0 d * ((m : ℝ) + 1))) ≤
      gradScale_U1 omega := le_iSup (fun m : ℕ => ENNReal.ofReal
        (gradScale_env omega m / (gradScale_c0 d * ((m : ℝ) + 1)))) m
  have h2 := ENNReal.toReal_mono hU h1
  rw [ENNReal.toReal_ofReal (div_nonneg (gradScale_env_nonneg omega m) hpos.le),
    div_le_iff₀ hpos] at h2
  linarith only [h2]

/-- The cube derivative norms are dominated by `U₂ ρ^k`. -/
theorem gradScale_cubeNorm_le {omega : ShellSeq d} (hU : gradScale_U2 omega ≠ ⊤) (k : ℕ) :
    ShellField.shellCubeDerivNorm k (omega k) ≤
      (gradScale_U2 omega).toReal * shellDerivTailScale ^ k := by
  have hpos : 0 < shellDerivTailScale ^ k :=
    pow_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num))) k
  have h1 : ENNReal.ofReal (ShellField.shellCubeDerivNorm k (omega k) /
      shellDerivTailScale ^ k) ≤ gradScale_U2 omega :=
    le_iSup (fun k : ℕ => ENNReal.ofReal (ShellField.shellCubeDerivNorm k (omega k) /
      shellDerivTailScale ^ k)) k
  have h2 := ENNReal.toReal_mono hU h1
  rw [ENNReal.toReal_ofReal (div_nonneg (ShellField.shellCubeDerivNorm_nonneg _ _) hpos.le),
    div_le_iff₀ hpos] at h2
  exact h2

/-- **The cube bound with the measurable scale.** -/
theorem gradScale_norm_fullStreamDeriv_le_cube {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (omega : ShellSeq d) (m : ℕ)
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k))
    (hU1 : gradScale_U1 omega ≠ ⊤) (hU2 : gradScale_U2 omega ≠ ⊤)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d (m : ℤ))) :
    ‖fullStreamDeriv omega x‖ ≤ ((m : ℝ) + 1) * (gradScale_G omega / 3) := by
  have hsx : Summable fun n : ℕ => ShellField.deriv (omega n) x :=
    Summable.of_norm_bounded ((hsum).mul_left (Real.sqrt d))
      fun n => norm_shellDeriv_le_originCube omega n m hx
  have h := hsx.sum_add_tsum_nat_add (m + 1)
  have hfs : fullStreamDeriv omega x = ∑' n : ℕ, ShellField.deriv (omega n) x := rfl
  have h1 := (norm_add_le _ _).trans (add_le_add (fieldReg_norm_partial_deriv_le omega m hx)
    (gradScale_norm_tail_deriv_le omega m hx
      (fun k _ => gradScale_cubeNorm_le hU2 k)))
  rw [hfs, ← h]
  refine h1.trans ?_
  have h2 := gradScale_env_le hPrefix hU1 m
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hu2 : 0 ≤ (gradScale_U2 omega).toReal := ENNReal.toReal_nonneg
  have hsq : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hinv : 0 ≤ (1 - shellDerivTailScale)⁻¹ :=
    inv_nonneg.2 (by linarith only [shellDerivTailScale_lt_one])
  have h3 : Real.sqrt d * (shellDerivLargeCubeSupBound 0 m omega +
      shellDerivLargeCubeSumSupBound 0 m m omega) ≤
      Real.sqrt d * (gradScale_c0 d * ((m : ℝ) + 1) * (gradScale_U1 omega).toReal) :=
    mul_le_mul_of_nonneg_left h2 hsq
  have h4 : Real.sqrt d * (gradScale_U2 omega).toReal * (1 - shellDerivTailScale)⁻¹ ≤
      ((m : ℝ) + 1) * (Real.sqrt d * (gradScale_U2 omega).toReal *
        (1 - shellDerivTailScale)⁻¹) :=
    le_mul_of_one_le_left (by positivity) hm1
  have h5 : gradScale_G omega / 3 = Real.sqrt d * gradScale_c0 d * (gradScale_U1 omega).toReal +
      Real.sqrt d * (gradScale_U2 omega).toReal * (1 - shellDerivTailScale)⁻¹ := by
    unfold gradScale_G gradScale_a1 gradScale_a2
    ring
  rw [h5]
  have h6 : ((m : ℝ) + 1) * (Real.sqrt d * gradScale_c0 d * (gradScale_U1 omega).toReal +
      Real.sqrt d * (gradScale_U2 omega).toReal * (1 - shellDerivTailScale)⁻¹) =
      Real.sqrt d * (gradScale_c0 d * ((m : ℝ) + 1) * (gradScale_U1 omega).toReal) +
      ((m : ℝ) + 1) * (Real.sqrt d * (gradScale_U2 omega).toReal *
        (1 - shellDerivTailScale)⁻¹) := by ring
  rw [h6]
  linarith only [h3, h4]

/-- **The gradient is controlled pathwise by `G`.** -/
theorem gradScale_norm_fullStreamDeriv_le {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (omega : ShellSeq d)
    (hsum : ∀ m : ℕ, Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k))
    (hU1 : gradScale_U1 omega ≠ ⊤) (hU2 : gradScale_U2 omega ≠ ⊤) (x : Vec d) :
    ‖fullStreamDeriv omega x‖ ≤ gradScale_G omega * (1 + Real.log (2 + ‖x‖)) := by
  obtain ⟨m, hm, hm'⟩ := fieldReg_exists_cube_log x
  have h1 := gradScale_norm_fullStreamDeriv_le_cube hPrefix omega m (hsum m) hU1 hU2 hm
  have hG : 0 ≤ gradScale_G omega := by
    have ha1 : 0 ≤ gradScale_a1 d := by
      have : 0 < gradScale_c0 d := gradScale_c0_pos hPrefix
      unfold gradScale_a1; positivity
    have ha2 : 0 ≤ gradScale_a2 d := by
      have : 0 ≤ (1 - shellDerivTailScale)⁻¹ :=
        inv_nonneg.2 (by linarith only [shellDerivTailScale_lt_one])
      unfold gradScale_a2; positivity
    unfold gradScale_G
    exact add_nonneg (mul_nonneg ha1 ENNReal.toReal_nonneg) (mul_nonneg ha2 ENNReal.toReal_nonneg)
  have h2 : ((m : ℝ) + 1) * (gradScale_G omega / 3) ≤
      (3 * (1 + Real.log (2 + ‖x‖))) * (gradScale_G omega / 3) :=
    mul_le_mul_of_nonneg_right hm' (by positivity)
  have h3 : (3 * (1 + Real.log (2 + ‖x‖))) * (gradScale_G omega / 3) =
      gradScale_G omega * (1 + Real.log (2 + ‖x‖)) := by ring
  linarith only [h1, h2, h3]

/-- **Part A, pathwise bound.**  Almost surely `‖∇k(x)‖ ≤ G (1 + log (2 + |x|))` for all `x`,
with the measurable random variable `G = gradScale_G`. -/
theorem gradScale_ae_log_growth {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ x : Vec d,
      ‖fullStreamDeriv omega x‖ ≤ gradScale_G omega * (1 + Real.log (2 + ‖x‖)) := by
  filter_upwards [gradScale_ae_ne_top (μ := P.toMeasure) (U := gradScale_U1)
      (fun t ht => gradScale_measure_U1_tail hPrefix hJ3 ht),
    gradScale_ae_ne_top (μ := P.toMeasure) (U := gradScale_U2)
      (fun t ht => gradScale_measure_U2_tail hJ3 ht),
    ae_forall_summable_shellDerivLinftyNorm_originCube hJ3] with omega h1 h2 h3 x
  exact gradScale_norm_fullStreamDeriv_le hPrefix omega h3 h1 h2 x

/-- **Part A, the tail of `G`.**  With `a = gradScale_rate d`, for every `t ≥ a`,
`P[G > t] ≤ 8 exp(-(t/a)²)`. -/
theorem gradScale_measure_G_tail {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {t : ℝ} (ht : gradScale_rate d ≤ t) :
    P.toMeasure {omega : ShellSeq d | t < gradScale_G omega} ≤
      ENNReal.ofReal (8 * Real.exp (-((t / gradScale_rate d) ^ 2))) := by
  have hc0 := gradScale_c0_pos hPrefix
  have hd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2
    (lt_of_lt_of_le (by norm_num) hPrefix.dimension))
  have hinv : 0 < (1 - shellDerivTailScale)⁻¹ :=
    inv_pos.2 (by linarith only [shellDerivTailScale_lt_one])
  have ha1 : 0 < gradScale_a1 d := by unfold gradScale_a1; positivity
  have ha2 : 0 < gradScale_a2 d := by unfold gradScale_a2; positivity
  set a := gradScale_rate d with ha
  have hapos : 0 < a := by
    rw [ha]; unfold gradScale_rate
    exact mul_pos (by norm_num) (lt_max_of_lt_left ha1)
  have hta : 1 ≤ t / a := by rw [le_div_iff₀ hapos]; linarith only [ht]
  have h1a : 2 * gradScale_a1 d ≤ a := by
    rw [ha]; unfold gradScale_rate
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
  have h2a : 2 * gradScale_a2 d ≤ a := by
    rw [ha]; unfold gradScale_rate
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  have hq : ∀ (ai : ℝ), 0 < ai → 2 * ai ≤ a → 1 ≤ t / (2 * ai) ∧ t / a ≤ t / (2 * ai) := by
    intro ai hai hle
    have ht0 : 0 ≤ t := by linarith only [ht, hapos]
    refine ⟨?_, div_le_div_of_nonneg_left ht0 (by positivity) hle⟩
    exact hta.trans (div_le_div_of_nonneg_left ht0 (by positivity) hle)
  obtain ⟨hq1, hq1'⟩ := hq _ ha1 h1a
  obtain ⟨hq2, hq2'⟩ := hq _ ha2 h2a
  have hsub : {omega : ShellSeq d | t < gradScale_G omega} ⊆
      {omega : ShellSeq d | ENNReal.ofReal (t / (2 * gradScale_a1 d)) < gradScale_U1 omega} ∪
      {omega : ShellSeq d | ENNReal.ofReal (t / (2 * gradScale_a2 d)) < gradScale_U2 omega} := by
    intro omega hω
    have hω' : t < gradScale_a1 d * (gradScale_U1 omega).toReal +
        gradScale_a2 d * (gradScale_U2 omega).toReal := hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon
    obtain ⟨c1, c2⟩ := hcon
    have hlt : ∀ (U : ℝ≥0∞) (ai : ℝ), 0 < ai → ENNReal.ofReal (t / (2 * ai)) ≥ U →
        ai * U.toReal ≤ t / 2 := by
      intro U ai hai hU
      have hne : U ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hU
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hU
      rw [ENNReal.toReal_ofReal (by
        have : 0 ≤ t := by linarith only [ht, hapos]
        positivity)] at this
      have h2 := mul_le_mul_of_nonneg_left this hai.le
      have h3 : ai * (t / (2 * ai)) = t / 2 := by field_simp
      linarith only [h2, h3]
    have e1 := hlt _ _ ha1 c1
    have e2 := hlt _ _ ha2 c2
    linarith only [hω', e1, e2]
  refine (measure_mono (μ := P.toMeasure) hsub).trans ((measure_union_le _ _).trans ?_)
  have b1 := gradScale_measure_U1_tail hPrefix hJ3 hq1
  have b2 := gradScale_measure_U2_tail hJ3 hq2
  have e1 : Real.exp (-((t / (2 * gradScale_a1 d)) ^ 2)) ≤ Real.exp (-((t / a) ^ 2)) := by
    refine Real.exp_le_exp.2 ?_
    have : (t / a) ^ 2 ≤ (t / (2 * gradScale_a1 d)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hq1' 2
    linarith only [this]
  have e2 : Real.exp (-((t / (2 * gradScale_a2 d)) ^ 2)) ≤ Real.exp (-((t / a) ^ 2)) := by
    refine Real.exp_le_exp.2 ?_
    have : (t / a) ^ 2 ≤ (t / (2 * gradScale_a2 d)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hq2' 2
    linarith only [this]
  calc _ ≤ ENNReal.ofReal (4 * Real.exp (-((t / a) ^ 2))) +
        ENNReal.ofReal (4 * Real.exp (-((t / a) ^ 2))) :=
      add_le_add (b1.trans (ENNReal.ofReal_le_ofReal (by linarith only [e1])))
        (b2.trans (ENNReal.ofReal_le_ofReal (by linarith only [e2])))
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-! ## Witness: the Dirac zero law -/

end

end SuperdiffusionCLT.Section8
