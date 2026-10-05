/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldRegularityC

/-!
# A measurable random scale for the gradient of the recentred stream: the tail

The two random suprema `gradScale_U1`, `gradScale_U2` are countable suprema of the measurable
observables of the large-cube envelopes and of the cube derivative norms, normalized by their
growth rates.  `gradScale_G` is the measurable random variable
`3 √d (c₀ U₁ + (1-ρ)⁻¹ U₂)` (with `ρ = 3^{-1/2}`), which controls the gradient pathwise in
`GradientScaleB.lean`.  Here we prove that `G` has a Gaussian tail: `P[G > t] ≤ 8 exp(-(t/a)²)`
for `t ≥ a`, with an explicit constant `a`.
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

/-- The sum of the two large-cube envelopes at shell scale `0` on the cube `cu_m`. -/
def gradScale_env (omega : ShellSeq d) (m : ℕ) : ℝ :=
  shellDerivLargeCubeSupBound 0 m omega + shellDerivLargeCubeSumSupBound 0 m m omega

/-- The growth constant of the envelope. -/
def gradScale_c0 (d : ℕ) : ℝ := shellDerivLargeCubeConst d + shellDerivLargeCubeSumConst d

/-- The supremum over the cubes of the envelope normalized by its growth rate `c₀ (m+1)`. -/
def gradScale_U1 (omega : ShellSeq d) : ℝ≥0∞ :=
  ⨆ m : ℕ, ENNReal.ofReal (gradScale_env omega m / (gradScale_c0 d * ((m : ℝ) + 1)))

/-- The supremum over the shells of the cube derivative norm normalized by `3^{-k/2}`. -/
def gradScale_U2 (omega : ShellSeq d) : ℝ≥0∞ :=
  ⨆ k : ℕ, ENNReal.ofReal (ShellField.shellCubeDerivNorm k (omega k) / shellDerivTailScale ^ k)

/-- The coefficient of `U₁` in the random scale. -/
def gradScale_a1 (d : ℕ) : ℝ := 3 * Real.sqrt d * gradScale_c0 d

/-- The coefficient of `U₂` in the random scale. -/
def gradScale_a2 (d : ℕ) : ℝ := 3 * Real.sqrt d * (1 - shellDerivTailScale)⁻¹

/-- **The random scale of the gradient.**  A measurable function of the shell sequence. -/
def gradScale_G (omega : ShellSeq d) : ℝ :=
  gradScale_a1 d * (gradScale_U1 omega).toReal + gradScale_a2 d * (gradScale_U2 omega).toReal

/-- The tail constant: `P[G > t] ≤ 8 exp(-(t/a)²)` for `t ≥ a`. -/
def gradScale_rate (d : ℕ) : ℝ := 2 * max (gradScale_a1 d) (gradScale_a2 d)

theorem gradScale_measurable_U1 : Measurable (gradScale_U1 : ShellSeq d → ℝ≥0∞) := by
  refine Measurable.iSup fun m => ENNReal.measurable_ofReal.comp ?_
  have h1 : Measurable (fun omega : ShellSeq d => gradScale_env omega m) :=
    (measurable_shellDerivLargeCubeSupBound 0 m).add (measurable_shellDerivLargeCubeSumSupBound 0 m m)
  exact h1.div_const _

theorem gradScale_measurable_U2 : Measurable (gradScale_U2 : ShellSeq d → ℝ≥0∞) := by
  refine Measurable.iSup fun k => ENNReal.measurable_ofReal.comp ?_
  exact (measurable_shellCubeDerivNorm_coordinate k k).div_const _

/-- **`G` is measurable.** -/
theorem gradScale_measurable_G : Measurable (gradScale_G : ShellSeq d → ℝ) :=
  (gradScale_measurable_U1.ennreal_toReal.const_mul _).add
    (gradScale_measurable_U2.ennreal_toReal.const_mul _)

/-! ## Summing the Gaussian tails -/

theorem gradScale_tsum_exp_le {t : ℝ} (ht : 1 ≤ t) :
    ∑' m : ℕ, ENNReal.ofReal (Real.exp (-(t ^ 2 * ((m : ℝ) + 1)))) ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2))) := by
  set r : ℝ := Real.exp (-(t ^ 2)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 1 / 2 := by
    have h1 : -(t ^ 2) ≤ -1 := by nlinarith only [ht]
    have h2 : r ≤ Real.exp (-1) := Real.exp_le_exp.2 h1
    have h3 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have h4 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    have h5 : (Real.exp 1)⁻¹ ≤ 1 / 2 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) h3
    linarith only [h2, h4, h5]
  have hterm : ∀ m : ℕ, Real.exp (-(t ^ 2 * ((m : ℝ) + 1))) = r * r ^ m := by
    intro m
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hsum : Summable fun m : ℕ => r * r ^ m :=
    (summable_geometric_of_lt_one hr0.le (by linarith only [hr1])).mul_left r
  have h1 : ∑' m : ℕ, ENNReal.ofReal (Real.exp (-(t ^ 2 * ((m : ℝ) + 1)))) =
      ENNReal.ofReal (∑' m : ℕ, r * r ^ m) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum]
    exact tsum_congr fun m => by rw [hterm]
  rw [h1]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le (by linarith only [hr1])]
  have h2 : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith only [hr1]) (by norm_num)]
    linarith only [hr1]
  calc r * (1 - r)⁻¹ ≤ r * 2 := mul_le_mul_of_nonneg_left h2 hr0.le
    _ = 2 * r := by ring

theorem gradScale_natCast_add_one_le_three_pow (k : ℕ) : (k : ℝ) + 1 ≤ (3 : ℝ) ^ k := by
  have h := one_add_mul_le_pow (a := (2 : ℝ)) (by norm_num) k
  norm_num at h
  linarith only [h, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-! ## The tails of the envelopes and the cube norms -/

theorem gradScale_sqrt_mul (m : ℕ) :
    Real.sqrt (1 + (((m - 0 : ℕ) : ℝ))) * Real.sqrt ((m : ℝ) + 1) = (m : ℝ) + 1 := by
  rw [Nat.sub_zero, add_comm (1 : ℝ), ← Real.sqrt_mul (by positivity),
    Real.sqrt_mul_self (by positivity)]

theorem gradScale_exp_arg (t : ℝ) (m : ℕ) :
    (t * Real.sqrt ((m : ℝ) + 1)) ^ (2 : ℝ) = t ^ 2 * ((m : ℝ) + 1) := by
  rw [Real.rpow_two, mul_pow, Real.sq_sqrt (by positivity)]

theorem gradScale_measure_X_tail {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (m : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    P.toMeasure {omega : ShellSeq d |
        shellDerivLargeCubeConst d * (((m : ℝ) + 1) * t) < shellDerivLargeCubeSupBound 0 m omega} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2 * ((m : ℝ) + 1)))) := by
  have h := isBigOWith_gammaSigma_shellDerivLargeCubeSupBound hPrefix hJ3
    (Nat.zero_le m)
  have h1 : 1 ≤ t * Real.sqrt ((m : ℝ) + 1) := by
    have : 1 ≤ Real.sqrt ((m : ℝ) + 1) :=
      Real.one_le_sqrt.2 (by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    nlinarith only [ht, this]
  have h2 := IndependentSums.isBigOWith_gammaSigma_iff.1 h h1
  rw [gradScale_exp_arg t m] at h2
  have h3 : shellDerivLargeCubeConst d * ((3 : ℝ) ^ 0)⁻¹ * Real.sqrt (1 + (((m - 0 : ℕ) : ℝ))) *
      (t * Real.sqrt ((m : ℝ) + 1)) = shellDerivLargeCubeConst d * (((m : ℝ) + 1) * t) := by
    have := gradScale_sqrt_mul m
    calc _ = shellDerivLargeCubeConst d * (Real.sqrt (1 + (((m - 0 : ℕ) : ℝ))) *
          Real.sqrt ((m : ℝ) + 1)) * t := by simp only [pow_zero, inv_one]; ring
      _ = _ := by rw [this]; ring
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  have h4 : IndependentSums.upperTailEvent (shellDerivLargeCubeSupBound 0 m : ShellSeq d → ℝ)
      (shellDerivLargeCubeConst d * ((3 : ℝ) ^ 0)⁻¹ * Real.sqrt (1 + (((m - 0 : ℕ) : ℝ))) *
        (t * Real.sqrt ((m : ℝ) + 1))) = {omega : ShellSeq d |
        shellDerivLargeCubeConst d * (((m : ℝ) + 1) * t) < shellDerivLargeCubeSupBound 0 m omega} := by
    rw [h3]; rfl
  rw [← h4]
  exact h2

theorem gradScale_measure_X'_tail {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (m : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    P.toMeasure {omega : ShellSeq d |
        shellDerivLargeCubeSumConst d * (((m : ℝ) + 1) * t) <
          shellDerivLargeCubeSumSupBound 0 m m omega} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2 * ((m : ℝ) + 1)))) := by
  have h := isBigOWith_gammaSigma_shellDerivLargeCubeSumSupBound hPrefix hJ3
    (Nat.zero_le m) le_rfl
  have h1 : 1 ≤ t * Real.sqrt ((m : ℝ) + 1) := by
    have : 1 ≤ Real.sqrt ((m : ℝ) + 1) :=
      Real.one_le_sqrt.2 (by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    nlinarith only [ht, this]
  have h2 := IndependentSums.isBigOWith_gammaSigma_iff.1 h h1
  rw [gradScale_exp_arg t m] at h2
  have h3 : shellDerivLargeCubeSumConst d * ((3 : ℝ) ^ 0)⁻¹ *
      Real.sqrt (1 + (((m - 0 : ℕ) : ℝ))) * (t * Real.sqrt ((m : ℝ) + 1)) =
      shellDerivLargeCubeSumConst d * (((m : ℝ) + 1) * t) := by
    have := gradScale_sqrt_mul m
    calc _ = shellDerivLargeCubeSumConst d * (Real.sqrt (1 + (((m - 0 : ℕ) : ℝ))) *
          Real.sqrt ((m : ℝ) + 1)) * t := by simp only [pow_zero, inv_one]; ring
      _ = _ := by rw [this]; ring
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  have h4 : IndependentSums.upperTailEvent
      (shellDerivLargeCubeSumSupBound 0 m m : ShellSeq d → ℝ)
      (shellDerivLargeCubeSumConst d * ((3 : ℝ) ^ 0)⁻¹ * Real.sqrt (1 + (((m - 0 : ℕ) : ℝ))) *
        (t * Real.sqrt ((m : ℝ) + 1))) = {omega : ShellSeq d |
        shellDerivLargeCubeSumConst d * (((m : ℝ) + 1) * t) <
          shellDerivLargeCubeSumSupBound 0 m m omega} := by
    rw [h3]; rfl
  rw [← h4]
  exact h2

theorem gradScale_c0_pos {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) :
    0 < gradScale_c0 d :=
  add_pos
    (lt_of_lt_of_le zero_lt_one (one_le_shellDerivLargeCubeConst d))
    (shellDerivLargeCubeSumConst_pos hPrefix)

/-- **The Gaussian tail of `U₁`** (as an extended-real variable, so that `U₁ = ∞` is included). -/
theorem gradScale_measure_U1_tail {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {t : ℝ} (ht : 1 ≤ t) :
    P.toMeasure {omega : ShellSeq d | ENNReal.ofReal t < gradScale_U1 omega} ≤
      ENNReal.ofReal (4 * Real.exp (-(t ^ 2))) := by
  have hc0 := gradScale_c0_pos hPrefix
  have hsub : {omega : ShellSeq d | ENNReal.ofReal t < gradScale_U1 omega} ⊆ ⋃ m : ℕ,
      ({omega : ShellSeq d | shellDerivLargeCubeConst d * (((m : ℝ) + 1) * t) <
          shellDerivLargeCubeSupBound 0 m omega} ∪
        {omega : ShellSeq d | shellDerivLargeCubeSumConst d * (((m : ℝ) + 1) * t) <
          shellDerivLargeCubeSumSupBound 0 m m omega}) := by
    intro omega hω
    have h1 : ENNReal.ofReal t < gradScale_U1 omega := hω
    rw [gradScale_U1, lt_iSup_iff] at h1
    obtain ⟨m, hm⟩ := h1
    have h2 := (ENNReal.ofReal_lt_ofReal_iff'.1 hm).1
    have hpos : 0 < gradScale_c0 d * ((m : ℝ) + 1) :=
      mul_pos hc0 (by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    rw [lt_div_iff₀ hpos] at h2
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq]
    refine ⟨m, ?_⟩
    by_contra hcon
    push Not at hcon
    have h3 : gradScale_c0 d * ((m : ℝ) + 1) * t = shellDerivLargeCubeConst d *
        (((m : ℝ) + 1) * t) + shellDerivLargeCubeSumConst d * (((m : ℝ) + 1) * t) := by
      unfold gradScale_c0; ring
    have h4 : t * (gradScale_c0 d * ((m : ℝ) + 1)) = gradScale_c0 d * ((m : ℝ) + 1) * t := by ring
    unfold gradScale_env at h2
    linarith only [h2, h3, h4, hcon.1, hcon.2]
  have h5 := (measure_mono (μ := P.toMeasure) hsub).trans (measure_iUnion_le _)
  refine h5.trans ?_
  have h6 : ∀ m : ℕ, P.toMeasure ({omega : ShellSeq d |
      shellDerivLargeCubeConst d * (((m : ℝ) + 1) * t) < shellDerivLargeCubeSupBound 0 m omega} ∪
      {omega : ShellSeq d | shellDerivLargeCubeSumConst d * (((m : ℝ) + 1) * t) <
        shellDerivLargeCubeSumSupBound 0 m m omega}) ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2 * ((m : ℝ) + 1)))) +
        ENNReal.ofReal (Real.exp (-(t ^ 2 * ((m : ℝ) + 1)))) := fun m =>
    (measure_union_le _ _).trans (add_le_add (gradScale_measure_X_tail hPrefix hJ3 m ht)
      (gradScale_measure_X'_tail hPrefix hJ3 m ht))
  refine (ENNReal.tsum_le_tsum h6).trans ?_
  rw [ENNReal.tsum_add]
  have h7 := gradScale_tsum_exp_le ht
  calc _ ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2))) + ENNReal.ofReal (2 * Real.exp (-(t ^ 2))) :=
        add_le_add h7 h7
    _ = ENNReal.ofReal (4 * Real.exp (-(t ^ 2))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The Gaussian tail of `U₂`** (as an extended-real variable). -/
theorem gradScale_measure_U2_tail {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) {t : ℝ} (ht : 1 ≤ t) :
    P.toMeasure {omega : ShellSeq d | ENNReal.ofReal t < gradScale_U2 omega} ≤
      ENNReal.ofReal (4 * Real.exp (-(t ^ 2))) := by
  have hsub : {omega : ShellSeq d | ENNReal.ofReal t < gradScale_U2 omega} ⊆ ⋃ k : ℕ,
      {omega : ShellSeq d | ((3 : ℝ) ^ k)⁻¹ * (Real.sqrt 3 ^ k * t) <
        ShellField.shellCubeDerivNorm k (omega k)} := by
    intro omega hω
    have h1 : ENNReal.ofReal t < gradScale_U2 omega := hω
    rw [gradScale_U2, lt_iSup_iff] at h1
    obtain ⟨k, hk⟩ := h1
    have h2 := (ENNReal.ofReal_lt_ofReal_iff'.1 hk).1
    have hpos : 0 < shellDerivTailScale ^ k := pow_pos
      (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num))) k
    rw [lt_div_iff₀ hpos, shellDerivTailScale_pow_eq] at h2
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨k, ?_⟩
    have h3 : ((3 : ℝ) ^ k)⁻¹ * (Real.sqrt 3 ^ k * t) = t * (((3 : ℝ) ^ k)⁻¹ * Real.sqrt 3 ^ k) := by
      ring
    rw [h3]
    exact h2
  have h5 := (measure_mono (μ := P.toMeasure) hsub).trans (measure_iUnion_le _)
  refine h5.trans ?_
  have h6 : ∀ k : ℕ, P.toMeasure {omega : ShellSeq d | ((3 : ℝ) ^ k)⁻¹ * (Real.sqrt 3 ^ k * t) <
        ShellField.shellCubeDerivNorm k (omega k)} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2 * ((k : ℝ) + 1)))) := by
    intro k
    have h1 : 1 ≤ Real.sqrt 3 ^ k * t := by
      have : 1 ≤ Real.sqrt 3 ^ k := one_le_pow₀ (Real.one_le_sqrt.2 (by norm_num))
      nlinarith only [this, ht]
    refine (measure_shellCubeDerivNorm_gaussian_tail hJ3 k h1).trans ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h2 : (Real.sqrt 3 ^ k * t) ^ 2 = (3 : ℝ) ^ k * t ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, Real.sq_sqrt (by norm_num)]
    rw [h2]
    have h3 := gradScale_natCast_add_one_le_three_pow k
    have h4 : 0 ≤ t ^ 2 := sq_nonneg t
    nlinarith only [h3, h4]
  refine (ENNReal.tsum_le_tsum h6).trans ?_
  refine (gradScale_tsum_exp_le ht).trans (ENNReal.ofReal_le_ofReal ?_)
  have := Real.exp_pos (-(t ^ 2))
  linarith only [this]

end

end SuperdiffusionCLT.Section8
