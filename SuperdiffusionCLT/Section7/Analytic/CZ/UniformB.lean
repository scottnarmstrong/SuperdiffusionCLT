/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Global `W^{1,p}` estimate: summation of local estimates with bounded overlap

If pieces `P i` cover `α` almost everywhere, the sets `B i ⊇ P i` have multiplicity at most `N`, and
the local estimates `‖g‖_{L^p(P i)} ≤ a (‖g‖_{L²(B i)} + ‖φ‖_{L²(B i)}) + b ‖F‖_{L^p(B i)}` hold, then
`‖g‖_{L^p} ≤ 4 (a √N (‖g‖_{L²} + ‖φ‖_{L²}) + b N^{1/p} ‖F‖_{L^p})` for `p ≥ 2`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

theorem p13_tsum_rpow_le {ι : Type*} (s : ι → ℝ≥0∞) {q : ℝ} (hq : 1 ≤ q) :
    ∑' i, s i ^ q ≤ (∑' i, s i) ^ q := by
  set S := ∑' i, s i with hS
  have hq0 : 0 ≤ q - 1 := by linarith only [hq]
  by_cases htop : S = ⊤
  · rw [htop, ENNReal.top_rpow_of_pos (by linarith only [hq])]
    exact le_top
  have hsi : ∀ i, s i ≤ S := fun i => ENNReal.le_tsum i
  calc ∑' i, s i ^ q = ∑' i, s i ^ (q - 1) * s i := by
        refine tsum_congr fun i => ?_
        have := ENNReal.rpow_add_of_nonneg (x := s i) (q - 1) 1 hq0 zero_le_one
        rw [sub_add_cancel, ENNReal.rpow_one] at this
        exact this
    _ ≤ ∑' i, S ^ (q - 1) * s i :=
        ENNReal.tsum_le_tsum fun i => mul_le_mul_left (ENNReal.rpow_le_rpow (hsi i) hq0) _
    _ = S ^ (q - 1) * S := ENNReal.tsum_mul_left
    _ = S ^ q := by
        have := ENNReal.rpow_add_of_nonneg (x := S) (q - 1) 1 hq0 zero_le_one
        rw [sub_add_cancel, ENNReal.rpow_one] at this
        exact this.symm

theorem p13_lintegral_tsum_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    {B : ι → Set α} (hB : ∀ i, MeasurableSet (B i)) {N : ℕ}
    (hN : ∀ y, ∃ s : Finset ι, (∀ i, y ∈ B i → i ∈ s) ∧ s.card ≤ N)
    {h : α → ℝ≥0∞} (hh : AEMeasurable h μ) :
    ∑' i, ∫⁻ x in B i, h x ∂μ ≤ (N : ℝ≥0∞) * ∫⁻ x, h x ∂μ := by
  have e1 : ∀ i, ∫⁻ x in B i, h x ∂μ = ∫⁻ x, (B i).indicator h x ∂μ := fun i =>
    (lintegral_indicator (hB i) h).symm
  simp only [e1]
  rw [← lintegral_tsum fun i => hh.indicator (hB i), ← lintegral_const_mul'' _ hh]
  refine lintegral_mono fun y => ?_
  obtain ⟨s, hs, hcard⟩ := hN y
  have h0 : ∀ i ∉ s, (B i).indicator h y = 0 := fun i hi =>
    Set.indicator_of_notMem (fun hy => hi (hs i hy)) _
  rw [tsum_eq_sum h0]
  calc ∑ i ∈ s, (B i).indicator h y ≤ ∑ _i ∈ s, h y :=
        Finset.sum_le_sum fun i _ => Set.indicator_le_self' (fun _ _ => zero_le) y
    _ = s.card * h y := by simp
    _ ≤ N * h y := mul_le_mul_left (by exact_mod_cast hcard) _

theorem p13_lintegral_cover_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    {P : ι → Set α} (hcov : ∀ᵐ x ∂μ, ∃ i, x ∈ P i) (h : α → ℝ≥0∞) :
    ∫⁻ x, h x ∂μ ≤ ∑' i, ∫⁻ x in P i, h x ∂μ := by
  have hU : μ.restrict (⋃ i, P i) = μ := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    filter_upwards [hcov] with x hx
    exact Set.mem_iUnion.2 hx
  calc ∫⁻ x, h x ∂μ = ∫⁻ x in ⋃ i, P i, h x ∂μ := by rw [hU]
    _ ≤ ∑' i, ∫⁻ x in P i, h x ∂μ := lintegral_iUnion_le _ _

theorem p13_eLpNorm_pow {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    {f : α → E} (hf : AEStronglyMeasurable f μ) {q : ℝ} (hq : 0 < q) :
    eLpNorm f (ENNReal.ofReal q) μ ^ q = ∫⁻ x, ‖f x‖ₑ ^ q ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal ((ENNReal.ofReal_pos.2 hq).ne') ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hq.le, ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]

theorem p13_sum_L2 {α ι E : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    [NormedAddCommGroup E] {B : ι → Set α} (hB : ∀ i, MeasurableSet (B i)) {N : ℕ}
    (hN : ∀ y, ∃ s : Finset ι, (∀ i, y ∈ B i → i ∈ s) ∧ s.card ≤ N)
    {g : α → E} (hg : AEStronglyMeasurable g μ) {p : ℝ} (hp : 2 ≤ p) :
    ∑' i, eLpNorm g 2 (μ.restrict (B i)) ^ p ≤
      (N : ℝ≥0∞) ^ (p / 2) * eLpNorm g 2 μ ^ p := by
  have hp0 : 0 < p := by linarith only [hp]
  have h2 : (ENNReal.ofReal 2 : ℝ≥0∞) = 2 := by simp
  have key : ∀ (ν : Measure α), AEStronglyMeasurable g ν →
      eLpNorm g 2 ν ^ p = (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂ν) ^ (p / 2) := by
    intro ν hν
    have := p13_eLpNorm_pow hν (q := 2) (by norm_num)
    rw [h2] at this
    rw [← this, ← ENNReal.rpow_mul]
    congr 1
    ring
  have hmeas : AEMeasurable (fun x => ‖g x‖ₑ ^ (2 : ℝ)) μ := hg.enorm.pow_const _
  calc ∑' i, eLpNorm g 2 (μ.restrict (B i)) ^ p
      = ∑' i, (∫⁻ x in B i, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) ^ (p / 2) :=
        tsum_congr fun i => key _ (hg.mono_measure Measure.restrict_le_self)
    _ ≤ (∑' i, ∫⁻ x in B i, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) ^ (p / 2) :=
        p13_tsum_rpow_le _ (by linarith only [hp])
    _ ≤ ((N : ℝ≥0∞) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) ^ (p / 2) :=
        ENNReal.rpow_le_rpow (p13_lintegral_tsum_le hB hN hmeas) (by positivity)
    _ = (N : ℝ≥0∞) ^ (p / 2) * eLpNorm g 2 μ ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), key μ hg]

theorem p13_add3_rpow_le (x y z : ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (x + y + z) ^ p ≤ (2 : ℝ≥0∞) ^ (2 * (p - 1)) * (x ^ p + y ^ p + z ^ p) := by
  have h1 := ENNReal.rpow_add_le_mul_rpow_add_rpow (x + y) z hp
  have h2 := ENNReal.rpow_add_le_mul_rpow_add_rpow x y hp
  have hc : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (p - 1) :=
    calc (1 : ℝ≥0∞) = 1 ^ (p - 1) := (ENNReal.one_rpow _).symm
      _ ≤ (2 : ℝ≥0∞) ^ (p - 1) := ENNReal.rpow_le_rpow (by norm_num) (by linarith only [hp])
  have hsplit : (2 : ℝ≥0∞) ^ (2 * (p - 1)) = (2 : ℝ≥0∞) ^ (p - 1) * (2 : ℝ≥0∞) ^ (p - 1) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith only [hp]) (by linarith only [hp])]
    congr 1
    ring
  rw [hsplit]
  calc (x + y + z) ^ p ≤ (2 : ℝ≥0∞) ^ (p - 1) * ((x + y) ^ p + z ^ p) := h1
    _ ≤ (2 : ℝ≥0∞) ^ (p - 1) * ((2 : ℝ≥0∞) ^ (p - 1) * (x ^ p + y ^ p) + z ^ p) :=
        mul_le_mul_right (add_le_add h2 le_rfl) _
    _ ≤ (2 : ℝ≥0∞) ^ (p - 1) * ((2 : ℝ≥0∞) ^ (p - 1) * (x ^ p + y ^ p + z ^ p)) := by
        refine mul_le_mul_right ?_ _
        calc (2 : ℝ≥0∞) ^ (p - 1) * (x ^ p + y ^ p) + z ^ p
            ≤ (2 : ℝ≥0∞) ^ (p - 1) * (x ^ p + y ^ p) + (2 : ℝ≥0∞) ^ (p - 1) * z ^ p :=
              add_le_add le_rfl (le_mul_of_one_le_left zero_le hc)
          _ = (2 : ℝ≥0∞) ^ (p - 1) * (x ^ p + y ^ p + z ^ p) := by ring
    _ = _ := by ring

theorem p13_tsum_mul_rpow {ι : Type*} (c : ℝ≥0∞) (e : ι → ℝ≥0∞) {p : ℝ} (hp : 0 ≤ p) :
    ∑' i, (c * e i) ^ p = c ^ p * ∑' i, e i ^ p := by
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun i => ENNReal.mul_rpow_of_nonneg _ _ hp

theorem p13_sum_Lp {α ι E : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    [NormedAddCommGroup E] {B : ι → Set α} (hB : ∀ i, MeasurableSet (B i)) {N : ℕ}
    (hN : ∀ y, ∃ s : Finset ι, (∀ i, y ∈ B i → i ∈ s) ∧ s.card ≤ N)
    {F : α → E} (hF : AEStronglyMeasurable F μ) {p : ℝ} (hp : 0 < p) :
    ∑' i, eLpNorm F (ENNReal.ofReal p) (μ.restrict (B i)) ^ p ≤
      (N : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal p) μ ^ p := by
  rw [p13_eLpNorm_pow hF hp]
  calc ∑' i, eLpNorm F (ENNReal.ofReal p) (μ.restrict (B i)) ^ p
      = ∑' i, ∫⁻ x in B i, ‖F x‖ₑ ^ p ∂μ :=
        tsum_congr fun i => p13_eLpNorm_pow (hF.mono_measure Measure.restrict_le_self) hp
    _ ≤ _ := p13_lintegral_tsum_le hB hN (hF.enorm.pow_const _)

theorem p13_two_rpow_le {p : ℝ} (hp : 2 ≤ p) :
    ((2 : ℝ≥0∞) ^ (2 * (p - 1))) ^ (1 / p) ≤ 4 := by
  have hp0 : 0 < p := by linarith only [hp]
  rw [← ENNReal.rpow_mul]
  have h4 : (4 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (2 : ℝ) := by
    rw [ENNReal.rpow_two]; norm_num
  rw [h4]
  refine ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  rw [mul_one_div, div_le_iff₀ hp0]
  linarith only [hp]

/-- **Summation of local estimates with bounded overlap.** -/
theorem p13_sum_estimate {α ι E₁ E₂ E₃ : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup E₃]
    {g : α → E₁} {φ : α → E₂} {F : α → E₃}
    (hg : AEStronglyMeasurable g μ) (hφ : AEStronglyMeasurable φ μ)
    (hF : AEStronglyMeasurable F μ) {p : ℝ} (hp : 2 ≤ p) {P B : ι → Set α}
    (hB : ∀ i, MeasurableSet (B i))
    (hcov : ∀ᵐ x ∂μ, ∃ i, x ∈ P i) {N : ℕ}
    (hN : ∀ y, ∃ s : Finset ι, (∀ i, y ∈ B i → i ∈ s) ∧ s.card ≤ N) {a a' b : ℝ≥0∞}
    (hloc : ∀ i, eLpNorm g (ENNReal.ofReal p) (μ.restrict (P i)) ≤
      a * eLpNorm g 2 (μ.restrict (B i)) + a' * eLpNorm φ 2 (μ.restrict (B i)) +
        b * eLpNorm F (ENNReal.ofReal p) (μ.restrict (B i))) :
    eLpNorm g (ENNReal.ofReal p) μ ≤
      4 * (a * (N : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm g 2 μ +
        a' * (N : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm φ 2 μ +
        b * (N : ℝ≥0∞) ^ (1 / p) * eLpNorm F (ENNReal.ofReal p) μ) := by
  have hp0 : 0 < p := by linarith only [hp]
  have hp1 : 1 ≤ p := by linarith only [hp]
  set T := eLpNorm g (ENNReal.ofReal p) μ with hT
  set K : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (2 * (p - 1)) with hK
  set u := a * (N : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm g 2 μ with hu
  set v := a' * (N : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm φ 2 μ with hv
  set w := b * (N : ℝ≥0∞) ^ (1 / p) * eLpNorm F (ENNReal.ofReal p) μ with hw
  have hrestr : ∀ (E : Type _) [NormedAddCommGroup E] (f : α → E), AEStronglyMeasurable f μ →
      ∀ S : Set α, AEStronglyMeasurable f (μ.restrict S) := fun E _ f hf S =>
    hf.mono_measure Measure.restrict_le_self
  -- the first inequality: T^p ≤ Σ t_i^p
  have h1 : T ^ p ≤ ∑' i, eLpNorm g (ENNReal.ofReal p) (μ.restrict (P i)) ^ p := by
    rw [hT, p13_eLpNorm_pow hg hp0]
    refine (p13_lintegral_cover_le hcov _).trans (le_of_eq (tsum_congr fun i => ?_))
    rw [p13_eLpNorm_pow (hrestr _ g hg _) hp0]
  have h2 : ∀ i, eLpNorm g (ENNReal.ofReal p) (μ.restrict (P i)) ^ p ≤
      K * ((a * eLpNorm g 2 (μ.restrict (B i))) ^ p + (a' * eLpNorm φ 2 (μ.restrict (B i))) ^ p +
        (b * eLpNorm F (ENNReal.ofReal p) (μ.restrict (B i))) ^ p) := by
    intro i
    refine (ENNReal.rpow_le_rpow (hloc i) hp0.le).trans ?_
    exact p13_add3_rpow_le _ _ _ hp1
  have h3 : T ^ p ≤ K * (∑' i, (a * eLpNorm g 2 (μ.restrict (B i))) ^ p +
      ∑' i, (a' * eLpNorm φ 2 (μ.restrict (B i))) ^ p +
      ∑' i, (b * eLpNorm F (ENNReal.ofReal p) (μ.restrict (B i))) ^ p) := by
    refine h1.trans ((ENNReal.tsum_le_tsum h2).trans (le_of_eq ?_))
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_add]
  have hNp : ((N : ℝ≥0∞) ^ (1 / 2 : ℝ)) ^ p = (N : ℝ≥0∞) ^ (p / 2) := by
    rw [← ENNReal.rpow_mul]; congr 1; ring
  have hNq : ((N : ℝ≥0∞) ^ (1 / p)) ^ p = (N : ℝ≥0∞) := by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
  have h4 : ∑' i, (a * eLpNorm g 2 (μ.restrict (B i))) ^ p ≤ u ^ p := by
    rw [p13_tsum_mul_rpow _ _ hp0.le, hu, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hNp, mul_assoc]
    exact mul_le_mul_right (p13_sum_L2 hB hN hg hp) _
  have h5 : ∑' i, (a' * eLpNorm φ 2 (μ.restrict (B i))) ^ p ≤ v ^ p := by
    rw [p13_tsum_mul_rpow _ _ hp0.le, hv, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hNp, mul_assoc]
    exact mul_le_mul_right (p13_sum_L2 hB hN hφ hp) _
  have h6 : ∑' i, (b * eLpNorm F (ENNReal.ofReal p) (μ.restrict (B i))) ^ p ≤ w ^ p := by
    rw [p13_tsum_mul_rpow _ _ hp0.le, hw, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hNq, mul_assoc]
    exact mul_le_mul_right (p13_sum_Lp hB hN hF hp0) _
  have h7 : T ^ p ≤ K * (u + v + w) ^ p := by
    refine h3.trans (mul_le_mul_right ?_ _)
    calc _ ≤ u ^ p + v ^ p + w ^ p := add_le_add (add_le_add h4 h5) h6
      _ ≤ (u + v) ^ p + w ^ p := add_le_add_left (ENNReal.add_rpow_le_rpow_add _ _ hp1) _
      _ ≤ (u + v + w) ^ p := ENNReal.add_rpow_le_rpow_add _ _ hp1
  have h8 : T ≤ K ^ (1 / p) * (u + v + w) := by
    have e1 : ∀ X : ℝ≥0∞, (X ^ p) ^ (1 / p) = X := fun X => by
      rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
    have := ENNReal.rpow_le_rpow h7 (one_div_pos.2 hp0).le
    rwa [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.2 hp0).le, e1, e1] at this
  calc T ≤ K ^ (1 / p) * (u + v + w) := h8
    _ ≤ 4 * (u + v + w) := mul_le_mul_left (p13_two_rpow_le hp) _
    _ = _ := by rw [hu, hv, hw]

end SuperdiffusionCLT.Section7
