/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.Assembly

/-!
# Integrability and pointwise inequalities for the principal-term assembly

* `pa_blockLenSq_ahomSqrt`: `|bfAhom^{1/2} Y|² = shom |Y₁|² + shom⁻¹ |Y₂|²`.
* `pa_hint_integrable`: the weights `(1 + D) P̂_α P̂_β` are integrable once `D⁴` and `|bfAhom^{1/2} P̂|⁴`
  have finite integrals.
* `pa_dzp_pow4_integrable`: `D'⁴` is integrable (the moment bound `dzp_moment` is a Bochner integral).
* `pa_young_dL`: the pointwise Young inequality `x y ≤ M³ x⁴ + 1/(16 M) + y²/(2 M)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open scoped ENNReal

variable {d : ℕ}

theorem pa_blockLenSq_ahomSqrt [NeZero d] (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (hσ : 0 < sigmaBarInfinite nu L P) (Y : BlockVec d) :
    blockLenSq (ahomSqrtApply nu L P Y) =
      sigmaBarInfinite nu L P * vecNormSq Y.1 + (sigmaBarInfinite nu L P)⁻¹ * vecNormSq Y.2 := by
  rw [← ahomInfinite_quad nu L P hσ]
  obtain ⟨p, q⟩ := Y
  unfold ahomInfinite
  rw [blockVecDot_blockMatVecMul_blockDiag_smul_one]

theorem pa_coord_sq_le (Y : BlockVec d) (α : BlockCoord d) :
    toFullBlockVec Y α ^ 2 ≤ vecNormSq Y.1 + vecNormSq Y.2 := by
  have h1 := vecNormSq_nonneg Y.1
  have h2 := vecNormSq_nonneg Y.2
  have hsq : ∀ (v : Vec d) (i : Fin d), v i ^ 2 ≤ vecNormSq v := by
    intro v i
    unfold vecNormSq vecDot
    calc v i ^ 2 = v i * v i := sq _
      _ ≤ ∑ j, v j * v j :=
        Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
          (Finset.mem_univ i)
  cases α with
  | inl i => simp only [toFullBlockVec]; linarith only [hsq Y.1 i, h2]
  | inr i => simp only [toFullBlockVec]; linarith only [hsq Y.2 i, h1]

/-- `|bfAhom^{1/2} Y|² ≥ (shom + shom⁻¹)⁻¹ |Y|²`, in the multiplied form. -/
theorem pa_norm_le_lenSq [NeZero d] (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (hσ : 0 < sigmaBarInfinite nu L P) (Y : BlockVec d) :
    vecNormSq Y.1 + vecNormSq Y.2 ≤
      (sigmaBarInfinite nu L P + (sigmaBarInfinite nu L P)⁻¹) *
        blockLenSq (ahomSqrtApply nu L P Y) := by
  rw [pa_blockLenSq_ahomSqrt nu L P hσ]
  set s := sigmaBarInfinite nu L P
  have hs : s * s⁻¹ = 1 := mul_inv_cancel₀ hσ.ne'
  have h1 := vecNormSq_nonneg Y.1
  have h2 := vecNormSq_nonneg Y.2
  have hsi : 0 < s⁻¹ := inv_pos.mpr hσ
  have e1 : vecNormSq Y.1 = s⁻¹ * (s * vecNormSq Y.1) := by
    rw [← mul_assoc, mul_comm s⁻¹ s, hs, one_mul]
  have e2 : vecNormSq Y.2 = s * (s⁻¹ * vecNormSq Y.2) := by
    rw [← mul_assoc, hs, one_mul]
  have a1 : 0 ≤ s * vecNormSq Y.1 := mul_nonneg hσ.le h1
  have a2 : 0 ≤ s⁻¹ * vecNormSq Y.2 := mul_nonneg hsi.le h2
  nlinarith only [e1, e2, a1, a2, hσ, hsi, mul_nonneg hσ.le a2, mul_nonneg hsi.le a1]

/-- The pointwise bound of the weight. -/
theorem pa_weight_le {D Lf c p N : ℝ} (hD : 0 ≤ D) (hc : 0 ≤ c) (hN : N ≤ c * Lf)
    (hp : |p| ≤ N) :
    (1 + D) * |p| ≤ 2 * c + c * D ^ 4 + c / 2 * Lf ^ 2 := by
  have hp0 : 0 ≤ |p| := abs_nonneg p
  have hN0 : 0 ≤ N := le_trans hp0 hp
  have hcL : 0 ≤ c * Lf := le_trans hN0 hN
  have hL0 : c = 0 ∨ 0 ≤ Lf := by
    by_cases hc0 : c = 0
    · exact Or.inl hc0
    · right
      by_contra hneg
      have hneg := lt_of_not_ge hneg
      have : c * Lf < 0 := mul_neg_of_pos_of_neg (lt_of_le_of_ne hc (Ne.symm hc0)) hneg
      linarith only [this, hcL]
  rcases hL0 with hc0 | hL
  · subst hc0
    have : N ≤ 0 := by simpa using hN
    have : |p| ≤ 0 := le_trans hp this
    simp only [zero_mul, mul_zero, add_zero, zero_div]
    have : |p| = 0 := le_antisymm this hp0
    rw [this]; simp
  · have h1 : (1 + D) * |p| ≤ (1 + D) * (c * Lf) :=
      mul_le_mul_of_nonneg_left (hp.trans hN) (by linarith only [hD])
    have h2 : (1 + D) * Lf ≤ ((1 + D) ^ 2 + Lf ^ 2) / 2 := by
      nlinarith only [sq_nonneg ((1 + D) - Lf)]
    have h3 : (1 + D) ^ 2 ≤ 4 + 2 * D ^ 4 := by
      nlinarith only [sq_nonneg (D ^ 2 - 1), sq_nonneg (D - 1), hD]
    have h4 : (1 + D) * (c * Lf) = c * ((1 + D) * Lf) := by ring
    have h5 : c * ((1 + D) * Lf) ≤ c * (((4 + 2 * D ^ 4) + Lf ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left (h2.trans (by linarith only [h3])) hc
    nlinarith only [h1, h4, h5]

/-- **Integrability of the weights** `(1 + D) P̂_α P̂_β`. -/
theorem pa_hint_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {D Lf : Ω → ℝ} {Phat : Ω → BlockVec d} {c : ℝ} (hc : 0 ≤ c)
    (hD : Measurable D) (hD0 : ∀ ω, 0 ≤ D ω)
    (hPm : ∀ α : BlockCoord d, Measurable fun ω => toFullBlockVec (Phat ω) α)
    (hLb : ∀ ω, vecNormSq (Phat ω).1 + vecNormSq (Phat ω).2 ≤ c * Lf ω)
    (hD4 : Integrable (fun ω => D ω ^ 4) μ)
    (hL2 : ∫⁻ ω, ENNReal.ofReal (Lf ω ^ 2) ∂μ ≠ ⊤) (α β : BlockCoord d) :
    Integrable (fun ω => (1 + D ω) * (toFullBlockVec (Phat ω) α * toFullBlockVec (Phat ω) β)) μ := by
  have hmeas : Measurable fun ω => (1 + D ω) *
      (toFullBlockVec (Phat ω) α * toFullBlockVec (Phat ω) β) :=
    (measurable_const.add hD).mul ((hPm α).mul (hPm β))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  set g1 : Ω → ℝ := fun ω => 2 * c + c * D ω ^ 4 with hg1
  set g2 : Ω → ℝ := fun ω => c / 2 * Lf ω ^ 2 with hg2
  have hg1i : Integrable g1 μ := (integrable_const _).add (hD4.const_mul c)
  have hg10 : ∀ ω, 0 ≤ g1 ω := fun ω => by simp only [hg1]; positivity
  have hg20 : ∀ ω, 0 ≤ g2 ω := fun ω => by simp only [hg2]; positivity
  have hpt : ∀ ω, ‖(1 + D ω) * (toFullBlockVec (Phat ω) α * toFullBlockVec (Phat ω) β)‖ₑ ≤
      ENNReal.ofReal (g1 ω) + ENNReal.ofReal (g2 ω) := by
    intro ω
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (hg10 ω) (hg20 ω)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpp : |toFullBlockVec (Phat ω) α * toFullBlockVec (Phat ω) β| ≤
        vecNormSq (Phat ω).1 + vecNormSq (Phat ω).2 := by
      have a1 := pa_coord_sq_le (Phat ω) α
      have a2 := pa_coord_sq_le (Phat ω) β
      rw [abs_le]
      constructor <;> nlinarith only [a1, a2, sq_nonneg (toFullBlockVec (Phat ω) α +
        toFullBlockVec (Phat ω) β), sq_nonneg (toFullBlockVec (Phat ω) α -
        toFullBlockVec (Phat ω) β)]
    rw [abs_mul, abs_of_nonneg (by linarith only [hD0 ω] : (0 : ℝ) ≤ 1 + D ω)]
    have := pa_weight_le (hD0 ω) hc (hLb ω) hpp
    simp only [hg1, hg2]
    linarith only [this]
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [lintegral_add_left' (hg1i.aemeasurable.ennreal_ofReal)]
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · have := hg1i.hasFiniteIntegral
    unfold HasFiniteIntegral at this
    refine lt_of_le_of_lt (le_of_eq ?_) this
    exact lintegral_congr fun ω => (Real.enorm_eq_ofReal (hg10 ω)).symm
  · have : ∫⁻ ω, ENNReal.ofReal (g2 ω) ∂μ =
        ENNReal.ofReal (c / 2) * ∫⁻ ω, ENNReal.ofReal (Lf ω ^ 2) ∂μ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_congr fun ω => ENNReal.ofReal_mul (by positivity)
    rw [this]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hL2)

/-- `D'⁴` is integrable, for every cube. -/
theorem pa_dzp_pow4_integrable [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {m h : ℕ} (hh : 1 ≤ h) (hhm : h ≤ m)
    (n : ℕ) (R : TriadicCube d) :
    Integrable (fun ω => dzPrime nu n m h R ω ^ 4) P.toMeasure := by
  set cc : ℝ := (d : ℝ) * Real.sqrt d with hcc
  set z : Vec d := cubeCenter R with hz
  set g : ShellSeq d → ℝ := fun ω =>
    finiteShellDerivGauge (m - h) m (ShellField.translateSequence z ω) with hg
  set α : ℝ := nu⁻¹ * cc * (3 : ℝ) ^ n with hα
  have hα0 : 0 ≤ α := by positivity
  have hpoint : ∀ ω, dzPrime nu n m h R ω ^ 4 ≤ 8 * (α ^ 4 * g ω ^ 4 + α ^ 8 * g ω ^ 8) := by
    intro ω
    have hg0 : 0 ≤ g ω := finiteShellDerivGauge_nonneg _ _ _
    have hx : 0 ≤ α * g ω := mul_nonneg hα0 hg0
    have hD' : dzPrime nu n m h R ω = α * g ω + (α * g ω) ^ 2 := rfl
    rw [hD']
    calc (α * g ω + (α * g ω) ^ 2) ^ 4 ≤ 8 * ((α * g ω) ^ 4 + (α * g ω) ^ 8) :=
          add_sq_pow_four_le
      _ = 8 * (α ^ 4 * g ω ^ 4 + α ^ 8 * g ω ^ 8) := by ring
  obtain ⟨hi4, -⟩ := gauge_moment hPrefix hJ3 hh hhm z 4 (by norm_num)
  obtain ⟨hi8, -⟩ := gauge_moment hPrefix hJ3 hh hhm z 8 (by norm_num)
  have hint : Integrable (fun ω => 8 * (α ^ 4 * g ω ^ 4 + α ^ 8 * g ω ^ 8)) P.toMeasure :=
    ((hi4.const_mul (α ^ 4)).add (hi8.const_mul (α ^ 8))).const_mul 8
  refine hint.mono' ((measurable_dzPrime nu n m h R).pow_const 4).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_of_nonneg (pow_nonneg (dzPrime_nonneg hnu n m h R ω) 4)]
  exact hpoint ω

/-- The pointwise Young inequality `x y ≤ M³ x⁴ + 1/(16 M) + y²/(2 M)` (`M > 0`). -/
theorem pa_young_dL {x y M : ℝ} (hM : 0 < M) :
    x * y ≤ M ^ 3 * x ^ 4 + 1 / (16 * M) + y ^ 2 / (2 * M) := by
  have key : 16 * M * (x * y) ≤ 16 * M ^ 4 * x ^ 4 + 1 + 8 * y ^ 2 := by
    nlinarith only [sq_nonneg (4 * M ^ 2 * x ^ 2 - 1), sq_nonneg (M * x - y)]
  have h : x * y ≤ (16 * M ^ 4 * x ^ 4 + 1 + 8 * y ^ 2) / (16 * M) := by
    rw [le_div_iff₀ (by positivity)]
    linarith only [key]
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

end SuperdiffusionCLT.Section5
