/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.FlatW2pB

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Flat `W^{2,p}`: the limit of the Hessian series

If `w = ∑ₖ xₖ` with `xₖ ∈ H¹₀` having weak Hessians that are geometrically small in `L̲^p`, and the
partial sums converge to `w` in `H¹`, then `w` has a weak Hessian in `L̲^p`, with the bound given by
the sum.
-/

namespace SuperdiffusionCLT.Section7

open SuperdiffusionCLT.Sobolev

variable {d : ℕ}

/-- Partial sums of a sequence in `H¹₀`. -/
noncomputable def flatPartialSum {U : Set (Vec d)} (x : ℕ → H10Function U) : ℕ → H10Function U
  | 0 => x 0
  | n + 1 => flatPartialSum x n + x (n + 1)

theorem flatPartialSum_grad_succ {U : Set (Vec d)} (x : ℕ → H10Function U) (n : ℕ) :
    (flatPartialSum x (n + 1)).toH1Function.grad =
      fun y => (flatPartialSum x n).toH1Function.grad y + (x (n + 1)).toH1Function.grad y := rfl

theorem flatPartialSum_weak {U : Set (Vec d)} (x : ℕ → H10Function U)
    (Hx : ∀ n, HasWeakHessianOn U (x n).toH1Function) (i j : Fin d) :
    ∀ n, HasWeakPartialDerivOn U j (fun y => (flatPartialSum x n).toH1Function.grad y i)
      (fun y => ∑ k ∈ Finset.range (n + 1), (Hx k).hess i j y) := by
  intro n
  induction n with
  | zero =>
    simpa [flatPartialSum] using (Hx 0).weak_second i j
  | succ n ih =>
    have h := flatW2p_weakPartial_add (u₁ := fun y => (flatPartialSum x n).toH1Function.grad y i)
      (u₂ := fun y => (x (n + 1)).toH1Function.grad y i)
      (g₁ := fun y => ∑ k ∈ Finset.range (n + 1), (Hx k).hess i j y)
      (g₂ := fun y => (Hx (n + 1)).hess i j y)
      ((flatPartialSum x n).toH1Function.gradMemL2 i) ((x (n + 1)).toH1Function.gradMemL2 i)
      (memLp_finsetSum _ fun k _ => (Hx k).hess_memL2 i j) ((Hx (n + 1)).hess_memL2 i j)
      ih ((Hx (n + 1)).weak_second i j)
    have e : (fun y => ∑ k ∈ Finset.range (n + 1 + 1), (Hx k).hess i j y) =
        fun y => (∑ k ∈ Finset.range (n + 1), (Hx k).hess i j y) + (Hx (n + 1)).hess i j y := by
      funext y; rw [Finset.sum_range_succ]
    rw [e]
    exact h

/-- Existence of the limit of a geometrically convergent series in `L^p`. -/
theorem flatW2p_exists_limit {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [CompleteSpace E] {μ : Measure α} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : ℕ → α → E) (hf : ∀ n, MemLp (f n) p μ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ n, eLpNorm (f n) p μ ≤ ENNReal.ofReal (B * (1 / 2) ^ n)) :
    ∃ F₀ : α → E, MemLp F₀ p μ ∧ eLpNorm F₀ p μ ≤ ENNReal.ofReal (2 * B) ∧
      Tendsto (fun N => eLpNorm ((∑ k ∈ Finset.range (N + 1), f k) - F₀) p μ) atTop (𝓝 0) := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  have hR : ∀ N, MemLp (∑ k ∈ Finset.range (N + 1), f k) p μ :=
    fun N => memLp_finsetSum' _ fun k _ => hf k
  have hRn : ∀ N, eLpNorm (∑ k ∈ Finset.range (N + 1), f k) p μ ≤ ENNReal.ofReal (2 * B) := by
    intro N
    calc eLpNorm (∑ k ∈ Finset.range (N + 1), f k) p μ
        ≤ ∑ k ∈ Finset.range (N + 1), eLpNorm (f k) p μ :=
          eLpNorm_sum_le hp
      _ ≤ ∑ k ∈ Finset.range (N + 1), ENNReal.ofReal (B * (1 / 2) ^ k) :=
          Finset.sum_le_sum fun k _ => hB k
      _ = ENNReal.ofReal (∑ k ∈ Finset.range (N + 1), B * (1 / 2) ^ k) :=
          (ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity).symm
      _ ≤ ENNReal.ofReal (2 * B) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← Finset.mul_sum]
          have := sum_geometric_two_le (N + 1)
          nlinarith only [this, hB0]
  set S : ℕ → Lp E p μ := fun N => (hR N).toLp (∑ k ∈ Finset.range (N + 1), f k) with hS
  have hcauchy : CauchySeq S := by
    refine cauchySeq_of_le_geometric (1 / 2 : ℝ) B (by norm_num) (fun n => ?_)
    rw [dist_eq_norm]
    have hsub : S n - S (n + 1) = ((hR n).sub (hR (n + 1))).toLp
        ((∑ k ∈ Finset.range (n + 1), f k) - ∑ k ∈ Finset.range (n + 1 + 1), f k) :=
      (MemLp.toLp_sub (hR n) (hR (n + 1))).symm
    rw [hsub, Lp.norm_toLp]
    have e : (∑ k ∈ Finset.range (n + 1), f k) - ∑ k ∈ Finset.range (n + 1 + 1), f k =
        -f (n + 1) := by
      rw [Finset.sum_range_succ _ (n + 1)]; abel
    rw [e, eLpNorm_neg]
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hB (n + 1))
    rw [ENNReal.toReal_ofReal (by positivity)] at h1
    refine h1.trans ?_
    rw [pow_succ]
    have : 0 ≤ B * (1 / 2) ^ n := by positivity
    nlinarith only [this]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨⇑L, Lp.memLp L, ?_, ?_⟩
  · have hnorm : ∀ N, ‖S N‖ ≤ 2 * B := by
      intro N
      rw [hS]
      simp only [Lp.norm_toLp]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hRn N)).trans
        (by rw [ENNReal.toReal_ofReal (by positivity)])
    have hle : ‖L‖ ≤ 2 * B := le_of_tendsto' hL.norm hnorm
    have : eLpNorm (⇑L) p μ = ENNReal.ofReal ‖L‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top L)]
    rw [this]
    exact ENNReal.ofReal_le_ofReal hle
  · have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' S L).1 hL
    refine h1.congr fun N => ?_
    refine eLpNorm_congr_ae ?_
    exact (MemLp.coeFn_toLp (hR N)).sub EventuallyEq.rfl

/-- `L̲²` closeness in terms of `L̲^p` closeness on the probability measure. -/
theorem flatW2p_restrict_two_le (Q : TriadicCube d) {p : ℝ≥0∞} (hp2 : 2 ≤ p) {E : Type*}
    [NormedAddCommGroup E] {F : Vec d → ℝ} {Φ : Vec d → E}
    (hF : AEStronglyMeasurable F (normalizedCubeMeasure Q))
    (hle : ∀ y, ‖F y‖ ≤ ‖Φ y‖) :
    eLpNorm F 2 (volume.restrict (openCubeSet Q)) ≤
      ENNReal.ofReal ((Homogenization.cubeVolume Q) ^ (2 : ℝ≥0∞).toReal⁻¹) *
        eLpNorm Φ p (normalizedCubeMeasure Q) := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) := ⟨normalizedCubeMeasure_apply_univ Q⟩
  rw [eLpNorm_restrict_eq]
  gcongr
  calc eLpNorm F 2 (normalizedCubeMeasure Q) ≤ eLpNorm Φ 2 (normalizedCubeMeasure Q) :=
        eLpNorm_mono_ae hF (Filter.Eventually.of_forall hle)
    _ ≤ eLpNorm Φ p (normalizedCubeMeasure Q) :=
        eLpNorm_le_eLpNorm_of_exponent_le hp2

/-- **Hessian from the series.** -/
theorem flatW2p_hessian_of_series [NeZero d] (Q : TriadicCube d) {p : ℝ≥0∞} (hp2 : 2 ≤ p)
    (x : ℕ → H10Function (openCubeSet Q))
    (Hx : ∀ n, HasWeakHessianOn (openCubeSet Q) (x n).toH1Function)
    (hHp : ∀ n, MemLp (flatHessMat (Hx n)) p (normalizedCubeMeasure Q)) {Bq : ℝ}
    (hHb : ∀ n, cubeLpNorm Q p (flatHessMat (Hx n)) ≤ Bq * (1 / 2) ^ n)
    (w : H10Function (openCubeSet Q))
    (hgrad : Tendsto (fun n => eLpNorm (fun y => (flatPartialSum x n).toH1Function.grad y -
      w.toH1Function.grad y) 2 (normalizedCubeMeasure Q)) atTop (𝓝 0)) :
    ∃ H : HasWeakHessianOn (openCubeSet Q) w.toH1Function,
      MemLp (flatHessMat H) p (normalizedCubeMeasure Q) ∧
        cubeLpNorm Q p (flatHessMat H) ≤ 2 * Bq := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) := ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hBq : 0 ≤ Bq := by
    have := hHb 0
    have h0 : 0 ≤ cubeLpNorm Q p (flatHessMat (Hx 0)) := ENNReal.toReal_nonneg
    simpa using h0.trans this
  have hB : ∀ n, eLpNorm (flatHessMat (Hx n)) p (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal (Bq * (1 / 2) ^ n) := fun n =>
    (ENNReal.le_ofReal_iff_toReal_le (hHp n).eLpNorm_lt_top.ne (by positivity)).2 (hHb n)
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp2
  obtain ⟨F₀, hF₀, hF₀n, hlim⟩ := flatW2p_exists_limit (μ := normalizedCubeMeasure Q) hp1
    (fun n => flatHessMat (Hx n)) hHp hBq hB
  have hF₀2 : MemLp F₀ 2 (normalizedCubeMeasure Q) := hF₀.mono_exponent hp2
  have hent : ∀ i j, MemLp (fun y => HilbertMat.toMat (F₀ y) i j) 2 (normalizedCubeMeasure Q) := by
    intro i j
    refine hF₀2.norm.mono ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((HilbertMat.entryL i j).continuous.comp_aestronglyMeasurable
        hF₀2.aestronglyMeasurable)
    · have := abs_hess_le_norm F₀ i j y
      simpa [Real.norm_eq_abs] using this
  have hentry_le : ∀ (M : HilbertMat d) (i j : Fin d), |HilbertMat.entryL i j M| ≤ ‖M‖ := by
    intro M i j
    have := abs_hess_le_norm (fun _ => M) i j 0
    simpa using this
  have hweak : ∀ i j, HasWeakPartialDerivOn (openCubeSet Q) j
      (fun y => w.toH1Function.grad y i) (fun y => HilbertMat.toMat (F₀ y) i j) := by
    intro i j
    have hgm : ∀ n, AEStronglyMeasurable (fun y => (flatPartialSum x n).toH1Function.grad y -
        w.toH1Function.grad y) (normalizedCubeMeasure Q) := fun n =>
      ((memLp_two_grad Q (flatPartialSum x n)).sub (memLp_two_grad Q w)).aestronglyMeasurable
    refine HasWeakPartialDerivOn.of_tendsto_eLpNorm_two
      (u_n := fun n y => (flatPartialSum x n).toH1Function.grad y i)
      (g_n := fun n y => ∑ k ∈ Finset.range (n + 1), (Hx k).hess i j y)
      (w.toH1Function.gradMemL2 i) (memLp_restrict_of_normalized Q (hent i j))
      (fun n => (flatPartialSum x n).toH1Function.gradMemL2 i)
      (fun n => memLp_finsetSum _ fun k _ => (Hx k).hess_memL2 i j)
      (fun n => flatPartialSum_weak x Hx i j n) ?_ ?_
    · have hc : Tendsto (fun n => ENNReal.ofReal ((Homogenization.cubeVolume Q) ^
          (2 : ℝ≥0∞).toReal⁻¹) * eLpNorm (fun y => (flatPartialSum x n).toH1Function.grad y -
            w.toH1Function.grad y) 2 (normalizedCubeMeasure Q)) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul hgrad (Or.inr ENNReal.ofReal_ne_top)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
        (fun _ => bot_le) (fun n => ?_)
      refine flatW2p_restrict_two_le Q (le_refl _) ?_ (fun y => ?_)
      · exact ((continuous_apply i).comp_aestronglyMeasurable
          ((memLp_two_grad Q (flatPartialSum x n)).sub (memLp_two_grad Q w)).aestronglyMeasurable)
      · have := norm_le_pi_norm ((flatPartialSum x n).toH1Function.grad y -
          w.toH1Function.grad y) i
        simpa using this
    · have hRm : ∀ n, AEStronglyMeasurable ((∑ k ∈ Finset.range (n + 1), flatHessMat (Hx k)) - F₀)
          (normalizedCubeMeasure Q) := fun n =>
        ((memLp_finsetSum' _ fun k _ => hHp k).sub hF₀).aestronglyMeasurable
      have hc : Tendsto (fun n => ENNReal.ofReal ((Homogenization.cubeVolume Q) ^
          (2 : ℝ≥0∞).toReal⁻¹) * eLpNorm ((∑ k ∈ Finset.range (n + 1), flatHessMat (Hx k)) - F₀)
            p (normalizedCubeMeasure Q)) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofReal_ne_top)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
        (fun _ => bot_le) (fun n => ?_)
      have hform : ∀ y, (∑ k ∈ Finset.range (n + 1), (Hx k).hess i j y) -
          HilbertMat.toMat (F₀ y) i j =
          HilbertMat.entryL i j (((∑ k ∈ Finset.range (n + 1), flatHessMat (Hx k)) - F₀) y) := by
        intro y
        simp [Finset.sum_apply, flatHessMat]
      have hFm : AEStronglyMeasurable (fun y => (∑ k ∈ Finset.range (n + 1), (Hx k).hess i j y) -
          HilbertMat.toMat (F₀ y) i j) (normalizedCubeMeasure Q) := by
        have := (HilbertMat.entryL i j).continuous.comp_aestronglyMeasurable (hRm n)
        refine this.congr (Filter.Eventually.of_forall fun y => ?_)
        exact (hform y).symm
      refine flatW2p_restrict_two_le Q hp2 hFm (fun y => ?_)
      rw [hform y]
      exact hentry_le _ i j
  refine ⟨{ hess := fun i j y => HilbertMat.toMat (F₀ y) i j
            hess_memL2 := fun i j => by
              simpa [MemScalarL2, volumeMeasureOn] using memLp_restrict_of_normalized Q (hent i j)
            weak_second := hweak }, ?_⟩
  have hfm : flatHessMat (HasWeakHessianOn.mk (fun i j y => HilbertMat.toMat (F₀ y) i j)
      (fun i j => by
        simpa [MemScalarL2, volumeMeasureOn] using memLp_restrict_of_normalized Q (hent i j))
      hweak) = F₀ := by
    funext y
    simp [flatHessMat]
  rw [hfm]
  refine ⟨hF₀, ?_⟩
  unfold cubeLpNorm
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hF₀n).trans
    (by rw [ENNReal.toReal_ofReal (by positivity)])

end SuperdiffusionCLT.Section7
