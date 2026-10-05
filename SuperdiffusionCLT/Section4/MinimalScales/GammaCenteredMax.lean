/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.GammaSigma.Operations

/-!
# Centered finite maximum in the `Γ_σ` tail class

For `σ ≥ 1`, a maximum of `N` variables each `O_{Γ_σ}(A)` equals
`A (log (2N))^{1/σ}` plus a nonnegative variable that is `O_{Γ_σ}(A)`.
The constants are both `1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- The centering level `A (log (2N))^{1/σ}`. -/
noncomputable def gammaCenter (σ A : ℝ) (N : ℕ) : ℝ :=
  A * Real.log (2 * (N : ℝ)) ^ σ⁻¹

/-- The positive part of the maximum after centering. -/
noncomputable def gammaCenteredMax (σ A : ℝ) (s : Finset ι) (hs : s.Nonempty)
    (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω => max (s.sup' hs (fun i => X i ω) - gammaCenter σ A s.card) 0

theorem real_add_rpow_le {σ a b : ℝ} (hσ : 1 ≤ σ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ σ + b ^ σ ≤ (a + b) ^ σ := by
  have h := NNReal.add_rpow_le_rpow_add a.toNNReal b.toNNReal hσ
  have h4 := NNReal.coe_le_coe.mpr h
  simpa [NNReal.coe_add, NNReal.coe_rpow, Real.coe_toNNReal _ ha,
    Real.coe_toNNReal _ hb] using h4

omit [MeasurableSpace Ω] in
theorem le_center_add_gammaCenteredMax (σ A : ℝ) (s : Finset ι) (hs : s.Nonempty)
    (X : ι → Ω → ℝ) (ω : Ω) :
    s.sup' hs (fun i => X i ω) ≤ gammaCenter σ A s.card + gammaCenteredMax σ A s hs X ω := by
  unfold gammaCenteredMax
  have := le_max_left (s.sup' hs (fun i => X i ω) - gammaCenter σ A s.card) 0
  linarith only [this]

omit [MeasurableSpace Ω] in
theorem gammaCenteredMax_nonneg (σ A : ℝ) (s : Finset ι) (hs : s.Nonempty)
    (X : ι → Ω → ℝ) (ω : Ω) : 0 ≤ gammaCenteredMax σ A s hs X ω :=
  le_max_right _ _

theorem measurable_gammaCenteredMax (σ A : ℝ) (s : Finset ι) (hs : s.Nonempty)
    (X : ι → Ω → ℝ) (hX : ∀ i ∈ s, Measurable (X i)) :
    Measurable (gammaCenteredMax σ A s hs X) := by
  unfold gammaCenteredMax
  have h1 : Measurable (fun ω => s.sup' hs (fun i => X i ω)) :=
    by
      have h := Finset.measurable_sup' hs (fun i hi => hX i hi)
      convert h using 1
      ext ω
      exact (Finset.sup'_apply hs X ω).symm
  exact (h1.sub measurable_const).max measurable_const

/-- Centered finite maximum, `σ ≥ 1`: the excess over `A (log (2N))^{1/σ}` is `O_{Γ_σ}(A)`. -/
theorem gammaSigma_centered_finset_sup' {μ : Measure Ω} [IsFiniteMeasure μ] {σ A : ℝ}
    (hσ : 1 ≤ σ) (hA : 0 ≤ A) (s : Finset ι) (hs : s.Nonempty) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ s, Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma σ) (X i) A) :
    Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma σ)
      (gammaCenteredMax σ A s hs X) A := by
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  set L : ℝ := Real.log (2 * (s.card : ℝ)) ^ σ⁻¹ with hL
  have hcard : 1 ≤ (s.card : ℝ) := by exact_mod_cast hs.card_pos
  have hlog : 0 ≤ Real.log (2 * (s.card : ℝ)) :=
    Real.log_nonneg (by linarith only [hcard])
  have hL0 : 0 ≤ L := Real.rpow_nonneg hlog _
  have hLσ : L ^ σ = Real.log (2 * (s.card : ℝ)) := by
    rw [hL, ← Real.rpow_mul hlog, inv_mul_cancel₀ (by linarith only [hσ]), Real.rpow_one]
  have hsub : Homogenization.IndependentSums.upperTailEvent
      (fun ω => |gammaCenteredMax σ A s hs X ω|) (A * t) ⊆
      ⋃ i ∈ s, Homogenization.IndependentSums.upperTailEvent (fun ω => |X i ω|)
        (A * (L + t)) := by
    intro ω hω
    have hω' : A * t < |gammaCenteredMax σ A s hs X ω| := hω
    rw [abs_of_nonneg (gammaCenteredMax_nonneg σ A s hs X ω)] at hω'
    have hpos : 0 < gammaCenteredMax σ A s hs X ω :=
      lt_of_le_of_lt (mul_nonneg hA ht0) hω'
    have hmax : s.sup' hs (fun i => X i ω) - gammaCenter σ A s.card =
        gammaCenteredMax σ A s hs X ω := by
      unfold gammaCenteredMax at hpos ⊢
      rcases le_total (s.sup' hs (fun i => X i ω) - gammaCenter σ A s.card) 0 with h | h
      · rw [max_eq_right h] at hpos ⊢; exact absurd hpos (lt_irrefl _)
      · rw [max_eq_left h]
    obtain ⟨i, hi, hiω⟩ := Finset.exists_mem_eq_sup' hs (fun i => X i ω)
    simp only [Set.mem_iUnion]
    refine ⟨i, hi, ?_⟩
    show A * (L + t) < |X i ω|
    have hc : gammaCenter σ A s.card = A * L := rfl
    have : A * (L + t) < X i ω := by
      rw [← hiω]; rw [hc] at hmax
      linarith only [hmax, hω']
    exact lt_of_lt_of_le this (le_abs_self _)
  have hsT : 1 ≤ L + t := by
    have hL1 : 0 ≤ L := hL0
    linarith only [ht, hL1]
  have hpow := real_add_rpow_le hσ hL0 ht0
  have hbound : ∀ i ∈ s, μ.real (Homogenization.IndependentSums.upperTailEvent
      (fun ω => |X i ω|) (A * (L + t))) ≤ Real.exp (-(L ^ σ + t ^ σ)) := by
    intro i hi
    have := hX i hi hsT
    refine this.trans ?_
    simp only [Homogenization.IndependentSums.gammaSigma_inv]
    exact Real.exp_le_exp.mpr (by linarith only [hpow])
  calc μ.real (Homogenization.IndependentSums.upperTailEvent
        (fun ω => |gammaCenteredMax σ A s hs X ω|) (A * t))
      ≤ μ.real (⋃ i ∈ s, Homogenization.IndependentSums.upperTailEvent (fun ω => |X i ω|)
        (A * (L + t))) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i ∈ s, μ.real (Homogenization.IndependentSums.upperTailEvent (fun ω => |X i ω|)
        (A * (L + t))) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ s, Real.exp (-(L ^ σ + t ^ σ)) := Finset.sum_le_sum hbound
    _ = (s.card : ℝ) * Real.exp (-(L ^ σ + t ^ σ)) := by simp
    _ ≤ (Homogenization.IndependentSums.gammaSigma σ t)⁻¹ := by
        simp only [Homogenization.IndependentSums.gammaSigma_inv]
        rw [hLσ, neg_add, Real.exp_add, Real.exp_neg, Real.exp_log (by linarith only [hcard])]
        have hte : 0 ≤ Real.exp (-(t ^ σ)) := (Real.exp_pos _).le
        have h2 : (s.card : ℝ) * (2 * (s.card : ℝ))⁻¹ ≤ 1 := by
          rw [mul_inv, ← mul_assoc, mul_comm (s.card : ℝ) _⁻¹ , mul_assoc,
            mul_inv_cancel₀ (by linarith only [hcard]), mul_one]
          norm_num
        calc (s.card : ℝ) * ((2 * (s.card : ℝ))⁻¹ * Real.exp (-(t ^ σ)))
            = ((s.card : ℝ) * (2 * (s.card : ℝ))⁻¹) * Real.exp (-(t ^ σ)) := by ring
          _ ≤ 1 * Real.exp (-(t ^ σ)) := mul_le_mul_of_nonneg_right h2 hte
          _ = _ := one_mul _

/-- Packaged form: `max ≤ A (log (2N))^{1/σ} + Y` with `Y` nonnegative, measurable and
`O_{Γ_σ}(A)`. -/
theorem gammaSigma_centered_finset_sup'_exists {μ : Measure Ω} [IsFiniteMeasure μ] {σ A : ℝ}
    (hσ : 1 ≤ σ) (hA : 0 ≤ A) (s : Finset ι) (hs : s.Nonempty) (X : ι → Ω → ℝ)
    (hmeas : ∀ i ∈ s, Measurable (X i))
    (hX : ∀ i ∈ s, Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma σ) (X i) A) :
    ∃ Y : Ω → ℝ, Measurable Y ∧ (∀ ω, 0 ≤ Y ω) ∧
      Homogenization.IndependentSums.IsBigO μ
        (Homogenization.IndependentSums.gammaSigma σ) Y A ∧
      ∀ ω, s.sup' hs (fun i => X i ω) ≤
        A * Real.log (2 * (s.card : ℝ)) ^ σ⁻¹ + Y ω :=
  ⟨gammaCenteredMax σ A s hs X, measurable_gammaCenteredMax σ A s hs X hmeas,
    gammaCenteredMax_nonneg σ A s hs X,
    gammaSigma_centered_finset_sup' hσ hA s hs X hX,
    le_center_add_gammaCenteredMax σ A s hs X⟩

/-- Index set `Finset.Icc a b` of naturals, `a ≤ b`: here `N = b + 1 - a`. -/
theorem gammaSigma_centered_Icc {μ : Measure Ω} [IsFiniteMeasure μ] {σ A : ℝ}
    (hσ : 1 ≤ σ) (hA : 0 ≤ A) {a b : ℕ} (hab : a ≤ b) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ i ∈ Finset.Icc a b, Measurable (X i))
    (hX : ∀ i ∈ Finset.Icc a b, Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma σ) (X i) A) :
    ∃ Y : Ω → ℝ, Measurable Y ∧ (∀ ω, 0 ≤ Y ω) ∧
      Homogenization.IndependentSums.IsBigO μ
        (Homogenization.IndependentSums.gammaSigma σ) Y A ∧
      ∀ ω, (Finset.Icc a b).sup' (Finset.nonempty_Icc.mpr hab) (fun i => X i ω) ≤
        A * Real.log (2 * ((b + 1 - a : ℕ) : ℝ)) ^ σ⁻¹ + Y ω := by
  have h := gammaSigma_centered_finset_sup'_exists hσ hA (Finset.Icc a b)
    (Finset.nonempty_Icc.mpr hab) X hmeas hX
  simpa [Nat.card_Icc] using h

/-- Satisfiability: the zero family. -/
example : ∃ Y : ℝ → ℝ, Measurable Y ∧ (∀ ω, 0 ≤ Y ω) ∧
    Homogenization.IndependentSums.IsBigO (volume.restrict (Set.Icc (0:ℝ) 1))
      (Homogenization.IndependentSums.gammaSigma 1) Y 1 ∧
    ∀ ω, (Finset.Icc 0 3).sup' (Finset.nonempty_Icc.mpr (by norm_num))
      (fun _ : ℕ => (0 : ℝ)) ≤
      1 * Real.log (2 * (((3 + 1 - 0 : ℕ)) : ℝ)) ^ (1 : ℝ)⁻¹ + Y ω := by
  have := gammaSigma_centered_Icc (μ := (volume.restrict (Set.Icc (0:ℝ) 1)))
    (σ := 1) (A := 1) le_rfl zero_le_one (a := 0) (b := 3) (by norm_num)
    (fun _ => fun _ : ℝ => (0:ℝ)) (fun _ _ => measurable_const) (by
      intro _ _ t ht
      have h : Homogenization.IndependentSums.upperTailEvent
          (fun ω : ℝ => |(fun _ : ℝ => (0:ℝ)) ω|) (1 * t) = ∅ := by
        ext ω; simp [Homogenization.IndependentSums.upperTailEvent]
        linarith only [ht]
      rw [h]; simp; positivity)
  exact this

end SuperdiffusionCLT.Section4.MinimalScales
