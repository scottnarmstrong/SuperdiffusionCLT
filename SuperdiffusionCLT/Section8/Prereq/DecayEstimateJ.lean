/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DecayEstimateI
public import SuperdiffusionCLT.Section8.Prereq.AdjointFieldB
public import SuperdiffusionCLT.Section7.MinimalScale.RootScales
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import SuperdiffusionCLT.Section8.Prereq.AdjointField
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApiC

@[expose] public section

namespace SuperdiffusionCLT.Section8

noncomputable section

/-!
# Tails of random scales

Stretched-exponential tails `P[t < X] ≤ C exp(-C⁻¹ (log t)^σ)`, `t ≥ 2`: maxima, enlargement by a
constant, and conversion from the weak-Orlicz control of `log X`.
-/

section

open Homogenization MeasureTheory
open scoped ENNReal

theorem decayEst_log_rpow_nonneg {t σ : ℝ} (ht : 2 ≤ t) : 0 ≤ Real.log t ^ σ :=
  Real.rpow_nonneg (Real.log_nonneg (by linarith only [ht])) _

/-- Tail of a maximum. -/
theorem decayEst_tail_max {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X₁ X₂ : Ω → ℝ} {C₁ C₂ σ : ℝ} (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
    (h₁ : ∀ t : ℝ, 2 ≤ t → μ.real {ω | t < X₁ ω} ≤ C₁ * Real.exp (-(C₁⁻¹ * Real.log t ^ σ)))
    (h₂ : ∀ t : ℝ, 2 ≤ t → μ.real {ω | t < X₂ ω} ≤ C₂ * Real.exp (-(C₂⁻¹ * Real.log t ^ σ))) :
    ∀ t : ℝ, 2 ≤ t → μ.real {ω | t < max (X₁ ω) (X₂ ω)} ≤
      (C₁ + C₂) * Real.exp (-((C₁ + C₂)⁻¹ * Real.log t ^ σ)) := by
  intro t ht
  have hL := decayEst_log_rpow_nonneg (σ := σ) ht
  have hsub : {ω | t < max (X₁ ω) (X₂ ω)} ⊆ {ω | t < X₁ ω} ∪ {ω | t < X₂ ω} := by
    intro ω hω
    have hω' : t < max (X₁ ω) (X₂ ω) := hω
    exact lt_max_iff.1 hω'
  have hC0 : 0 < C₁ + C₂ := by linarith only [hC₁, hC₂]
  have e1 : Real.exp (-(C₁⁻¹ * Real.log t ^ σ)) ≤
      Real.exp (-((C₁ + C₂)⁻¹ * Real.log t ^ σ)) := by
    refine Real.exp_le_exp.2 ?_
    have : (C₁ + C₂)⁻¹ ≤ C₁⁻¹ := inv_anti₀ (by linarith only [hC₁]) (by linarith only [hC₂])
    nlinarith only [this, hL]
  have e2 : Real.exp (-(C₂⁻¹ * Real.log t ^ σ)) ≤
      Real.exp (-((C₁ + C₂)⁻¹ * Real.log t ^ σ)) := by
    refine Real.exp_le_exp.2 ?_
    have : (C₁ + C₂)⁻¹ ≤ C₂⁻¹ := inv_anti₀ (by linarith only [hC₂]) (by linarith only [hC₁])
    nlinarith only [this, hL]
  calc μ.real {ω | t < max (X₁ ω) (X₂ ω)}
      ≤ μ.real ({ω | t < X₁ ω} ∪ {ω | t < X₂ ω}) := measureReal_mono hsub
    _ ≤ μ.real {ω | t < X₁ ω} + μ.real {ω | t < X₂ ω} := measureReal_union_le _ _
    _ ≤ C₁ * Real.exp (-(C₁⁻¹ * Real.log t ^ σ)) + C₂ * Real.exp (-(C₂⁻¹ * Real.log t ^ σ)) :=
        add_le_add (h₁ t ht) (h₂ t ht)
    _ ≤ C₁ * Real.exp (-((C₁ + C₂)⁻¹ * Real.log t ^ σ)) +
        C₂ * Real.exp (-((C₁ + C₂)⁻¹ * Real.log t ^ σ)) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 (by linarith only [hC₁]))
          (mul_le_mul_of_nonneg_left e2 (by linarith only [hC₂]))
    _ = _ := by ring

/-- Enlarging a scale by the constant `3`. -/
theorem decayEst_tail_max_three {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {C σ : ℝ} (hC : 1 ≤ C) (hσ : 0 < σ)
    (h : ∀ t : ℝ, 2 ≤ t → μ.real {ω | t < X ω} ≤ C * Real.exp (-(C⁻¹ * Real.log t ^ σ))) :
    ∀ t : ℝ, 2 ≤ t → μ.real {ω | t < max (X ω) 3} ≤
      (C + Real.exp (Real.log 3 ^ σ)) *
        Real.exp (-((C + Real.exp (Real.log 3 ^ σ))⁻¹ * Real.log t ^ σ)) := by
  intro t ht
  set E : ℝ := Real.exp (Real.log 3 ^ σ) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _)
  have hC' : 0 < C + E := by linarith only [hC, hE1]
  have hL := decayEst_log_rpow_nonneg (σ := σ) ht
  by_cases h3 : t < 3
  · -- bounded by one
    have h1 : μ.real {ω | t < max (X ω) 3} ≤ 1 := measureReal_le_one
    refine h1.trans ?_
    have hL3 : Real.log t ^ σ ≤ Real.log 3 ^ σ :=
      Real.rpow_le_rpow (Real.log_nonneg (by linarith only [ht]))
        (Real.log_le_log (by linarith only [ht]) h3.le) hσ.le
    have hinv : (C + E)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith only [hC, hE1])
    have h4 : -((C + E)⁻¹ * Real.log t ^ σ) ≥ -(Real.log 3 ^ σ) := by
      nlinarith only [hinv, hL, hL3]
    have h5 : Real.exp (-(Real.log 3 ^ σ)) ≤ Real.exp (-((C + E)⁻¹ * Real.log t ^ σ)) :=
      Real.exp_le_exp.2 h4
    have h6 : E * Real.exp (-(Real.log 3 ^ σ)) = 1 := by
      rw [hE, ← Real.exp_add]
      simp
    calc (1 : ℝ) = E * Real.exp (-(Real.log 3 ^ σ)) := h6.symm
      _ ≤ (C + E) * Real.exp (-(Real.log 3 ^ σ)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hC]) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left h5 hC'.le
  · have hsub : {ω | t < max (X ω) 3} ⊆ {ω | t < X ω} := by
      intro ω hω
      have hω' : t < max (X ω) 3 := hω
      rcases lt_max_iff.1 hω' with h | h
      · exact h
      · exact absurd h h3
    have e1 : Real.exp (-(C⁻¹ * Real.log t ^ σ)) ≤
        Real.exp (-((C + E)⁻¹ * Real.log t ^ σ)) := by
      refine Real.exp_le_exp.2 ?_
      have : (C + E)⁻¹ ≤ C⁻¹ := inv_anti₀ (by linarith only [hC]) (by linarith only [hE1])
      nlinarith only [this, hL]
    calc μ.real {ω | t < max (X ω) 3} ≤ μ.real {ω | t < X ω} := measureReal_mono hsub
      _ ≤ C * Real.exp (-(C⁻¹ * Real.log t ^ σ)) := h t ht
      _ ≤ C * Real.exp (-((C + E)⁻¹ * Real.log t ^ σ)) :=
          mul_le_mul_of_nonneg_left e1 (by linarith only [hC])
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hE1]) (Real.exp_pos _).le


/-- The stretched-exponential tail of `X` from weak-Orlicz control of `log X`. -/
theorem decayEst_tail_of_isBigO {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {Λ ρ : ℝ} (hΛ : 1 ≤ Λ)
    (hρ : 0 < ρ)
    (hO : Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
      (fun ω => Real.log (X ω)) Λ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 2 ≤ t →
      μ.real {ω | t < X ω} ≤ C * Real.exp (-(C⁻¹ * Real.log t ^ ρ)) := by
  have hΛ0 : 0 < Λ := by linarith only [hΛ]
  have hΛρ : 0 < Λ ^ ρ := Real.rpow_pos_of_pos hΛ0 _
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  refine ⟨Real.exp 1 + Λ ^ ρ, by linarith only [he1, hΛρ], fun t ht => ?_⟩
  set C : ℝ := Real.exp 1 + Λ ^ ρ with hC
  have hC1 : 1 ≤ C := by linarith only [he1, hΛρ]
  have hC0 : 0 < C := by linarith only [hC1]
  have hCΛ : Λ ^ ρ ≤ C := by linarith only [he1]
  have hL := decayEst_log_rpow_nonneg (σ := ρ) ht
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith only [ht])
  by_cases hcase : Λ ≤ Real.log t
  · set s : ℝ := Real.log t / Λ with hs
    have hs1 : 1 ≤ s := by rw [hs, le_div_iff₀ hΛ0]; linarith only [hcase]
    have hsub : {ω | t < X ω} ⊆ {ω | Λ * s < |Real.log (X ω)|} := by
      intro ω hω
      have hω' : t < X ω := hω
      have h1 : Real.log t < Real.log (X ω) :=
        Real.log_lt_log (by linarith only [ht]) hω'
      show Λ * s < |Real.log (X ω)|
      rw [hs, mul_div_cancel₀ _ hΛ0.ne']
      exact lt_of_lt_of_le h1 (le_abs_self _)
    have h1 := SuperdiffusionCLT.Section7.ms_tail_of_isBigO hO s hs1
    have hsρ : s ^ ρ = Real.log t ^ ρ / Λ ^ ρ := by
      rw [hs, Real.div_rpow hlogt.le hΛ0.le]
    have hCinv : C⁻¹ * Real.log t ^ ρ ≤ s ^ ρ := by
      rw [hsρ, inv_mul_eq_div]
      exact div_le_div_of_nonneg_left hL hΛρ hCΛ
    calc μ.real {ω | t < X ω} ≤ μ.real {ω | Λ * s < |Real.log (X ω)|} := measureReal_mono hsub
      _ ≤ 1 * Real.exp (-(s ^ ρ)) := h1
      _ ≤ 1 * Real.exp (-(C⁻¹ * Real.log t ^ ρ)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith only [hCinv])) zero_le_one
      _ ≤ C * Real.exp (-(C⁻¹ * Real.log t ^ ρ)) :=
          mul_le_mul_of_nonneg_right hC1 (Real.exp_pos _).le
  · push Not at hcase
    have hL3 : Real.log t ^ ρ ≤ Λ ^ ρ := Real.rpow_le_rpow hlogt.le hcase.le hρ.le
    have h1 : μ.real {ω | t < X ω} ≤ 1 := measureReal_le_one
    refine h1.trans ?_
    have h2 : C⁻¹ * Real.log t ^ ρ ≤ 1 := by
      calc C⁻¹ * Real.log t ^ ρ ≤ C⁻¹ * Λ ^ ρ := mul_le_mul_of_nonneg_left hL3 (inv_nonneg.2 hC0.le)
        _ ≤ C⁻¹ * C := mul_le_mul_of_nonneg_left hCΛ (inv_nonneg.2 hC0.le)
        _ = 1 := inv_mul_cancel₀ hC0.ne'
    have h3 : Real.exp (-1) ≤ Real.exp (-(C⁻¹ * Real.log t ^ ρ)) :=
      Real.exp_le_exp.2 (by linarith only [h2])
    have h4 : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
    calc (1 : ℝ) = Real.exp 1 * Real.exp (-1) := h4.symm
      _ ≤ C * Real.exp (-1) :=
          mul_le_mul_of_nonneg_right (by linarith only [hΛρ]) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hC0.le

end

/-!
# Random scales for the adjoint field and almost-sure existence

Transfer of a random scale with a stretched-exponential tail to the transposed field, and the
almost-sure existence of Dirichlet solutions of the transposed problem on balls.
-/

section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal

variable {d : ℕ}

theorem decayEst_ofReal_measureReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (s : Set Ω) : μ s = ENNReal.ofReal (μ.real s) := by
  rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Transposed random scale.** A scale with a stretched-exponential tail, valid almost surely for
the recentered field, gives a scale with the same tail valid for the transposed field. -/
theorem decayEst_transpose_scale {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (nu : ℝ)
    {Ψ : ℝ → (Vec d → Mat d) → Prop} {C σ : ℝ} (hC : 0 ≤ C) {X : ShellSeq d → ℝ}
    (hXm : Measurable X)
    (hT : ∀ t : ℝ, 2 ≤ t →
      P.toMeasure.real {ω | t < X ω} ≤ C * Real.exp (-(C⁻¹ * Real.log t ^ σ)))
    (hΨ : ∀ᵐ ω ∂P.toMeasure, Ψ (X ω) (fullCoefficientRecentered nu ω)) :
    ∃ X' : ShellSeq d → ℝ, Measurable X' ∧
      (∀ t : ℝ, 2 ≤ t →
        P.toMeasure.real {ω | t < X' ω} ≤ C * Real.exp (-(C⁻¹ * Real.log t ^ σ))) ∧
      ∀ᵐ ω ∂P.toMeasure, Ψ (X' ω) (fun x => matTranspose (fullCoefficientRecentered nu ω x)) := by
  classical
  obtain ⟨X', hX'm, hX'T, hX'Ψ⟩ := adjField_exists_scale_transpose hJ4 nu
    (Ψ := Ψ) (fun t => if 2 ≤ t then C * Real.exp (-(C⁻¹ * Real.log t ^ σ)) else 1)
    ⟨X, hXm, fun t => by
      by_cases ht : 2 ≤ t
      · simp only [ht, ↓reduceIte]
        rw [decayEst_ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal (hT t ht)
      · simp only [ht, ↓reduceIte, ENNReal.ofReal_one]
        exact prob_le_one, hΨ⟩
  refine ⟨X', hX'm, fun t ht => ?_, hX'Ψ⟩
  have := hX'T t
  simp only [ht, ↓reduceIte] at this
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) this

/-- Almost surely, the Dirichlet problem for the transposed field on every ball with an `L²`
right-hand side has an `H¹₀` solution. -/
theorem decayEst_exist_ae [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ ω ∂P.toMeasure, ∀ (R' : ℝ) (g : Vec d → ℝ), 0 < R' →
      MemLp g 2 (volume.restrict (euclidBall (d := d) R')) →
      ∃ v : H10Function (euclidBall (d := d) R'),
        IsWeakSolutionOn (fun x => matTranspose (fullCoefficientRecentered nu ω x))
          (euclidBall R') v.toH1Function g (fun _ => 0) := by
  have h1 := rc_ae_dirichlet_wellPosed (d := d) hJ3 hnu
  have h2 : ∀ᵐ ω ∂P.toMeasure, (fun b : Vec d → Mat d => ∀ (R' : ℝ) (g : Vec d → ℝ), 0 < R' →
      MemLp g 2 (volume.restrict (euclidBall (d := d) R')) →
      ∃ u : H1Function (euclidBall (d := d) R'),
        IsDirichletSolution b (euclidBall R') g 0 u) (fullCoefficientRecentered nu ω) := by
    filter_upwards [h1] with ω hω R' g hR' hg
    have hb : Bornology.IsBounded (euclidBall (d := d) R') :=
      Metric.isBounded_ball.subset (euclidBall_subset_ball hR')
    obtain ⟨u, hu⟩ := ((hω _ (isOpen_euclidBall R') hb g hg 0).1 1 one_pos).1
    refine ⟨u, ?_⟩
    have hfun : epField nu ω 1 = fullCoefficientRecentered nu ω := by
      funext x
      simp [epField]
    rwa [hfun] at hu
  have h3 := adjField_ae_transpose hJ4 nu
    (Ψ := fun b : Vec d → Mat d => ∀ (R' : ℝ) (g : Vec d → ℝ), 0 < R' →
      MemLp g 2 (volume.restrict (euclidBall (d := d) R')) →
      ∃ u : H1Function (euclidBall (d := d) R'),
        IsDirichletSolution b (euclidBall R') g 0 u) h2
  filter_upwards [h3] with ω hω R' g hR' hg
  obtain ⟨u, hu⟩ := hω R' g hR' hg
  obtain ⟨w, -, hw⟩ := decayEst_h10_of_dirichlet (isOpen_euclidBall R') hu
  exact ⟨w, hw⟩

end

end

end SuperdiffusionCLT.Section8
