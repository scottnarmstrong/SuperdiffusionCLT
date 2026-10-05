/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.EuclidBall
public import SuperdiffusionCLT.Section6.Prereq.FullField
public import SuperdiffusionCLT.Section6.Prereq.GrowthSpace
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Homogenization.PDE.Harmonic

@[expose] public section

open scoped ENNReal

namespace SuperdiffusionCLT.Section6.Root

open MeasureTheory

/-- `C₀ L^{-(1-σ)/2} log L ≤ (C₀/ε) L^{-α}` with `ε = (1-σ)/2 - α`, for every `L > 0`. -/
private theorem s6w0_flat_absorb {C₀ α σ L : ℝ} (hC₀ : 0 ≤ C₀) (hα : α < (1 - σ) / 2) (hL : 0 < L) :
    C₀ * L ^ (-((1 - σ) / 2)) * Real.log L ≤
      C₀ / ((1 - σ) / 2 - α) * L ^ (-α) := by
  have hε : 0 < (1 - σ) / 2 - α := by linarith only [hα]
  have hlog := Real.log_le_rpow_div hL.le hε
  have hpow : 0 ≤ C₀ * L ^ (-((1 - σ) / 2)) := mul_nonneg hC₀ (Real.rpow_nonneg hL.le _)
  calc C₀ * L ^ (-((1 - σ) / 2)) * Real.log L
      ≤ C₀ * L ^ (-((1 - σ) / 2)) * (L ^ ((1 - σ) / 2 - α) / ((1 - σ) / 2 - α)) :=
        mul_le_mul_of_nonneg_left hlog hpow
    _ = C₀ / ((1 - σ) / 2 - α) * (L ^ (-((1 - σ) / 2)) * L ^ ((1 - σ) / 2 - α)) := by
        field_simp
    _ = C₀ / ((1 - σ) / 2 - α) * L ^ (-α) := by
        rw [← Real.rpow_add hL]
        congr 2
        ring

/-- The `O_{Γ_σ}` tail of `log X` gives the printed tail of `X` (`e.Xgamma.Xi`). -/
private theorem s6w0_tail_of_isBigOWith {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {σ Ctail C : ℝ} (hσ : 0 < σ) (hCt : 0 < Ctail)
    (hT : Homogenization.IndependentSums.IsBigOWith μ
      (Homogenization.IndependentSums.gammaSigma σ) (fun ω => Real.log (X ω)) Ctail)
    (hC1 : 1 ≤ C) (hCexp : Real.exp (Ctail ^ σ) ≤ C) {t : ℝ} (ht : 2 ≤ t) :
    μ.real {ω | t < X ω} ≤ C * Real.exp (-(C⁻¹ * Real.log t ^ σ)) := by
  have ht0 : 0 < t := by linarith only [ht]
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith only [ht])
  have hT0 : 0 < Ctail ^ σ := Real.rpow_pos_of_pos hCt σ
  have hTC : Ctail ^ σ ≤ C := by
    have := Real.add_one_le_exp (Ctail ^ σ)
    linarith only [this, hCexp]
  have hC0 : 0 < C := by linarith only [hC1]
  have ha0 : 0 ≤ Real.log t ^ σ := Real.rpow_nonneg hlog0 σ
  have hCinv : C⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC1
  by_cases h : Ctail ≤ Real.log t
  · have hs : 1 ≤ Real.log t / Ctail := (one_le_div hCt).2 h
    have hsub : {ω | t < X ω} ⊆ Homogenization.IndependentSums.upperTailEvent
        (fun ω => Real.log (X ω)) (Ctail * (Real.log t / Ctail)) := by
      intro ω hω
      show Ctail * (Real.log t / Ctail) < Real.log (X ω)
      rw [mul_div_cancel₀ _ hCt.ne']
      exact Real.log_lt_log ht0 hω
    have h1 := (measureReal_mono hsub).trans (hT hs)
    have hpow : (Real.log t / Ctail) ^ σ = Real.log t ^ σ / Ctail ^ σ :=
      Real.div_rpow hlog0 hCt.le σ
    have hexp : (Homogenization.IndependentSums.gammaSigma σ (Real.log t / Ctail))⁻¹ =
        Real.exp (-(Real.log t ^ σ / Ctail ^ σ)) := by
      simp only [Homogenization.IndependentSums.gammaSigma, hpow, Real.exp_neg]
    rw [hexp] at h1
    have hle : C⁻¹ * Real.log t ^ σ ≤ Real.log t ^ σ / Ctail ^ σ := by
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right ((inv_le_inv₀ hC0 hT0).2 hTC) ha0
    have hmono : Real.exp (-(Real.log t ^ σ / Ctail ^ σ)) ≤
        Real.exp (-(C⁻¹ * Real.log t ^ σ)) :=
      Real.exp_le_exp.2 (neg_le_neg hle)
    have hpos : 0 ≤ Real.exp (-(C⁻¹ * Real.log t ^ σ)) := (Real.exp_pos _).le
    calc μ.real {ω | t < X ω} ≤ Real.exp (-(Real.log t ^ σ / Ctail ^ σ)) := h1
      _ ≤ Real.exp (-(C⁻¹ * Real.log t ^ σ)) := hmono
      _ = 1 * Real.exp (-(C⁻¹ * Real.log t ^ σ)) := (one_mul _).symm
      _ ≤ C * Real.exp (-(C⁻¹ * Real.log t ^ σ)) := mul_le_mul_of_nonneg_right hC1 hpos
  · replace h : Real.log t < Ctail := not_le.1 h
    have ha : Real.log t ^ σ ≤ Ctail ^ σ := Real.rpow_le_rpow hlog0 h.le hσ.le
    have hb : C⁻¹ * Real.log t ^ σ ≤ Ctail ^ σ := by
      have : C⁻¹ * Real.log t ^ σ ≤ 1 * Real.log t ^ σ := mul_le_mul_of_nonneg_right hCinv ha0
      linarith only [this, ha]
    have hexp : Real.exp (-(Ctail ^ σ)) ≤ Real.exp (-(C⁻¹ * Real.log t ^ σ)) :=
      Real.exp_le_exp.2 (neg_le_neg hb)
    have hone : 1 ≤ C * Real.exp (-(C⁻¹ * Real.log t ^ σ)) := by
      have h2 : Real.exp (Ctail ^ σ) * Real.exp (-(Ctail ^ σ)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      calc (1 : ℝ) = Real.exp (Ctail ^ σ) * Real.exp (-(Ctail ^ σ)) := h2.symm
        _ ≤ C * Real.exp (-(C⁻¹ * Real.log t ^ σ)) :=
          mul_le_mul hCexp hexp (Real.exp_pos _).le hC0.le
    exact (measureReal_le_one).trans hone

/-- **`t.C1beta` from `p.C1beta.sharp`** with `ρ = σ` and `X ↦ max X 2`.
Hypothesis: the body of `Frozen.Section6.c1beta_sharp`; conclusion: the body of
`Frozen.Section6.c1beta`, both stated verbatim. -/
theorem c1beta_of_sharp (d : ℕ) [NeZero d]
    (hSharp :
      ∃ C : ℝ, 1 ≤ C ∧
        ∀ γ ρ : ℝ, 0 < γ → γ < 1 → 0 < ρ → ρ < 1 →
          ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
            ∀ cStar : ℝ, 0 < cStar →
              ∀ K : ℝ,
                ∃ Ctail : ℝ, 0 < Ctail ∧
                  ∀ (P : MeasureTheory.ProbabilityMeasure
                        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                        hPrefix hJ2 hJ3 →
                    ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                      Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
                      Homogenization.IndependentSums.IsBigOWith P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma ρ)
                        (fun omega => Real.log (X omega)) Ctail ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                        -- Liouville theorem
                        (Module.finrank ℝ
                            (Submodule.span ℝ
                              (SuperdiffusionCLT.Section6.growthSpace
                                (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                                γ)) = 1 + d ∧
                          ∀ γ' : ℝ, 0 < γ' → γ' < 1 →
                            SuperdiffusionCLT.Section6.growthSpace
                                (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                                γ' =
                              SuperdiffusionCLT.Section6.growthSpace
                                (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                                γ) ∧
                        -- flatness at every scale
                        (∀ φ ∈ SuperdiffusionCLT.Section6.growthSpace
                              (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) γ,
                          ∀ r : ℝ, X omega ≤ r →
                            (⨅ e : Homogenization.Vec d,
                                SuperdiffusionCLT.Section6.ballL2 r
                                  (fun x => φ x - Homogenization.vecDot e x -
                                    ∫ y, φ y ∂SuperdiffusionCLT.Section6.ballMeasure r)) ≤
                              ENNReal.ofReal
                                  (C * Real.log r ^ (-((1 - ρ) / 2)) * Real.log (Real.log r)) *
                                SuperdiffusionCLT.Section6.ballL2 r φ) ∧
                        -- large-scale C^{1,γ} estimate
                        (∀ R : ℝ, X omega ≤ R →
                          ∀ (u : Homogenization.Vec d → ℝ)
                            (g : Homogenization.Vec d → Homogenization.Vec d),
                            SuperdiffusionCLT.Section6.IsBallSolution
                                (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                                R u g →
                              ∃ φ ∈ SuperdiffusionCLT.Section6.growthSpace
                                  (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                                  γ,
                                ∃ gφ : Homogenization.Vec d → Homogenization.Vec d,
                                  SuperdiffusionCLT.Section6.IsEntireSolution
                                      (SuperdiffusionCLT.Section6.fullCoefficientRecentered
                                        nu omega) φ gφ ∧
                                    ∀ r : ℝ, X omega ≤ r → r < R →
                                      SuperdiffusionCLT.Section6.ballGradL2 r
                                          (fun x => g x - gφ x) ≤
                                        ENNReal.ofReal (C * (r / R) ^ γ) *
                                          SuperdiffusionCLT.Section6.ballGradL2 R g)) :
    ∀ α γ σ : ℝ, 0 < γ → γ < 1 → 0 < σ → σ < 1 → 0 < α → α < (1 - σ) / 2 →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∃ C : ℝ, 1 ≤ C ∧
              ∀ (P : MeasureTheory.ProbabilityMeasure
                    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                    hPrefix hJ2 hJ3 →
                ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                  Measurable X ∧ (∀ omega, 2 ≤ X omega) ∧
                  -- e.Xgamma.Xi
                  (∀ t : ℝ, 2 ≤ t →
                    P.toMeasure.real {omega | t < X omega} ≤
                      C * Real.exp (-(C⁻¹ * Real.log t ^ σ))) ∧
                  ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                    -- Liouville theorem
                    (Module.finrank ℝ
                        (Submodule.span ℝ
                          (SuperdiffusionCLT.Section6.growthSpace
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                            γ)) = 1 + d ∧
                      ∀ γ' : ℝ, 0 < γ' → γ' < 1 →
                        SuperdiffusionCLT.Section6.growthSpace
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                            γ' =
                          SuperdiffusionCLT.Section6.growthSpace
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                            γ) ∧
                    -- e.flatness.at.every.scale
                    (∀ φ ∈ SuperdiffusionCLT.Section6.growthSpace
                          (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) γ,
                      ∀ r : ℝ, X omega ≤ r →
                        (⨅ e : Homogenization.Vec d,
                            SuperdiffusionCLT.Section6.ballL2 r
                              (fun x => φ x - Homogenization.vecDot e x -
                                ∫ y, φ y ∂SuperdiffusionCLT.Section6.ballMeasure r)) ≤
                          ENNReal.ofReal (C * Real.log r ^ (-α)) *
                            SuperdiffusionCLT.Section6.ballL2 r φ) ∧
                    -- e.largescaleC1gamma
                    (∀ R : ℝ, X omega ≤ R →
                      ∀ (u : Homogenization.Vec d → ℝ)
                        (g : Homogenization.Vec d → Homogenization.Vec d),
                        SuperdiffusionCLT.Section6.IsBallSolution
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                            R u g →
                          ∃ φ ∈ SuperdiffusionCLT.Section6.growthSpace
                              (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                              γ,
                            ∃ gφ : Homogenization.Vec d → Homogenization.Vec d,
                              SuperdiffusionCLT.Section6.IsEntireSolution
                                  (SuperdiffusionCLT.Section6.fullCoefficientRecentered
                                    nu omega) φ gφ ∧
                                ∀ r : ℝ, X omega ≤ r → r < R →
                                  SuperdiffusionCLT.Section6.ballGradL2 r
                                      (fun x => g x - gφ x) ≤
                                    ENNReal.ofReal (C * (r / R) ^ γ) *
                                      SuperdiffusionCLT.Section6.ballGradL2 R g) := by
  obtain ⟨C₀, hC₀, hS⟩ := hSharp
  intro α γ σ hγ0 hγ1 hσ0 hσ1 hα0 hα1 nu hnu hnu1 cStar hc K
  obtain ⟨Ctail, hCt, hS⟩ := hS γ σ hγ0 hγ1 hσ0 hσ1 nu hnu hnu1 cStar hc K
  set B : ℝ := C₀ / ((1 - σ) / 2 - α) with hB
  set C : ℝ := max (max 1 C₀) (max B (Real.exp (Ctail ^ σ))) with hCdef
  have hC1 : 1 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCC₀ : C₀ ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCB : B ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCexp : Real.exp (Ctail ^ σ) ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, hC1, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X, hXm, hX1, hXt, hae⟩ := hS P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨fun ω => max (X ω) 2, hXm.max measurable_const, fun ω => le_max_right _ _, ?_, ?_⟩
  · intro t ht
    have hset : {ω | t < max (X ω) 2} = {ω | t < X ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, lt_max_iff]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h (not_lt.2 ht)
      · exact Or.inl
    rw [hset]
    exact s6w0_tail_of_isBigOWith hσ0 hCt hXt hC1 hCexp ht
  · filter_upwards [hae] with ω hω
    obtain ⟨hL, hF, hC⟩ := hω
    refine ⟨hL, ?_, ?_⟩
    · intro φ hφ r hr
      have hXr : X ω ≤ r := le_trans (le_max_left _ _) hr
      have h2r : 2 ≤ r := le_trans (le_max_right _ _) hr
      refine (hF φ hφ r hXr).trans ?_
      gcongr ?_ * _
      refine ENNReal.ofReal_le_ofReal ?_
      have hL0 : 0 < Real.log r := Real.log_pos (by linarith only [h2r])
      have h1 := s6w0_flat_absorb (le_trans zero_le_one hC₀) hα1 hL0
      have h2 : B * Real.log r ^ (-α) ≤ C * Real.log r ^ (-α) :=
        mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg hL0.le _)
      exact h1.trans h2
    · intro R hR u g hu
      have hXR : X ω ≤ R := le_trans (le_max_left _ _) hR
      obtain ⟨φ, hφ, gφ, hgφ, hb⟩ := hC R hXR u g hu
      refine ⟨φ, hφ, gφ, hgφ, fun r hr hrR => ?_⟩
      have hXr : X ω ≤ r := le_trans (le_max_left _ _) hr
      have h2r : 2 ≤ r := le_trans (le_max_right _ _) hr
      have hR0 : 0 < R := by linarith only [h2r, hrR]
      have hq : 0 ≤ (r / R) ^ γ := Real.rpow_nonneg (div_nonneg (by linarith only [h2r]) hR0.le) _
      refine (hb r hXr hrR).trans ?_
      gcongr ?_ * _
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCC₀ hq)

end SuperdiffusionCLT.Section6.Root
