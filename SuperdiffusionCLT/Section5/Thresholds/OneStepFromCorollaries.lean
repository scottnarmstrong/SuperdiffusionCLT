/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Thresholds.OneStepFromCorollariesB
public import SuperdiffusionCLT.Section5.Thresholds.ThresholdChain
public import SuperdiffusionCLT.Frozen.Section4.SigmaBarCutoffComparison
public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences

/-!
# `p.one.step.sharp` from the two one-sided ratio corollaries

The proposition follows from `cor.upper.ratio` and `cor.lower.ratio` (taken as hypotheses
`hUpper`, `hLower`, stated verbatim) and the growth bracket `e.sL.growth`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

theorem lower_coeff_one_step {Cg cStar nu : ℝ} (hCg : 0 < Cg) (hc : 0 < cStar) (hnu : 0 < nu) :
    (max 1 (Cg * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ))))⁻¹ ≤
      Cg⁻¹ * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) := by
  have hB : 0 < Cg * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) := by positivity
  have h1 : (max 1 (Cg * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ))))⁻¹ ≤
      (Cg * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)))⁻¹ :=
    inv_anti₀ hB (le_max_right _ _)
  refine h1.trans (le_of_eq ?_)
  rw [Real.rpow_neg hc.le, Real.rpow_neg hnu.le, mul_inv, mul_inv, inv_inv, inv_inv]

/-- Monotonicity in the constant of the right side of the one-sided ratio bounds. -/
theorem ratio_rhs_mono {C' C b Lm K s h : ℝ} (hC : C' ≤ C) (hL : 0 ≤ Lm + K) (hs : 0 < s) :
    1 + (b + C' * (Lm + K)) * s ^ (-(2 : ℝ)) + C' * s ^ (-(4 : ℝ)) * h ^ (2 : ℝ) ≤
      1 + (b + C * (Lm + K)) * s ^ (-(2 : ℝ)) + C * s ^ (-(4 : ℝ)) * h ^ (2 : ℝ) := by
  have h2 : 0 ≤ s ^ (-(2 : ℝ)) := by positivity
  have h4 : 0 ≤ s ^ (-(4 : ℝ)) * h ^ (2 : ℝ) := by
    have : 0 ≤ h ^ (2 : ℝ) := by rw [Real.rpow_two]; positivity
    positivity
  have := mul_nonneg (sub_nonneg.2 hC) (add_nonneg (mul_nonneg hL h2) h4)
  linarith only [this]

/-- `1 ≤ log 3`. -/
theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have := Real.exp_one_lt_d9
  rw [Real.le_log_iff_exp_le (by norm_num)]
  linarith only [this]

/-- Scale arithmetic for `m = n + h`: from `399 h ≤ n` and `3 ≤ n`, `log²(n+h) ≤ 4 log² n`. -/
theorem log_sq_add_le {n h : ℕ} (hn : 3 ≤ n) (hh : 399 * h ≤ n) :
    Real.log ((n + h : ℕ) : ℝ) ^ (2 : ℝ) ≤ 4 * Real.log (n : ℝ) ^ (2 : ℝ) := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hhn : (h : ℝ) ≤ n := by
    have : h ≤ n := by omega
    exact_mod_cast this
  have h1 : ((n + h : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    push_cast; nlinarith only [hn3, hhn]
  have h2 : Real.log ((n + h : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hpos : (0 : ℝ) < ((n + h : ℕ) : ℝ) := by push_cast; linarith only [hn3]
    have := Real.log_le_log hpos h1
    rw [Real.log_pow] at this
    simpa using this
  have h3 : 0 ≤ Real.log ((n + h : ℕ) : ℝ) := Real.log_natCast_nonneg _
  rw [Real.rpow_two, Real.rpow_two]
  nlinarith only [h2, h3]

/-- **`p.one.step.sharp` from `cor.upper.ratio` and `cor.lower.ratio`**. -/
theorem sigmaBar_one_step_of_corollaries (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hUpper : ∃ C₀ C : ℝ, 1 ≤ C₀ ∧ 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ m h : ℕ, 1 ≤ h → 400 * h ≤ m →
            2 * SuperdiffusionCLT.Frozen.Section4.lNaught C₀ C₀ (3 / 4) cStar nu K ≤ (m : ℝ) →
            SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P)⁻¹ ≤
              1 + (cStar * Real.log 3 * (h : ℝ) + C * (Real.log (m : ℝ) ^ (2 : ℝ) + K)) *
                  (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^
                    (-(2 : ℝ)) +
                C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^
                  (-(4 : ℝ)) * (h : ℝ) ^ (2 : ℝ))
    (hLower : ∃ C₀ C : ℝ, 1 ≤ C₀ ∧ 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ m h : ℕ, 1 ≤ h → 400 * h ≤ m →
            2 * SuperdiffusionCLT.Frozen.Section4.lNaught C₀ C₀ (3 / 4) cStar nu K ≤ (m : ℝ) →
            SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P *
                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ ≤
              1 + (-(cStar * Real.log 3 * (h : ℝ)) + C * (Real.log (m : ℝ) ^ (2 : ℝ) + K)) *
                  (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^
                    (-(2 : ℝ)) +
                C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^
                  (-(4 : ℝ)) * (h : ℝ) ^ (2 : ℝ)) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∃ M : ℕ,
              ∀ (P : MeasureTheory.ProbabilityMeasure
                    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                    hPrefix hJ2 hJ3 →
                  ∀ n : ℕ, M ≤ n →
                    ∀ h : ℕ, 1 ≤ h →
                      (h : ℝ) ≤ SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P →
                        |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (n + h) P -
                            SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P -
                            cStar * Real.log 3 *
                              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P)⁻¹ *
                                (h : ℝ)| ≤
                          C * (Real.log (n : ℝ) ^ (2 : ℝ) + K) *
                            (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P)⁻¹ := by
  obtain ⟨C₀u, Cu, hC₀u, hCu, hu⟩ := hUpper
  obtain ⟨C₀l, Cl, hC₀l, hCl, hl⟩ := hLower
  obtain ⟨Cg, hCg, -, hgrowth⟩ :=
    SuperdiffusionCLT.Frozen.Section4.sigmaBar_cutoff_comparison d hd
  have hCm : 1 ≤ max Cu Cl := le_trans hCu (le_max_left _ _)
  refine ⟨5 * max Cu Cl, by linarith only [hCm], fun nu hnu hnu1 c hc K => ?_⟩
  obtain ⟨Lg, hLg⟩ := hgrowth nu hnu hnu1 c hc K
  have hCg0 : 0 < Cg := lt_of_lt_of_le one_pos hCg
  set A : ℝ := max 1 (Cg * c ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ))) with hAdef
  have hA0 : 0 < A := lt_of_lt_of_le one_pos (le_max_left _ _)
  obtain ⟨N1, hN13, hN1⟩ := threshold_bracket_lower A (2 * (c * Real.log 3)) 0 hA0 le_rfl
  obtain ⟨N2, -, hN2⟩ :=
    threshold_bracket_upper (399 * (Cg * c ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ))))
  refine ⟨max Lg (max N1 (max N2 (max ⌈2 * SuperdiffusionCLT.Frozen.Section4.lNaught
      C₀u C₀u (3 / 4) c nu K⌉₊ ⌈2 * SuperdiffusionCLT.Frozen.Section4.lNaught
      C₀l C₀l (3 / 4) c nu K⌉₊))), ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 n hn h h1 hhs
  have hnLg : Lg ≤ n := le_trans (le_max_left _ _) hn
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnN2 : N2 ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hn
  have hnLu : ⌈2 * SuperdiffusionCLT.Frozen.Section4.lNaught C₀u C₀u (3 / 4) c nu K⌉₊ ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hn
  have hnLl : ⌈2 * SuperdiffusionCLT.Frozen.Section4.lNaught C₀l C₀l (3 / 4) c nu K⌉₊ ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hn
  have hn3 : 3 ≤ n := le_trans hN13 hnN1
  have hK : 0 ≤ K := hJ5.K_pos.le
  -- the growth bracket at `n` and `n + h`
  obtain ⟨hlo, hhi⟩ := hLg P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 n hnLg
  have hσpos := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos
    (P := P) hnu n hPrefix hJ2 hJ3 hJ4
  have hσ'pos := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos
    (P := P) hnu (n + h) hPrefix hJ2 hJ3 hJ4
  set σ : ℝ := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P with hσ
  set σ' : ℝ := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (n + h) P with hσ'
  have hlogn : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hw : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ ((9 : ℝ) / 2) := by positivity
  have hwl : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ (-((9 : ℝ) / 2)) := by positivity
  have hσlow : A⁻¹ * (n : ℝ) ^ (1 / 2 : ℝ) * Real.log (n : ℝ) ^ (-(9 / 2 : ℝ)) ≤ σ := by
    refine le_trans (le_of_eq ?_) (le_trans (mul_le_mul_of_nonneg_right
      (lower_coeff_one_step hCg0 hc hnu) hwl) ?_)
    · ring
    · exact le_of_eq (by ring) |>.trans hlo
  obtain ⟨hGσ, -⟩ := hN1 n hnN1 σ hσlow
  have h399 : 399 * σ ≤ n := by
    refine hN2 n hnN2 (399 * σ) ?_
    calc 399 * σ ≤ 399 * (Cg * c ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) *
          (n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ ((9 : ℝ) / 2)) := by
            linarith only [hhi]
      _ = _ := by ring
  have hhσ : (h : ℝ) ≤ σ := hhs
  have h399h : 399 * h ≤ n := by
    have : (399 : ℝ) * h ≤ n := by linarith only [h399, hhσ]
    exact_mod_cast this
  have h400 : 400 * h ≤ n + h := by omega
  have hscaleu : 2 * SuperdiffusionCLT.Frozen.Section4.lNaught C₀u C₀u (3 / 4) c nu K ≤
      ((n + h : ℕ) : ℝ) := by
    have h1' := Nat.le_ceil (2 * SuperdiffusionCLT.Frozen.Section4.lNaught C₀u C₀u (3 / 4) c nu K)
    have h2' : ((⌈2 * SuperdiffusionCLT.Frozen.Section4.lNaught C₀u C₀u (3 / 4) c nu K⌉₊ : ℕ) : ℝ)
        ≤ ((n + h : ℕ) : ℝ) := by exact_mod_cast (by omega : _ ≤ n + h)
    linarith only [h1', h2']
  have hscalel : 2 * SuperdiffusionCLT.Frozen.Section4.lNaught C₀l C₀l (3 / 4) c nu K ≤
      ((n + h : ℕ) : ℝ) := by
    have h1' := Nat.le_ceil (2 * SuperdiffusionCLT.Frozen.Section4.lNaught C₀l C₀l (3 / 4) c nu K)
    have h2' : ((⌈2 * SuperdiffusionCLT.Frozen.Section4.lNaught C₀l C₀l (3 / 4) c nu K⌉₊ : ℕ) : ℝ)
        ≤ ((n + h : ℕ) : ℝ) := by exact_mod_cast (by omega : _ ≤ n + h)
    linarith only [h1', h2']
  have hup := hu nu c K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 (n + h) h h1 h400 hscaleu
  have hlow := hl nu c K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 (n + h) h h1 h400 hscalel
  rw [Nat.add_sub_cancel] at hup hlow
  have hLm0 : 0 ≤ Real.log ((n + h : ℕ) : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]; positivity
  have hLmK : 0 ≤ Real.log ((n + h : ℕ) : ℝ) ^ (2 : ℝ) + K := by linarith only [hLm0, hK]
  have hup2 := le_trans hup (ratio_rhs_mono (b := c * Real.log 3 * (h : ℝ))
    (le_max_left Cu Cl) hLmK hσpos)
  have hlow2 := le_trans hlow (ratio_rhs_mono (b := -(c * Real.log 3 * (h : ℝ)))
    (le_max_right Cu Cl) hLmK hσpos)
  have hl1 : (1 : ℝ) ≤ Real.log (n : ℝ) ^ (2 : ℝ) := by
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have : 1 ≤ Real.log (n : ℝ) :=
      le_trans one_le_log_three (Real.log_le_log (by norm_num) h3)
    rw [Real.rpow_two]; nlinarith only [this]
  have hc3 : 0 < c * Real.log 3 := by
    have := one_le_log_three
    positivity
  have hh1r : (1 : ℝ) ≤ h := by exact_mod_cast h1
  exact one_step_algebra (a := c * Real.log 3) (ℓ2 := Real.log (n : ℝ) ^ (2 : ℝ))
    (Lm := Real.log ((n + h : ℕ) : ℝ) ^ (2 : ℝ)) hσpos hσ'pos hc3 hh1r hhσ hGσ
    hCm hK hl1 hLm0 (log_sq_add_le hn3 h399h) hup2 hlow2

/-- Satisfiability of the hypotheses of `one_step_algebra`
(`s = s' = h = 1`, `a = 1/2`, `C = 1`, `K = 0`, `ℓ2 = Lm = 1`). -/
example : |(1 : ℝ) - 1 - (1 / 2) * (1 : ℝ)⁻¹ * 1| ≤ 5 * 1 * (1 + 0) * (1 : ℝ)⁻¹ :=
  one_step_algebra (s := 1) (s' := 1) (a := 1 / 2) (h := 1) (C := 1) (K := 0) (ℓ2 := 1)
    (Lm := 1) one_pos one_pos (by norm_num) le_rfl le_rfl (by norm_num) le_rfl le_rfl le_rfl
    (by norm_num) (by norm_num) (by norm_num [Real.one_rpow]) (by norm_num [Real.one_rpow])

end SuperdiffusionCLT.Section5
