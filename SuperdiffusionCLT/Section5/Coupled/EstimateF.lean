/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Coupled.EstimateE

/-!
# `lem.coupled.input`: the statement

The assembly of `e.coupled.estimate.explicit` from `coupled_Rz` (`Rz`), `coupled_hgradw`
(`hgradw`), the bulk inequality with the energy identity (`coupled_bulk_det`), and clause 3 of
`response_estimates` (the energy lower bound).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section3.ResponseFields (vecCubeLpENorm)
open scoped ENNReal

variable {d : ℕ}

/-- **`lem.coupled.input`** (`e.coupled.estimate.explicit`). -/
theorem coupled_input (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C₀ C : ℝ, 1 ≤ C₀ ∧ 1 ≤ C ∧ ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
      ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
        (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
        ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∀ m h : ℕ, 1 ≤ h → 400 * h ≤ m →
        2 * SuperdiffusionCLT.Frozen.Section4.lNaught C₀ C₀ (3 / 4) cStar nu K ≤ (m : ℝ) →
        ∀ n : ℕ, n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊ →
        ∀ e : Vec d, vecNormSq e = 1 →
        ∀ (wD : ∀ Kc : ℕ, ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ)))),
          (∀ Kc : ℕ, 100 * m ≤ Kc → ∀ omega,
            SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
              (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD Kc omega)) →
          Filter.limsup (fun Kc : ℕ => subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal
              (blockVecDot (coupledVec nu P m h Q ω e (wD Kc ω).toH1Function.grad)
                (coupledVec nu P m h Q ω e (wD Kc ω).toH1Function.grad)) ∂P.toMeasure))
              Filter.atTop ≤
            ENNReal.ofReal (1 - cStar * Real.log 3 * h * (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ)) +
              K * (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ)) +
              C * (sigmaBarInfinite nu (m - h) P) ^ (-(4 : ℝ)) * (h : ℝ) ^ 2) := by
  obtain ⟨Cr, hCr1, HR⟩ := coupled_Rz d hd
  obtain ⟨Cg, hCg1, HG⟩ := coupled_hgradw d hd
  obtain ⟨Cs, hCs1, HS⟩ := response_estimates d hd
  obtain ⟨C₀, Ce, hC₀, hCe, HSc⟩ := coupled4_scales d
  refine ⟨C₀, (Cg + Cr) ^ 2 + 2 * Cr * Ce ^ 2, hC₀, ?_, ?_⟩
  · have h1 : 1 ≤ (Cg + Cr) ^ 2 := by nlinarith only [hCg1, hCr1]
    have h2 : 0 ≤ 2 * Cr * Ce ^ 2 := by positivity
    linarith only [h1, h2]
  intro nu cStar K hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 hJ5 m h hh h400 hm n hn e he wD hwD
  obtain ⟨hmR, hnum, hσm⟩ := HSc nu cStar K hnu hnu1 P hPre hJ2 hJ3 hJ4 hJ5 m h hh h400 hm
  have hnm := scale_le_sub hnu hnu1 h400 hmR hnum hn
  have hσ : 0 < sigmaBarInfinite nu (m - h) P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu (m - h) hPre hJ2 hJ3 hJ4
  set σ := sigmaBarInfinite nu (m - h) P with hσdef
  set c : ℝ := σ⁻¹ with hc
  have hc0 : 0 < c := inv_pos.mpr hσ
  have hσ2 : σ ^ (-(2 : ℝ)) = c ^ 2 := coupled4_rpow_neg_two hσ
  have hσ4 : σ ^ (-(4 : ℝ)) = c ^ 4 := coupled4_rpow_neg_four hσ
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hmR
  have hm0 : (0 : ℝ) < m := by linarith only [hm']
  set μ : ℝ := (m : ℝ) ^ (-(100 : ℝ)) with hμdef
  have hpow : μ = ((m : ℝ) ^ 100)⁻¹ := by
    rw [hμdef, Real.rpow_neg hm0.le, show (100 : ℝ) = ((100 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hμ0 : 0 < μ := by rw [hpow]; positivity
  have hμ1 : μ ≤ 1 := by
    rw [hpow]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith only [hm']))
  have hμc : μ ≤ Ce ^ 2 * c ^ 2 := by
    have hs2 : σ ^ 2 ≤ Ce ^ 2 * (m : ℝ) ^ 4 := by
      have := pow_le_pow_left₀ hσ.le hσm 2
      calc σ ^ 2 ≤ (Ce * (m : ℝ) * m) ^ 2 := this
        _ = Ce ^ 2 * (m : ℝ) ^ 4 := by ring
    have hm4 : (m : ℝ) ^ 4 ≤ (m : ℝ) ^ 100 :=
      pow_le_pow_right₀ (by linarith only [hm']) (by norm_num)
    have hμm : μ * (m : ℝ) ^ 4 ≤ 1 := by
      rw [hpow, ← div_eq_inv_mul, div_le_one (by positivity)]
      exact hm4
    have hμσ : μ * σ ^ 2 ≤ Ce ^ 2 := by
      calc μ * σ ^ 2 ≤ μ * (Ce ^ 2 * (m : ℝ) ^ 4) := mul_le_mul_of_nonneg_left hs2 hμ0.le
        _ = Ce ^ 2 * (μ * (m : ℝ) ^ 4) := by ring
        _ ≤ Ce ^ 2 * 1 := mul_le_mul_of_nonneg_left hμm (by positivity)
        _ = Ce ^ 2 := by ring
    have hcσ : σ ^ 2 * c ^ 2 = 1 := by rw [hc]; field_simp
    calc μ = μ * σ ^ 2 * c ^ 2 := by rw [mul_assoc, hcσ, mul_one]
      _ ≤ Ce ^ 2 * c ^ 2 := mul_le_mul_of_nonneg_right hμσ (by positivity)
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by linarith only [hh1]
  set b : ℝ := Cg * c * h with hb
  set r : ℝ := Cr * c * μ with hr
  have hb0 : 0 < b := by positivity
  have hr0 : 0 < r := by positivity
  set T0 : ℝ := 1 - cStar * Real.log 3 * h * c ^ 2 + K * c ^ 2 +
    ((Cg + Cr) ^ 2 + 2 * Cr * Ce ^ 2) * c ^ 4 * (h : ℝ) ^ 2 with hT0
  set εf : ℕ → ℝ := fun Kc => Cs * (h : ℝ) ^ ((4 : ℝ) / 5) *
    ((1 + ((Kc - m : ℕ) : ℝ)) ^ ((2 : ℝ) / 5) *
      (3 : ℝ) ^ (-((2 : ℝ) / 5 * ((Kc - m : ℕ) : ℝ)))) with hεf
  have hper : ∀ Kc : ℕ, 100 * m ≤ Kc →
      subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal
        (blockVecDot (coupledVec nu P m h Q ω e (wD Kc ω).toH1Function.grad)
          (coupledVec nu P m h Q ω e (wD Kc ω).toH1Function.grad)) ∂P.toMeasure) ≤
        ENNReal.ofReal (T0 + εf Kc * c ^ 2) := by
    intro Kc hKc
    have hnK : n ≤ Kc := by omega
    obtain ⟨-, wN, -, hwN⟩ := exists_responses_hshellFlux nu P m h Kc e
    have hHD : ∀ omega, Nonempty (HasWeakHessianOn (openCubeSet (originCube d (Kc : ℤ)))
        (wD Kc omega).toH1Function) := fun omega =>
      SuperdiffusionCLT.Section3.ResponseFields.exists_hasWeakHessianOn_dirichletResponse hd
        omega (Nat.sub_le m h) (c • e) (wD Kc omega) (by
          have hw := hwD Kc hKc omega
          rw [responseData_hshellFlux_eq_dirichletRhsField] at hw
          exact hw)
    have hRb := HR nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc n hh h400 hKc hmR hnum hn e he.le
      (wD Kc) wN (hwD Kc hKc) hwN hHD
    have hGb := HG nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 hKc e he.le (wD Kc)
      (hwD Kc hKc)
    obtain ⟨-, -, hcl3⟩ := HS nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 cStar K hJ5 m h Kc hh h400 hKc e
      he.le (wD Kc) wN (hwD Kc hKc) hwN
    have hcl := (hcl3 he).1
    have hH : ∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2
        (fun x => matVecMul (finiteShellIncrement omega (m - h) m x)
          ((wD Kc omega).toH1Function.grad x)) ^ (2 : ℕ) ∂P.toMeasure ≤ ENNReal.ofReal (b ^ 2) := by
      refine hGb.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hσ2, hb]
      have : Cg * c ^ 2 * (h : ℝ) ^ 2 ≤ Cg ^ 2 * c ^ 2 * (h : ℝ) ^ 2 := by
        have : Cg ≤ Cg ^ 2 := by nlinarith only [hCg1]
        gcongr
      linarith only [this, show (Cg * c * (h : ℝ)) ^ 2 = Cg ^ 2 * c ^ 2 * (h : ℝ) ^ 2 by ring]
    have hR : subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
        (vecNormSq (coupledR m h Q omega (wD Kc omega).toH1Function.grad)) ∂P.toMeasure) ≤
        ENNReal.ofReal (r ^ 2) :=
      coupled4_sq_of_sqrt_le hr0.le hRb
    have hbulk := coupled_bulk nu P m h Kc n hnK e he (wD Kc) (hwD Kc hKc)
    have hGfin : ∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2
        (wD Kc omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (le_add_self.trans hbulk)
      exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH)⟩
    set gl : ℝ := cStar * Real.log 3 * h * c ^ 2 - (εf Kc + K) * c ^ 2 with hgl
    have hG : ENNReal.ofReal gl ≤ ∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2
        (wD Kc omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure := by
      rw [← ENNReal.ofReal_toReal hGfin]
      refine ENNReal.ofReal_le_ofReal ?_
      have := (abs_le.mp hcl).1
      rw [hσ2] at this
      rw [hgl, hεf]
      linarith only [this]
    have hfix := coupled4_fixed nu P m h Kc n hnK hσ e he (wD Kc) (hwD Kc hKc) b r gl hb0 hr0 hH
      hR hG
    refine hfix.trans (ENNReal.ofReal_le_ofReal ?_)
    have hal := coupled4_algebra c μ h Cg Cr Ce hμ0 hμ1 hh1 hCg1 hCr1 hμc
    rw [hgl, hT0]
    rw [← hc, hb, hr] 
    linarith only [hal]
  have hlim : Tendsto (fun Kc : ℕ => ENNReal.ofReal (T0 + εf Kc * c ^ 2)) atTop
      (𝓝 (ENNReal.ofReal T0)) := by
    refine ENNReal.tendsto_ofReal ?_
    have ht : Tendsto (fun Kc : ℕ => ((Kc - m : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat m)
    have h1 : Tendsto εf atTop (𝓝 0) := by
      have := (tendsto_tail.comp ht).const_mul (Cs * (h : ℝ) ^ ((4 : ℝ) / 5))
      rw [mul_zero] at this
      exact this
    have h2 := (tendsto_const_nhds (x := T0)).add (h1.mul_const (c ^ 2))
    simpa using h2
  calc _ ≤ Filter.limsup (fun Kc : ℕ => ENNReal.ofReal (T0 + εf Kc * c ^ 2)) atTop :=
        Filter.limsup_le_limsup (Filter.eventually_atTop.2 ⟨100 * m, hper⟩)
    _ = ENNReal.ofReal T0 := hlim.limsup_eq
    _ = _ := by rw [hσ2, hσ4, hT0]

/-- **Satisfiability witness for the non-law hypotheses of `coupled_input`**: for every shell law
the scale hypothesis `2 L₀ ≤ m` is met by a large `m` (with `h = 1`), a unit vector exists, and a
selection of the Dirichlet response exists on every cube.  (The law hypothesis `J5` is not met by
the Dirac law; it is the one assumed of the shell law.) -/
example [NeZero d] (nu cStar K C₀ : ℝ) (P : ProbabilityMeasure (ShellSeq d)) :
    ∃ m h : ℕ, 1 ≤ h ∧ 400 * h ≤ m ∧
      2 * SuperdiffusionCLT.Frozen.Section4.lNaught C₀ C₀ (3 / 4) cStar nu K ≤ (m : ℝ) ∧
      ∃ n : ℕ, n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊ ∧
      ∃ e : Vec d, vecNormSq e = 1 ∧
      ∃ wD : ∀ Kc : ℕ, ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))),
        ∀ Kc : ℕ, 100 * m ≤ Kc → ∀ omega,
          SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
            (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD Kc omega) := by
  set L := SuperdiffusionCLT.Frozen.Section4.lNaught C₀ C₀ (3 / 4) cStar nu K
  refine ⟨max 400 ⌈2 * L⌉₊, 1, le_rfl, le_max_left _ _, ?_, _, rfl, Pi.single 0 1, ?_, ?_⟩
  · exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  · simp [vecNormSq, vecDot, Pi.single_apply]
  · choose wD hwD using fun Kc : ℕ =>
      exists_responses_hshellFlux nu P (max 400 ⌈2 * L⌉₊) 1 Kc (Pi.single 0 1 : Vec d)
    exact ⟨fun Kc => wD Kc, fun Kc _ omega => (hwD Kc).choose_spec.1 omega⟩

end SuperdiffusionCLT.Section5
