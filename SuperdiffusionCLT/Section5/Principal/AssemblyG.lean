/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.AssemblyF

/-!
# `lem.principal.term`

`principal_term` is the reduction of the principal term: for the subcubes
`z + cu_n`, `z ∈ 3^n ℤ^d ∩ cu_Kc`,
`avsum E[P_z · bfA_m(z+cu_n) P_z] ≤ (1 + C shom_{m-h}^{-2} log²(ν⁻¹m)) avsum E|bfAhom^{1/2} G_{-hbar_z} P_z|² + C m^{-10}`,
with `P_z = blockSlope` of the Dirichlet and Neumann responses of `hshellFlux`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section4 (lNaught)
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Probability (shellSigma shellSigma_le_ambient)
open scoped ENNReal

variable {d : ℕ}

/-- **`lem.principal.term`**, the reduction of the principal term. -/
theorem principal_term (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C₀ C : ℝ, 1 ≤ C₀ ∧ 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ m h Kc : ℕ, 1 ≤ h → 400 * h ≤ m → 100 * m ≤ Kc →
          2 * lNaught C₀ C₀ (3 / 4) cStar nu K ≤ (m : ℝ) →
          ∀ e e' : Vec d, vecNormSq e ≤ 1 → vecNormSq e' ≤ 1 →
          ∀ n : ℕ, n = ⌊(m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3)⌋₊ →
          ∀ (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
            (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
            (∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
              (hshellFlux nu P m h omega e) (wD omega)) →
            (∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
              (hshellFlux nu P m h omega e') (wN omega)) →
          subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
              (blockVecDot
                (blockSlope nu (m - h) P Q e e' (wD omega).toH1Function.grad
                  (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))
                (blockMatVecMul (localizationCoarseAt nu m Q omega)
                  (blockSlope nu (m - h) P Q e e' (wD omega).toH1Function.grad
                    (fun y => (wN omega).toH1Function.grad y +
                      hshellFlux nu P m h omega e' y)))) ∂P.toMeasure) ≤
            ENNReal.ofReal (1 + C * (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ)) *
                Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ)) *
              subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
                (blockLenSq (ahomSqrtApply nu (m - h) P
                  (principalPhat m h Q omega
                    (blockSlope nu (m - h) P Q e e' (wD omega).toH1Function.grad
                      (fun y => (wN omega).toH1Function.grad y +
                        hshellFlux nu P m h omega e' y))))) ∂P.toMeasure) +
              ENNReal.ofReal (C * (m : ℝ) ^ (-(10 : ℝ))) := by
  obtain ⟨Ch, hCh1, Hh⟩ := homogBelow_at_scales d hd
  obtain ⟨Cag, hCag1, Hag⟩ := eLVsLnaughtAgain d hd
  obtain ⟨Csf, hCsf, Hsf⟩ := pa_scale_facts
  obtain ⟨C1, hC1, Hfv⟩ := principal_fv_to_inf d hd
  obtain ⟨C4, hC4, Hdz⟩ := dzp_moment d
  obtain ⟨Cu, hCu, Hu⟩ := principal_uz d hd
  set C₀ : ℝ := max (max Ch Cag) (max Csf C1) with hC₀
  set K1 : ℝ := (1 + C₀) * (C4 ^ 4 + 1 + 2048 * Cu ^ 8) with hK1
  have hC₀1 : 1 ≤ C₀ := by
    have : 1000 ≤ C₀ := le_trans hCsf (le_trans (le_max_left _ _) (le_max_right _ _))
    linarith only [this]
  have hK10 : 0 ≤ K1 := by
    rw [hK1]
    have : 0 ≤ C4 ^ 4 + 1 + 2048 * Cu ^ 8 := by positivity
    exact mul_nonneg (by linarith only [hC₀1]) this
  refine ⟨C₀, max C₀ K1, hC₀1, le_trans hC₀1 (le_max_left _ _), ?_⟩
  intro nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 m h Kc hh h400 h100 hm e e' he he' n hn
    wD wN hwD hwN
  have hcStar := hJ5.cStar_pos
  have hcStar2 := hJ5.cStar_le_two
  have hK0 := hJ5.K_pos.le
  have hCh : Ch ≤ C₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_refl _)
  have hCa : Cag ≤ C₀ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_refl _)
  have hCs : Csf ≤ C₀ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_refl _)
  have hC1' : C1 ≤ C₀ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_refl _)
  obtain ⟨hmR, hinvm, hnu2, hmn, hnmh⟩ := Hsf C₀ hCs cStar hcStar hcStar2 nu hnu hnu1 K hK0 m h n
    hh h400 hm hn
  have hnK : n ≤ Kc := by omega
  have hhm : h ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by linarith only [hmR]
  have hm1 : (1 : ℝ) ≤ m := by linarith only [hmR]
  have hσ0 : 0 < sigmaBarInfinite nu (m - h) P :=
    sigmaBarInfinite_pos hnu (m - h) hPrefix hJ2 hJ3 hJ4
  set σ := sigmaBarInfinite nu (m - h) P with hσdef
  have hag := (Hag C₀ hCa cStar nu hnu hnu1 K P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 m h n hh h400 hm hnu2 hn
    hmn).2
  have hlog1 : 1 ≤ Real.log (m : ℝ) := by
    have := four_le_log_of_large (show (55 : ℝ) ≤ m by linarith only [hmR])
    linarith only [this]
  have hσ8 : (m : ℝ) ^ 3 ≤ σ ^ 8 := by
    have h1 : (m : ℝ) ^ (3 / 8 : ℝ) ≤ σ := by
      refine le_trans ?_ hag
      have : 1 ≤ Real.log (m : ℝ) ^ (3 / 2 : ℝ) := Real.one_le_rpow hlog1 (by norm_num)
      have h0 : 0 ≤ (m : ℝ) ^ (3 / 8 : ℝ) := by positivity
      nlinarith only [this, h0]
    have h2 : ((m : ℝ) ^ (3 / 8 : ℝ)) ^ 8 ≤ σ ^ 8 :=
      pow_le_pow_left₀ (by positivity) h1 8
    have h3 : ((m : ℝ) ^ (3 / 8 : ℝ)) ^ 8 = (m : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le, ← Real.rpow_natCast]; norm_num
    linarith only [h2, h3]
  -- the defect `ε`
  set ε : ℝ := C₀ * σ ^ (-(2 : ℝ)) * Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ) with hεdef
  have hlogQ0 : 0 ≤ Real.log (nu⁻¹ * (m : ℝ)) := by
    apply Real.log_nonneg
    have hinv1 : 1 ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
    nlinarith only [hinv1, hmR]
  have hε0 : 0 ≤ ε := by
    rw [hεdef]
    exact mul_nonneg (mul_nonneg (by linarith only [hC₀1]) (Real.rpow_nonneg hσ0.le _))
      (Real.rpow_nonneg hlogQ0 _)
  have hεC : ε ≤ C₀ := by
    have h1 := (Hh C₀ hCh cStar nu K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 m h n hh h400 hm hn).2
    have h2 : (m : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hm1 (by norm_num)
    have h3 : C₀ * (m : ℝ) ^ (-(3 / 4 : ℝ)) ≤ C₀ * 1 :=
      mul_le_mul_of_nonneg_left h2 (by linarith only [hC₀1])
    linarith only [h1, h3]
  -- the slope, `P̂` and the length
  set X : TriadicCube d → ShellSeq d → BlockVec d := fun Q ω =>
    blockSlope nu (m - h) P Q e e' (wD ω).toH1Function.grad
      (fun y => (wN ω).toH1Function.grad y + hshellFlux nu P m h ω e' y) with hX
  set Lq : TriadicCube d → ShellSeq d → ℝ := fun Q ω =>
    blockLenSq (ahomSqrtApply nu (m - h) P (principalPhat m h Q ω (X Q ω))) with hLq
  change subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal
        (blockVecDot (X Q ω) (blockMatVecMul (localizationCoarseAt nu m Q ω) (X Q ω)))
        ∂P.toMeasure) ≤
      ENNReal.ofReal (1 + max C₀ K1 * σ ^ (-(2 : ℝ)) * Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ)) *
        subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (Lq Q ω) ∂P.toMeasure) +
      ENNReal.ofReal (max C₀ K1 * (m : ℝ) ^ (-(10 : ℝ)))
  have hdesc : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      Q.scale = n ∧ openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ)) := by
    intro Q hQ
    have hnm : (n : ℤ) ≤ (Kc : ℤ) := by exact_mod_cast hnK
    exact ⟨Homogenization.Book.Ch04.scale_eq_of_mem_descendantsAtScale_originCube hnm hQ,
      openCubeSet_subset_of_mem_descendantsAtScale (k := (n : ℤ)) hnm hQ⟩
  have hPfresh : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), ∀ α : BlockCoord d,
      Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
        (fun ω => toFullBlockVec (principalPhat m h Q ω (X Q ω)) α) :=
    fun Q hQ α => pa_phat_coord_fresh nu P m h Kc e e' e e' wD wN hwD hwN Q (hdesc Q hQ).2 α
  have hPamb : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), ∀ α : BlockCoord d,
      Measurable (fun ω => toFullBlockVec (principalPhat m h Q ω (X Q ω)) α) :=
    fun Q hQ α => (hPfresh Q hQ α).mono (shellSigma_le_ambient _) le_rfl
  have hLm : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), Measurable (Lq Q) :=
    fun Q hQ => pa_lenSq_measurable nu (m - h) P hσ0 (hPamb Q hQ)
  -- the eighth-moment input and the moment of `P̂`
  have hU1 : 1 ≤ Cu * (1 + σ⁻¹ * (h : ℝ) ^ ((1 : ℝ) / 2)) := by
    have : 0 ≤ σ⁻¹ * (h : ℝ) ^ ((1 : ℝ) / 2) := by positivity
    nlinarith only [hCu, this]
  have hUz := Hu nu hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 m h Kc n hh h400 h100 hnK e e' he he'
    wD wN hwD hwN
  have hPM := principal_Phat_moment P m h hnK hσ0 e e'
    (fun ω => (wD ω).toH1Function.grad)
    (fun ω y => (wN ω).toH1Function.grad y + hshellFlux nu P m h ω e' y) hU1 hUz
  have hB : subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (Lq Q ω ^ 2) ∂P.toMeasure) ≤
      ENNReal.ofReal ((2 * (Cu * (1 + σ⁻¹ * (h : ℝ) ^ ((1 : ℝ) / 2))) ^ 2) ^ 4) :=
    pa_le_of_rpow_quarter (by positivity) hPM
  -- the moment of `D'`
  have hDz := Hdz nu hnu hnu1 P hPrefix hJ3 m h n Kc hh h400 (by exact_mod_cast hmR) hinvm hn
  have hF : subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (dzPrime nu n m h Q ω ^ 4)
      ∂P.toMeasure) ≤ ENNReal.ofReal ((C4 * (m : ℝ) ^ (-(100 : ℝ))) ^ 4) := by
    have hint : ∀ Q : TriadicCube d,
        Integrable (fun ω => dzPrime nu n m h Q ω ^ 4) P.toMeasure :=
      fun Q => pa_dzp_pow4_integrable hnu hPrefix hJ3 hh hhm n Q
    have hcongr : ∀ Q : TriadicCube d, ∫⁻ ω, ENNReal.ofReal (dzPrime nu n m h Q ω ^ 4)
        ∂P.toMeasure = ENNReal.ofReal (∫ ω, dzPrime nu n m h Q ω ^ 4 ∂P.toMeasure) := fun Q =>
      (ofReal_integral_eq_lintegral_ofReal (hint Q) (Filter.Eventually.of_forall fun ω =>
        pow_nonneg (dzPrime_nonneg hnu n m h Q ω) 4)).symm
    simp only [hcongr]
    rw [pa_subcubeAvg_ofReal hnK (fun Q => integral_nonneg fun ω =>
      pow_nonneg (dzPrime_nonneg hnu n m h Q ω) 4)]
    refine ENNReal.ofReal_le_ofReal ?_
    set a : ℝ := ((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ)⁻¹ *
      ∑ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
        ∫ ω, dzPrime nu n m h Q ω ^ 4 ∂P.toMeasure with ha
    have ha0 : 0 ≤ a := by
      rw [ha]
      exact mul_nonneg (inv_nonneg.mpr (pa_card_pos hnK).le) (Finset.sum_nonneg fun Q _ =>
        integral_nonneg fun ω => pow_nonneg (dzPrime_nonneg hnu n m h Q ω) 4)
    have := pow_le_pow_left₀ (Real.rpow_nonneg ha0 _) hDz 4
    rwa [← Real.rpow_natCast, ← Real.rpow_mul ha0, show (1 : ℝ) / 4 * ((4 : ℕ) : ℝ) = 1 by norm_num,
      Real.rpow_one] at this
  have hq : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      ∫⁻ ω, ENNReal.ofReal (blockVecDot (X Q ω)
          (blockMatVecMul (localizationCoarseAt nu m Q ω) (X Q ω))) ∂P.toMeasure ≤
        ENNReal.ofReal (1 + ε) * ∫⁻ ω, ENNReal.ofReal
          ((1 + dzPrime nu n m h Q ω) * Lq Q ω) ∂P.toMeasure := by
    intro Q hQ
    obtain ⟨hQs, -⟩ := hdesc Q hQ
    refine pa_cube_bound hnu m h hPrefix hJ2 hJ3 hJ4 Q hε0 (measurable_dzPrime_fresh nu n m h Q)
      (fun ω => principalDz_le_dzPrime hnu hnmh Q hQs ω) (hPfresh Q hQ) ?_ ?_
    · intro α β
      exact pa_hint_integrable (Lf := Lq Q) (Phat := fun ω => principalPhat m h Q ω (X Q ω))
        (c := σ + σ⁻¹) (add_nonneg hσ0.le (inv_nonneg.2 hσ0.le)) (measurable_dzPrime nu n m h Q)
        (fun ω => dzPrime_nonneg hnu n m h Q ω) (hPamb Q hQ)
        (fun ω => pa_norm_le_lenSq nu (m - h) P hσ0 _)
        (pa_dzp_pow4_integrable hnu hPrefix hJ3 hh hhm n Q)
        (pa_subcubeAvg_ne_top_of_le hnK hB hQ) α β
    · intro Y
      exact Hfv C₀ hC1' cStar nu K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 m h n hh h400 hm hn Q hQs Y
  have hchain := pa_avg_chain (a := fun Q ω => blockVecDot (X Q ω)
      (blockMatVecMul (localizationCoarseAt nu m Q ω) (X Q ω)))
    (D := fun Q ω => dzPrime nu n m h Q ω) (L := Lq) (μ := P.toMeasure) hnK hε0
    (M := (m : ℝ) ^ 100) (by positivity) (F := (C4 * (m : ℝ) ^ (-(100 : ℝ))) ^ 4)
    (B := (2 * (Cu * (1 + σ⁻¹ * (h : ℝ) ^ ((1 : ℝ) / 2))) ^ 2) ^ 4)
    (by positivity) (by positivity) (fun Q _ => measurable_dzPrime nu n m h Q) hLm
    (fun Q ω => dzPrime_nonneg hnu n m h Q ω) (fun Q ω => pa_blockLenSq_nonneg _) hq hF hB
  have hfin := pa_final_real (m := (m : ℝ)) (σ := σ) (h := (h : ℝ)) (Cu := Cu) (C4 := C4)
    (ε := ε) (C0 := C₀) hmR (by exact_mod_cast hhm) (Nat.cast_nonneg h) hσ0 hσ8
    (by linarith only [hC4]) hε0 hεC
  refine hchain.trans (add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    (ENNReal.ofReal_le_ofReal ?_))
  · have hmax : C₀ ≤ max C₀ K1 := le_max_left _ _
    have h0 : 0 ≤ σ ^ (-(2 : ℝ)) := Real.rpow_nonneg hσ0.le _
    have h1 : 0 ≤ Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ) := Real.rpow_nonneg hlogQ0 _
    have : C₀ * σ ^ (-(2 : ℝ)) * Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ) ≤
        max C₀ K1 * σ ^ (-(2 : ℝ)) * Real.log (nu⁻¹ * (m : ℝ)) ^ (2 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmax h0) h1
    rw [hεdef]
    linarith only [this]
  · refine le_trans hfin ?_
    rw [hK1]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hm0.le _)

/-! ## Satisfiability -/

/-- The non-law hypotheses of `principal_term` are met: for every law `P`, every pair of directions
and every constants there are scales `m, h, Kc, n` with the scale hypotheses, and Dirichlet and
Neumann responses of the fresh-shell flux. (The law bundle itself is the standing assumption; the
Dirac law does not satisfy `ShellLawJ5`.) -/
example (C cStar K nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (P : ProbabilityMeasure (ShellSeq 2))
    (e e' : Vec 2) :
    ∃ m h Kc n : ℕ, 1 ≤ h ∧ 400 * h ≤ m ∧ 100 * m ≤ Kc ∧
      2 * lNaught C C (3 / 4) cStar nu K ≤ (m : ℝ) ∧
      n = ⌊(m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3)⌋₊ ∧
      ∃ (wD : ShellSeq 2 → H10Function (openCubeSet (originCube 2 (Kc : ℤ))))
        (wN : ShellSeq 2 → H1MeanZeroFunction (openCubeSet (originCube 2 (Kc : ℤ)))),
        (∀ omega, IsCubeDirichletResponse (originCube 2 (Kc : ℤ))
          (hshellFlux nu P m h omega e) (wD omega)) ∧
        (∀ omega, IsCubeNeumannResponse (originCube 2 (Kc : ℤ))
          (hshellFlux nu P m h omega e') (wN omega)) := by
  obtain ⟨m, h, n, h1, h2, h3, -, h5, -⟩ :=
    eLVsLnaughtAgain_scale_witness C cStar K nu hnu hnu1
  obtain ⟨wD, -, hD, -, -⟩ := exists_response_data (d := 2) le_rfl nu P m h (100 * m) e
  obtain ⟨-, wN, -, hN, -⟩ := exists_response_data (d := 2) le_rfl nu P m h (100 * m) e'
  exact ⟨m, h, 100 * m, n, h1, h2, le_rfl, h3, h5, wD, wN, hD, hN⟩

end SuperdiffusionCLT.Section5
