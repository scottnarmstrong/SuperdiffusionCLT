/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.PrimeC

/-!
# Package C6, part 4: node 7 in expectation (route W, general form)

`akhcPrime_expected_energy_le`: the expected route-W weak-norm energy at scale `m`, normalized by
the source's `M₀ = diag(σ̂_m, σ̂_m⁻¹)`, is bounded by

`16 (E[avgDom] + C² κ S_w (Σ w_n τ_{m,n} + (ε/2) S_w E[G] + (θ/ε) E[flSum])
      + C² u² κ B_J · 2(1 + E[G]) + C² constTail)`,

where `M⁺` (normalized by `E = Ahom(cu_h)`) enters only through an integrable dominator `G` of
its square (package C3), and every other expectation is an explicit expectation of normalized
fluctuations or a `τ`-defect.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Response

noncomputable section

/-- Linearity of the integral for the dominating combination. -/
theorem akhcPrime_integral_combo {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f1 f2 f3 f4 : Ω → ℝ} (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
    (h3 : Integrable f3 μ) (h4 : Integrable f4 μ) (c1 c2 c3 a b B : ℝ) :
    ∫ ω, 16 * (f1 ω + c1 * (f2 ω + a * f4 ω + b * f3 ω) + c2 * (B * (2 * (1 + f4 ω))) + c3) ∂μ =
      16 * ((∫ ω, f1 ω ∂μ) + c1 * ((∫ ω, f2 ω ∂μ) + a * (∫ ω, f4 ω ∂μ) + b * ∫ ω, f3 ω ∂μ) +
        c2 * (B * (2 * (1 + ∫ ω, f4 ω ∂μ))) + c3) := by
  have hfun : (fun ω => 16 * (f1 ω + c1 * (f2 ω + a * f4 ω + b * f3 ω) +
      c2 * (B * (2 * (1 + f4 ω))) + c3)) =
      fun ω => ((16 * f1 ω + (16 * c1) * f2 ω) + ((16 * c1 * a + 32 * c2 * B) * f4 ω +
        (16 * c1 * b) * f3 ω)) + (32 * c2 * B + 16 * c3) := by
    funext ω; ring
  rw [hfun, integral_add, integral_add, integral_add, integral_add, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
  · simp only [probReal_univ, one_smul]
    ring
  · exact h4.const_mul _
  · exact h3.const_mul _
  · exact h1.const_mul _
  · exact h2.const_mul _
  · exact (h1.const_mul _).add (h2.const_mul _)
  · exact (h4.const_mul _).add (h3.const_mul _)
  · exact ((h1.const_mul _).add (h2.const_mul _)).add ((h4.const_mul _).add (h3.const_mul _))
  · exact integrable_const _

/-- **Node 7, route W, general expectation form.** For `k < m`, the reference
`E = Ahom(cu_h)` (positive definite) and an integrable dominator `G` of `(M⁺_{m,ρ}(E))²`
whose index sets are bounded (package C3's conclusion), the expected energy
`E[σ̂_m G² + σ̂_m⁻¹ F²]` is bounded by the explicit combination below. -/
theorem akhcPrime_expected_energy_le {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {k m h : ℕ} (hkm : k < m) {β s' ρ ε : ℝ} (hβ : β ≤ 1 / 2) (hlo : 1 / 4 ≤ s')
    (hhi : s' < 1 / 2) (hgap : ρ / 2 < s') (hε : 0 < ε) (e : Vec d) (he : vecNormSq e = 1)
    (hb : 0 < sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (hc : 0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))))
    (hE : (toFullBlockMat (annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ))))).PosDef)
    (G : ShellSeq d → ℝ) (hGint : Integrable G P.toMeasure)
    (hMG : ∀ omega, SuperdiffusionCLT.AKHC61.Tails.akhcMM_Mplus nu L P m h ρ omega ^ 2 ≤
      G omega)
    (hBdd : ∀ omega : ShellSeq d, BddAbove {M : ℝ | ∃ Q : TriadicCube d,
      Q.scale ≤ ((m : ℕ) : ℤ) ∧ cubeCenter Q ∈ cubeSet (originCube d ((m : ℕ) : ℤ)) ∧
      M = Real.rpow (3 : ℝ) (-ρ * ((((m : ℕ) : ℤ) : ℝ) - (Q.scale : ℝ))) *
        SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess
          (annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ))))
          (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField)})
    (hIntA : Integrable (akhcPrime_avgDom nu L P β m k) (cutoffLaw (d := d) nu L P))
    (hIntD : Integrable (akhcPrime_defSum (1 / 2) s' (m : ℤ) (k : ℤ)
      (akhcSpecialPAtScale nu L P (m : ℤ) e) (akhcSpecialQAtScale nu L P (m : ℤ) e))
      (cutoffLaw (d := d) nu L P))
    (hIntF : Integrable (akhcPrime_flSum nu L P s' m k) (cutoffLaw (d := d) nu L P))
    (hIntEn : Integrable (akhcPrime_energy nu L P m e) (cutoffLaw (d := d) nu L P)) :
    ∫ a, akhcPrime_energy nu L P m e a ∂(cutoffLaw (d := d) nu L P) ≤
      16 * ((∫ a, akhcPrime_avgDom nu L P β m k a ∂(cutoffLaw (d := d) nu L P)) +
        Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
            (akhcSigmaHatAtScale nu L P (m : ℤ) *
                (akhcWeakC2_maximizerConst s' ρ *
                  Book.Ch02.matrixNorm
                    (annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ)))).lowerRight) +
              (akhcSigmaHatAtScale nu L P (m : ℤ))⁻¹ *
                (akhcWeakC2_maximizerConst s' ρ *
                  Book.Ch02.matrixNorm
                    (annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ)))).upperLeft)) *
            akhcPrime_wSum (1 / 2) s' (m : ℤ) (k : ℤ) *
          ((∫ a, akhcPrime_defSum (1 / 2) s' (m : ℤ) (k : ℤ)
              (akhcSpecialPAtScale nu L P (m : ℤ) e) (akhcSpecialQAtScale nu L P (m : ℤ) e) a
              ∂(cutoffLaw (d := d) nu L P)) +
            ε / 2 * akhcPrime_wSum (1 / 2) s' (m : ℤ) (k : ℤ) * (∫ omega, G omega ∂P.toMeasure) +
            SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m / ε *
              ∫ a, akhcPrime_flSum nu L P s' m k a ∂(cutoffLaw (d := d) nu L P)) +
        Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
            akhcPrime_u (1 / 2) s' (m : ℤ) (k : ℤ) ^ 2 *
            (akhcSigmaHatAtScale nu L P (m : ℤ) *
                (akhcWeakC2_maximizerConst s' ρ *
                  Book.Ch02.matrixNorm
                    (annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ)))).lowerRight) +
              (akhcSigmaHatAtScale nu L P (m : ℤ))⁻¹ *
                (akhcWeakC2_maximizerConst s' ρ *
                  Book.Ch02.matrixNorm
                    (annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ)))).upperLeft)) *
          (akhcWNSq_Bj (annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ))))
              (akhcSpecialPAtScale nu L P (m : ℤ) e) (akhcSpecialQAtScale nu L P (m : ℤ) e) *
            (2 * (1 + ∫ omega, G omega ∂P.toMeasure))) +
        Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
          akhcPrime_constTail nu L P m k e) := by
  set E := annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ))) with hEdef
  set C := Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d
  set σ := akhcSigmaHatAtScale nu L P (m : ℤ)
  set Kl := akhcWeakC2_maximizerConst s' ρ * Book.Ch02.matrixNorm E.lowerRight
  set Ku := akhcWeakC2_maximizerConst s' ρ * Book.Ch02.matrixNorm E.upperLeft
  set Sw := akhcPrime_wSum (1 / 2) s' (m : ℤ) (k : ℤ)
  set u := akhcPrime_u (1 / 2) s' (m : ℤ) (k : ℤ)
  set p := akhcSpecialPAtScale nu L P (m : ℤ) e
  set q := akhcSpecialQAtScale nu L P (m : ℤ) e
  set Bj := akhcWNSq_Bj E p q
  set θ := SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m
  have hs' : 0 < s' := by linarith only [hlo]
  have hKc : 0 ≤ akhcWeakC2_maximizerConst s' ρ := by
    unfold akhcWeakC2_maximizerConst; positivity
  have hKl : 0 ≤ Kl := mul_nonneg hKc (Book.Ch02.matrixNorm_nonneg _)
  have hKu : 0 ≤ Ku := mul_nonneg hKc (Book.Ch02.matrixNorm_nonneg _)
  have hBj : 0 ≤ Bj := akhcWNSq_Bj_nonneg hE p q
  set φ : ShellSeq d → RegCoeffField d := fun omega => coefficientCutoff nu omega L
  have hφ : AEMeasurable φ P.toMeasure :=
    (measurable_coefficientCutoff (d := d) nu L).aemeasurable
  -- the pointwise domination
  have hpt : ∀ omega : ShellSeq d, akhcPrime_energy nu L P m e (φ omega) ≤
      16 * (akhcPrime_avgDom nu L P β m k (φ omega) +
        C ^ 2 * (σ * Kl + σ⁻¹ * Ku) * Sw *
          (akhcPrime_defSum (1 / 2) s' (m : ℤ) (k : ℤ) p q (φ omega) +
            ε / 2 * Sw * G omega + θ / ε * akhcPrime_flSum nu L P s' m k (φ omega)) +
        C ^ 2 * u ^ 2 * (σ * Kl + σ⁻¹ * Ku) * (Bj * (2 * (1 + G omega))) +
        C ^ 2 * akhcPrime_constTail nu L P m k e) := by
    intro omega
    have ha := aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L
    set M := akhcWeakC_eventMoreprotoPlus ((m : ℕ) : ℤ) ρ E (φ omega).toFun with hMdef
    have hM0 : 0 ≤ M := akhcWeakD_eventMoreprotoPlus_nonneg _ _ _ _
    have hMG' : M ^ 2 ≤ G omega := hMG omega
    have hl := akhcWeakD_lambdaSqCoeffField_inv_le hE ha hs' hgap (hBdd omega)
    have hL := akhcWeakD_LambdaSqCoeffField_le hE ha hs' hgap (hBdd omega)
    have hloew := akhcWeakD_blockMatLoewnerLE_of_mem hE (hBdd omega)
      (R := originCube d ((m : ℕ) : ℤ)) le_rfl
      (by
        have hopen : cubeCenter (originCube d ((m : ℕ) : ℤ)) ∈
            openCubeSet (originCube d ((m : ℕ) : ℤ)) := by
          rw [← ball_cubeCenter_eq_openCubeSet]
          exact Metric.mem_ball_self (cubeRadius_pos _)
        exact openCubeSet_subset_cubeSet _ hopen)
    have hw1 : Real.rpow (3 : ℝ) (ρ * ((((m : ℕ) : ℤ) : ℝ) -
        ((originCube d ((m : ℕ) : ℤ)).scale : ℝ))) = 1 := by
      rw [show (originCube d ((m : ℕ) : ℤ)).scale = ((m : ℕ) : ℤ) from rfl, sub_self, mul_zero]
      exact Real.rpow_zero 3
    rw [hw1, one_mul] at hloew
    have hJ := akhcWNSq_responseJ_le (φ omega) ha (originCube d ((m : ℕ) : ℤ)) p q hM0 hloew
    have h := akhcPrime_energy_le hnu L hJ4 (φ omega) ha hkm hβ hlo hhi e hb hc he hKl hKu hBj
      hM0 hMG' hε hl hL hJ
    rw [akhcPrime_misSum_eq] at h
    calc akhcPrime_energy nu L P m e (φ omega) ≤ _ := h
      _ = _ := by ring
  -- transfer to the underlying law
  have hmapI : ∀ f : RegCoeffField d → ℝ, Integrable f (cutoffLaw (d := d) nu L P) →
      Integrable (fun omega => f (φ omega)) P.toMeasure := fun f hf =>
    (integrable_map_measure hf.aestronglyMeasurable hφ).mp hf
  have hmapE : ∀ f : RegCoeffField d → ℝ, Integrable f (cutoffLaw (d := d) nu L P) →
      ∫ a, f a ∂(cutoffLaw (d := d) nu L P) = ∫ omega, f (φ omega) ∂P.toMeasure := fun f hf =>
    integral_map hφ hf.aestronglyMeasurable
  have hY := akhcPrime_integral_combo (μ := P.toMeasure) (hmapI _ hIntA) (hmapI _ hIntD)
    (hmapI _ hIntF) hGint (C ^ 2 * (σ * Kl + σ⁻¹ * Ku) * Sw) (C ^ 2 * u ^ 2 * (σ * Kl + σ⁻¹ * Ku))
    (C ^ 2 * akhcPrime_constTail nu L P m k e) (ε / 2 * Sw) (θ / ε) Bj
  have hYint : Integrable (fun omega => 16 * (akhcPrime_avgDom nu L P β m k (φ omega) +
        C ^ 2 * (σ * Kl + σ⁻¹ * Ku) * Sw *
          (akhcPrime_defSum (1 / 2) s' (m : ℤ) (k : ℤ) p q (φ omega) +
            ε / 2 * Sw * G omega + θ / ε * akhcPrime_flSum nu L P s' m k (φ omega)) +
        C ^ 2 * u ^ 2 * (σ * Kl + σ⁻¹ * Ku) * (Bj * (2 * (1 + G omega))) +
        C ^ 2 * akhcPrime_constTail nu L P m k e)) P.toMeasure := by
    refine Integrable.const_mul ?_ _
    refine ((((hmapI _ hIntA).add ?_).add ?_).add (integrable_const _))
    · refine Integrable.const_mul ?_ _
      exact (((hmapI _ hIntD).add (hGint.const_mul _)).add ((hmapI _ hIntF).const_mul _))
    · refine Integrable.const_mul ?_ _
      have hfun : (fun omega => Bj * (2 * (1 + G omega))) =
          fun omega => Bj * 2 * G omega + Bj * 2 := by
        funext omega; ring
      rw [hfun]
      exact (hGint.const_mul _).add (integrable_const _)
  rw [hmapE _ hIntEn, hmapE _ hIntA, hmapE _ hIntD, hmapE _ hIntF]
  calc ∫ omega, akhcPrime_energy nu L P m e (φ omega) ∂P.toMeasure
      ≤ ∫ omega, 16 * (akhcPrime_avgDom nu L P β m k (φ omega) +
        C ^ 2 * (σ * Kl + σ⁻¹ * Ku) * Sw *
          (akhcPrime_defSum (1 / 2) s' (m : ℤ) (k : ℤ) p q (φ omega) +
            ε / 2 * Sw * G omega + θ / ε * akhcPrime_flSum nu L P s' m k (φ omega)) +
        C ^ 2 * u ^ 2 * (σ * Kl + σ⁻¹ * Ku) * (Bj * (2 * (1 + G omega))) +
        C ^ 2 * akhcPrime_constTail nu L P m k e) ∂P.toMeasure :=
        integral_mono (hmapI _ hIntEn) hYint hpt
    _ = _ := hY

end

end SuperdiffusionCLT.AKHC61.WeakNorms
