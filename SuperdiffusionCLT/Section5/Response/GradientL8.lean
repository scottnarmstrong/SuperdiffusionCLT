/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Carriers.BlockOffset
public import SuperdiffusionCLT.Section5.Response.ResponseData
public import SuperdiffusionCLT.Section5.Response.GammaMoments
public import SuperdiffusionCLT.Frozen.Section3.ResponseFieldsAprioriOrderOne
public import SuperdiffusionCLT.Frozen.Section2.StreamIncrementScaleEstimates
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.Norms.CubeCarrierIdents
public import SuperdiffusionCLT.Section2.Cutoff.StreamCutoffAPI
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOne
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputsB

/-!
# The gradient `L⁸` clause of `lem.response`

display `e.response.grad.l8`: for the
Dirichlet and Neumann responses of the flux `shom_{m-h}^{-1} hshell e` on the cube `cu_K`,

`E[‖∇w_D‖_{L̲⁸}⁸ + ‖∇w_N‖_{L̲⁸}⁸]^{1/8} ≤ C shom_{m-h}^{-1} h^{1/2}`.

The proof applies the a priori clause `e.abstract.response.L8` of
`Frozen.Section3.responseFields_apriori_orderOne` to each sample, bounds the flux in `L̲⁸(cu_K)` by the
`L^p` clause of `Frozen.Section2.streamIncrement_scale_estimates` at `p = 8` with
`n = m - h`, and takes the `L⁸(P)` norm through the `O_{Γ₂}` moment bound.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- The flux `L̲^q` norm on a cube is at most `shom_{m-h}^{-1}` times the `L̲^q` norm of the
increment `k_m - k_{m-h}`, for `|e| ≤ 1`. -/
theorem vecCubeLpENorm_hshellFlux_le [NeZero d] (nu : ℝ)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    {e : Vec d} (he : vecNormSq e ≤ 1) (Q : TriadicCube d) (q : ℝ≥0∞) :
    SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm Q q
        (hshellFlux nu P m h omega e) ≤
      ‖(sigmaBarInfinite nu (m - h) P)⁻¹‖ₑ *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q q
          (fun x => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x) := by
  have hdelta : ∀ x, SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x =
      SuperdiffusionCLT.Frozen.Section2.streamCutoff omega m x -
        SuperdiffusionCLT.Frozen.Section2.streamCutoff omega (m - h) x :=
    fun x => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_apply_eq_streamCutoff_sub
      omega (Nat.sub_le m h) x
  have hcont : Continuous (fun x : Vec d =>
      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x) := by
    have hfun : (fun x : Vec d =>
        SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x) =
        fun x => ∑ k ∈ Finset.Ioc (m - h) m, (omega k) x := by
      funext x
      rw [SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_apply]
      rfl
    rw [hfun]
    exact continuous_finsetSum _ fun k _ => (omega k).1.1.continuous
  have hform : hshellFlux nu P m h omega e = fun x =>
      (sigmaBarInfinite nu (m - h) P)⁻¹ •
        matVecMul (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x) e := by
    funext x
    rw [hshellFlux, hdelta]
  rw [hform, SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm_const_smul]
  gcongr
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (hilbertifyVecField (fun x =>
        matVecMul (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x) e))
      (normalizedCubeMeasure Q) := by
    refine (SuperdiffusionCLT.Section2.Estimates.Stream.continuous_hilbertifyVecField ?_).aestronglyMeasurable
    exact continuous_pi fun i => by
      simp only [matVecMul]
      exact continuous_finsetSum _ fun j _ =>
        ((continuous_apply j).comp ((continuous_apply i).comp hcont)).mul continuous_const
  refine SuperdiffusionCLT.Section2.Norms.cubeLpENorm_mono_enorm hmeas (fun x => ?_)
  rw [SuperdiffusionCLT.Section3.ResponseFields.norm_hilbertifyVecField_apply,
    SuperdiffusionCLT.Section2.Norms.norm_eq_matrixOperatorNorm]
  refine (Homogenization.Book.Ch02.vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm _ e).trans ?_
  have : Homogenization.Book.Ch02.vecNorm e ≤ 1 := by
    have hsq := Homogenization.Book.Ch02.vecNorm_sq_eq_vecNormSq e
    exact (pow_le_one_iff_of_nonneg (Homogenization.Book.Ch02.vecNorm_nonneg e)
      two_ne_zero).1 (hsq ▸ he)
  exact mul_le_of_le_one_right (Homogenization.Book.Ch02.matrixOperatorNorm_nonneg _) this

/-- **The gradient `L⁸` clause of `lem.response`** (`e.response.grad.l8`): for the Dirichlet and
Neumann responses `w_D, w_N` of the flux `shom_{m-h}^{-1} (k_m - k_{m-h}) e` on `cu_K`,
`E[‖∇w_D‖_{L̲⁸}⁸ + ‖∇w_N‖_{L̲⁸}⁸]^{1/8} ≤ C shom_{m-h}^{-1} h^{1/2}`. -/
theorem response_gradient_L8 (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ m h Kc : ℕ, 1 ≤ h → 400 * h ≤ m → 100 * m ≤ Kc →
          ∀ e : Vec d, vecNormSq e ≤ 1 →
          ∀ (wD : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                H10Function (openCubeSet (originCube d (Kc : ℤ))))
            (wN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
            (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
              (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD omega)) →
            (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
              (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wN omega)) →
          ((∫⁻ omega, (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                  (originCube d (Kc : ℤ)) 8 (wD omega).toH1Function.grad) ^ (8 : ℕ) +
                (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                  (originCube d (Kc : ℤ)) 8 (wN omega).toH1Function.grad) ^ (8 : ℕ)
                ∂P.toMeasure) ^ ((1 : ℝ) / 8) ≤
            ENNReal.ofReal (C * (sigmaBarInfinite nu (m - h) P)⁻¹ * (h : ℝ) ^ ((1 : ℝ) / 2)))
  := by
  obtain ⟨Cap, hCapTop, hAp⟩ :=
    SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderOne d hd
  obtain ⟨C₂, hV⟩ := SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates d
  obtain ⟨C₀, C₁, hV2⟩ := hV (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨Cv, hV3⟩ := hV2 8 (by norm_num)
  refine ⟨max 1 (Cap.toReal * (7 * |Cv| + 6)), le_max_left _ _, ?_⟩
  intro nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 e he wD wN hwD hwN
  have hσ : 0 < sigmaBarInfinite nu (m - h) P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu (m - h) hPre hJ2 hJ3 hJ4
  have hV4 := hV3 P hPre hJ1 hJ2 hJ3 hJ4
  have hnm : m - h < m := by omega
  have hmK : m ≤ Kc := by omega
  obtain ⟨X, hXm, hXO, hXle⟩ := (hV4.1 Kc m (m - h) hnm hmK).2.1
  have hhm : m - (m - h) = h := by omega
  rw [hhm] at hXO hXle
  have h8 : ENNReal.ofReal 8 = 8 := by simp
  rw [h8] at hXle
  have hhpos : (0 : ℝ) < (h : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hh) _
  have hA : 0 < (|Cv| + 1) * 3 * (h : ℝ) ^ ((1 : ℝ) / 2) := by positivity
  have hs8 : (8 : ℝ) ^ ((1 : ℝ) / 2) ≤ 3 := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have ht : (3 : ℝ) ^ (-((d : ℝ) / (2 * 8) * ((Kc - m : ℕ) : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by have : 0 ≤ (d : ℝ) / (2 * 8) * ((Kc - m : ℕ) : ℝ) := by positivity
          linarith only [this])
  have hXO' : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2) X
      ((|Cv| + 1) * 3 * (h : ℝ) ^ ((1 : ℝ) / 2)) := by
    refine hXO.mono_scale ?_
    have h8nn : 0 ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have htnn : 0 ≤ (3 : ℝ) ^ (-((d : ℝ) / (2 * 8) * ((Kc - m : ℕ) : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    calc Cv * (8 : ℝ) ^ ((1 : ℝ) / 2) * (h : ℝ) ^ ((1 : ℝ) / 2) *
          (3 : ℝ) ^ (-((d : ℝ) / (2 * 8) * ((Kc - m : ℕ) : ℝ)))
        ≤ |Cv| * 3 * (h : ℝ) ^ ((1 : ℝ) / 2) * 1 := by
          gcongr
          · exact le_abs_self Cv
        _ ≤ (|Cv| + 1) * 3 * (h : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [mul_one]; gcongr; linarith only
  set c : ℝ := |Cv| * (h : ℝ) ^ ((1 : ℝ) / 2) with hc
  set K' : ℝ := Cap.toReal * (sigmaBarInfinite nu (m - h) P)⁻¹ with hK'
  have hcnn : 0 ≤ c := by positivity
  have hK'nn : 0 ≤ K' := mul_nonneg ENNReal.toReal_nonneg (inv_nonneg.2 hσ.le)
  have hpt : ∀ omega,
      SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (originCube d (Kc : ℤ)) 8
          (wD omega).toH1Function.grad +
        SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (originCube d (Kc : ℤ)) 8
          (wN omega).toH1Function.grad ≤
      ENNReal.ofReal (K' * (c + |X omega|)) := by
    intro omega
    have h1 := (hAp Kc (hshellFlux nu P m h omega e) (wD omega) (wN omega) (hwD omega)
      (hwN omega)).1
    have h2 := vecCubeLpENorm_hshellFlux_le nu P m h omega he (originCube d (Kc : ℤ)) 8
    have h3 := hXle omega
    have hcap : Cap = ENNReal.ofReal Cap.toReal := (ENNReal.ofReal_toReal hCapTop.ne).symm
    have hinv : ‖(sigmaBarInfinite nu (m - h) P)⁻¹‖ₑ =
        ENNReal.ofReal (sigmaBarInfinite nu (m - h) P)⁻¹ :=
      Real.enorm_eq_ofReal (inv_nonneg.2 hσ.le)
    refine h1.trans ?_
    refine (mul_le_mul_right h2 Cap).trans ?_
    rw [hinv] at *
    refine (mul_le_mul_right (mul_le_mul_right h3 _) Cap).trans ?_
    have hle : Cv * (h : ℝ) ^ ((1 : ℝ) / 2) + X omega ≤ c + |X omega| := by
      have : Cv * (h : ℝ) ^ ((1 : ℝ) / 2) ≤ c :=
        mul_le_mul_of_nonneg_right (le_abs_self Cv) hhpos.le
      linarith only [this, le_abs_self (X omega)]
    rw [hcap, ← ENNReal.ofReal_mul (inv_nonneg.2 hσ.le), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hK', ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hle hK'nn
  have hZnn : ∀ omega, 0 ≤ K' * (c + |X omega|) := fun omega =>
    mul_nonneg hK'nn (add_nonneg hcnn (abs_nonneg _))
  have hint : ∫⁻ omega, (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                  (originCube d (Kc : ℤ)) 8 (wD omega).toH1Function.grad) ^ (8 : ℕ) +
                (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                  (originCube d (Kc : ℤ)) 8 (wN omega).toH1Function.grad) ^ (8 : ℕ) ∂P.toMeasure ≤
      ∫⁻ omega, ‖K' * (c + |X omega|)‖ₑ ^ ((8 : ℝ≥0∞).toReal) ∂P.toMeasure := by
    refine lintegral_mono fun omega => ?_
    have h8r : ((8 : ℝ≥0∞).toReal) = ((8 : ℕ) : ℝ) := by norm_num
    rw [h8r, ENNReal.rpow_natCast, Real.enorm_eq_ofReal (hZnn omega)]
    exact (pow_add_pow_le bot_le bot_le (by norm_num)).trans
      (pow_le_pow_left₀ bot_le (hpt omega) 8)
  have hq : (8 : ℝ≥0∞) ≠ 0 := by norm_num
  have hqt : (8 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hZm : Measurable (fun omega => K' * (c + |X omega|)) :=
    measurable_const.mul (measurable_const.add (continuous_abs.measurable.comp hXm))
  have hnorm : (∫⁻ omega, ‖K' * (c + |X omega|)‖ₑ ^ ((8 : ℝ≥0∞).toReal) ∂P.toMeasure) ^
      (1 / (8 : ℝ≥0∞).toReal) = eLpNorm (fun omega => K' * (c + |X omega|)) 8 P.toMeasure :=
    (eLpNorm_eq_lintegral_rpow_enorm_toReal hq hqt hZm.aestronglyMeasurable).symm
  have hone : (1 : ℝ) / 8 = 1 / (8 : ℝ≥0∞).toReal := by norm_num
  rw [hone]
  refine (ENNReal.rpow_le_rpow hint (by norm_num)).trans ?_
  rw [hnorm]
  have hsm : (fun omega => K' * (c + |X omega|)) = K' • (fun omega => c + |X omega|) := rfl
  rw [hsm, eLpNorm_const_smul]
  refine (mul_le_mul_right (eLpNorm_eight_const_add_abs_le hA hcnn hXm hXO') _).trans ?_
  rw [Real.enorm_eq_ofReal hK'nn, ← ENNReal.ofReal_mul hK'nn]
  refine ENNReal.ofReal_le_ofReal ?_
  have heq : K' * (c + 2 * ((|Cv| + 1) * 3 * (h : ℝ) ^ ((1 : ℝ) / 2))) =
      (Cap.toReal * (7 * |Cv| + 6)) * (sigmaBarInfinite nu (m - h) P)⁻¹ *
        (h : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [hK', hc]; ring
  rw [heq]
  gcongr
  exact le_max_right _ _

/-- **Satisfiability witness.** The non-law hypotheses of the clause are met together: the scale
conditions at `(m, h, K) = (400, 1, 40000)`, a direction `e` with `|e|² ≤ 1`, and Dirichlet and
Neumann responses of the shell flux for every sample. -/
example [NeZero d] (hd : 2 ≤ d) (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) :
    ∃ m h Kc : ℕ, 1 ≤ h ∧ 400 * h ≤ m ∧ 100 * m ≤ Kc ∧
      ∃ e : Vec d, vecNormSq e ≤ 1 ∧
        ∃ (wD : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
              H10Function (openCubeSet (originCube d (Kc : ℤ))))
          (wN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
              H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
          (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
            (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD omega)) ∧
          (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
            (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wN omega)) := by
  refine ⟨400, 1, 40000, by norm_num, by norm_num, by norm_num, 0, ?_, ?_⟩
  · simp [vecNormSq, vecDot]
  · obtain ⟨wD, wN, hD, hN, _⟩ := exists_response_data hd nu P 400 1 40000 0
    exact ⟨wD, wN, hD, hN⟩

end SuperdiffusionCLT.Section5
