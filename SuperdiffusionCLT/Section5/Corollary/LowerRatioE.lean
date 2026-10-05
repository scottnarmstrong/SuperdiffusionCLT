/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Corollary.LowerRatioD
public import SuperdiffusionCLT.Section5.Localization.CrudeSzG
public import SuperdiffusionCLT.Section5.Localization.LocalizationA

/-!
# `cor.lower.ratio`: expectation of the basic split

Subcube averages commute with the integral, and `ofReal` of a subcube mean is bounded by the
subcube average of `ofReal`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Section2.Localization
open scoped ENNReal

variable {d : ℕ}

theorem lowerRatio_ofReal_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ENNReal.ofReal_add_le).trans (add_le_add le_rfl ih)

/-- `ofReal` of a subcube mean is at most the subcube average of `ofReal`. -/
theorem lowerRatio_ofReal_subcubeMean_le {Kc n : ℕ} (f : TriadicCube d → ℝ)
    (g : TriadicCube d → ℝ≥0∞)
    (h : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), ENNReal.ofReal (f Q) ≤ g Q) :
    ENNReal.ofReal (subcubeMean (originCube d (Kc : ℤ)) (n : ℤ) f) ≤ subcubeAvg Kc n g := by
  unfold subcubeMean subcubeAvg
  set D := descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ) with hD
  by_cases h0 : D.card = 0
  · simp [h0]
  · have hpos : (0 : ℝ) < (D.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hpos.le), ENNReal.ofReal_inv_of_pos hpos,
      ENNReal.ofReal_natCast]
    refine mul_le_mul' le_rfl ((lowerRatio_ofReal_sum_le D f).trans ?_)
    exact Finset.sum_le_sum h

/-- Subcube averages commute with the integral (for measurable cell integrands). -/
theorem lowerRatio_lintegral_subcubeAvg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {Kc n : ℕ}
    (f : TriadicCube d → Ω → ℝ≥0∞)
    (hf : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), Measurable (f Q)) :
    ∫⁻ ω, subcubeAvg Kc n (fun Q => f Q ω) ∂μ = subcubeAvg Kc n (fun Q => ∫⁻ ω, f Q ω ∂μ) := by
  unfold subcubeAvg
  beta_reduce
  rw [lintegral_const_mul'' _ (Finset.measurable_sum _ fun Q hQ => hf Q hQ).aemeasurable,
    lintegral_finsetSum _ fun Q hQ => hf Q hQ]

/-- **The expectation of the basic split** at `e' = 0`, `w_N = 0`: with a measurable majorant `B`
of the cell errors, `shom_{m-h} shom_m^{-1}` is at most the principal term plus `E[B]`. -/
theorem lowerRatio_core [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m h Kc n : ℕ) (hn : n ≤ Kc)
    (Pl : MeasureTheory.ProbabilityMeasure (ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d Pl)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d Pl)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d Pl)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d Pl)
    (hσ : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) Pl)
    (e : Vec d) (he : vecNormSq e = 1)
    (wD : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
      H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (wN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
      H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))
    (hwD : ∀ ω, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
      (originCube d (Kc : ℤ)) (hshellFlux nu Pl m h ω e) (wD ω))
    (hwN : ∀ ω, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
      (originCube d (Kc : ℤ)) (hshellFlux nu Pl m h ω 0) (wN ω))
    (hN0 : ∀ ω y, (wN ω).toH1Function.grad y + hshellFlux nu Pl m h ω 0 y = 0)
    (B : TriadicCube d → ShellSeq d → ℝ≥0∞)
    (hBm : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), Measurable (B Q))
    (hB : ∀ (St : ShellSeq d → TriadicCube d → BlockState d),
      (∀ ω, ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
        IsBlockOffsetMinimizer
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu ω m).toCoeffField
          (cubeSet Q)
          (blockFluct nu (m - h) Pl Q (wD ω).toH1Function.grad
            (fun y => (wN ω).toH1Function.grad y + hshellFlux nu Pl m h ω 0 y)) (St ω Q)) →
      ∀ ω, ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
        ENNReal.ofReal |volumeAverage (cubeSet Q) (fun x =>
          blockVecDot ((2 : ℝ) • blockSlope nu (m - h) Pl Q e 0 (wD ω).toH1Function.grad
              (fun y => (wN ω).toH1Function.grad y + hshellFlux nu Pl m h ω 0 y) + (St ω Q).eval x)
            (blockMatVecMul (blockCoeffField
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu ω m).toCoeffField x)
              ((St ω Q).eval x)))| ≤ B Q ω) :
    ENNReal.ofReal (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) Pl *
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m Pl)⁻¹) ≤
      subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (blockVecDot
        (blockSlope nu (m - h) Pl Q e 0 (wD ω).toH1Function.grad
          (fun y => (wN ω).toH1Function.grad y + hshellFlux nu Pl m h ω 0 y))
        (blockMatVecMul (localizationCoarseAt nu m Q ω)
          (blockSlope nu (m - h) Pl Q e 0 (wD ω).toH1Function.grad
            (fun y => (wN ω).toH1Function.grad y + hshellFlux nu Pl m h ω 0 y))))
        ∂Pl.toMeasure) +
        subcubeAvg Kc n (fun Q => ∫⁻ ω, B Q ω ∂Pl.toMeasure) := by
  set σ := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) Pl with hσdef
  have hk' : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  obtain ⟨S, hS⟩ := loc_exists_minimizers (d := d) hnu m (fun ω Q =>
    blockSlope nu (m - h) Pl Q e 0 (wD ω).toH1Function.grad
      (fun y => (wN ω).toH1Function.grad y + hshellFlux nu Pl m h ω 0 y))
  have hex : ∀ (ω : ShellSeq d) (Q : TriadicCube d),
      ∃ X : BlockState d, Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ) →
        IsBlockOffsetMinimizer
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu ω m).toCoeffField
          (cubeSet Q)
          (blockFluct nu (m - h) Pl Q (wD ω).toH1Function.grad
            (fun y => (wN ω).toH1Function.grad y + hshellFlux nu Pl m h ω 0 y)) X := by
    intro ω Q
    by_cases hQ : Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)
    · have hsub := openCubeSet_subset_of_mem_descendantsAtScale hk' hQ
      obtain ⟨lam, Lam, hEll⟩ := exists_isEllipticFieldOn_coefficientCutoff_cubeSet hnu ω m Q
      have hFL2 := loc_isBlockL2_blockFluct nu (m - h) Pl Q
        (g1 := (wD ω).toH1Function.grad)
        (g2 := fun y => (wN ω).toH1Function.grad y + hshellFlux nu Pl m h ω 0 y)
        (SuperdiffusionCLT.Section3.Terms.memVectorL2_mono hsub (memVectorL2_grad _))
        (SuperdiffusionCLT.Section3.Terms.memVectorL2_mono hsub
          ((memVectorL2_grad (wN ω).toH1Function).add (memVectorL2_hshellFlux nu Pl ω 0 Kc)))
      obtain ⟨X, hX, -⟩ := exists_isBlockOffsetMinimizer_cubeSet Q hEll hFL2.1 hFL2.2
      exact ⟨X, fun _ => hX⟩
    · exact ⟨constBlockState 0, fun h' => absurd h' hQ⟩
  choose St hSt using hex
  have hmeasA : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      Measurable (fun ω => ENNReal.ofReal (blockVecDot
        (blockSlope nu (m - h) Pl Q e 0 (wD ω).toH1Function.grad
          (fun y => (wN ω).toH1Function.grad y + hshellFlux nu Pl m h ω 0 y))
        (blockMatVecMul (localizationCoarseAt nu m Q ω)
          (blockSlope nu (m - h) Pl Q e 0 (wD ω).toH1Function.grad
            (fun y => (wN ω).toH1Function.grad y + hshellFlux nu Pl m h ω 0 y))))) := by
    intro Q hQ
    have hsub := openCubeSet_subset_of_mem_descendantsAtScale hk' hQ
    have hm := loc_measurable_pairing_S hnu Pl m h Kc e 0 wD wN hwD hwN hsub (fun ω => S ω Q)
      (fun ω => hS ω Q)
    have heq : (fun ω => ENNReal.ofReal (blockVecDot
        (blockSlope nu (m - h) Pl Q e 0 (wD ω).toH1Function.grad
          (fun y => (wN ω).toH1Function.grad y + hshellFlux nu Pl m h ω 0 y))
        (blockMatVecMul (localizationCoarseAt nu m Q ω)
          (blockSlope nu (m - h) Pl Q e 0 (wD ω).toH1Function.grad
            (fun y => (wN ω).toH1Function.grad y + hshellFlux nu Pl m h ω 0 y))))) =
        fun ω => ENNReal.ofReal (blockPairingAverage (cubeSet Q)
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu ω m).toCoeffField
          (S ω Q) (S ω Q)) := by
      funext ω
      obtain ⟨lam, Lam, hEll⟩ := exists_isEllipticFieldOn_coefficientCutoff_cubeSet hnu ω m Q
      rw [blockPairingAverage_self_eq_coarseBlockMatrix Q hEll _ (hS ω Q)]
      rfl
    rw [heq]
    exact hm
  have hpt : ∀ ω : ShellSeq d, ENNReal.ofReal (blockVecDot ((0 : Vec d), σ ^ ((1 : ℝ) / 2) • e)
      (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ)))
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu ω m).toCoeffField)
        ((0 : Vec d), σ ^ ((1 : ℝ) / 2) • e))) ≤
      subcubeAvg Kc n (fun Q => ENNReal.ofReal (blockVecDot
        (blockSlope nu (m - h) Pl Q e 0 (wD ω).toH1Function.grad
          (fun y => (wN ω).toH1Function.grad y + hshellFlux nu Pl m h ω 0 y))
        (blockMatVecMul (localizationCoarseAt nu m Q ω)
          (blockSlope nu (m - h) Pl Q e 0 (wD ω).toH1Function.grad
            (fun y => (wN ω).toH1Function.grad y + hshellFlux nu Pl m h ω 0 y)))) + B Q ω) := by
    intro ω
    refine (ENNReal.ofReal_le_ofReal (lowerRatio_split hnu m h Kc n hn Pl e ω (wD ω)
      (fun y => (wN ω).toH1Function.grad y + hshellFlux nu Pl m h ω 0 y) (hN0 ω) (S ω) (St ω)
      (fun Q _ => hS ω Q) (fun Q hQ => hSt ω Q hQ))).trans ?_
    refine lowerRatio_ofReal_subcubeMean_le _ _ fun Q hQ => ?_
    refine ENNReal.ofReal_add_le.trans (add_le_add le_rfl ?_)
    exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
      (hB St (fun ω Q hQ => hSt ω Q hQ) ω Q hQ)
  have hv : vecNormSq (σ ^ ((1 : ℝ) / 2) • e) = σ := by
    have h1 : vecNormSq (σ ^ ((1 : ℝ) / 2) • e) =
        (σ ^ ((1 : ℝ) / 2)) ^ 2 * vecNormSq e := by
      unfold vecNormSq vecDot
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [h1, he, mul_one, ← Real.rpow_natCast, ← Real.rpow_mul hσ.le]
    norm_num
  have hbase := lowerRatio_ratio_le hnu m hPrefix hJ2 hJ3 hJ4 Kc (σ ^ ((1 : ℝ) / 2) • e)
  rw [hv] at hbase
  refine hbase.trans ((lintegral_mono hpt).trans ?_)
  refine (le_of_eq (lowerRatio_lintegral_subcubeAvg Pl.toMeasure _
    fun Q hQ => (hmeasA Q hQ).add (hBm Q hQ))).trans ?_
  refine le_trans (subcubeAvg_mono_on fun Q hQ => (lintegral_add_left (hmeasA Q hQ) _).le) ?_
  rw [subcubeAvg_add]

end SuperdiffusionCLT.Section5
