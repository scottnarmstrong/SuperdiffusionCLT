/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Neumann.NeumannInputB

/-!
# The Neumann input: the annealed bound at one cube size

`lintegral_subcubeAvg_neumann_le`: the annealed subcube average of the Neumann block norm is at
most `1 + y`, whenever the annealed energy `E ‖grad w_N‖²_{L̲²(cu_Kc)}` is finite and at most `y`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)

variable {d : ℕ}

theorem sum_lintegral_le_lintegral_sum {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Finset ι) (f : ι → α → ENNReal) :
    ∑ i ∈ S, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ S, f i a ∂μ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    simp only [Finset.sum_insert hi]
    exact (add_le_add_right ih _).trans (le_lintegral_add _ _)

/-- Interchange of the subcube average and the annealed integral, in the direction `≤`. -/
theorem subcubeAvg_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {Kc n : ℕ} (hn : n ≤ Kc)
    (f : TriadicCube d → α → ENNReal) :
    subcubeAvg Kc n (fun Q => ∫⁻ a, f Q a ∂μ) ≤ ∫⁻ a, subcubeAvg Kc n (fun Q => f Q a) ∂μ := by
  have hc : ((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ENNReal)⁻¹ ≠ ⊤ := by
    refine ENNReal.inv_ne_top.2 ?_
    have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
      show (n : ℤ) ≤ (Kc : ℤ)
      exact_mod_cast hn
    have hne := descendantsAtScale_nonempty (originCube d (Kc : ℤ)) hk
    exact Nat.cast_ne_zero.2 (Finset.card_pos.2 hne).ne'
  unfold subcubeAvg
  rw [lintegral_const_mul' _ _ hc]
  exact mul_le_mul' le_rfl (sum_lintegral_le_lintegral_sum μ _ _)

theorem vecCubeLpENorm_two_ne_top {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm Q 2 F ≠ ⊤ :=
  (SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2 hF).eLpNorm_lt_top.ne

theorem ofReal_one_add_vecSqAvg {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    ENNReal.ofReal (1 + SuperdiffusionCLT.Section2.Estimates.Stream.vecSqAvg Q F) =
      1 + SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm Q 2 F ^ (2 : ℕ) := by
  have hsq := SuperdiffusionCLT.Section2.Estimates.Stream.toReal_vecCubeLpENorm_two_sq_memLp
    Q (SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2 hF)
  have hfin := vecCubeLpENorm_two_ne_top hF
  rw [← hsq, ENNReal.ofReal_add zero_le_one (sq_nonneg _), ENNReal.ofReal_one,
    ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin]

/-- The annealed bound at one cube size. -/
theorem lintegral_subcubeAvg_neumann_le [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) (hs : 0 < sigmaBarInfinite nu (m - h) P) {Kc n : ℕ} (hn : n ≤ Kc) (e' : Vec d)
    (he : vecNormSq e' = 1)
    (g : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Vec d → Vec d)
    (hg : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) (g omega)) {y : ℝ}
    (hfin : ∫⁻ omega, SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
        (originCube d (Kc : ℤ)) 2 (g omega) ^ (2 : ℕ) ∂P.toMeasure ≠ ⊤)
    (hy : (∫⁻ omega, SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
        (originCube d (Kc : ℤ)) 2 (g omega) ^ (2 : ℕ) ∂P.toMeasure).toReal ≤ y) :
    subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
        (blockVecDot
          (ahomSqrtApply nu (m - h) P
            (blockMatVecMul (gaugeMat (-principalGauge m h Q omega))
              (ahomInvSqrtApply nu (m - h) P
                (e', volumeAverageVec (cubeSet Q)
                  (fun y => g omega y + hshellFlux nu P m h omega e' y)))))
          (ahomSqrtApply nu (m - h) P
            (blockMatVecMul (gaugeMat (-principalGauge m h Q omega))
              (ahomInvSqrtApply nu (m - h) P
                (e', volumeAverageVec (cubeSet Q)
                  (fun y => g omega y + hshellFlux nu P m h omega e' y)))))) ∂P.toMeasure) ≤
      ENNReal.ofReal (1 + y) := by
  calc _ ≤ ∫⁻ omega, subcubeAvg Kc n (fun Q => ENNReal.ofReal
        (blockVecDot
          (ahomSqrtApply nu (m - h) P
            (blockMatVecMul (gaugeMat (-principalGauge m h Q omega))
              (ahomInvSqrtApply nu (m - h) P
                (e', volumeAverageVec (cubeSet Q)
                  (fun y => g omega y + hshellFlux nu P m h omega e' y)))))
          (ahomSqrtApply nu (m - h) P
            (blockMatVecMul (gaugeMat (-principalGauge m h Q omega))
              (ahomInvSqrtApply nu (m - h) P
                (e', volumeAverageVec (cubeSet Q)
                  (fun y => g omega y + hshellFlux nu P m h omega e' y))))))) ∂P.toMeasure :=
        subcubeAvg_lintegral_le _ hn _
    _ ≤ ∫⁻ omega, (1 + SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
        (originCube d (Kc : ℤ)) 2 (g omega) ^ (2 : ℕ)) ∂P.toMeasure :=
        lintegral_mono fun omega => by
          rw [← ofReal_one_add_vecSqAvg (hg omega)]
          exact subcubeAvg_neumannBlock_le nu P m h hs hn omega e' he (hg omega)
    _ = 1 + ∫⁻ omega, SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
        (originCube d (Kc : ℤ)) 2 (g omega) ^ (2 : ℕ) ∂P.toMeasure := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (1 + y) := by
        rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg]
        exact ENNReal.ofReal_le_ofReal (by linarith only [hy])

end SuperdiffusionCLT.Section5
