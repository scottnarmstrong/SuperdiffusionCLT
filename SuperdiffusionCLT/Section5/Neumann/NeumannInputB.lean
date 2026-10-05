/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Neumann.NeumannInput

/-!
# The Neumann input: the per-sample bound

For one sample the subcube average of `|bfAhom^{1/2} G_{-hbar_z} bfAhom^{-1/2}(e', ...)|^2`
is at most `1 + ‖grad w_N‖²_{L̲²(cu_Kc)}` (`subcubeAvg_neumannBlock_le`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)

variable {d : ℕ}

theorem integrable_component_of_mem_descendantsAtDepth {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) (i : Fin d) :
    Integrable (fun x : Vec d => g x i) (volume.restrict (cubeSet R)) := by
  have : IsFiniteMeasure (volume.restrict (openCubeSet R)) :=
    SuperdiffusionCLT.Section3.ResponseFields.instIsFiniteMeasureVolumeMeasureOnOpenCubeSet R
  have hR' := SuperdiffusionCLT.Section3.Terms.memVectorL2_openCubeSet_of_mem_descendantsAtDepth
    hR hg
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact MemLp.integrable (by norm_num) (MemLp.eval hR' i)

/-- The per-sample bound of the Neumann input. -/
theorem subcubeAvg_neumannBlock_le [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) (hs : 0 < sigmaBarInfinite nu (m - h) P) {Kc n : ℕ} (hn : n ≤ Kc)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (e' : Vec d)
    (he : vecNormSq e' = 1) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) g) :
    subcubeAvg Kc n (fun Q => ENNReal.ofReal
        (blockVecDot
          (ahomSqrtApply nu (m - h) P
            (blockMatVecMul (gaugeMat (-principalGauge m h Q omega))
              (ahomInvSqrtApply nu (m - h) P
                (e', volumeAverageVec (cubeSet Q)
                  (fun y => g y + hshellFlux nu P m h omega e' y)))))
          (ahomSqrtApply nu (m - h) P
            (blockMatVecMul (gaugeMat (-principalGauge m h Q omega))
              (ahomInvSqrtApply nu (m - h) P
                (e', volumeAverageVec (cubeSet Q)
                  (fun y => g y + hshellFlux nu P m h omega e' y))))))) ≤
      ENNReal.ofReal (1 + SuperdiffusionCLT.Section2.Estimates.Stream.vecSqAvg
        (originCube d (Kc : ℤ)) g) := by
  refine le_trans (le_of_eq ?_) (subcubeAvg_unit_prod_le hn e' he hg)
  have hdesc : descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ) =
      descendantsAtDepth (originCube d (Kc : ℤ)) (Kc - n) := by
    have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
      show (n : ℤ) ≤ (Kc : ℤ)
      exact_mod_cast hn
    rw [descendantsAtScale_eq_descendantsAtDepth _ hk]
    congr 1
    show Int.toNat ((Kc : ℤ) - (n : ℤ)) = Kc - n
    omega
  unfold subcubeAvg
  rw [hdesc]
  congr 1
  refine Finset.sum_congr rfl fun Q hQ => ?_
  beta_reduce
  rw [neumannVector_eq nu P m h Q omega e' g hs
    (integrable_component_of_mem_descendantsAtDepth hQ hg)]

end SuperdiffusionCLT.Section5
