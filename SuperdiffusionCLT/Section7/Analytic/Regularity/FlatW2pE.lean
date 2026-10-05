/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.FlatW2pD

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Flat `W^{2,p}` on a cube: the estimate

`flatW2p_divergence` is the divergence-form estimate.
-/

namespace SuperdiffusionCLT.Section7

open SuperdiffusionCLT.Sobolev

variable {d : ℕ}

theorem flatW2p_zero_mem_openCubeSet [NeZero d] (m : ℤ) :
    (0 : Vec d) ∈ openCubeSet (originCube d m) := by
  intro i
  have h : 0 < cubeScaleFactor (originCube d m) := cubeScaleFactor_pos' _
  have e : ((originCube d m).index i : ℝ) = 0 := by simp [originCube]
  rw [e]
  constructor <;> simp [cubeScaleFactor] <;> positivity

/-- **Flat `W^{2,p}`, divergence form.** -/
theorem flatW2p_divergence (hd : 2 ≤ d) {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hpt : p < ⊤) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ (m : ℤ) (A : CoeffField d) (K : ℝ),
        (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) →
        (∀ x ∈ openCubeSet (originCube d m), ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε) →
        (∀ x ∈ openCubeSet (originCube d m), ∀ i j k,
          |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K) →
        K * cubeScaleFactor (originCube d m) ≤ ε →
        ∀ (G : Vec d → Vec d) (DG : Fin d → Vec d → Vec d),
          MemLp G p (normalizedCubeMeasure (originCube d m)) →
          HasWeakJacobianOn (openCubeSet (originCube d m)) G DG →
          MemLp (jacobianHilbertMat DG) p (normalizedCubeMeasure (originCube d m)) →
          ∀ w : H10Function (openCubeSet (originCube d m)),
            IsZeroTraceDirichletRhsWeakSolution A (openCubeSet (originCube d m)) w
              (fun x => -G x) →
            ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) w.toH1Function,
              MemLp (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) p
                (normalizedCubeMeasure (originCube d m)) ∧
              cubeLpNorm (originCube d m) p (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≤
                C * (cubeLpNorm (originCube d m) p (jacobianHilbertMat DG) +
                  (cubeScaleFactor (originCube d m))⁻¹ * cubeLpNorm (originCube d m) p G) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C₂, hC₂pos, hC₂⟩ := CubeCalderonZygmund.exists_cubeDirichletDivergence_cz d
    (⟨2, by norm_num, by simp⟩ : FiniteLpExponent)
  obtain ⟨ε, C₀, hε, hC₀, hcontr, hseq⟩ := flatW2p_sequence hd hp2 hpt hC₂pos
  refine ⟨ε, 2 * C₀, hε, by positivity, ?_⟩
  intro m A K hA hAε hAK hKℓ G DG hGp hweak hJp w hw
  have hK0 : 0 ≤ K :=
    (abs_nonneg _).trans (hAK 0 (flatW2p_zero_mem_openCubeSet m) 0 0 0)
  have hG2 : MemLp G 2 (normalizedCubeMeasure (originCube d m)) := hGp.mono_exponent hp2
  have hAm : ∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet (originCube d m))) :=
    fun i j => (hA i j).continuous.aestronglyMeasurable
  obtain ⟨x, Hx, h0, hs, hHp, hHb⟩ := hseq m A K hA hAε hAK hK0 hKℓ G DG hGp hweak hJp
  have hprob := problem_of_A (originCube d m) hAm hε.le hAε hG2 hw
  have hS := flatW2p_partialSum_problem (originCube d m) hAm hε.le hAε hG2 x h0 hs
  have hlim := l2_tendsto_of_contraction (originCube d m) hAm hε.le hAε (hC₂ (originCube d m)) hC₂pos.le hcontr hG2
    (flatPartialSum x) hprob hS
  obtain ⟨H, hHmem, hHbd⟩ := flatW2p_hessian_of_series (originCube d m) hp2 x Hx hHp hHb w hlim
  refine ⟨H, hHmem, ?_⟩
  have : 2 * (C₀ * (cubeLpNorm (originCube d m) p (jacobianHilbertMat DG) +
      (cubeScaleFactor (originCube d m))⁻¹ * cubeLpNorm (originCube d m) p G)) =
      2 * C₀ * (cubeLpNorm (originCube d m) p (jacobianHilbertMat DG) +
      (cubeScaleFactor (originCube d m))⁻¹ * cubeLpNorm (originCube d m) p G) := by ring
  rw [← this]
  exact hHbd

end SuperdiffusionCLT.Section7
