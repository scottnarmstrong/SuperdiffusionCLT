/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.GeneratorsB
public import SuperdiffusionCLT.Section8.Prereq.DomainIdentificationB

/-!
# The `H¹` limit of a sequence with Cauchy gradients

* `gen_h1_limit`: if `f_n ∈ H¹(U)` converge in `L²(U)` to `F ∈ L²(U)` and every gradient coordinate
  is Cauchy in `L²(U)`, then `F` is the value of an `H¹(U)` function whose gradient is the `L²`
  limit of the gradients.
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- Coordinate gradients which are Cauchy in `L²` have an `L²` limit. -/
theorem gen_coord_limit {U : Set (Vec d)} (g : ℕ → Vec d → ℝ)
    (hg : ∀ n, MemLp (g n) 2 (volume.restrict U))
    (hcau : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
      eLpNorm (fun x => g n x - g m x) 2 (volume.restrict U) ≤ ENNReal.ofReal ε) :
    ∃ G : Vec d → ℝ, MemLp G 2 (volume.restrict U) ∧
      Tendsto (fun n => eLpNorm (fun x => g n x - G x) 2 (volume.restrict U)) atTop (𝓝 0) := by
  set μ := volume.restrict U
  have hC : CauchySeq (fun n => (hg n).toLp (g n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcau (ε / 2) (by linarith only [hε])
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
    have h1 : eLpNorm (g m - g n) 2 μ ≤ ENNReal.ofReal (ε / 2) := hN n m hn hm
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_ofReal (by linarith only [hε])] at this
    linarith only [this, hε]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hC
  have hLm : MemLp (L : Vec d → ℝ) 2 μ := Lp.memLp L
  refine ⟨L, hLm, ?_⟩
  have := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hL
  refine this.congr fun n => ?_
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub ((hg n).toLp (g n)) L, (hg n).coeFn_toLp] with x h1 h2
  rw [Pi.sub_apply, h2]

theorem gen_h1_limit {U : Set (Vec d)} (f : ℕ → H1Function U) (F : Vec d → ℝ)
    (hF : MemLp F 2 (volume.restrict U))
    (hval : Tendsto (fun n => eLpNorm (fun x => (f n).toFun x - F x) 2 (volume.restrict U))
      atTop (𝓝 0))
    (hcau : ∀ i : Fin d, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
      eLpNorm (fun x => (f n).grad x i - (f m).grad x i) 2 (volume.restrict U) ≤
        ENNReal.ofReal ε) :
    ∃ W : H1Function U, W.toFun = F ∧ ∀ i : Fin d,
      Tendsto (fun n => eLpNorm (fun x => (f n).grad x i - W.grad x i) 2 (volume.restrict U))
        atTop (𝓝 0) := by
  choose G hGm hGt using fun i : Fin d => gen_coord_limit (U := U) (fun n x => (f n).grad x i)
    (fun n => (f n).gradMemL2 i) (hcau i)
  refine ⟨⟨F, fun x i => G i x, hF, fun i => hGm i, fun i φ hφ hc hs => ?_⟩, rfl, hGt⟩
  have hφ0 : Continuous φ := hφ.continuous
  have hdφ : Continuous fun x => fderiv ℝ φ x (basisVec i) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφm : MemLp φ 2 (volume.restrict U) :=
    (hφ0.memLp_of_hasCompactSupport hc).restrict U
  have hdφm : MemLp (fun x => fderiv ℝ φ x (basisVec i)) 2 (volume.restrict U) := by
    have hcs : HasCompactSupport fun x => fderiv ℝ φ x (basisVec i) := by
      have := hc.fderiv (𝕜 := ℝ)
      exact this.comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) (by simp)
    exact (hdφ.memLp_of_hasCompactSupport hcs).restrict U
  have h1 := domId_tendsto_integral_mul hdφm (fun n => (f n).memL2) hF hval
  have h2 := domId_tendsto_integral_mul hφm (fun n => (f n).gradMemL2 i) (hGm i) (hGt i)
  have h3 : ∀ n, ∫ x in U, (f n).toFun x * fderiv ℝ φ x (basisVec i) =
      -∫ x in U, (f n).grad x i * φ x := fun n => (f n).hasWeakGradient i φ hφ hc hs
  have h1' : Tendsto (fun n => ∫ x in U, (f n).toFun x * fderiv ℝ φ x (basisVec i)) atTop
      (𝓝 (∫ x in U, F x * fderiv ℝ φ x (basisVec i))) := by
    simpa only [mul_comm] using h1
  have h2' : Tendsto (fun n => ∫ x in U, (f n).grad x i * φ x) atTop
      (𝓝 (∫ x in U, G i x * φ x)) := by
    simpa only [mul_comm] using h2
  have h4 := tendsto_nhds_unique (h1'.congr h3) (h2'.neg)
  exact h4

end SuperdiffusionCLT.Section8
