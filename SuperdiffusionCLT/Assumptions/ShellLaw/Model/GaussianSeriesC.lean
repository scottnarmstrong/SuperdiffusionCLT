/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.GaussianSeriesB

/-!
# Locality of the cell series

At a point `x` only the cells of `cellsNear x` contribute to the value and to the first two
derivatives; near `x` only the cells of the finite set `nv_cellsAround x` can contribute.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization Set Real MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

theorem nv_mem_cellsNear_of_lt {x : Vec d} {k : Fin d → ℤ}
    (hlt : ∀ i, |x i - (k i : ℝ) / 2| < 1) : k ∈ cellsNear x := by
  refine Fintype.mem_piFinset.2 fun i ↦ ?_
  have h2 := abs_lt.1 (hlt i)
  have f0 := Int.floor_le (2 * x i)
  have f1 := Int.lt_floor_add_one (2 * x i)
  rw [Finset.mem_Icc]
  constructor
  · have : ((⌊2 * x i⌋ : ℤ) : ℝ) - 2 < (k i : ℝ) := by linarith only [h2.2, f0]
    have h3 : ((⌊2 * x i⌋ - 2 : ℤ) : ℝ) < (k i : ℝ) := by push_cast; exact this
    have := Int.cast_lt.1 h3
    omega
  · have : (k i : ℝ) < ((⌊2 * x i⌋ : ℤ) : ℝ) + 3 := by linarith only [h2.1, f1]
    have h3 : (k i : ℝ) < ((⌊2 * x i⌋ + 3 : ℤ) : ℝ) := by push_cast; exact this
    have := Int.cast_lt.1 h3
    omega

/-- The derivatives of the coefficient vanish also on the boundary `|x i - c i| = 1`. -/
theorem nv_iteratedFDeriv_eq_zero_of_one_le {c x : Vec d} {i : Fin d} (hx : 1 ≤ |x i - c i|)
    (p : NvFrame d) (n : ℕ) :
    iteratedFDeriv ℝ n (fun y ↦ cellKernelCoeff c y p) x = 0 := by
  have hg : Continuous fun y : Vec d ↦ iteratedFDeriv ℝ n (fun y ↦ cellKernelCoeff c y p) y :=
    (contDiff_cellKernelCoeff c p).continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)
  set σ : ℝ := if 0 ≤ x i - c i then 1 else -1 with hσ
  set u : Vec d := σ • Pi.single i 1 with hu
  have hT : Tendsto (fun t : ℝ ↦ iteratedFDeriv ℝ n (fun y ↦ cellKernelCoeff c y p) (x + t • u))
      (𝓝[>] 0) (𝓝 (iteratedFDeriv ℝ n (fun y ↦ cellKernelCoeff c y p) x)) := by
    have hc : Continuous fun t : ℝ ↦ x + t • u := continuous_const.add (continuous_id.smul continuous_const)
    have := (hg.comp hc).tendsto 0
    simp only [Function.comp_apply, zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      iteratedFDeriv ℝ n (fun y ↦ cellKernelCoeff c y p) (x + t • u) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    refine iteratedFDeriv_cellKernelCoeff_eq_zero ⟨i, ?_⟩ p n
    have hcoord : (x + t • u) i = x i + t * σ := by
      simp [hu]
    rw [hcoord]
    by_cases h0 : 0 ≤ x i - c i
    · have hs : σ = 1 := by simp [hσ, h0]
      rw [hs]
      have : 1 ≤ x i - c i := by rwa [abs_of_nonneg h0] at hx
      rw [abs_of_pos (by linarith only [this, ht'])]
      linarith only [this, ht']
    · have hs : σ = -1 := by simp [hσ, h0]
      rw [hs]
      have hneg : x i - c i < 0 := lt_of_not_ge h0
      have : 1 ≤ -(x i - c i) := by rwa [abs_of_neg hneg] at hx
      rw [abs_of_neg (by linarith only [this, ht'])]
      linarith only [this, ht']
  exact tendsto_nhds_unique hT (tendsto_const_nhds.congr' (hev.mono fun t ht ↦ ht.symm))

/-- All derivatives of the coefficient of a cell outside `cellsNear x` vanish at `x`. -/
theorem nv_iteratedFDeriv_eq_zero_of_not_mem_cellsNear {x : Vec d} {k : Fin d → ℤ}
    (hk : k ∉ cellsNear x) (p : NvFrame d) (n : ℕ) :
    iteratedFDeriv ℝ n (fun y ↦ cellKernelCoeff (nv_cen k) y p) x = 0 := by
  by_contra hne
  refine hk (nv_mem_cellsNear_of_lt fun i ↦ ?_)
  exact lt_of_not_ge fun h ↦ hne (nv_iteratedFDeriv_eq_zero_of_one_le (i := i) h p n)

/-- The cells that can contribute in the box of half-width `1/2` around `x`. -/
def nv_cellsAround (x : Vec d) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i ↦ Finset.Icc (⌊2 * x i⌋ - 3) (⌊2 * x i⌋ + 4)

theorem nv_cellsNear_subset_around (x : Vec d) : cellsNear x ⊆ nv_cellsAround x := by
  intro k hk
  refine Fintype.mem_piFinset.2 fun i ↦ ?_
  have := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hk i)
  rw [Finset.mem_Icc]
  omega

/-- A cell outside `nv_cellsAround x0` has vanishing coefficients on the box around `x0`. -/
theorem nv_far_of_not_mem_around {x0 x : Vec d} {k : Fin d → ℤ}
    (hk : k ∉ nv_cellsAround x0) (hx : ∀ i, |x i - x0 i| < 1 / 2) :
    ∃ i, 1 < |x i - (k i : ℝ) / 2| := by
  by_contra hcon
  push Not at hcon
  refine hk (Fintype.mem_piFinset.2 fun i ↦ ?_)
  have h1 := abs_le.1 (hcon i)
  have h2 := abs_lt.1 (hx i)
  have f0 := Int.floor_le (2 * x0 i)
  have f1 := Int.lt_floor_add_one (2 * x0 i)
  rw [Finset.mem_Icc]
  constructor
  · have : ((⌊2 * x0 i⌋ : ℤ) : ℝ) - 4 < (k i : ℝ) := by linarith only [h1.1, h1.2, h2.1, h2.2, f0, f1]
    have h3 : ((⌊2 * x0 i⌋ - 4 : ℤ) : ℝ) < (k i : ℝ) := by push_cast; exact this
    have := Int.cast_lt.1 h3
    omega
  · have : (k i : ℝ) < ((⌊2 * x0 i⌋ : ℤ) : ℝ) + 5 := by linarith only [h1.1, h1.2, h2.1, h2.2, f0, f1]
    have h3 : (k i : ℝ) < ((⌊2 * x0 i⌋ + 5 : ℤ) : ℝ) := by push_cast; exact this
    have := Int.cast_lt.1 h3
    omega

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
