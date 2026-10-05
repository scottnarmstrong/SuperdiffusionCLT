/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.LinftyL2
public import SuperdiffusionCLT.Section7.Root.HolderRootC
public import SuperdiffusionCLT.Section7.MinimalScale.RootScalesC

/-!
# `L^∞`-`L²` estimate: one cube, and the scale

* `linfL2_step`: the interior estimate on a translated cube `y + □_n` for a weak solution with zero
  right-hand side on a set `W ⊇ y + □_m`, in real terms.
* `linfL2_scale`: the triadic scale `n = ⌊log₃ (r / C₀)⌋` attached to a radius `r ≥ C₀ 3^{m⋆}`.
-/

@[expose] public section

open MeasureTheory Homogenization SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section7
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- One block of the interior estimate, with zero right-hand side. -/
theorem linfL2_step {a : CoeffField d} {shom : ℕ → ℝ} {C0 c N Lhat X0 ε ρ : ℝ} {A : ℕ}
    (hIP : ∀ m n : ℕ, n < m →
      ((m : ℝ) - (n : ℝ)) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) ≤ c →
      Lhat ≤ (nK N n : ℝ) → X0 ≤ (3 : ℝ) ^ nK N n →
      ∀ y ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + A)),
        ∀ (f : Vec d → ℝ) (u : H1Function (shiftCube y (m : ℤ))),
          IsWeakSolutionOn a (shiftCube y (m : ℤ)) u f (fun _ => 0) →
          eLpNorm (fun x => u.toFun x - ⨍ z in shiftCube y (n : ℤ), u.toFun z) ⊤
              (volume.restrict (shiftCube y (n : ℤ))) ≤
            ENNReal.ofReal (C0 * (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ)))) *
              (lpBar (shiftCube y (m : ℤ)) 2
                  (fun x => u.toFun x - ⨍ z in shiftCube y (m : ℤ), u.toFun z) +
                ENNReal.ofReal ((shom m)⁻¹ * (3 : ℝ) ^ (2 * (m : ℝ))) *
                  eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ)))))
    {W : Set (Vec d)} {m n : ℕ} (hnm : n < m)
    (hδ : ((m : ℝ) - (n : ℝ)) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) ≤ c)
    (hL : Lhat ≤ (nK N n : ℝ)) (hX : X0 ≤ (3 : ℝ) ^ nK N n)
    {y : Vec d} (hy : y ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + A)))
    (hsub : h1_cube y m ⊆ W) (hC0 : 0 ≤ C0)
    (u : H1Function W) (hu : IsWeakSolutionOn a W u (fun _ => 0) (fun _ => 0)) :
    MemLp u.toFun ⊤ (volume.restrict (h1_cube y n)) ∧
      h1_linf (h1_cube y n) u.toFun (h1_avg (h1_cube y n) u.toFun) ≤
        C0 * (3 : ℝ) ^ (-((m : ℤ) - (n : ℤ))) * h1_l2 (h1_cube y m) u.toFun := by
  have hsub' : shiftCube y (m : ℤ) ⊆ W := by
    rw [hr_shiftCube_eq]; exact hsub
  have hres := wh2_isWeakSolutionOn_restrict (rc_isOpen_shiftCube y (m : ℤ)) hsub' hu
  have hI := hIP m n hnm hδ hL hX y hy (fun _ => 0)
    (u.restrict (rc_isOpen_shiftCube y (m : ℤ)) hsub') hres
  simp only [H1Function.restrict] at hI
  rw [hr_shiftCube_eq, hr_shiftCube_eq] at hI
  simp only [hr_avg_eq] at hI
  have hu2 : MemLp u.toFun 2 (volume.restrict W) := u.memL2
  have hcm : MemLp u.toFun 2 (volume.restrict (h1_cube y m)) :=
    hu2.mono_measure (Measure.restrict_mono hsub le_rfl)
  rw [hr_lpBar_eq (h1_vol_cube_ne_top y m) (h1_vol_cube_pos y m) hcm] at hI
  have hn3 : (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ))) = (3 : ℝ) ^ (-((m : ℤ) - (n : ℤ))) := by
    rw [← Real.rpow_intCast]; push_cast; rfl
  have hl2 : 0 ≤ h1_l2 (h1_cube y m) u.toFun := Real.sqrt_nonneg _
  have hz : eLpNorm (fun _ : Vec d => (0 : ℝ)) ⊤
      (volume.restrict (h1_cube y m)) = 0 := by simp
  rw [hz, mul_zero, add_zero, ← ENNReal.ofReal_mul (by positivity), hn3] at hI
  have hBd0 : 0 ≤ C0 * (3 : ℝ) ^ (-((m : ℤ) - (n : ℤ))) * h1_l2 (h1_cube y m) u.toFun := by
    positivity
  have hne : eLpNorm (fun x => u.toFun x - h1_avg (h1_cube y n) u.toFun) ⊤
      (volume.restrict (h1_cube y n)) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hI
  have hmem : MemLp (fun x => u.toFun x - h1_avg (h1_cube y n) u.toFun) ⊤
      (volume.restrict (h1_cube y n)) := lt_top_iff_ne_top.2 hne
  refine ⟨?_, ?_⟩
  · have := h1_finite_restrict (h1_vol_cube_ne_top y n)
    have h := hmem.add (memLp_const (h1_avg (h1_cube y n) u.toFun))
    have e : ((fun x => u.toFun x - h1_avg (h1_cube y n) u.toFun) +
        fun _ => h1_avg (h1_cube y n) u.toFun) = u.toFun := by
      funext x; simp
    rwa [e] at h
  · unfold h1_linf
    exact ENNReal.toReal_le_of_le_ofReal hBd0 hI

end SuperdiffusionCLT.Section8
