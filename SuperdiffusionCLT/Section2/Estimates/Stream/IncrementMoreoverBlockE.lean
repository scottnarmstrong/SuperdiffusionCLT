/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Cutoff.CenteredCoeffOn
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementGagliardoSup
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockD

/-!
# The continuity of the limiting centered field

The multiscale Poincaré bridge of `MultiscalePoincareFullGradient` is stated for a continuous matrix field,
while `Section2.Carriers.centeredStreamField` provides only pointwise convergence on the
centring set. On the summability guard, the series of shell derivative norms converges on
**every** natural cube, the defining series converges uniformly on every
open origin cube `cu_i` with `m < i`, because the centred shell term is
bounded there by `√d · 3^i · ‖∇ j_k‖_{L∞(cu_i)}` through the mean-value
inequality on the convex set `openCubeSet cu_i ⊇ cubeSet cu_m`. The open
origin cubes exhaust `Vec d`, so the sum is continuous at every point.

## Main results

* `convex_openCubeSet`, `exists_lt_mem_openCubeSet_originCube`,
  `norm_centeredShellTerm_le_openCubeSet`, `continuous_centeredShellTerm`,
  `continuous_centeredStreamField`: the continuity of the limiting field on the
  guard.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Estimates
namespace Stream

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A constant factor passes through a normalized average. -/
theorem volumeAverage_const_mul (U : Set (Vec d)) (c : ℝ) (f : Vec d → ℝ) :
    volumeAverage U (fun x => c * f x) = c * volumeAverage U f := by
  rw [volumeAverage, volumeAverage, integral_const_mul]
  ring

/-! ## Continuity of the limiting centered field on the guard -/

section Elementwise

open scoped Matrix.Norms.Elementwise

/-- The open realization of a triadic cube is convex. -/
theorem convex_openCubeSet (Q : TriadicCube d) : Convex ℝ (openCubeSet Q) := by
  rw [openCubeSet_eq_pi_Ioo]
  exact convex_pi fun i _ ↦ convex_Ioo _ _

/-- **The open origin cubes exhaust the ambient space**, at arbitrarily large
scale. -/
theorem exists_lt_mem_openCubeSet_originCube (m : ℕ) (x : Vec d) :
    ∃ i : ℕ, m < i ∧ x ∈ openCubeSet (originCube d (i : ℤ)) := by
  obtain ⟨N, hN⟩ :=
    pow_unbounded_of_one_lt (2 * ‖x‖ + 1) (by norm_num : (1 : ℝ) < 3)
  refine ⟨max N (m + 1),
    lt_of_lt_of_le (Nat.lt_succ_self m) (le_max_right _ _), ?_⟩
  have hmono : (3 : ℝ) ^ N ≤ (3 : ℝ) ^ (max N (m + 1)) :=
    pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
  have hbig : 2 * ‖x‖ + 1 < (3 : ℝ) ^ (max N (m + 1)) :=
    lt_of_lt_of_le hN hmono
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have habs : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  rw [zpow_natCast]
  constructor
  · linarith only [hbig, habs, (abs_le.1 habs).1]
  · linarith only [hbig, habs, (abs_le.1 habs).2]

/-- **The centred shell term is uniformly small on a strictly larger open
origin cube.** The mean-value inequality on the convex set
`openCubeSet cu_i ⊇ cubeSet cu_m` gives the Weierstrass majorant of the
defining series away from the centring cube. -/
theorem norm_centeredShellTerm_le_openCubeSet {m i : ℕ} (hmi : m < i)
    (omega : ShellSeq d) (k : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (i : ℤ))) :
    ‖centeredShellTerm omega (cubeSet (originCube d (m : ℤ))) k x‖ ≤
      Real.sqrt d * (3 : ℝ) ^ i *
        shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k) := by
  have hsub := cubeSet_originCube_subset_openCubeSet (d := d) hmi
  have hLnn :
      0 ≤ shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k) :=
    shellDerivLinftyNorm_nonneg _ _
  refine norm_sub_volumeAverageMat_le (isBounded_cubeSet _)
    (volume_cubeSet_ne_zero _)
    (fun a b => integrableOn_entry_of_isBounded (shellReg omega k)
      (isBounded_cubeSet _) a b) ?_
  intro y hy
  have hyi : y ∈ openCubeSet (originCube d (i : ℤ)) := hsub hy
  have hmv := norm_shell_sub_le (isBounded_openCubeSet (originCube d (i : ℤ)))
    (convex_openCubeSet (originCube d (i : ℤ))) (omega k) hx hyi
  have hdist : ‖y - x‖ ≤ (3 : ℝ) ^ i := by
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ i := by positivity
    refine (pi_norm_le_iff_of_nonneg h3).2 fun j => ?_
    rw [mem_openCubeSet_originCube_iff] at hx hyi
    obtain ⟨hx1, hx2⟩ := hx j
    obtain ⟨hy1, hy2⟩ := hyi j
    rw [zpow_natCast] at hx1 hx2 hy1 hy2
    have hcoord : (y - x) j = y j - x j := rfl
    rw [hcoord, Real.norm_eq_abs, abs_le]
    constructor <;> linarith only [hx1, hx2, hy1, hy2]
  calc ‖shellReg omega k x - shellReg omega k y‖
      = ‖(omega k) y - (omega k) x‖ := by
        rw [← norm_neg]
        simp only [shellReg, ShellField.forgetShell_apply]
        congr 1
        abel
    _ ≤ Real.sqrt d *
          shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k) *
          ‖y - x‖ := hmv
    _ ≤ Real.sqrt d *
          shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k) *
          (3 : ℝ) ^ i :=
        mul_le_mul_of_nonneg_left hdist
          (mul_nonneg (Real.sqrt_nonneg _) hLnn)
    _ = Real.sqrt d * (3 : ℝ) ^ i *
          shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ)))
            (omega k) := by ring

/-- Every centred shell term is continuous: the shell is a stored continuous
map and the centring is a constant. -/
theorem continuous_centeredShellTerm (omega : ShellSeq d) (U : Set (Vec d))
    (k : ℕ) : Continuous (centeredShellTerm omega U k) := by
  refine continuous_matrix fun a b => ?_
  have hentry : (fun x : Vec d => centeredShellTerm omega U k x a b)
      = fun x : Vec d => shellReg omega k x a b
          - volumeAverageMat U (fun y => shellReg omega k y) a b := by
    funext x
    simp only [centeredShellTerm, Matrix.sub_apply]
  rw [hentry]
  exact (shellReg_entry_continuous omega k a b).sub continuous_const

/-- **The limiting centered field is continuous on the summability
guard.** The defining series converges uniformly on every open origin cube, and
those cubes exhaust the ambient space. -/
theorem continuous_centeredStreamField {m : ℕ} (omega : ShellSeq d)
    (hguard : ∀ i : ℕ, Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k)) :
    Continuous (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨i, hmi, hxi⟩ := exists_lt_mem_openCubeSet_originCube (d := d) m x
  have huniform := tendstoUniformlyOn_tsum_nat
    (f := fun k : ℕ =>
      centeredShellTerm omega (cubeSet (originCube d (m : ℤ))) k)
    (u := fun k : ℕ => Real.sqrt d * (3 : ℝ) ^ i *
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k))
    ((hguard i).mul_left _) (s := openCubeSet (originCube d (i : ℤ)))
    (fun k y hy => norm_centeredShellTerm_le_openCubeSet hmi omega k hy)
  have hcont : ContinuousOn
      (centeredStreamField omega (cubeSet (originCube d (m : ℤ))))
      (openCubeSet (originCube d (i : ℤ))) :=
    huniform.continuousOn (Filter.Frequently.of_forall fun N =>
      continuousOn_finsetSum _ fun k _ =>
        (continuous_centeredShellTerm omega _ k).continuousOn)
  exact hcont.continuousAt ((isOpen_openCubeSet _).mem_nhds hxi)

end Elementwise

/-! ## The bridge in the printed carrier -/

section Bridge

open scoped Matrix.Norms.L2Operator

end Bridge

end

end Stream
end Estimates
end Section2
end SuperdiffusionCLT
