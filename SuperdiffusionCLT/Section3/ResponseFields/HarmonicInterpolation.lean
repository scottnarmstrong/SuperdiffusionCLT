/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.Norms
public import Homogenization.Sobolev.Foundations.QuantitativeCutoff
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.QuantCutoffLowerH1
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Transport
public import Homogenization.Geometry.ConvexDomain

/-!
# Step 3 of `l.abstract.response.fields`: the cube cutoffs and the boundary layer

The paper (Step 3 of the proof of `l.abstract.response.fields`) proves the harmonic
interpolation inequality `e.abstract.harmonic.interpolation`

> `‖∇v‖_{L̲²(cu_M)} ≤ C (3^{-M}‖v − (v)_{cu_M}‖_{L̲²(cu_M)})^{1/5} ‖∇v‖_{L̲⁴(cu_M)}^{4/5}`

for `v` harmonic in `cu_M`. The proof fixes `ε ∈ (0,1/2)`, takes a cutoff
`φ ∈ C_c^∞(cu_M)` with

> `0 ≤ φ ≤ 1`, `φ = 1` on the set of points whose distance from `∂cu_M` is
> larger than `ε 3^M`, and `‖∇φ‖_{L^∞} ≤ C ε⁻¹ 3^{-M}`,

tests `Δv = 0` against `(v − (v)_{cu_M})φ²`, splits the integral into the
interior and the boundary layer, applies Hölder on the second piece and
balances the two terms in `ε`.

This file supplies the three ingredients of that proof which do not involve the
equation: the cutoff family, the size of the boundary layer, and the two
inequalities the split consumes. The Caccioppoli inequality obtained by testing
the equation, and the assembly, are in `HarmonicInterpolationB.lean`.

## The cutoff

`collarCutoff Q ε` is the canonical smooth cutoff of
`Homogenization.QuantitativeCubeCutoff` between the concentric subcubes of
relative radii `1 − 2ε` and `1 − ε`. Its four printed properties are
`collarCutoff_nonneg`, `collarCutoff_le_one`,
`collarCutoff_eq_one_of_mem_cubeShrunkSet` (the printed "`φ = 1` at distance
more than `ε3^M` from `∂cu_M`", written with the upstream
`cubeShrunkSet Q ε`) and `vecNorm_gradCollarCutoff_le` (the printed
`‖∇φ‖_{L^∞} ≤ Cε⁻¹3^{-M}`, with `3^{-M} = (cubeScaleFactor Q)⁻¹` and the
explicit constant `collarCutoffGradientConst d`).

## The boundary layer

`normalizedCubeMeasure_cubeBoundaryLayer_le` is the geometric statement behind
the printed `‖1 − φ²‖_{L̲²(cu_M)} ≤ Cε^{1/2}`: the collar of relative width `ε`
has normalized measure at most `2dε`, by Bernoulli's inequality applied to
`1 − (1 − 2ε)^d`. `cubeLpENorm_four_collarDefect_le` is that printed bound
itself, in the square-root form `‖(1 − φ²)^{1/2}‖_{L̲⁴(cu_M)}` in which the
Hölder step consumes it.

## The two inequalities of the split

`vecCubeLpENorm_two_sq_split` is the splitting display, and
`le_mul_rpow_fifth_mul_rpow_four_fifth` is the balancing of the two terms in `ε`, in `ℝ≥0∞`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section3
namespace ResponseFields

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The cutoff family -/

/-- The constant `C` of the printed cutoff bound `‖∇φ‖_{L^∞} ≤ Cε⁻¹3^{-M}`,
in the Euclidean magnitude. -/
noncomputable def collarCutoffGradientConst (d : ℕ) : ℝ :=
  4 * (d : ℝ) ^ (2 : ℕ) * Homogenization.smoothTransitionProfile.derivBound

theorem collarCutoffGradientConst_nonneg (d : ℕ) :
    0 ≤ collarCutoffGradientConst d := by
  have h := Homogenization.smoothTransitionProfile.derivBound_nonneg
  have hd : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := by positivity
  exact mul_nonneg (by positivity) h

/-- The cutoff `φ` at collar width `ε`: the canonical smooth cube
cutoff between the concentric subcubes of relative radii `1 − 2ε` and `1 − ε`.
It is defined for every real `ε`; the printed properties hold for
`ε ∈ (0, 1/2)`. -/
noncomputable def collarCutoff (Q : TriadicCube d) (ε : ℝ) : Vec d → ℝ :=
  QuantitativeCubeCutoff.canonicalFun Q (1 - 2 * ε) (1 - ε)

variable {Q : TriadicCube d} {ε : ℝ}

private theorem cubeScaleFactor_pos' (Q : TriadicCube d) : 0 < cubeScaleFactor Q := by
  simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)

private theorem inner_pos (hεh : ε < 1 / 2) : 0 < 1 - 2 * ε := by linarith only [hεh]

private theorem inner_lt_outer (hε0 : 0 < ε) : 1 - 2 * ε < 1 - ε := by
  linarith only [hε0]

theorem collarCutoff_smooth (Q : TriadicCube d) (hε0 : 0 < ε) (hεh : ε < 1 / 2) :
    ContDiff ℝ (⊤ : ℕ∞) (collarCutoff Q ε) :=
  QuantitativeCubeCutoff.canonicalFun_smooth Q (inner_pos hεh) (inner_lt_outer hε0)

theorem collarCutoff_nonneg (Q : TriadicCube d) (ε : ℝ) (x : Vec d) :
    0 ≤ collarCutoff Q ε x :=
  QuantitativeCubeCutoff.canonicalFun_nonneg Q _ _ x

theorem collarCutoff_le_one (Q : TriadicCube d) (ε : ℝ) (x : Vec d) :
    collarCutoff Q ε x ≤ 1 :=
  QuantitativeCubeCutoff.canonicalFun_le_one Q _ _ x

theorem collarCutoff_hasCompactSupport (Q : TriadicCube d) (hε0 : 0 < ε)
    (hεh : ε < 1 / 2) : HasCompactSupport (collarCutoff Q ε) :=
  QuantitativeCubeCutoff.canonicalFun_hasCompactSupport Q (inner_pos hεh)
    (inner_lt_outer hε0)

/-! ### The geometry of the concentric subcubes -/

/-- A closed concentric subcube of relative radius `ρ < 1` sits inside the open
cube. This is what makes the cutoff compactly supported in
`cu_M`. -/
theorem scaledClosedCubeSet_subset_openCubeSet (Q : TriadicCube d) {ρ : ℝ}
    (hρ : ρ < 1) : scaledClosedCubeSet Q ρ ⊆ openCubeSet Q := by
  intro x hx i
  have hs : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hxi : |x i - (Q.index i : ℝ) * cubeScaleFactor Q| ≤
      ρ * ((1 / 2 : ℝ) * cubeScaleFactor Q) := hx i
  have habs := abs_le.1 hxi
  constructor
  · nlinarith only [habs.1, hs, hρ]
  · nlinarith only [habs.2, hs, hρ]

/-- The interior of the printed boundary layer: the points at distance more
than `ε 3^M` from `∂cu_M` lie in the closed concentric subcube of
relative radius `1 − 2ε`, where the cutoff is `1`. -/
theorem cubeShrunkSet_subset_scaledClosedCubeSet (Q : TriadicCube d) (t : ℝ) :
    cubeShrunkSet Q t ⊆ scaledClosedCubeSet Q (1 - 2 * t) := by
  intro x hx i
  have hs : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hxi : ((Q.index i : ℝ) - 1 / 2 + t) * cubeScaleFactor Q ≤ x i ∧
      x i < ((Q.index i : ℝ) + 1 / 2 - t) * cubeScaleFactor Q := hx i
  show |x i - (Q.index i : ℝ) * cubeScaleFactor Q| ≤
    (1 - 2 * t) * ((1 / 2 : ℝ) * cubeScaleFactor Q)
  rw [abs_le]
  constructor
  · nlinarith only [hxi.1, hs]
  · nlinarith only [hxi.2, hs]

theorem collarCutoff_tsupport_subset (Q : TriadicCube d) (hε0 : 0 < ε)
    (hεh : ε < 1 / 2) : tsupport (collarCutoff Q ε) ⊆ openCubeSet Q :=
  le_trans
    (QuantitativeCubeCutoff.canonicalFun_tsupport_subset_scaledClosedCubeSet
      (inner_pos hεh) (inner_lt_outer hε0))
    (scaledClosedCubeSet_subset_openCubeSet Q (by linarith only [hε0]))

/-- **`φ = 1` off the collar**: the cutoff is `1` at every point
whose distance from `∂cu_M` exceeds `ε 3^M`. -/
theorem collarCutoff_eq_one_of_mem_cubeShrunkSet (Q : TriadicCube d)
    (hε0 : 0 < ε) (hεh : ε < 1 / 2) {x : Vec d} (hx : x ∈ cubeShrunkSet Q ε) :
    collarCutoff Q ε x = 1 :=
  QuantitativeCubeCutoff.canonicalFun_eq_one_on_inner (inner_pos hεh)
    (inner_lt_outer hε0) (cubeShrunkSet_subset_scaledClosedCubeSet Q ε hx)

/-! ### The gradient of the cutoff -/

/-- The gradient of the cutoff, in the coordinates of `Vec d`. -/
noncomputable def gradCollarCutoff (Q : TriadicCube d) (ε : ℝ) : Vec d → Vec d :=
  fun x i => (fderiv ℝ (collarCutoff Q ε) x) (basisVec i)

private theorem norm_basisVec' (i : Fin d) : ‖basisVec i‖ = (1 : ℝ) := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).2 ?_
    intro j
    by_cases hji : j = i
    · subst hji; simp [basisVec]
    · simp [basisVec, hji]
  · have hi : ‖basisVec i i‖ ≤ ‖basisVec i‖ := norm_le_pi_norm (basisVec i) i
    simpa [basisVec] using hi

private theorem vecNorm_sq_eq_sum (y : Vec d) :
    vecNorm y ^ (2 : ℕ) = ∑ i, (y i) ^ (2 : ℕ) := by
  rw [vecNorm, PiLp.norm_sq_eq_of_L2]
  simp [sq_abs]

/-- The ambient supremum norm of `Vec d` is dominated by the Euclidean
magnitude. -/
theorem norm_le_vecNorm (y : Vec d) : ‖y‖ ≤ vecNorm y := by
  refine (pi_norm_le_iff_of_nonneg (vecNorm_nonneg y)).2 (fun j => ?_)
  have hmem : (y j) ^ (2 : ℕ) ≤ ∑ i, (y i) ^ (2 : ℕ) :=
    Finset.single_le_sum (f := fun i => (y i) ^ (2 : ℕ))
      (fun i _ => sq_nonneg (y i)) (Finset.mem_univ j)
  rw [← vecNorm_sq_eq_sum] at hmem
  have habs : |y j| ^ (2 : ℕ) ≤ vecNorm y ^ (2 : ℕ) := by
    rwa [sq_abs]
  have := le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (vecNorm_nonneg y) habs
  simpa [Real.norm_eq_abs] using this

/-- The gradient of the cutoff is continuous. -/
theorem gradCollarCutoff_continuous (Q : TriadicCube d) (hε0 : 0 < ε)
    (hεh : ε < 1 / 2) : Continuous (gradCollarCutoff Q ε) := by
  have hfd : Continuous (fun x : Vec d => fderiv ℝ (collarCutoff Q ε) x) :=
    (collarCutoff_smooth Q hε0 hεh).continuous_fderiv (by simp)
  exact continuous_pi (fun i => hfd.clm_apply continuous_const)

/-- **`‖∇φ‖_{L^∞} ≤ Cε⁻¹3^{-M}`**, in the Euclidean magnitude and with
`3^{-M} = (cubeScaleFactor cu_M)⁻¹`. -/
theorem vecNorm_gradCollarCutoff_le (Q : TriadicCube d) (hε0 : 0 < ε)
    (hεh : ε < 1 / 2) (x : Vec d) :
    vecNorm (gradCollarCutoff Q ε x) ≤
      collarCutoffGradientConst d * ε⁻¹ * (cubeScaleFactor Q)⁻¹ := by
  have hs : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have hsne : cubeScaleFactor Q ≠ 0 := ne_of_gt hs
  have hderiv : (0 : ℝ) ≤ Homogenization.smoothTransitionProfile.derivBound :=
    Homogenization.smoothTransitionProfile.derivBound_nonneg
  have he0 : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε0
  have hsf0 : (0 : ℝ) < (cubeScaleFactor Q)⁻¹ := inv_pos.2 hs
  have hop := QuantitativeCubeCutoff.canonicalFun_gradient_bound Q (inner_pos hεh)
    (inner_lt_outer hε0) x
  have hop' : ‖fderiv ℝ (collarCutoff Q ε) x‖ ≤
      (d : ℝ) * Homogenization.smoothTransitionProfile.derivBound *
        (4 * ε⁻¹ * (cubeScaleFactor Q)⁻¹) := by
    refine le_trans hop (le_of_eq ?_)
    have hden : (1 - ε - (1 - 2 * ε)) * cubeRadius Q =
        ε * cubeScaleFactor Q / 2 := by
      rw [cubeRadius]; ring
    rw [hden]
    congr 1
    field_simp
    norm_num
  have hop_nonneg : 0 ≤ ‖fderiv ℝ (collarCutoff Q ε) x‖ := norm_nonneg _
  have hcoord : ∀ i : Fin d,
      (gradCollarCutoff Q ε x i) ^ (2 : ℕ) ≤
        ‖fderiv ℝ (collarCutoff Q ε) x‖ ^ (2 : ℕ) := by
    intro i
    have h1 : |gradCollarCutoff Q ε x i| ≤ ‖fderiv ℝ (collarCutoff Q ε) x‖ := by
      have hle := (fderiv ℝ (collarCutoff Q ε) x).le_opNorm (basisVec i)
      rw [norm_basisVec' i, mul_one] at hle
      simpa [gradCollarCutoff, Real.norm_eq_abs] using hle
    have h2 := sq_abs (gradCollarCutoff Q ε x i)
    nlinarith only [h1, h2, abs_nonneg (gradCollarCutoff Q ε x i), hop_nonneg]
  have hsum : vecNorm (gradCollarCutoff Q ε x) ^ (2 : ℕ) ≤
      (d : ℝ) * ‖fderiv ℝ (collarCutoff Q ε) x‖ ^ (2 : ℕ) := by
    rw [vecNorm_sq_eq_sum]
    calc ∑ i, (gradCollarCutoff Q ε x i) ^ (2 : ℕ)
        ≤ ∑ _i : Fin d, ‖fderiv ℝ (collarCutoff Q ε) x‖ ^ (2 : ℕ) :=
          Finset.sum_le_sum (fun i _ => hcoord i)
      _ = (d : ℝ) * ‖fderiv ℝ (collarCutoff Q ε) x‖ ^ (2 : ℕ) := by
          simp [Finset.sum_const]
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdd : (d : ℝ) ^ (3 : ℕ) ≤ (d : ℝ) ^ (4 : ℕ) := by
    rcases Nat.eq_zero_or_pos d with hzero | hpos
    · simp [hzero]
    · have hone : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hpos
      nlinarith only [hone, pow_nonneg hd 3]
  have hsq : ‖fderiv ℝ (collarCutoff Q ε) x‖ ^ (2 : ℕ) ≤
      ((d : ℝ) * Homogenization.smoothTransitionProfile.derivBound *
        (4 * ε⁻¹ * (cubeScaleFactor Q)⁻¹)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hop_nonneg hop' 2
  have hmid : (d : ℝ) * ‖fderiv ℝ (collarCutoff Q ε) x‖ ^ (2 : ℕ) ≤
      (collarCutoffGradientConst d * ε⁻¹ * (cubeScaleFactor Q)⁻¹) ^ (2 : ℕ) := by
    refine le_trans (mul_le_mul_of_nonneg_left hsq hd) ?_
    have hL : (d : ℝ) * ((d : ℝ) * Homogenization.smoothTransitionProfile.derivBound *
          (4 * ε⁻¹ * (cubeScaleFactor Q)⁻¹)) ^ (2 : ℕ) =
        16 * (d : ℝ) ^ (3 : ℕ) *
          (Homogenization.smoothTransitionProfile.derivBound ^ (2 : ℕ) *
            ((ε⁻¹) ^ (2 : ℕ) * ((cubeScaleFactor Q)⁻¹) ^ (2 : ℕ))) := by
      ring
    have hR : (collarCutoffGradientConst d * ε⁻¹ * (cubeScaleFactor Q)⁻¹) ^ (2 : ℕ) =
        16 * (d : ℝ) ^ (4 : ℕ) *
          (Homogenization.smoothTransitionProfile.derivBound ^ (2 : ℕ) *
            ((ε⁻¹) ^ (2 : ℕ) * ((cubeScaleFactor Q)⁻¹) ^ (2 : ℕ))) := by
      rw [collarCutoffGradientConst]
      ring
    rw [hL, hR]
    have hpos : (0 : ℝ) ≤ Homogenization.smoothTransitionProfile.derivBound ^ (2 : ℕ) *
        ((ε⁻¹) ^ (2 : ℕ) * ((cubeScaleFactor Q)⁻¹) ^ (2 : ℕ)) := by positivity
    nlinarith only [hdd, hpos]
  have hrhs : 0 ≤ collarCutoffGradientConst d * ε⁻¹ * (cubeScaleFactor Q)⁻¹ :=
    mul_nonneg (mul_nonneg (collarCutoffGradientConst_nonneg d) he0.le) hsf0.le
  exact le_of_pow_le_pow_left₀ (by norm_num) hrhs (le_trans hsum hmid)

/-! ## The boundary layer -/

/-- **The collar of relative width `ε` is small**: the normalized measure of
the set of points of `cu_M` within `ε 3^M` of `∂cu_M` is at most `2dε`. This
is the geometric content of the printed `‖1 − φ²‖_{L̲²(cu_M)} ≤ Cε^{1/2}`,
and it is Bernoulli's inequality for `1 − (1 − 2ε)^d`. -/
theorem normalizedCubeMeasure_cubeBoundaryLayer_le (Q : TriadicCube d)
    (hε0 : 0 ≤ ε) (hεh : ε ≤ 1 / 2) :
    normalizedCubeMeasure Q (cubeBoundaryLayer Q ε) ≤
      ENNReal.ofReal (2 * (d : ℝ) * ε) := by
  have hs : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hvol : 0 < cubeVolume Q := cubeVolume_pos Q
  have hsub : cubeBoundaryLayer Q ε ⊆ cubeSet Q := cubeBoundaryLayer_subset_cubeSet Q ε
  have hfin : volume (cubeBoundaryLayer Q ε) ≠ ⊤ :=
    measure_ne_top_of_subset hsub (volume_cubeSet_lt_top Q).ne
  have hrestrict : (volume.restrict (cubeSet Q)) (cubeBoundaryLayer Q ε) =
      volume (cubeBoundaryLayer Q ε) := by
    rw [Measure.restrict_apply' (measurableSet_cubeSet Q),
      Set.inter_eq_self_of_subset_left hsub]
  have htoReal := volume_cubeBoundaryLayer_toReal_of_nonneg_le_half Q hε0 hεh
  have hofReal : volume (cubeBoundaryLayer Q ε) =
      ENNReal.ofReal (cubeVolume Q - ((1 - 2 * ε) * cubeScaleFactor Q) ^ d) := by
    rw [← htoReal, ENNReal.ofReal_toReal hfin]
  -- Bernoulli
  have hbern : 1 + (d : ℝ) * (-(2 * ε)) ≤ (1 + -(2 * ε)) ^ d :=
    one_add_mul_le_pow (by linarith only [hε0, hεh]) d
  have hpow : ((1 - 2 * ε) * cubeScaleFactor Q) ^ d =
      (1 - 2 * ε) ^ d * cubeVolume Q := by
    rw [mul_pow, cubeVolume]
  have hkey : cubeVolume Q - ((1 - 2 * ε) * cubeScaleFactor Q) ^ d ≤
      2 * (d : ℝ) * ε * cubeVolume Q := by
    rw [hpow]
    have hb : 1 - 2 * (d : ℝ) * ε ≤ (1 - 2 * ε) ^ d := by
      have hrw : (1 : ℝ) + -(2 * ε) = 1 - 2 * ε := by ring
      rw [hrw] at hbern
      linarith only [hbern]
    nlinarith only [hb, hvol]
  calc normalizedCubeMeasure Q (cubeBoundaryLayer Q ε)
      = ENNReal.ofReal ((cubeVolume Q)⁻¹) * volume (cubeBoundaryLayer Q ε) := by
        rw [normalizedCubeMeasure, cubeMeasure]
        simp only [Measure.smul_apply, smul_eq_mul]
        rw [hrestrict]
    _ = ENNReal.ofReal ((cubeVolume Q)⁻¹ *
          (cubeVolume Q - ((1 - 2 * ε) * cubeScaleFactor Q) ^ d)) := by
        rw [hofReal, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hvol))]
    _ ≤ ENNReal.ofReal (2 * (d : ℝ) * ε) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hinv : 0 < (cubeVolume Q)⁻¹ := inv_pos.2 hvol
        have := mul_le_mul_of_nonneg_left hkey hinv.le
        calc (cubeVolume Q)⁻¹ * (cubeVolume Q -
              ((1 - 2 * ε) * cubeScaleFactor Q) ^ d)
            ≤ (cubeVolume Q)⁻¹ * (2 * (d : ℝ) * ε * cubeVolume Q) := this
          _ = 2 * (d : ℝ) * ε := by field_simp

/-- The defect `(1 − φ²)^{1/2}` of the boundary-layer splitting:
it vanishes off the collar and is bounded by one. -/
noncomputable def collarDefect (Q : TriadicCube d) (ε : ℝ) : Vec d → ℝ :=
  fun x => Real.sqrt (1 - (collarCutoff Q ε x) ^ (2 : ℕ))

theorem collarDefect_nonneg (Q : TriadicCube d) (ε : ℝ) (x : Vec d) :
    0 ≤ collarDefect Q ε x := Real.sqrt_nonneg _

theorem collarDefect_sq (Q : TriadicCube d) (ε : ℝ) (x : Vec d) :
    (collarDefect Q ε x) ^ (2 : ℕ) = 1 - (collarCutoff Q ε x) ^ (2 : ℕ) := by
  refine Real.sq_sqrt ?_
  have h0 := collarCutoff_nonneg Q ε x
  have h1 := collarCutoff_le_one Q ε x
  nlinarith only [h0, h1]

theorem collarDefect_le_one (Q : TriadicCube d) (ε : ℝ) (x : Vec d) :
    collarDefect Q ε x ≤ 1 := by
  have hsq := collarDefect_sq Q ε x
  have h0 := collarDefect_nonneg Q ε x
  nlinarith only [hsq, h0, sq_nonneg (collarCutoff Q ε x)]

theorem collarDefect_eq_zero_of_mem_cubeShrunkSet (Q : TriadicCube d)
    (hε0 : 0 < ε) (hεh : ε < 1 / 2) {x : Vec d} (hx : x ∈ cubeShrunkSet Q ε) :
    collarDefect Q ε x = 0 := by
  rw [collarDefect, collarCutoff_eq_one_of_mem_cubeShrunkSet Q hε0 hεh hx]
  norm_num

/-- **`‖1 − φ²‖_{L̲²(cu_M)} ≤ Cε^{1/2}`** in the square-root form
`‖(1 − φ²)^{1/2}‖_{L̲⁴(cu_M)}` that Hölder consumes, with the explicit
constant `(2dε)^{1/4}`. -/
theorem cubeLpENorm_four_collarDefect_le (Q : TriadicCube d) (hε0 : 0 < ε)
    (hεh : ε < 1 / 2) :
    Section2.Norms.cubeLpENorm Q 4 (collarDefect Q ε) ≤
      ENNReal.ofReal (2 * (d : ℝ) * ε) ^ ((1 : ℝ) / 4) := by
  classical
  set S : Set (Vec d) := cubeBoundaryLayer Q ε ∪ (cubeSet Q)ᶜ with hS
  have hSmeas : MeasurableSet S :=
    (measurableSet_cubeBoundaryLayer Q ε).union (measurableSet_cubeSet Q).compl
  have hpoint : ∀ x : Vec d,
      ‖collarDefect Q ε x‖ ≤ ‖S.indicator (fun _ : Vec d => (1 : ℝ)) x‖ := by
    intro x
    by_cases hx : x ∈ cubeShrunkSet Q ε
    · rw [collarDefect_eq_zero_of_mem_cubeShrunkSet Q hε0 hεh hx]
      simp
    · have hxS : x ∈ S := by
        by_cases hc : x ∈ cubeSet Q
        · exact Or.inl ⟨hc, hx⟩
        · exact Or.inr hc
      rw [Set.indicator_of_mem hxS]
      have h0 := collarDefect_nonneg Q ε x
      have h1 := collarDefect_le_one Q ε x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]
      simpa using h1
  have hcompl : normalizedCubeMeasure Q (cubeSet Q)ᶜ = 0 := by
    rw [normalizedCubeMeasure, cubeMeasure]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply' (measurableSet_cubeSet Q)]
    simp
  have hmeas : normalizedCubeMeasure Q S ≤ ENNReal.ofReal (2 * (d : ℝ) * ε) := by
    refine le_trans (measure_union_le _ _) ?_
    rw [hcompl, add_zero]
    exact normalizedCubeMeasure_cubeBoundaryLayer_le Q hε0.le hεh.le
  calc Section2.Norms.cubeLpENorm Q 4 (collarDefect Q ε)
      ≤ Section2.Norms.cubeLpENorm Q 4 (S.indicator (fun _ : Vec d => (1 : ℝ))) :=
        Section2.Norms.cubeLpENorm_mono_enorm
          (Real.continuous_sqrt.comp (continuous_const.sub
            ((collarCutoff_smooth Q hε0 hεh).continuous.pow 2))).aestronglyMeasurable hpoint
    _ = normalizedCubeMeasure Q S ^ ((1 : ℝ) / 4) := by
        rw [Section2.Norms.cubeLpENorm,
          eLpNorm_indicator_const hSmeas.nullMeasurableSet (by norm_num) (by norm_num)]
        simp
    _ ≤ ENNReal.ofReal (2 * (d : ℝ) * ε) ^ ((1 : ℝ) / 4) :=
        ENNReal.rpow_le_rpow hmeas (by norm_num)

/-! ## The splitting and Hölder on the boundary layer -/

private theorem eLpNorm_two_sq' {α : Type*} {E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] (ν : Measure α) (f : α → E) (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 2 ν ^ (2 : ℕ) = ∫⁻ a, ‖f a‖ₑ ^ (2 : ℕ) ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

theorem collarCutoff_continuous (Q : TriadicCube d) (hε0 : 0 < ε)
    (hεh : ε < 1 / 2) : Continuous (collarCutoff Q ε) :=
  (collarCutoff_smooth Q hε0 hεh).continuous

theorem collarDefect_continuous (Q : TriadicCube d) (hε0 : 0 < ε)
    (hεh : ε < 1 / 2) : Continuous (collarDefect Q ε) :=
  Real.continuous_sqrt.comp
    (continuous_const.sub ((collarCutoff_continuous Q hε0 hεh).pow 2))

private theorem hilbertify_smul (c : Vec d → ℝ) (F : Vec d → Vec d) (x : Vec d) :
    hilbertifyVecField (fun y => c y • F y) x = c x • hilbertifyVecField F x :=
  map_smul (HilbertVec.linearEquivVec d).symm (c x) (F x)

/-- **The splitting of the integral into the interior and the boundary layer**:
`φ² + (1 − φ²) = 1` splits `‖F‖_{L̲²(cu_M)}²` into the two pieces
that are then estimated separately. -/
theorem vecCubeLpENorm_two_sq_split (Q : TriadicCube d) (hε0 : 0 < ε)
    (hεh : ε < 1 / 2) {F : Vec d → Vec d}
    (hF : AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q)) :
    vecCubeLpENorm Q 2 F ^ (2 : ℕ) =
      vecCubeLpENorm Q 2 (fun x => collarCutoff Q ε x • F x) ^ (2 : ℕ) +
        vecCubeLpENorm Q 2 (fun x => collarDefect Q ε x • F x) ^ (2 : ℕ) := by
  have hFe : AEMeasurable (fun x => ‖hilbertifyVecField F x‖ₑ ^ (2 : ℕ))
      (normalizedCubeMeasure Q) := (hF.enorm.pow_const 2)
  have hcut : Measurable (fun x => ‖collarCutoff Q ε x‖ₑ ^ (2 : ℕ)) :=
    ((collarCutoff_continuous Q hε0 hεh).measurable.enorm).pow_const 2
  have hprod : AEMeasurable (fun x => ‖collarCutoff Q ε x‖ₑ ^ (2 : ℕ) *
      ‖hilbertifyVecField F x‖ₑ ^ (2 : ℕ)) (normalizedCubeMeasure Q) :=
    (hcut.aemeasurable).mul hFe
  have hone : ∀ x : Vec d,
      ‖collarCutoff Q ε x‖ₑ ^ (2 : ℕ) + ‖collarDefect Q ε x‖ₑ ^ (2 : ℕ) = 1 := by
    intro x
    have hz0 := collarCutoff_nonneg Q ε x
    have hg0 := collarDefect_nonneg Q ε x
    rw [show ‖collarCutoff Q ε x‖ₑ = ENNReal.ofReal (collarCutoff Q ε x) by
        rw [Real.enorm_eq_ofReal hz0],
      show ‖collarDefect Q ε x‖ₑ = ENNReal.ofReal (collarDefect Q ε x) by
        rw [Real.enorm_eq_ofReal hg0],
      ← ENNReal.ofReal_pow hz0, ← ENNReal.ofReal_pow hg0,
      ← ENNReal.ofReal_add (by positivity) (by positivity), collarDefect_sq]
    simp
  have e1 : ∫⁻ a, ‖hilbertifyVecField (fun x => collarCutoff Q ε x • F x) a‖ₑ ^ (2 : ℕ)
        ∂normalizedCubeMeasure Q =
      ∫⁻ a, ‖collarCutoff Q ε a‖ₑ ^ (2 : ℕ) * ‖hilbertifyVecField F a‖ₑ ^ (2 : ℕ)
        ∂normalizedCubeMeasure Q :=
    lintegral_congr (fun a => by rw [hilbertify_smul, enorm_smul, mul_pow])
  have e2 : ∫⁻ a, ‖hilbertifyVecField (fun x => collarDefect Q ε x • F x) a‖ₑ ^ (2 : ℕ)
        ∂normalizedCubeMeasure Q =
      ∫⁻ a, ‖collarDefect Q ε a‖ₑ ^ (2 : ℕ) * ‖hilbertifyVecField F a‖ₑ ^ (2 : ℕ)
        ∂normalizedCubeMeasure Q :=
    lintegral_congr (fun a => by rw [hilbertify_smul, enorm_smul, mul_pow])
  have hm1 : AEStronglyMeasurable
      (hilbertifyVecField (fun x => collarCutoff Q ε x • F x)) (normalizedCubeMeasure Q) := by
    rw [show hilbertifyVecField (fun x => collarCutoff Q ε x • F x) =
      fun x => collarCutoff Q ε x • hilbertifyVecField F x from funext (hilbertify_smul _ _)]
    exact (collarCutoff_continuous Q hε0 hεh).aestronglyMeasurable.smul hF
  have hm2 : AEStronglyMeasurable
      (hilbertifyVecField (fun x => collarDefect Q ε x • F x)) (normalizedCubeMeasure Q) := by
    rw [show hilbertifyVecField (fun x => collarDefect Q ε x • F x) =
      fun x => collarDefect Q ε x • hilbertifyVecField F x from funext (hilbertify_smul _ _)]
    exact (collarDefect_continuous Q hε0 hεh).aestronglyMeasurable.smul hF
  rw [vecCubeLpENorm, vecCubeLpENorm, vecCubeLpENorm, Section2.Norms.cubeLpENorm,
    Section2.Norms.cubeLpENorm, Section2.Norms.cubeLpENorm, eLpNorm_two_sq' _ _ hF,
    eLpNorm_two_sq' _ _ hm1, eLpNorm_two_sq' _ _ hm2, e1, e2, ← lintegral_add_left' hprod]
  exact lintegral_congr (fun x => by rw [← add_mul, hone x, one_mul])

private theorem cubeLpENorm_two_le_mul_four' {E : Type*} [NormedAddCommGroup E]
    {Q : TriadicCube d} {f : Vec d → E} {u w : Vec d → ℝ}
    (hu0 : ∀ x, 0 ≤ u x) (hw0 : ∀ x, 0 ≤ w x)
    (hum : AEStronglyMeasurable u (normalizedCubeMeasure Q))
    (hwm : AEStronglyMeasurable w (normalizedCubeMeasure Q))
    (hfm : AEStronglyMeasurable f (normalizedCubeMeasure Q))
    (hf : ∀ x, ‖f x‖ ≤ u x * w x) :
    Section2.Norms.cubeLpENorm Q 2 f ≤
      Section2.Norms.cubeLpENorm Q 4 u * Section2.Norms.cubeLpENorm Q 4 w := by
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
      ← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩
  have hmono : Section2.Norms.cubeLpENorm Q 2 f ≤
      Section2.Norms.cubeLpENorm Q 2 (fun x => u x * w x) := by
    refine Section2.Norms.cubeLpENorm_mono_enorm hfm (fun x => ?_)
    rw [show ‖u x * w x‖ = u x * w x from abs_of_nonneg (mul_nonneg (hu0 x) (hw0 x))]
    exact hf x
  refine le_trans hmono ?_
  rw [Section2.Norms.cubeLpENorm, show (fun x => u x * w x) = u • w from rfl]
  exact eLpNorm_smul_le_mul_eLpNorm hum hwm

private theorem cubeLpENorm_vecNorm_eq (Q : TriadicCube d) (q : ℝ≥0∞)
    (F : Vec d → Vec d)
    (hF : AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q)) :
    Section2.Norms.cubeLpENorm Q q (fun x => vecNorm (F x)) = vecCubeLpENorm Q q F := by
  refine le_antisymm (Section2.Norms.cubeLpENorm_mono_enorm hF.norm (fun x => ?_))
    (Section2.Norms.cubeLpENorm_mono_enorm hF (fun x => ?_))
  · exact le_of_eq (abs_of_nonneg (vecNorm_nonneg (F x)))
  · exact le_of_eq (abs_of_nonneg (vecNorm_nonneg (F x))).symm

/-- **Hölder on the boundary layer**: the boundary piece of the
splitting is bounded by `‖1 − φ²‖_{L̲²(cu_M)}^{1/2}` times `‖F‖_{L̲⁴(cu_M)}`,
written with the defect `(1 − φ²)^{1/2}` in `L̲⁴`. -/
theorem vecCubeLpENorm_two_collarDefect_smul_le (Q : TriadicCube d)
    (hε0 : 0 < ε) (hεh : ε < 1 / 2) {F : Vec d → Vec d}
    (hF : AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q)) :
    vecCubeLpENorm Q 2 (fun x => collarDefect Q ε x • F x) ≤
      Section2.Norms.cubeLpENorm Q 4 (collarDefect Q ε) * vecCubeLpENorm Q 4 F := by
  rw [← cubeLpENorm_vecNorm_eq Q 4 F hF, vecCubeLpENorm]
  refine cubeLpENorm_two_le_mul_four' (collarDefect_nonneg Q ε)
    (fun x => vecNorm_nonneg (F x))
    (collarDefect_continuous Q hε0 hεh).aestronglyMeasurable hF.norm
    ((collarDefect_continuous Q hε0 hεh).aestronglyMeasurable.smul hF |>.congr
      (Filter.Eventually.of_forall fun x => (hilbertify_smul _ _ x).symm))
    (fun x => ?_)
  rw [hilbertify_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (collarDefect_nonneg Q ε x)]
  exact le_of_eq rfl

/-! ## The balancing of the two terms -/

private theorem le_of_sq_le_sq' {x y : ℝ≥0∞} (h : x ^ (2 : ℕ) ≤ y ^ (2 : ℕ)) : x ≤ y := by
  have hx : x ^ (2 : ℕ) = x ^ ((2 : ℝ)) := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  have hy : y ^ (2 : ℕ) = y ^ ((2 : ℝ)) := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  rw [hx, hy] at h
  have hh := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
  rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    show (2 : ℝ) * ((1 : ℝ) / 2) = 1 by norm_num,
    ENNReal.rpow_one, ENNReal.rpow_one] at hh

/-- **The choice `ε ≃ (A/B)^{4/5}`** in real arithmetic: for
`0 < A < B` there is an admissible collar width at which the sum of the two
terms is at most `(4C_a + C_b)(A^{1/5}B^{4/5})²`. -/
private theorem exists_collar_width {a b Ca Cb : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a < b) (hCb : 0 ≤ Cb) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧
      Ca * (ε⁻¹) ^ (2 : ℕ) * a ^ (2 : ℕ) + Cb * ε ^ ((1 : ℝ) / 2) * b ^ (2 : ℕ) ≤
        (4 * Ca + Cb) * (a ^ ((1 : ℝ) / 5) * b ^ ((4 : ℝ) / 5)) ^ (2 : ℕ) := by
  set q : ℝ := a / b with hq
  have hq0 : 0 < q := div_pos ha hb
  have hq1 : q < 1 := (div_lt_one hb).2 hab
  have hqb : a = q * b := by rw [hq]; field_simp
  set r : ℝ := q ^ ((4 : ℝ) / 5) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hq0 _
  have hr1 : r < 1 := Real.rpow_lt_one hq0.le hq1 (by norm_num)
  refine ⟨r / 2, by positivity, by linarith only [hr1], ?_⟩
  have hb15 : b ^ ((1 : ℝ) / 5) * b ^ ((4 : ℝ) / 5) = b := by
    rw [← Real.rpow_add hb]
    norm_num
  have hG : (a ^ ((1 : ℝ) / 5) * b ^ ((4 : ℝ) / 5)) ^ (2 : ℕ) =
      q ^ ((2 : ℝ) / 5) * b ^ (2 : ℕ) := by
    rw [hqb, Real.mul_rpow hq0.le hb.le, mul_assoc, hb15, mul_pow]
    congr 1
    rw [← Real.rpow_natCast (q ^ ((1 : ℝ) / 5)) 2, ← Real.rpow_mul hq0.le]
    norm_num
  have hr2 : r ^ (2 : ℕ) = q ^ ((8 : ℝ) / 5) := by
    rw [hr, ← Real.rpow_natCast (q ^ ((4 : ℝ) / 5)) 2, ← Real.rpow_mul hq0.le]
    norm_num
  have hrhalf : r ^ ((1 : ℝ) / 2) = q ^ ((2 : ℝ) / 5) := by
    rw [hr, ← Real.rpow_mul hq0.le]
    norm_num
  have hq2 : q ^ (2 : ℕ) / q ^ ((8 : ℝ) / 5) = q ^ ((2 : ℝ) / 5) := by
    rw [← Real.rpow_natCast q 2, ← Real.rpow_sub hq0]
    norm_num
  have hinv : ((r / 2)⁻¹) ^ (2 : ℕ) = 4 / r ^ (2 : ℕ) := by
    rw [inv_pow, div_pow, inv_div]
    norm_num
  have hkey : ((r / 2)⁻¹) ^ (2 : ℕ) * a ^ (2 : ℕ) =
      4 * (q ^ ((2 : ℝ) / 5) * b ^ (2 : ℕ)) := by
    rw [hinv, hqb, mul_pow, hr2, ← hq2]
    ring
  have ht2 : (r / 2) ^ ((1 : ℝ) / 2) * b ^ (2 : ℕ) ≤
      q ^ ((2 : ℝ) / 5) * b ^ (2 : ℕ) := by
    have h1 : (r / 2) ^ ((1 : ℝ) / 2) ≤ r ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) (by linarith only [hr0]) (by norm_num)
    rw [← hrhalf]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  rw [hG]
  calc Ca * ((r / 2)⁻¹) ^ (2 : ℕ) * a ^ (2 : ℕ) +
        Cb * (r / 2) ^ ((1 : ℝ) / 2) * b ^ (2 : ℕ)
      = Ca * (((r / 2)⁻¹) ^ (2 : ℕ) * a ^ (2 : ℕ)) +
          Cb * ((r / 2) ^ ((1 : ℝ) / 2) * b ^ (2 : ℕ)) := by ring
    _ ≤ Ca * (4 * (q ^ ((2 : ℝ) / 5) * b ^ (2 : ℕ))) +
          Cb * (q ^ ((2 : ℝ) / 5) * b ^ (2 : ℕ)) := by
        rw [hkey]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left ht2 hCb)
    _ = (4 * Ca + Cb) * (q ^ ((2 : ℝ) / 5) * b ^ (2 : ℕ)) := by ring

/-- **The balancing of the two terms.** If a nonnegative extended real `X`
obeys `X² ≤ C_a ε⁻² A² + C_b ε^{1/2} B²` at every admissible collar width
`ε ∈ (0,1/2)`, and in addition `X ≤ B`, then `X ≤ C A^{1/5} B^{4/5}` with the
explicit constant `C = (4C_a + C_b)^{1/2} + 1`.

The hypothesis `X ≤ B` is the printed "if `A > B`, then the same conclusion
follows from `‖∇v‖_{L̲²} ≤ B`"; the hypothesis `A ≠ 0` is the
printed "the cases `A = 0` or `B = 0` are trivial" on the side that
the `ε`-family cannot see, the case `B = 0` being covered by `X ≤ B`. -/
theorem le_mul_rpow_fifth_mul_rpow_four_fifth {X A B : ℝ≥0∞} {Ca Cb : ℝ}
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hA : A ≠ 0) (hXB : X ≤ B)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      X ^ (2 : ℕ) ≤ ENNReal.ofReal (Ca * (ε⁻¹) ^ (2 : ℕ)) * A ^ (2 : ℕ) +
        ENNReal.ofReal (Cb * ε ^ ((1 : ℝ) / 2)) * B ^ (2 : ℕ)) :
    X ≤ ENNReal.ofReal ((4 * Ca + Cb) ^ ((1 : ℝ) / 2) + 1) *
      A ^ ((1 : ℝ) / 5) * B ^ ((4 : ℝ) / 5) := by
  have hsum0 : (0 : ℝ) ≤ 4 * Ca + Cb := by linarith only [hCa, hCb]
  have hroot0 : (0 : ℝ) ≤ (4 * Ca + Cb) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hsum0 _
  have hsq : ((4 * Ca + Cb) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = 4 * Ca + Cb := by
    rw [← Real.rpow_natCast ((4 * Ca + Cb) ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hsum0]
    norm_num
  have hK1 : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal ((4 * Ca + Cb) ^ ((1 : ℝ) / 2) + 1) := by
    rw [ENNReal.one_le_ofReal]
    linarith only [hroot0]
  have hKne : ENNReal.ofReal ((4 * Ca + Cb) ^ ((1 : ℝ) / 2) + 1) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hK1)
  rcases eq_or_ne B 0 with hB0 | hB0
  · rw [hB0, le_zero_iff] at hXB
    rw [hXB]
    exact zero_le
  have hA5 : A ^ ((1 : ℝ) / 5) ≠ 0 := by
    rw [Ne, ENNReal.rpow_eq_zero_iff]
    push Not
    exact ⟨fun hz => absurd hz hA, fun _ => by norm_num⟩
  have hB45 : B ^ ((4 : ℝ) / 5) ≠ 0 := by
    rw [Ne, ENNReal.rpow_eq_zero_iff]
    push Not
    exact ⟨fun hz => absurd hz hB0, fun _ => by norm_num⟩
  rcases eq_or_ne B ⊤ with hBtop | hBtop
  · rw [hBtop, ENNReal.top_rpow_of_pos (by norm_num),
      ENNReal.mul_top (mul_ne_zero hKne hA5)]
    exact le_top
  rcases eq_or_ne A ⊤ with hAtop | hAtop
  · rw [hAtop, ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top hKne,
      ENNReal.top_mul hB45]
    exact le_top
  rcases le_or_gt B A with hBA | hAB
  · refine le_trans hXB ?_
    calc B = B ^ ((1 : ℝ) / 5) * B ^ ((4 : ℝ) / 5) := by
            rw [← ENNReal.rpow_add _ _ hB0 hBtop]
            norm_num
      _ ≤ A ^ ((1 : ℝ) / 5) * B ^ ((4 : ℝ) / 5) :=
            mul_le_mul' (ENNReal.rpow_le_rpow hBA (by norm_num)) le_rfl
      _ ≤ ENNReal.ofReal ((4 * Ca + Cb) ^ ((1 : ℝ) / 2) + 1) *
            A ^ ((1 : ℝ) / 5) * B ^ ((4 : ℝ) / 5) := by
            refine mul_le_mul' ?_ le_rfl
            conv_lhs => rw [← one_mul (A ^ ((1 : ℝ) / 5))]
            exact mul_le_mul' hK1 le_rfl
  · have ha : 0 < A.toReal := ENNReal.toReal_pos hA hAtop
    have hb : 0 < B.toReal := ENNReal.toReal_pos hB0 hBtop
    have hab : A.toReal < B.toReal := (ENNReal.toReal_lt_toReal hAtop hBtop).2 hAB
    obtain ⟨ε, hε0, hεh, hreal⟩ := exists_collar_width (Ca := Ca) ha hb hab hCb
    have hXsq := h ε hε0 hεh
    have hAof : A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hAtop).symm
    have hBof : B = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hBtop).symm
    have hc1 : (0 : ℝ) ≤ Ca * (ε⁻¹) ^ (2 : ℕ) := by positivity
    have hc2 : (0 : ℝ) ≤ Cb * ε ^ ((1 : ℝ) / 2) :=
      mul_nonneg hCb (Real.rpow_nonneg hε0.le _)
    have hEq : ((4 * Ca + Cb) ^ ((1 : ℝ) / 2) *
          (A.toReal ^ ((1 : ℝ) / 5) * B.toReal ^ ((4 : ℝ) / 5))) ^ (2 : ℕ) =
        (4 * Ca + Cb) *
          (A.toReal ^ ((1 : ℝ) / 5) * B.toReal ^ ((4 : ℝ) / 5)) ^ (2 : ℕ) := by
      rw [mul_pow ((4 * Ca + Cb) ^ ((1 : ℝ) / 2))
        (A.toReal ^ ((1 : ℝ) / 5) * B.toReal ^ ((4 : ℝ) / 5)) 2, hsq]
    have hstep : X ^ (2 : ℕ) ≤
        ENNReal.ofReal (Ca * (ε⁻¹) ^ (2 : ℕ) * A.toReal ^ (2 : ℕ) +
          Cb * ε ^ ((1 : ℝ) / 2) * B.toReal ^ (2 : ℕ)) := by
      refine le_trans hXsq (le_of_eq ?_)
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul hc1, ENNReal.ofReal_mul hc2,
        ENNReal.ofReal_pow ha.le, ENNReal.ofReal_pow hb.le, ← hAof, ← hBof]
    have hstep2 : X ^ (2 : ℕ) ≤
        ENNReal.ofReal (((4 * Ca + Cb) ^ ((1 : ℝ) / 2) *
          (A.toReal ^ ((1 : ℝ) / 5) * B.toReal ^ ((4 : ℝ) / 5))) ^ (2 : ℕ)) := by
      refine le_trans hstep (ENNReal.ofReal_le_ofReal ?_)
      rw [hEq]
      exact hreal
    have hfin : X ≤ ENNReal.ofReal ((4 * Ca + Cb) ^ ((1 : ℝ) / 2) *
        (A.toReal ^ ((1 : ℝ) / 5) * B.toReal ^ ((4 : ℝ) / 5))) := by
      refine le_of_sq_le_sq' ?_
      rwa [ENNReal.ofReal_pow (by positivity)] at hstep2
    refine le_trans hfin ?_
    have hval : ENNReal.ofReal ((4 * Ca + Cb) ^ ((1 : ℝ) / 2) + 1) *
          A ^ ((1 : ℝ) / 5) * B ^ ((4 : ℝ) / 5) =
        ENNReal.ofReal (((4 * Ca + Cb) ^ ((1 : ℝ) / 2) + 1) *
          (A.toReal ^ ((1 : ℝ) / 5) * B.toReal ^ ((4 : ℝ) / 5))) := by
      conv_lhs => rw [hAof, hBof]
      rw [ENNReal.ofReal_rpow_of_pos ha, ENNReal.ofReal_rpow_of_pos hb,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        mul_assoc]
    rw [hval]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
    linarith only []

end

end ResponseFields
end Section3
end SuperdiffusionCLT
