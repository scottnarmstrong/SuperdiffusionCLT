/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.CoefficientLinftyMoments
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockE

/-!
# The depth-weighted window maximum and the `L∞` envelope

`IncrementMoreoverBlockD` bounds one `Finset.sup'`
over the joint window `centeredScaleWindow d h m` of scales and centres, through
the finite-maximum rule of the pinned library, at the amplitude `C(d) h`, the
printed `O_{Γ₂}(C h)` of `e.bounding.the.diff.of.k.union`.

The envelope family `X_m` of `e.Xm.deff` needs one random variable dominating
`h⁻¹` times that maximum **simultaneously for every** `h ∈ [1, m]`, at an
amplitude that does not grow with `m`; composing that bound with the
finite-maximum rule over the `m` values of `h` costs a factor `(3 log m)^{1/2}`.

This module removes the loss by weighting the window itself. The variable

`moreoverWindowMax m ω = max_{(n,Q)} (1 ⊔ (m-n))⁻¹ |(k_m)_{z_Q+cu_n} - (k_m)_{cu_m}|`

dominates `h⁻¹ centeredScaleCubeMax h m ω` for `1 ≤ h ≤ m`, because
`1 ⊔ (m-n) ≤ h` on the window of `h`; and its `Γ₂` amplitude is a
**dimension-only** constant, because the union bound is taken depth by depth:
the `(3^d)^j` cubes at depth `j` carry the weight `(1 ⊔ j)⁻¹` against the
one-cube amplitude `C(d) j^{1/2}`, so each depth contributes
`exp(-(A/C)^2 (1 ⊔ j) t^2)` and `3^{dj}` is beaten once `(A/C)^2 ≥ d log 3 + 2`.

The module also lands the `L∞` envelope `moreoverLinftyBound` of
`k - (k)_{cu_m}` on `cu_m`, with its `Γ₂` amplitude and growth bounds.

## Main definitions and results

* `moreoverWindowDepth`, `moreoverWindowWeight`, `moreoverWindowMax`,
  `moreoverWindowConst`: the depth-weighted maximum and its amplitude.
* `centeredScaleCubeMax_le_mul_moreoverWindowMax`,
  `inv_mul_centeredScaleCubeMax_le_moreoverWindowMax`: the domination, and
  `isBigOWith_gammaSigma_moreoverWindowMax`: the uniform `Γ₂` amplitude.
* `moreoverLinftyBound`, `moreoverLinftyAmp`,
  `isBigO_gammaSigma_moreoverLinftyBound`, `moreoverLinftyGrowthConst`,
  `inv_mul_moreoverLinftyAmp_le`, `moreoverLinftyAmp_le_mul`: the `L∞` envelope,
  its `Γ₂` tail and the two uniform growth bounds.
* `moreoverDepthWeight`, `pow_rpow_neg_mul_succ_le`: the depth series and the
  geometric weight of the depths below the cube.

## References
* `e.bounding.the.diff.of.k.union`, `e.Xm.deff`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Estimates
namespace Stream

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-! ## The depth-weighted window maximum -/

/-- The depth of the scale `n` in the window of `cu_m`, truncated at one. -/
def moreoverWindowDepth (m n : ℕ) : ℕ := max 1 (m - n)

theorem one_le_moreoverWindowDepth (m n : ℕ) : 1 ≤ moreoverWindowDepth m n :=
  le_max_left _ _

theorem moreoverWindowDepth_le {h m n : ℕ} (hh : 0 < h) (hwin : m - h ≤ n) :
    moreoverWindowDepth m n ≤ h := by
  refine max_le hh ?_
  omega

/-- The reciprocal depth weight of the scale `n` in the window of `cu_m`. -/
def moreoverWindowWeight (m n : ℕ) : ℝ := ((moreoverWindowDepth m n : ℕ) : ℝ)⁻¹

theorem moreoverWindowWeight_pos (m n : ℕ) : 0 < moreoverWindowWeight m n := by
  refine inv_pos.2 ?_
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_moreoverWindowDepth m n)

theorem inv_le_moreoverWindowWeight {h m n : ℕ} (hh : 0 < h) (hwin : m - h ≤ n) :
    ((h : ℝ))⁻¹ ≤ moreoverWindowWeight m n := by
  have hdepth : ((moreoverWindowDepth m n : ℕ) : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast moreoverWindowDepth_le hh hwin
  have hpos : (0 : ℝ) < ((moreoverWindowDepth m n : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_moreoverWindowDepth m n)
  simpa only [moreoverWindowWeight, one_div] using
    one_div_le_one_div_of_le hpos hdepth

/-- **The depth-weighted maximum over the full window of `cu_m`.** -/
def moreoverWindowMax (m : ℕ) (omega : ShellSeq d) : ℝ :=
  (centeredScaleWindow d m m).sup' (centeredScaleWindow_nonempty d m m)
    fun p => moreoverWindowWeight m p.1 *
      centeredCubeAverageEnvelope p.1 m (cubeCenter p.2) omega

theorem moreoverWindowMax_nonneg (m : ℕ) (omega : ShellSeq d) :
    0 ≤ moreoverWindowMax (d := d) m omega := by
  obtain ⟨p, hp⟩ := centeredScaleWindow_nonempty d m m
  refine le_trans ?_
    (Finset.le_sup'
      (fun q : ℕ × TriadicCube d =>
        moreoverWindowWeight m q.1 *
          centeredCubeAverageEnvelope q.1 m (cubeCenter q.2) omega) hp)
  exact mul_nonneg (moreoverWindowWeight_pos m p.1).le
    (centeredCubeAverageEnvelope_nonneg p.1 m (cubeCenter p.2) omega)

theorem measurable_moreoverWindowMax (m : ℕ) :
    Measurable (moreoverWindowMax (d := d) m) := by
  have hmeas := Finset.measurable_sup' (centeredScaleWindow_nonempty d m m)
    (f := fun p : ℕ × TriadicCube d => fun omega : ShellSeq d =>
      moreoverWindowWeight m p.1 *
        centeredCubeAverageEnvelope p.1 m (cubeCenter p.2) omega)
    (fun p _ =>
      (measurable_centeredCubeAverageEnvelope p.1 m (cubeCenter p.2)).const_mul _)
  have hfun : (centeredScaleWindow d m m).sup'
      (centeredScaleWindow_nonempty d m m)
      (fun p : ℕ × TriadicCube d => fun omega : ShellSeq d =>
        moreoverWindowWeight m p.1 *
          centeredCubeAverageEnvelope p.1 m (cubeCenter p.2) omega) =
      moreoverWindowMax (d := d) m := by
    funext omega
    exact Finset.sup'_apply _ _ omega
  rwa [hfun] at hmeas

/-- **The domination of the printed window maximum**: one variable dominates
`centeredScaleCubeMax h m ω` at the linear rate `h`, for every `1 ≤ h`. -/
theorem centeredScaleCubeMax_le_mul_moreoverWindowMax {h m : ℕ} (hh : 0 < h)
    (omega : ShellSeq d) :
    centeredScaleCubeMax (d := d) h m omega ≤
      (h : ℝ) * moreoverWindowMax (d := d) m omega := by
  have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  refine Finset.sup'_le _ _ ?_
  intro p hp
  obtain ⟨hn, hQ⟩ := mem_Icc_of_mem_centeredScaleWindow hp
  have hIcc := Finset.mem_Icc.1 hn
  have hmem : p ∈ centeredScaleWindow d m m := by
    refine mem_centeredScaleWindow (Finset.mem_Icc.2 ⟨?_, hIcc.2⟩) hQ
    omega
  have hsup :
      moreoverWindowWeight m p.1 *
          centeredCubeAverageEnvelope p.1 m (cubeCenter p.2) omega ≤
        moreoverWindowMax (d := d) m omega :=
    Finset.le_sup'
      (fun q : ℕ × TriadicCube d =>
        moreoverWindowWeight m q.1 *
          centeredCubeAverageEnvelope q.1 m (cubeCenter q.2) omega) hmem
  have hw : ((h : ℝ))⁻¹ ≤ moreoverWindowWeight m p.1 :=
    inv_le_moreoverWindowWeight hh hIcc.1
  have henv := centeredCubeAverageEnvelope_nonneg p.1 m (cubeCenter p.2) omega
  have hstep : ((h : ℝ))⁻¹ *
      centeredCubeAverageEnvelope p.1 m (cubeCenter p.2) omega ≤
        moreoverWindowMax (d := d) m omega :=
    le_trans (mul_le_mul_of_nonneg_right hw henv) hsup
  have hmul := mul_le_mul_of_nonneg_left hstep hhpos.le
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hhpos), one_mul] at hmul

/-- The reciprocal form of the domination, which is the hypothesis `hwindow`
of `coarseAverage_le_of_moreoverMinimalScale_le`. -/
theorem inv_mul_centeredScaleCubeMax_le_moreoverWindowMax {h m : ℕ} (hh : 0 < h)
    (omega : ShellSeq d) :
    ((h : ℝ))⁻¹ * centeredScaleCubeMax (d := d) h m omega ≤
      moreoverWindowMax (d := d) m omega := by
  have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hmain := centeredScaleCubeMax_le_mul_moreoverWindowMax (d := d) (m := m) hh omega
  calc ((h : ℝ))⁻¹ * centeredScaleCubeMax (d := d) h m omega
      ≤ ((h : ℝ))⁻¹ * ((h : ℝ) * moreoverWindowMax (d := d) m omega) :=
        mul_le_mul_of_nonneg_left hmain (inv_nonneg.2 hhpos.le)
    _ = moreoverWindowMax (d := d) m omega := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hhpos), one_mul]

/-! ## The per-element amplitude at the depth of the scale -/

/-- **The derivative-tail self-amplitude against the one-cube constant.**
Despite the name, what is stated here is the depth-0 step of the top-scale
branch of `isBigO_gammaSigma_centeredCubeAverageEnvelope_depth` — the
derivative-tail self-amplitude `(d : ℝ) * Real.sqrt d * streamDerivTailConst ≤
centeredCubeAverageConst d` — **not** the `coarseAverageDiffConst` comparison the
name suggests. -/
theorem coarseAverageDiffConst_le_centeredCubeAverageConst (d : ℕ) :
    (d : ℝ) * Real.sqrt d * streamDerivTailConst ≤ centeredCubeAverageConst d := by
  have hD : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt d * streamDerivTailConst := by
    have h0 : (0 : ℝ) ≤ streamDerivTailConst := by
      rw [streamDerivTailConst]; norm_num
    positivity
  have hC := coarseAverageDiffConst_nonneg d
  rw [centeredCubeAverageConst]
  nlinarith only [hD, hC]

/-- **The `Γ₂` amplitude of one member of the full window**, at the depth
weight of its scale: the one-cube amplitude `C(d) (m-n)^{1/2}` of
`IncrementMoreoverBlockC` for `n < m`, and the derivative-tail amplitude of
`IncrementMoreoverBlockD` at the top scale `n = m`. -/
theorem isBigO_gammaSigma_centeredCubeAverageEnvelope_depth
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {m : ℕ}
    {p : ℕ × TriadicCube d} (hp : p ∈ centeredScaleWindow d m m) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (centeredCubeAverageEnvelope p.1 m (cubeCenter p.2))
      (centeredCubeAverageConst d *
        Real.sqrt ((moreoverWindowDepth m p.1 : ℕ) : ℝ)) := by
  obtain ⟨hn, hQ⟩ := mem_Icc_of_mem_centeredScaleWindow hp
  have hnm : p.1 ≤ m := (Finset.mem_Icc.1 hn).2
  rcases lt_or_eq_of_le hnm with hlt | heq
  · have hdepth : moreoverWindowDepth m p.1 = m - p.1 := by
      rw [moreoverWindowDepth]
      omega
    rw [hdepth]
    exact isBigO_gammaSigma_centeredCubeAverageEnvelope hPrefix hJ1 hJ2 hJ3 hJ4 hlt
      (cubeCenter p.2)
  · have hQm : p.2 = originCube d (m : ℤ) := by
      rw [heq, largeCubeSubcubes_self] at hQ
      exact Finset.mem_singleton.1 hQ
    have hcentre : cubeCenter p.2 = (0 : Vec d) := by
      rw [hQm, cubeCenter_originCube_eq_zero]
    have hdepth : ((moreoverWindowDepth m p.1 : ℕ) : ℝ) = 1 := by
      have : moreoverWindowDepth m p.1 = 1 := by
        rw [moreoverWindowDepth]
        omega
      rw [this]; norm_num
    rw [hdepth, Real.sqrt_one, mul_one, hcentre, heq]
    exact (isBigO_gammaSigma_centeredCubeAverageEnvelope_self hJ3 m).mono_scale
      (coarseAverageDiffConst_le_centeredCubeAverageConst d)


/-! ## The depth decomposition of the window -/

private theorem pairwiseDisjoint_windowFibres (d m : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.Icc 0 m) : Set ℕ)
      fun n : ℕ => (largeCubeSubcubes d n m).image fun Q : TriadicCube d => (n, Q) := by
  intro a _ b _ hab
  refine Finset.disjoint_left.2 ?_
  intro q hqa hqb
  obtain ⟨Ra, _, hRa⟩ := Finset.mem_image.1 hqa
  obtain ⟨Rb, _, hRb⟩ := Finset.mem_image.1 hqb
  exact hab ((congrArg Prod.fst hRa).trans (congrArg Prod.fst hRb).symm)

/-- The sum of a scale-dependent quantity over the full window of `cu_m`
decomposes into the depths, each carrying its `(3^d)^(m-n)` centres. -/
theorem sum_window_eq_sum_depth (d m : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ centeredScaleWindow d m m, f p.1 =
      ∑ n ∈ Finset.Icc 0 m, (((3 ^ d) ^ (m - n) : ℕ) : ℝ) * f n := by
  classical
  have hwin : centeredScaleWindow d m m =
      (Finset.Icc 0 m).biUnion fun n : ℕ =>
        (largeCubeSubcubes d n m).image fun Q : TriadicCube d => (n, Q) := by
    rw [centeredScaleWindow, Nat.sub_self]
  rw [hwin, Finset.sum_biUnion (pairwiseDisjoint_windowFibres d m)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_image (fun x _ y _ hxy => (Prod.mk.injEq .. ▸ hxy).2)]
  show ∑ _Q ∈ largeCubeSubcubes d n m, f n = _
  rw [Finset.sum_const, largeCubeSubcubes_card, nsmul_eq_mul]


/-! ## The geometric depth sum -/

private theorem three_le_exp_two : (3 : ℝ) ≤ Real.exp 2 := by
  have := Real.add_one_le_exp (x := (2 : ℝ))
  linarith only [this]

private theorem rpow_two_eq_sq (x : ℝ) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
  rw [← Real.rpow_natCast x 2]
  norm_num

/-- **The geometric depth sum of the union bound.** The `(3^d)^j` centres of
depth `j` are beaten by the weight `exp(-κ t² (1 ⊔ j))` as soon as
`κ ≥ d log 3 + 2`, uniformly for `t ≥ 1`. -/
theorem sum_depth_exp_le (d : ℕ) {kappa t : ℝ}
    (hkappa : (d : ℝ) * Real.log 3 + 2 ≤ kappa) (ht : 1 ≤ t) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1),
        ((3 : ℝ) ^ d) ^ j * Real.exp (-(kappa * t ^ 2 * ((max 1 j : ℕ) : ℝ))) ≤
      Real.exp (-(t ^ 2)) := by
  have hlog3 : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 := by
    have : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  have ht2 : (1 : ℝ) ≤ t ^ 2 := by nlinarith only [ht]
  set r : ℝ := (3 : ℝ) ^ d * Real.exp (-(kappa * t ^ 2)) with hr
  have hpow3 : ((3 : ℝ) ^ d) = Real.exp ((d : ℝ) * Real.log 3) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 3)]
  have hrexp : r = Real.exp ((d : ℝ) * Real.log 3 - kappa * t ^ 2) := by
    rw [hr, hpow3, ← Real.exp_add]
    congr 1
  have hrle : r ≤ Real.exp (-(2 * t ^ 2)) := by
    rw [hrexp]
    refine Real.exp_le_exp.2 ?_
    nlinarith only [hlog3, ht2, hkappa]
  have hr0 : 0 ≤ r := by
    rw [hr]; positivity
  have hrsmall : r ≤ Real.exp (-2) := by
    refine hrle.trans (Real.exp_le_exp.2 ?_)
    nlinarith only [ht2]
  have hexp2 : Real.exp (-2 : ℝ) ≤ 1 / 3 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    simpa using three_le_exp_two
  have hr1 : r < 1 := lt_of_le_of_lt (hrsmall.trans hexp2) (by norm_num)
  have hsplit : ∑ j ∈ Finset.range (m + 1),
      ((3 : ℝ) ^ d) ^ j * Real.exp (-(kappa * t ^ 2 * ((max 1 j : ℕ) : ℝ))) =
      (∑ j ∈ Finset.range m,
        ((3 : ℝ) ^ d) ^ (j + 1) *
          Real.exp (-(kappa * t ^ 2 * ((max 1 (j + 1) : ℕ) : ℝ)))) +
        Real.exp (-(kappa * t ^ 2)) := by
    rw [Finset.sum_range_succ']
    norm_num
  have hterm : ∀ j ∈ Finset.range m,
      ((3 : ℝ) ^ d) ^ (j + 1) *
        Real.exp (-(kappa * t ^ 2 * ((max 1 (j + 1) : ℕ) : ℝ))) = r ^ (j + 1) := by
    intro j _
    have hmax : ((max 1 (j + 1) : ℕ) : ℝ) = ((j : ℝ) + 1) := by
      have hj : max 1 (j + 1) = j + 1 := by omega
      rw [hj]; push_cast; ring
    rw [hmax, hr, mul_pow, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring_nf
  rw [hsplit, Finset.sum_congr rfl hterm]
  have hgeom : ∑ j ∈ Finset.range m, r ^ (j + 1) ≤ r * (1 - r)⁻¹ := by
    have hfac : ∑ j ∈ Finset.range m, r ^ (j + 1) =
        r * ∑ j ∈ Finset.range m, r ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hfac]
    refine mul_le_mul_of_nonneg_left ?_ hr0
    have hs : Summable (fun i : ℕ => r ^ i) := summable_geometric_of_lt_one hr0 hr1
    have h1 : ∑ i ∈ Finset.range m, r ^ i ≤ ∑' i : ℕ, r ^ i :=
      hs.sum_le_tsum _ (fun i _ => pow_nonneg hr0 i)
    rwa [tsum_geometric_of_lt_one hr0 hr1] at h1
  have hinv : (1 - r)⁻¹ ≤ 3 / 2 := by
    have h23 : (2 : ℝ) / 3 ≤ 1 - r := by
      have := hrsmall.trans hexp2
      linarith only [this]
    rw [inv_le_comm₀ (by linarith only [h23]) (by norm_num)]
    linarith only [h23]
  have hkey : r * (1 - r)⁻¹ + Real.exp (-(kappa * t ^ 2)) ≤
      (5 / 2) * Real.exp (-(2 * t ^ 2)) := by
    have hinv0 : (0 : ℝ) ≤ (1 - r)⁻¹ := by
      have hpos : (0 : ℝ) < 1 - r := by linarith only [hr1]
      exact (inv_pos.2 hpos).le
    have h1 : r * (1 - r)⁻¹ ≤ Real.exp (-(2 * t ^ 2)) * (3 / 2) :=
      mul_le_mul hrle hinv hinv0 (Real.exp_pos _).le
    have h2 : Real.exp (-(kappa * t ^ 2)) ≤ Real.exp (-(2 * t ^ 2)) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith only [hkappa, hlog3, ht2]
    linarith only [h1, h2]
  refine le_trans (by linarith only [hgeom]) (le_trans hkey ?_)
  have hexp1 : (5 : ℝ) / 2 ≤ Real.exp (t ^ 2) := by
    have h1 : Real.exp 1 ≤ Real.exp (t ^ 2) := Real.exp_le_exp.2 ht2
    have h2 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    linarith only [h1, h2]
  have hfac : Real.exp (-(2 * t ^ 2)) =
      Real.exp (-(t ^ 2)) * (Real.exp (t ^ 2))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]
    ring_nf
  rw [hfac]
  have hle : (5 / 2 : ℝ) * (Real.exp (t ^ 2))⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ (Real.exp_pos _), one_mul]
    exact hexp1
  calc (5 / 2 : ℝ) * (Real.exp (-(t ^ 2)) * (Real.exp (t ^ 2))⁻¹)
      = Real.exp (-(t ^ 2)) * ((5 / 2 : ℝ) * (Real.exp (t ^ 2))⁻¹) := by ring
    _ ≤ Real.exp (-(t ^ 2)) * 1 :=
        mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
    _ = Real.exp (-(t ^ 2)) := by ring


/-! ## The uniform amplitude of the depth-weighted maximum -/

/-- The dimension-only `Γ₂` amplitude of the depth-weighted window maximum: the
one-cube constant of `IncrementMoreoverBlockC` inflated by the square root of
`d log 3 + 2`, the exponent at which the `3^{dj}` centres of depth `j` are
beaten. -/
def moreoverWindowConst (d : ℕ) : ℝ :=
  centeredCubeAverageConst d * Real.sqrt ((d : ℝ) * Real.log 3 + 2)

/-- **The depth-weighted window maximum has a dimension-only `Γ₂`
amplitude**, uniformly in the cube scale `m`. -/
theorem isBigOWith_gammaSigma_moreoverWindowMax
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m : ℕ) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (moreoverWindowMax (d := d) m) (moreoverWindowConst d) := by
  classical
  intro t ht
  have hlog3 : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 := by
    have : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  set kappa : ℝ := (d : ℝ) * Real.log 3 + 2 with hkappadef
  have hkappa2 : (2 : ℝ) ≤ kappa := by rw [hkappadef]; linarith only [hlog3]
  have hkappa0 : (0 : ℝ) ≤ kappa := by linarith only [hkappa2]
  have hsqk : (1 : ℝ) ≤ Real.sqrt kappa := by
    have h1 : Real.sqrt 1 ≤ Real.sqrt kappa :=
      Real.sqrt_le_sqrt (by linarith only [hkappa2])
    simpa using h1
  have hsqk2 : Real.sqrt kappa * Real.sqrt kappa = kappa :=
    Real.mul_self_sqrt hkappa0
  have hdepth1 : ∀ n : ℕ, (1 : ℝ) ≤ ((moreoverWindowDepth m n : ℕ) : ℝ) := by
    intro n
    exact_mod_cast one_le_moreoverWindowDepth m n
  have hdeppos : ∀ n : ℕ, (0 : ℝ) < ((moreoverWindowDepth m n : ℕ) : ℝ) :=
    fun n => lt_of_lt_of_le zero_lt_one (hdepth1 n)
  have hsqdepth : ∀ n : ℕ,
      (1 : ℝ) ≤ Real.sqrt ((moreoverWindowDepth m n : ℕ) : ℝ) := by
    intro n
    have h1 : Real.sqrt 1 ≤ Real.sqrt ((moreoverWindowDepth m n : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (hdepth1 n)
    simpa using h1
  have hsqsq : ∀ n : ℕ,
      Real.sqrt ((moreoverWindowDepth m n : ℕ) : ℝ) *
          Real.sqrt ((moreoverWindowDepth m n : ℕ) : ℝ) =
        ((moreoverWindowDepth m n : ℕ) : ℝ) :=
    fun n => Real.mul_self_sqrt (hdeppos n).le
  have hscale1 : ∀ n : ℕ,
      (1 : ℝ) ≤ Real.sqrt kappa * t * Real.sqrt ((moreoverWindowDepth m n : ℕ) : ℝ) := by
    intro n
    have h1 : (1 : ℝ) ≤ Real.sqrt kappa * t :=
      one_le_mul_of_one_le_of_one_le hsqk ht
    have h2 : (1 : ℝ) * 1 ≤ (Real.sqrt kappa * t) *
        Real.sqrt ((moreoverWindowDepth m n : ℕ) : ℝ) :=
      mul_le_mul h1 (hsqdepth n) zero_le_one (by linarith only [h1])
    linarith only [h2]
  have hsub : IndependentSums.upperTailEvent (moreoverWindowMax (d := d) m)
      (moreoverWindowConst d * t) ⊆
      ⋃ p ∈ centeredScaleWindow d m m,
        IndependentSums.upperTailEvent
          (centeredCubeAverageEnvelope p.1 m (cubeCenter p.2))
          (centeredCubeAverageConst d *
              Real.sqrt ((moreoverWindowDepth m p.1 : ℕ) : ℝ) *
            (Real.sqrt kappa * t *
              Real.sqrt ((moreoverWindowDepth m p.1 : ℕ) : ℝ))) := by
    intro omega homega
    have hlt : moreoverWindowConst d * t < moreoverWindowMax (d := d) m omega := homega
    rw [moreoverWindowMax, Finset.lt_sup'_iff] at hlt
    obtain ⟨p, hp, hp2⟩ := hlt
    refine Set.mem_biUnion hp ?_
    show centeredCubeAverageConst d *
        Real.sqrt ((moreoverWindowDepth m p.1 : ℕ) : ℝ) *
          (Real.sqrt kappa * t *
            Real.sqrt ((moreoverWindowDepth m p.1 : ℕ) : ℝ)) <
      centeredCubeAverageEnvelope p.1 m (cubeCenter p.2) omega
    have hprod : centeredCubeAverageConst d *
        Real.sqrt ((moreoverWindowDepth m p.1 : ℕ) : ℝ) *
          (Real.sqrt kappa * t *
            Real.sqrt ((moreoverWindowDepth m p.1 : ℕ) : ℝ)) =
        (moreoverWindowConst d * t) * ((moreoverWindowDepth m p.1 : ℕ) : ℝ) := by
      rw [moreoverWindowConst, ← hkappadef]
      linear_combination (centeredCubeAverageConst d * Real.sqrt kappa * t) *
        (hsqsq p.1)
    rw [hprod]
    have hmul := mul_lt_mul_of_pos_right hp2 (hdeppos p.1)
    have hw : ((moreoverWindowDepth m p.1 : ℕ) : ℝ) * moreoverWindowWeight m p.1 = 1 := by
      rw [moreoverWindowWeight]
      exact mul_inv_cancel₀ (ne_of_gt (hdeppos p.1))
    calc moreoverWindowConst d * t * ((moreoverWindowDepth m p.1 : ℕ) : ℝ)
        < moreoverWindowWeight m p.1 *
            centeredCubeAverageEnvelope p.1 m (cubeCenter p.2) omega *
            ((moreoverWindowDepth m p.1 : ℕ) : ℝ) := hmul
      _ = centeredCubeAverageEnvelope p.1 m (cubeCenter p.2) omega := by
          linear_combination
            (centeredCubeAverageEnvelope p.1 m (cubeCenter p.2) omega) * hw
  have hper : ∀ p ∈ centeredScaleWindow d m m,
      P.toMeasure.real (IndependentSums.upperTailEvent
          (centeredCubeAverageEnvelope p.1 m (cubeCenter p.2))
          (centeredCubeAverageConst d *
              Real.sqrt ((moreoverWindowDepth m p.1 : ℕ) : ℝ) *
            (Real.sqrt kappa * t *
              Real.sqrt ((moreoverWindowDepth m p.1 : ℕ) : ℝ)))) ≤
        Real.exp (-(kappa * t ^ 2 * ((moreoverWindowDepth m p.1 : ℕ) : ℝ))) := by
    intro p hp
    have hbig := isBigO_gammaSigma_centeredCubeAverageEnvelope_depth hPrefix hJ1
      hJ2 hJ3 hJ4 hp
    have hnn : ∀ omega : ShellSeq d,
        0 ≤ centeredCubeAverageEnvelope p.1 m (cubeCenter p.2) omega :=
      fun omega => centeredCubeAverageEnvelope_nonneg p.1 m (cubeCenter p.2) omega
    have hwith :=
      (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
        (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2) hnn).2 hbig
    have hval := hwith (hscale1 p.1)
    rw [IndependentSums.gammaSigma_inv, rpow_two_eq_sq] at hval
    have hsq : (Real.sqrt kappa * t *
        Real.sqrt ((moreoverWindowDepth m p.1 : ℕ) : ℝ)) ^ (2 : ℕ) =
        kappa * t ^ 2 * ((moreoverWindowDepth m p.1 : ℕ) : ℝ) := by
      have h1 := hsqsq p.1
      linear_combination (t ^ 2 *
          (Real.sqrt ((moreoverWindowDepth m p.1 : ℕ) : ℝ) *
            Real.sqrt ((moreoverWindowDepth m p.1 : ℕ) : ℝ))) * hsqk2 +
        (t ^ 2 * kappa) * h1
    rw [hsq] at hval
    exact hval
  have hstep : P.toMeasure.real
      (IndependentSums.upperTailEvent (moreoverWindowMax (d := d) m)
        (moreoverWindowConst d * t)) ≤
      ∑ p ∈ centeredScaleWindow d m m,
        Real.exp (-(kappa * t ^ 2 * ((moreoverWindowDepth m p.1 : ℕ) : ℝ))) := by
    refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    exact Finset.sum_le_sum hper
  refine le_trans hstep ?_
  rw [IndependentSums.gammaSigma_inv, rpow_two_eq_sq]
  have hsumeq : ∑ p ∈ centeredScaleWindow d m m,
      Real.exp (-(kappa * t ^ 2 * ((moreoverWindowDepth m p.1 : ℕ) : ℝ))) =
      ∑ n ∈ Finset.Icc 0 m,
        (((3 ^ d) ^ (m - n) : ℕ) : ℝ) *
          Real.exp (-(kappa * t ^ 2 * ((max 1 (m - n) : ℕ) : ℝ))) :=
    sum_window_eq_sum_depth d m
      (fun n => Real.exp (-(kappa * t ^ 2 * ((moreoverWindowDepth m n : ℕ) : ℝ))))
  rw [hsumeq]
  have hIcc : Finset.Icc 0 m = Finset.range (m + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and,
      Nat.lt_succ_iff]
  rw [hIcc]
  have hrewrite : ∑ n ∈ Finset.range (m + 1),
      (((3 ^ d) ^ (m - n) : ℕ) : ℝ) *
        Real.exp (-(kappa * t ^ 2 * ((max 1 (m - n) : ℕ) : ℝ))) =
      ∑ n ∈ Finset.range (m + 1),
        (fun j : ℕ => ((3 : ℝ) ^ d) ^ j *
          Real.exp (-(kappa * t ^ 2 * ((max 1 j : ℕ) : ℝ)))) (m - n) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    have hcast : (((3 ^ d) ^ (m - n) : ℕ) : ℝ) = ((3 : ℝ) ^ d) ^ (m - n) := by
      push_cast
      ring
    rw [hcast]
  rw [hrewrite]
  have hreflect := Finset.sum_range_reflect
    (fun j : ℕ => ((3 : ℝ) ^ d) ^ j *
      Real.exp (-(kappa * t ^ 2 * ((max 1 j : ℕ) : ℝ)))) (m + 1)
  simp only [Nat.add_sub_cancel] at hreflect
  rw [hreflect]
  exact sum_depth_exp_le d (le_of_eq hkappadef.symm) ht m

/-! ## The `L∞` envelope of the limiting centered field -/

/-- The `L∞(cu_m)` envelope of `k - (k)_{cu_m}`: the sup envelope of the infrared
cutoff `k_m` on `cu_m`, doubled through its own average at the dimension cost of
`matrixOperatorNorm_volumeAverageMat_le`, plus the mean-value tail of the shells above `m`. -/
def moreoverLinftyBound (m : ℕ) (omega : ShellSeq d) : ℝ :=
  (1 + (d : ℝ)) * streamCutoffLargeCubeSupBound m m omega +
    (d : ℝ) * Real.sqrt d * shellDerivTailGauge m omega

theorem moreoverLinftyBound_nonneg (m : ℕ) (omega : ShellSeq d) :
    0 ≤ moreoverLinftyBound (d := d) m omega := by
  have h1 : (0 : ℝ) ≤ streamCutoffLargeCubeSupBound m m omega :=
    streamCutoffLargeCubeSupBound_nonneg m m omega
  have h2 : (0 : ℝ) ≤ shellDerivTailGauge m omega := shellDerivTailGauge_nonneg m omega
  rw [moreoverLinftyBound]
  positivity

theorem measurable_moreoverLinftyBound (m : ℕ) :
    Measurable (moreoverLinftyBound (d := d) m) :=
  ((measurable_streamCutoffLargeCubeSupBound m m).const_mul _).add
    ((measurable_shellDerivTailGauge m).const_mul _)

/-- The centered infrared cutoff on `cu_m` is at most `(1+d)` times its sup envelope. -/
theorem matrixOperatorNorm_centeredStreamCutoff_le (omega : ShellSeq d) (m : ℕ)
    {x : Vec d} (hx : x ∈ cubeSet (originCube d (m : ℤ))) :
    matrixOperatorNorm
        (centeredStreamCutoff omega m (cubeSet (originCube d (m : ℤ))) x) ≤
      (1 + (d : ℝ)) * streamCutoffLargeCubeSupBound m m omega := by
  have hS : (0 : ℝ) ≤ streamCutoffLargeCubeSupBound m m omega :=
    streamCutoffLargeCubeSupBound_nonneg m m omega
  have hpoint : matrixOperatorNorm (streamCutoff omega m x) ≤
      streamCutoffLargeCubeSupBound m m omega :=
    matrixOperatorNorm_streamCutoff_le_streamCutoffLargeCubeSupBound omega hx
  have havg : matrixOperatorNorm
      (volumeAverageMat (cubeSet (originCube d (m : ℤ)))
        (streamCutoff omega m)) ≤ (d : ℝ) * streamCutoffLargeCubeSupBound m m omega := by
    refine matrixOperatorNorm_volumeAverageMat_le
      (volume_cubeSet_lt_top (originCube d (m : ℤ))).ne hS ?_
    intro y hy i k
    refine le_trans (abs_entry_le_matrixOperatorNorm _ i k) ?_
    exact matrixOperatorNorm_streamCutoff_le_streamCutoffLargeCubeSupBound omega hy
  rw [centeredStreamCutoff_apply]
  have hsub : matrixOperatorNorm (streamCutoff omega m x -
      volumeAverageMat (cubeSet (originCube d (m : ℤ))) (streamCutoff omega m)) ≤
      matrixOperatorNorm (streamCutoff omega m x) +
        matrixOperatorNorm
          (volumeAverageMat (cubeSet (originCube d (m : ℤ))) (streamCutoff omega m)) := by
    simpa only [matrixOperatorNorm_eq_l2_opNorm] using
      norm_sub_le (streamCutoff omega m x)
        (volumeAverageMat (cubeSet (originCube d (m : ℤ))) (streamCutoff omega m))
  refine hsub.trans ?_
  linarith only [hpoint, havg]

/-- **The `L∞` term of `e.Xm.deff` is dominated by the explicit envelope.** -/
theorem cubeLpENorm_infty_centeredStreamField_le_moreoverLinftyBound
    (omega : ShellSeq d) (m : ℕ)
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k)) :
    Norms.cubeLpENorm (originCube d (m : ℤ)) ∞
        (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ≤
      ENNReal.ofReal (moreoverLinftyBound (d := d) m omega) :=
  cubeLpENorm_infty_centeredStreamField_le omega m hsum
    (fun _ hx => matrixOperatorNorm_centeredStreamCutoff_le omega m hx)

/-- **The pointwise entrywise envelope of the limiting centered field on `cu_m`.** -/
theorem abs_entry_centeredStreamField_le_moreoverLinftyBound (omega : ShellSeq d)
    (m : ℕ)
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k))
    {y : Vec d} (hy : y ∈ cubeSet (originCube d (m : ℤ))) (i k : Fin d) :
    |centeredStreamField omega (cubeSet (originCube d (m : ℤ))) y i k| ≤
      moreoverLinftyBound (d := d) m omega := by
  refine le_trans (abs_entry_le_matrixOperatorNorm _ i k) ?_
  have hcut := matrixOperatorNorm_centeredStreamCutoff_le omega m hy
  have htail := matrixOperatorNorm_centeredStreamField_sub_centeredStreamCutoff_le
    (U := cubeSet (originCube d (m : ℤ))) (isBounded_cubeSet _) (convex_cubeSet _)
    (volume_cubeSet_ne_zero _) (R := (3 : ℝ) ^ m)
    (fun _ ha _ hb => dist_le_of_mem_cubeSet_originCube ha hb) omega
    (summable_shellDerivLinftyNorm_cubeSet_originCube hsum) m hy
  have hcoeff : (d : ℝ) *
      (Real.sqrt d * (3 : ℝ) ^ m *
        shellDerivTailOn (cubeSet (originCube d (m : ℤ))) omega m) =
      (d : ℝ) * Real.sqrt d * shellDerivTailGauge m omega := by
    rw [← mul_shellDerivTailOn_cubeSet_originCube m omega]
    ring
  rw [hcoeff] at htail
  have hsplit : matrixOperatorNorm
      (centeredStreamField omega (cubeSet (originCube d (m : ℤ))) y) ≤
      matrixOperatorNorm
          (centeredStreamField omega (cubeSet (originCube d (m : ℤ))) y -
            centeredStreamCutoff omega m (cubeSet (originCube d (m : ℤ))) y) +
        matrixOperatorNorm
          (centeredStreamCutoff omega m (cubeSet (originCube d (m : ℤ))) y) := by
    have := norm_add_le
      (centeredStreamField omega (cubeSet (originCube d (m : ℤ))) y -
        centeredStreamCutoff omega m (cubeSet (originCube d (m : ℤ))) y)
      (centeredStreamCutoff omega m (cubeSet (originCube d (m : ℤ))) y)
    simpa only [matrixOperatorNorm_eq_l2_opNorm, sub_add_cancel] using this
  rw [moreoverLinftyBound]
  linarith only [hsplit, hcut, htail]


/-! ## The `Γ₂` amplitude of the `L∞` envelope -/

theorem gammaTriangleConst_two_nonneg :
    (0 : ℝ) ≤ IndependentSums.gammaTriangleConst 2 := by
  have h : (0 : ℝ) ≤ IndependentSums.gammaGrowthConst 2 :=
    le_trans (by norm_num) (IndependentSums.two_le_gammaGrowthConst 2)
  rw [IndependentSums.gammaTriangleConst]
  have h12 : (0 : ℝ) ≤ IndependentSums.gammaGrowthConst 2 ^ (12 : ℝ) :=
    Real.rpow_nonneg h _
  linarith only [h12]

theorem streamCutoffLinftyGammaTwoAmplitude_nonneg {C : ℝ} (hC : 0 ≤ C)
    (d L m : ℕ) : 0 ≤ streamCutoffLinftyGammaTwoAmplitude C d L m := by
  have hG := gammaTriangleConst_two_nonneg
  have hV : (0 : ℝ) ≤ shellValueLargeCubeConst d :=
    le_trans zero_le_one (one_le_shellValueLargeCubeConst d)
  rw [streamCutoffLinftyGammaTwoAmplitude]
  have h1 : (0 : ℝ) ≤ shellValueLargeCubeConst d * Real.sqrt (1 + ((m : ℕ) : ℝ)) :=
    mul_nonneg hV (Real.sqrt_nonneg _)
  have h2 : (0 : ℝ) ≤ C * (Real.sqrt ((L : ℕ) : ℝ) * Real.sqrt ((m : ℕ) : ℝ)) :=
    mul_nonneg hC (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have h3 : (0 : ℝ) ≤ shellValueLargeCubeConst d * Real.sqrt (1 + ((m : ℕ) : ℝ)) +
      C * (Real.sqrt ((L : ℕ) : ℝ) * Real.sqrt ((m : ℕ) : ℝ)) := by
    linarith only [h1, h2]
  exact mul_nonneg hG h3

/-- The `Γ₂` amplitude of the `L∞` envelope of the limiting centered field on
`cu_m`: the two amplitudes above joined by the finite triangle inequality. -/
def moreoverLinftyAmp (d m : ℕ) : ℝ :=
  16384 * ((1 + (d : ℝ)) *
      streamCutoffLinftyGammaTwoAmplitude (largeCubeLinftyConst d) d m m + 1 +
    ((d : ℝ) * Real.sqrt d * streamDerivTailConst + 1))

/-- **The `Γ₂` tail of the `L∞` envelope.** -/
theorem isBigO_gammaSigma_moreoverLinftyBound (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (m : ℕ) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (moreoverLinftyBound (d := d) m) (moreoverLinftyAmp d m) := by
  classical
  have hCl : (0 : ℝ) ≤ largeCubeLinftyConst d := (largeCubeLinftyConst_pos hPrefix).le
  have hS : (0 : ℝ) ≤
      streamCutoffLinftyGammaTwoAmplitude (largeCubeLinftyConst d) d m m :=
    streamCutoffLinftyGammaTwoAmplitude_nonneg hCl d m m
  have hD : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt d * streamDerivTailConst := by
    have h0 : (0 : ℝ) ≤ streamDerivTailConst := by
      rw [streamDerivTailConst]; norm_num
    positivity
  set X : Fin 2 → ShellSeq d → ℝ :=
    ![fun omega => (1 + (d : ℝ)) * streamCutoffLargeCubeSupBound m m omega,
      fun omega => (d : ℝ) * Real.sqrt d * shellDerivTailGauge m omega] with hX
  set a : Fin 2 → ℝ :=
    ![(1 + (d : ℝ)) *
        streamCutoffLinftyGammaTwoAmplitude (largeCubeLinftyConst d) d m m + 1,
      (d : ℝ) * Real.sqrt d * streamDerivTailConst + 1] with ha
  have hapos : ∀ i, 0 < a i := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · simp only [ha, Matrix.cons_val_zero]
      have : (0 : ℝ) ≤ (1 + (d : ℝ)) *
          streamCutoffLinftyGammaTwoAmplitude (largeCubeLinftyConst d) d m m := by
        have h1 : (0 : ℝ) ≤ 1 + (d : ℝ) := by positivity
        exact mul_nonneg h1 hS
      linarith only [this]
    · simp only [ha, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith only [hD]
  have hXmeas : ∀ i, Measurable (X i) := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · simp only [hX, Matrix.cons_val_zero]
      exact (measurable_streamCutoffLargeCubeSupBound m m).const_mul _
    · simp only [hX, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact (measurable_shellDerivTailGauge m).const_mul _
  have hXbig : ∀ i, IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma 2) (X i) (a i) := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · simp only [hX, ha, Matrix.cons_val_zero]
      have hbase := isBigO_gammaSigma_streamCutoffLargeCubeSupBound
        hPrefix hJ2 hJ3 hJ4 (le_refl m)
      have hscaled := hbase.const_mul (c := 1 + (d : ℝ)) (by positivity)
      exact hscaled.mono_scale (by linarith only [])
    · simp only [hX, ha, Matrix.cons_val_one, Matrix.cons_val_zero]
      have hbase := isBigO_gammaSigma_shellDerivTailGauge (P := P) hJ3 m
      have hscaled := hbase.const_mul (c := (d : ℝ) * Real.sqrt d) (by positivity)
      exact hscaled.mono_scale (by linarith only [])
  have hsum := SuperdiffusionCLT.Probability.isBigO_gammaSigma_finSum_of_one_le
    (mu := P.toMeasure) (N := 2) (X := X) (a := a) (sigma := 2)
    (by norm_num) (by norm_num) hapos hXbig hXmeas
  have hfun : (fun omega : ShellSeq d => ∑ i, X i omega) =
      moreoverLinftyBound (d := d) m := by
    funext omega
    rw [Fin.sum_univ_two]
    simp only [hX, Matrix.cons_val_zero, Matrix.cons_val_one, moreoverLinftyBound]
  rw [hfun] at hsum
  refine hsum.mono_scale (le_of_eq ?_)
  rw [moreoverLinftyAmp, Fin.sum_univ_two]
  simp only [ha, Matrix.cons_val_zero, Matrix.cons_val_one]


/-- The geometric weight of the depths below the cube beats the linear `L∞` growth. -/
theorem pow_rpow_neg_mul_succ_le {s : ℝ} (hs : 0 < s) (m : ℕ) :
    ((3 : ℝ) ^ (-s)) ^ (m + 1) * (1 + (m : ℝ)) ≤ (s * Real.log 3)⁻¹ := by
  have hlog : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hsl : (0 : ℝ) < s * Real.log 3 := by positivity
  set x : ℝ := ((m : ℝ) + 1) * (s * Real.log 3) with hxdef
  have hx0 : 0 < x := by
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [hxdef]
    exact mul_pos hm hsl
  have hpow : ((3 : ℝ) ^ (-s)) ^ (m + 1) = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_nat_mul,
      hxdef]
    congr 1
    push_cast
    ring
  have hxe : x ≤ Real.exp x := by
    have := Real.add_one_le_exp (x := x)
    linarith only [this]
  have hkey : x * Real.exp (-x) ≤ 1 := by
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos x), one_mul]
    exact hxe
  have hfac : (1 : ℝ) + (m : ℝ) = x * (s * Real.log 3)⁻¹ := by
    rw [hxdef, mul_assoc, mul_inv_cancel₀ (ne_of_gt hsl), mul_one]
    ring
  rw [hpow, hfac]
  calc Real.exp (-x) * (x * (s * Real.log 3)⁻¹)
      = (x * Real.exp (-x)) * (s * Real.log 3)⁻¹ := by ring
    _ ≤ 1 * (s * Real.log 3)⁻¹ :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = (s * Real.log 3)⁻¹ := by ring


/-! ## The depth series weight -/

theorem rpow_neg_lt_one {s : ℝ} (hs : 0 < s) : (3 : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])

theorem rpow_neg_nonneg (s : ℝ) : (0 : ℝ) ≤ (3 : ℝ) ^ (-s) :=
  Real.rpow_nonneg (by norm_num) _

/-- The value of the printed depth series `∑_j 3^{-sj}(1 ⊔ j)`, bounded through `1 ⊔ j ≤ 1 + j`. -/
def moreoverDepthWeight (s : ℝ) : ℝ :=
  (1 - (3 : ℝ) ^ (-s))⁻¹ + (3 : ℝ) ^ (-s) / (1 - (3 : ℝ) ^ (-s)) ^ 2

theorem moreoverDepthWeight_nonneg {s : ℝ} (hs : 0 < s) :
    0 ≤ moreoverDepthWeight s := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-s) := rpow_neg_nonneg s
  have hr1 : (3 : ℝ) ^ (-s) < 1 := rpow_neg_lt_one hs
  have hpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-s) := by linarith only [hr1]
  rw [moreoverDepthWeight]
  positivity


end

end Stream
end Estimates
end Section2
end SuperdiffusionCLT
