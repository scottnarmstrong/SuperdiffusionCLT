/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3BlupFinal
public import SuperdiffusionCLT.Section3.HighContrast.RangeDependenceRestriction

/-!
# Transporting the `Γ_{1/3}` tail to every triadic cube

The obligation `_hBlup` of the term-3 final assembly carries conjunct 2 — the `Γ_{1/3}` tail
of the remainder witness `blupRemainderZrem` at the amplitude
`Czero ν^{-3} L' 3^{-(ℓ-n)}` — with the binder `∀ z : TriadicCube d`, every
triadic cube of every integer scale.  The tail
`blupRemainderZrem_gammaSigma_one_third`
(`Section3/Terms/BlupRemainderAssembly.lean`) proves it only on the cubes of
the localization scale `n`, and the chain reads only those (the `hDscale`
hypothesis of the chain).

## The transport is true, and the only extra input is J1

The obstruction is *not* the quantifier over finer cubes: the stream carrier
`translatedStreamNormSq ell L e · z` is the squared tested increment
`|(k_ℓ − k_{L'})_{z + cu_m} e|²`, and the origin-cube tail
`isBigO_gammaSigma_translatedStreamNormSq_originCube`
(`Section3/Terms/RHSTerm3InputsE.lean`) is stated at every *nonnegative* scale
`nn` with `nn ≤ ℓ < L`: below the shell scale the cube average is dominated by
the shell `L∞` norm at unit amplitude
(`isBigO_gammaSigma_shellSpatialAverage_entry_of_le_scale`, J3 + the
prefix), and the independent-sum concentration over the shells `(ℓ, L]`
(J2 + the negation half of J4) gives the `√(L − ℓ)` gain.

Above `ℓ` — a cube coarser than the shells it averages — the average is
*smaller*, not larger: the colour decomposition
`isBigO_gammaSigma_shellSpatialAverage_entry`
(the spatial-average tail estimate for the stream increment) bounds every shell average
uniformly by `1 + spatialAverageColorConst d`, with the *decay*
`3^{-(d/2)(m-k)}` for a cube of scale `m` coarser than the shell `k`.  Summing
the same independent-sum concentration over the shells at that uniform
amplitude transports the tail to *every* triadic cube, at the cost of replacing
the stream constant `streamTailConst d` by
`streamTailConstAll d = (streamIncrementNormConst d · (1 + spatialAverageColorConst d))²`.

So the transport is **true on the whole quantifier**, and the exact extra input
it needs — beyond the prefix, J2, J3, J4 consumed by the scale-`n` tail —
is **J1** (the restriction-lane range dependence), whose coarser-cube
branch is `isBigO_gammaSigma_shellSpatialAverage_entry`.  The term-3 final assembly already
carries J1 in the form `ShellLawJ1Restriction`; the bridge
`Section3.HighContrast.shellLawJ1_of_shellLawJ1Restriction` turns it into the `ShellLawJ1`
the colour decomposition consumes.  The only price is the *constant*: the tail
holds at `blupRemainderConstAll d` in place of `blupRemainderConst d`, so the
slot is filled as soon as `blupRemainderConstAll d ≤ Czero`.  No cube of
any scale is excluded, and no scale threshold is needed; in particular the
statement is not false above `ℓ`.

## Main results

* `isBigO_gammaSigma_matrixOperatorNorm_streamIncrementAverage_all`: the
  printed stream-increment display at every scale, with the colour constant.
* `isBigO_gammaSigma_translatedStreamNormSq_originCube_all` and
  `isBigO_gammaSigma_translatedStreamNormSq` — the squared display at every
  origin cube and its transport to every triadic cube.
* `isBigO_gammaSigma_one_blupQuadCarrier_all`: the `Γ₁` tail of the quadratic
  carrier at every cube.
* `blupRemainderZrem_gammaSigma_one_third_all`: conjunct 2 on every cube.
* `blup_tail_allCubes`: the `hTailAll` residual, with `Czero` dominating the transported
  constant.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal
open scoped BigOperators Matrix.Norms.Elementwise

variable {d : ℕ}

noncomputable section

/-! ## The coarser-cube constants -/

/-- The stream-increment operator-norm constant at *every* cube scale: the
`streamIncrementNormConst d` enlarged by the colour constant
`1 + spatialAverageColorConst d` of the coarse-cube shell average. -/
def streamIncrementNormConstAll (d : ℕ) : ℝ :=
  streamIncrementNormConst d * (1 + spatialAverageColorConst d)

theorem streamIncrementNormConstAll_pos (hd : 0 < d) :
    0 < streamIncrementNormConstAll d := by
  rw [streamIncrementNormConstAll]
  exact mul_pos (streamIncrementNormConst_pos hd)
    (by linarith only [spatialAverageColorConst_nonneg d])

/-- The squared stream constant at every cube scale. -/
def streamTailConstAll (d : ℕ) : ℝ := streamIncrementNormConstAll d ^ 2

theorem streamTailConstAll_pos (hd : 0 < d) : 0 < streamTailConstAll d := by
  rw [streamTailConstAll]
  exact pow_pos (streamIncrementNormConstAll_pos hd) 2

/-- The quadratic-carrier tail constant at every cube scale: the `Γ₁` triangle
constant times the sum of the two Young amounts' tail constants, with the
all-scale stream constant. -/
def blupQuadTailConstAll (d : ℕ) : ℝ :=
  gammaTriangleConst 1 *
    (2 * (1 + 2 * cutoffEnvelopeConst d) + 2 * streamTailConstAll d)

theorem blupQuadTailConstAll_pos (hd : 0 < d) : 0 < blupQuadTailConstAll d := by
  unfold blupQuadTailConstAll
  refine mul_pos IndependentSums.gammaTriangleConst_pos ?_
  refine add_pos (mul_pos (by norm_num) ?_) (mul_pos (by norm_num) ?_)
  · exact add_pos (by norm_num)
      (mul_pos (by norm_num) (cutoffEnvelopeConst_pos d))
  · exact streamTailConstAll_pos hd

/-- The printed `Γ_{1/3}` remainder constant at every cube scale. -/
def blupRemainderConstAll (d : ℕ) : ℝ :=
  orliczProductConst 1 1 * dEstimateConst d * blupQuadTailConstAll d

/-- A power of `3` with a nonpositive exponent is at most `1`. -/
private theorem three_rpow_of_nonpos_le_one {E : ℝ} (hE : E ≤ 0) :
    (3 : ℝ) ^ E ≤ 1 := by
  rw [← Real.rpow_zero (3 : ℝ)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hE

/-- The exponent `-(d/2) · X` is nonpositive for `0 ≤ d`, `0 ≤ X`. -/
private theorem neg_half_mul_nonpos {d : ℕ} {X : ℝ} (hX : 0 ≤ X) :
    -(↑d / 2) * X ≤ 0 := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by linarith only [hd0])) hX

/-! ## The coarse average of a finite stream increment at any integer scale -/

/-- **`(k_L − k_ℓ)_{cu_m} = ∑_{k=ℓ+1}^L (j_k)_{cu_m}` at every integer cube
scale**, the `ℤ`-indexed form of `volumeAverageMat_originCube_finiteShellIncrement_eq_sum`
consumed by the all-scale transport. -/
theorem volumeAverageMat_originCube_finiteShellIncrement_eq_sum_int
    (omega : ShellSeq d) (nn : ℤ) (l L : ℕ) :
    volumeAverageMat (cubeSet (originCube d nn))
        (fun y => finiteShellIncrement omega l L y) =
      ∑ k ∈ Finset.Ioc l L, ShellField.shellSpatialAverage nn 0 (omega k) := by
  rw [volumeAverageMat_cubeSet_eq_openCubeSet,
    volumeAverageMat_finiteShellIncrement_eq_sum
      (Section2.Carriers.isBounded_openCubeSet_originCube nn) omega l L]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ShellField.shellSpatialAverage_eq_volumeAverageMat_translateSet_openCubeSet,
    translateSet_zero]
  rfl

/-! ## The printed display at every cube scale -/

/-- **The printed stream-increment display at every cube scale.**  Unlike
`isBigO_gammaSigma_matrixOperatorNorm_streamIncrementAverage`, the cube scale
`nn` is an arbitrary integer: no comparison `nn ≤ ℓ` is required.  The entry of
each shell average is bounded at the uniform amplitude
`1 + spatialAverageColorConst d` of the colour decomposition
(`isBigO_gammaSigma_shellSpatialAverage_entry`), which carries the decay
`3^{-(d/2)(nn-k)}` for a cube coarser than the shell; the shells are centred by
J4, independent by J2, and concentrated by the independent-sum inequality of the
CoarseGraining library, and the `d²` matrix entries are summed by the generalized
triangle inequality. -/
theorem isBigO_gammaSigma_matrixOperatorNorm_streamIncrementAverage_all
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {nn : ℤ} {l L : ℕ} (hlL : l < L) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d =>
        Book.Ch02.matrixOperatorNorm
          (volumeAverageMat (cubeSet (originCube d nn))
            (fun y => finiteShellIncrement omega l L y)))
      (streamIncrementNormConstAll d * Real.sqrt ((L - l : ℕ) : ℝ)) := by
  classical
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hcol : 0 ≤ spatialAverageColorConst d := spatialAverageColorConst_nonneg d
  set Y : Fin d → Fin d → ℕ → ShellSeq d → ℝ := fun i j k omega =>
    ShellField.shellSpatialAverage nn 0 (omega k) i j with hYdef
  have hYmeas : ∀ i j : Fin d, ∀ k : ℕ, Measurable (Y i j k) := by
    intro i j k
    have hrow : Measurable fun A : Mat d => A i := measurable_pi_apply i
    have hcolp : Measurable fun v : Fin d → ℝ => v j := measurable_pi_apply j
    exact ((hcolp.comp hrow).comp
      (ShellField.measurable_shellSpatialAverage nn 0)).comp
      (ShellField.measurable_shellCoordinate k)
  have hYbig : ∀ i j : Fin d, ∀ k ∈ Finset.Ioc l L,
      IsBigO P.toMeasure (gammaSigma 2) (Y i j k) (1 + spatialAverageColorConst d) := by
    intro i j k _hk
    have hbase := isBigO_gammaSigma_shellSpatialAverage_entry hPrefix hJ1 hJ3 hJ4 k nn 0 i j
    refine hbase.mono_scale ?_
    have hX : (0 : ℤ) ≤ max (nn - (k : ℤ)) 0 := le_max_right _ _
    have hXr : (0 : ℝ) ≤ (((max (nn - (k : ℤ)) 0 : ℤ)) : ℝ) := by exact_mod_cast hX
    have h3le : (3 : ℝ) ^ (-((d : ℝ) / 2) * (((max (nn - (k : ℤ)) 0 : ℤ)) : ℝ)) ≤ 1 :=
      three_rpow_of_nonpos_le_one (neg_half_mul_nonpos (d := d) hXr)
    have hcol1 : (0 : ℝ) ≤ 1 + spatialAverageColorConst d := by linarith only [hcol]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h3le hcol1
  have hYmean : ∀ i j : Fin d, ∀ k : ℕ,
      ∫ omega : ShellSeq d, Y i j k omega ∂P.toMeasure = 0 := by
    intro i j k
    refine integral_eq_zero_of_odd_under_negateSequence hJ4 (hYmeas i j k) ?_
    intro omega
    simp only [hYdef, ShellField.negateSequence_apply,
      ShellField.shellSpatialAverage_negate, Matrix.neg_apply]
  have hYindep : ∀ i j : Fin d,
      ProbabilityTheory.iIndepFun (fun (k : ℕ) (omega : ShellSeq d) => Y i j k omega)
        P.toMeasure := by
    intro i j
    have hmeasField : Measurable fun jf : ShellField d =>
        ShellField.shellSpatialAverage nn 0 jf i j := by
      have hrow : Measurable fun A : Mat d => A i := measurable_pi_apply i
      have hcolp : Measurable fun v : Fin d → ℝ => v j := measurable_pi_apply j
      exact (hcolp.comp hrow).comp (ShellField.measurable_shellSpatialAverage nn 0)
    exact hJ2.independent.comp
      (fun _ : ℕ => fun jf : ShellField d =>
        ShellField.shellSpatialAverage nn 0 jf i j)
      (fun _ => hmeasField)
  have hcard : ((Finset.Ioc l L).card : ℝ) = ((L - l : ℕ) : ℝ) := by
    rw [Nat.card_Ioc]
  have hsqrtpos : (0 : ℝ) < Real.sqrt ((L - l : ℕ) : ℝ) := by
    have hgap : (0 : ℝ) < ((L - l : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hlL
    exact Real.sqrt_pos.2 hgap
  have hKpos : (0 : ℝ) < 1 + spatialAverageColorConst d := by linarith only [hcol]
  have hAmp : (0 : ℝ) < Book.Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt ((L - l : ℕ) : ℝ) * (1 + spatialAverageColorConst d) := by
    have h2 : (0 : ℝ) < Book.Ch04.gammaSigmaIndependentSumConst 2 :=
      SuperdiffusionCLT.Probability.gammaSigmaIndependentSumConst_two_pos
    exact mul_pos (mul_pos h2 hsqrtpos) hKpos
  have hentry : ∀ q : Fin d × Fin d,
      IsBigO P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d => |∑ k ∈ Finset.Ioc l L, Y q.1 q.2 k omega|)
        (Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((L - l : ℕ) : ℝ) * (1 + spatialAverageColorConst d)) := by
    intro q
    have h := Book.Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
      (μ := P.toMeasure) (X := Y q.1 q.2) (s := Finset.Ioc l L) (σ := 2)
      (K := 1 + spatialAverageColorConst d)
      (hYindep q.1 q.2) (hYmeas q.1 q.2) (Finset.nonempty_Ioc.mpr hlL)
      (by norm_num) (by norm_num) hKpos
      (fun k hk => hYbig q.1 q.2 k hk) (fun k _ => hYmean q.1 q.2 k)
    rw [hcard] at h
    show IsBigOWith _ _ _ _
    simp only [abs_abs]
    exact h
  have hmeasSum : ∀ q : Fin d × Fin d,
      Measurable fun omega : ShellSeq d =>
        |∑ k ∈ Finset.Ioc l L, Y q.1 q.2 k omega| := by
    intro q
    have hsum : Measurable fun omega : ShellSeq d =>
        ∑ k ∈ Finset.Ioc l L, Y q.1 q.2 k omega :=
      Finset.measurable_sum (Finset.Ioc l L) fun k _ => hYmeas q.1 q.2 k
    simpa only [Real.norm_eq_abs] using hsum.norm
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty :=
    ⟨(⟨0, hd⟩, ⟨0, hd⟩), Finset.mem_univ _⟩
  have htriangle := isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := P.toMeasure) (Finset.univ : Finset (Fin d × Fin d))
    (X := fun q (omega : ShellSeq d) => |∑ k ∈ Finset.Ioc l L, Y q.1 q.2 k omega|)
    (a := fun _ : Fin d × Fin d =>
      Book.Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt ((L - l : ℕ) : ℝ) *
        (1 + spatialAverageColorConst d))
    (σ := 2) (by norm_num) hne (fun _ _ => hAmp) (fun q _ => hentry q)
    (fun q _ => hmeasSum q)
  have hamp : gammaTriangleConst 2 *
      ∑ _q : Fin d × Fin d,
        (Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((L - l : ℕ) : ℝ) * (1 + spatialAverageColorConst d)) =
      streamIncrementNormConstAll d * Real.sqrt ((L - l : ℕ) : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, streamIncrementNormConstAll, streamIncrementNormConst]
    push_cast
    ring
  rw [hamp] at htriangle
  refine htriangle.of_abs_le fun omega => ?_
  have hnonneg : (0 : ℝ) ≤ ∑ q : Fin d × Fin d,
      |∑ k ∈ Finset.Ioc l L, Y q.1 q.2 k omega| :=
    Finset.sum_nonneg fun q _ => abs_nonneg _
  rw [abs_of_nonneg (Book.Ch02.matrixOperatorNorm_nonneg _), abs_of_nonneg hnonneg]
  have hentryEq : ∑ i : Fin d, ∑ j : Fin d,
      |volumeAverageMat (cubeSet (originCube d nn))
        (fun y => finiteShellIncrement omega l L y) i j| =
      ∑ q : Fin d × Fin d, |∑ k ∈ Finset.Ioc l L, Y q.1 q.2 k omega| := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [volumeAverageMat_originCube_finiteShellIncrement_eq_sum_int]
    simp only [Matrix.sum_apply, hYdef]
  rw [← hentryEq]
  exact (Book.Ch02.matrixOperatorNorm_le_matrixFrobeniusNorm _).trans
    (Book.Ch02.matrixFrobeniusNorm_le_sum_abs_entries _)

/-! ## The squared stream display at every origin cube -/

/-- **`hStreamTailCentred` at every integer cube scale.**  For a unit direction
`e` and scales `ℓ < L`, the squared tested increment on `cu_m` is
`O_{Γ₁}(streamTailConstAll d · (L − ℓ))` for *every* integer scale `m`, with no
comparison to `ℓ`: the all-scale operator-norm display of
`isBigO_gammaSigma_matrixOperatorNorm_streamIncrementAverage_all` is squared by
the printed power rule, and `|Me|² ≤ |M|²` closes the passage to the tested
vector. -/
theorem isBigO_gammaSigma_translatedStreamNormSq_originCube_all
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {nn : ℤ} {l L : ℕ} (hlL : l < L)
    {e : Vec d} (he : vecNormSq e = 1) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d =>
        translatedStreamNormSq l L e omega (originCube d nn))
      (streamTailConstAll d * ((L - l : ℕ) : ℝ)) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  set N : ShellSeq d → ℝ := fun omega =>
    Book.Ch02.matrixOperatorNorm
      (volumeAverageMat (cubeSet (originCube d nn))
        (fun y => finiteShellIncrement omega l L y)) with hNdef
  set A : ℝ := streamIncrementNormConstAll d * Real.sqrt ((L - l : ℕ) : ℝ) with hAdef
  have hNnonneg : ∀ omega : ShellSeq d, 0 ≤ N omega := fun omega =>
    Book.Ch02.matrixOperatorNorm_nonneg _
  have hsqrtpos : (0 : ℝ) < Real.sqrt ((L - l : ℕ) : ℝ) := by
    have hgap : (0 : ℝ) < ((L - l : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hlL
    exact Real.sqrt_pos.2 hgap
  have hApos : 0 < A := by
    rw [hAdef]
    exact mul_pos (streamIncrementNormConstAll_pos hd) hsqrtpos
  have hN : IsBigO P.toMeasure (gammaSigma 2) N A :=
    isBigO_gammaSigma_matrixOperatorNorm_streamIncrementAverage_all hPrefix hJ1 hJ2 hJ3 hJ4 hlL
  have hsq := SuperdiffusionCLT.Probability.isBigO_gammaSigma_rpow_fwd
    (mu := P.toMeasure) (X := N) (K := A) (σ := 2) (p := 2)
    (by norm_num) hApos.le hNnonneg hN
  have hsigma : (2 : ℝ) / 2 = 1 := by norm_num
  rw [hsigma] at hsq
  have hrp : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
    intro x
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [← hcast, Real.rpow_natCast]
  have hfun : (fun omega : ShellSeq d => N omega ^ (2 : ℝ)) =
      fun omega : ShellSeq d => N omega ^ (2 : ℕ) := by
    funext omega
    exact hrp (N omega)
  have hamp : A ^ (2 : ℝ) = streamTailConstAll d * ((L - l : ℕ) : ℝ) := by
    have hnn : (0 : ℝ) ≤ ((L - l : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hrp, hAdef, mul_pow, Real.sq_sqrt hnn, streamTailConstAll]
  rw [hfun, hamp] at hsq
  refine hsq.of_abs_le fun omega => ?_
  have hle := translatedStreamNormSq_le_sq_matrixOperatorNorm he l L omega
    (originCube d nn)
  rw [abs_of_nonneg (translatedStreamNormSq_nonneg l L e omega _),
    abs_of_nonneg (pow_nonneg (hNnonneg omega) 2)]
  exact hle

/-! ## The quadratic carrier at every cube -/

/-- **The `Γ₁` tail of the quadratic carrier at every triadic cube.**  The
envelope amount is scale-free; the stream amount is transported by
`isBigO_gammaSigma_translatedStreamNormSq` from the all-scale origin display
`isBigO_gammaSigma_translatedStreamNormSq_originCube_all`, so no condition on
`z.scale` remains. -/
theorem isBigO_gammaSigma_one_blupQuadCarrier_all [NeZero d]
    {P : ProbabilityMeasure (ShellSeq d)} {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (ell L : ℕ) (hlL : ell < L) (hell : 1 ≤ ell) (e : Vec d) (he : vecNormSq e = 1)
    (z : TriadicCube d) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => blupQuadCarrier nu ell L e omega z)
      (blupQuadTailConstAll d * nu⁻¹ * (L : ℝ)) := by
  have hdn : 0 < d := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hPrefix.dimension
  have hE := isBigO_gammaSigma_translatedBlockNorm_envelope hnu hPrefix hJ2 hJ3 hJ4 ell z
  have hE2 := hE.const_mul (show (0 : ℝ) ≤ 2 by norm_num)
  have hEm : Measurable fun omega : ShellSeq d =>
      2 * translatedBlockNorm nu ell omega z :=
    Measurable.const_mul (measurable_translatedBlockNorm hnu ell z) 2
  have hS0 := isBigO_gammaSigma_translatedStreamNormSq_originCube_all (P := P) hPrefix
    hJ1 hJ2 hJ3 hJ4 (nn := z.scale) (l := ell) (L := L) hlL he
  have hS := isBigO_gammaSigma_translatedStreamNormSq (P := P) hPrefix hJ2
    (l := ell) (L := L) e (Q := z) hS0
  have hS2 := hS.const_mul
    (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (inv_nonneg.mpr hnu.le))
  have hSm : Measurable fun omega : ShellSeq d =>
      (2 * nu⁻¹) * translatedStreamNormSq ell L e omega z :=
    Measurable.const_mul (measurable_translatedStreamNormSq ell L e z) (2 * nu⁻¹)
  have hE2amp : 0 < 2 * envelopeUpperScalar d nu ell := by
    refine mul_pos (by norm_num) (envelopeUpperScalar_pos hnu d ell)
  have hS2amp : 0 < (2 * nu⁻¹) * (streamTailConstAll d * ((L - ell : ℕ) : ℝ)) := by
    have hcast : (0 : ℝ) < ((L - ell : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.sub_pos_of_lt hlL)
    exact mul_pos (mul_pos (by norm_num) (inv_pos.mpr hnu))
      (mul_pos (streamTailConstAll_pos hdn) hcast)
  have htri := isBigO_gammaSigma_add_of_isBigO (sigma := 1)
    (show (0 : ℝ) < 1 by norm_num) hE2amp hS2amp hE2 hS2 hEm hSm
  have hinv0 : 0 ≤ nu⁻¹ := inv_nonneg.mpr hnu.le
  have hEL : (ell : ℝ) ≤ (L : ℝ) := Nat.cast_le.mpr hlL.le
  have hsub : ((L - ell : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.sub_le L ell
  have hterm1 : 2 * envelopeUpperScalar d nu ell ≤
      2 * ((1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * (L : ℝ)) := by
    refine mul_le_mul_of_nonneg_left (le_trans
      (envelopeUpperScalar_le_nuInv_mul hnu hnu1 d hell) ?_)
      (by norm_num)
    exact mul_le_mul_of_nonneg_left hEL
      (mul_nonneg (add_nonneg (by norm_num : (0 : ℝ) ≤ 1)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((cutoffEnvelopeConst_pos d).le)))
        (inv_nonneg.mpr hnu.le))
  have hterm2 : (2 * nu⁻¹) * (streamTailConstAll d * ((L - ell : ℕ) : ℝ)) ≤
      2 * streamTailConstAll d * nu⁻¹ * (L : ℝ) := by
    calc (2 * nu⁻¹) * (streamTailConstAll d * ((L - ell : ℕ) : ℝ))
        ≤ (2 * nu⁻¹) * (streamTailConstAll d * (L : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsub (streamTailConstAll_pos hdn).le)
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hinv0)
      _ = 2 * streamTailConstAll d * nu⁻¹ * (L : ℝ) := by ring
  refine htri.mono_scale ?_
  have hS : 2 * envelopeUpperScalar d nu ell +
      (2 * nu⁻¹) * (streamTailConstAll d * ((L - ell : ℕ) : ℝ)) ≤
      (2 * (1 + 2 * cutoffEnvelopeConst d) + 2 * streamTailConstAll d) * nu⁻¹ *
        (L : ℝ) := by
    calc 2 * envelopeUpperScalar d nu ell +
          (2 * nu⁻¹) * (streamTailConstAll d * ((L - ell : ℕ) : ℝ))
        ≤ 2 * ((1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * (L : ℝ)) +
          2 * streamTailConstAll d * nu⁻¹ * (L : ℝ) := by linarith only [hterm1, hterm2]
      _ = (2 * (1 + 2 * cutoffEnvelopeConst d) + 2 * streamTailConstAll d) * nu⁻¹ *
          (L : ℝ) := by ring
  unfold blupQuadTailConstAll
  exact le_trans (mul_le_mul_of_nonneg_left hS
    (IndependentSums.gammaTriangleConst_pos (σ := (1 : ℝ))).le) (le_of_eq (by ring))

/-! ## The `Γ_{1/3}` remainder at every cube -/

/-- **The printed `Γ_{1/3}` remainder of `e.blupbounds.remainder` on every
triadic cube.**  The localization scalar keeps its scale-`nn` tail (it is read
through the translation `triadicCubeShift z` and does not see `z.scale`), and
the quadratic carrier uses the all-scale tail
`isBigO_gammaSigma_one_blupQuadCarrier_all`.  The amplitude is exactly the
printed one, at the transported constant `blupRemainderConstAll d`. -/
theorem blupRemainderZrem_gammaSigma_one_third_all [NeZero d]
    {P : ProbabilityMeasure (ShellSeq d)} {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (nn ell L : ℕ) (hnl : nn < ell) (hlL : ell < L)
    (e : Vec d) (he : vecNormSq e = 1) (z : TriadicCube d) :
    IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3))
      (fun omega : ShellSeq d => blupRemainderZrem nu nn ell L e omega z)
      (blupRemainderConstAll d * nu ^ (-(3 : ℝ)) * (L : ℝ) *
        (3 : ℝ) ^ (-(((ell - nn : ℕ) : ℝ)))) := by
  obtain ⟨Z, hZm, hZbig, hZdom⟩ :=
    dEstimate_gammaSigma_one_translatedCube hnu hnu1 hPrefix hJ3 nn ell L hnl hlL
      (triadicCubeShift z)
  have hq2 : 0 ≤ nu ^ (-(2 : ℝ)) := by
    have hrw : nu ^ (-(2 : ℝ)) = nu⁻¹ * nu⁻¹ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_two, pow_two, mul_inv]
    rw [hrw]
    positivity
  have hDnn : ∀ omega : ShellSeq d,
      0 ≤ translatedIncrementD nu (triadicCubeShift z) nn ell L omega := by
    intro omega
    unfold translatedIncrementD
    have hosc := translatedIncrementOscBound_nonneg (triadicCubeShift z) nn ell L omega
    exact add_nonneg (mul_nonneg (inv_nonneg.mpr hnu.le) hosc)
      (mul_nonneg hq2 (sq_nonneg _))
  have hZnn : ∀ omega : ShellSeq d, 0 ≤ Z omega := fun omega =>
    le_trans (hDnn omega) (hZdom omega)
  have hDfun := hZbig.of_abs_le fun omega => by
    rw [abs_of_nonneg (hDnn omega), abs_of_nonneg (hZnn omega)]
    exact hZdom omega
  have hQ := isBigO_gammaSigma_one_blupQuadCarrier_all hnu hnu1 hPrefix hJ1 hJ2 hJ3 hJ4
    ell L hlL (by omega : 1 ≤ ell) e he z
  have hA1nn : 0 ≤ dEstimateConst d * nu ^ (-(2 : ℝ)) *
      (3 : ℝ) ^ (-(((ell - nn : ℕ) : ℝ))) := by
    refine mul_nonneg (mul_nonneg ?_ hq2)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    unfold dEstimateConst
    have hosc0 : 0 ≤ oscTailConst d := by
      unfold oscTailConst
      exact mul_nonneg (upperShellFluxConst_nonneg d)
        IndependentSums.gammaTriangleConst_pos.le
    exact mul_nonneg IndependentSums.gammaTriangleConst_pos.le
      (add_nonneg hosc0 (sq_nonneg _))
  have hdn : 0 < d := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hPrefix.dimension
  have hinv0 : 0 ≤ nu⁻¹ := inv_nonneg.mpr hnu.le
  have hA2nn : 0 ≤ blupQuadTailConstAll d * nu⁻¹ * (L : ℝ) :=
    mul_nonneg (mul_nonneg (blupQuadTailConstAll_pos hdn).le hinv0)
      (Nat.cast_nonneg L)
  have hprod := isBigO_gammaSigma_mul (σ₁ := (1 : ℝ)) (σ₂ := (1 : ℝ))
    (by norm_num) (by norm_num) hA1nn hA2nn hDfun hQ
  have hrpow : nu ^ (-(3 : ℝ)) = nu ^ (-(2 : ℝ)) * nu⁻¹ := by
    have hsum : (-(2 : ℝ)) + (-(1 : ℝ)) = -(3 : ℝ) := by norm_num
    rw [← Real.rpow_neg_one, ← Real.rpow_add hnu, hsum]
  have hamp : (dEstimateConst d * nu ^ (-(2 : ℝ)) *
        (3 : ℝ) ^ (-(((ell - nn : ℕ) : ℝ)))) *
      (blupQuadTailConstAll d * nu⁻¹ * (L : ℝ)) =
      (dEstimateConst d * blupQuadTailConstAll d) * nu ^ (-(3 : ℝ)) * (L : ℝ) *
        (3 : ℝ) ^ (-(((ell - nn : ℕ) : ℝ))) := by
    rw [hrpow]
    ring
  refine isBigO_gammaSigma_of_exponent_le
    (show ((1 : ℝ) / 3) ≤ ((1 : ℝ) * 1 / ((1 : ℝ) + 1)) by norm_num) ?_
  refine hprod.mono_scale ?_
  exact le_of_eq (by rw [hamp]; unfold blupRemainderConstAll; ring)

/-! ## The `hTailAll` hypothesis and the `_hBlup` slot -/

/-- **Conjunct 2 of `_hBlup` on every triadic cube.**  From the all-scale
remainder tail, the `Γ_{1/3}` tail at the amplitude
`Czero ν^{-3} L' 3^{-(ℓ-n)}` holds on every cube as soon as `Czero` dominates
the transported constant `blupRemainderConstAll d`.  This is the ungated form
`hTailAll` the slot consumes; the scale-`n` tail is the special
case and needs no J1, while the transport beyond the scale `ℓ` needs
`ShellLawJ1` carried by the colour decomposition. -/
theorem blup_tail_allCubes [NeZero d]
    {P : ProbabilityMeasure (ShellSeq d)} {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (e : Vec d) (he : vecNormSq e = 1)
    {Czero : ℝ} (hConstAll : blupRemainderConstAll d ≤ Czero) :
    ∀ z : TriadicCube d,
      IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3))
        (fun omega : ShellSeq d => blupRemainderZrem nu S.n S.ell S.LPrime e omega z)
        (Czero * nu ^ (-(3 : ℝ)) * ((S.LPrime : ℕ) : ℝ) *
          (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) := by
  obtain ⟨hnl, hlL, -, -⟩ := blup_scales_of_ordering d hSorder
  intro z
  refine (blupRemainderZrem_gammaSigma_one_third_all hnu hnu1 hPrefix hJ1 hJ2 hJ3 hJ4
    S.n S.ell S.LPrime hnl hlL e he z).mono_scale ?_
  have hnu3 : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) := (Real.rpow_pos_of_pos hnu _).le
  have hL : (0 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hConstAll hnu3) hL) h3

/-! ## The reduction with the `Γ_{1/3}` tail discharged -/

end

end SuperdiffusionCLT.Section3.Terms
