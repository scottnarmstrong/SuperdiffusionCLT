/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellDerivTailGauge
public import SuperdiffusionCLT.Section2.Estimates.Stream.SpatialAverageTail
public import SuperdiffusionCLT.Assumptions.ShellLaw.J2EntryConsequences
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField

/-!
# The coarse-average difference of the infrared cutoff

The paper states and proves the
display `e.bounding.something.that.is.more.complicated.than.it.seems`, the
central estimate of the "Moreover" block of the stream-increment scale
estimates: for `n ≤ m` and a cube `z + cu_n` inside `cu_m`,

> `|(k)_{z + cu_n} - (k)_{cu_m}| ≤ O_{Γ₂}(C (m - n)^{1/2})`.

This module proves that display for the infrared cutoff `k_m = ∑_{k ≤ m} j_k`,
which is the form the printed proof establishes first, before letting the
upper cutoff tend to infinity.

## The split of the printed proof

The printed proof splits the shells at the two scales:

1. the coarse shells `k ≤ n`, where both spatial averages carry the decay
   `3^{-(d/2)(scale - k)}` of the display `e.jk.spatialavg` and the
   weights sum geometrically — `isBigOWith_gammaSigma_shellSpatialAverageDifference_range`;
2. the shells `k ∈ (n, m]`, which are independent (J2) and centred
   (J4) and each of unit amplitude, so the centred independent-sum
   concentration of the CoarseGraining library produces the square root — this is the
   printed appeal to Proposition `p.concentration` and is
   `isBigOWith_gammaSigma_shellSpatialAverageDifference_Ioc`;
3. the shells `k > m`, whose contribution the printed proof bounds by the
   oscillation `C 3^m ‖∇(k_M - k_m)‖_{L∞(cu_m)}` — that is the separate
   `shellDerivTailGauge` of the `Stream` namespace and its uniform `Γ₂` tail.

Only the square root of step 2 is a genuine gain over the triangle
inequality: `m - n` shells of unit amplitude summed by the generalized
triangle inequality alone would give `C (m - n)`, and the printed statement
needs `C (m - n)^{1/2}`.

## The uniformity that fails

The estimate holds for each fixed centre `z`. It does **not** hold uniformly
in `z` at the same amplitude: the maximum over the `3^{d(m-n)}` triadic
sub-cubes of `cu_m` costs a further factor `(log 3^{d(m-n)})^{1/2}`, which is
again of order `(m - n)^{1/2}`, so the uniform statement is of order
`(m - n)`. That is why the printed proof takes the union bound separately, in
`e.bounding.the.diff.of.k.union`, at the larger amplitude
`C h`.

## Main definitions

* `coarseAverageMidConst`, `coarseAverageHeadConst`, `coarseAverageDiffConst`:
  the explicit dimension-only amplitudes of the three steps.

## Main results

* `integral_eq_zero_of_odd_under_negateSequence`: the centring input of the
  independent-sum concentration inequality, from J4.
* `isBigOWith_gammaSigma_shellSpatialAverageDifference_Ioc`: step 2.
* `isBigOWith_gammaSigma_shellSpatialAverageDifference_range`: step 1.
* `isBigOWith_gammaSigma_streamCutoffAverageDifference`: the display for the
  infrared cutoff, in shell-average form. The identification of that form with
  the printed carrier `(k_m)_{z + cu_n} - (k_m)_{cu_m}` is
  `StreamCutoffCoarseAverage.lean` in the same directory.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Estimates
namespace Stream

open Homogenization MeasureTheory ProbabilityTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-! ## Mean zero from whole-sequence negation -/

/-- **Whole-sequence negation centres every odd observable.** Under the
J4 negation symmetry, a measurable real observable which changes sign under
`ShellField.negateSequence` has zero mean. This is the centring hypothesis of
the independent-sum concentration inequality. -/
theorem integral_eq_zero_of_odd_under_negateSequence (hJ4 : ShellLawJ4 d P)
    {X : (ℕ → ShellField d) → ℝ} (hXMeas : Measurable X)
    (hodd : ∀ omega : ℕ → ShellField d,
      X (ShellField.negateSequence omega) = -X omega) :
    ∫ omega : ℕ → ShellField d, X omega ∂P.toMeasure = 0 := by
  have hNegLaw : Measure.map (ShellField.negateSequence (d := d)) P.toMeasure =
      P.toMeasure := by
    have h := congrArg ProbabilityMeasure.toMeasure hJ4.negation
    change Measure.map (ShellField.negateSequence (d := d)) P.toMeasure =
      P.toMeasure at h
    exact h
  have hEq : (∫ omega, X omega ∂P.toMeasure) =
      -∫ omega, X omega ∂P.toMeasure := by
    calc
      ∫ omega, X omega ∂P.toMeasure =
          ∫ omega, X omega
            ∂Measure.map (ShellField.negateSequence (d := d)) P.toMeasure := by
        rw [hNegLaw]
      _ = ∫ omega, X (ShellField.negateSequence omega) ∂P.toMeasure :=
        integral_map ShellField.measurable_negateSequence.aemeasurable
          hXMeas.aestronglyMeasurable
      _ = ∫ omega, -X omega ∂P.toMeasure := by
        refine integral_congr_ae ?_
        filter_upwards with omega
        exact hodd omega
      _ = -∫ omega, X omega ∂P.toMeasure := integral_neg X
  exact CharZero.eq_neg_self_iff.mp hEq

/-! ## The independent shell range of the coarse-average difference -/

private theorem matrixOperatorNorm_le_sum_abs_entries (A : Mat d) :
    matrixOperatorNorm A ≤ ∑ q : Fin d × Fin d, |A q.1 q.2| := by
  have hsum : ∑ q : Fin d × Fin d, |A q.1 q.2| =
      ∑ i : Fin d, ∑ l : Fin d, |A i l| :=
    Fintype.sum_prod_type fun q : Fin d × Fin d ↦ |A q.1 q.2|
  rw [hsum]
  exact (matrixOperatorNorm_le_matrixFrobeniusNorm A).trans
    (matrixFrobeniusNorm_le_sum_abs_entries A)

private theorem measurable_shellSpatialAverage_entry_coordinate
    (h : ℤ) (y : Vec d) (k : ℕ) (i l : Fin d) :
    Measurable (fun omega : ℕ → ShellField d ↦
      ShellField.shellSpatialAverage h y (omega k) i l) := by
  have hrow : Measurable (fun A : Mat d ↦ A i) := measurable_pi_apply i
  have hcol : Measurable (fun v : Fin d → ℝ ↦ v l) := measurable_pi_apply l
  exact ((hcol.comp hrow).comp
    (ShellField.measurable_shellSpatialAverage h y)).comp
    (ShellField.measurable_shellCoordinate k)

/-- The amplitude of the middle range of the coarse-average difference: the
matrix-entry triangle prefactor, the independent-sum constant of the CoarseGraining library, and
twice the unit amplitude of one spatial average. -/
def coarseAverageMidConst (d : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 * (d : ℝ) ^ 2 *
    (Book.Ch04.gammaSigmaIndependentSumConst 2 *
      (IndependentSums.gammaTriangleConst 2 *
        (2 * (1 + spatialAverageColorConst d))))

theorem coarseAverageMidConst_nonneg (d : ℕ) : 0 ≤ coarseAverageMidConst d := by
  have h1 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have h2 : (0 : ℝ) < Book.Ch04.gammaSigmaIndependentSumConst 2 :=
    SuperdiffusionCLT.Probability.gammaSigmaIndependentSumConst_two_pos
  have h3 : 0 ≤ spatialAverageColorConst d := spatialAverageColorConst_nonneg d
  rw [coarseAverageMidConst]
  positivity

/-- **The middle range of the printed display
`e.bounding.something.that.is.more.complicated.than.it.seems`** (the
second step of its proof). The shells `j_{n+1}, …, j_m` are independent (J2) and
centred (J4), and each of their spatial averages, over the translated cube
`z + cu_n` and over `cu_m` alike, has a unit `Γ₂` amplitude by the
display `e.jk.spatialavg`. The centred independent-sum concentration
of the CoarseGraining library therefore gives the square-root gain: the whole range has amplitude
`C (m - n)^{1/2}`, not `C (m - n)`. -/
theorem isBigOWith_gammaSigma_shellSpatialAverageDifference_Ioc
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {n m : ℕ} (hnm : n < m) (z : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ℕ → ShellField d ↦
        matrixOperatorNorm
          (∑ k ∈ Finset.Ioc n m,
            (ShellField.shellSpatialAverage (n : ℤ) z (omega k) -
              ShellField.shellSpatialAverage (m : ℤ) 0 (omega k))))
      (coarseAverageMidConst d * Real.sqrt ((m - n : ℕ) : ℝ)) := by
  classical
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hcolor : 0 ≤ spatialAverageColorConst d := spatialAverageColorConst_nonneg d
  have htri : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hind : (0 : ℝ) < Book.Ch04.gammaSigmaIndependentSumConst 2 :=
    SuperdiffusionCLT.Probability.gammaSigmaIndependentSumConst_two_pos
  set K : ℝ := IndependentSums.gammaTriangleConst 2 *
    (2 * (1 + spatialAverageColorConst d)) with hKdef
  have hK : 0 < K := by
    rw [hKdef]; positivity
  set Y : Fin d → Fin d → ℕ → (ℕ → ShellField d) → ℝ := fun i l k omega =>
    ShellField.shellSpatialAverage (n : ℤ) z (omega k) i l -
      ShellField.shellSpatialAverage (m : ℤ) 0 (omega k) i l with hYdef
  have hYmeas : ∀ i l : Fin d, ∀ k : ℕ, Measurable (Y i l k) := by
    intro i l k
    exact (measurable_shellSpatialAverage_entry_coordinate (n : ℤ) z k i l).sub
      (measurable_shellSpatialAverage_entry_coordinate (m : ℤ) 0 k i l)
  have hYbig : ∀ i l : Fin d, ∀ k : ℕ,
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (Y i l k) K := by
    intro i l k
    have hunit : ∀ h : ℤ, ∀ y : Vec d,
        IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
          (fun omega : ℕ → ShellField d ↦
            ShellField.shellSpatialAverage h y (omega k) i l)
          (1 + spatialAverageColorConst d) := by
      intro h y
      refine (isBigO_gammaSigma_shellSpatialAverage_entry hPrefix hJ1 hJ3 hJ4
        k h y i l).mono_scale ?_
      have hle : (3 : ℝ) ^ (-((d : ℝ) / 2) *
          ((max (h - (k : ℤ)) 0 : ℤ) : ℝ)) ≤ 1 := by
        refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
        have hmax : (0 : ℝ) ≤ ((max (h - (k : ℤ)) 0 : ℤ) : ℝ) := by
          exact_mod_cast le_max_right (h - (k : ℤ)) 0
        have hdd : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
        nlinarith only [hmax, hdd]
      calc (1 + spatialAverageColorConst d) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ))
          ≤ (1 + spatialAverageColorConst d) * 1 :=
            mul_le_mul_of_nonneg_left hle (by linarith only [hcolor])
        _ = 1 + spatialAverageColorConst d := mul_one _
    have hneg := (hunit (m : ℤ) 0).neg
    have hsum := SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO
      (mu := P.toMeasure) (sigma := 2) (by norm_num)
      (A := 1 + spatialAverageColorConst d) (B := 1 + spatialAverageColorConst d)
      (by linarith only [hcolor]) (by linarith only [hcolor])
      (hunit (n : ℤ) z) hneg
      (measurable_shellSpatialAverage_entry_coordinate (n : ℤ) z k i l)
      (measurable_shellSpatialAverage_entry_coordinate (m : ℤ) 0 k i l).neg
    have hfun : (fun omega : ℕ → ShellField d ↦
        ShellField.shellSpatialAverage (n : ℤ) z (omega k) i l +
          -ShellField.shellSpatialAverage (m : ℤ) 0 (omega k) i l) = Y i l k := by
      funext omega
      rw [hYdef]
      ring
    rw [hfun] at hsum
    have hamp : IndependentSums.gammaTriangleConst 2 *
        ((1 + spatialAverageColorConst d) + (1 + spatialAverageColorConst d)) = K := by
      rw [hKdef]; ring
    rwa [hamp] at hsum
  have hYmean : ∀ i l : Fin d, ∀ k : ℕ,
      ∫ omega : ℕ → ShellField d, Y i l k omega ∂P.toMeasure = 0 := by
    intro i l k
    refine integral_eq_zero_of_odd_under_negateSequence hJ4 (hYmeas i l k) ?_
    intro omega
    simp only [hYdef, ShellField.negateSequence_apply,
      ShellField.shellSpatialAverage_negate, Matrix.neg_apply]
    ring
  have hYindep : ∀ i l : Fin d,
      ProbabilityTheory.iIndepFun (fun (k : ℕ) (omega : ℕ → ShellField d) ↦
        Y i l k omega) P.toMeasure := by
    intro i l
    have hmeasField : Measurable (fun jf : ShellField d ↦
        ShellField.shellSpatialAverage (n : ℤ) z jf i l -
          ShellField.shellSpatialAverage (m : ℤ) 0 jf i l) := by
      have hrow : Measurable (fun A : Mat d ↦ A i) := measurable_pi_apply i
      have hcol : Measurable (fun v : Fin d → ℝ ↦ v l) := measurable_pi_apply l
      exact (((hcol.comp hrow).comp
        (ShellField.measurable_shellSpatialAverage (n : ℤ) z)).sub
        ((hcol.comp hrow).comp
          (ShellField.measurable_shellSpatialAverage (m : ℤ) 0)))
    exact hJ2.independent.comp
      (fun _ : ℕ ↦ fun jf : ShellField d ↦
        ShellField.shellSpatialAverage (n : ℤ) z jf i l -
          ShellField.shellSpatialAverage (m : ℤ) 0 jf i l)
      (fun _ ↦ hmeasField)
  have hcard : ((Finset.Ioc n m).card : ℝ) = ((m - n : ℕ) : ℝ) := by
    rw [Nat.card_Ioc]
  have hentry : ∀ q : Fin d × Fin d,
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ℕ → ShellField d ↦
          |∑ k ∈ Finset.Ioc n m, Y q.1 q.2 k omega|)
        (Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((m - n : ℕ) : ℝ) * K) := by
    intro q
    have h := Book.Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
      (μ := P.toMeasure) (X := Y q.1 q.2) (s := Finset.Ioc n m) (σ := 2) (K := K)
      (hYindep q.1 q.2) (hYmeas q.1 q.2) (Finset.nonempty_Ioc.mpr hnm)
      (by norm_num) (by norm_num) hK
      (fun k _ ↦ hYbig q.1 q.2 k) (fun k _ ↦ hYmean q.1 q.2 k)
    rw [hcard] at h
    simpa only [IndependentSums.IsBigO, abs_abs] using h
  have hmeasSum : ∀ q : Fin d × Fin d,
      Measurable (fun omega : ℕ → ShellField d ↦
        |∑ k ∈ Finset.Ioc n m, Y q.1 q.2 k omega|) := by
    intro q
    have hsum : Measurable (fun omega : ℕ → ShellField d ↦
        ∑ k ∈ Finset.Ioc n m, Y q.1 q.2 k omega) :=
      Finset.measurable_sum (Finset.Ioc n m) fun k _ ↦ hYmeas q.1 q.2 k
    simpa only [Real.norm_eq_abs] using hsum.norm
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty :=
    ⟨(⟨0, hd⟩, ⟨0, hd⟩), Finset.mem_univ _⟩
  have hAmp : (0 : ℝ) < Book.Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt ((m - n : ℕ) : ℝ) * K := by
    have hgap : (0 : ℝ) < ((m - n : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hnm
    have : (0 : ℝ) < Real.sqrt ((m - n : ℕ) : ℝ) := Real.sqrt_pos.2 hgap
    positivity
  have htriangle := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := P.toMeasure) (Finset.univ : Finset (Fin d × Fin d))
    (X := fun q (omega : ℕ → ShellField d) ↦
      |∑ k ∈ Finset.Ioc n m, Y q.1 q.2 k omega|)
    (a := fun _ : Fin d × Fin d ↦
      Book.Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((m - n : ℕ) : ℝ) * K)
    (σ := 2) (by norm_num) hne (fun _ _ ↦ hAmp) (fun q _ ↦ hentry q)
    (fun q _ ↦ hmeasSum q)
  have hamp : IndependentSums.gammaTriangleConst 2 *
      ∑ _q : Fin d × Fin d,
        (Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((m - n : ℕ) : ℝ) * K) =
      coarseAverageMidConst d * Real.sqrt ((m - n : ℕ) : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, coarseAverageMidConst, hKdef]
    push_cast
    ring
  rw [hamp] at htriangle
  refine htriangle.of_le fun omega ↦ ?_
  have hentryEq : ∑ q : Fin d × Fin d,
      |(∑ k ∈ Finset.Ioc n m,
        (ShellField.shellSpatialAverage (n : ℤ) z (omega k) -
          ShellField.shellSpatialAverage (m : ℤ) 0 (omega k))) q.1 q.2| =
      ∑ q : Fin d × Fin d, |∑ k ∈ Finset.Ioc n m, Y q.1 q.2 k omega| := by
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    congr 1
    simp only [Matrix.sum_apply, Matrix.sub_apply, hYdef]
  refine le_trans (matrixOperatorNorm_le_sum_abs_entries _) ?_
  rw [hentryEq]
  exact le_abs_self _

/-! ## The coarse shell range of the coarse-average difference -/

private theorem rpow_three_neg_nat (j : ℕ) :
    (3 : ℝ) ^ (-(j : ℝ)) = ((3 : ℝ)⁻¹) ^ j := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← inv_pow]

private theorem matrixOperatorNorm_finset_sum_le {iota : Type*} (s : Finset iota)
    (f : iota → Mat d) :
    matrixOperatorNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, matrixOperatorNorm (f i) := by
  simp only [matrixOperatorNorm_eq_l2_opNorm]
  exact norm_sum_le s f

private theorem matrixOperatorNorm_add_le (A B : Mat d) :
    matrixOperatorNorm (A + B) ≤ matrixOperatorNorm A + matrixOperatorNorm B := by
  simp only [matrixOperatorNorm_eq_l2_opNorm]
  exact norm_add_le A B

private theorem matrixOperatorNorm_sub_le (A B : Mat d) :
    matrixOperatorNorm (A - B) ≤ matrixOperatorNorm A + matrixOperatorNorm B := by
  simp only [matrixOperatorNorm_eq_l2_opNorm]
  exact norm_sub_le A B

private theorem sum_range_rpow_weight_le {h : ℤ} {n : ℕ} (hd : 2 ≤ d)
    (hn : (n : ℤ) ≤ h) :
    ∑ k ∈ Finset.range (n + 1),
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ)) ≤ 3 / 2 := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hstep : ∀ k ∈ Finset.range (n + 1),
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ)) ≤
        ((3 : ℝ)⁻¹) ^ (n - k) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkh : (k : ℤ) ≤ h := le_trans (by exact_mod_cast hkn) hn
    have hmax : max (h - (k : ℤ)) 0 = h - (k : ℤ) := max_eq_left (by omega)
    have hcast : (((n - k : ℕ) : ℕ) : ℝ) ≤ ((h - (k : ℤ) : ℤ) : ℝ) := by
      have : ((n - k : ℕ) : ℤ) ≤ h - (k : ℤ) := by omega
      exact_mod_cast this
    have hnonneg : (0 : ℝ) ≤ ((h - (k : ℤ) : ℤ) : ℝ) := by
      have : (0 : ℤ) ≤ h - (k : ℤ) := by omega
      exact_mod_cast this
    have hexp : -((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ) ≤
        -(((n - k : ℕ) : ℕ) : ℝ) := by
      rw [hmax]
      nlinarith only [hcast, hnonneg, hdR]
    calc (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ))
        ≤ (3 : ℝ) ^ (-(((n - k : ℕ) : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = ((3 : ℝ)⁻¹) ^ (n - k) := rpow_three_neg_nat (n - k)
  refine le_trans (Finset.sum_le_sum hstep) ?_
  have hrefl : ∑ k ∈ Finset.range (n + 1), ((3 : ℝ)⁻¹) ^ (n - k) =
      ∑ j ∈ Finset.range (n + 1), ((3 : ℝ)⁻¹) ^ j := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' : j < n + 1 := Finset.mem_range.mp hj
    congr 1
    omega
  rw [hrefl]
  have hsummable : Summable fun j : ℕ ↦ ((3 : ℝ)⁻¹) ^ j :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hle := hsummable.sum_le_tsum (Finset.range (n + 1))
    (fun j _ ↦ by positivity)
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hle
  refine le_trans hle (le_of_eq ?_)
  norm_num

private theorem spatialAverageTailConst_pos_of_pos (hd : 0 < d) :
    0 < spatialAverageTailConst d := by
  have hcolor : 0 ≤ spatialAverageColorConst d := spatialAverageColorConst_nonneg d
  have htri : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [spatialAverageTailConst]
  positivity

/-- The amplitude of the coarse range of the coarse-average difference. -/
def coarseAverageHeadConst (d : ℕ) : ℝ :=
  16384 * (IndependentSums.gammaTriangleConst 2 * (3 * spatialAverageTailConst d))

theorem coarseAverageHeadConst_nonneg (d : ℕ) :
    0 ≤ coarseAverageHeadConst d := by
  have h1 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have h2 : 0 ≤ spatialAverageTailConst d := by
    have := spatialAverageColorConst_nonneg d
    rw [spatialAverageTailConst]
    positivity
  rw [coarseAverageHeadConst]
  positivity

private theorem coarseAverageHeadConst_pos_of_pos (hd : 0 < d) :
    0 < coarseAverageHeadConst d := by
  have htri : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hC : 0 < spatialAverageTailConst d := spatialAverageTailConst_pos_of_pos hd
  rw [coarseAverageHeadConst]
  positivity

/-- **The coarse range of the printed display
`e.bounding.something.that.is.more.complicated.than.it.seems`** (the
first step of its proof): the shells `j_0, …, j_n`, coarser than the small cube, contribute
`O_{Γ₂}(C)` with no growth in `m - n` at all. Both spatial averages of shell
`k ≤ n` carry the decay `3^{-(d/2)(scale - k)}` of `e.jk.spatialavg`,
and those weights are summable geometrically over `k ≤ n` because the
dimension is at least two. -/
theorem isBigOWith_gammaSigma_shellSpatialAverageDifference_range
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {n m : ℕ} (hnm : n ≤ m) (z : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ℕ → ShellField d ↦
        matrixOperatorNorm
          (∑ k ∈ Finset.range (n + 1),
            (ShellField.shellSpatialAverage (n : ℤ) z (omega k) -
              ShellField.shellSpatialAverage (m : ℤ) 0 (omega k))))
      (coarseAverageHeadConst d) := by
  classical
  have hd : 2 ≤ d := hPrefix.dimension
  have hCpos : 0 < spatialAverageTailConst d := by
    have hcolor : 0 ≤ spatialAverageColorConst d := spatialAverageColorConst_nonneg d
    have htri : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
      IndependentSums.gammaTriangleConst_pos
    have hdR : (0 : ℝ) < (d : ℝ) := by
      have : 0 < d := lt_of_lt_of_le (by norm_num) hd
      exact_mod_cast this
    rw [spatialAverageTailConst]
    positivity
  set a : ℕ → ℝ := fun k ↦ spatialAverageTailConst d *
    (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max ((n : ℤ) - (k : ℤ)) 0 : ℤ) : ℝ)) with hadef
  set b : ℕ → ℝ := fun k ↦ spatialAverageTailConst d *
    (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max ((m : ℤ) - (k : ℤ)) 0 : ℤ) : ℝ)) with hbdef
  have hapos : ∀ k : ℕ, 0 < a k := by
    intro k; rw [hadef]
    have : (0 : ℝ) < (3 : ℝ) ^ (-((d : ℝ) / 2) *
      ((max ((n : ℤ) - (k : ℤ)) 0 : ℤ) : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hbpos : ∀ k : ℕ, 0 < b k := by
    intro k; rw [hbdef]
    have : (0 : ℝ) < (3 : ℝ) ^ (-((d : ℝ) / 2) *
      ((max ((m : ℤ) - (k : ℤ)) 0 : ℤ) : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  set X : ℕ → (ℕ → ShellField d) → ℝ := fun k omega ↦
    matrixOperatorNorm (ShellField.shellSpatialAverage (n : ℤ) z (omega k)) +
      matrixOperatorNorm (ShellField.shellSpatialAverage (m : ℤ) 0 (omega k))
    with hXdef
  have hmeasNorm : ∀ (h : ℤ) (y : Vec d) (k : ℕ),
      Measurable (fun omega : ℕ → ShellField d ↦
        matrixOperatorNorm (ShellField.shellSpatialAverage h y (omega k))) := by
    intro h y k
    exact ShellField.continuous_matrixOperatorNorm.measurable.comp
      ((ShellField.measurable_shellSpatialAverage h y).comp
        (ShellField.measurable_shellCoordinate k))
  have hXmeas : ∀ k : ℕ, Measurable (X k) := by
    intro k
    exact (hmeasNorm (n : ℤ) z k).add (hmeasNorm (m : ℤ) 0 k)
  have hbigOne : ∀ (h : ℤ) (y : Vec d) (k : ℕ),
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ℕ → ShellField d ↦
          matrixOperatorNorm (ShellField.shellSpatialAverage h y (omega k)))
        (spatialAverageTailConst d *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (h - (k : ℤ)) 0 : ℤ) : ℝ))) := by
    intro h y k
    refine (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
      (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2)
      (fun omega ↦ matrixOperatorNorm_nonneg _)).1 ?_
    exact isBigOWith_gammaSigma_matrixOperatorNorm_shellSpatialAverage
      hPrefix hJ1 hJ3 hJ4 k h y
  have hXbig : ∀ k : ℕ,
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) (X k)
        (IndependentSums.gammaTriangleConst 2 * (a k + b k)) :=
    fun k ↦ SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO
      (mu := P.toMeasure) (sigma := 2) (by norm_num) (hapos k) (hbpos k)
      (hbigOne (n : ℤ) z k) (hbigOne (m : ℤ) 0 k)
      (hmeasNorm (n : ℤ) z k) (hmeasNorm (m : ℤ) 0 k)
  have hampPos : ∀ k ∈ Finset.range (n + 1),
      (0 : ℝ) < IndependentSums.gammaTriangleConst 2 * (a k + b k) := by
    intro k _
    have := IndependentSums.gammaTriangleConst_pos (σ := (2 : ℝ))
    have h1 := hapos k
    have h2 := hbpos k
    positivity
  have htriangle := SuperdiffusionCLT.Probability.isBigO_gammaSigma_finset_sum_of_one_le
    (mu := P.toMeasure) (Finset.range (n + 1)) (X := X)
    (a := fun k ↦ IndependentSums.gammaTriangleConst 2 * (a k + b k))
    (sigma := 2) (by norm_num) (Finset.nonempty_range_add_one) hampPos
    (fun k _ ↦ hXbig k) (fun k _ ↦ hXmeas k)
  have hsum_le : ∑ k ∈ Finset.range (n + 1),
      IndependentSums.gammaTriangleConst 2 * (a k + b k) ≤
      IndependentSums.gammaTriangleConst 2 * (3 * spatialAverageTailConst d) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ IndependentSums.gammaTriangleConst_pos.le
    have hsa : ∑ k ∈ Finset.range (n + 1), a k ≤
        spatialAverageTailConst d * (3 / 2) := by
      rw [hadef, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (sum_range_rpow_weight_le (d := d) hd (le_refl (n : ℤ))) hCpos.le
    have hsb : ∑ k ∈ Finset.range (n + 1), b k ≤
        spatialAverageTailConst d * (3 / 2) := by
      rw [hbdef, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left
        (sum_range_rpow_weight_le (d := d) hd ?_) hCpos.le
      exact_mod_cast hnm
    rw [Finset.sum_add_distrib]
    linarith only [hsa, hsb]
  have hle : (16384 : ℝ) * ∑ k ∈ Finset.range (n + 1),
      IndependentSums.gammaTriangleConst 2 * (a k + b k) ≤
      coarseAverageHeadConst d := by
    rw [coarseAverageHeadConst]
    exact mul_le_mul_of_nonneg_left hsum_le (by norm_num)
  have hfinal := htriangle.mono_scale hle
  refine hfinal.of_le fun omega ↦ ?_
  have hbound : matrixOperatorNorm
      (∑ k ∈ Finset.range (n + 1),
        (ShellField.shellSpatialAverage (n : ℤ) z (omega k) -
          ShellField.shellSpatialAverage (m : ℤ) 0 (omega k))) ≤
      ∑ k ∈ Finset.range (n + 1), X k omega := by
    refine le_trans (matrixOperatorNorm_finset_sum_le _ _) ?_
    refine Finset.sum_le_sum fun k _ ↦ ?_
    rw [hXdef]
    exact matrixOperatorNorm_sub_le _ _
  refine le_trans hbound (le_abs_self _)

/-! ## The coarse-average difference of the infrared cutoff -/

/-- The constant of the printed display
`e.bounding.something.that.is.more.complicated.than.it.seems`: the two-term
triangle prefactor applied to the coarse range and the independent range. -/
def coarseAverageDiffConst (d : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 *
    (coarseAverageHeadConst d + coarseAverageMidConst d)

theorem coarseAverageDiffConst_nonneg (d : ℕ) :
    0 ≤ coarseAverageDiffConst d := by
  have htri : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have h1 : 0 ≤ coarseAverageHeadConst d := coarseAverageHeadConst_nonneg d
  have h2 : 0 ≤ coarseAverageMidConst d := coarseAverageMidConst_nonneg d
  rw [coarseAverageDiffConst]
  positivity

/-- The finite sum of shell spatial-average differences is measurable in the
shell sequence. -/
theorem measurable_shellAverageDifferenceSum (n m : ℕ) (z : Vec d)
    (s : Finset ℕ) :
    Measurable (fun omega : ℕ → ShellField d ↦
      ∑ k ∈ s,
        (ShellField.shellSpatialAverage (n : ℤ) z (omega k) -
          ShellField.shellSpatialAverage (m : ℤ) 0 (omega k))) := by
  refine Finset.measurable_sum s fun k _ ↦ ?_
  exact ((ShellField.measurable_shellSpatialAverage (n : ℤ) z).comp
      (ShellField.measurable_shellCoordinate k)).sub
    ((ShellField.measurable_shellSpatialAverage (m : ℤ) 0).comp
      (ShellField.measurable_shellCoordinate k))

private theorem range_succ_sum_split {M : Type*} [AddCommMonoid M]
    {n m : ℕ} (hnm : n ≤ m) (f : ℕ → M) :
    ∑ k ∈ Finset.range (m + 1), f k =
      (∑ k ∈ Finset.range (n + 1), f k) + ∑ k ∈ Finset.Ioc n m, f k := by
  have hIoc : Finset.Ioc n m = Finset.Ico (n + 1) (m + 1) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.range_eq_Ico, Finset.range_eq_Ico]
  exact (Finset.sum_Ico_consecutive f (Nat.zero_le (n + 1))
    (Nat.succ_le_succ hnm)).symm

/-- **The printed display
`e.bounding.something.that.is.more.complicated.than.it.seems`** for the
infrared cutoff `k_m = ∑_{k ≤ m} j_k`: for `n < m` and every centre `z`, the difference
of the spatial averages of `k_m` over the
translated cube `z + cu_n` and over `cu_m` has a symmetric `Γ₂` tail at
amplitude `C(d) (m - n)^{1/2}`.

The coarse shells `k ≤ n` contribute a bounded amount, by the geometric decay
of `e.jk.spatialavg`; the shells `k ∈ (n, m]` are independent and centred, so
the concentration inequality of the CoarseGraining library gives the square-root
growth.  This is exactly the split of the printed proof, with the third printed piece
(the shells above `m`) treated separately by `isBigO_gammaSigma_shellDerivTailGauge`. -/
theorem isBigOWith_gammaSigma_streamCutoffAverageDifference
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {n m : ℕ} (hnm : n < m) (z : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ℕ → ShellField d ↦
        matrixOperatorNorm
          (∑ k ∈ Finset.range (m + 1),
            (ShellField.shellSpatialAverage (n : ℤ) z (omega k) -
              ShellField.shellSpatialAverage (m : ℤ) 0 (omega k))))
      (coarseAverageDiffConst d * Real.sqrt ((m - n : ℕ) : ℝ)) := by
  classical
  have hgap : (1 : ℝ) ≤ ((m - n : ℕ) : ℝ) := by
    have : 1 ≤ m - n := Nat.sub_pos_of_lt hnm
    exact_mod_cast this
  have hsqrt : (1 : ℝ) ≤ Real.sqrt ((m - n : ℕ) : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hgap
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hheadPos : 0 < coarseAverageHeadConst d :=
    coarseAverageHeadConst_pos_of_pos hd0
  have hmidPos : 0 < coarseAverageMidConst d * Real.sqrt ((m - n : ℕ) : ℝ) := by
    have h1 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
      IndependentSums.gammaTriangleConst_pos
    have h2 : (0 : ℝ) < Book.Ch04.gammaSigmaIndependentSumConst 2 :=
      SuperdiffusionCLT.Probability.gammaSigmaIndependentSumConst_two_pos
    have h3 : 0 ≤ spatialAverageColorConst d := spatialAverageColorConst_nonneg d
    have h4 : (0 : ℝ) < Real.sqrt ((m - n : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hsqrt
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    rw [coarseAverageMidConst]
    positivity
  have hHead := isBigOWith_gammaSigma_shellSpatialAverageDifference_range
    hPrefix hJ1 hJ3 hJ4 (n := n) (m := m) hnm.le z
  have hMid := isBigOWith_gammaSigma_shellSpatialAverageDifference_Ioc
    hPrefix hJ1 hJ2 hJ3 hJ4 hnm z
  have hHeadO := (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
    (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2)
    (fun omega ↦ matrixOperatorNorm_nonneg _)).1 hHead
  have hMidO := (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
    (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2)
    (fun omega ↦ matrixOperatorNorm_nonneg _)).1 hMid
  have hsum := SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO
    (mu := P.toMeasure) (sigma := 2) (by norm_num) hheadPos hmidPos hHeadO hMidO
    (ShellField.continuous_matrixOperatorNorm.measurable.comp
      (measurable_shellAverageDifferenceSum n m z (Finset.range (n + 1))))
    (ShellField.continuous_matrixOperatorNorm.measurable.comp
      (measurable_shellAverageDifferenceSum n m z (Finset.Ioc n m)))
  have hamp : IndependentSums.gammaTriangleConst 2 *
      (coarseAverageHeadConst d +
        coarseAverageMidConst d * Real.sqrt ((m - n : ℕ) : ℝ)) ≤
      coarseAverageDiffConst d * Real.sqrt ((m - n : ℕ) : ℝ) := by
    rw [coarseAverageDiffConst]
    have hstep : coarseAverageHeadConst d +
        coarseAverageMidConst d * Real.sqrt ((m - n : ℕ) : ℝ) ≤
        (coarseAverageHeadConst d + coarseAverageMidConst d) *
          Real.sqrt ((m - n : ℕ) : ℝ) := by
      have h1 : coarseAverageHeadConst d ≤
          coarseAverageHeadConst d * Real.sqrt ((m - n : ℕ) : ℝ) := by
        nlinarith only [hsqrt, hheadPos]
      nlinarith only [h1]
    calc IndependentSums.gammaTriangleConst 2 *
          (coarseAverageHeadConst d +
            coarseAverageMidConst d * Real.sqrt ((m - n : ℕ) : ℝ))
        ≤ IndependentSums.gammaTriangleConst 2 *
            ((coarseAverageHeadConst d + coarseAverageMidConst d) *
              Real.sqrt ((m - n : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep IndependentSums.gammaTriangleConst_pos.le
      _ = IndependentSums.gammaTriangleConst 2 *
            (coarseAverageHeadConst d + coarseAverageMidConst d) *
              Real.sqrt ((m - n : ℕ) : ℝ) := by ring
  refine (hsum.mono_scale hamp).of_le fun omega ↦ ?_
  have hsplit := range_succ_sum_split (M := Mat d) hnm.le
    (fun k ↦ ShellField.shellSpatialAverage (n : ℤ) z (omega k) -
      ShellField.shellSpatialAverage (m : ℤ) 0 (omega k))
  rw [hsplit]
  exact le_trans (matrixOperatorNorm_add_le _ _) (le_abs_self _)

end

end Stream
end Estimates
end Section2
end SuperdiffusionCLT
