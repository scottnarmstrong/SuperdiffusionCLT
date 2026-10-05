/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.TermGaugeAssembly
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Inputs

/-!
# mixGaugeFinal: assembling `hGaugeBound`, part 1 (geometry and Orlicz averages)

`p.mixing.P.three.prime#term2-scale-comparison`'s Cauchy-Schwarz/Jensen/`e.kmn.bounds` consequence:
`TermsCombined.lean`'s `hGaugeBound` hypothesis needs three `IsBigO`
witnesses (`Γ2`, `Γ1`, `Γ_{1/3}`) bounding twice the gauge-term average over
`descendantsAtDepth (originCube d m) (m - n)`. This file supplies the
deterministic and Orlicz-averaging half of the assembly:

* every descendant cube in that finset has the same scale, so
  `TermGaugeAssembly.lean`'s per-cube `Γ2`/`Γ1` bounds on
  `matrixOperatorNorm (volumeAverageMat R (Δk))`/its square apply uniformly;
* `Homogenization.IndependentSums.isBigO_finsetAverage_of_isBigO_gammaSigma`
  folds the (constant-amplitude) per-cube family into a single `Γ2`/`Γ1`
  bound on the finset-averaged quantities `mixGaugeFinal_Y1`,
  `mixGaugeFinal_Y2`;
* `TermGaugeBilinear.lean`'s per-cube bilinear bound, summed and averaged
  over the finset, controls twice the averaged gauge term by
  `(4 t Y1(omega) + 2 t^2 Y2(omega)) * (Aell-energy)`, with
  `t := sigmaBarStarInvScalar nu ell P (cu_n)`.

Part 2 (`TermGaugeFinalB.lean`) converts the `t`-order amplitudes to
`sigmaBarStarScalar nu L`-order ones via a scale comparison and
supplies the final witnesses for `hGaugeBound`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq finiteShellIncrement)
open SuperdiffusionCLT.Section2.Estimates.Stream

noncomputable section

variable {d : ℕ}

/-! ## Geometry: the descendant finset sits at one common scale -/

/-- Every `R ∈ descendantsAtDepth (originCube d m) (m - n)` has scale
`m - (m - n)` (natural subtraction twice): the integer identity
`scale_eq_sub_of_mem_descendantsAtDepth` read through `Nat.cast_sub` applied
to the always-true `m - n ≤ m`. This holds for every `n, m : ℕ` with no order
hypothesis: when `n ≤ m` it says the scale is `n`; when `n > m` the finset is
the singleton `{originCube d m}` (depth `0`, since `m - n = 0`) and the
formula reduces to scale `m`. -/
theorem mixGaugeFinal_scale_of_mem_descendants (n m : ℕ) {R : Homogenization.TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n)) :
    R.scale = ((m - (m - n) : ℕ) : ℤ) := by
  have h := scale_eq_sub_of_mem_descendantsAtDepth hR
  have hsub : (m - n : ℕ) ≤ m := Nat.sub_le m n
  rw [h, show (originCube d (m : ℤ)).scale = (m : ℤ) from rfl, Nat.cast_sub hsub]

/-! ## Positivity of the `p`-th moment constant -/

/-- Strict positivity of `finiteShellIncrementPthMomentConst d p`: the same
argument as `IncrementPthMomentLargeCube.lean`'s `private` lemma of the same
name, reproved here since a `private` declaration is file-scoped. -/
theorem mixGaugeFinal_finiteShellIncrementPthMomentConst_pos
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) {p : ℝ}
    (hp : (1 : ℝ) ≤ p) : 0 < finiteShellIncrementPthMomentConst d p := by
  have hsigma : (0 : ℝ) < 2 / p := div_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hp)
  have hbase : (0 : ℝ) < Real.exp 1 * gammaMomentConst (2 / p) :=
    mul_pos (Real.exp_pos 1) (gammaMomentConst_pos hsigma)
  rw [finiteShellIncrementPthMomentConst]
  exact mul_pos (Real.rpow_pos_of_pos hbase _) (streamLinftyConst_pos hPrefix)

/-! ## The finset-averaged size observables -/

/-- The finset average of `matrixOperatorNorm (volumeAverageMat R (Δk))` over
`descendantsAtDepth (originCube d m) (m - n)`. -/
noncomputable def mixGaugeFinal_Y1 (omega : ShellSeq d) (ell L n m : ℕ) : ℝ :=
  ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
    ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
      matrixOperatorNorm (volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y))

/-- The finset average of `matrixOperatorNorm (volumeAverageMat R (Δk))^2`
over `descendantsAtDepth (originCube d m) (m - n)`. -/
noncomputable def mixGaugeFinal_Y2 (omega : ShellSeq d) (ell L n m : ℕ) : ℝ :=
  ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
    ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
      matrixOperatorNorm (volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2

theorem mixGaugeFinal_Y1_measurable [NeZero d] (ell L n m : ℕ) :
    Measurable (fun omega : ShellSeq d ↦ mixGaugeFinal_Y1 omega ell L n m) := by
  unfold mixGaugeFinal_Y1
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_sum _ fun R _ ↦
    ShellField.continuous_matrixOperatorNorm.measurable.comp
      (SuperdiffusionCLT.Section3.Terms.measurable_volumeAverageMat_finiteShellIncrement ell L R)

theorem mixGaugeFinal_Y2_measurable [NeZero d] (ell L n m : ℕ) :
    Measurable (fun omega : ShellSeq d ↦ mixGaugeFinal_Y2 omega ell L n m) := by
  unfold mixGaugeFinal_Y2
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun R _ ↦ ?_
  exact (ShellField.continuous_matrixOperatorNorm.measurable.comp
    (SuperdiffusionCLT.Section3.Terms.measurable_volumeAverageMat_finiteShellIncrement ell L R)).pow_const 2

theorem mixGaugeFinal_Y1_nonneg (omega : ShellSeq d) (ell L n m : ℕ) :
    0 ≤ mixGaugeFinal_Y1 omega ell L n m := by
  unfold mixGaugeFinal_Y1
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun R _ ↦ matrixOperatorNorm_nonneg _)

theorem mixGaugeFinal_Y2_nonneg (omega : ShellSeq d) (ell L n m : ℕ) :
    0 ≤ mixGaugeFinal_Y2 omega ell L n m := by
  unfold mixGaugeFinal_Y2
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun R _ ↦ sq_nonneg _)

/-! ## `Γ2`/`Γ1` bounds on the finset-averaged size observables -/

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- **The `Γ2` bound on `mixGaugeFinal_Y1`.** Folds the constant-amplitude
per-cube `Γ2` bound of `TermGaugeAssembly.lean`'s
`mixTail_isBigO_matrixOperatorNorm_volumeAverageMat` over the (nonempty)
descendant finset via `isBigO_finsetAverage_of_isBigO_gammaSigma`; since the
amplitude does not depend on the cube, the finset average of the constant
amplitude collapses back to itself. -/
theorem mixGaugeFinal_Y1_isBigO [NeZero d]
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (ell L n m : ℕ) (hellL : ell < L) :
    IsBigO P.toMeasure (gammaSigma 2) (fun omega ↦ mixGaugeFinal_Y1 omega ell L n m)
      (gammaTriangleConst 2 *
        ((d : ℝ) * finiteShellIncrementPthMomentConst d 1 *
          Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ))) := by
  set s := descendantsAtDepth (originCube d (m : ℤ)) (m - n) with hsdef
  set A1 : ℝ := (d : ℝ) * finiteShellIncrementPthMomentConst d 1 *
    Real.sqrt (((L - ell : ℕ) : ℕ) : ℝ) with hA1def
  have hA1pos : 0 < A1 := by
    have hK1pos := mixGaugeFinal_finiteShellIncrementPthMomentConst_pos hPrefix (p := 1) le_rfl
    have hdpos : (0 : ℝ) < d := by
      have hdN : (0 : ℕ) < d := Nat.pos_of_ne_zero (NeZero.ne d)
      exact_mod_cast hdN
    have hgap : (0 : ℝ) < (((L - ell : ℕ) : ℕ) : ℝ) := by
      have hgapN : (0 : ℕ) < L - ell := Nat.sub_pos_of_lt hellL
      exact_mod_cast hgapN
    have hsqrtpos := Real.sqrt_pos.2 hgap
    rw [hA1def]
    positivity
  have hs : s.Nonempty := descendantsAtDepth_nonempty _ _
  have hX : ∀ R ∈ s, IsBigO P.toMeasure (gammaSigma 2)
      (fun omega ↦ matrixOperatorNorm (volumeAverageMat (cubeSet R)
        (fun y ↦ finiteShellIncrement omega ell L y))) A1 := by
    intro R hR
    exact mixTail_isBigO_matrixOperatorNorm_volumeAverageMat hPrefix hJ2 hJ3 hJ4 ell L hellL R
      (m - (m - n)) (mixGaugeFinal_scale_of_mem_descendants n m hR)
  have hXm : ∀ R ∈ s, Measurable (fun omega ↦ matrixOperatorNorm (volumeAverageMat (cubeSet R)
      (fun y ↦ finiteShellIncrement omega ell L y))) := fun R _ ↦
    ShellField.continuous_matrixOperatorNorm.measurable.comp
      (SuperdiffusionCLT.Section3.Terms.measurable_volumeAverageMat_finiteShellIncrement ell L R)
  have havg := isBigO_finsetAverage_of_isBigO_gammaSigma (μ := P.toMeasure) s
    (X := fun R omega ↦ matrixOperatorNorm (volumeAverageMat (cubeSet R)
      (fun y ↦ finiteShellIncrement omega ell L y)))
    (a := fun _ ↦ A1) (σ := 2) (by norm_num) hs (fun R _ ↦ hA1pos) hX hXm
  have hconst : (s.card : ℝ)⁻¹ * ∑ _R ∈ s, A1 = A1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard0 : (s.card : ℝ) ≠ 0 := by
      have hcardpos := hs.card_pos
      exact_mod_cast hcardpos.ne'
    field_simp
  rw [hconst] at havg
  simpa only [mixGaugeFinal_Y1, hsdef] using havg

/-- **The `Γ1` bound on `mixGaugeFinal_Y2`.** Same route as
`mixGaugeFinal_Y1_isBigO`, folding `TermGaugeAssembly.lean`'s per-cube `Γ1`
bound on `matrixOperatorNorm (volumeAverageMat R (Δk))^2`. -/
theorem mixGaugeFinal_Y2_isBigO [NeZero d]
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (ell L n m : ℕ) (hellL : ell < L) :
    IsBigO P.toMeasure (gammaSigma 1) (fun omega ↦ mixGaugeFinal_Y2 omega ell L n m)
      (gammaTriangleConst 1 *
        ((d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 *
          (((L - ell : ℕ) : ℕ) : ℝ))) := by
  set s := descendantsAtDepth (originCube d (m : ℤ)) (m - n) with hsdef
  set A2 : ℝ := (d : ℝ) ^ 2 * finiteShellIncrementPthMomentConst d 2 ^ 2 *
    (((L - ell : ℕ) : ℕ) : ℝ) with hA2def
  have hA2pos : 0 < A2 := by
    have hK2pos := mixGaugeFinal_finiteShellIncrementPthMomentConst_pos hPrefix (p := 2) (by norm_num)
    have hdpos : (0 : ℝ) < d := by
      have hdN : (0 : ℕ) < d := Nat.pos_of_ne_zero (NeZero.ne d)
      exact_mod_cast hdN
    have hgap : (0 : ℝ) < (((L - ell : ℕ) : ℕ) : ℝ) := by
      have hgapN : (0 : ℕ) < L - ell := Nat.sub_pos_of_lt hellL
      exact_mod_cast hgapN
    rw [hA2def]
    positivity
  have hs : s.Nonempty := descendantsAtDepth_nonempty _ _
  have hX : ∀ R ∈ s, IsBigO P.toMeasure (gammaSigma 1)
      (fun omega ↦ matrixOperatorNorm (volumeAverageMat (cubeSet R)
        (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2) A2 := by
    intro R hR
    exact mixTail_isBigO_matrixOperatorNorm_sq_volumeAverageMat hPrefix hJ2 hJ3 hJ4 ell L hellL R
      (m - (m - n)) (mixGaugeFinal_scale_of_mem_descendants n m hR)
  have hXm : ∀ R ∈ s, Measurable (fun omega ↦ matrixOperatorNorm (volumeAverageMat (cubeSet R)
      (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2) := fun R _ ↦
    (ShellField.continuous_matrixOperatorNorm.measurable.comp
      (SuperdiffusionCLT.Section3.Terms.measurable_volumeAverageMat_finiteShellIncrement ell L R)).pow_const 2
  have havg := isBigO_finsetAverage_of_isBigO_gammaSigma (μ := P.toMeasure) s
    (X := fun R omega ↦ matrixOperatorNorm (volumeAverageMat (cubeSet R)
      (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2)
    (a := fun _ ↦ A2) (σ := 1) (by norm_num) hs (fun R _ ↦ hA2pos) hX hXm
  have hconst : (s.card : ℝ)⁻¹ * ∑ _R ∈ s, A2 = A2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard0 : (s.card : ℝ) ≠ 0 := by
      have hcardpos := hs.card_pos
      exact_mod_cast hcardpos.ne'
    field_simp
  rw [hconst] at havg
  simpa only [mixGaugeFinal_Y2, hsdef] using havg

/-! ## Nonnegativity of the `Aell`-bilinear form -/

/-- **`Aell` is positive semidefinite on `cu_n`.** From
`mixMain_annealedBilinear_eq`'s decomposition into the two nonnegative scalar
blocks `sigmaBarScalar`, `sigmaBarStarInvScalar`. -/
theorem mixGaugeFinal_Aell_bilinear_nonneg [NeZero d] {nu : ℝ} (hnu : 0 < nu) (ell : ℕ)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (n : ℤ) (p : BlockVec d) :
    0 ≤ blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P n) p) := by
  have heq : blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P n) p) =
      sigmaBarScalar nu ell P (cubeSet (originCube d n)) * vecNormSq p.1 +
        sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) * vecNormSq p.2 := by
    unfold mixTerms_Aell
    exact mixMain_annealedBilinear_eq hnu ell hJ4 n p
  rw [heq]
  have hspos := sigmaBarScalar_originCube_pos hnu ell hPrefix hJ2 hJ3 hJ4 n
  have htpos := sigmaBarStarInvScalar_pos_cutoff hnu ell hPrefix hJ2 hJ3 hJ4 n
  exact add_nonneg (mul_nonneg hspos.le (vecNormSq_nonneg p.1))
    (mul_nonneg htpos.le (vecNormSq_nonneg p.2))

/-! ## The deterministic averaged bilinear bound, at `t := sigmaBarStarInvScalar nu ell` -/

/-- **The finset-averaged gauge-term bilinear bound**, at the `ell`-order
scalar `t := sigmaBarStarInvScalar nu ell P (cu_n)`: summing
`TermGaugeBilinear.lean`'s per-cube bound
`mixTail_gaugeTermMatrix_bilinear_le` over `descendantsAtDepth (originCube d
m) (m - n)` and dividing by the cardinality turns the per-cube envelope
`4 t ‖h_R‖ + 2 t^2 ‖h_R‖^2` into `4 t Y1(omega) + 2 t^2 Y2(omega)`, with
`Y1, Y2` the finset averages `mixGaugeFinal_Y1`, `mixGaugeFinal_Y2`. -/
theorem mixGaugeFinal_bilinear_avg_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (ell L n m : ℕ) (omega : ShellSeq d) (p q : BlockVec d) :
    2 * (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
          blockVecDot p (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P (n : ℤ) R) q)) ≤
      (4 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
            mixGaugeFinal_Y1 omega ell L n m +
          2 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) ^ 2 *
            mixGaugeFinal_Y2 omega ell L n m) *
        (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
          blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := by
  set s := descendantsAtDepth (originCube d (m : ℤ)) (m - n) with hsdef
  set t := sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) with htdef
  set K := blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
      blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q) with hKdef
  set N : Homogenization.TriadicCube d → ℝ := fun R ↦
      matrixOperatorNorm (volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y))
    with hNdef
  have hY1eq : mixGaugeFinal_Y1 omega ell L n m = (s.card : ℝ)⁻¹ * ∑ R ∈ s, N R := rfl
  have hY2eq : mixGaugeFinal_Y2 omega ell L n m = (s.card : ℝ)⁻¹ * ∑ R ∈ s, N R ^ 2 := rfl
  rw [hY1eq, hY2eq]
  have hpoint : ∀ R ∈ s,
      2 * blockVecDot p (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P (n : ℤ) R) q) ≤
        (4 * t * N R + 2 * t ^ 2 * N R ^ 2) * K :=
    fun R _ ↦ mixTail_gaugeTermMatrix_bilinear_le hnu omega ell L hPrefix hJ2 hJ3 hJ4 (n : ℤ) R p q
  have hsum :
      ∑ R ∈ s, 2 * blockVecDot p (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P (n : ℤ) R) q) ≤
        ∑ R ∈ s, (4 * t * N R + 2 * t ^ 2 * N R ^ 2) * K :=
    Finset.sum_le_sum hpoint
  have hcardnn : (0 : ℝ) ≤ (s.card : ℝ)⁻¹ := by positivity
  have hstep : (s.card : ℝ)⁻¹ *
      ∑ R ∈ s, 2 * blockVecDot p (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P (n : ℤ) R) q) ≤
      (s.card : ℝ)⁻¹ * ∑ R ∈ s, (4 * t * N R + 2 * t ^ 2 * N R ^ 2) * K :=
    mul_le_mul_of_nonneg_left hsum hcardnn
  have hlhs : 2 * ((s.card : ℝ)⁻¹ *
      ∑ R ∈ s, blockVecDot p (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P (n : ℤ) R) q)) =
      (s.card : ℝ)⁻¹ *
        ∑ R ∈ s, 2 * blockVecDot p (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P (n : ℤ) R) q) := by
    rw [← Finset.mul_sum]; ring
  have hrhs : (s.card : ℝ)⁻¹ * ∑ R ∈ s, (4 * t * N R + 2 * t ^ 2 * N R ^ 2) * K =
      (4 * t * ((s.card : ℝ)⁻¹ * ∑ R ∈ s, N R) +
          2 * t ^ 2 * ((s.card : ℝ)⁻¹ * ∑ R ∈ s, N R ^ 2)) * K := by
    rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  calc 2 * ((s.card : ℝ)⁻¹ *
        ∑ R ∈ s, blockVecDot p (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P (n : ℤ) R) q))
      = (s.card : ℝ)⁻¹ *
          ∑ R ∈ s, 2 * blockVecDot p (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P (n : ℤ) R) q) :=
        hlhs
    _ ≤ (s.card : ℝ)⁻¹ * ∑ R ∈ s, (4 * t * N R + 2 * t ^ 2 * N R ^ 2) * K := hstep
    _ = (4 * t * ((s.card : ℝ)⁻¹ * ∑ R ∈ s, N R) +
          2 * t ^ 2 * ((s.card : ℝ)⁻¹ * ∑ R ∈ s, N R ^ 2)) * K :=
        hrhs

end

end SuperdiffusionCLT.Section4.Mixing
