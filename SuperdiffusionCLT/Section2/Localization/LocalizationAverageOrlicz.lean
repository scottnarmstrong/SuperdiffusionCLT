/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageWork
public import SuperdiffusionCLT.Section2.Carriers.BlockOperatorNorm
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Probability.OrliczIndexWeakening

/-!
# The single Orlicz premise of the averaged gauged comparison

`SuperdiffusionCLT.Section2.Localization.localization_average_of_orlicz`
reduces the statement
`SuperdiffusionCLT.Frozen.Section2.localization_average`
(the paper's `l.localization.average`, with its proof) to exactly one hypothesis, whose shape is
reproduced verbatim here as `LocalizationAverageOrliczPremise`:

```
IsBigO P.toMeasure (gammaSigma (1/3))
  (averagedGaugeComparison nu l L P m n Pvec)
  (localizationAverageEnvelope C nu l L m n Pvec)
```

The present module does not close that premise, which is the whole analytic content of the
printed proof, but it isolates its internal structure, which the printed proof establishes with
the two-term split `|LHS| ≤ T1 + T2`.

## The weak-type part of the printed proof

The premise is a weak-`Γ_{1/3}` tail estimate.  The printed proof produces it in
two pieces and then combines them.

* **The concentration step.**  With `h_z := (k_L − k_ℓ)_{z+cu_n}`,
  `F_> := σ(j_r : r > ℓ)` and the normalized centered variables `X_z`, conditioning on the
  independent upper-scale field gives the exponential tail

  ```
  P[ |⨍_z X_z| > t Cν⁻²(1∨ℓ) 3^{-(d/2)(m-ℓ)} | F_> ] ≤ exp(-t)  ∀ t ≥ 1,
  ```

  that is, the `Γ₁` bound; the second summand `T2` is the same argument on `Z_z`, giving
  `T2 ≤ O_{Γ_{1/2}}(Cν⁻¹(1∨ℓ)(1∨L)(1∨(m-n)) 3^{-(d/2)(m-ℓ)}|P|²)`.

* **The first summand.**  `T1` is controlled by the deterministic comparison `D_z` together with
  the fourth-moment average; Cauchy--Schwarz then gives

  ```
  T1 ≤ O_{Γ_{1/3}}( 1_{L>ℓ} Cν⁻³ L 3^{-(ℓ-n)} |P|² )
  ```

  after enlarging `C(d)`.

* **The combine.**  `Γ_{1/2}`-tails are stronger than `Γ_{1/3}`-tails and
  `ν⁻¹ ≤ ν⁻³` on `ν ∈ (0,1]`, so both summands are `Γ_{1/3}` at the two printed
  amplitudes, whose sum is `localizationAverageEnvelope`.

## Main results

The final combine.  `localization_average_orlicz_of_summands`
derives the premise from

1. the pointwise decomposition `|LHS ω| ≤ T1 ω + T2 ω`,
2. `T1 = O_{Γ_{1/3}}(localizationAverageEnvelopeT1 C ν ℓ L n Pvec)`
   (the first printed amplitude),
3. `T2 = O_{Γ_{1/2}}(localizationAverageEnvelopeT2 C ν ℓ L m n Pvec)`
   (the second printed amplitude),

using the index weakening `isBigO_gammaSigma_one_third_of_one_half`, the
two-term triangle inequality `isBigO_gammaSigma_add_of_isBigO` and the
amplitude monotonicity `IsBigO.mono_scale`.  The printed envelope is proved to be
exactly the sum of the two summand amplitudes
(`localizationAverageEnvelope_eq_T1_add_T2`) and the assembly constant
`orliczAssemblyConst = 2 * gammaTriangleConst (1/3)` is named explicitly; the
printed proof likewise enlarges its constant at these two points.

## The remaining estimates

Neither of the two summand estimates (2)--(3) is proved in this file, and
neither is the pointwise decomposition (1).  The decomposition (1) is the
instantiation of `l.localization.A` at the
perturbation field `k_L − k_ℓ − h_z`, combined with
`e.commute.coarse.grained.k0`; the second summand (3) is the sublattice
concentration of the conditionally independent centered variables `Z_z`,
whose inputs are `e.Enaught.vs.A.and.Ahom`, `e.Enaught.mixing`,
`e.jk.spatialavg` and `a.j.frd` (the range-of-dependence colouring); the first
summand (2) needs `e.nabla.kmn.Linfty` and the fourth moment.
Those estimates are the content of the printed proof, not of
this file.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## The premise, named -/

/-- The single hypothesis `hOrlicz` of
`localization_average_of_orlicz`, named: the printed estimate
`e.localization.average.oneshot`
for the averaged gauged comparison, with `localizationAverageEnvelope` the
printed amplitude. -/
def LocalizationAverageOrliczPremise (C nu : ℝ)
    (P : ProbabilityMeasure (ShellSeq d)) (m n l L : ℕ) (Pvec : BlockVec d) : Prop :=
  IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 3))
    (averagedGaugeComparison nu l L P m n Pvec)
    (localizationAverageEnvelope C nu l L m n Pvec)

/-! ## The two printed summand amplitudes -/

/-- The first printed summand amplitude of `e.localization.average.oneshot`
(first term): `C ν⁻³ |P|² 1_{L>ℓ} L 3^{-(ℓ-n)}`.  The indicator is
the printed one: the localization error vanishes identically when `L = ℓ`. -/
noncomputable def localizationAverageEnvelopeT1 (C nu : ℝ) (l L n : ℕ)
    (Pvec : BlockVec d) : ℝ :=
  C * nu ^ (-(3 : ℝ)) * blockVecDot Pvec Pvec *
    (if l < L then (L : ℝ) * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ)) else 0)

/-- The second printed summand amplitude of `e.localization.average.oneshot`
(second term):
`C ν⁻³ |P|² (1∨ℓ)(1∨L)(1∨(m-n)) 3^{-(d/2)(m-ℓ)}`. -/
noncomputable def localizationAverageEnvelopeT2 (C nu : ℝ) (l L m n : ℕ)
    (Pvec : BlockVec d) : ℝ :=
  C * nu ^ (-(3 : ℝ)) * blockVecDot Pvec Pvec *
    (max 1 (l : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
      (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - l : ℕ) : ℝ))))

/-- The assembly constant of the printed combine: twice the `Γ_{1/3}` triangle
constant `gammaTriangleConst (1/3)`.  Two copies appear because both summands
are lifted to the same amplitude `localizationAverageEnvelope C ν ℓ L m n Pvec`
before the triangle inequality is applied.  The printed proof performs the same
enlargement of `C(d)`. -/
noncomputable def orliczAssemblyConst : ℝ :=
  2 * IndependentSums.gammaTriangleConst ((1 : ℝ) / 3)

/-! ## The printed envelope is the sum of the two summand amplitudes -/

/-- **The printed amplitude is exactly the sum of the two printed summand
amplitudes**: the envelope of `e.localization.average.oneshot`
splits into `localizationAverageEnvelopeT1 + localizationAverageEnvelopeT2`. -/
theorem localizationAverageEnvelope_eq_T1_add_T2 (C nu : ℝ) (l L m n : ℕ)
    (Pvec : BlockVec d) :
    localizationAverageEnvelope C nu l L m n Pvec =
      localizationAverageEnvelopeT1 C nu l L n Pvec +
        localizationAverageEnvelopeT2 C nu l L m n Pvec := by
  unfold localizationAverageEnvelope localizationAverageEnvelopeT1 localizationAverageEnvelopeT2
  ring

/-- The printed envelope is linear in its constant `C`, the form in which the
assembly constant is absorbed. -/
theorem localizationAverageEnvelope_const_mul (k C nu : ℝ) (l L m n : ℕ)
    (Pvec : BlockVec d) :
    localizationAverageEnvelope (k * C) nu l L m n Pvec =
      k * localizationAverageEnvelope C nu l L m n Pvec := by
  unfold localizationAverageEnvelope
  ring

/-! ## Positivity of the amplitudes -/

/-- The first printed summand amplitude is nonnegative. -/
theorem localizationAverageEnvelopeT1_nonneg {C nu : ℝ} (hC : 0 ≤ C) (hnu : 0 ≤ nu)
    (l L n : ℕ) (Pvec : BlockVec d) :
    0 ≤ localizationAverageEnvelopeT1 C nu l L n Pvec := by
  unfold localizationAverageEnvelopeT1
  refine mul_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hnu _))
    (SuperdiffusionCLT.Section2.Carriers.blockVecDot_self_nonneg Pvec)) ?_
  by_cases h : l < L
  · rw [ite_eq_left h]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  · rw [ite_eq_right h]

/-- The second printed summand amplitude is nonnegative. -/
theorem localizationAverageEnvelopeT2_nonneg {C nu : ℝ} (hC : 0 ≤ C) (hnu : 0 ≤ nu)
    (l L m n : ℕ) (Pvec : BlockVec d) :
    0 ≤ localizationAverageEnvelopeT2 C nu l L m n Pvec := by
  unfold localizationAverageEnvelopeT2
  refine mul_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hnu _))
    (SuperdiffusionCLT.Section2.Carriers.blockVecDot_self_nonneg Pvec)) ?_
  refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_)
    (Real.rpow_nonneg (by norm_num) _)
  · exact le_trans zero_le_one (le_max_left _ _)
  · exact le_trans zero_le_one (le_max_left _ _)
  · exact le_trans zero_le_one (le_max_left _ _)

/-- The second printed summand amplitude is positive whenever `C > 0`, `ν > 0`
and `Pvec ≠ 0`, since every remaining factor is strictly positive. -/
theorem localizationAverageEnvelopeT2_pos {C nu : ℝ} (hC : 0 < C) (hnu : 0 < nu)
    (l L m n : ℕ) {Pvec : BlockVec d}
    (hdot : 0 < blockVecDot Pvec Pvec) :
    0 < localizationAverageEnvelopeT2 C nu l L m n Pvec := by
  unfold localizationAverageEnvelopeT2
  refine mul_pos (mul_pos (mul_pos hC (Real.rpow_pos_of_pos hnu _)) hdot) ?_
  refine mul_pos (mul_pos (mul_pos ?_ ?_) ?_) (Real.rpow_pos_of_pos (by norm_num) _)
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-! ## The per-cube carrier of the averaged comparison -/

/-- The per-cube term of the averaged gauged comparison: the quadratic form
`P · (bfA_L(z+cu_n) − G_{−h_z}ᵗ bfAhom_ℓ(cu_n) G_{−h_z}) P` at
the lattice cube `R = z + cu_n`, with `h_z` the volume average of the finite
shell increment on `R`, as in `averagedGaugeComparison`.  This is the observable
whose conditional concentration yields the second summand. -/
noncomputable def gaugeComparisonCube (nu : ℝ) (l L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (n : ℕ) (R : TriadicCube d)
    (Pvec : BlockVec d) (omega : ShellSeq d) : ℝ :=
  blockVecDot Pvec
    (blockMatVecMul
      (ofFullBlockMat
        (toFullBlockMat
            (coarseBlockMatrix (cubeSet R)
              (coefficientCutoff nu omega L).toCoeffField) -
          toFullBlockMat
            (blockMatMul
              (blockMatTranspose
                (blockG
                  (-volumeAverageMat (cubeSet R)
                    (fun y => finiteShellIncrement omega l L y))))
              (blockMatMul
                (annealedBlockMatrix nu l P
                  (cubeSet (originCube d (n : ℤ))))
                (blockG
                  (-volumeAverageMat (cubeSet R)
                    (fun y => finiteShellIncrement omega l L y)))))))
      Pvec)

/-- **The averaged gauged comparison is the normalized lattice average of the
per-cube terms**: `averagedGaugeComparison` splits into
`|3^nℤ^d ∩ cu_m|⁻¹ ∑_R gaugeComparisonCube R`, over the descendants
`R = z + cu_n` of `cu_m`.  This is definitional; it exposes the carrier to which
the printed concentration step applies. -/
theorem averagedGaugeComparison_eq_average (nu : ℝ) (l L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (m n : ℕ) (Pvec : BlockVec d) :
    averagedGaugeComparison nu l L P m n Pvec =
      fun omega : ShellSeq d =>
        ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
            gaugeComparisonCube nu l L P n R Pvec omega :=
  rfl

/-! ## The assembly of the two printed summand estimates -/

/-- The identically zero observable obeys every `Γ_σ` tail bound at amplitude
`0`, the base case of the degenerate amplitude in the assembly. -/
private theorem isBigO_gammaSigma_zero (mu : MeasureTheory.Measure (ShellSeq d))
    (sigma : ℝ) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (fun _ : ShellSeq d => (0 : ℝ)) 0 := by
  intro t _ht
  have hset : IndependentSums.upperTailEvent
      (fun omega : ShellSeq d => |(fun _ : ShellSeq d => (0 : ℝ)) omega|)
      (0 * t) = (∅ : Set (ShellSeq d)) := by
    ext omega
    simp only [IndependentSums.upperTailEvent, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      abs_zero, lt_self_iff_false, zero_mul]
  rw [hset]
  have hzero : mu.real (∅ : Set (ShellSeq d)) = 0 := by
    simp only [MeasureTheory.Measure.real, measure_empty, ENNReal.toReal_zero]
  rw [hzero]
  exact inv_nonneg.mpr (by
    simpa only [IndependentSums.gammaSigma_apply] using (Real.exp_pos (t ^ sigma)).le)

/-- **The printed combine.**  From

1. the pointwise splitting `|LHS ω| ≤ T1 ω + T2 ω`,
2. `T1 = O_{Γ_{1/3}}(C ν⁻³ |P|² 1_{L>ℓ} L 3^{-(ℓ-n)})`, and
3. `T2 = O_{Γ_{1/2}}(C ν⁻³ |P|² (1∨ℓ)(1∨L)(1∨(m-n)) 3^{-(d/2)(m-ℓ)})`
   (weakened to `Γ_{1/3}` and `ν⁻³`),

the averaged gauged comparison is `O_{Γ_{1/3}}` at the printed envelope with the
explicitly named constant `orliczAssemblyConst * C`.  Both summands are lifted to
the common amplitude `localizationAverageEnvelope C ν ℓ L m n Pvec` (through
`IsBigO.mono_scale`) and combined by `isBigO_gammaSigma_add_of_isBigO`; the
triangle constant is the printed enlargement of `C(d)`. -/
theorem localization_average_orlicz_of_summands {C nu : ℝ} (hC : 0 < C) (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (m n l L : ℕ) (Pvec : BlockVec d)
    (T1 T2 : ShellSeq d → ℝ) (hT1m : Measurable T1) (hT2m : Measurable T2)
    (hT1nn : ∀ omega, 0 ≤ T1 omega) (hT2nn : ∀ omega, 0 ≤ T2 omega)
    (hdecomp : ∀ omega : ShellSeq d,
      |averagedGaugeComparison nu l L P m n Pvec omega| ≤ T1 omega + T2 omega)
    (hT1 : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 3)) T1
      (localizationAverageEnvelopeT1 C nu l L n Pvec))
    (hT2 : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 2)) T2
      (localizationAverageEnvelopeT2 C nu l L m n Pvec)) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 3))
      (averagedGaugeComparison nu l L P m n Pvec)
      (localizationAverageEnvelope (orliczAssemblyConst * C) nu l L m n Pvec) := by
  by_cases hdot : blockVecDot Pvec Pvec = 0
  · -- Degenerate case `Pvec = 0`: both amplitudes and the comparison vanish.
    have hPvec : Pvec = 0 := by
      have hsum : vecNormSq Pvec.1 + vecNormSq Pvec.2 = 0 := by
        rwa [SuperdiffusionCLT.Section2.Carriers.blockVecDot_self] at hdot
      rw [add_eq_zero_iff_of_nonneg (vecNormSq_nonneg Pvec.1) (vecNormSq_nonneg Pvec.2)] at hsum
      exact Prod.ext (Homogenization.vecNormSq_eq_zero hsum.1)
        (Homogenization.vecNormSq_eq_zero hsum.2)
    subst hPvec
    have henv0 :
        localizationAverageEnvelope (orliczAssemblyConst * C) nu l L m n (0 : BlockVec d) = 0 := by
      simp only [localizationAverageEnvelope, hdot, mul_zero, zero_mul]
    rw [averagedGaugeComparison_zero, henv0]
    exact isBigO_gammaSigma_zero P.toMeasure ((1 : ℝ) / 3)
  · -- Main case: `Pvec ≠ 0`, so the envelope is strictly positive.
    have hdotpos : 0 < blockVecDot Pvec Pvec :=
      lt_of_le_of_ne (SuperdiffusionCLT.Section2.Carriers.blockVecDot_self_nonneg Pvec)
        (Ne.symm hdot)
    have hA1nn := localizationAverageEnvelopeT1_nonneg hC.le hnu.le l L n Pvec
    have hA2nn := localizationAverageEnvelopeT2_nonneg hC.le hnu.le l L m n Pvec
    have hA2pos := localizationAverageEnvelopeT2_pos hC hnu l L m n hdotpos
    have hPpos : 0 < localizationAverageEnvelope C nu l L m n Pvec := by
      rw [localizationAverageEnvelope_eq_T1_add_T2]
      exact add_pos_of_nonneg_of_pos hA1nn hA2pos
    have hle1 : localizationAverageEnvelopeT1 C nu l L n Pvec ≤
        localizationAverageEnvelope C nu l L m n Pvec := by
      rw [localizationAverageEnvelope_eq_T1_add_T2]
      exact le_add_of_nonneg_right hA2nn
    have hle2 : localizationAverageEnvelopeT2 C nu l L m n Pvec ≤
        localizationAverageEnvelope C nu l L m n Pvec := by
      rw [localizationAverageEnvelope_eq_T1_add_T2]
      exact le_add_of_nonneg_left hA1nn
    have hT1lift : IndependentSums.IsBigO P.toMeasure
        (IndependentSums.gammaSigma ((1 : ℝ) / 3)) T1
        (localizationAverageEnvelope C nu l L m n Pvec) :=
      hT1.mono_scale hle1
    have hT2lift : IndependentSums.IsBigO P.toMeasure
        (IndependentSums.gammaSigma ((1 : ℝ) / 3)) T2
        (localizationAverageEnvelope C nu l L m n Pvec) :=
      (SuperdiffusionCLT.Probability.isBigO_gammaSigma_one_third_of_one_half hT2).mono_scale
        hle2
    have hsum := SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO
      (mu := P.toMeasure) (X := T1) (Y := T2)
      (A := localizationAverageEnvelope C nu l L m n Pvec)
      (B := localizationAverageEnvelope C nu l L m n Pvec)
      (sigma := (1 : ℝ) / 3) (by norm_num) hPpos hPpos hT1lift hT2lift hT1m hT2m
    have henv : localizationAverageEnvelope (orliczAssemblyConst * C) nu l L m n Pvec =
        IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
          (localizationAverageEnvelope C nu l L m n Pvec +
            localizationAverageEnvelope C nu l L m n Pvec) := by
      unfold orliczAssemblyConst
      rw [localizationAverageEnvelope_const_mul]
      ring
    have hfin : IndependentSums.IsBigO P.toMeasure
        (IndependentSums.gammaSigma ((1 : ℝ) / 3)) (fun omega => T1 omega + T2 omega)
        (localizationAverageEnvelope (orliczAssemblyConst * C) nu l L m n Pvec) :=
      hsum.mono_scale (le_of_eq henv.symm)
    exact IndependentSums.IsBigO.of_abs_le hfin fun omega => by
      rw [abs_of_nonneg (add_nonneg (hT1nn omega) (hT2nn omega))]
      exact hdecomp omega

/-! ## Non-vacuity of the reduction

The two summand hypotheses and the pointwise splitting are jointly satisfiable:
at `Pvec = 0` the comparison and both amplitudes vanish, so the hypotheses hold
with the exhibited witnesses `T1 = T2 = 0` and the reduction is not vacuous. -/

end SuperdiffusionCLT.Section2.Localization
