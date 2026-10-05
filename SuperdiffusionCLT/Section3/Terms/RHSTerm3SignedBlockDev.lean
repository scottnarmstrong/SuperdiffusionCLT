/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SourceGapsB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Holder

/-!
# The signed trace bound and the signed third printed term

The signed trace bound and the third printed term of the Hoelder display in the proof of
`l.RHS.term3`.

The coordinate sum of the original Hoelder step is the *absolute*
coordinate sum `sum_i |e_i · (b_ell(z+cu_n) - shom_ell(cu_n)) e_i|` in the printed
proof, while the right-hand factor `coarseBlockDevMoment`
(`Section3/Terms/RHSTerm3InputsD.lean`) of the third printed term of the
Hoelder display averages the centred coarse blocks *signed* over the lattice,
and only the signed average has the concentration gain of
`l.RHS.term3#block-concentration`.  The paper performs the corresponding
silent step when it drops the absolute values; the
fact it uses is the signed trace bound that
`matrixOperatorNorm_le_sum_diag_of_posSemidef`
(`Section3/Terms/RHSTerm3Holder.lean`) proves before the absolute values go in.

* `translatedBlockDevSumSigned` — the coordinate sum without the
  absolute values, i.e. the signed trace deviation of the coarse block.
* `translatedBlockDevSumSigned_eq_originCube` — its translation covariance.
* `translatedBlockNorm_le_blockDevSumSigned` — the signed trace bound
  `|b_ell(z+cu_n)| <= d shom_ell(cu_n) + sum_i e_i . (b_ell(z+cu_n) -
  shom_ell(cu_n)) e_i`, the replacement of `translatedBlockNorm_le_blockDevSum`.
* `holder_term_three` — the third printed term of the Hoelder display
  at the *signed* carrier: the Hoelder step
  `weightedBlockAverage_integral_le` with the second moment of the signed
  lattice average of the trace bounded through the `L^2` triangle inequality
  over the `d` coordinate averages.  The measurability side conditions that
  the original Hoelder step cannot discharge (there is no measurability datum on `w`)
  are the same `hsq` side condition as for the second and fourth printed terms;
  everything on the coarse-block side is discharged here, from the `Γ₁`
  envelope of the centred block.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The signed coordinate sum -/

/-- **`sum_{i=1}^d e_i . (b_ell(z+cu_n) - shom_ell(cu_n)) e_i`**, the coordinate
sum of the proof of `l.RHS.term3` *without* the absolute
values: the signed trace deviation of the coarse block, built from
`blockDeviation`.  It dominates `|b_ell(z+cu_n)| - d shom_ell(cu_n)` through
`translatedBlockNorm_le_blockDevSumSigned`, and its lattice average is the
object the third printed term of the Hoelder display averages. -/
def translatedBlockDevSumSigned [NeZero d] (nu : ℝ) (ell nn : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (omega : ShellSeq d) (z : TriadicCube d) : ℝ :=
  ∑ i : Fin d, blockDeviation nu ell P nn (Pi.single i (1 : ℝ)) omega z

/-- **The signed coordinate sum is translation covariant**, like every quenched
object term 3 reads on `z + cu_n`. -/
theorem translatedBlockDevSumSigned_eq_originCube [NeZero d] (nu : ℝ) (ell nn : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (omega : ShellSeq d) (Q : TriadicCube d) :
    translatedBlockDevSumSigned nu ell nn P omega Q =
      translatedBlockDevSumSigned nu ell nn P
        (ShellField.translateSequence (triadicCubeShift Q) omega)
        (originCube d Q.scale) := by
  rw [translatedBlockDevSumSigned, translatedBlockDevSumSigned]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [blockDeviation, blockDeviation, translatedCoarseBlock_eq_originCube nu ell omega Q]

/-! ## The signed trace bound -/

/-- **The signed trace bound on `|b_ell(z+cu_n)|`**,
from the proof of `l.RHS.term3` without the absolute
values:

`|b_ell(z+cu_n)| <= d shom_ell(cu_n) + sum_i e_i . (b_ell(z+cu_n) -
  shom_ell(cu_n)) e_i`,

at the carriers `translatedBlockNorm` and `blockDeviation`.  The coarse
block is positive semidefinite (`posSemidef_translatedCoarseBlock`), so its
operator norm is at most its trace; the trace is the sum of the `d` centred
coordinate entries plus `d shom_ell(cu_n)`, and this time *no* absolute value
is inserted, so the bound is the exact trace inequality. -/
theorem translatedBlockNorm_le_blockDevSumSigned [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (ell nn : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (omega : ShellSeq d)
    (z : TriadicCube d) :
    translatedBlockNorm nu ell omega z ≤
      (d : ℝ) * sigmaBarSeq nu ell P nn + translatedBlockDevSumSigned nu ell nn P omega z := by
  classical
  have htr := matrixOperatorNorm_le_sum_diag_of_posSemidef
    (posSemidef_translatedCoarseBlock hnu ell omega z)
  have hdiag : ∀ i : Fin d, translatedCoarseBlock nu ell omega z i i =
      blockDeviation nu ell P nn (Pi.single i (1 : ℝ)) omega z +
        sigmaBarSeq nu ell P nn := by
    intro i
    have h1 : blockDeviation nu ell P nn (Pi.single i (1 : ℝ)) omega z =
        translatedCoarseBlock nu ell omega z i i - sigmaBarSeq nu ell P nn := by
      show vecDot (Pi.single i (1 : ℝ))
          (matVecMul (translatedCoarseBlock nu ell omega z) (Pi.single i (1 : ℝ))) -
            sigmaBarSeq nu ell P nn = _
      rw [Homogenization.vecDot_single_matVecMul_single
        (translatedCoarseBlock nu ell omega z) i i]
    linarith only [h1]
  have hconst : ∑ _i : Fin d, sigmaBarSeq nu ell P nn =
      (d : ℝ) * sigmaBarSeq nu ell P nn := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsplit : ∑ i : Fin d, translatedCoarseBlock nu ell omega z i i =
      (∑ i : Fin d, blockDeviation nu ell P nn (Pi.single i (1 : ℝ)) omega z) +
        (d : ℝ) * sigmaBarSeq nu ell P nn := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hdiag i,
      Finset.sum_add_distrib, hconst]
  have hle : ∑ i : Fin d, blockDeviation nu ell P nn (Pi.single i (1 : ℝ)) omega z =
      translatedBlockDevSumSigned nu ell nn P omega z := rfl
  show Book.Ch02.matrixOperatorNorm (translatedCoarseBlock nu ell omega z) ≤ _
  rw [hsplit] at htr
  linarith only [htr, hle]

/-! ## The `L^2` triangle inequality for a finite sum of coordinate averages -/

/-- The square of the sum of finitely many `L^2` functions is at most the square
of the sum of their `L^2` norms: the triangle inequality in `L^2`, proved by
expanding the square and applying Cauchy-Schwarz to each pair. -/
private theorem integral_sq_sum_le {P : ProbabilityMeasure (ShellSeq d)}
    (g : Fin d → ShellSeq d → ℝ) (hmem : ∀ i : Fin d, MemLp (g i) 2 P.toMeasure) :
    ∫ omega : ShellSeq d, (∑ i : Fin d, g i omega) ^ (2 : ℕ) ∂P.toMeasure ≤
      (∑ i : Fin d, Real.sqrt (∫ omega : ShellSeq d, |g i omega| ^ (2 : ℕ)
        ∂P.toMeasure)) ^ (2 : ℕ) := by
  classical
  have hexpand : ∀ omega : ShellSeq d, (∑ i : Fin d, g i omega) ^ (2 : ℕ) =
      ∑ i : Fin d, ∑ j : Fin d, g i omega * g j omega := by
    intro omega
    rw [sq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
  have hint : ∀ i j : Fin d, Integrable (fun omega : ShellSeq d => g i omega * g j omega)
      P.toMeasure := fun i j => (hmem i).integrable_mul (hmem j)
  have hintD : ∀ i : Fin d, Integrable (fun omega : ShellSeq d => ∑ j : Fin d,
      g i omega * g j omega) P.toMeasure :=
    fun i => MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin d))
      (fun j (_ : j ∈ Finset.univ) => hint i j)
  have hint2 : Integrable (fun omega : ShellSeq d => (∑ i : Fin d, g i omega) ^ (2 : ℕ))
      P.toMeasure :=
    (MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin d))
      (fun i (_ : i ∈ Finset.univ) => hintD i)).congr
      (Filter.Eventually.of_forall fun omega => (hexpand omega).symm)
  have hsplit : ∫ omega : ShellSeq d, (∑ i : Fin d, g i omega) ^ (2 : ℕ) ∂P.toMeasure =
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ omega : ShellSeq d, g i omega * g j omega ∂P.toMeasure := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexpand),
      MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin d))
        (fun i (_ : i ∈ Finset.univ) => hintD i)]
    exact Finset.sum_congr rfl fun i _ =>
      MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin d))
        (fun j (_ : j ∈ Finset.univ) => hint i j)
  have hsqabs : ∀ i : Fin d, ∫ omega : ShellSeq d, g i omega ^ (2 : ℕ) ∂P.toMeasure =
      ∫ omega : ShellSeq d, |g i omega| ^ (2 : ℕ) ∂P.toMeasure :=
    fun i => integral_congr_ae (Filter.Eventually.of_forall fun omega => (sq_abs _).symm)
  have hrw : (∑ i : Fin d, Real.sqrt (∫ omega : ShellSeq d, |g i omega| ^ (2 : ℕ)
      ∂P.toMeasure)) ^ (2 : ℕ) =
      ∑ i : Fin d, ∑ j : Fin d, Real.sqrt (∫ omega : ShellSeq d, |g i omega| ^ (2 : ℕ)
        ∂P.toMeasure) * Real.sqrt (∫ omega : ShellSeq d, |g j omega| ^ (2 : ℕ)
        ∂P.toMeasure) := by
    rw [sq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
  rw [hsplit, hrw]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
    refine le_trans (integral_mul_le_sqrt_mul_sqrt (hmem i) (hmem j)) ?_
    rw [← hsqabs i, ← hsqabs j]

/-! ## The algebra of the signed inner average -/

/-- The lattice average of the signed coordinate sum is the sum of the `d`
lattice averages of the coordinate deviations. -/
private theorem avg_signed_eq_sum [NeZero d] (nu : ℝ) (ell nn : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (omega : ShellSeq d)
    (D : Finset (TriadicCube d)) :
    ((D.card : ℝ))⁻¹ * ∑ z ∈ D, translatedBlockDevSumSigned nu ell nn P omega z =
      ∑ i : Fin d, ((D.card : ℝ))⁻¹ * ∑ z ∈ D,
        blockDeviation nu ell P nn (Pi.single i (1 : ℝ)) omega z := by
  calc ((D.card : ℝ))⁻¹ * ∑ z ∈ D, translatedBlockDevSumSigned nu ell nn P omega z
      = ((D.card : ℝ))⁻¹ * ∑ z ∈ D, ∑ i : Fin d,
          blockDeviation nu ell P nn (Pi.single i (1 : ℝ)) omega z := rfl
    _ = ((D.card : ℝ))⁻¹ * ∑ i : Fin d, ∑ z ∈ D,
          blockDeviation nu ell P nn (Pi.single i (1 : ℝ)) omega z := by
        rw [← Finset.sum_comm]
    _ = ∑ i : Fin d, ((D.card : ℝ))⁻¹ * ∑ z ∈ D,
          blockDeviation nu ell P nn (Pi.single i (1 : ℝ)) omega z := by
        rw [Finset.mul_sum]

/-- The unit coordinate vector of `Vec d`. -/
private theorem vecNormSq_single (i : Fin d) : vecNormSq (Pi.single i (1 : ℝ)) = 1 := by
  show vecDot (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) = 1
  rw [vecDot_single_left]
  simp

/-! ## The signed third printed term -/

/-- **The binder `_hTerm3` of the Hoelder bridge, restated at the signed carrier**,
the third printed term of the Hoelder display in the proof of `l.RHS.term3`:

`E[avsum_{z'} |(nabla w)_{z'+cu_k}|^2 avsum_{z in z'+3^n Z^d cap cu_k}
  sum_i Y_z^{(i)}]
  <= sum_i E[|avsum_{z in 3^n Z^d cap cu_k} Y_z^{(i)}|^2]^{1/2}
      E[||nabla w||^4_{L4bar(cu_m)}]^{1/2}`

with `Y_z^{(i)}` the `blockDeviation` and the inner lattice average
*signed*, i.e. with the carrier `translatedBlockDevSumSigned` in place of the
absolute coordinate sum, whose weighted average is not
dominated by `coarseBlockDevMoment`.

The proof is the Hoelder step `weightedBlockAverage_integral_le` with
`M := coarseBlockDevMoment`; the second moment it needs on every outer cube
`z'` comes from the translation covariance of the signed trace
(`integral_sq_descendantAverage_eq`, the silent replacement of the inner
average that the paper makes silently) and the triangle
inequality `integral_sq_sum_le` over the `d` coordinate averages, whose `L^2`
norms are the summands of `coarseBlockDevMoment`.  Integrability of the
coordinate averages is discharged from the `Γ₁` envelope of the centred
coarse block, so no datum on `w` enters; the only side condition on `w` is the
`hsq` of the Hoelder step, the same one the second and fourth printed terms
carry. -/
theorem holder_term_three [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    {zc : TriadicCube d} (hzc : zc.scale = ((coarseBlockScale d S : ℕ) : ℤ))
    (hfin : (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ)
        ∂P.toMeasure) ≠ ⊤)
    (hsq : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad))) 2 P.toMeasure) :
    ∫ omega : ShellSeq d,
        weightedBlockAverage d S.n (coarseBlockScale d S) S.m
          ((w omega).toH1Function.grad)
          (translatedBlockDevSumSigned nu S.ell S.n P omega) ∂P.toMeasure ≤
      coarseBlockDevMoment nu S.ell S.n P
          (descendantsAtDepth zc (coarseBlockScale d S - S.n)) *
        gradResponseMoment (m := S.m) 4 4 P w ^ ((1 : ℝ) / 2) := by
  classical
  have hellP : S.ell ≤ S.ellPrime := le_of_lt hSorder.ell_lt_ellPrime
  have hnl : S.n ≤ S.ell := le_of_lt hSorder.n_lt_ell
  obtain ⟨hk1, hk2, -, -⟩ := coarse_block_scale_choice d S hellP
  have hnk : S.n ≤ coarseBlockScale d S := le_trans hnl hk1
  have hkm : coarseBlockScale d S ≤ S.m :=
    le_trans hk2 (le_of_lt hSorder.ellPrime_lt_m)
  set D : Finset (TriadicCube d) := descendantsAtDepth zc (coarseBlockScale d S - S.n)
  have hscaleD : ∀ z ∈ D, z.scale = ((S.n : ℕ) : ℤ) := by
    intro z hz
    have h := scale_eq_sub_of_mem_descendantsAtDepth hz
    rw [hzc] at h
    rw [h, Nat.cast_sub hnk]
    ring
  -- the covariance of the signed trace
  have hcov : ∀ (omega : ShellSeq d) (Q : TriadicCube d),
      translatedBlockDevSumSigned nu S.ell S.n P omega Q =
        translatedBlockDevSumSigned nu S.ell S.n P
          (ShellField.translateSequence (triadicCubeShift Q) omega)
          (originCube d Q.scale) :=
    translatedBlockDevSumSigned_eq_originCube nu S.ell S.n P
  -- the pointwise identity of the inner average
  have havg : ∀ omega : ShellSeq d,
      ((D.card : ℝ))⁻¹ * ∑ z ∈ D, translatedBlockDevSumSigned nu S.ell S.n P omega z =
        ∑ i : Fin d, ((D.card : ℝ))⁻¹ * ∑ z ∈ D,
          blockDeviation nu S.ell P S.n (Pi.single i (1 : ℝ)) omega z :=
    fun omega => avg_signed_eq_sum nu S.ell S.n P omega D
  -- the coordinate averages are in `L^2(P)`
  have hmemZ : ∀ (i : Fin d) (z : TriadicCube d), z.scale = ((S.n : ℕ) : ℤ) →
      MemLp (fun omega : ShellSeq d =>
        blockDeviation nu S.ell P S.n (Pi.single i (1 : ℝ)) omega z) 2 P.toMeasure := by
    intro i z hz
    have hKpos : (0 : ℝ) < envelopeUpperScalar d nu S.ell + sigmaBarSeq nu S.ell P S.n := by
      have h1 := envelopeUpperScalar_pos hnu d S.ell
      have h2 := sigmaBarSeq_pos hnu S.ell hPrefix hJ2 hJ3 hJ4 S.n
      linarith only [h1, h2]
    obtain ⟨hint4, -⟩ := integral_fourth_le_of_isBigO_gammaSigma_one hKpos
      (measurable_blockDeviation hnu S.ell S.n (Pi.single i (1 : ℝ)) z)
      (isBigO_gammaSigma_blockDeviation_of_shellLaws hnu hPrefix hJ2 hJ3 hJ4 S.ell S.n
        (vecNormSq_single i) hz)
    have hsqeq : ∀ omega : ShellSeq d,
        (blockDeviation nu S.ell P S.n (Pi.single i (1 : ℝ)) omega z ^ (2 : ℕ)) ^ (2 : ℕ)
          = blockDeviation nu S.ell P S.n (Pi.single i (1 : ℝ)) omega z ^ (4 : ℕ) := by
      intro omega
      rw [← pow_mul]
    have hmemSq : MemLp (fun omega : ShellSeq d =>
        blockDeviation nu S.ell P S.n (Pi.single i (1 : ℝ)) omega z ^ (2 : ℕ))
        2 P.toMeasure :=
      (memLp_two_iff_integrable_sq
        ((measurable_blockDeviation hnu S.ell S.n (Pi.single i (1 : ℝ)) z).pow_const
          2).aestronglyMeasurable).2
        (hint4.congr (Filter.Eventually.of_forall fun omega => (hsqeq omega).symm))
    exact (memLp_two_iff_integrable_sq
      (measurable_blockDeviation hnu S.ell S.n (Pi.single i (1 : ℝ)) z).aestronglyMeasurable).2
      (hmemSq.integrable (by norm_num))
  have hmemg : ∀ i : Fin d, MemLp (fun omega : ShellSeq d =>
      ((D.card : ℝ))⁻¹ * ∑ z ∈ D,
        blockDeviation nu S.ell P S.n (Pi.single i (1 : ℝ)) omega z) 2 P.toMeasure :=
    fun i => (memLp_finsetSum D fun z hz => hmemZ i z (hscaleD z hz)).const_mul _
  -- the signed trace is in `L^2(P)` on every descendant of `zc`
  have hmemS : ∀ z : TriadicCube d, z.scale = ((S.n : ℕ) : ℤ) →
      MemLp (fun omega : ShellSeq d =>
        translatedBlockDevSumSigned nu S.ell S.n P omega z) 2 P.toMeasure := by
    intro z hz
    exact memLp_finsetSum (Finset.univ : Finset (Fin d)) fun i _ => hmemZ i z hz
  have hmemAvg : MemLp (fun omega : ShellSeq d =>
      ((D.card : ℝ))⁻¹ * ∑ z ∈ D, translatedBlockDevSumSigned nu S.ell S.n P omega z)
      2 P.toMeasure :=
    (memLp_finsetSum D fun z hz => hmemS z (hscaleD z hz)).const_mul
      ((D.card : ℝ))⁻¹
  -- the second moment of the signed average on `D` is at most the square of
  -- the deviation moment
  have hsqavg : ∀ omega : ShellSeq d,
      (((D.card : ℝ))⁻¹ * ∑ z ∈ D, translatedBlockDevSumSigned nu S.ell S.n P omega z) ^
        (2 : ℕ)
      = (∑ i : Fin d, ((D.card : ℝ))⁻¹ * ∑ z ∈ D,
          blockDeviation nu S.ell P S.n (Pi.single i (1 : ℝ)) omega z) ^ (2 : ℕ) :=
    fun omega => congrArg (fun t : ℝ => t ^ (2 : ℕ)) (havg omega)
  have hsingle : ∫ omega : ShellSeq d,
      (((D.card : ℝ))⁻¹ * ∑ z ∈ D, translatedBlockDevSumSigned nu S.ell S.n P omega z) ^
        (2 : ℕ) ∂P.toMeasure ≤
      coarseBlockDevMoment nu S.ell S.n P D ^ (2 : ℕ) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsqavg)]
    refine le_trans (integral_sq_sum_le
      (fun i omega => ((D.card : ℝ))⁻¹ * ∑ z ∈ D,
        blockDeviation nu S.ell P S.n (Pi.single i (1 : ℝ)) omega z) hmemg) ?_
    exact le_of_eq rfl
  -- the Hoelder step, with the covariance transfer to every outer cube
  have hscale : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      zc.scale = z'.scale := by
    intro z' hz'
    rw [hzc, scale_of_mem_largeCubeSubcubes hkm hz']
  refine weightedBlockAverage_integral_le P w
    (fun omega z => translatedBlockDevSumSigned nu S.ell S.n P omega z)
    (by
      rw [coarseBlockDevMoment]
      exact Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _) hfin hsq ?_ ?_
  · intro z' hz'
    exact memLp_two_descendantAverage_translate hPrefix hJ2 hcov (hscale z' hz')
      (coarseBlockScale d S - S.n) hmemAvg
  · intro z' hz'
    rw [integral_sq_descendantAverage_eq hPrefix hJ2 hcov (hscale z' hz')
      (coarseBlockScale d S - S.n) hmemAvg.aestronglyMeasurable]
    exact hsingle

end

end SuperdiffusionCLT.Section3.Terms