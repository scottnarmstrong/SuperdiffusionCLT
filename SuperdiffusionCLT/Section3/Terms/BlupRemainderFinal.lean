/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.BlupRemainderAssembly
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SourceGapsB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Holder

/-!
# The integrability conjunct of `e.blupbounds.remainder`, and the tested reading

The obligation `_hBlup` of the reduction of term 3 is the printed
remainder witness of `e.blupbounds` in the `∃ Zrem` shape: measurability in the shell sequence at
every cube, the printed `Γ_{1/3}` tail at the amplitude
`C ν^{-3} L' 3^{-(ℓ-n)}`, the pointwise tested display, and the integrability of
the `∇w`-weighted block average of the remainder.

This module proves the integrability conjunct unconditionally and records
exactly what the pointwise conjunct needs.

* **The integrability conjunct (the last printed ingredient).**
  `integrable_weightedBlockAverage_of_isBigO_gammaSigma_third` derives the
  integrability of `weightedBlockAverage` from the printed `Γ_{1/3}` tail
  alone, through the second moment of a `Γ_{1/3}` variable
  (`integral_sq_le_of_isBigO_gammaSigma_third`,
  `RHSTerm3SourceGapsB.lean`): each per-cube remainder is in
  `L²(P)`, the lattice average over the descendants is in `L²(P)` by the
  triangle inequality, and the `∇w`-weight of each outer cube is in `L²(P)` by
  the side condition `hsq`.  The side condition `hsq` is carried by the whole
  chain: there is no measurability datum on the response `w` at this surface.
* **The pointwise conjunct is the *tested* reading, and it is strictly
  stronger than the print.**  The conjunct of `_hBlup` compares the operator norm
  `|b_{L'} − b_ℓ|` with `|b_ℓ| + 2 q(e) + Zrem`, where `q(e) =
  (k_ℓ − k_{L'})^t σ_{ℓ,*}^{-1} (k_ℓ − k_{L'})` is the quadratic form
  *tested at the single direction* `e` of the proof of `l.RHS.term3`.  The deterministic core
  `blupbounds_operatorNorm_le`
  (`BellUpscaleBoundRemainder.lean`) concludes the same left side with
  the *operator-norm square* `|σ_{ℓ,*}^{-1/2} (k_ℓ − k_{L'})|²` in the
  quadratic slot, and the latter dominates the former.  Substituting the smaller tested form
  in an upper bound is therefore *not* implied: the printed display gives the
  conjunct only with the extra nonnegative amount `2 (|σ_{ℓ,*}^{-1/2} (k_ℓ − k_{L'})|² −
  q(e))` added to the remainder.  The chain consumes the
  operator-norm reading while the obligation `_hBlup` asks for the tested one.
* **The scale quantifier of the tail.**  The tail binder of `_hBlup` is
  `∀ z : TriadicCube d`.  The assembly supplies it on the cubes of the
  localization scale, `z.scale = nn`
  (`blupRemainderZrem_gammaSigma_one_third`): the `D`-estimate is scale-free in
  the cube, but the stream tail
  `isBigO_gammaSigma_translatedStreamNormSq_originCube` needs the cube's scale
  at most the inner scale `ℓ`, so cubes of larger scale are not covered.  Every
  use of `Zrem` in the chain is at the scale-`nn` cubes, so this is a quantifier mismatch
  rather than a mathematical gap; it is recorded and not repaired here.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal
open scoped BigOperators
open scoped MatrixOrder

variable {d : ℕ}

noncomputable section

/-! ## Positivity of the printed remainder constants -/

/-- The printed D-estimate constant is positive: the `Γ₁` triangle constant
times `M + M²` with `M = oscTailConst d > 0`. -/
theorem dEstimateConst_pos {d : ℕ} (hd : 0 < d) : 0 < dEstimateConst d := by
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hosc : 0 < oscTailConst d := by
    unfold oscTailConst
    refine mul_pos ?_ IndependentSums.gammaTriangleConst_pos
    unfold upperShellFluxConst
    exact div_pos (mul_pos (pow_pos hdR 2) (Real.sqrt_pos.mpr hdR)) (by norm_num)
  unfold dEstimateConst
  exact mul_pos IndependentSums.gammaTriangleConst_pos
    (add_pos_of_pos_of_nonneg hosc (sq_nonneg _))

/-- The `d`-only constant of the printed `Γ_{1/3}` remainder is positive. -/
theorem blupRemainderConst_pos {d : ℕ} (hd : 0 < d) : 0 < blupRemainderConst d := by
  unfold blupRemainderConst
  exact mul_pos (mul_pos (orliczProductConst_pos 1 1) (dEstimateConst_pos hd))
    (blupQuadTailConst_pos hd)

/-! ## The integrability of the weighted block average -/

/-- **The integrability conjunct of `e.blupbounds.remainder`**: for a remainder
`Zrem` that is measurable in the shell sequence at every cube and has the
printed `Γ_{1/3}` tail at the amplitude `K` on the cubes of the localization
scale `n`, the `∇w`-weighted double lattice average of `Zrem` over the
descendants is integrable.

The proof reads the Hoelder step of the proof of `l.RHS.term3` backwards: each `Zrem · z`
is square integrable by `integral_sq_le_of_isBigO_gammaSigma_third`, the lattice
average of the descendants is square integrable by the triangle inequality for
finitely many `L²(P)` functions, and the `∇w`-weight of each outer cube is
square integrable by `hsq`; a product of square integrable functions is
integrable (`MemLp.integrable_mul`), and the outer average is a finite sum of
such products.

`hsq` is the `L²(P)` side condition of the whole chain: there is no
measurability datum on the response `w` at this surface, so it is carried. -/
theorem integrable_weightedBlockAverage_of_isBigO_gammaSigma_third {n k m : ℕ}
    (hkn : n ≤ k) (hkm : k ≤ m)
    {P : ProbabilityMeasure (ShellSeq d)}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ))))
    {K : ℝ} (hK : 0 < K)
    {Zrem : ShellSeq d → TriadicCube d → ℝ}
    (hZremMeas : ∀ z : TriadicCube d, Measurable fun omega : ShellSeq d => Zrem omega z)
    (hZremTail : ∀ z : TriadicCube d, z.scale = ((n : ℕ) : ℤ) →
      IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3))
        (fun omega : ShellSeq d => Zrem omega z) K)
    (hsq : ∀ z' ∈ largeCubeSubcubes d k m,
      MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad))) 2 P.toMeasure) :
    Integrable (fun omega : ShellSeq d =>
      weightedBlockAverage d n k m ((w omega).toH1Function.grad) (Zrem omega))
      P.toMeasure := by
  classical
  have hMemLp : ∀ z : TriadicCube d, z.scale = ((n : ℕ) : ℤ) →
      MemLp (fun omega : ShellSeq d => Zrem omega z) 2 P.toMeasure := fun z hz =>
    (memLp_two_iff_integrable_sq (hZremMeas z).aestronglyMeasurable).2
      (integral_sq_le_of_isBigO_gammaSigma_third hK (hZremMeas z) (hZremTail z hz)).1
  have hscale : ∀ z' ∈ largeCubeSubcubes d k m, ∀ z ∈ descendantsAtDepth z' (k - n),
      z.scale = ((n : ℕ) : ℤ) := by
    intro z' hz' z hz
    have hsub := scale_eq_sub_of_mem_descendantsAtDepth hz
    have hz'k : z'.scale = (k : ℤ) := scale_of_mem_largeCubeSubcubes hkm hz'
    have hcast : (((k - n : ℕ) : ℤ)) = (k : ℤ) - (n : ℤ) := by omega
    rw [hz'k, hcast] at hsub
    linarith only [hsub]
  have hAvg : ∀ z' ∈ largeCubeSubcubes d k m,
      MemLp (fun omega : ShellSeq d =>
        (((descendantsAtDepth z' (k - n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (k - n), Zrem omega z) 2 P.toMeasure :=
    fun z' hz' => (memLp_finsetSum (descendantsAtDepth z' (k - n))
      (fun z hz => hMemLp z (hscale z' hz' z hz))).const_mul _
  have hInt : ∀ z' ∈ largeCubeSubcubes d k m,
      Integrable (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z')
            ((w omega).toH1Function.grad)) *
          ((((descendantsAtDepth z' (k - n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (k - n), Zrem omega z)) P.toMeasure :=
    fun z' hz' => (hsq z' hz').integrable_mul (hAvg z' hz')
  simpa only [weightedBlockAverage] using
    (MeasureTheory.integrable_finsetSum (largeCubeSubcubes d k m) hInt).const_mul
      (((largeCubeSubcubes d k m).card : ℝ)⁻¹)

/-- **The integrability conjunct of `e.blupbounds.remainder` at the
remainder witness**: the `∇w`-weighted block average of `blupRemainderZrem` is
integrable.  This is the fourth conjunct of the `_hBlup` slot at the
concrete witness of `BlupRemainderAssembly.lean`, its printed
`Γ_{1/3}` tail being `blupRemainderZrem_gammaSigma_one_third`.

The amplitude `blupRemainderConst d * ν^{-3} L 3^{-(ℓ-nn)}` is positive because
`blupRemainderConst_pos` holds and `nn < ℓ < L`. -/
theorem integrable_weightedBlockAverage_blupRemainderZrem [NeZero d]
    {P : ProbabilityMeasure (ShellSeq d)} {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (nn ell L k m : ℕ) (hnl : nn < ell) (hlL : ell < L)
    (hkn : nn ≤ k) (hkm : k ≤ m)
    (e : Vec d) (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ))))
    (hsq : ∀ z' ∈ largeCubeSubcubes d k m,
      MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad))) 2 P.toMeasure) :
    Integrable (fun omega : ShellSeq d =>
      weightedBlockAverage d nn k m ((w omega).toH1Function.grad)
        (blupRemainderZrem nu nn ell L e omega)) P.toMeasure := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hPrefix.dimension
  have hnu3 : (0 : ℝ) < nu ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hnu _
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(((ell - nn : ℕ) : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hL : (0 : ℝ) < ((L : ℕ) : ℝ) := by
    have hLnat : 0 < L := by omega
    exact_mod_cast hLnat
  refine integrable_weightedBlockAverage_of_isBigO_gammaSigma_third (P := P) hkn hkm w
    (mul_pos (mul_pos (mul_pos (blupRemainderConst_pos hd) hnu3) hL) h3)
    (fun z => measurable_blupRemainderZrem hnu nn ell L e z) ?_ hsq
  intro z hz
  exact blupRemainderZrem_gammaSigma_one_third hnu hnu1 hPrefix hJ2 hJ3 hJ4 nn ell L
    hnl hlL e he z hz

/-! ## The tested reading of the printed quadratic slot -/

end

end SuperdiffusionCLT.Section3.Terms
