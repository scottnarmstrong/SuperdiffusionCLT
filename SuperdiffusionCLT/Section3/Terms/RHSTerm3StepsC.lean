/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3StepsB
public import SuperdiffusionCLT.Probability.OrliczIndexWeakening

/-!
# `l.RHS.term3`, Steps 2 and 3: `e.RHS.term3.A` and the coarse-block average

The second half of the decomposition `e.w-flux-indepen-decomp`, the display
`e.RHS.term3.A`, and the first three steps of `e.bL.to.bhomell`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Probability

noncomputable section

variable {d : ℕ}

/-! ## `l.RHS.term3#w-average-difference` -/

/-- The exponent bookkeeping of the estimate of `l.RHS.term3#w-average-difference`:
`(C_p 3^k)(C_w 3^{-ℓ'}ν^{-1/2})(C_b(L'ν⁻¹)^{1/2})` is
`C_pC_wC_b 3^{k−ℓ'}ν⁻¹(L')^{1/2}`, which the standing ranges `ν ≤ 1`,
`1 ≤ L'` and the rounding bound `3^{k−ℓ'} ≤ 3·3^{−(ℓ'−ℓ)/4}` turn into the
printed `C 3^{−(ℓ'−ℓ)/4}(L')²ν^{−5/2}`. -/
private theorem w_average_difference_arith {nu LP Cp Cw Cb kk el rr : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hLP : 1 ≤ LP)
    (hCp : 0 ≤ Cp) (hCw : 0 ≤ Cw) (hCb : 0 ≤ Cb)
    (hround : (3 : ℝ) ^ (kk - el) ≤ 3 * (3 : ℝ) ^ (-(rr / 4))) :
    Cp * (3 : ℝ) ^ kk * (Cw * (3 : ℝ) ^ (-el) * nu ^ (-(1 : ℝ) / 2)) *
        (Cb * (LP * nu⁻¹) ^ ((1 : ℝ) / 2)) ≤
      3 * (Cp * Cw * Cb) * (3 : ℝ) ^ (-(rr / 4)) * LP ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2) := by
  have hLPnn : (0 : ℝ) ≤ LP := le_trans zero_le_one hLP
  have hinvnn : (0 : ℝ) ≤ nu⁻¹ := le_of_lt (inv_pos.2 hnu)
  have hsplit : (LP * nu⁻¹) ^ ((1 : ℝ) / 2) = LP ^ ((1 : ℝ) / 2) * nu ^ (-(1 : ℝ) / 2) := by
    rw [Real.mul_rpow hLPnn hinvnn, Real.inv_rpow hnu.le, ← Real.rpow_neg hnu.le]
    ring_nf
  have hnupow : nu ^ (-(1 : ℝ) / 2) * nu ^ (-(1 : ℝ) / 2) = nu ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hnu]
    norm_num
  have hthree : (3 : ℝ) ^ kk * (3 : ℝ) ^ (-el) = (3 : ℝ) ^ (kk - el) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    ring_nf
  have hid : Cp * (3 : ℝ) ^ kk * (Cw * (3 : ℝ) ^ (-el) * nu ^ (-(1 : ℝ) / 2)) *
      (Cb * (LP * nu⁻¹) ^ ((1 : ℝ) / 2)) =
      (Cp * Cw * Cb) * ((3 : ℝ) ^ (kk - el)) * (LP ^ ((1 : ℝ) / 2) * nu ^ (-(1 : ℝ))) := by
    rw [hsplit, ← hthree, ← hnupow]
    ring
  have hCnn : (0 : ℝ) ≤ Cp * Cw * Cb := by positivity
  have hLPle : LP ^ ((1 : ℝ) / 2) ≤ LP ^ (2 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hLP (by norm_num : (1 : ℝ) / 2 ≤ (2 : ℕ))
    rwa [Real.rpow_natCast] at h
  have hnule : nu ^ (-(1 : ℝ)) ≤ nu ^ (-(5 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hnu hnu1 (by norm_num)
  have hLPnn' : (0 : ℝ) ≤ LP ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hLPnn _
  have hnunn : (0 : ℝ) ≤ nu ^ (-(1 : ℝ)) := Real.rpow_nonneg hnu.le _
  have hlast : LP ^ ((1 : ℝ) / 2) * nu ^ (-(1 : ℝ)) ≤ LP ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2) :=
    mul_le_mul hLPle hnule hnunn (pow_nonneg hLPnn 2)
  have hthreenn : (0 : ℝ) ≤ (3 : ℝ) ^ (kk - el) := Real.rpow_nonneg (by norm_num) _
  have hrrnn : (0 : ℝ) ≤ 3 * (3 : ℝ) ^ (-(rr / 4)) := by positivity
  have hfinnn : (0 : ℝ) ≤ LP ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2) := by
    exact mul_nonneg (pow_nonneg hLPnn 2) (Real.rpow_nonneg hnu.le _)
  calc Cp * (3 : ℝ) ^ kk * (Cw * (3 : ℝ) ^ (-el) * nu ^ (-(1 : ℝ) / 2)) *
        (Cb * (LP * nu⁻¹) ^ ((1 : ℝ) / 2))
      = (Cp * Cw * Cb) * ((3 : ℝ) ^ (kk - el)) *
        (LP ^ ((1 : ℝ) / 2) * nu ^ (-(1 : ℝ))) := hid
    _ ≤ (Cp * Cw * Cb) * (3 * (3 : ℝ) ^ (-(rr / 4))) *
        (LP ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hround hCnn) hlast
          (mul_nonneg hLPnn' hnunn) (mul_nonneg hCnn hrrnn)
    _ = 3 * (Cp * Cw * Cb) * (3 : ℝ) ^ (-(rr / 4)) * LP ^ (2 : ℕ) *
        nu ^ (-(5 : ℝ) / 2) := by ring

/-- **`l.RHS.term3#w-average-difference`**,
the second term of
`e.w-flux-indepen-decomp`, in which the two cube averages of `∇w` are
compared across the two nested scales `n < k`, costs
`C3^{−(ℓ'−ℓ)/4}(L')²ν^{−5/2}`.

Free binders: `bHalfDiff omega z' z` is the printed
`|b_{L'}^{1/2}(z+cu_n)((∇w)_{z+cu_n} − (∇w)_{z'+cu_k})|²`, `normFlux` is as in
`coarse_average_CS`, `bNormSq omega` is `|b_{L'}(cu_n)|²` and
`hessianL4 omega` is `‖∇²w‖⁴_{L̲⁴(cu_m)}`.  The *difference of the two cube
averages* itself is available (`volumeAverageVec`), so the printed fourth moment
`avsum E[|(∇w)_{z+cu_n} − (∇w)_{z'+cu_k}|⁴]` is written out.

The paper's steps enter as hypotheses in their printed shapes:

* `hInsert` — the `b_{L'}^{±1/2}` insertion (same
  invertibility gap as in `coarse_average_CS`);
* `hHolder` — the pointwise bound `|b^{1/2}x|² ≤ |b||x|²` and
  the Cauchy-Schwarz decoupling of the pair, together with the stationarity
  that replaces `avsum_z E[|b_{L'}(z+cu_n)|²]` by `E[|b_{L'}(cu_n)|²]`; the
  paper performs all three silently;
* `hEllip` — `E[|b_{L'}(cu_n)|²]^{1/4} ≤ C(ν⁻¹L')^{1/2}`, the
  `l.bfAm.ellip`/`e.Enaught.mixing` envelope (compare
  `envelopeRescale_ellipticity`);
* `hPoincare` — the two-scale Poincaré bound
  `E[avsum|(∇w)_{z+cu_n} − (∇w)_{z'+cu_k}|⁴]^{1/4} ≤ C3^k E[‖∇²w‖⁴]^{1/4}`,
  which the paper compresses: it is a Poincaré-type bound
  across two nested cube scales, asserted without proof;
* `hNablaw` — `e.nablaw.Lt` (`l.w.basic.regbounds`, half A) in its fourth
  moment form together with `e.p-bound-crude` `|p| ≤ ν^{-1/2}`,
  as in the paper's "we used `e.nablaw.Lt` and `e.p-bound-crude`".

The Cauchy-Schwarz step against `e.flux-additivity-estimate-in-an-lemma`, the
absorption `(δ + η_L)^{1/2} ≤ 1`, and the whole exponent bookkeeping are
proved. -/
theorem w_average_difference
    (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (hell : S.ell ≤ S.ellPrime) (hnk : S.n ≤ coarseBlockScale d S)
    (hkm : coarseBlockScale d S ≤ S.m) (hLP : 1 ≤ ((S.LPrime : ℕ) : ℝ))
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (bHalfDiff : ShellSeq d → TriadicCube d → TriadicCube d → ℝ)
    (normFlux : ShellSeq d → TriadicCube d → ℝ)
    (bNormSq hessianL4 : ShellSeq d → ℝ)
    {delta etaL Cb Cp Cw : ℝ} (hCb : 0 ≤ Cb) (hCp : 0 ≤ Cp) (hCw : 0 ≤ Cw)
    (hde1 : delta + etaL ≤ 1)
    (hbDnn : ∀ (omega : ShellSeq d) (z' z : TriadicCube d), 0 ≤ bHalfDiff omega z' z)
    (hnfnn : ∀ (omega : ShellSeq d) (z : TriadicCube d), 0 ≤ normFlux omega z)
    (hbNnn : ∀ omega : ShellSeq d, 0 ≤ bNormSq omega)
    (hInsert : ∀ omega : ShellSeq d, ∀ p ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      vecDot (volumeAverageVec (openCubeSet p.2) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet p.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (uMgrad omega y - uNGlued omega y))) ≤
        bHalfDiff omega p.1 p.2 ^ ((1 : ℝ) / 2) * normFlux omega p.2 ^ ((1 : ℝ) / 2))
    (hFluxAvg : ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ z ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d, normFlux omega z ∂P.toMeasure ≤ delta + etaL)
    (hHolder : (((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ p ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
            ∫ omega : ShellSeq d, bHalfDiff omega p.1 p.2 ∂P.toMeasure) ^ ((1 : ℝ) / 2) ≤
      (((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ p ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
            ∫ omega : ShellSeq d,
              vecNormSq (volumeAverageVec (openCubeSet p.2) ((w omega).toH1Function.grad) -
                  volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad)) ^ (2 : ℝ)
              ∂P.toMeasure) ^ ((1 : ℝ) / 4) *
        (∫ omega : ShellSeq d, bNormSq omega ∂P.toMeasure) ^ ((1 : ℝ) / 4))
    (hEllip : (∫ omega : ShellSeq d, bNormSq omega ∂P.toMeasure) ^ ((1 : ℝ) / 4) ≤
      Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((1 : ℝ) / 2))
    (hPoincare : (((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ p ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
            ∫ omega : ShellSeq d,
              vecNormSq (volumeAverageVec (openCubeSet p.2) ((w omega).toH1Function.grad) -
                  volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad)) ^ (2 : ℝ)
              ∂P.toMeasure) ^ ((1 : ℝ) / 4) ≤
      Cp * (3 : ℝ) ^ ((coarseBlockScale d S : ℕ) : ℝ) *
        (∫ omega : ShellSeq d, hessianL4 omega ∂P.toMeasure) ^ ((1 : ℝ) / 4))
    (hNablaw : (∫ omega : ShellSeq d, hessianL4 omega ∂P.toMeasure) ^ ((1 : ℝ) / 4) ≤
      Cw * (3 : ℝ) ^ (-((S.ellPrime : ℕ) : ℝ)) * nu ^ (-(1 : ℝ) / 2))
    (hLHSint : Integrable (fun omega : ShellSeq d =>
      ((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ p ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
          vecDot (volumeAverageVec (openCubeSet p.2) ((w omega).toH1Function.grad) -
              volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad))
            (volumeAverageVec (openCubeSet p.2)
              (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (uMgrad omega y - uNGlued omega y)))) P.toMeasure)
    (hProdInt : ∀ p ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      Integrable (fun omega : ShellSeq d =>
        bHalfDiff omega p.1 p.2 ^ ((1 : ℝ) / 2) * normFlux omega p.2 ^ ((1 : ℝ) / 2))
        P.toMeasure)
    (hMemb : ∀ p ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d => bHalfDiff omega p.1 p.2 ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure)
    (hMemf : ∀ p ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d => normFlux omega p.2 ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure) :
    ∫ omega : ShellSeq d,
        ((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ p ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
            vecDot (volumeAverageVec (openCubeSet p.2) ((w omega).toH1Function.grad) -
                volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad))
              (volumeAverageVec (openCubeSet p.2)
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure ≤
      3 * (Cp * Cw * Cb) * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) *
        ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2) := by
  classical
  set T : Finset ((_ : TriadicCube d) × TriadicCube d) :=
    coarsePairs d S.n (coarseBlockScale d S) S.m with hT
  have hBavg : ((T.card : ℝ))⁻¹ *
      ∑ p ∈ T, ∫ omega : ShellSeq d, normFlux omega p.2 ∂P.toMeasure ≤ delta + etaL := by
    rw [hT, avsum_coarsePairs_snd hnk hkm
      (fun z => ∫ omega : ShellSeq d, normFlux omega z ∂P.toMeasure)]
    exact hFluxAvg
  have hbAvgnn : (0 : ℝ) ≤ ((T.card : ℝ))⁻¹ *
      ∑ p ∈ T, ∫ omega : ShellSeq d, bHalfDiff omega p.1 p.2 ∂P.toMeasure :=
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun p _ =>
      MeasureTheory.integral_nonneg fun omega => hbDnn omega p.1 p.2)
  have hdenn : (0 : ℝ) ≤ delta + etaL :=
    le_trans (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun p _ =>
      MeasureTheory.integral_nonneg fun omega => hnfnn omega p.2)) hBavg
  have hmain := integral_avsum_le_rpow_half_mul (mu := P.toMeasure) T
    (coarsePairs_nonempty d S.n (coarseBlockScale d S) S.m)
    (fun omega p => vecDot
      (volumeAverageVec (openCubeSet p.2) ((w omega).toH1Function.grad) -
        volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad))
      (volumeAverageVec (openCubeSet p.2)
        (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (uMgrad omega y - uNGlued omega y))))
    (fun omega p => bHalfDiff omega p.1 p.2) (fun omega p => normFlux omega p.2)
    (fun omega p => hbDnn omega p.1 p.2) (fun omega p => hnfnn omega p.2)
    hInsert hBavg hLHSint hProdInt hMemb hMemf
  have habsorb : (delta + etaL) ^ ((1 : ℝ) / 2) ≤ 1 := by
    have h := Real.rpow_le_rpow hdenn hde1 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
    rwa [Real.one_rpow] at h
  have hstep2 : (((T.card : ℝ))⁻¹ *
        ∑ p ∈ T, ∫ omega : ShellSeq d, bHalfDiff omega p.1 p.2 ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
      (delta + etaL) ^ ((1 : ℝ) / 2) ≤
      (((T.card : ℝ))⁻¹ *
        ∑ p ∈ T, ∫ omega : ShellSeq d, bHalfDiff omega p.1 p.2 ∂P.toMeasure) ^
          ((1 : ℝ) / 2) := by
    nth_rewrite 2 [← mul_one ((((T.card : ℝ))⁻¹ *
      ∑ p ∈ T, ∫ omega : ShellSeq d, bHalfDiff omega p.1 p.2 ∂P.toMeasure) ^ ((1 : ℝ) / 2))]
    exact mul_le_mul_of_nonneg_left habsorb (Real.rpow_nonneg hbAvgnn _)
  have hEllipnn : (0 : ℝ) ≤ Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((1 : ℝ) / 2) := by
    have : (0 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) * nu⁻¹ :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt (inv_pos.2 hnu))
    exact mul_nonneg hCb (Real.rpow_nonneg this _)
  have hHnn : (0 : ℝ) ≤ Cw * (3 : ℝ) ^ (-((S.ellPrime : ℕ) : ℝ)) * nu ^ (-(1 : ℝ) / 2) := by
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((S.ellPrime : ℕ) : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have h2 : (0 : ℝ) ≤ nu ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hnu.le _
    exact mul_nonneg (mul_nonneg hCw h1) h2
  have hPnn : (0 : ℝ) ≤ Cp * (3 : ℝ) ^ ((coarseBlockScale d S : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ (3 : ℝ) ^ ((coarseBlockScale d S : ℕ) : ℝ) :=
      Real.rpow_nonneg (by norm_num) _
    exact mul_nonneg hCp this
  have hPoincare' := hPoincare.trans (mul_le_mul_of_nonneg_left hNablaw hPnn)
  have hprod : (((T.card : ℝ))⁻¹ *
        ∑ p ∈ T, ∫ omega : ShellSeq d, bHalfDiff omega p.1 p.2 ∂P.toMeasure) ^
        ((1 : ℝ) / 2) ≤
      Cp * (3 : ℝ) ^ ((coarseBlockScale d S : ℕ) : ℝ) *
        (Cw * (3 : ℝ) ^ (-((S.ellPrime : ℕ) : ℝ)) * nu ^ (-(1 : ℝ) / 2)) *
        (Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((1 : ℝ) / 2)) := by
    exact hHolder.trans (mul_le_mul hPoincare' hEllip
      (Real.rpow_nonneg (MeasureTheory.integral_nonneg hbNnn) _) (mul_nonneg hPnn hHnn))
  exact ((hmain.trans hstep2).trans hprod).trans
    (w_average_difference_arith hnu hnu1 hLP hCp hCw hCb
      (rpow_coarseBlockScale_sub_ellPrime_le hd S hell))

/-! ## `e.RHS.term3.A` -/

private theorem vecDot_sub_left'' (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- **`e.w-flux-indepen-decomp`**: the coarse-grained average term of
`e.additivity.defect.splitting` splits into the term in which the `∇w` factor has been
coarsened to the scale-`k` cube and the term carrying the coarse-versus-fine difference of
the `∇w` averages.  With the triadic carriers of the development this is the lattice
partition of the large cube into subcubes together with add-and-subtract. -/
theorem avsum_pairing_decomposition {n k m : ℕ} (hnk : n ≤ k) (hkm : k ≤ m)
    (g F : TriadicCube d → Vec d) :
    ((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
        ∑ z ∈ largeCubeSubcubes d n m, vecDot (g z) (F z) =
      ((coarsePairs d n k m).card : ℝ)⁻¹ *
          ∑ p ∈ coarsePairs d n k m, vecDot (g p.1) (F p.2) +
        ((coarsePairs d n k m).card : ℝ)⁻¹ *
          ∑ p ∈ coarsePairs d n k m, vecDot (g p.2 - g p.1) (F p.2) := by
  classical
  rw [← avsum_coarsePairs_snd hnk hkm (fun z => vecDot (g z) (F z)), ← mul_add,
    ← Finset.sum_add_distrib]
  refine congrArg (fun t => ((coarsePairs d n k m).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [vecDot_sub_left'']
  ring

/-- **`e.RHS.term3.A`**:
the coarse-grained average term of `e.additivity.defect.splitting` is bounded
by the coarse-block second moment of `∇w` times `(δ + Cη_L)^{1/2}`, plus the
coarse-versus-fine averaging error `C3^{-(ℓ'−ℓ)/4}(L')²ν^{−5/2}`.

The left side is *verbatim* the second summand produced by
`additivity_defect_splitting`, so the two theorems compose.  The two
hypotheses are the conclusions of `coarse_average_CS` and
`w_average_difference` verbatim; the decomposition `e.w-flux-indepen-decomp`
and the additivity of the Bochner integral are proved here. -/
theorem rhs_term3_A
    {nu : ℝ} (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) {k : ℕ}
    (hnk : S.n ≤ k) (hkm : k ≤ S.m)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (bHalfW : ShellSeq d → TriadicCube d → TriadicCube d → ℝ)
    {delta etaL Cerr : ℝ}
    (hCS : ∫ omega : ShellSeq d,
        ((coarsePairs d S.n k S.m).card : ℝ)⁻¹ * ∑ p ∈ coarsePairs d S.n k S.m,
          vecDot (volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad))
            (volumeAverageVec (openCubeSet p.2)
              (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure ≤
      (((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
          ∑ z' ∈ largeCubeSubcubes d k S.m,
            (((descendantsAtDepth z' (k - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (k - S.n),
                ∫ omega : ShellSeq d, bHalfW omega z' z ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
        (delta + etaL) ^ ((1 : ℝ) / 2))
    (hDiff : ∫ omega : ShellSeq d,
        ((coarsePairs d S.n k S.m).card : ℝ)⁻¹ * ∑ p ∈ coarsePairs d S.n k S.m,
          vecDot (volumeAverageVec (openCubeSet p.2) ((w omega).toH1Function.grad) -
              volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad))
            (volumeAverageVec (openCubeSet p.2)
              (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure ≤
      Cerr * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) *
        ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2))
    (hInt1 : Integrable (fun omega : ShellSeq d =>
      ((coarsePairs d S.n k S.m).card : ℝ)⁻¹ * ∑ p ∈ coarsePairs d S.n k S.m,
        vecDot (volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet p.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (uMgrad omega y - uNGlued omega y)))) P.toMeasure)
    (hInt2 : Integrable (fun omega : ShellSeq d =>
      ((coarsePairs d S.n k S.m).card : ℝ)⁻¹ * ∑ p ∈ coarsePairs d S.n k S.m,
        vecDot (volumeAverageVec (openCubeSet p.2) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet p.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (uMgrad omega y - uNGlued omega y)))) P.toMeasure) :
    ∫ omega : ShellSeq d,
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (volumeAverageVec (openCubeSet R)
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure ≤
      (((largeCubeSubcubes d k S.m).card : ℝ)⁻¹ *
          ∑ z' ∈ largeCubeSubcubes d k S.m,
            (((descendantsAtDepth z' (k - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (k - S.n),
                ∫ omega : ShellSeq d, bHalfW omega z' z ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
          (delta + etaL) ^ ((1 : ℝ) / 2) +
        Cerr * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) *
          ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2) := by
  have hpt : ∀ omega : ShellSeq d,
      ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (volumeAverageVec (openCubeSet R)
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (uMgrad omega y - uNGlued omega y))) =
        ((coarsePairs d S.n k S.m).card : ℝ)⁻¹ * ∑ p ∈ coarsePairs d S.n k S.m,
            vecDot (volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad))
              (volumeAverageVec (openCubeSet p.2)
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (uMgrad omega y - uNGlued omega y))) +
          ((coarsePairs d S.n k S.m).card : ℝ)⁻¹ * ∑ p ∈ coarsePairs d S.n k S.m,
            vecDot (volumeAverageVec (openCubeSet p.2) ((w omega).toH1Function.grad) -
                volumeAverageVec (openCubeSet p.1) ((w omega).toH1Function.grad))
              (volumeAverageVec (openCubeSet p.2)
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (uMgrad omega y - uNGlued omega y))) := fun omega =>
    avsum_pairing_decomposition hnk hkm
      (fun z => volumeAverageVec (openCubeSet z) ((w omega).toH1Function.grad))
      (fun z => volumeAverageVec (openCubeSet z)
        (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (uMgrad omega y - uNGlued omega y)))
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_add hInt1 hInt2]
  exact add_le_add hCS hDiff

/-! ## The weighted coarse-block average -/

/-- **The `∇w`-weighted double lattice average**
`avsum_{z'∈3^kℤ^d∩cu_m}|(∇w)_{z'+cu_k}|² avsum_{z∈z'+3^nℤ^d∩cu_k} F(z)` of the
carrier swap and the Hoelder display in the proof of `l.RHS.term3`. -/
def weightedBlockAverage (d n k m : ℕ) (g : Vec d → Vec d) (F : TriadicCube d → ℝ) : ℝ :=
  ((largeCubeSubcubes d k m).card : ℝ)⁻¹ *
    ∑ z' ∈ largeCubeSubcubes d k m,
      vecNormSq (volumeAverageVec (openCubeSet z') g) *
        ((((descendantsAtDepth z' (k - n)).card : ℕ) : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (k - n), F z)

theorem weightedBlockAverage_add {n k m : ℕ} (g : Vec d → Vec d) (F G : TriadicCube d → ℝ) :
    weightedBlockAverage d n k m g (fun z => F z + G z) =
      weightedBlockAverage d n k m g F + weightedBlockAverage d n k m g G := by
  simp only [weightedBlockAverage]
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine congrArg (fun t => ((largeCubeSubcubes d k m).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [Finset.sum_add_distrib, mul_add]
  ring

theorem weightedBlockAverage_const_mul {n k m : ℕ} (g : Vec d → Vec d) (c : ℝ)
    (F : TriadicCube d → ℝ) :
    weightedBlockAverage d n k m g (fun z => c * F z) =
      c * weightedBlockAverage d n k m g F := by
  have hbody : ∀ z' ∈ largeCubeSubcubes d k m,
      vecNormSq (volumeAverageVec (openCubeSet z') g) *
          ((((descendantsAtDepth z' (k - n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (k - n), c * F z) =
        c * (vecNormSq (volumeAverageVec (openCubeSet z') g) *
          ((((descendantsAtDepth z' (k - n)).card : ℕ) : ℝ)⁻¹ *
            ∑ z ∈ descendantsAtDepth z' (k - n), F z)) := by
    intro z' _
    rw [← Finset.mul_sum]
    ring
  simp only [weightedBlockAverage]
  rw [Finset.sum_congr rfl hbody, ← Finset.mul_sum]
  ring

/-! ## `e.bL.to.bhomell.pre0zz` -/

/-! ## `l.RHS.term3#sigma-star-carrier-swap` -/

/-! ## `l.RHS.term3#holder-split` -/

end

end SuperdiffusionCLT.Section3.Terms
