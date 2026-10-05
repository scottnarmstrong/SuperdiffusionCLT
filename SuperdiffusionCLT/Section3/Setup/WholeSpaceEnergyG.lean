/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyF

/-!
# `l.LHS.term1` from the per-shell data

The statement of `l.LHS.term1` together with its proof: the lower bound
`e.nabla.w.lower.bound` with the summed display `e.wN.wD.with.average.error` no longer
assumed but produced from the two per-shell displays and the geometric summation of
`WholeSpaceEnergyF.lean`.

## Main results

* `abs_toReal_sub_cStar_mul_le_lhsTerm1Const`: the bound with its constant written out.
* `vecCubeLpENorm_grad_sub_le_of_shellGapSum`: the bridge from the per-shell gaps to the
  summed display.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory
open ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.ResponseFields
open scoped BigOperators ENNReal

noncomputable section

/-! ## The constant written out -/

/-- **`l.LHS.term1` with its constant written out**: the
`∀`-body of `l_LHS_term1_constFirst` at the explicit witness
`lhsTerm1Const Cgap Cav`, which the existential statement hides.  Every
step is the printed one: `e.average.error.energy` and the
second moment of the summed display are
`lintegral_vecCubeLpENorm_sq_response_gap_le`, the next step is
`abs_toReal_sub_wholeSpaceEnergy_le`, and the last step (`e.use.nondeg.ass`)
is `abs_wholeSpaceEnergy_sub_cStar_mul_le` together with the scale identity
`L' − ℓ' = m − n`. -/
theorem abs_toReal_sub_cStar_mul_le_lhsTerm1Const
    (d : ℕ) [NeZero d] (Cgap Cav : ℝ) (hCgap : 0 < Cgap) (hCav : 0 < Cav)
    (nu : ℝ) (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    [hInv : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    (cStar K : ℝ)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d) (he : vecNormSq e = 1) (hunit : Book.Ch02.vecNorm e = 1)
    (p : Vec d) (hp : p = testVector nu S.LPrime P S.n e)
    (F : ShellSeq d → Vec d → Vec d)
    (hF : ∀ omega : ShellSeq d, F omega = fun x =>
      matVecMul (streamCutoff omega S.LPrime x -
        streamCutoff omega S.ellPrime x) p)
    (gradHatW : ShellSeq d → Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (wN : ShellSeq d →
      H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ))))
    (hwD : ∀ omega : ShellSeq d,
      IsCubeDirichletResponse (originCube d (S.m : ℤ)) (F omega) (wD omega))
    (hwN : ∀ omega : ShellSeq d,
      IsCubeNeumannResponse (originCube d (S.m : ℤ)) (F omega) (wN omega))
    (hwDmeas : AEStronglyMeasurable
      (fun omega : ShellSeq d => vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (wD omega).toH1Function.grad) P.toMeasure)
    (hFmemLp : MemLp (fun omega : ShellSeq d =>
        HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
    (hGmemLp : MemLp (fun omega : ShellSeq d =>
        HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure)
    (hproj : (hGmemLp.toLp fun omega : ShellSeq d =>
          HilbertVec.ofVec (gradHatW omega)) =
        -stationaryPotentialProjection (μ := P.toMeasure)
          (hFmemLp.toLp fun omega : ShellSeq d =>
            HilbertVec.ofVec (F omega 0)))
    (hlow : ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure ≤
        ∫⁻ omega : ShellSeq d,
          ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure)
    (hup : ∫⁻ omega : ShellSeq d,
          ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure ≤
        ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (wN omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure)
    (Y : ShellSeq d → ℝ) (hY0 : ∀ omega, 0 ≤ Y omega)
    (hYm : Measurable Y)
    (hYbig : IsBigO P.toMeasure (gammaSigma 2) Y
      (Cgap * Book.Ch02.vecNorm p))
    (Z : ℕ → ShellSeq d → ℝ) (hZm : ∀ r, Measurable (Z r))
    (hZbig : ∀ r ∈ Finset.Icc S.m S.LPrime,
      IsBigO P.toMeasure (gammaSigma 2) (Z r)
        (Cav * Book.Ch02.vecNorm p))
    (hZbound : ∀ (r : ℕ) (omega : ShellSeq d),
      Book.Ch02.vecNorm (shellFluxAverage (S.m : ℤ) omega r p) ≤ Z r omega)
    (hbridge : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => (wN omega).toH1Function.grad x -
            (wD omega).toH1Function.grad x) ≤
        ENNReal.ofReal (Y omega + Book.Ch02.vecNorm
          (∑ r ∈ Finset.Icc S.m S.LPrime,
            shellFluxAverage (S.m : ℤ) omega r p)))
    (hJ5app : |‖blockPotentialResponse P S.ellPrime S.LPrime
            (blockRegLaw_stationary hPrefix hJ2 S.ellPrime S.LPrime) e
            (memLp_originForcing_blockRegLaw hJ3 S.ellPrime S.LPrime e
              hunit)‖ ^ 2 -
          cStar * Real.log 3 * ((S.LPrime - S.ellPrime : ℕ) : ℝ)| ≤ K)
 :
    |(∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure :
            ℝ≥0∞).toReal -
        cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * vecNormSq p| ≤
      (lhsTerm1Const Cgap Cav * (1 + ((S.LPrime - S.m : ℕ) : ℝ)) + K) *
        vecNormSq p := by
  classical
  have : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure := hInv
  have hlam := sigmaBarStarInvSqrt_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hp' : p = sigmaBarStarInvSqrt nu S.LPrime P S.n • e := by
    rw [hp, testVector]
  have hpt : 0 < Book.Ch02.vecNorm p := by
    have hnorm : Book.Ch02.vecNorm p =
        |sigmaBarStarInvSqrt nu S.LPrime P S.n| * Book.Ch02.vecNorm e := by
      rw [hp']
      show ‖HilbertVec.ofVec (sigmaBarStarInvSqrt nu S.LPrime P S.n • e)‖ = _
      rw [ofVec_smul, norm_smul, Real.norm_eq_abs]
      rfl
    rw [hnorm, hunit, mul_one, abs_of_pos hlam]
    exact hlam
  set t : ℝ := Book.Ch02.vecNorm p
  have hpsq : vecNormSq p = t ^ 2 := (vecNorm_sq_eq_vecNormSq p).symm
  have ht2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  set Q : ℝ := 1 + ((S.LPrime - S.m : ℕ) : ℝ) with hQdef
  have hQ1 : (1 : ℝ) ≤ Q := by
    have h0 : (0 : ℝ) ≤ ((S.LPrime - S.m : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hQdef]
    linarith only [h0]
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ1
  set G2 : ℝ := 1 + Real.Gamma 2 with hG2def
  have hG20 : (0 : ℝ) ≤ G2 := by
    have hg := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [hG2def]
    linarith only [hg]
  have hApos : ∀ r ∈ Finset.Icc S.m S.LPrime, 0 < Cav * t :=
    fun _ _ => mul_pos hCav hpt
  have hgapB := lintegral_vecCubeLpENorm_sq_response_gap_le hJ2 hJ4 S.m
    (Finset.Icc S.m S.LPrime) p wD wN (Cgap * t) (mul_pos hCgap hpt) Y hY0 hYm
    hYbig (fun _ => Cav * t) hApos Z hZm hZbig hZbound hbridge
  have hcard : (Finset.Icc S.m S.LPrime).card = S.LPrime - S.m + 1 := by
    rw [Nat.card_Icc]
    have := hSorder.m_lt_LPrime
    omega
  have hsumconst : ∑ _r ∈ Finset.Icc S.m S.LPrime, (Cav * t) ^ 2 =
      Q * (Cav * t) ^ 2 := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul, hQdef]
    push_cast
    ring
  have hBle : 2 * ((Cgap * t) ^ 2 * G2) +
      2 * (G2 * ∑ _r ∈ Finset.Icc S.m S.LPrime, (Cav * t) ^ 2) ≤
      lhsTerm1Const Cgap Cav * Q * vecNormSq p := by
    have ha0 : (0 : ℝ) ≤ 2 * G2 * Cgap ^ 2 := by positivity
    have hQt : t ^ 2 ≤ Q * t ^ 2 := le_mul_of_one_le_left ht2 hQ1
    have hQt0 : (0 : ℝ) ≤ Q * t ^ 2 := mul_nonneg hQ0 ht2
    have hmax : 2 * G2 * Cgap ^ 2 + 2 * G2 * Cav ^ 2 ≤
        lhsTerm1Const Cgap Cav := by
      have h := le_max_right (1 : ℝ)
        (2 * (1 + Real.Gamma 2) * (Cgap ^ 2 + Cav ^ 2))
      rw [lhsTerm1Const, hG2def]
      have hring : 2 * (1 + Real.Gamma 2) * Cgap ^ 2 +
          2 * (1 + Real.Gamma 2) * Cav ^ 2 =
          2 * (1 + Real.Gamma 2) * (Cgap ^ 2 + Cav ^ 2) := by ring
      rw [hring]
      exact h
    calc 2 * ((Cgap * t) ^ 2 * G2) +
        2 * (G2 * ∑ _r ∈ Finset.Icc S.m S.LPrime, (Cav * t) ^ 2)
        = 2 * G2 * Cgap ^ 2 * t ^ 2 + 2 * G2 * Cav ^ 2 * (Q * t ^ 2) := by
          rw [hsumconst]
          ring
      _ ≤ 2 * G2 * Cgap ^ 2 * (Q * t ^ 2) + 2 * G2 * Cav ^ 2 * (Q * t ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hQt ha0) le_rfl
      _ = (2 * G2 * Cgap ^ 2 + 2 * G2 * Cav ^ 2) * (Q * t ^ 2) := by ring
      _ ≤ lhsTerm1Const Cgap Cav * (Q * t ^ 2) :=
          mul_le_mul_of_nonneg_right hmax hQt0
      _ = lhsTerm1Const Cgap Cav * Q * vecNormSq p := by
          rw [hpsq]
          ring
  have hBnn : (0 : ℝ) ≤ lhsTerm1Const Cgap Cav * Q * vecNormSq p := by
    have h1 : (0 : ℝ) ≤ lhsTerm1Const Cgap Cav :=
      le_trans zero_le_one (one_le_lhsTerm1Const Cgap Cav)
    have h2 : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
    positivity
  have hgapB' : ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
      (fun x => (wN omega).toH1Function.grad x -
        (wD omega).toH1Function.grad x) ^ (2 : ℕ) ∂P.toMeasure ≤
      ENNReal.ofReal (lhsTerm1Const Cgap Cav * Q * vecNormSq p) :=
    hgapB.trans (ENNReal.ofReal_le_ofReal hBle)
  have hEnergyGap := abs_toReal_sub_wholeSpaceEnergy_le hwD hwN hwDmeas hGmemLp
    hlow hup hBnn hgapB'
  have hnm : S.ellPrime ≤ S.LPrime :=
    le_of_lt (lt_trans hSorder.ellPrime_lt_m hSorder.m_lt_LPrime)
  have hscale : ((S.LPrime - S.ellPrime : ℕ) : ℝ) = ((S.m - S.n : ℕ) : ℝ) := by
    rw [S.LPrime_sub_ellPrime_eq_m_sub_n]
  have hnondeg := abs_wholeSpaceEnergy_sub_cStar_mul_le hPrefix hJ2 hJ3 hnm e
    hunit he (sigmaBarStarInvSqrt nu S.LPrime P S.n) p hp' F hF gradHatW hFmemLp
    hGmemLp hproj hJ5app
  rw [hscale] at hnondeg
  have htri := abs_sub_le
    ((∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal)
    (wholeSpaceEnergy P.toMeasure gradHatW)
    (cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * vecNormSq p)
  have hsplit : lhsTerm1Const Cgap Cav * Q * vecNormSq p + K * vecNormSq p =
      (lhsTerm1Const Cgap Cav * Q + K) * vecNormSq p := by ring
  rw [← hsplit]
  exact htri.trans (add_le_add hEnergyGap hnondeg)

/-! ## The bridge from the per-shell gaps -/

/-- **The summed display `e.wN.wD.with.average.error`** in
the shape `l_LHS_term1_constFirst` consumes: the shell decomposition of the
flux, `vecCubeLpENorm_grad_sub_le_of_shellBranches` at the print's shifts
`b_r = (j_r p)_{cu_m}` for `r ≥ m` and `b_r = 0` below, and the domination of
the sum of the per-shell observables by the single observable `Y`. -/
theorem vecCubeLpENorm_grad_sub_le_of_shellGapSum (d : ℕ)
    (S : ScaleSelection) (hlm : S.ellPrime < S.m) (hmL : S.m ≤ S.LPrime)
    (p : Vec d) (F : ShellSeq d → Vec d → Vec d)
    (hF : ∀ omega : ShellSeq d, F omega = fun x =>
      matVecMul (streamCutoff omega S.LPrime x -
        streamCutoff omega S.ellPrime x) p)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (wN : ShellSeq d →
      H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ))))
    (hwD : ∀ omega : ShellSeq d,
      IsCubeDirichletResponse (originCube d (S.m : ℤ)) (F omega) (wD omega))
    (hwN : ∀ omega : ShellSeq d,
      IsCubeNeumannResponse (originCube d (S.m : ℤ)) (F omega) (wN omega))
    (wDr : ℕ → ShellSeq d →
      H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (wNr : ℕ → ShellSeq d →
      H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ))))
    (hwDr : ∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
      IsCubeDirichletResponse (originCube d (S.m : ℤ)) (shellFlux omega r p)
        (wDr r omega))
    (hwNr : ∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
      IsCubeNeumannResponse (originCube d (S.m : ℤ)) (shellFlux omega r p)
        (wNr r omega))
    (Zgap : ℕ → ShellSeq d → ℝ)
    (hZgap0 : ∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
      0 ≤ Zgap r omega)
    (hZgapBound : ∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => (wNr r omega).toH1Function.grad x +
              (if S.m ≤ r then shellFluxAverage (S.m : ℤ) omega r p else 0) -
            (wDr r omega).toH1Function.grad x) ≤
        ENNReal.ofReal (Zgap r omega))
    (Y : ShellSeq d → ℝ)
    (hYsum : ∀ omega : ShellSeq d,
      ∑ r ∈ Finset.Ioc S.ellPrime S.LPrime, Zgap r omega ≤ Y omega) :
    ∀ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => (wN omega).toH1Function.grad x -
          (wD omega).toH1Function.grad x) ≤
      ENNReal.ofReal (Y omega + Book.Ch02.vecNorm
        (∑ r ∈ Finset.Icc S.m S.LPrime,
          shellFluxAverage (S.m : ℤ) omega r p)) := by
  classical
  have hlL : S.ellPrime ≤ S.LPrime := le_of_lt (lt_of_lt_of_le hlm hmL)
  have hFsum : ∀ omega : ShellSeq d,
      F omega = fun x => ∑ r ∈ Finset.Ioc S.ellPrime S.LPrime,
        shellFlux omega r p x := by
    intro omega
    funext x
    rw [hF omega]
    exact matVecMul_streamCutoff_sub_eq_sum_shellFlux omega hlL p x
  have hbsum : ∀ omega : ShellSeq d,
      ∑ r ∈ Finset.Ioc S.ellPrime S.LPrime,
          (if S.m ≤ r then shellFluxAverage (S.m : ℤ) omega r p else 0) =
        ∑ r ∈ Finset.Icc S.m S.LPrime,
          shellFluxAverage (S.m : ℤ) omega r p := by
    intro omega
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext r
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
    omega
  intro omega
  have hwDo : IsCubeDirichletResponse (originCube d (S.m : ℤ))
      (fun x => ∑ r ∈ Finset.Ioc S.ellPrime S.LPrime, shellFlux omega r p x)
      (wD omega) := by
    have h := hwD omega
    rwa [hFsum omega] at h
  have hwNo : IsCubeNeumannResponse (originCube d (S.m : ℤ))
      (fun x => ∑ r ∈ Finset.Ioc S.ellPrime S.LPrime, shellFlux omega r p x)
      (wN omega) := by
    have h := hwN omega
    rwa [hFsum omega] at h
  have hmain := vecCubeLpENorm_grad_sub_le_of_shellBranches
    (Q := originCube d (S.m : ℤ)) (Finset.Ioc S.ellPrime S.LPrime) p omega
    (fun r => wDr r omega) (fun r => wNr r omega) hwDo hwNo
    (fun r hr => hwDr r hr omega) (fun r hr => hwNr r hr omega)
    (fun r => if S.m ≤ r then shellFluxAverage (S.m : ℤ) omega r p else 0)
    (fun r => Zgap r omega) (fun r hr => hZgap0 r hr omega)
    (fun r hr => hZgapBound r hr omega)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hbsum omega]
  exact add_le_add (hYsum omega) le_rfl

/-! ## The constant in the input constants alone -/

end

end SuperdiffusionCLT.Section3.Setup
