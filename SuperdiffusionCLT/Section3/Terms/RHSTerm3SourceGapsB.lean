/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SourceGaps

/-!
# The second and fourth printed terms of the Hoelder split, and the carrier swap

The Hoelder bridge of the proof of `l.RHS.term3` carries `hSwap` (the carrier swap)
and the three
printed terms `hTerm2`, `hTerm3`, `hTerm4` of the Hoelder display in that proof.
This module discharges
`hSwap`, `hTerm2` and `hTerm4` at the carriers, from the general
lattice-shift covariance and the fourth-power Jensen inequality of
`Section3/Terms/RHSTerm3SourceGaps.lean`.

## Why `hTerm3` is not here

`hTerm3` is **not** derivable at these carriers, and not for want of an
ingredient.  Its left side is the weighted average of `translatedBlockDevSum
nu S.ell S.n P omega z = sum_i |e_i . (b_ell(z+cu_n) - shom_ell(cu_n)) e_i|`,
the *absolute* coordinate sum of the printed proof, while its right side is
`coarseBlockDevMoment nu S.ell S.n P D = sum_i E[|avsum_{z in D} e_i .
(b_ell(z+cu_n) - shom_ell(cu_n)) e_i|^2]^{1/2}`, whose inner lattice average is
*signed*.  Only the signed average enjoys the concentration gain
`3^{-d(k-ell)/2}` of `blockDeviation_concentration`; `avsum_z sum_i
|Y_z^{(i)}|` has no cancellation and stays of order `E|Y_0|` however large
`k - ell` is, so the inequality fails for a non-degenerate law once `k - ell`
is large.  The paper has the same discontinuity: the decomposition is printed
with absolute values and the Hoelder display drops them without comment.  What the
display needs is the *signed* trace bound
`|b_ell(z+cu_n)| <= d shom_ell(cu_n) + sum_i e_i . (b_ell(z+cu_n) -
shom_ell(cu_n)) e_i`, which is what `matrixOperatorNorm_le_sum_diag_of_posSemidef`
(`Section3/Terms/RHSTerm3Holder.lean`) proves before the absolute values go in.
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

/-! ## The fourth moment of the response gradient is finite -/

/-- **`E[||nabla w||^4_{L4bar(cu_m)}] < infinity`**, from the first conjunct of
`l.w.basic.regbounds` in
its exact shape; the derivation is the fourth-moment bound for the response gradient, stopped at the
finiteness. -/
theorem lintegral_gradFour_pow_ne_top [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    {p : Vec d} (hp : p = testVector nu S.LPrime P S.n e)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    {C : ℝ} (hC : 1 ≤ C) {Z : ShellSeq d → ℝ} (hZmeas : Measurable Z)
    (hZbigO : IsBigO P.toMeasure (gammaSigma 2) Z
      (C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))))
    (hZbound : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 8 (w omega).toH1Function.grad ≤
        ENNReal.ofReal (Z omega)) :
    (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ)
        ∂P.toMeasure) ≠ ⊤ := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC
  have hhR : (0 : ℝ) < (S.h : ℝ) := by
    have h1 := hSorder.ellPrime_lt_m
    have h2 := S.ellPrime_add_h
    have h3 : 1 ≤ S.h := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h3
  have hpn : (0 : ℝ) < vecNormSq p := by
    rw [hp, vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he]
    exact sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hA : (0 : ℝ) < C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2)) :=
    mul_pos hC0 (mul_pos (Real.sqrt_pos.2 hpn) (Real.rpow_pos_of_pos hhR _))
  have hptr : ∀ omega : ShellSeq d,
      (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ) ≤
        ENNReal.ofReal (|Z omega| ^ (((4 : ℕ) : ℝ))) := by
    intro omega
    have hdown : vecCubeLpENorm (originCube d (S.m : ℤ)) 4
        (w omega).toH1Function.grad ≤ ENNReal.ofReal |Z omega| :=
      le_trans (le_trans (vecCubeLpENorm_mono_exponent (originCube d (S.m : ℤ))
        (by norm_num) (aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
          (w omega).toH1Function.grad_memVectorL2)) (hZbound omega))
        (ENNReal.ofReal_le_ofReal (le_abs_self _))
    rw [Real.rpow_natCast, ENNReal.ofReal_pow (abs_nonneg _)]
    exact pow_le_pow_left' hdown 4
  have hint : MeasureTheory.Integrable
      (fun omega : ShellSeq d => |Z omega| ^ (((4 : ℕ) : ℝ))) P.toMeasure :=
    SuperdiffusionCLT.Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
      hA hZmeas.aemeasurable hZbigO 4
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (le_trans (lintegral_mono hptr)
      (le_of_eq (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun _ =>
          Real.rpow_nonneg (abs_nonneg _) _)).symm))

/-! ## The printed `Gamma_{1/3}` remainder in `L^2(P)` -/

/-- **The second moment of a `Gamma_{1/3}` variable**,
the printed remainder
`O_{Gamma_{1/3}}(C nu^{-3} L' 3^{-(ell-n)})` of `e.bL.to.bhomell.pre0zz` is
square integrable, with `L^2(P)` norm at most `8 Gamma-moment-constant` times
its amplitude. -/
theorem integral_sq_le_of_isBigO_gammaSigma_third
    {P : ProbabilityMeasure (ShellSeq d)} {X : ShellSeq d → ℝ} {K : ℝ}
    (hK : 0 < K) (hXm : Measurable X)
    (hX : IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X K) :
    Integrable (fun omega : ShellSeq d => X omega ^ (2 : ℕ)) P.toMeasure ∧
      ∫ omega : ShellSeq d, X omega ^ (2 : ℕ) ∂P.toMeasure ≤
        (8 * gammaMomentConst ((1 : ℝ) / 3) * K) ^ (2 : ℕ) := by
  have hgrow := hasGammaMomentGrowthWith_of_isBigO_gammaSigma (μ := P.toMeasure)
    (show (0 : ℝ) < (1 : ℝ) / 3 by norm_num) hK hXm.aemeasurable hX
  obtain ⟨hint, hbd⟩ := hgrow (show (1 : ℝ) ≤ 2 by norm_num)
  have hpt : ∀ omega : ShellSeq d, |X omega| ^ (2 : ℝ) = X omega ^ (2 : ℕ) := fun _ => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have hpow : ((2 : ℝ) ^ (((1 : ℝ) / 3)⁻¹)) = 8 := by
    rw [show (((1 : ℝ) / 3)⁻¹) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  refine ⟨hint.congr (Filter.Eventually.of_forall hpt), ?_⟩
  have heq : ∫ omega : ShellSeq d, |X omega| ^ (2 : ℝ) ∂P.toMeasure =
      ∫ omega : ShellSeq d, X omega ^ (2 : ℕ) ∂P.toMeasure :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [heq, hpow] at hbd
  have hrw : (gammaMomentConst ((1 : ℝ) / 3) * K * 8) ^ (2 : ℝ) =
      (8 * gammaMomentConst ((1 : ℝ) / 3) * K) ^ (2 : ℕ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hrw] at hbd
  exact hbd

private theorem sqrt_integral_sq_le {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f : Omega → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∫ a, f a ^ (2 : ℕ) ∂mu ≤ c ^ (2 : ℕ)) :
    Real.sqrt (∫ a, f a ^ (2 : ℕ) ∂mu) ≤ c := by
  rw [show c = Real.sqrt (c ^ (2 : ℕ)) from (Real.sqrt_sq hc).symm]
  exact Real.sqrt_le_sqrt h

/-- Jensen for a finite average: the square of the average is at most the
average of the squares. -/
private theorem sq_inv_card_sum_le {iota : Type*} (s : Finset iota) (a : iota → ℝ) :
    ((s.card : ℝ)⁻¹ * ∑ i ∈ s, a i) ^ (2 : ℕ) ≤
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, a i ^ (2 : ℕ) := by
  classical
  rcases Finset.eq_empty_or_nonempty s with hs | hs
  · subst hs; simp
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hs
  have hcheb : (∑ i ∈ s, a i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, a i ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hkey : ((s.card : ℝ)⁻¹ * ∑ i ∈ s, a i) ^ (2 : ℕ) =
      ((s.card : ℝ)⁻¹) ^ 2 * (∑ i ∈ s, a i) ^ 2 := by ring
  rw [hkey]
  have hmul := mul_le_mul_of_nonneg_left hcheb (le_of_lt (pow_pos (inv_pos.2 hcard) 2))
  refine le_trans hmul (le_of_eq ?_)
  field_simp

/-- A uniform second-moment bound transfers to the lattice average. -/
theorem integral_sq_descendantAverage_le {P : ProbabilityMeasure (ShellSeq d)}
    {F : ShellSeq d → TriadicCube d → ℝ} {M : ℝ} (Q : TriadicCube d) (j : ℕ)
    (hint : ∀ z ∈ descendantsAtDepth Q j,
      Integrable (fun omega : ShellSeq d => F omega z ^ (2 : ℕ)) P.toMeasure)
    (hbd : ∀ z ∈ descendantsAtDepth Q j,
      ∫ omega : ShellSeq d, F omega z ^ (2 : ℕ) ∂P.toMeasure ≤ M ^ (2 : ℕ)) :
    ∫ omega : ShellSeq d, ((((descendantsAtDepth Q j).card : ℝ))⁻¹ *
        ∑ z ∈ descendantsAtDepth Q j, F omega z) ^ (2 : ℕ) ∂P.toMeasure ≤
      M ^ (2 : ℕ) := by
  classical
  set D : Finset (TriadicCube d) := descendantsAtDepth Q j with hDdef
  have hcard : (0 : ℝ) < (D.card : ℝ) := by
    rw [hDdef]
    exact_mod_cast Finset.card_pos.2 (descendantsAtDepth_nonempty Q j)
  by_cases hInt : Integrable (fun omega : ShellSeq d =>
      ((D.card : ℝ)⁻¹ * ∑ z ∈ D, F omega z) ^ (2 : ℕ)) P.toMeasure
  · have hIntR : Integrable (fun omega : ShellSeq d =>
        (D.card : ℝ)⁻¹ * ∑ z ∈ D, F omega z ^ (2 : ℕ)) P.toMeasure :=
      (MeasureTheory.integrable_finsetSum D hint).const_mul _
    have h1 := MeasureTheory.integral_mono hInt hIntR
      (fun omega => sq_inv_card_sum_le D (fun z => F omega z))
    have h2 : ∫ omega : ShellSeq d,
        ((D.card : ℝ)⁻¹ * ∑ z ∈ D, F omega z ^ (2 : ℕ)) ∂P.toMeasure =
        (D.card : ℝ)⁻¹ * ∑ z ∈ D, ∫ omega : ShellSeq d,
          F omega z ^ (2 : ℕ) ∂P.toMeasure := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum D hint]
    have h3 : ∑ z ∈ D, ∫ omega : ShellSeq d, F omega z ^ (2 : ℕ) ∂P.toMeasure ≤
        (D.card : ℝ) * M ^ (2 : ℕ) := by
      have h := Finset.sum_le_sum hbd
      rwa [Finset.sum_const, nsmul_eq_mul] at h
    have h4 : (D.card : ℝ)⁻¹ * ∑ z ∈ D, ∫ omega : ShellSeq d,
        F omega z ^ (2 : ℕ) ∂P.toMeasure ≤ M ^ (2 : ℕ) := by
      have h5 := mul_le_mul_of_nonneg_left h3 (le_of_lt (inv_pos.2 hcard))
      have h6 : (D.card : ℝ)⁻¹ * ((D.card : ℝ) * M ^ (2 : ℕ)) = M ^ (2 : ℕ) := by
        field_simp
      linarith only [h5, h6]
    rw [h2] at h1
    linarith only [h1, h4]
  · rw [MeasureTheory.integral_undef hInt]
    positivity

/-! ## The two provable printed terms -/

/-- The constant of the fourth printed term: the amplitude of the printed
`Gamma_{1/3}` remainder times the second-moment factor of
`integral_sq_le_of_isBigO_gammaSigma_third`. -/
def holderRemainderConst (Czero : ℝ) : ℝ := 8 * gammaMomentConst ((1 : ℝ) / 3) * Czero

theorem holderRemainderConst_nonneg {Czero : ℝ} (h : 0 ≤ Czero) :
    0 ≤ holderRemainderConst Czero := by
  have hg := gammaMomentConst_pos (show (0 : ℝ) < (1 : ℝ) / 3 by norm_num)
  rw [holderRemainderConst]
  positivity

/-- **The binders `hTerm2` and `hTerm4` of the Hoelder bridge**, in their exact shapes.
Both are instances of the Hoelder step
`weightedBlockAverage_integral_le`; the second-moment bound it needs on every
outer cube `z'` comes, for `hTerm2`, from the lattice-shift covariance
`integral_sq_descendantAverage_eq` -- exactly the silent replacement of the
inner average made in the paper -- and for
`hTerm4` from the printed `Gamma_{1/3}` remainder through
`integral_sq_le_of_isBigO_gammaSigma_third`.

`hZwmeas`-`hZwbound` are the first conjunct of `l.w.basic.regbounds`
(`e.nablaw.Lt`) in its exact shape; `hsq` and `hQuadZc` are
`L^2(P)` side conditions, there being no measurability datum on `w` here.  The
third printed term `hTerm3` is **not** here; the module docstring says why. -/
theorem holder_terms_bridge [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    {p : Vec d} (hp : p = testVector nu S.LPrime P S.n e)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    {C : ℝ} (hC : 1 ≤ C) {Zw : ShellSeq d → ℝ} (hZwmeas : Measurable Zw)
    (hZwbigO : IsBigO P.toMeasure (gammaSigma 2) Zw
      (C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))))
    (hZwbound : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 8 (w omega).toH1Function.grad ≤
        ENNReal.ofReal (Zw omega))
    {zc : TriadicCube d} (hzc : zc.scale = ((coarseBlockScale d S : ℕ) : ℤ))
    (Zrem : ShellSeq d → TriadicCube d → ℝ) {Czero : ℝ} (hCzero : 0 < Czero)
    (hZremMeas : ∀ z : TriadicCube d, Measurable fun omega : ShellSeq d => Zrem omega z)
    (hZremTail : ∀ z : TriadicCube d, IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3))
      (fun omega : ShellSeq d => Zrem omega z)
      (Czero * nu ^ (-(3 : ℝ)) * ((S.LPrime : ℕ) : ℝ) *
        (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))))
    (hsq : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad))) 2 P.toMeasure)
    (hQuadZc : MemLp (fun omega : ShellSeq d =>
      (((descendantsAtDepth zc (coarseBlockScale d S - S.n)).card : ℝ))⁻¹ *
        ∑ z ∈ descendantsAtDepth zc (coarseBlockScale d S - S.n),
          translatedStreamQuadForm nu S.ell S.LPrime e omega z) 2 P.toMeasure) :
    (∫ omega : ShellSeq d,
        weightedBlockAverage d S.n (coarseBlockScale d S) S.m
          ((w omega).toH1Function.grad)
          (translatedStreamQuadForm nu S.ell S.LPrime e omega) ∂P.toMeasure ≤
      Real.sqrt (∫ omega : ShellSeq d,
            |(((descendantsAtDepth zc (coarseBlockScale d S - S.n)).card : ℝ))⁻¹ *
                ∑ z ∈ descendantsAtDepth zc (coarseBlockScale d S - S.n),
                  translatedStreamQuadForm nu S.ell S.LPrime e omega z| ^ 2
          ∂P.toMeasure) * gradResponseMoment (m := S.m) 4 4 P w ^ ((1 : ℝ) / 2)) ∧
    (∫ omega : ShellSeq d,
        weightedBlockAverage d S.n (coarseBlockScale d S) S.m
          ((w omega).toH1Function.grad) (Zrem omega) ∂P.toMeasure ≤
      holderRemainderConst Czero * nu ^ (-(3 : ℝ)) * ((S.LPrime : ℕ) : ℝ) *
        (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) *
        gradResponseMoment (m := S.m) 4 4 P w ^ ((1 : ℝ) / 2)) := by
  classical
  have hfin := lintegral_gradFour_pow_ne_top hnu hPrefix hJ2 hJ3 hJ4 S hSorder he hp w
    hC hZwmeas hZwbigO hZwbound
  have hellP : S.ell ≤ S.ellPrime := le_of_lt hSorder.ell_lt_ellPrime
  obtain ⟨-, hkl, -, -⟩ := coarse_block_scale_choice d S hellP
  have hkm : coarseBlockScale d S ≤ S.m :=
    le_trans hkl (le_of_lt hSorder.ellPrime_lt_m)
  have hscale : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      zc.scale = z'.scale := by
    intro z' hz'
    rw [hzc, scale_of_mem_largeCubeSubcubes hkm hz']
  -- the second printed term
  have hquadTerm : ∫ omega : ShellSeq d,
      weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        ((w omega).toH1Function.grad)
        (translatedStreamQuadForm nu S.ell S.LPrime e omega) ∂P.toMeasure ≤
      Real.sqrt (∫ omega : ShellSeq d,
            |(((descendantsAtDepth zc (coarseBlockScale d S - S.n)).card : ℝ))⁻¹ *
                ∑ z ∈ descendantsAtDepth zc (coarseBlockScale d S - S.n),
                  translatedStreamQuadForm nu S.ell S.LPrime e omega z| ^ 2
          ∂P.toMeasure) * gradResponseMoment (m := S.m) 4 4 P w ^ ((1 : ℝ) / 2) := by
    have habs : ∫ omega : ShellSeq d,
        |(((descendantsAtDepth zc (coarseBlockScale d S - S.n)).card : ℝ))⁻¹ *
            ∑ z ∈ descendantsAtDepth zc (coarseBlockScale d S - S.n),
              translatedStreamQuadForm nu S.ell S.LPrime e omega z| ^ 2 ∂P.toMeasure =
        ∫ omega : ShellSeq d,
          ((((descendantsAtDepth zc (coarseBlockScale d S - S.n)).card : ℝ))⁻¹ *
              ∑ z ∈ descendantsAtDepth zc (coarseBlockScale d S - S.n),
                translatedStreamQuadForm nu S.ell S.LPrime e omega z) ^ (2 : ℕ)
          ∂P.toMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall fun _ => sq_abs _)
    have hX0 : (0 : ℝ) ≤ ∫ omega : ShellSeq d,
        |(((descendantsAtDepth zc (coarseBlockScale d S - S.n)).card : ℝ))⁻¹ *
            ∑ z ∈ descendantsAtDepth zc (coarseBlockScale d S - S.n),
              translatedStreamQuadForm nu S.ell S.LPrime e omega z| ^ 2 ∂P.toMeasure :=
      MeasureTheory.integral_nonneg fun _ => by positivity
    refine weightedBlockAverage_integral_le P w
      (fun omega => translatedStreamQuadForm nu S.ell S.LPrime e omega)
      (Real.sqrt_nonneg _) hfin hsq ?_ ?_
    · intro z' hz'
      exact memLp_two_descendantAverage_translate hPrefix hJ2
        (fun omega Q => translatedStreamQuadForm_eq_originCube nu S.ell S.LPrime e omega Q)
        (hscale z' hz') (coarseBlockScale d S - S.n) hQuadZc
    · intro z' hz'
      have heq := integral_sq_descendantAverage_eq hPrefix hJ2
        (fun omega Q => translatedStreamQuadForm_eq_originCube nu S.ell S.LPrime e omega Q)
        (hscale z' hz') (coarseBlockScale d S - S.n) hQuadZc.aestronglyMeasurable
      rw [heq, Real.sq_sqrt hX0, habs]
  refine ⟨hquadTerm, ?_⟩
  -- the fourth printed term
  have hLpos : (0 : ℝ) < ((S.LPrime : ℕ) : ℝ) := by
    have h1 : 0 < S.LPrime := lt_of_le_of_lt (Nat.zero_le S.m) hSorder.m_lt_LPrime
    exact_mod_cast h1
  have hLam : (0 : ℝ) < Czero * nu ^ (-(3 : ℝ)) * ((S.LPrime : ℕ) : ℝ) *
      (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) := by
    have hnu3 : (0 : ℝ) < nu ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hnu _
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hmoment : ∀ z : TriadicCube d,
      Integrable (fun omega : ShellSeq d => Zrem omega z ^ (2 : ℕ)) P.toMeasure ∧
        ∫ omega : ShellSeq d, Zrem omega z ^ (2 : ℕ) ∂P.toMeasure ≤
          (holderRemainderConst Czero * nu ^ (-(3 : ℝ)) * ((S.LPrime : ℕ) : ℝ) *
            (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) ^ (2 : ℕ) := by
    intro z
    obtain ⟨hI, hB⟩ := integral_sq_le_of_isBigO_gammaSigma_third hLam (hZremMeas z)
      (hZremTail z)
    refine ⟨hI, ?_⟩
    have hconst : 8 * gammaMomentConst ((1 : ℝ) / 3) *
          (Czero * nu ^ (-(3 : ℝ)) * ((S.LPrime : ℕ) : ℝ) *
            (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) =
        holderRemainderConst Czero * nu ^ (-(3 : ℝ)) * ((S.LPrime : ℕ) : ℝ) *
          (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) := by
      rw [holderRemainderConst]
      ring
    rwa [hconst] at hB
  have hMemLp : ∀ z : TriadicCube d,
      MemLp (fun omega : ShellSeq d => Zrem omega z) 2 P.toMeasure := by
    intro z
    exact (memLp_two_iff_integrable_sq (hZremMeas z).aestronglyMeasurable).2 (hmoment z).1
  have hM0 : (0 : ℝ) ≤ holderRemainderConst Czero * nu ^ (-(3 : ℝ)) *
      ((S.LPrime : ℕ) : ℝ) * (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) := by
    have hc := holderRemainderConst_nonneg (le_of_lt hCzero)
    have hnu3 : (0 : ℝ) < nu ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hnu _
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    positivity
  refine weightedBlockAverage_integral_le P w Zrem hM0 hfin hsq ?_ ?_
  · intro z' _
    exact ((memLp_finsetSum (descendantsAtDepth z' (coarseBlockScale d S - S.n))
      (fun z _ => hMemLp z)).const_mul _)
  · intro z' _
    exact integral_sq_descendantAverage_le z' (coarseBlockScale d S - S.n)
      (fun z _ => (hmoment z).1) (fun z _ => (hmoment z).2)

/-- **The balanced comparison on a translated cube**: the
quenched localization anchor `l.localization` at the triple `(l, n, L)`, read on
`cu_n`, holds on every triadic cube of scale `n` with the transported deviation
`translateObservable X Q`. -/
theorem localization_loewner_translated [NeZero d] {nu : ℝ} {nn l L : ℕ}
    {X : ShellSeq d → ℝ}
    (hquenched : ∀ omega : ShellSeq d,
      MatLoewnerLE
          ((1 - X omega) • Homogenization.sigmaStarInvCoarse
            (openCubeSet (originCube d (nn : ℤ)))
            (coefficientCutoff nu omega l).toCoeffField)
          (Homogenization.sigmaStarInvCoarse (openCubeSet (originCube d (nn : ℤ)))
            (coefficientCutoff nu omega L).toCoeffField) ∧
        MatLoewnerLE
          (Homogenization.sigmaStarInvCoarse (openCubeSet (originCube d (nn : ℤ)))
            (coefficientCutoff nu omega L).toCoeffField)
          ((1 + X omega) • Homogenization.sigmaStarInvCoarse
            (openCubeSet (originCube d (nn : ℤ)))
            (coefficientCutoff nu omega l).toCoeffField))
    {Q : TriadicCube d} (hQ : Q.scale = (nn : ℤ)) (omega : ShellSeq d) :
    MatLoewnerLE
        ((1 - translateObservable X Q omega) • Homogenization.sigmaStarInvCoarse
          (cubeSet Q) (coefficientCutoff nu omega l).toCoeffField)
        (Homogenization.sigmaStarInvCoarse (cubeSet Q)
          (coefficientCutoff nu omega L).toCoeffField) ∧
      MatLoewnerLE
        (Homogenization.sigmaStarInvCoarse (cubeSet Q)
          (coefficientCutoff nu omega L).toCoeffField)
        ((1 + translateObservable X Q omega) • Homogenization.sigmaStarInvCoarse
          (cubeSet Q) (coefficientCutoff nu omega l).toCoeffField) := by
  have hopen : ∀ (j : ℕ) (om : ShellSeq d),
      Homogenization.sigmaStarInvCoarse (openCubeSet (originCube d (nn : ℤ)))
          (coefficientCutoff nu om j).toCoeffField =
        Homogenization.sigmaStarInvCoarse (cubeSet (originCube d (nn : ℤ)))
          (coefficientCutoff nu om j).toCoeffField := by
    intro j om
    rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
  have hcovl := sigmaStarInvCoarse_cubeSet_translate nu l omega Q
  have hcovL := sigmaStarInvCoarse_cubeSet_translate nu L omega Q
  rw [hQ] at hcovl hcovL
  have hq := hquenched (ShellField.translateSequence (triadicCubeShift Q) omega)
  rw [hopen l, hopen L] at hq
  rw [hcovl, hcovL]
  exact hq

/-- **The replacement error of the carrier swap, pointwise**: the two quadratic
forms differ by the relative factor `X` of the balanced comparison, and the
crude ellipticity bound turns the `s_{l,*}^{-1}` form into
`nu^{-1}|(k_l - k_L)_{z+cu_n}e|^2`. -/
theorem translatedStreamQuadFormGap_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {l L : ℕ} (e : Vec d) {X : ShellSeq d → ℝ} {z : TriadicCube d}
    (hLoew : ∀ omega : ShellSeq d,
      MatLoewnerLE
          ((1 - X omega) • Homogenization.sigmaStarInvCoarse (cubeSet z)
            (coefficientCutoff nu omega l).toCoeffField)
          (Homogenization.sigmaStarInvCoarse (cubeSet z)
            (coefficientCutoff nu omega L).toCoeffField) ∧
        MatLoewnerLE
          (Homogenization.sigmaStarInvCoarse (cubeSet z)
            (coefficientCutoff nu omega L).toCoeffField)
          ((1 + X omega) • Homogenization.sigmaStarInvCoarse (cubeSet z)
            (coefficientCutoff nu omega l).toCoeffField))
    (omega : ShellSeq d) :
    translatedStreamQuadFormGap nu l L e omega z ≤
      |X omega| * (nu⁻¹ * translatedStreamNormSq l L e omega z) := by
  set v : Vec d := streamIncrementCubeVec l L e omega z with hvdef
  have hscal : ∀ c : ℝ, vecDot v (matVecMul (c • Homogenization.sigmaStarInvCoarse
      (cubeSet z) (coefficientCutoff nu omega l).toCoeffField) v) =
      c * translatedStreamQuadFormLower nu l L e omega z := by
    intro c
    rw [smul_matVecMul, vecDot_smul_right]
    rfl
  obtain ⟨h1, h2⟩ := hLoew omega
  have hv1 := h1 v
  have hv2 := h2 v
  rw [hscal (1 - X omega)] at hv1
  rw [hscal (1 + X omega)] at hv2
  have hqL : vecDot v (matVecMul (Homogenization.sigmaStarInvCoarse (cubeSet z)
      (coefficientCutoff nu omega L).toCoeffField) v) =
      translatedStreamQuadForm nu l L e omega z := rfl
  rw [hqL] at hv1 hv2
  have hlow := translatedStreamQuadFormLower_nonneg hnu l L e omega z
  have habs : |translatedStreamQuadFormLower nu l L e omega z -
      translatedStreamQuadForm nu l L e omega z| ≤
      X omega * translatedStreamQuadFormLower nu l L e omega z := by
    rw [abs_le]
    constructor
    · linarith only [hv2]
    · linarith only [hv1]
  have hXabs : X omega * translatedStreamQuadFormLower nu l L e omega z ≤
      |X omega| * translatedStreamQuadFormLower nu l L e omega z :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hlow
  have hnuI : |X omega| * translatedStreamQuadFormLower nu l L e omega z ≤
      |X omega| * (nu⁻¹ * translatedStreamNormSq l L e omega z) :=
    mul_le_mul_of_nonneg_left
      (translatedStreamQuadFormLower_le_nuInv_mul hnu l L e omega z) (abs_nonneg _)
  rw [translatedStreamQuadFormGap_eq_abs_sub]
  linarith only [habs, hXabs, hnuI]

/-! ## The second moment of the replacement error -/

/-- **The second moment of the replacement error of the carrier swap on one
translated cube**: the relative `Γ₁` error `X` of the balanced comparison
and the `Γ₁` envelope of `|(k_l - k_L)_{z+cu_n}e|^2` combined by
Cauchy-Schwarz at the fourth moment.  This is the *"Hoelder/Orlicz
bookkeeping"* that the paper leaves implicit. -/
theorem integral_sq_translatedStreamQuadFormGap_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} {l L : ℕ} (e : Vec d)
    {X : ShellSeq d → ℝ} {z : TriadicCube d} {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hXm : Measurable X) (hXtail : IsBigO P.toMeasure (gammaSigma 1) X A)
    (hNtail : IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => translatedStreamNormSq l L e omega z) B)
    (hLoew : ∀ omega : ShellSeq d,
      MatLoewnerLE
          ((1 - X omega) • Homogenization.sigmaStarInvCoarse (cubeSet z)
            (coefficientCutoff nu omega l).toCoeffField)
          (Homogenization.sigmaStarInvCoarse (cubeSet z)
            (coefficientCutoff nu omega L).toCoeffField) ∧
        MatLoewnerLE
          (Homogenization.sigmaStarInvCoarse (cubeSet z)
            (coefficientCutoff nu omega L).toCoeffField)
          ((1 + X omega) • Homogenization.sigmaStarInvCoarse (cubeSet z)
            (coefficientCutoff nu omega l).toCoeffField)) :
    Integrable (fun omega : ShellSeq d =>
        translatedStreamQuadFormGap nu l L e omega z ^ (2 : ℕ)) P.toMeasure ∧
      ∫ omega : ShellSeq d,
          translatedStreamQuadFormGap nu l L e omega z ^ (2 : ℕ) ∂P.toMeasure ≤
        (nu⁻¹ * (16 * gammaMomentConst 1 ^ (2 : ℕ) * (A * B))) ^ (2 : ℕ) := by
  classical
  obtain ⟨hX4i, hX4⟩ := integral_fourth_le_of_isBigO_gammaSigma_one hA hXm hXtail
  obtain ⟨hN4i, hN4⟩ := integral_fourth_le_of_isBigO_gammaSigma_one hB
    (measurable_translatedStreamNormSq l L e z) hNtail
  have hsqeq : ∀ (Y : ShellSeq d → ℝ) (omega : ShellSeq d),
      (Y omega ^ (2 : ℕ)) ^ (2 : ℕ) = Y omega ^ (4 : ℕ) := by
    intro Y omega
    rw [← pow_mul]
  have hXmem : MemLp (fun omega : ShellSeq d => X omega ^ (2 : ℕ)) 2 P.toMeasure := by
    refine (memLp_two_iff_integrable_sq (hXm.pow_const 2).aestronglyMeasurable).2 ?_
    exact hX4i.congr (Filter.Eventually.of_forall fun omega => (hsqeq X omega).symm)
  have hNmem : MemLp (fun omega : ShellSeq d =>
      translatedStreamNormSq l L e omega z ^ (2 : ℕ)) 2 P.toMeasure := by
    refine (memLp_two_iff_integrable_sq
      ((measurable_translatedStreamNormSq l L e z).pow_const 2).aestronglyMeasurable).2 ?_
    exact hN4i.congr (Filter.Eventually.of_forall fun omega =>
      (hsqeq (fun o => translatedStreamNormSq l L e o z) omega).symm)
  have hCS := integral_mul_le_sqrt_mul_sqrt hXmem hNmem
  have hX4' : ∫ omega : ShellSeq d, (X omega ^ (2 : ℕ)) ^ (2 : ℕ) ∂P.toMeasure ≤
      ((4 * gammaMomentConst 1 * A) ^ (2 : ℕ)) ^ (2 : ℕ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun omega => hsqeq X omega),
      ← pow_mul]
    exact hX4
  have hN4' : ∫ omega : ShellSeq d,
      (translatedStreamNormSq l L e omega z ^ (2 : ℕ)) ^ (2 : ℕ) ∂P.toMeasure ≤
      ((4 * gammaMomentConst 1 * B) ^ (2 : ℕ)) ^ (2 : ℕ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun omega =>
        hsqeq (fun o => translatedStreamNormSq l L e o z) omega), ← pow_mul]
    exact hN4
  have hgm : (0 : ℝ) < gammaMomentConst 1 :=
    gammaMomentConst_pos (show (0 : ℝ) < 1 by norm_num)
  have hXsqrt := sqrt_integral_sq_le (f := fun omega : ShellSeq d => X omega ^ (2 : ℕ))
    (by positivity) hX4'
  have hNsqrt := sqrt_integral_sq_le
    (f := fun omega : ShellSeq d => translatedStreamNormSq l L e omega z ^ (2 : ℕ))
    (by positivity) hN4'
  have hprod : ∫ omega : ShellSeq d,
      X omega ^ (2 : ℕ) * translatedStreamNormSq l L e omega z ^ (2 : ℕ) ∂P.toMeasure ≤
      (4 * gammaMomentConst 1 * A) ^ (2 : ℕ) * (4 * gammaMomentConst 1 * B) ^ (2 : ℕ) := by
    refine le_trans hCS ?_
    exact mul_le_mul hXsqrt hNsqrt (Real.sqrt_nonneg _) (by positivity)
  have hptw : ∀ omega : ShellSeq d,
      translatedStreamQuadFormGap nu l L e omega z ^ (2 : ℕ) ≤
        nu⁻¹ ^ (2 : ℕ) *
          (X omega ^ (2 : ℕ) * translatedStreamNormSq l L e omega z ^ (2 : ℕ)) := by
    intro omega
    have hg := translatedStreamQuadFormGap_le hnu e hLoew omega
    have hg0 : 0 ≤ translatedStreamQuadFormGap nu l L e omega z := abs_nonneg _
    have hrhs : |X omega| * (nu⁻¹ * translatedStreamNormSq l L e omega z) =
        |X omega| * nu⁻¹ * translatedStreamNormSq l L e omega z := by ring
    rw [hrhs] at hg
    have hsq := pow_le_pow_left₀ hg0 hg 2
    have hexp : (|X omega| * nu⁻¹ * translatedStreamNormSq l L e omega z) ^ (2 : ℕ) =
        nu⁻¹ ^ (2 : ℕ) *
          (X omega ^ (2 : ℕ) * translatedStreamNormSq l L e omega z ^ (2 : ℕ)) := by
      rw [mul_pow, mul_pow, sq_abs]
      ring
    rw [hexp] at hsq
    exact hsq
  have hIntR : Integrable (fun omega : ShellSeq d => nu⁻¹ ^ (2 : ℕ) *
      (X omega ^ (2 : ℕ) * translatedStreamNormSq l L e omega z ^ (2 : ℕ)))
      P.toMeasure := (hXmem.integrable_mul hNmem).const_mul _
  have hIntG : Integrable (fun omega : ShellSeq d =>
      translatedStreamQuadFormGap nu l L e omega z ^ (2 : ℕ)) P.toMeasure := by
    refine Integrable.mono' hIntR
      ((measurable_translatedStreamQuadFormGap hnu l L e z).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hptw omega
  refine ⟨hIntG, ?_⟩
  have hmono := MeasureTheory.integral_mono hIntG hIntR hptw
  have hconstmul : ∫ omega : ShellSeq d, nu⁻¹ ^ (2 : ℕ) *
      (X omega ^ (2 : ℕ) * translatedStreamNormSq l L e omega z ^ (2 : ℕ))
      ∂P.toMeasure = nu⁻¹ ^ (2 : ℕ) * ∫ omega : ShellSeq d,
        X omega ^ (2 : ℕ) * translatedStreamNormSq l L e omega z ^ (2 : ℕ)
        ∂P.toMeasure := MeasureTheory.integral_const_mul _ _
  have hnu2 : (0 : ℝ) ≤ nu⁻¹ ^ (2 : ℕ) := by positivity
  have hstep := mul_le_mul_of_nonneg_left hprod hnu2
  have hfinal : nu⁻¹ ^ (2 : ℕ) *
      ((4 * gammaMomentConst 1 * A) ^ (2 : ℕ) * (4 * gammaMomentConst 1 * B) ^ (2 : ℕ)) =
      (nu⁻¹ * (16 * gammaMomentConst 1 ^ (2 : ℕ) * (A * B))) ^ (2 : ℕ) := by ring
  rw [hconstmul] at hmono
  linarith only [hmono, hstep, hfinal]

/-! ## The carrier swap -/

/-- The constant of the carrier-swap display: the `Γ₁` fourth-moment factor,
the localization amplitude `CL`, the stream-tail amplitude and the
`e.nablaw.Lt` constant. -/
def swapConst (d : ℕ) (C CL : ℝ) : ℝ :=
  16 * gammaMomentConst 1 ^ (2 : ℕ) * CL * streamTailConst d * nablaW4SqrtConst C

/-- **The binder `hSwap` of the Hoelder bridge**, the carrier swap of the proof of
`l.RHS.term3`, at `Cs0 = swapConst d C CL`.

`hLocAnchor` is the localization anchor `l.localization` at the triple
`(ell, n, L')` on `cu_n`, in the shape the binder `_hLocAnchor` of
the final Term 3 statement supplies it; `hZwmeas`-`hZwbound` are the
first conjunct of `l.w.basic.regbounds`; `hsq` is the `L^2(P)` side condition of
`weightedBlockAverage_integral_le`.  The proof is the printed one: the balanced
comparison transported to each translate, the crude quenched ellipticity bound,
the fourth-moment Cauchy-Schwarz, the Hoelder step and the fourth-moment form of
`e.nablaw.Lt`; the polynomial factors are absorbed into `nu^{-4}(L')^4` and the
rate is lowered from `3^{-(ell-n)}` to `3^{-(ell-n)/4}` as the printed proof asks. -/
theorem swap_bridge [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    {p : Vec d} (hp : p = testVector nu S.LPrime P S.n e)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    {C : ℝ} (hC : 1 ≤ C) {Zw : ShellSeq d → ℝ} (hZwmeas : Measurable Zw)
    (hZwbigO : IsBigO P.toMeasure (gammaSigma 2) Zw
      (C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))))
    (hZwbound : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 8 (w omega).toH1Function.grad ≤
        ENNReal.ofReal (Zw omega))
    {CL : ℝ} (hCL : 0 < CL)
    (hLocAnchor : ∃ X : ShellSeq d → ℝ, Measurable X ∧
      IsBigO P.toMeasure (gammaSigma 1) X
          (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((S.ell - S.n : ℕ) : ℝ))) ∧
        ∀ omega : ShellSeq d,
          MatLoewnerLE
              ((1 - X omega) • Homogenization.sigmaStarInvCoarse
                (openCubeSet (originCube d (S.n : ℤ)))
                (coefficientCutoff nu omega S.ell).toCoeffField)
              (Homogenization.sigmaStarInvCoarse
                (openCubeSet (originCube d (S.n : ℤ)))
                (coefficientCutoff nu omega S.LPrime).toCoeffField) ∧
            MatLoewnerLE
              (Homogenization.sigmaStarInvCoarse
                (openCubeSet (originCube d (S.n : ℤ)))
                (coefficientCutoff nu omega S.LPrime).toCoeffField)
              ((1 + X omega) • Homogenization.sigmaStarInvCoarse
                (openCubeSet (originCube d (S.n : ℤ)))
                (coefficientCutoff nu omega S.ell).toCoeffField))
    (hsq : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad))) 2 P.toMeasure) :
    ∫ omega : ShellSeq d,
        weightedBlockAverage d S.n (coarseBlockScale d S) S.m
          ((w omega).toH1Function.grad)
          (translatedStreamQuadFormGap nu S.ell S.LPrime e omega) ∂P.toMeasure ≤
      swapConst d C CL * nu ^ (-(4 : ℝ)) * ((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ) *
        (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ) / 4)) := by
  classical
  obtain ⟨X, hXm, hXtail, hXLoew⟩ := hLocAnchor
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hnl : S.n ≤ S.ell := le_of_lt hSorder.n_lt_ell
  have hlL : S.ell < S.LPrime :=
    lt_trans hSorder.ell_lt_ellPrime
      (lt_trans hSorder.ellPrime_lt_m hSorder.m_lt_LPrime)
  have hellP : S.ell ≤ S.ellPrime := le_of_lt hSorder.ell_lt_ellPrime
  obtain ⟨hlk, hkl, -, -⟩ := coarse_block_scale_choice d S hellP
  have hkm : coarseBlockScale d S ≤ S.m :=
    le_trans hkl (le_of_lt hSorder.ellPrime_lt_m)
  have hnk : S.n ≤ coarseBlockScale d S := le_trans hnl hlk
  -- the two amplitudes
  set T : ℝ := (3 : ℝ) ^ (-((S.ell - S.n : ℕ) : ℝ)) with hTdef
  set A : ℝ := CL * nu ^ (-(2 : ℝ)) * T with hAdef
  set B : ℝ := streamTailConst d * ((S.LPrime - S.ell : ℕ) : ℝ) with hBdef
  have hT0 : (0 : ℝ) < T := Real.rpow_pos_of_pos (by norm_num) _
  have hA0 : (0 : ℝ) < A := by
    have h := Real.rpow_pos_of_pos hnu (-(2 : ℝ))
    rw [hAdef]; positivity
  have hLL : (0 : ℝ) < ((S.LPrime - S.ell : ℕ) : ℝ) := by
    have h1 : 0 < S.LPrime - S.ell := Nat.sub_pos_of_lt hlL
    exact_mod_cast h1
  have hB0 : (0 : ℝ) < B := by
    rw [hBdef]
    exact mul_pos (streamTailConst_pos hd0) hLL
  set M : ℝ := nu⁻¹ * (16 * gammaMomentConst 1 ^ (2 : ℕ) * (A * B)) with hMdef
  have hgm : (0 : ℝ) < gammaMomentConst 1 :=
    gammaMomentConst_pos (show (0 : ℝ) < 1 by norm_num)
  have hM0 : (0 : ℝ) ≤ M := by
    rw [hMdef]
    have hnuI : (0 : ℝ) < nu⁻¹ := inv_pos.2 hnu
    positivity
  -- the per-cube second moment of the replacement error
  have hcube : ∀ z : TriadicCube d, z.scale = (S.n : ℤ) →
      Integrable (fun omega : ShellSeq d =>
          translatedStreamQuadFormGap nu S.ell S.LPrime e omega z ^ (2 : ℕ))
          P.toMeasure ∧
        ∫ omega : ShellSeq d,
            translatedStreamQuadFormGap nu S.ell S.LPrime e omega z ^ (2 : ℕ)
            ∂P.toMeasure ≤ M ^ (2 : ℕ) := by
    intro z hz
    have hNtail : IsBigO P.toMeasure (gammaSigma 1)
        (fun omega : ShellSeq d =>
          translatedStreamNormSq S.ell S.LPrime e omega z) B := by
      refine isBigO_gammaSigma_translatedStreamNormSq hPrefix hJ2 S.ell S.LPrime e ?_
      rw [hz]
      exact isBigO_gammaSigma_translatedStreamNormSq_originCube hPrefix hJ2 hJ3 hJ4
        hnl hlL he
    exact integral_sq_translatedStreamQuadFormGap_le hnu e hA0 hB0
      (measurable_translateObservable hXm z)
      (isBigO_gammaSigma_translateObservable hPrefix hJ2 hXm hXtail z) hNtail
      (localization_loewner_translated hXLoew hz)
  have hmemgap : ∀ z : TriadicCube d, z.scale = (S.n : ℤ) →
      MemLp (fun omega : ShellSeq d =>
        translatedStreamQuadFormGap nu S.ell S.LPrime e omega z) 2 P.toMeasure := by
    intro z hz; exact (memLp_two_iff_integrable_sq
      (measurable_translatedStreamQuadFormGap hnu S.ell S.LPrime e z).aestronglyMeasurable).2
      (hcube z hz).1
  have hdesc : ∀ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
      ∀ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n), z.scale = (S.n : ℤ) := by
    intro z' hz' z hz
    have h := scale_eq_sub_of_mem_descendantsAtDepth hz
    rw [scale_of_mem_largeCubeSubcubes hkm hz'] at h
    rw [h, Nat.cast_sub hnk]
    ring
  -- the Hoelder step
  have hfin := lintegral_gradFour_pow_ne_top hnu hPrefix hJ2 hJ3 hJ4 S hSorder he hp w
    hC hZwmeas hZwbigO hZwbound
  have hholder := weightedBlockAverage_integral_le (n := S.n)
    (k := coarseBlockScale d S) (m := S.m) P w
    (fun omega => translatedStreamQuadFormGap nu S.ell S.LPrime e omega) hM0 hfin hsq
    (fun z' hz' => (memLp_finsetSum
      (descendantsAtDepth z' (coarseBlockScale d S - S.n))
      (fun z hz => hmemgap z (hdesc z' hz' z hz))).const_mul _)
    (fun z' hz' => integral_sq_descendantAverage_le z'
      (coarseBlockScale d S - S.n) (fun z hz => (hcube z (hdesc z' hz' z hz)).1)
      (fun z hz => (hcube z (hdesc z' hz' z hz)).2))
  -- the fourth moment of `e.nablaw.Lt`
  have hpsq : vecNormSq p = sigmaBarStarInvSeq nu S.LPrime P S.n := by
    rw [hp]
    exact vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he
  have hpnu : vecNormSq p ≤ nu⁻¹ := by
    rw [hpsq]
    exact sigmaBarStarInvSeq_le_nuInv hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hnabla := nablaW4_of_regbounds d nu hnu P hPrefix hJ2 hJ3 hJ4 S hSorder e he
    p hp w hC hZwmeas hZwbigO hZwbound
  have hG : gradResponseMoment (m := S.m) 4 4 P w ^ ((1 : ℝ) / 2) ≤
      nablaW4SqrtConst C * ((S.LPrime - S.ell : ℕ) : ℝ) * nu⁻¹ := by
    refine le_trans hnabla (mul_le_mul_of_nonneg_left hpnu ?_)
    exact mul_nonneg (nablaW4SqrtConst_nonneg C) (le_of_lt hLL)
  have hGM : M * gradResponseMoment (m := S.m) 4 4 P w ^ ((1 : ℝ) / 2) ≤
      M * (nablaW4SqrtConst C * ((S.LPrime - S.ell : ℕ) : ℝ) * nu⁻¹) :=
    mul_le_mul_of_nonneg_left hG hM0
  -- the arithmetic of the rate reduction
  have hnupow : nu⁻¹ * nu ^ (-(2 : ℝ)) * nu⁻¹ = nu ^ (-(4 : ℝ)) := by
    rw [show nu⁻¹ = nu ^ (-(1 : ℝ)) from (Real.rpow_neg_one nu).symm,
      ← Real.rpow_add hnu, ← Real.rpow_add hnu]
    norm_num
  have hMG : M * (nablaW4SqrtConst C * ((S.LPrime - S.ell : ℕ) : ℝ) * nu⁻¹) =
      swapConst d C CL * (nu⁻¹ * nu ^ (-(2 : ℝ)) * nu⁻¹) *
        (((S.LPrime - S.ell : ℕ) : ℝ) * ((S.LPrime - S.ell : ℕ) : ℝ)) * T := by
    rw [hMdef, hAdef, hBdef, swapConst]
    ring
  have hLLle : ((S.LPrime - S.ell : ℕ) : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := by
    have h : S.LPrime - S.ell ≤ S.LPrime := Nat.sub_le _ _
    exact_mod_cast h
  have hL1 : (1 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := by
    have h : 1 ≤ S.LPrime := by omega
    exact_mod_cast h
  have hsquare : ((S.LPrime - S.ell : ℕ) : ℝ) * ((S.LPrime - S.ell : ℕ) : ℝ) ≤
      ((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ) := by
    have h1 := mul_le_mul hLLle hLLle (le_of_lt hLL) (le_trans zero_le_one hL1)
    have h3 : ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) ≤ ((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ) :=
      pow_le_pow_right₀ hL1 (by norm_num)
    have h4 : ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) =
        ((S.LPrime : ℕ) : ℝ) * ((S.LPrime : ℕ) : ℝ) := by ring
    linarith only [h1, h3, h4]
  have hTle : T ≤ (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ) / 4)) := by
    rw [hTdef]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h : (0 : ℝ) ≤ ((S.ell - S.n : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith only [h]
  have hswap0 : (0 : ℝ) ≤ swapConst d C CL := by
    rw [swapConst]
    have h1 := streamTailConst_pos hd0
    have h2 := nablaW4SqrtConst_nonneg C
    positivity
  have hfinal : swapConst d C CL * (nu⁻¹ * nu ^ (-(2 : ℝ)) * nu⁻¹) *
      (((S.LPrime - S.ell : ℕ) : ℝ) * ((S.LPrime - S.ell : ℕ) : ℝ)) * T ≤
      swapConst d C CL * nu ^ (-(4 : ℝ)) * ((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ) *
        (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ) / 4)) := by
    rw [hnupow]
    have hc0 : (0 : ℝ) ≤ swapConst d C CL * nu ^ (-(4 : ℝ)) :=
      mul_nonneg hswap0 (le_of_lt (Real.rpow_pos_of_pos hnu _))
    refine mul_le_mul (mul_le_mul_of_nonneg_left hsquare hc0) hTle (le_of_lt hT0) ?_
    exact mul_nonneg hc0 (by positivity)
  rw [hMG] at hGM
  linarith only [hholder, hGM, hfinal]

end

end SuperdiffusionCLT.Section3.Terms
