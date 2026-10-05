/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Besov.Basic
public import Homogenization.Book.Ch04.Theorems.Concentration
public import Homogenization.CoarseGraining.Subadditivity
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Probability.OrliczInterpolationMin
public import SuperdiffusionCLT.Section2.Annealed.Blocks
public import SuperdiffusionCLT.Section2.Annealed.CutoffRealizationPackage
public import SuperdiffusionCLT.Section2.Localization.CoarseCentering
public import SuperdiffusionCLT.Section2.Localization.LoewnerMinAlgebra
public import SuperdiffusionCLT.Section2.Localization.UnsymmetricConversion
public import SuperdiffusionCLT.Section3.Setup.CrudeBounds
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Inputs
public import SuperdiffusionCLT.Section3.Terms.TranslatedBlocks

/-!
# The mixing minscale anchored at the localization pair and the Step-E concentration

The first conjunct of the conclusion of the main statement
`sigmaStarInv_mixing_minscale` (the printed lemma `l.mixing.minscale` of the paper),
in the anchored form used by Section 3: for `h < n <= l` there is a
measurable `X = O_{Gamma_2}(CM nu^-2 3^{-(n-h)/4})` with

`s^-1_{l,*}(cu_n) <= shom^-1_{l,*}(cu_h) + X . Id` in Loewner order,

from the localization pair of `cutoff_localization`, the
Step-E descendant-average concentration and the annealed centering correction.

The three inputs are the localization pair `hLocAnchor` (whose truncated deterministic
sandwich is assembled here through the interpolation and the min{1, .} Loewner algebra), the
Step-E concentration `hStepE` at the assembled matrix-Loewner level of the depth-`(n - h)`
descendant family, and the annealed centering correction `hStepD` across the cutoffs.  The
remaining ingredients are the subadditivity realization and the `Gamma_2` triangle inequality.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.Terms

noncomputable section

/-! ## Small real-arithmetic helpers of the printed midpoint argument -/

/-- The rate conversion from the half rate at the midpoint scale to the quarter
rate at the outer scale. -/
theorem mixingRpowQuarterLE {a b : ℕ} (h2 : (2 : ℝ) * (((a : ℕ) : ℕ) : ℝ) ≥ (((b : ℕ) : ℕ) : ℝ)) :
    (3 : ℝ) ^ (-((((a : ℕ) : ℕ) : ℝ) / 2)) ≤ (3 : ℝ) ^ (-((((b : ℕ) : ℕ) : ℝ) / 4)) := by
  refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).2 ?_
  have h4 : (4 : ℝ) * ((((a : ℕ) : ℕ) : ℝ) / 2) = (2 : ℝ) * (((a : ℕ) : ℕ) : ℝ) := by ring
  have h5 : (4 : ℝ) * ((((b : ℕ) : ℕ) : ℝ) / 4) = (((b : ℕ) : ℕ) : ℝ) := by field_simp
  linarith only [h2, h4, h5]

/-- The elementary identity `nu^-1 . nu^-1 = nu^-2` of real powers. -/
private theorem mixingNuInvSqEq {nu : ℝ} (hnu : 0 < nu) :
    (nu⁻¹ : ℝ) * nu⁻¹ = nu ^ (-(2 : ℝ)) := by
  have h1 : (nu : ℝ) ^ (-(2 : ℝ)) = (nu ^ (-(1 : ℝ))) * (nu ^ (-(1 : ℝ))) := by
    rw [show (-(2 : ℝ)) = -(1 : ℝ) + -(1 : ℝ) from by ring, Real.rpow_add hnu]
  rw [h1, Real.rpow_neg_one]

/-- The split of the interpolation amplitude: the Γ₁ amplitude
`sqrt (CL nu^-2 3^-e)` of the localization anchor is
`sqrt CL . nu^-1 . 3^-(e / 2)`. -/
private theorem mixingSqrtSplit {nu CL : ℝ} (hnu : 0 < nu) (hCL : 0 ≤ CL) (e : ℝ) :
    Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-e))
      = Real.sqrt CL * nu⁻¹ * (3 : ℝ) ^ (-(e / 2)) := by
  have hnu1pos : (0 : ℝ) < nu⁻¹ := inv_pos.mpr hnu
  have hnu2 : (nu ^ (-(2 : ℝ)) : ℝ) = nu⁻¹ * nu⁻¹ := (mixingNuInvSqEq hnu).symm
  have hx : (0 : ℝ) ≤ CL * (nu⁻¹ * nu⁻¹) := by positivity
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hpow : ((3 : ℝ) ^ (-e)) = ((3 : ℝ) ^ (-(e / 2))) * ((3 : ℝ) ^ (-(e / 2))) := by
    rw [show (-e : ℝ) = -(e / 2) + -(e / 2) from by ring, Real.rpow_add h3pos]
  have e3 : Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-e))
      = Real.sqrt CL * nu⁻¹ * Real.sqrt ((3 : ℝ) ^ (-e)) := by
    rw [hnu2, Real.sqrt_mul hx (3 ^ (-e)), Real.sqrt_mul hCL (nu⁻¹ * nu⁻¹),
      Real.sqrt_mul_self hnu1pos.le]
  rw [e3, hpow,
    Real.sqrt_mul_self (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-(e / 2)))]

/-- The split of the interpolation amplitude of the localization anchor: the
`Gamma_2` amplitude `nu^-1 . sqrt (CL nu^-2 3^-a)` produced by the truncated
interpolation is dominated by the quarter-rate amplitude
`sqrt CL . nu^-2 . 3^-(b / 4)` once `2 a >= b`. -/
private theorem mixingSqrtAmpLE {nu CL : ℝ} (hnu : 0 < nu) (hCL : 0 ≤ CL) {a b : ℕ}
    (h2 : (2 : ℝ) * (((a : ℕ) : ℕ) : ℝ) ≥ (((b : ℕ) : ℕ) : ℝ)) :
    nu⁻¹ * Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((a : ℕ) : ℕ) : ℝ)))
      ≤ Real.sqrt CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((((b : ℕ) : ℕ) : ℝ) / 4)) := by
  have hnu1 : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg hnu.le _
  have hsq := mixingNuInvSqEq hnu
  have hsplit : nu⁻¹ * Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((a : ℕ) : ℕ) : ℝ)))
      = Real.sqrt CL * (nu⁻¹ * nu⁻¹) * (3 : ℝ) ^ (-(((((a : ℕ) : ℕ) : ℝ) / 2))) := by
    rw [mixingSqrtSplit hnu hCL]
    ring
  rw [hsplit, hsq]
  refine mul_le_mul_of_nonneg_left (mixingRpowQuarterLE h2)
    (mul_nonneg (Real.sqrt_nonneg CL) hnu1)

/-- The amplitude constant of the final `Gamma_2` triangle of the assembly:
the nested `gammaTriangleConst 2` factors of the truncated-average, Step-E and
Step-D pieces, with the square-root amplitude of the localization anchor. -/
def mixingAmpConst (CL CFluc CDet : ℝ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 *
    (IndependentSums.gammaTriangleConst 2 *
        (IndependentSums.gammaTriangleConst 2 * Real.sqrt CL + CFluc) + CDet)

/-! ## Small Loewner and descendants-average algebra -/

/-- Loewner order is preserved by congruence of both matrices. -/
private theorem mixingMatLoewnerLE_congr {d : ℕ} {A A' B B' : Mat d}
    (hA : A = A') (hB : B = B') (h : MatLoewnerLE A B) : MatLoewnerLE A' B' := by
  rw [← hA, ← hB]
  exact h

/-- A positive-semidefinite matrix dominates zero in Loewner order. -/
private theorem mixingMatLoewnerLE_zero_of_posSemidef {d : ℕ} {A : Mat d}
    (hpsd : A.PosSemidef) : MatLoewnerLE 0 A :=
  matLoewnerLE_of_quad_le fun y => by
    rw [quad_zero]
    exact posSemidef_quadratic_nonneg hpsd y

/-- The anchored pair with a possibly negative balanced scalar also holds with
the nonnegative truncation `max 0 t`: for `t <= 0` the pair itself pins the two
matrices together, since the coefficients `1 + t` and `1 - t` then bracket
`1`. -/
private theorem mixingMatLoewnerLE_pair_of_signed_pair {d : ℕ} {A B : Mat d} {t : ℝ}
    (hUp : MatLoewnerLE B ((1 + t) • A)) (hLow : MatLoewnerLE ((1 - t) • A) B)
    (hApos : MatLoewnerLE 0 A) :
    MatLoewnerLE B ((1 + max 0 t) • A) ∧ MatLoewnerLE ((1 - max 0 t) • A) B := by
  rcases le_total 0 t with h0 | h0
  · have hm : max 0 t = t := max_eq_right h0
    rw [hm]
    exact ⟨hUp, hLow⟩
  · have hm : max 0 t = 0 := max_eq_left h0
    simp only [hm, add_zero, sub_zero, one_smul]
    have hAq : ∀ y : Vec d, 0 ≤ vecDot y (matVecMul A y) := fun y => by
      have h0' := quad_le_of_matLoewnerLE hApos y
      linarith only [h0', quad_zero y]
    constructor
    · refine matLoewnerLE_of_quad_le fun y => ?_
      have h1 := quad_le_of_matLoewnerLE hUp y
      rw [quad_smul] at h1
      have h3 : (1 + t) * vecDot y (matVecMul A y) ≤ vecDot y (matVecMul A y) := by
        have h4 : (1 + t) * vecDot y (matVecMul A y)
            ≤ (1 + 0) * vecDot y (matVecMul A y) :=
          mul_le_mul_of_nonneg_right (by linarith only [h0]) (hAq y)
        rwa [add_zero, one_mul] at h4
      linarith only [h1, h3]
    · refine matLoewnerLE_of_quad_le fun y => ?_
      have h1 := quad_le_of_matLoewnerLE hLow y
      rw [quad_smul] at h1
      have h3 : vecDot y (matVecMul A y) ≤ (1 - t) * vecDot y (matVecMul A y) := by
        have h4 : (1 - 0) * vecDot y (matVecMul A y)
            ≤ (1 - t) * vecDot y (matVecMul A y) :=
          mul_le_mul_of_nonneg_right (by linarith only [h0]) (hAq y)
        rwa [sub_zero, one_mul] at h4
      linarith only [h1, h3]

/-- The descendants average is monotone. -/
private theorem mixingDescendantsAverage_le {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    {F G : TriadicCube d → ℝ} (h : ∀ R ∈ descendantsAtDepth Q j, F R ≤ G R) :
    descendantsAverage Q j F ≤ descendantsAverage Q j G := by
  unfold descendantsAverage
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun R hR => h R hR) ?_
  exact inv_nonneg.2 (by exact_mod_cast Nat.zero_le _)

/-- Additivity of the descendants average. -/
private theorem mixingDescendantsAverage_add {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (A B : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => A R + B R)
      = descendantsAverage Q j A + descendantsAverage Q j B := by
  simp only [descendantsAverage, Finset.sum_add_distrib]
  ring

/-- Linearity of the descendants average on the right. -/
private theorem mixingDescendantsAverage_mul_right {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (c : ℝ) (A : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => A R * c) = descendantsAverage Q j A * c := by
  simp only [descendantsAverage]
  rw [← Finset.sum_mul, mul_assoc]

/-- The matrix descendants average with a per-cube additive correction: the
average of `F` is below the average of `G` plus the average of the scalar
corrections times the identity, whenever every member satisfies the
corresponding inequality. -/
private theorem mixingDescendantsAverageMat_le_add_smul {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F G : TriadicCube d → Mat d) (g : TriadicCube d → ℝ)
    (h : ∀ R ∈ descendantsAtDepth Q j,
      MatLoewnerLE (F R) (G R + (g R) • (1 : Mat d))) :
    MatLoewnerLE (descendantsAverageMat Q j F)
      (descendantsAverageMat Q j G + (descendantsAverage Q j g) • (1 : Mat d)) := by
  refine matLoewnerLE_of_quad_le fun y => ?_
  have hrhs : vecDot y (matVecMul (descendantsAverageMat Q j G +
        (descendantsAverage Q j g) • (1 : Mat d)) y)
      = vecDot y (matVecMul (descendantsAverageMat Q j G) y)
        + (descendantsAverage Q j g) * vecNormSq y := by
    rw [quad_add, quad_smul, quad_one]
  rw [hrhs, vecDot_matVecMul_descendantsAverageMat Q j F y,
    vecDot_matVecMul_descendantsAverageMat Q j G y]
  have hperR : ∀ R ∈ descendantsAtDepth Q j,
      vecDot y (matVecMul (F R) y)
        ≤ vecDot y (matVecMul (G R) y) + (g R) * vecNormSq y := by
    intro R hR
    have hle := quad_le_of_matLoewnerLE (h R hR) y
    rw [quad_add, quad_smul, quad_one] at hle
    exact hle
  have hsplit : descendantsAverage Q j (fun R => vecDot y (matVecMul (F R) y)) ≤
      descendantsAverage Q j (fun R => vecDot y (matVecMul (G R) y)
        + (g R) * vecNormSq y) :=
    mixingDescendantsAverage_le fun R hR => hperR R hR
  rw [mixingDescendantsAverage_add] at hsplit
  have hmul : descendantsAverage Q j (fun R => (g R) * vecNormSq y)
      = (descendantsAverage Q j g) * vecNormSq y :=
    mixingDescendantsAverage_mul_right Q j _ _
  linarith only [hsplit, hmul]

/-! ## The transport of the localization pair to a descendant cube -/

/-- The coarse matrix on a translate-cube descendant is the coarse matrix on
the centred cube of the same scale read at the translated shell sequence (the
stationarity of `s^-1_{L,*}`). -/
private theorem mixingSigmaStarInvCoarse_descendant_eq {d : ℕ} [NeZero d] {nu : ℝ}
    (omega : ShellSeq d) (l : ℕ) {hk : ℤ} {R : TriadicCube d} (hRscale : R.scale = hk) :
    sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega l).toCoeffField =
      sigmaStarInvCoarse (openCubeSet (originCube d hk))
        (coefficientCutoff nu
          (ShellField.translateSequence (triadicCubeShift R) omega) l).toCoeffField := by
  rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet R,
    sigmaStarInvCoarse_openCubeSet_coefficientCutoff nu l omega R, hRscale]

/-- The signed localization pair transported from the centred cube to a
descendant cube that is a translate of it. -/
private theorem mixingPairAtTranslate {d : ℕ} [NeZero d] {nu : ℝ} {mm l : ℕ} {hk : ℤ}
    {X₀ : ShellSeq d → ℝ}
    (hpair : ∀ omega : ShellSeq d,
      MatLoewnerLE
        (sigmaStarInvCoarse (cubeSet (originCube d hk))
          (coefficientCutoff nu omega l).toCoeffField)
        ((1 + X₀ omega) • sigmaStarInvCoarse (cubeSet (originCube d hk))
          (coefficientCutoff nu omega mm).toCoeffField) ∧
      MatLoewnerLE
        ((1 - X₀ omega) • sigmaStarInvCoarse (cubeSet (originCube d hk))
          (coefficientCutoff nu omega mm).toCoeffField)
        (sigmaStarInvCoarse (cubeSet (originCube d hk))
          (coefficientCutoff nu omega l).toCoeffField))
    (R : TriadicCube d) (hRscale : R.scale = hk) (omega : ShellSeq d) :
    MatLoewnerLE
        (sigmaStarInvCoarse (cubeSet R)
          (coefficientCutoff nu omega l).toCoeffField)
        ((1 + X₀ (ShellField.translateSequence (triadicCubeShift R) omega)) •
          sigmaStarInvCoarse (cubeSet R)
            (coefficientCutoff nu omega mm).toCoeffField) ∧
      MatLoewnerLE
        ((1 - X₀ (ShellField.translateSequence (triadicCubeShift R) omega)) •
          sigmaStarInvCoarse (cubeSet R)
            (coefficientCutoff nu omega mm).toCoeffField)
        (sigmaStarInvCoarse (cubeSet R)
          (coefficientCutoff nu omega l).toCoeffField) := by
  obtain ⟨hUp, hLow⟩ := hpair (ShellField.translateSequence (triadicCubeShift R) omega)
  have eL : ∀ (w : ShellSeq d),
      sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu w l).toCoeffField =
        sigmaStarInvCoarse (cubeSet (originCube d hk))
          (coefficientCutoff nu
            (ShellField.translateSequence (triadicCubeShift R) w) l).toCoeffField :=
    fun w => by
      rw [mixingSigmaStarInvCoarse_descendant_eq w l hRscale,
        sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
  have eM : ∀ (w : ShellSeq d),
      sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu w mm).toCoeffField =
        sigmaStarInvCoarse (cubeSet (originCube d hk))
          (coefficientCutoff nu
            (ShellField.translateSequence (triadicCubeShift R) w) mm).toCoeffField :=
    fun w => by
      rw [mixingSigmaStarInvCoarse_descendant_eq w mm hRscale,
        sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
  exact ⟨mixingMatLoewnerLE_congr (eL omega).symm
      (congrArg (fun M : Mat d => (1 + X₀ (ShellField.translateSequence
        (triadicCubeShift R) omega)) • M) (eM omega).symm) hUp,
    mixingMatLoewnerLE_congr (congrArg (fun M : Mat d => (1 - X₀
        (ShellField.translateSequence (triadicCubeShift R) omega)) • M) (eM omega).symm)
      (eL omega).symm hLow⟩

/-! ## The mixing minscale of the main statement, in the anchored form -/

/-- **The mixing anchor assembled from the localization anchor and the Step-E inputs.** The first
conjunct of the conclusion of `SuperdiffusionCLT.Frozen.Section2.sigmaStarInv_mixing_minscale`
(the printed lemma `l.mixing.minscale` of the paper, standing molecular diffusivity range
`nu in (0, 1]`), stated so that it matches verbatim the `hMix` hypothesis of the Section-3
consumer `sstar_lower_bound_quenched_of_anchors`.

For every `h < n <= l` there is a measurable witness
`X = O_{Gamma_2}(CM nu^-2 3^{-(n-h)/4})` with the Loewner inequality

`s^-1_{l,*}(cu_n) <= shom^-1_{l,*}(cu_h) + X . Id`.

The inputs are:

* `hLocAnchor` — the third and fourth Loewner conjunct of the
  conclusion of `cutoff_localization`, at every admissible
  triple of scales, with the anchor's own binders and a positive constant
  `CL`, carried verbatim;
* `hStepE` — the Step-E concentration at the assembled matrix level:
  the descendants average of the midpoint-cutoff coarse matrices is
  Loewner-below the annealed block at `cu_h` plus `XFluc . Id` with
  `XFluc = O_{Gamma_2}(CFluc nu^-2 3^{-(n-h)/4})`;
* `hStepD` — the annealed centering correction across the cutoffs at
  the centred cube `cu_h`: `shom^-1_{m,*}(cu_h) <= shom^-1_{l,*}(cu_h) +
  Y . Id` with `Y = O_{Gamma_2}(CDet nu^-2 3^{-(m-h)/2})`;
* `hdom` — the constant domination of the nested triangle constant over `CM`.

The proof runs on a midpoint scale `mm` between `h` and `m`: the
subadditivity realization bounds `s^-1_{l,*}(cu_n)` by the descendants
average at cutoff `l`, the truncated deterministic sandwich
(the interpolation and the min{1, .} Loewner algebra, applied to
the transported localization pair at every descendant) bounds that average by
the descendants average at cutoff `mm` plus the truncated balanced average, and
`hStepE` and `hStepD` close the chain to `shom^-1_{l,*}(cu_h)`.  The witness is
the sum of the three `Gamma_2` pieces, at the nested-triangle amplitude
dominated by `CM` through `hdom`. -/
theorem sigmaStarInv_mixing_minscale_of_anchors_midpoint {d : ℕ} [NeZero d]
    {nu CL CM CFluc CDet : ℝ} {P : ProbabilityMeasure (ShellSeq d)}
    (hnu : 0 < nu) (hCL : 0 < CL) (hCFluc : 0 < CFluc) (hCDet : 0 < CDet)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hdom : mixingAmpConst CL CFluc CDet ≤ CM)
    (hLocAnchor : ∀ mm nn LL : ℕ, nn ≤ mm → mm ≤ LL →
        ∀ U : Book.Ch02.Domain d,
          (U : Set (Vec d)) ⊆ openCubeSet (originCube d (nn : ℤ)) →
          ∃ X : ShellSeq d → ℝ,
            Measurable X ∧
            IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) X
                (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - nn : ℕ) : ℝ))) ∧
              ∀ omega : ShellSeq d,
                MatLoewnerLE
                    ((1 - X omega) • sigmaStarInvCoarse (U : Set (Vec d))
                      (coefficientCutoff nu omega mm).toCoeffField)
                    (sigmaStarInvCoarse (U : Set (Vec d))
                      (coefficientCutoff nu omega LL).toCoeffField) ∧
                  MatLoewnerLE
                    (sigmaStarInvCoarse (U : Set (Vec d))
                      (coefficientCutoff nu omega LL).toCoeffField)
                    ((1 + X omega) • sigmaStarInvCoarse (U : Set (Vec d))
                      (coefficientCutoff nu omega mm).toCoeffField))
    {h n l mm : ℕ} (hhm : h < mm) (hmn : mm ≤ n)
    (hmid : (2 : ℝ) * (((mm - h : ℕ) : ℕ) : ℝ) ≥ (((n - h : ℕ) : ℕ) : ℝ))
    (hStepEmm : ∃ XFluc : ShellSeq d → ℝ,
          Measurable XFluc ∧
          IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) XFluc
              (CFluc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
            ∀ omega : ShellSeq d,
              MatLoewnerLE
                (descendantsAverageMat (originCube d (n : ℤ)) (n - h)
                  (fun R => sigmaStarInvCoarse (cubeSet R)
                    (coefficientCutoff nu omega mm).toCoeffField))
                (sigmaBarStarInv nu mm P (cubeSet (originCube d (h : ℤ))) +
                  XFluc omega • (1 : Mat d)))
    (hStepD : ∀ h m l : ℕ, h < m → m ≤ l →
        ∃ Y : ShellSeq d → ℝ,
          Measurable Y ∧
          IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) Y
              (CDet * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((m - h : ℕ) : ℝ) / 2))) ∧
            ∀ omega : ShellSeq d,
              MatLoewnerLE
                (sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))))
                (sigmaBarStarInv nu l P (cubeSet (originCube d (h : ℤ))) +
                  Y omega • (1 : Mat d)))
    -- The conclusion is the `hMix` hypothesis of
    -- `sstar_lower_bound_quenched_of_anchors`, verbatim:
    (hnl : n ≤ l) :
    ∃ X : ShellSeq d → ℝ,
      Measurable X ∧
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) X
          (CM * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
        ∀ omega : ShellSeq d,
          MatLoewnerLE
            (sigmaStarInvCoarse (cubeSet (originCube d (n : ℤ)))
              (coefficientCutoff nu omega l).toCoeffField)
            (sigmaBarStarInv nu l P (cubeSet (originCube d (h : ℤ))) +
              X omega • (1 : Mat d)) := by
  -- the Step-E fluctuation at the supplied scale
  obtain ⟨XFluc, hXFlucM, hXFlucO, hXFlucL⟩ := hStepEmm
  -- the annealed centering correction across the cutoffs
  obtain ⟨Y, hYM, hYO, hYL⟩ := hStepD h mm l hhm (le_trans hmn hnl)
  -- the centred cube as the localization domain
  have hneU : Set.Nonempty (openCubeSet (originCube d (h : ℤ))) := by
    refine ⟨cubeCenter (originCube d (h : ℤ)), ?_⟩
    rw [← ball_cubeCenter_eq_openCubeSet, Metric.mem_ball, dist_self]
    exact cubeRadius_pos _
  have hUcoe : (((⟨openCubeSet (originCube d (h : ℤ)),
      isOpenBoundedConvexDomain_openCubeSet _, hneU⟩ :
        Book.Ch02.Domain d) : Set (Vec d))) = openCubeSet (originCube d (h : ℤ)) := rfl
  obtain ⟨X₀, hX₀M, hX₀O, hX₀L⟩ := hLocAnchor mm h l (le_of_lt hhm)
    (le_trans hmn hnl)
    ⟨openCubeSet (originCube d (h : ℤ)), isOpenBoundedConvexDomain_openCubeSet _, hneU⟩
    (le_of_eq hUcoe)
  -- the signed pair on the centred cube, in the `cubeSet` spelling
  have hX₀pairRaw : ∀ omega : ShellSeq d,
      MatLoewnerLE
        (sigmaStarInvCoarse (cubeSet (originCube d (h : ℤ)))
          (coefficientCutoff nu omega l).toCoeffField)
        ((1 + X₀ omega) • sigmaStarInvCoarse (cubeSet (originCube d (h : ℤ)))
          (coefficientCutoff nu omega mm).toCoeffField) ∧
      MatLoewnerLE
        ((1 - X₀ omega) • sigmaStarInvCoarse (cubeSet (originCube d (h : ℤ)))
          (coefficientCutoff nu omega mm).toCoeffField)
        (sigmaStarInvCoarse (cubeSet (originCube d (h : ℤ)))
          (coefficientCutoff nu omega l).toCoeffField) := by
    intro omega
    obtain ⟨hLowRaw, hUpRaw⟩ := hX₀L omega
    rw [hUcoe] at hLowRaw hUpRaw
    have b : ∀ c : ℕ, sigmaStarInvCoarse (openCubeSet (originCube d (h : ℤ)))
        (coefficientCutoff nu omega c).toCoeffField
        = sigmaStarInvCoarse (cubeSet (originCube d (h : ℤ)))
          (coefficientCutoff nu omega c).toCoeffField := fun c => by
      rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
    exact ⟨mixingMatLoewnerLE_congr (b l)
        (congrArg (fun M : Mat d => (1 + X₀ omega) • M) (b mm)) hUpRaw,
      mixingMatLoewnerLE_congr
        (congrArg (fun M : Mat d => (1 - X₀ omega) • M) (b mm)) (b l) hLowRaw⟩
  -- the nonnegative truncation of the anchor variable
  have hXplM : Measurable (fun omega => max 0 (X₀ omega)) := measurable_const.max hX₀M
  have hXplnn : ∀ omega, 0 ≤ max 0 (X₀ omega) := fun omega => le_max_left _ _
  have hXplO : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega => max 0 (X₀ omega))
      (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ))) :=
    hX₀O.of_abs_le fun omega => by
      rcases le_total 0 (X₀ omega) with hcase | hcase
      · rw [max_eq_right hcase, abs_of_nonneg hcase]
      · rw [max_eq_left hcase, abs_zero]
        exact abs_nonneg _
  -- the interpolation (the truncated balanced variable)
  have hA1pos : (0 : ℝ) < CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ)) := by
    positivity
  have hA1nn : (0 : ℝ) ≤ CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ)) :=
    hA1pos.le
  have hY : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega => min 1 (max 0 (X₀ omega)))
      (Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ)))) :=
    isBigO_gammaSigma_min_one_of_isBigO_gammaSigma_one hA1nn hXplnn hXplO
  have hYm : Measurable (fun omega => min 1 (max 0 (X₀ omega))) :=
    measurable_min_one hXplM
  -- the transported fluctuation bound on every descendant cube
  have hYR : ∀ R : TriadicCube d,
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega => nu⁻¹ * min 1 (max 0 (X₀
          (ShellField.translateSequence (triadicCubeShift R) omega))))
        (nu⁻¹ * Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ)))) :=
    fun R => IndependentSums.IsBigO.const_mul (inv_pos.mpr hnu).le
      (isBigO_gammaSigma_translateObservable hPrefix hJ2 hYm hY R)
  -- the balanced average observable
  set tAvg : ShellSeq d → ℝ := fun omega => descendantsAverage (originCube d (n : ℤ))
    (n - h) (fun R => nu⁻¹ * min 1 (max 0 (X₀
      (ShellField.translateSequence (triadicCubeShift R) omega)))) with htAvgdef
  have htAvgM : Measurable tAvg := by
    rw [htAvgdef]
    unfold descendantsAverage
    exact measurable_const.mul (Finset.measurable_sum _ fun R _ =>
      (measurable_min_one (measurable_translateObservable hXplM R)).const_mul nu⁻¹)
  -- the finset triangle over the descendant family
  have hTavgO : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) tAvg
      (IndependentSums.gammaTriangleConst 2 *
        (nu⁻¹ * Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ))))) := by
    have hDne : (descendantsAtDepth (originCube d (n : ℤ)) (n - h)).Nonempty :=
      descendantsAtDepth_nonempty _ _
    have hcardNe : ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) ≠ 0 := by
      exact_mod_cast hDne.card_pos.ne.symm
    have ha : ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h),
        (0 : ℝ) < ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ)⁻¹ *
          (nu⁻¹ * Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ)))) :=
      fun R _ => mul_pos (inv_pos.mpr (by exact_mod_cast hDne.card_pos))
        (mul_pos (inv_pos.mpr hnu) (Real.sqrt_pos.mpr hA1pos))
    have hX : ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h),
        IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
          (fun omega => ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ)⁻¹ *
            (nu⁻¹ * min 1 (max 0 (X₀
              (ShellField.translateSequence (triadicCubeShift R) omega)))))
          (((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ)⁻¹ *
            (nu⁻¹ * Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ))))) :=
      fun R _ => IndependentSums.IsBigO.const_mul (inv_nonneg.2 (by
        exact_mod_cast Nat.zero_le _)) (hYR R)
    have hXm : ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h),
        Measurable (fun omega =>
          ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ)⁻¹ *
            (nu⁻¹ * min 1 (max 0 (X₀
              (ShellField.translateSequence (triadicCubeShift R) omega))))) :=
      fun R _ => measurable_const.mul ((measurable_min_one
        (measurable_translateObservable hXplM R)).const_mul nu⁻¹)
    have htri := Book.Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
      (descendantsAtDepth (originCube d (n : ℤ)) (n - h))
      (by norm_num : (0 : ℝ) < 2) hDne ha hX hXm
    have hfunEq : (fun omega : ShellSeq d =>
          Finset.sum (descendantsAtDepth (originCube d (n : ℤ)) (n - h))
            (fun R : TriadicCube d =>
              ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ)⁻¹ *
                (nu⁻¹ * min 1 (max 0 (X₀
                  (ShellField.translateSequence (triadicCubeShift R) omega))))))
        = tAvg := by
      funext omega
      rw [htAvgdef]
      exact (Finset.mul_sum _ _ _).symm
    have hampEq : IndependentSums.gammaTriangleConst 2 *
          Finset.sum (descendantsAtDepth (originCube d (n : ℤ)) (n - h))
            (fun R : TriadicCube d =>
              ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ)⁻¹ *
                (nu⁻¹ * Real.sqrt (CL * nu ^ (-(2 : ℝ))
                  * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ)))))
        = IndependentSums.gammaTriangleConst 2 *
          (nu⁻¹ * Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ)))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw [hfunEq, hampEq] at htri
    exact htri
  -- the per-cube transported sandwich
  have hsandR : ∀ (omega : ShellSeq d) (R : TriadicCube d),
      R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h) →
      MatLoewnerLE
        (sigmaStarInvCoarse (cubeSet R)
          (coefficientCutoff nu omega l).toCoeffField)
        (sigmaStarInvCoarse (cubeSet R)
          (coefficientCutoff nu omega mm).toCoeffField
        + (nu⁻¹ * min 1 (max 0 (X₀
          (ShellField.translateSequence (triadicCubeShift R) omega)))) • (1 : Mat d)) := by
    intro omega R hR
    have hRscale : R.scale = (h : ℤ) := by
      have h1 : R.scale = (originCube d (n : ℤ)).scale - ((n - h : ℕ) : ℤ) :=
        scale_eq_sub_of_mem_descendantsAtDepth hR
      rw [show (originCube d (n : ℤ)).scale = (n : ℤ) from rfl,
        show ((n - h : ℕ) : ℤ) = (n : ℤ) - (h : ℤ) from by omega] at h1
      omega
    have hpsdR : ∀ c : ℕ,
        (sigmaStarInvCoarse (cubeSet R)
          (coefficientCutoff nu omega c).toCoeffField).PosSemidef :=
      fun c => posSemidef_sigmaStarInvCoarse_cutoffCube hnu c omega R
    have hcrudeR : ∀ c : ℕ, MatLoewnerLE (sigmaStarInvCoarse (cubeSet R)
        (coefficientCutoff nu omega c).toCoeffField) (nu⁻¹ • (1 : Mat d)) := by
      intro c
      rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
      show MatLoewnerLE (sigmaStarInvCoarse (openCubeSet R)
        (coefficientCutoff nu omega c).toFun) (nu⁻¹ • (1 : Mat d))
      exact matLoewnerLE_sigmaStarInvCoarse_cutoffCube hnu omega c R
    obtain ⟨hUp, hLow⟩ := mixingPairAtTranslate (X₀ := X₀) (mm := mm) (l := l)
      (hk := (h : ℤ)) hX₀pairRaw R hRscale omega
    obtain ⟨hUp', hLow'⟩ := mixingMatLoewnerLE_pair_of_signed_pair hUp hLow
      (mixingMatLoewnerLE_zero_of_posSemidef (hpsdR mm))
    exact matLoewnerLE_add_min_smul_one_of_pair (hXplnn
      (ShellField.translateSequence (triadicCubeShift R) omega)) hUp' (hcrudeR mm)
      (hcrudeR l) (mixingMatLoewnerLE_zero_of_posSemidef (hpsdR mm))
  -- the average transport of the sandwich
  have havg : ∀ omega : ShellSeq d,
      MatLoewnerLE
        (descendantsAverageMat (originCube d (n : ℤ)) (n - h)
          (fun R => sigmaStarInvCoarse (cubeSet R)
            (coefficientCutoff nu omega l).toCoeffField))
        (descendantsAverageMat (originCube d (n : ℤ)) (n - h)
          (fun R => sigmaStarInvCoarse (cubeSet R)
            (coefficientCutoff nu omega mm).toCoeffField)
        + (tAvg omega) • (1 : Mat d)) :=
    fun omega => mixingDescendantsAverageMat_le_add_smul _ _ _ _
      (fun R => nu⁻¹ * min 1 (max 0 (X₀
        (ShellField.translateSequence (triadicCubeShift R) omega))))
      (fun R hR => hsandR omega R hR)
  -- the final quadratic-form chain at every omega
  have hquad : ∀ omega : ShellSeq d, ∀ y : Vec d,
      vecDot y (matVecMul (sigmaStarInvCoarse (cubeSet (originCube d (n : ℤ)))
        (coefficientCutoff nu omega l).toCoeffField) y)
      ≤ vecDot y (matVecMul (sigmaBarStarInv nu l P (cubeSet (originCube d (h : ℤ)))
        + (tAvg omega + XFluc omega + Y omega) • (1 : Mat d)) y) := by
    intro omega y
    have h1 := quad_le_of_matLoewnerLE
      (sigmaStarInvCoarse_subadditive_cubeSet_originCube_coefficientCutoff hnu omega l
        (n : ℤ) (n - h)) y
    have h2 := quad_le_of_matLoewnerLE (havg omega) y
    rw [quad_add, quad_smul, quad_one] at h2
    have h4 := quad_le_of_matLoewnerLE (hXFlucL omega) y
    rw [quad_add, quad_smul, quad_one] at h4
    have h5 := quad_le_of_matLoewnerLE (hYL omega) y
    rw [quad_add, quad_smul, quad_one] at h5
    rw [quad_add, quad_smul, quad_one]
    have hdistr : (tAvg omega + XFluc omega + Y omega) * vecNormSq y
        = tAvg omega * vecNormSq y + XFluc omega * vecNormSq y
          + Y omega * vecNormSq y := by
      rw [add_mul, add_mul]
    rw [hdistr]
    linarith only [h1, h2, h4, h5]
  -- the envelope of the three pieces
  have hfinalO : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega => tAvg omega + XFluc omega + Y omega)
      (CM * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) := by
    have hγ2 : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 :=
      IndependentSums.gammaTriangleConst_pos
    have hAmpTpos : (0 : ℝ) < IndependentSums.gammaTriangleConst 2 *
        (nu⁻¹ * Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ)))) :=
      mul_pos hγ2 (mul_pos (inv_pos.mpr hnu) (Real.sqrt_pos.mpr hA1pos))
    have hAmpFpos : (0 : ℝ) < CFluc * nu ^ (-(2 : ℝ))
        * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) :=
      mul_pos (mul_pos hCFluc (Real.rpow_pos_of_pos hnu _))
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _)
    have hAmpDpos : (0 : ℝ) < CDet * nu ^ (-(2 : ℝ))
        * (3 : ℝ) ^ (-(((mm - h : ℕ) : ℝ) / 2)) :=
      mul_pos (mul_pos hCDet (Real.rpow_pos_of_pos hnu _))
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _)
    have hstep1 := isBigO_gammaSigma_add_of_isBigO (mu := P.toMeasure) (sigma := 2)
      (by norm_num : (0 : ℝ) < 2)
      (A := IndependentSums.gammaTriangleConst 2 *
        (nu⁻¹ * Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ)))))
      (B := CFluc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)))
      hAmpTpos hAmpFpos hTavgO hXFlucO htAvgM hXFlucM
    have hstep2 := isBigO_gammaSigma_add_of_isBigO (mu := P.toMeasure) (sigma := 2)
      (by norm_num : (0 : ℝ) < 2)
      (A := IndependentSums.gammaTriangleConst 2 *
        (IndependentSums.gammaTriangleConst 2 *
          (nu⁻¹ * Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ))))
        + CFluc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))))
      (B := CDet * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((mm - h : ℕ) : ℝ) / 2)))
      (mul_pos hγ2 (add_pos hAmpTpos hAmpFpos)) hAmpDpos hstep1 hYO
      (htAvgM.add hXFlucM) hYM
    refine hstep2.mono_scale ?_
    have hrate : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) := by
      positivity
    have hs1 : IndependentSums.gammaTriangleConst 2 *
        (nu⁻¹ * Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ))))
        ≤ IndependentSums.gammaTriangleConst 2 * (Real.sqrt CL * nu ^ (-(2 : ℝ))
          * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) :=
      mul_le_mul_of_nonneg_left (mixingSqrtAmpLE hnu hCL.le hmid) hγ2.le
    have hs2 : IndependentSums.gammaTriangleConst 2 *
        (IndependentSums.gammaTriangleConst 2 *
          (nu⁻¹ * Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ))))
        + CFluc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)))
        ≤ IndependentSums.gammaTriangleConst 2 *
          (IndependentSums.gammaTriangleConst 2 * (Real.sqrt CL * nu ^ (-(2 : ℝ))
            * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)))
          + CFluc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) :=
      mul_le_mul_of_nonneg_left (add_le_add hs1 le_rfl) hγ2.le
    have hDle : CDet * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((mm - h : ℕ) : ℝ) / 2))
        ≤ CDet * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left (mixingRpowQuarterLE hmid) (by positivity)
    have hs3 : IndependentSums.gammaTriangleConst 2 *
        (IndependentSums.gammaTriangleConst 2 *
          (IndependentSums.gammaTriangleConst 2 *
            (nu⁻¹ * Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ))))
          + CFluc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)))
        + CDet * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((mm - h : ℕ) : ℝ) / 2)))
        ≤ IndependentSums.gammaTriangleConst 2 *
          (IndependentSums.gammaTriangleConst 2 *
            (IndependentSums.gammaTriangleConst 2 * (Real.sqrt CL * nu ^ (-(2 : ℝ))
              * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)))
            + CFluc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)))
          + CDet * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) :=
      mul_le_mul_of_nonneg_left (add_le_add hs2 hDle) hγ2.le
    have hkey := mul_le_mul_of_nonneg_right hdom hrate
    have e1 : mixingAmpConst CL CFluc CDet *
        (nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)))
        = IndependentSums.gammaTriangleConst 2 *
          (IndependentSums.gammaTriangleConst 2 *
            (IndependentSums.gammaTriangleConst 2 * (Real.sqrt CL * nu ^ (-(2 : ℝ))
              * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)))
            + CFluc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)))
          + CDet * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) := by
      unfold mixingAmpConst
      ring
    have e2 : CM * (nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)))
        = CM * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) :=
      (mul_assoc CM _ _).symm
    rw [e1, e2] at hkey
    calc IndependentSums.gammaTriangleConst 2 *
          (IndependentSums.gammaTriangleConst 2 *
            (IndependentSums.gammaTriangleConst 2 *
              (nu⁻¹ * Real.sqrt (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - h : ℕ) : ℝ))))
            + CFluc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)))
          + CDet * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((mm - h : ℕ) : ℝ) / 2)))
      ≤ IndependentSums.gammaTriangleConst 2 *
          (IndependentSums.gammaTriangleConst 2 *
            (IndependentSums.gammaTriangleConst 2 * (Real.sqrt CL * nu ^ (-(2 : ℝ))
              * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)))
            + CFluc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)))
          + CDet * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) := hs3
    _ ≤ CM * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) := hkey
  exact ⟨fun omega => tAvg omega + XFluc omega + Y omega,
    (htAvgM.add hXFlucM).add hYM, hfinalO, fun omega =>
    matLoewnerLE_of_quad_le (hquad omega)⟩

end

end SuperdiffusionCLT.Section2.Annealed