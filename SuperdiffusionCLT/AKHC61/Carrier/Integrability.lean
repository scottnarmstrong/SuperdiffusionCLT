/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Integrability
public import SuperdiffusionCLT.Section2.Annealed.Measurability
public import SuperdiffusionCLT.Section2.CoarseGraining.CutoffCorrespondence
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Package A1: integrability of the coarse block matrix entries under (P2')

[AK, Theorem 6.1] (`SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`)
is applied to the infrared cutoff field. Before its (P2')/(P3') hypotheses can
be used, the annealed block matrices they refer to
(`SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix`) must be
genuine Bochner integrals, i.e. every entry of the coarse block matrix
`bfA_L(cu)` of the cutoff field must be `P`-integrable, for every triadic cube.
This module supplies that integrability from `0 < nu` and the (P2') clause
alone, **without** J3 (the root's (P2')/(P3') binders do not carry it).

## Route

* diagonal entries of `bfA_L(cu_j)` at the base cube `cu_j = originCube d j`,
  `j ≥ m2`: if such an entry were not `P`-integrable, its Bochner integral
  (the corresponding entry of `annealedBlockMatrix`) would be the Lean junk
  value `0`. (P2') tested at `Q := cu_j` itself (scale exponent `0`) then
  forces the entry to be `≤ 0` pointwise, contradicting the strict positivity
  of the coarse block matrix's diagonal entries, which holds unconditionally
  (`Homogenization.Book.Ch02.bCoarse_posDef`,
  `Homogenization.Book.Ch02.sigmaStarCoarse_posDef`, no probability-law
  hypothesis at all) since the cutoff field's symmetric part is the constant
  `nu • 1`.
* off-diagonal entries at `cu_j` follow from the `2×2` positive-semidefinite
  minor bound already proved in
  `SuperdiffusionCLT.Section2.Annealed.BlockAverageBound`.
* a general triadic cube `Q` with `Q.scale ≤ j` is dominated, via (P2') again,
  by `(1 + 3^{-γ(Q.scale-j)} X) • Ahom(cu_j)` with `Ahom(cu_j)` now a genuine
  finite matrix (the previous step) and `X` integrable: the (P2') growth
  condition, evaluated at the single exponent `p := 2` (inside its range
  `[2, pPsiS]`, since `2 < pPsiS`), gives a Pareto-type tail bound for `X` of
  order `t^{-2}`, hence a finite first moment, by the layer-cake computation
  (mirroring `SuperdiffusionCLT.AKHC61.Carrier.OrliczMoments`, specialized
  to the single exponent pair `q = 1 < p = 2` since only the general-`p`
  quantifier shape of that file's `hGrowth` does not match (P2')'s narrower
  range `2 ≤ p`, so it is re-derived here for the fixed pair rather than
  reused).

Every hypothesis of the theorem is copied **verbatim** from the (P2')
clause of the main statement; no J3, no `PsiS ≥ 1` addition, no `J1V2`/`J5`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Carrier

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

/-! ## Step 0: the (P2') growth condition at the single exponent `p := 2`

This mirrors `SuperdiffusionCLT.AKHC61.Carrier.akhc_inv_psi_le_of_growth`
of `OrliczMoments.lean`, whose `hGrowth` hypothesis is universally quantified
over `p` in a range `(1, pPsi]`. The (P2') clause of the main statement only
supplies the growth bound for `p` in `[2, pPsiS]`, a narrower range that does
not contain `(1, 2)`, so that lemma cannot be instantiated directly; the
argument is repeated here for the single fixed exponent `p := 2`, which is all
that is needed for a first moment (`q := 1 < 2`). -/

/-- The (P2') growth condition, evaluated at `t := 1`, `p := 2`, combined with
`PsiS ≥ 0` and `1 ≤ KPsiS`, forces `PsiS 1 > 0`. -/
private theorem akhc_psiS_one_pos_of_growth
    {PsiS : ℝ → ℝ} {KPsiS : ℝ}
    (hPsiSNonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ PsiS t)
    (hGrowth2 : ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ (2 : ℝ) ≤ KPsiS ^ (3 * (⌈(2 : ℝ)⌉₊) ^ 2) * (PsiS (t * s) / PsiS t)) :
    0 < PsiS 1 := by
  rcases (hPsiSNonneg 1 zero_le_one).lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    have hstep := hGrowth2 1 1 le_rfl le_rfl
    simp only [one_mul] at hstep
    rw [← hzero] at hstep
    simp only [div_zero, mul_zero] at hstep
    norm_num at hstep

/-- The (P2') growth condition at `p := 2`, combined with `PsiS 1 > 0`
(`akhc_psiS_one_pos_of_growth`), gives a Pareto-type lower bound for `PsiS` on
`[1, ∞)`: `(PsiS s)⁻¹ ≤ KPsiS^{12} (PsiS 1)⁻¹ s^{-2}`. This mirrors
`akhc_inv_psi_le_of_growth` of
`OrliczMoments.lean`, specialized to the fixed exponent `p := 2` since the
(P2') growth clause is not available for `p ∈ (1, 2)`. -/
private theorem akhc_inv_psiS_le_of_growth2
    {PsiS : ℝ → ℝ} {KPsiS : ℝ} (hKPsiS : 1 ≤ KPsiS)
    (hPsiSNonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ PsiS t)
    (hGrowth2 : ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ (2 : ℝ) ≤ KPsiS ^ (3 * (⌈(2 : ℝ)⌉₊) ^ 2) * (PsiS (t * s) / PsiS t))
    {s : ℝ} (hs : 1 ≤ s) :
    (PsiS s)⁻¹ ≤ KPsiS ^ (3 * (⌈(2 : ℝ)⌉₊) ^ 2) * (PsiS 1)⁻¹ * s ^ (-(2 : ℝ)) := by
  have hPsi1_pos : 0 < PsiS 1 := akhc_psiS_one_pos_of_growth hPsiSNonneg hGrowth2
  have hK_pos : 0 < KPsiS := lt_of_lt_of_le zero_lt_one hKPsiS
  set Kp : ℝ := KPsiS ^ (3 * (⌈(2 : ℝ)⌉₊) ^ 2) with hKp_def
  have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
  have hKp_pos : 0 < Kp := by rw [hKp_def]; positivity
  have hstep := hGrowth2 1 s le_rfl hs
  rw [one_mul, div_eq_mul_inv] at hstep
  have hsp_le : s ^ (2 : ℝ) ≤ (Kp * (PsiS 1)⁻¹) * PsiS s := by nlinarith only [hstep]
  have hsp_pos : 0 < s ^ (2 : ℝ) := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hs) 2
  have hcoef_pos : 0 < Kp * (PsiS 1)⁻¹ := by positivity
  have hdiv : s ^ (2 : ℝ) / (Kp * (PsiS 1)⁻¹) ≤ PsiS s :=
    (div_le_iff₀ hcoef_pos).2 (by linarith only [hsp_le])
  have hdiv_pos : 0 < s ^ (2 : ℝ) / (Kp * (PsiS 1)⁻¹) := div_pos hsp_pos hcoef_pos
  have hinv : (PsiS s)⁻¹ ≤ (s ^ (2 : ℝ) / (Kp * (PsiS 1)⁻¹))⁻¹ := inv_anti₀ hdiv_pos hdiv
  have hrw : (s ^ (2 : ℝ) / (Kp * (PsiS 1)⁻¹))⁻¹ = Kp * (PsiS 1)⁻¹ * s ^ (-(2 : ℝ)) := by
    rw [inv_div, div_eq_mul_inv, ← Real.rpow_neg hs0]
  rwa [hrw] at hinv

/-- **First-moment finiteness from (P2')'s growth condition, without `PsiS ≥ 1`
normalization.** For `X` with `IndependentSums.IsBigO mu PsiS X A` (tail
`P[|X| > At] ≤ PsiS(t)⁻¹` for `t ≥ 1`) and the (P2') growth condition, `X` has
a finite first moment. This is the layer-cake computation of
`SuperdiffusionCLT.AKHC61.Carrier.akhc_integrable_abs_rpow_of_isBigO`
(`OrliczMoments.lean`), specialized to `q := 1 < p := 2`, and re-derived
because that file's `hGrowth` needs the growth bound for every
`p ∈ (1, pPsi]`, while (P2') only supplies it on `[2, pPsiS]`. -/
private theorem akhc_integrable_of_isBigO_growth2
    {PsiS : ℝ → ℝ} {KPsiS A : ℝ} (hKPsiS : 1 ≤ KPsiS)
    (hPsiSNonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ PsiS t)
    (hGrowth2 : ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ (2 : ℝ) ≤ KPsiS ^ (3 * (⌈(2 : ℝ)⌉₊) ^ 2) * (PsiS (t * s) / PsiS t))
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
    {X : Ω → ℝ} (hA : 0 < A) (hXm : Measurable X)
    (hX : Homogenization.IndependentSums.IsBigO mu PsiS X A) :
    Integrable X mu := by
  set Kp : ℝ := KPsiS ^ (3 * (⌈(2 : ℝ)⌉₊) ^ 2) * (PsiS 1)⁻¹ with hKp_def
  have hPsi1_pos : 0 < PsiS 1 := akhc_psiS_one_pos_of_growth hPsiSNonneg hGrowth2
  have hK_pos : 0 < KPsiS := lt_of_lt_of_le zero_lt_one hKPsiS
  have hKp_pos : 0 < Kp := by rw [hKp_def]; positivity
  -- The tail bound for `X` at the genuine scale `t ≥ A`.
  have hTailGen : ∀ t : ℝ, A ≤ t →
      mu.real {a : Ω | t < |X a|} ≤ Kp * A ^ (2 : ℝ) * t ^ (-(2 : ℝ)) := by
    intro t htA
    have hst : 1 ≤ t / A := by rw [le_div_iff₀ hA]; linarith only [htA]
    have h1 := (hX hst).trans (akhc_inv_psiS_le_of_growth2 hKPsiS hPsiSNonneg hGrowth2 hst)
    have heq : A * (t / A) = t := by field_simp
    have htpos : 0 < t := lt_of_lt_of_le hA htA
    have hdiv : (t / A) ^ (-(2 : ℝ)) = A ^ (2 : ℝ) * t ^ (-(2 : ℝ)) := by
      rw [Real.div_rpow htpos.le hA.le, Real.rpow_neg hA.le, div_eq_mul_inv, inv_inv]
      ring
    have hset : IndependentSums.upperTailEvent (fun a => |X a|) (A * (t / A)) =
        {a : Ω | t < |X a|} := by
      rw [heq]; rfl
    rw [hset, hdiv] at h1
    linarith only [h1]
  have hTail1 : ∀ t : ℝ, mu {a : Ω | t < |X a|} ≤ (1 : ENNReal) := fun t =>
    (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  have hLayer := MeasureTheory.lintegral_eq_lintegral_meas_lt (μ := mu)
    (f := fun ω => |X ω|) (Filter.Eventually.of_forall fun ω => abs_nonneg (X ω))
    (continuous_abs.measurable.comp hXm).aemeasurable
  have hUnion : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) A ∪ Set.Ioi A := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
    constructor
    · intro hx
      by_cases hxA : x ≤ A
      · exact Or.inl ⟨hx, hxA⟩
      · exact Or.inr (lt_of_not_ge hxA)
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · exact lt_trans hA hx
  have hsplit : ∫⁻ t in Set.Ioi (0 : ℝ), mu {a : Ω | t < |X a|} =
      (∫⁻ t in Set.Ioc (0 : ℝ) A, mu {a : Ω | t < |X a|})
        + ∫⁻ t in Set.Ioi A, mu {a : Ω | t < |X a|} := by
    rw [hUnion]
    exact MeasureTheory.lintegral_union measurableSet_Ioi
      (Set.disjoint_left.2 fun x (hx : x ∈ Set.Ioc (0 : ℝ) A) => not_lt.mpr hx.2)
  have hP1 : ∫⁻ t in Set.Ioc (0 : ℝ) A, mu {a : Ω | t < |X a|} ≤ ENNReal.ofReal A := by
    refine (setLIntegral_mono' measurableSet_Ioc fun t _ => hTail1 t).trans ?_
    simp [Real.volume_Ioc]
  have hf2 : IntegrableOn (fun t : ℝ => t ^ (-(2 : ℝ))) (Set.Ioi A) volume :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hA
  have hnn2 : 0 ≤ᵐ[volume.restrict (Set.Ioi A)] fun t : ℝ => t ^ (-(2 : ℝ)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (lt_trans hA ht).le _
  have hval2 : ∫ t : ℝ in Set.Ioi A, t ^ (-(2 : ℝ)) = A ^ (-(1 : ℝ)) := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hA]
    norm_num
  have hpoint2 : ∀ t ∈ Set.Ioi A, mu {a : Ω | t < |X a|} ≤
      ENNReal.ofReal (Kp * A ^ (2 : ℝ) * t ^ (-(2 : ℝ))) := by
    intro t htA
    have htail_ne_top : mu {a : Ω | t < |X a|} ≠ ⊤ := by finiteness
    have heq : mu {a : Ω | t < |X a|} = ENNReal.ofReal (mu.real {a : Ω | t < |X a|}) := by
      simp [Measure.real, htail_ne_top]
    rw [heq]
    exact ENNReal.ofReal_le_ofReal (hTailGen t htA.le)
  have hP2 : ∫⁻ t in Set.Ioi A, mu {a : Ω | t < |X a|} ≤
      ENNReal.ofReal (Kp * A ^ (2 : ℝ) * A ^ (-(1 : ℝ))) := by
    refine (setLIntegral_mono' measurableSet_Ioi hpoint2).trans ?_
    have hInt : Integrable (fun t : ℝ => Kp * A ^ (2 : ℝ) * t ^ (-(2 : ℝ)))
        (volume.restrict (Set.Ioi A)) := by
      simpa [IntegrableOn] using hf2.const_mul (Kp * A ^ (2 : ℝ))
    have hnn2' : 0 ≤ᵐ[volume.restrict (Set.Ioi A)]
        fun t : ℝ => Kp * A ^ (2 : ℝ) * t ^ (-(2 : ℝ)) := by
      filter_upwards [hnn2] with t ht; exact mul_nonneg (by positivity) ht
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn2']
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [MeasureTheory.integral_const_mul, hval2]
  have hfin : ∫⁻ ω, ENNReal.ofReal |X ω| ∂mu < ⊤ := by
    rw [hLayer, hsplit]
    refine lt_of_le_of_lt (add_le_add hP1 hP2) ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  have hnn : 0 ≤ᵐ[mu] fun ω => |X ω| := Filter.Eventually.of_forall fun ω => abs_nonneg _
  have hIntAbs : Integrable (fun ω => |X ω|) mu := by
    refine ⟨(continuous_abs.measurable.comp hXm).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnn]
    exact hfin
  exact (MeasureTheory.integrable_norm_iff hXm.aestronglyMeasurable).1
    (by simpa [Real.norm_eq_abs] using hIntAbs)

/-! ## Step D: the coarse block matrix of the cutoff field is strictly
positive-definite on its diagonal, at every triadic cube, deterministically

This is unconditional: it uses only `0 < nu` (the symmetric part of the
cutoff field is the constant `nu • 1`), through the already-proved
`Homogenization.Book.Ch02.bCoarse_posDef` and
`Homogenization.Book.Ch02.sigmaStarCoarse_posDef`, no probability-law
hypothesis. -/

variable {d : ℕ}

/-- The `Homogenization.coarseBlockMatrix` of the cutoff field on a triadic
cube agrees with the Chapter 2 public `coarseBlockMatrix` at
`SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn`,
whose lower ellipticity constant is exactly `nu`. Both Chapter 2 objects
share the same underlying field `(coefficientCutoff nu omega L).toFun`, so
they agree by `Book.Ch02.coarseBlockMatrix_eq_ofAEEq`. -/
private theorem akhc_coarseBlockMatrix_bridge_eq
    [NeZero d] {nu C : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ)
    (Q : TriadicCube d)
    (hentry : ∀ x ∈ (Book.Ch02.cubeDomain Q : Set (Vec d)), ∀ i j,
      |(coefficientCutoff nu omega L).toCoeffField x i j| ≤ C) :
    Homogenization.coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toFun =
      Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
        (SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn
          (Book.Ch02.cubeDomain Q) hnu omega L hentry) := by
  rw [coarseBlockMatrix_cubeSet_coefficientCutoff_eq_ch02 hnu omega L Q]
  refine Book.Ch02.coarseBlockMatrix_eq_ofAEEq ?_
  show
    ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (coefficientCutoff nu omega L)
        (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)).coeffOn Q).toCoeffField
      =ᵐ[volumeMeasureOn (Book.Ch02.cubeDomain Q : Set (Vec d))]
      (SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn
        (Book.Ch02.cubeDomain Q) hnu omega L hentry).toCoeffField
  rw [Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField,
    SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn_toCoeffField]
  exact Filter.Eventually.of_forall fun x => rfl

/-- `cubeCenter (originCube d j) ∈ cubeSet (originCube d j)`, and the scale of
`originCube d j` is `j`: the two side conditions needed to instantiate (P2')
at `Q := originCube d j` itself. -/
private theorem akhc_originCube_self_mem [NeZero d] (j : ℤ) :
    (originCube d j).scale ≤ j ∧
      cubeCenter (originCube d j) ∈ cubeSet (originCube d j) := by
  refine ⟨le_refl j, ?_⟩
  have hcenter : cubeCenter (originCube d j) = (0 : Vec d) := by
    funext i
    show ((originCube d j).index i : ℝ) * cubeScaleFactor (originCube d j) = 0
    simp [originCube]
  rw [hcenter, mem_cubeSet_originCube_iff]
  intro i
  simp only [Pi.zero_apply]
  have hpow : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  constructor
  · nlinarith only [hpow]
  · nlinarith only [hpow]

/-- **Every diagonal entry of the coarse block matrix of the cutoff field is
strictly positive, at every triadic cube and every sample.** This is
unconditional: the symmetric part of `a_L = nu Id + k_L` is the constant
`nu • 1`, so `Homogenization.Book.Ch02.bCoarse_posDef` (potential block) and
`Homogenization.Book.Ch02.sigmaStarCoarse_posDef` together with
`Matrix.PosDef.inv` (flux block, via `coarseBlockMatrix_lowerRight = sigmaStarCoarse⁻¹`)
give positive-definiteness with no probability-law hypothesis at all. -/
private theorem akhc_pos_blockMatEntry_diag
    [NeZero d] {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ)
    (Q : TriadicCube d) (alpha : BlockCoord d) :
    0 < blockMatEntry
      (Homogenization.coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toFun)
      alpha alpha := by
  obtain ⟨C, hC⟩ := exists_entryBound_coefficientCutoff nu omega L Q
  have hentry : ∀ x ∈ (Book.Ch02.cubeDomain Q : Set (Vec d)), ∀ i j,
      |(coefficientCutoff nu omega L).toCoeffField x i j| ≤ C := by
    rw [Book.Ch02.cubeDomain_coe]
    exact fun x hx i j => hC x (openCubeSet_subset_cubeSet Q hx) i j
  rw [akhc_coarseBlockMatrix_bridge_eq hnu omega L Q hentry]
  set a := SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn
    (Book.Ch02.cubeDomain Q) hnu omega L hentry with ha_def
  cases alpha with
  | inl i =>
      show 0 < (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) a).upperLeft i i
      rw [SuperdiffusionCLT.Section2.CoarseGraining.coarseBlockMatrix_upperLeft
        (Book.Ch02.cubeDomain Q) a]
      exact (SuperdiffusionCLT.Section2.CoarseGraining.bCoarse_coefficientCutoff_posDef
        (Book.Ch02.cubeDomain Q) hnu omega L hentry).diag_pos
  | inr i =>
      show 0 < (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) a).lowerRight i i
      rw [SuperdiffusionCLT.Section2.CoarseGraining.coarseBlockMatrix_lowerRight
        (Book.Ch02.cubeDomain Q) a]
      exact ((SuperdiffusionCLT.Section2.CoarseGraining.sigmaStarCoarse_coefficientCutoff_posDef
        (Book.Ch02.cubeDomain Q) hnu omega L hentry).inv).diag_pos

/-! ## Step E: diagonal integrability at the base cube `cu_j`, by contradiction -/

/-- `BlockMatLoewnerLE A B` gives the diagonal comparison at every block
coordinate, by testing the quadratic form at `blockBasis alpha`. -/
private theorem akhc_diag_le_of_blockMatLoewnerLE {A B : BlockMat d}
    (h : BlockMatLoewnerLE A B) (alpha : BlockCoord d) :
    blockMatEntry A alpha alpha ≤ blockMatEntry B alpha alpha := by
  have hle := h (blockBasis alpha)
  rw [blockBasis_pairing, blockBasis_pairing] at hle
  linarith only [hle]

/-- A diagonal entry of `annealedBlockMatrix` is the Bochner integral of the
corresponding entry of the coarse block matrix (the definition of
`annealedBlockMatrix`, unfolded at a diagonal block coordinate). -/
private theorem akhc_annealedBlockMatrix_entry_eq
    (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (U : Set (Vec d))
    (alpha : BlockCoord d) :
    blockMatEntry (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P U)
        alpha alpha =
      ∫ omega, blockMatEntry
          (Homogenization.coarseBlockMatrix U (coefficientCutoff nu omega L).toCoeffField)
          alpha alpha ∂P.toMeasure := by
  cases alpha with
  | inl i =>
      show (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P U).upperLeft i i =
        ∫ omega, (Homogenization.coarseBlockMatrix U
          (coefficientCutoff nu omega L).toFun).upperLeft i i ∂P.toMeasure
      exact SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix_upperLeft_apply
        nu L P U i i
  | inr i =>
      show (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P U).lowerRight i i =
        ∫ omega, (Homogenization.coarseBlockMatrix U
          (coefficientCutoff nu omega L).toFun).lowerRight i i ∂P.toMeasure
      exact SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix_lowerRight_apply
        nu L P U i i

/-- `Nonempty (ShellSeq d)`, from `P.toMeasure` being a probability measure. -/
private theorem akhc_nonempty_shellSeq (P : ProbabilityMeasure (ShellSeq d)) :
    Nonempty (ShellSeq d) := by
  obtain ⟨omega0, -⟩ := MeasureTheory.nonempty_of_measure_ne_zero
    (μ := P.toMeasure) (s := (Set.univ : Set (ShellSeq d))) (by simp)
  exact ⟨omega0⟩

/-- **Diagonal entries of `bfA_L(cu_j)` are `P`-integrable, `j ≥ m2`.** If a
diagonal entry were not integrable, its Bochner integral (the corresponding
entry of `annealedBlockMatrix nu L P (cubeSet (originCube d j))`) would be the
Lean junk value `0`. (P2') tested at `Q := originCube d j` itself (scale
exponent `0`) then forces every sample's diagonal entry of `bfA_L(cu_j)` to be
`≤ 0`, contradicting `akhc_pos_blockMatEntry_diag`. -/
private theorem akhc_integrable_blockMatEntry_diag_originCube
    [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
    (gamma : ℝ) (j : ℕ)
    {X : ShellSeq d → ℝ}
    (hLoewner : ∀ (omega : ShellSeq d) (Q : TriadicCube d),
      Q.scale ≤ (j : ℤ) →
      cubeCenter Q ∈ cubeSet (originCube d (j : ℤ)) →
      BlockMatLoewnerLE
        (Homogenization.coarseBlockMatrix (cubeSet Q)
          (coefficientCutoff nu omega L).toCoeffField)
        ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
          SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
            (cubeSet (originCube d (j : ℤ)))))
    (alpha : BlockCoord d) :
    Integrable (fun omega => blockMatEntry
        (Homogenization.coarseBlockMatrix (cubeSet (originCube d (j : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) alpha alpha) P.toMeasure := by
  by_contra hni
  have hzero : blockMatEntry (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
      (cubeSet (originCube d (j : ℤ)))) alpha alpha = 0 := by
    rw [akhc_annealedBlockMatrix_entry_eq]
    exact MeasureTheory.integral_undef hni
  obtain ⟨hscaleLe, hcenterMem⟩ := akhc_originCube_self_mem (d := d) (j : ℤ)
  obtain ⟨omega0⟩ := akhc_nonempty_shellSeq P
  have hle := akhc_diag_le_of_blockMatLoewnerLE
    (hLoewner omega0 (originCube d (j : ℤ)) hscaleLe hcenterMem) alpha
  have hexp : ((originCube d (j : ℤ)).scale : ℝ) - (j : ℝ) = 0 := by
    show (j : ℝ) - (j : ℝ) = 0
    ring
  rw [hexp, mul_zero, neg_zero, Real.rpow_zero] at hle
  have hsmulEntry : blockMatEntry
      ((1 + 1 * X omega0) •
        SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
          (cubeSet (originCube d (j : ℤ)))) alpha alpha =
      (1 + 1 * X omega0) * blockMatEntry
        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
          (cubeSet (originCube d (j : ℤ)))) alpha alpha := by
    cases alpha with
    | inl i => rfl
    | inr i => rfl
  rw [hsmulEntry, hzero, mul_zero] at hle
  exact absurd hle (not_le.2 (akhc_pos_blockMatEntry_diag hnu omega0 L (originCube d (j : ℤ)) alpha))

/-! ## Step F: a general triadic cube lies inside some large enough `cu_j` -/

/-- Every triadic cube's centre lies in `cubeSet (originCube d j)` for `j`
large enough, and above any given `m2` and the cube's own scale: the two side
conditions needed to instantiate (P2') at a general `Q`. -/
private theorem akhc_exists_j_originCube_mem [NeZero d] (Q : TriadicCube d) (m2 : ℕ) :
    ∃ j : ℕ, m2 ≤ j ∧ Q.scale ≤ (j : ℤ) ∧
      cubeCenter Q ∈ cubeSet (originCube d (j : ℤ)) := by
  classical
  set B : ℝ := ∑ i : Fin d, |cubeCenter Q i| with hB_def
  obtain ⟨j0, hj0⟩ := pow_unbounded_of_one_lt (2 * B) (show (1 : ℝ) < 3 by norm_num)
  set j : ℕ := m2 ⊔ Q.scale.toNat ⊔ j0 with hj_def
  have hj_m2 : m2 ≤ j := le_trans le_sup_left le_sup_left
  have hj_toNat : Q.scale.toNat ≤ j := le_trans le_sup_right le_sup_left
  have hj_j0 : j0 ≤ j := le_sup_right
  refine ⟨j, hj_m2, ?_, ?_⟩
  · calc Q.scale ≤ (Q.scale.toNat : ℤ) := Int.self_le_toNat Q.scale
      _ ≤ (j : ℤ) := by exact_mod_cast hj_toNat
  · rw [mem_cubeSet_originCube_iff]
    intro i
    have hzpow : (3 : ℝ) ^ (j : ℤ) = (3 : ℝ) ^ j := by rw [zpow_natCast]
    have hmono : (3 : ℝ) ^ j0 ≤ (3 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hj_j0
    have hkey : 2 * B < (3 : ℝ) ^ (j : ℤ) := by rw [hzpow]; exact lt_of_lt_of_le hj0 hmono
    have hBi : |cubeCenter Q i| ≤ B := by
      have := Finset.single_le_sum (f := fun i : Fin d => |cubeCenter Q i|)
        (fun i _ => abs_nonneg _) (Finset.mem_univ i)
      simpa [hB_def] using this
    rw [abs_le] at hBi
    exact ⟨by linarith only [hBi.1, hkey], by linarith only [hBi.2, hkey]⟩

/-! ## Step G: diagonal integrability at a general triadic cube -/

/-- Scalar multiples of a block matrix act entrywise on the diagonal. -/
private theorem akhc_smul_blockMatEntry_diag (t : ℝ) (M : BlockMat d) (alpha : BlockCoord d) :
    blockMatEntry (t • M) alpha alpha = t * blockMatEntry M alpha alpha := by
  cases alpha with
  | inl i => rfl
  | inr i => rfl

/-- Every diagonal entry of the coarse block matrix of the cutoff field is
`≥ 0` at every sample (positive semidefiniteness, unconditional). -/
private theorem akhc_nonneg_blockMatEntry_diag [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (L : ℕ) (Q : TriadicCube d) (alpha : BlockCoord d) :
    0 ≤ blockMatEntry
      (Homogenization.coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField)
      alpha alpha := by
  have h := zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff hnu omega L Q (blockBasis alpha)
  rwa [blockBasis_pairing] at h

/-- **Diagonal entries of `bfA_L(Q)` are `P`-integrable, at every triadic
cube `Q`.** `Q` is placed inside a large enough base cube `cu_j`
(`akhc_exists_j_originCube_mem`); the diagonal entries of `bfA_L(cu_j)` are
already integrable (`akhc_integrable_blockMatEntry_diag_originCube`), giving a
finite `Aval ≥ 0`; (P2') dominates `bfA_L(Q)`'s diagonal entry by
`Aval + c·Aval·|X|` with `c := 3^{-γ(Q.scale-j)} > 0`, and `X` has a finite
first moment by the (P2') growth condition at `p := 2`
(`akhc_integrable_of_isBigO_growth2`). -/
private theorem akhc_integrable_blockMatEntry_diag_general
    [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
    (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
    (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
    (hPsiSNonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ PsiS t)
    (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
    (hP2 : ∀ j : ℕ, m2 ≤ j →
      ∃ X : ShellSeq d → ℝ, Measurable X ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
        ∀ (omega : ShellSeq d) (R : TriadicCube d),
          R.scale ≤ (j : ℤ) → cubeCenter R ∈ cubeSet (originCube d (j : ℤ)) →
          BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (cubeSet R)
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((R.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (cubeSet (originCube d (j : ℤ)))))
    (Q : TriadicCube d) (alpha : BlockCoord d) :
    Integrable (fun omega => blockMatEntry
        (Homogenization.coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField)
        alpha alpha) P.toMeasure := by
  obtain ⟨j, hjm2, hjscale, hjmem⟩ := akhc_exists_j_originCube_mem Q m2
  obtain ⟨X, hXm, hXbig, hLoewner⟩ := hP2 j hjm2
  have hDiagCuJ := akhc_integrable_blockMatEntry_diag_originCube hnu P L gamma j hLoewner alpha
  set Aval : ℝ := blockMatEntry (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
      nu L P (cubeSet (originCube d (j : ℤ)))) alpha alpha with hAval_def
  have hAvalEq := akhc_annealedBlockMatrix_entry_eq nu L P (cubeSet (originCube d (j : ℤ))) alpha
  have hAval_nonneg : 0 ≤ Aval := by
    rw [hAval_def, hAvalEq]
    exact MeasureTheory.integral_nonneg
      fun omega => akhc_nonneg_blockMatEntry_diag hnu omega L (originCube d (j : ℤ)) alpha
  have hGrowth2 : ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ (2 : ℝ) ≤ KPsiS ^ (3 * (⌈(2 : ℝ)⌉₊) ^ 2) * (PsiS (t * s) / PsiS t) :=
    fun t s ht hs => hGrowth 2 le_rfl hpPsiS.le t s ht hs
  set A' : ℝ := max (H * (j : ℝ) ^ D) 1 with hA'_def
  have hA'_pos : 0 < A' := lt_of_lt_of_le zero_lt_one (le_max_right _ 1)
  have hX' : Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X A' :=
    hXbig.mono_scale (le_max_left (H * (j : ℝ) ^ D) 1)
  have hXint : Integrable X P.toMeasure :=
    akhc_integrable_of_isBigO_growth2 hKPsiS hPsiSNonneg hGrowth2 hA'_pos hXm hX'
  have hXabsint : Integrable (fun omega => |X omega|) P.toMeasure := hXint.abs
  set c : ℝ := (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) with hc_def
  have hc_pos : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hmaj_int : Integrable (fun omega => Aval + c * Aval * |X omega|) P.toMeasure :=
    (integrable_const Aval).add (hXabsint.const_mul (c * Aval))
  refine Integrable.mono' hmaj_int
    (SuperdiffusionCLT.Section2.Annealed.measurable_blockMatEntry_coarseBlockMatrix
      hnu L Q alpha alpha).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  have hle := akhc_diag_le_of_blockMatLoewnerLE (hLoewner omega Q hjscale hjmem) alpha
  rw [akhc_smul_blockMatEntry_diag, ← hAval_def, ← hc_def] at hle
  have hnn := akhc_nonneg_blockMatEntry_diag hnu omega L Q alpha
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hprod : c * Aval * X omega ≤ c * Aval * |X omega| :=
    mul_le_mul_of_nonneg_left (le_abs_self (X omega)) (mul_nonneg hc_pos.le hAval_nonneg)
  have hexpand : (1 + c * X omega) * Aval = Aval + c * Aval * X omega := by ring
  rw [hexpand] at hle
  linarith only [hle, hprod]

/-! ## Step H: off-diagonal entries, from the `2×2` positive-semidefinite
minor bound -/

/-- **Every entry of `bfA_L(Q)` is `P`-integrable, at every triadic cube `Q`
and every pair of block coordinates.** The diagonal case is
`akhc_integrable_blockMatEntry_diag_general`; the general case follows from
the `2×2` PSD-minor bound `abs_blockMatEntry_le_of_isSymmetricBlockMat`
(`SuperdiffusionCLT.Section2.Annealed.BlockAverageBound`, unconditional),
which bounds `|bfA_L(Q)_{αβ}|` by the mean of the two diagonal entries. -/
private theorem akhc_integrable_blockMatEntry_general
    [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
    (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
    (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
    (hPsiSNonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ PsiS t)
    (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
    (hP2 : ∀ j : ℕ, m2 ≤ j →
      ∃ X : ShellSeq d → ℝ, Measurable X ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
        ∀ (omega : ShellSeq d) (R : TriadicCube d),
          R.scale ≤ (j : ℤ) → cubeCenter R ∈ cubeSet (originCube d (j : ℤ)) →
          BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (cubeSet R)
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((R.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (cubeSet (originCube d (j : ℤ)))))
    (Q : TriadicCube d) (alpha beta : BlockCoord d) :
    Integrable (fun omega => blockMatEntry
        (Homogenization.coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField)
        alpha beta) P.toMeasure := by
  have hDiagA := akhc_integrable_blockMatEntry_diag_general hnu P L gamma H D m2 PsiS KPsiS pPsiS
    hKPsiS hpPsiS hPsiSNonneg hGrowth hP2 Q alpha
  have hDiagB := akhc_integrable_blockMatEntry_diag_general hnu P L gamma H D m2 PsiS KPsiS pPsiS
    hKPsiS hpPsiS hPsiSNonneg hGrowth hP2 Q beta
  refine Integrable.mono' ((hDiagA.add hDiagB).div_const 2)
    (SuperdiffusionCLT.Section2.Annealed.measurable_blockMatEntry_coarseBlockMatrix
      hnu L Q alpha beta).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs]
  exact abs_blockMatEntry_le_of_isSymmetricBlockMat
    (isSymmetricBlockMat_coarseBlockMatrix_coefficientCutoff hnu omega L Q)
    (zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff hnu omega L Q) alpha beta

/-! ## Package A1: the target theorem -/

/-- **Package A1.** Every entry of the coarse block matrix `bfA_L(Q)` of the
infrared cutoff field is `P`-integrable, at every triadic cube `Q` and every
pair of block coordinates, under `0 < nu` and the (P2') clause of the root,
copied verbatim from
`SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`:
the normalization `1 ≤ PsiS t` is now part of the root's own
clause, so no extra hypothesis is added. No J3 (the root does not carry it),
no `ShellLawPrefix`/`J2`/`J4` (not needed by this proof: every ingredient is
either deterministic in the sample or reads directly off (P2')). -/
theorem akhc_integrable_blockMatEntry_of_P2
    (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
    (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
    (_hgamma0 : 0 ≤ gamma) (_hgamma1 : gamma < 1) (_hH : 1 ≤ H) (_hD : 0 ≤ D)
    (_hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
    (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
    (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
    (hP2 : ∀ j : ℕ, m2 ≤ j →
      ∃ X : ShellSeq d → ℝ, Measurable X ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
        ∀ (omega : ShellSeq d) (Q : Homogenization.TriadicCube d),
          Q.scale ≤ (j : ℤ) →
          Homogenization.cubeCenter Q ∈
              Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
            Homogenization.BlockMatLoewnerLE
              (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
              ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
                SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ))))) :
    ∀ (Q : Homogenization.TriadicCube d) (alpha beta : Homogenization.BlockCoord d),
      MeasureTheory.Integrable
        (fun omega => Homogenization.blockMatEntry
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
          alpha beta) P.toMeasure := by
  have hPsiSNonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ PsiS t :=
    fun t ht => le_trans zero_le_one (hPsiSOne t ht)
  exact akhc_integrable_blockMatEntry_general hnu P L gamma H D m2 PsiS KPsiS pPsiS
    hKPsiS hpPsiS hPsiSNonneg hGrowth hP2

end

end SuperdiffusionCLT.AKHC61.Carrier
