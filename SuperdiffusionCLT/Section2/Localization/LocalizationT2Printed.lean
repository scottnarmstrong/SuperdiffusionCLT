/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayJ
public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayL
public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayI
public import Homogenization.Book.Ch04.Theorems.PartitionAverages

/-!
# Signed concentration on localization colour classes

The signed quadratic forms in the proof of `l.localization.average` are centred before
concentration. All spatial independence statements below concern separated
colour classes. Deterministic vectors can be fixed separately on each cube.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}
/-- The normalized perturbation retains the zero mean of each signed entry. -/
theorem localizationT2Printed_integral_V_entry [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (l n : ℕ) (R : Homogenization.TriadicCube d) (hR : R.scale = (n : ℤ))
    (a b : Homogenization.BlockCoord d) :
    ∫ omega, Homogenization.toFullBlockMat (localizationV nu l P n R omega) a b
      ∂P.toMeasure = 0 := by
  have hmean := displayL_integral_perturbation_entry_zero
    hnu P hPrefix hJ2 hJ3 hJ4 l n R hR
  cases a <;> cases b <;>
    simp only [localizationV, SuperdiffusionCLT.Section2.Annealed.envelopeRescale_eq,
      Homogenization.toFullBlockMat, Matrix.smul_apply, smul_eq_mul,
      MeasureTheory.integral_const_mul]
  case inl.inl i j => exact mul_eq_zero_of_right _ (hmean (Sum.inl i) (Sum.inl j))
  case inl.inr i j => exact mul_eq_zero_of_right _ (hmean (Sum.inl i) (Sum.inr j))
  case inr.inl i j => exact mul_eq_zero_of_right _ (hmean (Sum.inr i) (Sum.inl j))
  case inr.inr i j => exact mul_eq_zero_of_right _ (hmean (Sum.inr i) (Sum.inr j))
/-- Integrability also survives deterministic envelope normalization. -/
theorem localizationT2Printed_integrable_V_entry [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (l n : ℕ) (R : Homogenization.TriadicCube d) (a b : Homogenization.BlockCoord d) :
    Integrable (fun omega => Homogenization.toFullBlockMat
      (localizationV nu l P n R omega) a b) P.toMeasure := by
  have hi := displayL_integrable_perturbation_entry hnu P hPrefix hJ2 hJ3 hJ4 l n R
  cases a <;> cases b <;>
    simp only [localizationV, SuperdiffusionCLT.Section2.Annealed.envelopeRescale_eq,
      Homogenization.toFullBlockMat, Matrix.smul_apply, smul_eq_mul]
  case inl.inl i j => exact (hi (Sum.inl i) (Sum.inl j)).const_mul _
  case inl.inr i j => exact (hi (Sum.inl i) (Sum.inr j)).const_mul _
  case inr.inl i j => exact (hi (Sum.inr i) (Sum.inl j)).const_mul _
  case inr.inr i j => exact (hi (Sum.inr i) (Sum.inr j)).const_mul _
/-- Evaluation of a signed quadratic form is a measurable matrix observable. -/
theorem localizationT2Printed_measurable_quadratic (q : Homogenization.BlockVec d) :
    Measurable (fun A : Homogenization.FullBlockMat d =>
      Homogenization.blockVecDot q
        (Homogenization.blockMatVecMul (Homogenization.ofFullBlockMat A) q)) := by
  have heq : (fun A : Homogenization.FullBlockMat d =>
      Homogenization.blockVecDot q
        (Homogenization.blockMatVecMul (Homogenization.ofFullBlockMat A) q)) =
      fun A => ∑ a, ∑ b,
        (Homogenization.toFullBlockVec q a * Homogenization.toFullBlockVec q b) * A a b := by
    funext A
    rw [Homogenization.blockVecDot_blockMatVecMul_eq_toLinearMap₂',
      Homogenization.toFullBlockMat_ofFullBlockMat, Matrix.toLinearMap₂'_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [smul_eq_mul]
    ring
  rw [heq]
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
  have hm : Measurable (fun A : Homogenization.FullBlockMat d => A a b) :=
    (measurable_pi_apply b).comp (measurable_pi_apply a)
  exact hm.const_mul _
/-- The signed quadratic form has zero mean for every fixed vector. -/
theorem localizationT2Printed_integral_quadratic [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (l n : ℕ) (R : Homogenization.TriadicCube d) (hR : R.scale = (n : ℤ))
    (q : Homogenization.BlockVec d) :
    ∫ omega, Homogenization.blockVecDot q
      (Homogenization.blockMatVecMul (localizationV nu l P n R omega) q) ∂P.toMeasure = 0 := by
  rw [blockVecDot_blockMatVecMul_eq_sum (fun _ => q) (localizationV nu l P n R)]
  change (∫ omega, (∑ p : Homogenization.BlockCoord d × Homogenization.BlockCoord d,
    fun w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
      (Homogenization.toFullBlockVec q p.1 * Homogenization.toFullBlockVec q p.2) *
        Homogenization.toFullBlockMat (localizationV nu l P n R w) p.1 p.2) omega ∂P.toMeasure) = 0
  simp only [Finset.sum_apply]
  rw [MeasureTheory.integral_finsetSum]
  · simp only [MeasureTheory.integral_const_mul,
      localizationT2Printed_integral_V_entry hnu P hPrefix hJ2 hJ3 hJ4 l n R hR,
      mul_zero, Finset.sum_const_zero]
  · intro p _
    exact (localizationT2Printed_integrable_V_entry hnu P hPrefix hJ2 hJ3 hJ4
      l n R p.1 p.2).const_mul _
/-- A unit-ball quadratic observable is dominated by the operator norm. -/
theorem localizationT2Printed_abs_quadratic_le (A : Homogenization.BlockMat d)
    (q : Homogenization.BlockVec d)
    (hq : SuperdiffusionCLT.Section2.Carriers.blockVecNorm q ^ 2 ≤ 1) :
    |Homogenization.blockVecDot q (Homogenization.blockMatVecMul A q)| ≤
      SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm A := by
  have hnorm := SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm_nonneg A
  calc
    |Homogenization.blockVecDot q (Homogenization.blockMatVecMul A q)| ≤
        SuperdiffusionCLT.Section2.Carriers.blockVecNorm q *
          SuperdiffusionCLT.Section2.Carriers.blockVecNorm
            (Homogenization.blockMatVecMul A q) := abs_blockVecDot_le_blockVecNorm_mul _ _
    _ ≤ SuperdiffusionCLT.Section2.Carriers.blockVecNorm q *
        (SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm A *
          SuperdiffusionCLT.Section2.Carriers.blockVecNorm q) :=
      mul_le_mul_of_nonneg_left
        (SuperdiffusionCLT.Section2.Carriers.blockVecNorm_blockMatVecMul_le A q)
        (SuperdiffusionCLT.Section2.Carriers.blockVecNorm_nonneg q)
    _ = SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm A *
        SuperdiffusionCLT.Section2.Carriers.blockVecNorm q ^ 2 := by ring
    _ ≤ SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm A := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hq hnorm
/-- Fixed signed quadratic observables are measurable in the lower shells. -/
theorem localizationT2Printed_quadratic_lower {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (l n : ℕ) (R : Homogenization.TriadicCube d) (q : Homogenization.BlockVec d) :
    StronglyMeasurable[SuperdiffusionCLT.Probability.shellSigma (localizationLowerShells l)]
      (fun omega => Homogenization.blockVecDot q
        (Homogenization.blockMatVecMul (localizationV nu l P n R omega) q)) := by
  have hm := (localizationT2Printed_measurable_quadratic q).comp
    (displayJ_measurable_V_lower hnu l P n R)
  simpa only [Function.comp_def, Homogenization.ofFullBlockMat_toFullBlockMat] using
    hm.stronglyMeasurable
/-- Concentration for signed quadratic forms on one colour class. The vectors
are fixed parameters, independently chosen at each cube, in the unit ball.
All independence, tail and mean-zero inputs are supplied by the shell laws. -/
theorem localizationT2Printed_class_conditional [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ1 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {n l m : ℕ} (hnl : n ≤ l) (hlm : l ≤ m)
    (c : Fin d → Fin (SuperdiffusionCLT.Section2.Annealed.descendantColorModulus d (l - n)))
    (hc : c ∈ SuperdiffusionCLT.Section2.Annealed.descendantColorSet d (l - n) m n)
    (q : Homogenization.TriadicCube d → Homogenization.BlockVec d)
    (hq : ∀ R, SuperdiffusionCLT.Section2.Carriers.blockVecNorm (q R) ^ 2 ≤ 1) :
    SuperdiffusionCLT.Probability.CondIsBigO P.toMeasure
      (SuperdiffusionCLT.Probability.shellSigma (localizationUpperShells l))
      (Homogenization.IndependentSums.gammaSigma 1)
      (fun omega => ((SuperdiffusionCLT.Section2.Annealed.descendantColorClass
        d (l - n) m n c).card : ℝ)⁻¹ *
        ∑ R ∈ SuperdiffusionCLT.Section2.Annealed.descendantColorClass d (l - n) m n c,
          Homogenization.blockVecDot (q R)
            (Homogenization.blockMatVecMul (localizationV nu l P n R omega) (q R)))
      (fun _ => Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 1 *
        (Real.sqrt ((SuperdiffusionCLT.Section2.Annealed.descendantColorClass
          d (l - n) m n c).card : ℝ) /
          ((SuperdiffusionCLT.Section2.Annealed.descendantColorClass
            d (l - n) m n c).card : ℝ)) * 2) := by
  classical
  let s := SuperdiffusionCLT.Section2.Annealed.descendantColorClass d (l - n) m n c
  let X := fun (R : {R : Homogenization.TriadicCube d // R ∈ s}) omega =>
    Homogenization.blockVecDot (q R.val)
      (Homogenization.blockMatVecMul (localizationV nu l P n R.val omega) (q R.val))
  have hind : ProbabilityTheory.iIndepFun X P.toMeasure := by
    have hh := (displayJ_colorClass_independent hnu P hJ1 hJ2 hnl hlm c).comp
      (fun R => fun A => Homogenization.blockVecDot (q R.val)
        (Homogenization.blockMatVecMul (Homogenization.ofFullBlockMat A) (q R.val)))
      (fun R => localizationT2Printed_measurable_quadratic (q R.val))
    simpa only [Function.comp_def, Homogenization.ofFullBlockMat_toFullBlockMat] using hh
  have hcompl (R : {R : Homogenization.TriadicCube d // R ∈ s}) :
      StronglyMeasurable[SuperdiffusionCLT.Probability.shellSigma (localizationLowerShells l)]
        (X R) := localizationT2Printed_quadratic_lower hnu P l n R.val (q R.val)
  have htail (R : {R : Homogenization.TriadicCube d // R ∈ s}) :
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma 1) (X R) 2 := by
    apply (isBigO_gammaSigma_localizationV_opNorm hnu P hPrefix hJ2 hJ3 hJ4 l n R.val).of_abs_le
    intro omega
    exact (localizationT2Printed_abs_quadratic_le _ (q R.val) (hq R.val)).trans
      (le_abs_self _)
  have hmean (R : {R : Homogenization.TriadicCube d // R ∈ s}) :
      ∫ omega, X R omega ∂P.toMeasure = 0 := by
    have hmem := (SuperdiffusionCLT.Section2.Annealed.mem_descendantColorClass_iff.mp
      R.property).1
    exact localizationT2Printed_integral_quadratic hnu P hPrefix hJ2 hJ3 hJ4 l n R.val
      (SuperdiffusionCLT.Section2.Annealed.scale_eq_of_mem_descendantsAtDepth_originCube
        (hnl.trans hlm) hmem) (q R.val)
  have hs : s.Nonempty :=
    SuperdiffusionCLT.Section2.Annealed.exists_mem_of_mem_descendantColorSet hc
  have hh := SuperdiffusionCLT.Probability.condIsBigO_gammaSigma_finsetAverage_of_compl
    (localizationUpperShells_disjoint_lowerShells l) hJ2.independent
    (s := s.attach) (σ := 1) (K := 2) hind
    (fun R => SuperdiffusionCLT.Probability.Measurable.of_compl_ambient
      (hcompl R).measurable) hcompl hs.attach zero_lt_one (by norm_num) (by norm_num)
    (fun R _ => htail R) (fun R _ => hmean R)
  have hsum (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
      (∑ R ∈ s.attach, X R omega) = ∑ R ∈ s,
        Homogenization.blockVecDot (q R)
          (Homogenization.blockMatVecMul (localizationV nu l P n R omega) (q R)) :=
    Finset.sum_attach s (fun R => Homogenization.blockVecDot (q R)
      (Homogenization.blockMatVecMul (localizationV nu l P n R omega) (q R)))
  simpa only [Finset.card_attach, hsum] using hh
/-- Aggregation of the signed colour classes with the square-root colour cost.
This retains cancellations inside every class and allows a different fixed
unit-ball vector at each cube. -/
theorem localizationT2Printed_colored_average [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ1 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {n l m : ℕ} (hnl : n ≤ l) (hlm : l ≤ m)
    (q : Homogenization.TriadicCube d → Homogenization.BlockVec d)
    (hq : ∀ R, SuperdiffusionCLT.Section2.Carriers.blockVecNorm (q R) ^ 2 ≤ 1) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1)
      (fun omega => ((localizationAverageGrid d m n).card : ℝ)⁻¹ *
        ∑ R ∈ localizationAverageGrid d m n, Homogenization.blockVecDot (q R)
          (Homogenization.blockMatVecMul (localizationV nu l P n R omega) (q R)))
      (Homogenization.IndependentSums.gammaTriangleConst 1 *
        Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 1 *
        (Real.sqrt ((SuperdiffusionCLT.Section2.Annealed.descendantColorSet
          d (l - n) m n).card : ℝ) *
          (Real.sqrt ((localizationAverageGrid d m n).card : ℝ) /
            ((localizationAverageGrid d m n).card : ℝ))) * 2) := by
  classical
  let colors := SuperdiffusionCLT.Section2.Annealed.descendantColorSet d (l - n) m n
  let cls := SuperdiffusionCLT.Section2.Annealed.descendantColorClass d (l - n) m n
  let X := fun R omega => Homogenization.blockVecDot (q R)
    (Homogenization.blockMatVecMul (localizationV nu l P n R omega) (q R))
  have hmeas (R : Homogenization.TriadicCube d) : Measurable (X R) :=
    SuperdiffusionCLT.Probability.Measurable.of_compl_ambient
      (localizationT2Printed_quadratic_lower hnu P l n R (q R)).measurable
  have hclass c (hc : c ∈ colors) :
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma 1)
        (fun omega => ((cls c).card : ℝ)⁻¹ * ∑ R ∈ cls c, X R omega)
        (Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 1 *
          (Real.sqrt ((cls c).card : ℝ) / ((cls c).card : ℝ)) * 2) :=
    SuperdiffusionCLT.Probability.isBigO_of_condIsBigO
      (SuperdiffusionCLT.Probability.shellSigma_le_ambient (localizationUpperShells l))
      ((Finset.measurable_sum (cls c) (fun R _ => hmeas R)).const_mul _)
      (localizationT2Printed_class_conditional hnu P hPrefix hJ1 hJ2 hJ3 hJ4 hnl hlm c hc q hq)
  have hsum c (hc : c ∈ colors) :
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma 1)
        (fun omega => ∑ R ∈ cls c, X R omega)
        (Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 1 *
          Real.sqrt ((cls c).card : ℝ) * 2) := by
    have hpos : (0 : ℝ) < ((cls c).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr
        (SuperdiffusionCLT.Section2.Annealed.exists_mem_of_mem_descendantColorSet hc)
    have hh := (hclass c hc).const_mul hpos.le
    have he : ((cls c).card : ℝ) *
        (Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 1 *
          (Real.sqrt ((cls c).card : ℝ) / ((cls c).card : ℝ)) * 2) =
        Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 1 *
          Real.sqrt ((cls c).card : ℝ) * 2 := by field_simp
    simpa only [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, he] using hh
  have htotal : (0 : ℝ) < ((localizationAverageGrid d m n).card : ℝ) := by
    change (0 : ℝ) < ((Homogenization.descendantsAtDepth
      (Homogenization.originCube d (m : ℤ)) (m - n)).card : ℝ)
    rw [card_descendantsAtDepth_originCube]
    positivity
  have hh := Homogenization.Book.Ch04.isBigO_finsetAverage_colorClassSums_gammaSigma
    (μ := P.toMeasure) colors (Y := fun c omega => ∑ R ∈ cls c, X R omega)
    (classCount := fun c => ((cls c).card : ℝ)) (colorCount := (colors.card : ℝ))
    (totalCount := ((localizationAverageGrid d m n).card : ℝ))
    (C := Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 1) (K := 2)
    (σ := 1) zero_lt_one
    (SuperdiffusionCLT.Section2.Annealed.descendantColorSet_nonempty d (l - n) m n)
    (fun c hc => by
      have hp : 0 < (cls c).card := Finset.card_pos.mpr
        (SuperdiffusionCLT.Section2.Annealed.exists_mem_of_mem_descendantColorSet hc)
      exact Nat.cast_pos.mpr hp)
    htotal gammaSigmaIndependentSumConst_one_pos (by norm_num) hsum
    (fun c _ => Finset.measurable_sum (cls c) (fun R _ => hmeas R))
    (displayJ_color_sqrt_bound d l m n)
  have hsplit omega : (∑ c ∈ colors, ∑ R ∈ cls c, X R omega) =
      ∑ R ∈ localizationAverageGrid d m n, X R omega := by
    rw [← Finset.sum_biUnion
      (SuperdiffusionCLT.Section2.Annealed.pairwiseDisjoint_descendantColorClass
        d (l - n) m n)]
    rw [SuperdiffusionCLT.Section2.Annealed.biUnion_descendantColorClass]
  simpa only [hsplit] using hh
/-- Squared block length is the sum of the full-coordinate squares. -/
theorem localizationT2Printed_norm_sq (g : Homogenization.BlockVec d) :
    SuperdiffusionCLT.Section2.Carriers.blockVecNorm g ^ 2 =
      ∑ a : Homogenization.BlockCoord d, Homogenization.toFullBlockVec g a ^ 2 := by
  rw [SuperdiffusionCLT.Section2.Carriers.blockVecNorm_sq, Fintype.sum_sum_type]
  simp only [Homogenization.blockVecDot, Homogenization.vecDot,
    Homogenization.toFullBlockVec, pow_two]
/-- Integrate a uniform fibre bound against an independent random parameter.
The bound is required only at parameters actually attained by H. -/
theorem localizationT2Printed_measure_mixed_le {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {H : Ω → α} {Y : Ω → β}
    (hH : Measurable H) (hY : Measurable Y) (hind : ProbabilityTheory.IndepFun H Y μ)
    {s : Set (α × β)} (hs : MeasurableSet s) {b : ℝ≥0∞}
    (hb : ∀ omega, μ {w | (H omega, Y w) ∈ s} ≤ b) :
    μ {omega | (H omega, Y omega) ∈ s} ≤ b := by
  have : IsProbabilityMeasure (μ.map Y) := inferInstance
  have hmap := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    hH.aemeasurable hY.aemeasurable).mp hind
  calc
    μ {omega | (H omega, Y omega) ∈ s} = (μ.map (fun omega => (H omega, Y omega))) s :=
      (MeasureTheory.Measure.map_apply (hH.prodMk hY) hs).symm
    _ = (μ.map H).prod (μ.map Y) s := by rw [hmap]
    _ = ∫⁻ a, (μ.map Y) (Prod.mk a ⁻¹' s) ∂(μ.map H) := MeasureTheory.Measure.prod_apply hs
    _ = ∫⁻ omega, (μ.map Y) (Prod.mk (H omega) ⁻¹' s) ∂μ :=
      MeasureTheory.lintegral_map (_root_.measurable_measure_prodMk_left hs) hH
    _ ≤ ∫⁻ _omega, b ∂μ := by
      apply MeasureTheory.lintegral_mono
      intro omega
      change (μ.map Y) (Prod.mk (H omega) ⁻¹' s) ≤ b
      rw [MeasureTheory.Measure.map_apply hY (hs.preimage (measurable_prodMk_left (x := H omega)))]
      exact hb omega
    _ = b := by simp only [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]
/-- A uniform signed Gamma bound at fixed independent parameters remains valid
when those parameters are sampled. This step does not require the resulting
observable to be measurable in the lower shells alone. -/
theorem localizationT2Printed_isBigO_mixed {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {H : Ω → α} {Y : Ω → β}
    (hH : Measurable H) (hY : Measurable Y) (hind : ProbabilityTheory.IndepFun H Y μ)
    (f : α × β → ℝ) (hf : Measurable f) {σ A : ℝ}
    (hbound : ∀ omega, Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma σ) (fun w => f (H omega, Y w)) A) :
    Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma σ)
      (fun omega => f (H omega, Y omega)) A := by
  intro t ht
  have hs : MeasurableSet {p | A * t < |f p|} := measurableSet_lt measurable_const (continuous_abs.measurable.comp hf)
  have hb : ∀ omega, μ {w | A * t < |f (H omega, Y w)|} ≤
      ENNReal.ofReal ((Homogenization.IndependentSums.gammaSigma σ t)⁻¹) := by
    intro omega
    apply (ENNReal.le_ofReal_iff_toReal_le (MeasureTheory.measure_ne_top _ _) ?_).mpr
    · exact hbound omega ht
    · rw [Homogenization.IndependentSums.gammaSigma_inv]
      exact (Real.exp_pos _).le
  have hh := localizationT2Printed_measure_mixed_le hH hY hind hs hb
  have hr : 0 ≤ (Homogenization.IndependentSums.gammaSigma σ t)⁻¹ := by
    rw [Homogenization.IndependentSums.gammaSigma_inv]
    exact (Real.exp_pos _).le
  exact (ENNReal.le_ofReal_iff_toReal_le (MeasureTheory.measure_ne_top _ _) hr).mp hh
/-- Joint measurability of the signed quadratic form in its vector and matrix. -/
theorem localizationT2Printed_measurable_joint_quadratic :
    Measurable (fun p : Homogenization.BlockVec d × Homogenization.FullBlockMat d =>
      Homogenization.blockVecDot p.1
        (Homogenization.blockMatVecMul (Homogenization.ofFullBlockMat p.2) p.1)) := by
  have heq : (fun p : Homogenization.BlockVec d × Homogenization.FullBlockMat d =>
      Homogenization.blockVecDot p.1
        (Homogenization.blockMatVecMul (Homogenization.ofFullBlockMat p.2) p.1)) =
      fun p => ∑ a, ∑ b,
        (Homogenization.toFullBlockVec p.1 a * Homogenization.toFullBlockVec p.1 b) * p.2 a b := by
    funext p
    rw [Homogenization.blockVecDot_blockMatVecMul_eq_toLinearMap₂',
      Homogenization.toFullBlockMat_ofFullBlockMat, Matrix.toLinearMap₂'_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [smul_eq_mul]
    ring
  have hv (a : Homogenization.BlockCoord d) :
      Measurable (fun p : Homogenization.BlockVec d × Homogenization.FullBlockMat d =>
        Homogenization.toFullBlockVec p.1 a) := by
    cases a with
    | inl i => exact (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)
    | inr i => exact (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  rw [heq]
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
  exact ((hv a).mul (hv b)).mul
    ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp measurable_snd))
/-- Signed colour-class concentration with random upper-shell unit-ball vectors.
The vectors need not be independent of one another. Their independence from
the entire lower-shell matrix family is derived from J2. -/
theorem localizationT2Printed_random_colored_average [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ1 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {n l m : ℕ} (hnl : n ≤ l) (hlm : l ≤ m)
    (q : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
      Homogenization.TriadicCube d → Homogenization.BlockVec d)
    (hqm : Measurable[SuperdiffusionCLT.Probability.shellSigma (localizationUpperShells l)] q)
    (hq : ∀ omega R, SuperdiffusionCLT.Section2.Carriers.blockVecNorm (q omega R) ^ 2 ≤ 1) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1)
      (fun omega => ((localizationAverageGrid d m n).card : ℝ)⁻¹ *
        ∑ R ∈ localizationAverageGrid d m n, Homogenization.blockVecDot (q omega R)
          (Homogenization.blockMatVecMul (localizationV nu l P n R omega) (q omega R)))
      (Homogenization.IndependentSums.gammaTriangleConst 1 *
        Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 1 *
        (Real.sqrt ((SuperdiffusionCLT.Section2.Annealed.descendantColorSet
          d (l - n) m n).card : ℝ) *
          (Real.sqrt ((localizationAverageGrid d m n).card : ℝ) /
            ((localizationAverageGrid d m n).card : ℝ))) * 2) := by
  let Y := fun omega R => Homogenization.toFullBlockMat (localizationV nu l P n R omega)
  have hY : Measurable[SuperdiffusionCLT.Probability.shellSigma (localizationLowerShells l)] Y :=
    by
      let : MeasurableSpace (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :=
        SuperdiffusionCLT.Probability.shellSigma (localizationLowerShells l)
      exact Measurable.of_eval fun R => displayJ_measurable_V_lower hnu l P n R
  have hind := SuperdiffusionCLT.Probability.indep_shellSigma_of_shellLawJ2
    (localizationUpperShells_disjoint_lowerShells l) hJ2
  have hf := ProbabilityTheory.indep_of_indep_of_le_right
    (ProbabilityTheory.indep_of_indep_of_le_left hind hqm.comap_le) hY.comap_le
  have hfun : ProbabilityTheory.IndepFun q Y P.toMeasure :=
    (ProbabilityTheory.IndepFun_iff_Indep _ _ _).mpr hf
  let f := fun p : (Homogenization.TriadicCube d → Homogenization.BlockVec d) ×
      (Homogenization.TriadicCube d → Homogenization.FullBlockMat d) =>
    ((localizationAverageGrid d m n).card : ℝ)⁻¹ *
      ∑ R ∈ localizationAverageGrid d m n, Homogenization.blockVecDot (p.1 R)
        (Homogenization.blockMatVecMul (Homogenization.ofFullBlockMat (p.2 R)) (p.1 R))
  have hfm : Measurable f := by
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro R _
    have hp : Measurable (fun p :
        (Homogenization.TriadicCube d → Homogenization.BlockVec d) ×
        (Homogenization.TriadicCube d → Homogenization.FullBlockMat d) => (p.1 R, p.2 R)) :=
      ((measurable_pi_apply R).comp measurable_fst).prodMk
        ((measurable_pi_apply R).comp measurable_snd)
    exact localizationT2Printed_measurable_joint_quadratic.comp hp
  have hh := localizationT2Printed_isBigO_mixed
    (hqm.mono (SuperdiffusionCLT.Probability.shellSigma_le_ambient _) le_rfl)
    (hY.mono (SuperdiffusionCLT.Probability.shellSigma_le_ambient _) le_rfl)
    hfun f hfm (fun omega => by
      simpa only [f, Y, Homogenization.ofFullBlockMat_toFullBlockMat] using
        localizationT2Printed_colored_average hnu P hPrefix hJ1 hJ2 hJ3 hJ4
          hnl hlm (q omega) (hq omega))
  simpa only [f, Y, Homogenization.ofFullBlockMat_toFullBlockMat] using hh
/-- Normalize an envelope-weighted vector by the square root of its common
upper bound. The zero-bound case is included. -/
theorem localizationT2Printed_normalize_vector (g : Homogenization.BlockVec d) {W : ℝ}
    (hW : 0 ≤ W) (hg : SuperdiffusionCLT.Section2.Carriers.blockVecNorm g ^ 2 ≤ W) :
    SuperdiffusionCLT.Section2.Carriers.blockVecNorm ((Real.sqrt W)⁻¹ • g) ^ 2 ≤ 1 := by
  rw [SuperdiffusionCLT.Section2.Carriers.blockVecNorm_sq,
    Homogenization.blockVecDot_smul_left, Homogenization.blockVecDot_smul_right,
    ← SuperdiffusionCLT.Section2.Carriers.blockVecNorm_sq, ← mul_assoc,
    ← pow_two, inv_pow, Real.sq_sqrt hW]
  by_cases hzero : W = 0
  · simp only [hzero, inv_zero, zero_mul]
    exact zero_le_one
  · have hp : 0 < W := lt_of_le_of_ne hW (Ne.symm hzero)
    calc W⁻¹ * SuperdiffusionCLT.Section2.Carriers.blockVecNorm g ^ 2
        ≤ W⁻¹ * W := mul_le_mul_of_nonneg_left hg (inv_nonneg.mpr hW)
      _ = 1 := inv_mul_cancel₀ hp.ne'
/-- Recover the signed quadratic form after normalization, including W = 0. -/
theorem localizationT2Printed_normalize_quadratic (g : Homogenization.BlockVec d)
    (A : Homogenization.BlockMat d) {W : ℝ} (hW : 0 ≤ W)
    (hg : SuperdiffusionCLT.Section2.Carriers.blockVecNorm g ^ 2 ≤ W) :
    W * Homogenization.blockVecDot ((Real.sqrt W)⁻¹ • g)
        (Homogenization.blockMatVecMul A ((Real.sqrt W)⁻¹ • g)) =
      Homogenization.blockVecDot g (Homogenization.blockMatVecMul A g) := by
  rw [Homogenization.blockMatVecMul_smul, Homogenization.blockVecDot_smul_left,
    Homogenization.blockVecDot_smul_right, ← mul_assoc, ← mul_assoc]
  rw [show W * (Real.sqrt W)⁻¹ * (Real.sqrt W)⁻¹ = W * W⁻¹ by
    rw [mul_assoc, ← pow_two, inv_pow, Real.sq_sqrt hW]]
  by_cases hz : W = 0
  · have hn : SuperdiffusionCLT.Section2.Carriers.blockVecNorm g = 0 :=
      (sq_eq_zero_iff).mp (le_antisymm (hg.trans_eq hz) (sq_nonneg _))
    have hbound := abs_blockVecDot_le_blockVecNorm_mul g (Homogenization.blockMatVecMul A g)
    rw [hn, zero_mul] at hbound
    have hq : Homogenization.blockVecDot g (Homogenization.blockMatVecMul A g) = 0 :=
      abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))
    rw [hz, zero_mul, zero_mul, hq]
  · rw [mul_inv_cancel₀ hz, one_mul]
/-- The squared block length is measurable on the original block-vector carrier. -/
theorem localizationT2Printed_measurable_length :
    Measurable (fun g : Homogenization.BlockVec d =>
      SuperdiffusionCLT.Section2.Carriers.blockVecNorm g ^ 2) := by
  simp only [localizationT2Printed_norm_sq]
  apply Finset.measurable_sum
  intro a _
  cases a with
  | inl i => exact ((measurable_pi_apply i).comp measurable_fst).pow_const 2
  | inr i => exact ((measurable_pi_apply i).comp measurable_snd).pow_const 2
/-- The actual T2 admits the printed maximum-weight factorization, with the
normalized signed factor concentrated across the colour classes. -/
theorem localizationT2Printed_factor [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ1 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {n l m : ℕ} (hnl : n ≤ l) (hlm : l ≤ m) (L : ℕ) (v : Homogenization.BlockVec d) :
    ∃ U : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma 1) U
        (Homogenization.IndependentSums.gammaTriangleConst 1 *
          Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 1 *
          (Real.sqrt ((SuperdiffusionCLT.Section2.Annealed.descendantColorSet
            d (l - n) m n).card : ℝ) *
            (Real.sqrt ((localizationAverageGrid d m n).card : ℝ) /
              ((localizationAverageGrid d m n).card : ℝ))) * 2) ∧
      ∀ omega, localizationT2 nu l L P m n v omega =
        (localizationAverageGrid d m n).sup' (localizationAverageGrid_nonempty m n)
          (fun R => localizationW nu l L R v omega) * U omega := by
  classical
  let s := localizationAverageGrid d m n
  have hs : s.Nonempty := localizationAverageGrid_nonempty m n
  let g := fun omega R => Homogenization.blockMatVecMul (envelopeSqrt d nu l)
    (localizationGaugeVector l L R v omega)
  let W := fun omega => s.sup' hs (fun R => localizationW nu l L R v omega)
  have hgm R : Measurable[SuperdiffusionCLT.Probability.shellSigma (localizationUpperShells l)]
      (fun omega => g omega R) := by
    have hgauge : Measurable[SuperdiffusionCLT.Probability.shellSigma (localizationUpperShells l)]
        (localizationGaugeVector l L R v) := by
      let : MeasurableSpace (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :=
        SuperdiffusionCLT.Probability.shellSigma (localizationUpperShells l)
      exact (Measurable.of_eval fun i =>
        (displayL_stronglyMeasurable_gauge_entry l L R v (Sum.inl i)).measurable).prodMk
        (Measurable.of_eval fun i =>
          (displayL_stronglyMeasurable_gauge_entry l L R v (Sum.inr i)).measurable)
    exact (Homogenization.blockMatContinuousLinearMap (envelopeSqrt d nu l)).continuous.measurable.comp hgauge
  have hwm : Measurable[SuperdiffusionCLT.Probability.shellSigma (localizationUpperShells l)] W := by
    let : MeasurableSpace (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :=
      SuperdiffusionCLT.Probability.shellSigma (localizationUpperShells l)
    have he : W = s.sup' hs (fun R omega =>
        SuperdiffusionCLT.Section2.Carriers.blockVecNorm (g omega R) ^ 2) := by
      funext omega
      rw [Finset.sup'_apply]
      rfl
    rw [he]
    exact Finset.measurable_sup' hs
      (fun R _ => localizationT2Printed_measurable_length.comp (hgm R))
  have hle omega R (hR : R ∈ s) :
      SuperdiffusionCLT.Section2.Carriers.blockVecNorm (g omega R) ^ 2 ≤ W omega :=
    Finset.le_sup' (fun R => localizationW nu l L R v omega) hR
  have hW omega : 0 ≤ W omega := by
    obtain ⟨R, hR⟩ := hs
    exact (sq_nonneg _).trans (hle omega R hR)
  let q := fun omega R =>
    (Real.sqrt (max (W omega) (SuperdiffusionCLT.Section2.Carriers.blockVecNorm (g omega R) ^ 2)))⁻¹ • g omega R
  have hqm : Measurable[SuperdiffusionCLT.Probability.shellSigma (localizationUpperShells l)] q := by
    let : MeasurableSpace (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :=
      SuperdiffusionCLT.Probability.shellSigma (localizationUpperShells l)
    apply Measurable.of_eval
    intro R
    exact (Real.continuous_sqrt.measurable.comp
      (hwm.max (localizationT2Printed_measurable_length.comp (hgm R)))).inv.smul (hgm R)
  have hq omega R : SuperdiffusionCLT.Section2.Carriers.blockVecNorm (q omega R) ^ 2 ≤ 1 :=
    localizationT2Printed_normalize_vector (g omega R)
      ((hW omega).trans (le_max_left _ _)) (le_max_right _ _)
  refine ⟨fun omega => (s.card : ℝ)⁻¹ * ∑ R ∈ s, Homogenization.blockVecDot (q omega R)
    (Homogenization.blockMatVecMul (localizationV nu l P n R omega) (q omega R)),
    localizationT2Printed_random_colored_average hnu P hPrefix hJ1 hJ2 hJ3 hJ4
      hnl hlm q hqm hq, ?_⟩
  intro omega
  change (s.card : ℝ)⁻¹ * ∑ R ∈ s, localizationZ nu l L P n R v omega =
    W omega * ((s.card : ℝ)⁻¹ * ∑ R ∈ s, _)
  rw [mul_left_comm (W omega)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R hR
  have he := localizationT2Printed_normalize_quadratic (g omega R)
    (localizationV nu l P n R omega) (hW omega) (hle omega R hR)
  have hqeq : q omega R = (Real.sqrt (W omega))⁻¹ • g omega R := by
    dsimp [q]
    rw [max_eq_left (hle omega R hR)]
  rw [hqeq, he]
  exact blockVecDot_envelopeRescale_sandwich hnu l
    (localizationPerturbationMatrix nu l P n R omega) (localizationGaugeVector l L R v omega)
/-- The colour-count cost has the printed decay, with a dimension-only factor. -/
theorem localizationT2Printed_color_decay {n l m : ℕ} (hnl : n ≤ l) (hlm : l ≤ m) :
    Real.sqrt ((SuperdiffusionCLT.Section2.Annealed.descendantColorSet
      d (l - n) m n).card : ℝ) *
      (Real.sqrt ((localizationAverageGrid d m n).card : ℝ) /
        ((localizationAverageGrid d m n).card : ℝ)) ≤
      Real.sqrt (((d : ℝ) + 1) ^ d) * localizationAverageNormalisedAmplitude d m l := by
  have hpow : 1 ≤ (3 : ℕ) ^ (l - n) := Nat.one_le_pow _ _ (by norm_num)
  have hmod : 3 ^ (l - n) * d + 1 ≤ 3 ^ (l - n) * (d + 1) := by
    nlinarith only [hpow]
  have hcount := (SuperdiffusionCLT.Section2.Annealed.card_descendantColorSet_le
    d (l - n) m n).trans (Nat.pow_le_pow_left hmod d)
  have hc : ((SuperdiffusionCLT.Section2.Annealed.descendantColorSet
      d (l - n) m n).card : ℝ) ≤
      (((3 : ℝ) ^ (l - n)) * ((d : ℝ) + 1)) ^ d := by exact_mod_cast hcount
  have hp : (((3 : ℝ) ^ (l - n)) * ((d : ℝ) + 1)) ^ d =
      ((d : ℝ) + 1) ^ d * (3 : ℝ) ^ ((d : ℝ) * ((l - n : ℕ) : ℝ)) := by
    rw [mul_pow, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    simp only [Real.rpow_natCast]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm (l - n) d, mul_comm]
  rw [hp] at hc
  have hN : ((localizationAverageGrid d m n).card : ℝ) =
      (3 : ℝ) ^ ((d : ℝ) * ((m - n : ℕ) : ℝ)) := by
    rw [localizationAverageGrid_card, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    simp only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  have hgap : ((m - n : ℕ) : ℝ) = ((m - l : ℕ) : ℝ) + ((l - n : ℕ) : ℝ) := by
    have hh : m - n = (m - l) + (l - n) := by omega
    exact_mod_cast hh
  calc
    _ ≤ Real.sqrt (((d : ℝ) + 1) ^ d *
        (3 : ℝ) ^ ((d : ℝ) * ((l - n : ℕ) : ℝ))) *
        (Real.sqrt ((localizationAverageGrid d m n).card : ℝ) /
          ((localizationAverageGrid d m n).card : ℝ)) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hc)
        (div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
    _ = Real.sqrt (((d : ℝ) + 1) ^ d) * localizationAverageNormalisedAmplitude d m l := by
      rw [Real.sqrt_mul (by positivity), hN, mul_assoc]
      congr 1
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        ← Real.rpow_sub (by norm_num : (0 : ℝ) < 3),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      unfold localizationAverageNormalisedAmplitude
      congr 1
      rw [hgap]
      ring
/-- Dimension-only constant for the maximum weight. -/
noncomputable def localizationT2PrintedWeightConst (d : ℕ) : ℝ :=
  3 * (d : ℝ) * Real.log 3 *
    ((1 + 2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) *
      (2 * (1 + localizationDisplayI_gaugeConst d ^ 2)))
/-- Dimension-only constant for the normalized signed average. -/
noncomputable def localizationT2PrintedSumConst (d : ℕ) : ℝ :=
  Homogenization.IndependentSums.gammaTriangleConst 1 *
    Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 1 *
    Real.sqrt (((d : ℝ) + 1) ^ d) * 2

end SuperdiffusionCLT.Section2.Localization
