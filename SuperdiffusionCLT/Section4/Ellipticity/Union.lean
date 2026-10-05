/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Ellipticity.EllipticityBelowCutoffMain
public import SuperdiffusionCLT.Section2.Annealed.EnvelopeEllipticity
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers

/-!
# The union bound of `p.ellipticity.Ptwoprime`

The key ingredient of `ellipBelow_main` (`EllipticityBelowCutoffMain.lean`):
a single witness `X`, with `Γ₁` tail `O(1/γ)`, that dominates
`3^{-γ(m-k)} · envelopeRatioOn L (openCubeSet Q) omega` simultaneously over
every scale `k ≤ m` and every sub-cube `Q` of `cu_m` at that scale.

## Route

At depth `j = m - k ≥ 0` there are at most `3^{(d+1)(j+1)}` triadic cubes `Q`
whose centre can lie in `cu_m`; each has the `Γ₁(1)` tail
`isBigOWith_gammaSigma_envelopeRatioOn`. `X` is the countable supremum

`X(omega) := ⨆ j, 3^{-γj} · (max over that depth's cubes of the ratio)`,

well-defined for *every* `omega` (not merely almost surely) because every
`envelopeRatioOn L (openCubeSet Q) omega` for a relevant `Q` is dominated by a
single, omega-dependent but Q-independent constant: `openCubeSet Q ⊆ cu_{m+1}`
for every such `Q` (`ellipBelow_openCubeSet_subset_of_mem`), and the stream cutoff is
continuous, hence bounded on the compact closure of the fixed bounded set
`cu_{m+1}` (`ellipBelow_streamCutoff_bounded_on`, the same continuity-and-
compactness technique as `shellReg_entry_bounded`).

The `Γ₁(C/γ)` tail of `X` is the union bound: for `t ≥ 1`,

`P[X > t] ≤ Σ_j (card of depth j) · P[ratio > t·3^{γj}]`
`        ≤ Σ_j 3^{(d+1)(j+1)} · exp(-t·3^{γj})`
`        ≤ exp(-t) · 3^{d+1} · Σ_j 3^{(d+1)j - tγj}`,

using `3^{γj} ≥ 1 + γj log 3`, and the last sum is geometric with ratio
`≤ 1/3` once `tγ ≥ d + 2`, giving `P[X > t] ≤ K(d) exp(-t)` there; absorbing
`K(d)` into the amplitude gives the printed `O_{Γ1}(C(d)/γ)`.

## Main result

* `ellipBelow_union`: the exact `hUnion` hypothesis of `ellipBelow_main`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Ellipticity

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2

noncomputable section

variable {d : ℕ}

/-! ## Geometric containment -/

/-! ## The deterministic, omega-wise uniform field bound -/

/-- The stream cutoff's operator norm is bounded, for *every* fixed `omega`,
uniformly over any bounded set -- the same continuity-and-compactness
technique as `shellReg_entry_bounded` (`Section2/Cutoff/CenteredCoeffOn.lean`),
applied directly to the operator norm instead of to the matrix entries. -/
theorem ellipBelow_streamCutoff_bounded_on {U : Set (Vec d)} (hUb : Bornology.IsBounded U)
    (omega : ShellSeq d) (L : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ U, matrixOperatorNorm (streamCutoff omega L x) ≤ M := by
  obtain ⟨M, hM⟩ := hUb.isCompact_closure.exists_bound_of_continuousOn
    (ShellField.continuous_matrixOperatorNorm.comp
      (continuous_streamCutoff_apply omega L)).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hM x (subset_closure hx)
  simp only [Function.comp_apply, Real.norm_eq_abs,
    abs_of_nonneg (matrixOperatorNorm_nonneg ((streamCutoff omega L).toFun x))] at h
  exact h.trans (le_max_left _ _)

/-- **The uniform deterministic bound on `envelopeRatioOn`.** For every fixed
`omega, m, L`, there is a single real `Mbar omega` dominating
`envelopeRatioOn L (openCubeSet Q) omega` for *every* sub-cube `Q` of `cu_m`
at *every* scale `k ≤ m`: the field is continuous, hence bounded on the fixed
compact closure of `cu_{m+1}` (which contains every such sub-cube by
`ellipBelow_openCubeSet_subset_of_mem`), so the volume average defining the ratio is
bounded independently of `Q`. -/
private theorem ellipBelow_envelopeRatioOn_le_of_subset {m : ℤ} {L : ℕ} {omega : ShellSeq d}
    {M : ℝ} (hM : ∀ x ∈ cubeSet (originCube d (m + 1)),
      matrixOperatorNorm (streamCutoff omega L x) ≤ M)
    {Q : TriadicCube d} (hsub : openCubeSet Q ⊆ cubeSet (originCube d (m + 1))) :
    envelopeRatioOn L (openCubeSet Q) omega ≤
      max 1 (M ^ 2 / (cutoffEnvelopeConst d * max 1 (L : ℝ))) := by
  have hbound : ∀ x ∈ openCubeSet Q,
      matrixOperatorNorm (streamCutoff omega L x) ^ 2 ≤ M ^ 2 := by
    intro x hx
    exact pow_le_pow_left₀ (matrixOperatorNorm_nonneg _) (hM x (hsub hx)) 2
  have hfin : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply_univ]
    exact volume_openCubeSet_lt_top Q
  have hvol : volumeAverage (openCubeSet Q)
      (fun x => matrixOperatorNorm (streamCutoff omega L x) ^ 2) ≤ M ^ 2 :=
    volumeAverage_le_of_le_on (isOpen_openCubeSet Q).measurableSet
      (integrableOn_matrixOperatorNorm_sq_streamCutoff omega L Q)
      (ENNReal.toReal_ne_zero.2 ⟨volume_openCubeSet_ne_zero Q, (volume_openCubeSet_lt_top Q).ne⟩)
      hbound
  unfold envelopeRatioOn
  exact max_le_max le_rfl (div_le_div_of_nonneg_right hvol (cutoffEnvelopeScale_pos d L).le)

/-! ## The sub-cubes of `cu_m` at one depth -/

/-- The triadic cubes of scale `m - j` whose centre can lie in `cu_m`
(depth `j` below `cu_m`), the same combinatorial index set as the
(private) `subCubeFinset` of `Section2/Annealed/EnvelopeMinimalScale.lean`. -/
def ellipBelowSubCubeFinset (d : ℕ) (m : ℤ) (j : ℕ) : Finset (TriadicCube d) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(3 ^ j : ℤ)) (3 ^ j)).image
    fun idx => ⟨m - (j : ℤ), idx⟩

private theorem ellipBelow_card_subCubeFinset_le (d : ℕ) (m : ℤ) (j : ℕ) :
    (ellipBelowSubCubeFinset d m j).card ≤ 3 ^ ((d + 1) * (j + 1)) := by
  have hIcc : ∀ _i : Fin d, (Finset.Icc (-(3 ^ j : ℤ)) (3 ^ j)).card = 2 * 3 ^ j + 1 := by
    intro _i
    rw [Int.card_Icc]
    have hcast : ((3 : ℤ) ^ j + 1 - -(3 ^ j)) = ((2 * 3 ^ j + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hcast, Int.toNat_natCast]
  have hcard : (Fintype.piFinset fun _ : Fin d =>
      Finset.Icc (-(3 ^ j : ℤ)) (3 ^ j)).card = (2 * 3 ^ j + 1) ^ d := by
    rw [Fintype.card_piFinset, Finset.prod_congr rfl fun i _ => hIcc i, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  refine le_trans Finset.card_image_le ?_
  rw [hcard]
  have hbase : 2 * 3 ^ j + 1 ≤ 3 ^ (j + 1) := by
    have h1 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 3 ^ (j + 1) = 3 * 3 ^ j := by ring
    omega
  calc (2 * 3 ^ j + 1) ^ d ≤ (3 ^ (j + 1)) ^ d := Nat.pow_le_pow_left hbase d
    _ = 3 ^ ((j + 1) * d) := by rw [← pow_mul]
    _ ≤ 3 ^ ((d + 1) * (j + 1)) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have : (j + 1) * d = d * (j + 1) := Nat.mul_comm _ _
        rw [this]
        exact Nat.mul_le_mul_right _ (Nat.le_succ d)

private theorem ellipBelow_mem_subCubeFinset {m : ℤ} {j : ℕ} {Q : TriadicCube d}
    (hscale : Q.scale = m - (j : ℤ))
    (hmem : cubeCenter Q ∈ cubeSet (originCube d m)) :
    Q ∈ ellipBelowSubCubeFinset d m j := by
  have hA : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hB : (0 : ℝ) < (3 : ℝ) ^ (j : ℤ) := by positivity
  have hidx : ∀ i, Q.index i ∈ Finset.Icc (-(3 ^ j : ℤ)) (3 ^ j) := by
    intro i
    have h := (mem_cubeSet_originCube_iff.1 hmem) i
    have hcc : cubeCenter Q i =
        (Q.index i : ℝ) / (3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ m := by
      show (Q.index i : ℝ) * cubeScaleFactor Q = _
      rw [cubeScaleFactor, hscale, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring
    rw [hcc] at h
    have hlow : -(1 / 2 : ℝ) ≤ (Q.index i : ℝ) / (3 : ℝ) ^ (j : ℤ) := by
      have := h.1
      exact le_of_mul_le_mul_right (by linarith only [this]) hA
    have hhigh : (Q.index i : ℝ) / (3 : ℝ) ^ (j : ℤ) < 1 / 2 := by
      have := h.2
      exact lt_of_mul_lt_mul_right (by linarith only [this]) hA.le
    have hlow' : -(1 / 2 : ℝ) * (3 : ℝ) ^ (j : ℤ) ≤ (Q.index i : ℝ) :=
      (le_div_iff₀ hB).1 hlow
    have hhigh' : (Q.index i : ℝ) < 1 / 2 * (3 : ℝ) ^ (j : ℤ) :=
      (div_lt_iff₀ hB).1 hhigh
    have hcast : ((3 : ℝ) ^ (j : ℤ)) = (((3 ^ j : ℤ) : ℝ)) := by
      push_cast
      rw [zpow_natCast]
    rw [Finset.mem_Icc]
    constructor
    · have : (-((3 ^ j : ℤ) : ℝ)) ≤ (Q.index i : ℝ) := by
        rw [← hcast]
        linarith only [hlow', hB]
      exact_mod_cast this
    · have : (Q.index i : ℝ) ≤ (((3 ^ j : ℤ) : ℝ)) := by
        rw [← hcast]
        linarith only [hhigh', hB]
      exact_mod_cast this
  have hQ : (⟨m - (j : ℤ), Q.index⟩ : TriadicCube d) = Q := by
    rw [← hscale]
  exact Finset.mem_image.2 ⟨Q.index, Fintype.mem_piFinset.2 hidx, hQ⟩

/-- Every element of `ellipBelowSubCubeFinset d m j`, for any `j`, has its open
cube inside `cu_{m+1}`: unlike a centre-based containment fact, this needs only
Finset membership (the index box is a generous, not exact, cover of the depth-
`j` sub-cubes of `cu_m`), so it applies uniformly to the whole combinatorial
index set at every depth. -/
private theorem ellipBelow_openCubeSet_subset_of_mem {m : ℤ} {j : ℕ} {Q : TriadicCube d}
    (hQ : Q ∈ ellipBelowSubCubeFinset d m j) :
    openCubeSet Q ⊆ cubeSet (originCube d (m + 1)) := by
  obtain ⟨idx, hidx, hQeq⟩ := Finset.mem_image.1 hQ
  subst hQeq
  intro x hx
  have hxi := hx
  rw [mem_cubeSet_originCube_iff]
  intro i
  have hxii := hxi i
  have hidxi : idx i ∈ Finset.Icc (-(3 ^ j : ℤ)) (3 ^ j) := Fintype.mem_piFinset.1 hidx i
  rw [Finset.mem_Icc] at hidxi
  have hlowR : -(3 : ℝ) ^ j ≤ (idx i : ℝ) := by exact_mod_cast hidxi.1
  have hhighR : (idx i : ℝ) ≤ (3 : ℝ) ^ j := by exact_mod_cast hidxi.2
  set S : ℝ := cubeScaleFactor (⟨m - (j : ℤ), idx⟩ : TriadicCube d) with hSdef
  have hSeq : S = (3 : ℝ) ^ (m - (j : ℤ)) := rfl
  have hSpos : (0 : ℝ) < S := by rw [hSeq]; positivity
  have hprod : (3 : ℝ) ^ j * S = (3 : ℝ) ^ m := by
    rw [hSeq, ← zpow_natCast (3 : ℝ) j, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  have hSle : S ≤ (3 : ℝ) ^ m := by
    rw [hSeq]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hprodLow : -(3 : ℝ) ^ m ≤ (idx i : ℝ) * S := by
    have h := mul_le_mul_of_nonneg_right hlowR hSpos.le
    have heq : -(3 : ℝ) ^ j * S = -(3 : ℝ) ^ m := by rw [neg_mul, hprod]
    linarith only [h, heq]
  have hprodHigh : (idx i : ℝ) * S ≤ (3 : ℝ) ^ m := by
    have h := mul_le_mul_of_nonneg_right hhighR hSpos.le
    linarith only [h, hprod]
  have hpow : (3 : ℝ) ^ (m + 1) = (3 : ℝ) ^ m * 3 := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
  refine ⟨?_, ?_⟩
  · rw [hpow]
    linarith only [hxii.1, hprodLow, hSle]
  · rw [hpow]
    linarith only [hxii.2, hprodHigh, hSle]

/-- **The uniform deterministic bound on `envelopeRatioOn`, over the whole
combinatorial index set.** For every fixed `omega, m, L`, a single real
`Mbar omega` dominates `envelopeRatioOn L (openCubeSet Q) omega` for *every*
`j : ℕ` and *every* `Q ∈ ellipBelowSubCubeFinset d m j`. -/
theorem ellipBelow_envelopeRatioOn_bddAbove_finset (m : ℤ) (L : ℕ) (omega : ShellSeq d) :
    ∃ Mbar : ℝ, 0 ≤ Mbar ∧
      ∀ (j : ℕ) {Q : TriadicCube d}, Q ∈ ellipBelowSubCubeFinset d m j →
        envelopeRatioOn L (openCubeSet Q) omega ≤ Mbar := by
  obtain ⟨M, _hM0, hM⟩ := ellipBelow_streamCutoff_bounded_on
    (isBounded_cubeSet (originCube d (m + 1))) omega L
  refine ⟨max 1 (M ^ 2 / (cutoffEnvelopeConst d * max 1 (L : ℝ))),
    zero_le_one.trans (le_max_left _ _), fun j {Q} hQ =>
      ellipBelow_envelopeRatioOn_le_of_subset hM (ellipBelow_openCubeSet_subset_of_mem hQ)⟩

theorem ellipBelow_subCubeFinset_nonempty (d : ℕ) (m : ℤ) (j : ℕ) :
    (ellipBelowSubCubeFinset d m j).Nonempty := by
  refine ⟨⟨m - (j : ℤ), fun _ => 0⟩, ?_⟩
  refine Finset.mem_image.2 ⟨fun _ => 0, ?_, rfl⟩
  refine Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ⟨?_, ?_⟩
  · exact neg_nonpos.2 (by positivity)
  · positivity

/-! ## The depth-`j` block maximum -/

/-- The largest ratio over the (at most `3^{(d+1)(j+1)}`) sub-cubes of `cu_m`
at scale `m - j`. -/
def ellipBelow_blockMax (d : ℕ) (m : ℤ) (L : ℕ) (j : ℕ) (omega : ShellSeq d) : ℝ :=
  (ellipBelowSubCubeFinset d m j).sup' (ellipBelow_subCubeFinset_nonempty d m j)
    (fun Q => envelopeRatioOn L (openCubeSet Q) omega)

private theorem ellipBelow_measurable_envelopeRatioOn (L : ℕ) (Q : TriadicCube d) :
    Measurable (fun omega : ShellSeq d => envelopeRatioOn L (openCubeSet Q) omega) :=
  measurable_const.max
    ((measurable_volumeAverage_sq_streamCutoff (d := d) L (openCubeSet Q)).div_const
      (cutoffEnvelopeConst d * max 1 (L : ℝ)))

theorem ellipBelow_measurable_blockMax (m : ℤ) (L : ℕ) (j : ℕ) :
    Measurable (fun omega : ShellSeq d => ellipBelow_blockMax d m L j omega) := by
  have heq : (fun omega : ShellSeq d => ellipBelow_blockMax d m L j omega) =
      (ellipBelowSubCubeFinset d m j).sup' (ellipBelow_subCubeFinset_nonempty d m j)
        (fun Q omega => envelopeRatioOn L (openCubeSet Q) omega) := by
    funext omega
    unfold ellipBelow_blockMax
    exact (Finset.sup'_apply (C := fun _ : ShellSeq d => ℝ)
      (ellipBelow_subCubeFinset_nonempty d m j)
      (fun Q omega => envelopeRatioOn L (openCubeSet Q) omega) omega).symm
  rw [heq]
  exact Finset.measurable_sup' _ (fun Q _ => ellipBelow_measurable_envelopeRatioOn L Q)

theorem ellipBelow_one_le_blockMax (m : ℤ) (L : ℕ) (j : ℕ) (omega : ShellSeq d) :
    1 ≤ ellipBelow_blockMax d m L j omega := by
  obtain ⟨Q0, hQ0⟩ := ellipBelow_subCubeFinset_nonempty d m j
  exact le_trans (one_le_envelopeRatioOn L (openCubeSet Q0) omega)
    (Finset.le_sup' (fun Q => envelopeRatioOn L (openCubeSet Q) omega) hQ0)

theorem ellipBelow_le_blockMax (m : ℤ) (L : ℕ) (j : ℕ) (omega : ShellSeq d)
    {Q : TriadicCube d} (hQ : Q ∈ ellipBelowSubCubeFinset d m j) :
    envelopeRatioOn L (openCubeSet Q) omega ≤ ellipBelow_blockMax d m L j omega :=
  Finset.le_sup' (fun Q => envelopeRatioOn L (openCubeSet Q) omega) hQ

/-! ## The per-depth tail bound -/

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- **The depth-`j` union bound**: the tail of the depth-`j` block maximum is
at most the combinatorial count times the per-cube `Γ₁(1)` tail. -/
theorem ellipBelow_measureReal_blockMax_gt_le {m : ℤ} {L : ℕ} {j : ℕ}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {s : ℝ} (hs : 1 ≤ s) :
    P.toMeasure.real {omega : ShellSeq d | s < ellipBelow_blockMax d m L j omega} ≤
      (3 : ℝ) ^ ((d + 1) * (j + 1)) * Real.exp (-s) := by
  have hsub : {omega : ShellSeq d | s < ellipBelow_blockMax d m L j omega} ⊆
      ⋃ Q ∈ ellipBelowSubCubeFinset d m j,
        {omega : ShellSeq d | s < envelopeRatioOn L (openCubeSet Q) omega} := by
    intro omega homega
    have homega' : s < (ellipBelowSubCubeFinset d m j).sup' (ellipBelow_subCubeFinset_nonempty d m j)
        (fun Q => envelopeRatioOn L (openCubeSet Q) omega) := homega
    obtain ⟨Q, hQ, hQs⟩ := (Finset.lt_sup'_iff _).1 homega'
    exact Set.mem_biUnion hQ hQs
  have htail : ∀ Q ∈ ellipBelowSubCubeFinset d m j,
      P.toMeasure {omega : ShellSeq d | s < envelopeRatioOn L (openCubeSet Q) omega} ≤
        ENNReal.ofReal (Real.exp (-s)) := by
    intro Q _
    have h := isBigOWith_gammaSigma_envelopeRatioOn hPrefix hJ2 hJ3 hJ4 L
      (volume_openCubeSet_ne_zero Q) (volume_openCubeSet_lt_top Q).ne hs
    have hfin : P.toMeasure {omega : ShellSeq d | s < envelopeRatioOn L (openCubeSet Q) omega} ≠ ⊤ :=
      measure_ne_top _ _
    have hset : IndependentSums.upperTailEvent
        (fun omega => envelopeRatioOn L (openCubeSet Q) omega) (1 * s) =
        {omega : ShellSeq d | s < envelopeRatioOn L (openCubeSet Q) omega} := by
      rw [one_mul]; rfl
    rw [hset] at h
    have hreal : P.toMeasure.real
        {omega : ShellSeq d | s < envelopeRatioOn L (openCubeSet Q) omega} ≤ Real.exp (-s) := by
      refine h.trans (le_of_eq ?_)
      rw [IndependentSums.gammaSigma_apply, Real.rpow_one, ← Real.exp_neg]
    calc P.toMeasure {omega : ShellSeq d | s < envelopeRatioOn L (openCubeSet Q) omega}
        = ENNReal.ofReal (P.toMeasure.real
            {omega : ShellSeq d | s < envelopeRatioOn L (openCubeSet Q) omega}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal hfin]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  have hmeasure : P.toMeasure {omega : ShellSeq d | s < ellipBelow_blockMax d m L j omega} ≤
      ENNReal.ofReal ((3 : ℝ) ^ ((d + 1) * (j + 1)) * Real.exp (-s)) := by
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    refine le_trans (Finset.sum_le_sum htail) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((ellipBelowSubCubeFinset d m j).card : ℝ) ≤ (3 : ℝ) ^ ((d + 1) * (j + 1)) := by
      have h1 := ellipBelow_card_subCubeFinset_le d m j
      have h2 : (((ellipBelowSubCubeFinset d m j).card : ℕ) : ℝ) ≤
          ((3 ^ ((d + 1) * (j + 1)) : ℕ) : ℝ) := Nat.cast_le.2 h1
      simpa using h2
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le)
  have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  rw [ENNReal.toReal_ofReal (by positivity)] at htoReal
  rw [measureReal_def]
  exact htoReal

/-! ## The union-bound witness -/

/-- The union-bound witness: the supremum, over every depth `j`, of the
depth-`j` block maximum weighted by the printed decaying factor
`3^{-gamma j}`. Well-defined (a genuine finite real, for *every* `omega`, not
merely almost surely) because the range is bounded above by the crude
deterministic bound `ellipBelow_envelopeRatioOn_bddAbove_finset`. -/
def ellipBelow_unionWitness (d : ℕ) (m : ℤ) (L : ℕ) (gamma : ℝ) (omega : ShellSeq d) : ℝ :=
  ⨆ j : ℕ, (3 : ℝ) ^ (-(gamma * (j : ℝ))) * ellipBelow_blockMax d m L j omega

theorem ellipBelow_bddAbove_unionWitness {m : ℤ} {L : ℕ} {gamma : ℝ} (hg0 : 0 ≤ gamma)
    (omega : ShellSeq d) :
    BddAbove (Set.range fun j : ℕ =>
      (3 : ℝ) ^ (-(gamma * (j : ℝ))) * ellipBelow_blockMax d m L j omega) := by
  obtain ⟨Mbar, hMbar0, hMbar⟩ := ellipBelow_envelopeRatioOn_bddAbove_finset m L omega
  refine ⟨Mbar, ?_⟩
  rintro x ⟨j, rfl⟩
  have hweight : (3 : ℝ) ^ (-(gamma * (j : ℝ))) ≤ 1 := by
    rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) from (Real.rpow_zero 3).symm]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : 0 ≤ gamma * (j : ℝ) := mul_nonneg hg0 (Nat.cast_nonneg j)
    linarith only [this]
  have hbm : ellipBelow_blockMax d m L j omega ≤ Mbar :=
    Finset.sup'_le _ _ (fun Q hQ => hMbar j hQ)
  have hbm0 : 0 ≤ ellipBelow_blockMax d m L j omega :=
    le_trans zero_le_one (ellipBelow_one_le_blockMax m L j omega)
  calc (3 : ℝ) ^ (-(gamma * (j : ℝ))) * ellipBelow_blockMax d m L j omega
      ≤ 1 * Mbar := mul_le_mul hweight hbm hbm0 zero_le_one
    _ = Mbar := one_mul _

theorem ellipBelow_le_unionWitness {m : ℤ} {L : ℕ} {gamma : ℝ} (hg0 : 0 ≤ gamma)
    (omega : ShellSeq d) (j : ℕ) :
    (3 : ℝ) ^ (-(gamma * (j : ℝ))) * ellipBelow_blockMax d m L j omega ≤
      ellipBelow_unionWitness d m L gamma omega :=
  le_ciSup (ellipBelow_bddAbove_unionWitness hg0 omega) j

theorem ellipBelow_measurable_unionWitness {m : ℤ} {L : ℕ} {gamma : ℝ} :
    Measurable (fun omega : ShellSeq d => ellipBelow_unionWitness d m L gamma omega) := by
  unfold ellipBelow_unionWitness
  exact Measurable.iSup (fun j => (ellipBelow_measurable_blockMax m L j).const_mul _)

/-! ## The `Γ₁` tail -/

/-- The dimension-only amplitude constant absorbing the geometric-series
constant of the union bound into the `Γ₁` amplitude. -/
def ellipBelow_C0 (d : ℕ) : ℝ :=
  max ((d : ℝ) + 2) (1 + Real.log ((3 : ℝ) ^ (d + 1) * (3 / 2)))

theorem ellipBelow_one_le_C0 (d : ℕ) : 1 ≤ ellipBelow_C0 d := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  exact le_trans (by linarith only [hd]) (le_max_left _ _ : (d : ℝ) + 2 ≤ ellipBelow_C0 d)

/-- **The union bound, at the raw threshold `t`.** Valid once `t ≥ 1` and
`t·gamma ≥ d + 2`. -/
private theorem ellipBelow_measureReal_unionWitness_gt_le {m : ℤ} {L : ℕ} {gamma : ℝ}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (hg0 : 0 < gamma)
    {t : ℝ} (ht1 : 1 ≤ t) (htg : (d : ℝ) + 2 ≤ gamma * t) :
    P.toMeasure.real {omega : ShellSeq d | t < ellipBelow_unionWitness d m L gamma omega} ≤
      (3 : ℝ) ^ (d + 1) * (3 / 2) * Real.exp (-t) := by
  set q : ℝ := (3 : ℝ) ^ (d + 1) * (3 : ℝ) ^ (-(t * gamma)) with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hqle3 : q ≤ (3 : ℝ) ^ (-(1 : ℝ)) := by
    have hstep : (3 : ℝ) ^ (-(t * gamma)) ≤ (3 : ℝ) ^ (-((d : ℝ) + 2)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [htg])
    calc q ≤ (3 : ℝ) ^ (d + 1) * (3 : ℝ) ^ (-((d : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (3 : ℝ) ^ (-(1 : ℝ)) := by
          rw [← Real.rpow_natCast (3 : ℝ) (d + 1), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
          congr 1
          push_cast
          ring
  have hqlt : q < 1 := by
    have h1 : (3 : ℝ) ^ (-(1 : ℝ)) < 1 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_one]
      norm_num
    linarith only [hqle3, h1]
  have hsub : {omega : ShellSeq d | t < ellipBelow_unionWitness d m L gamma omega} ⊆
      ⋃ j : ℕ, {omega : ShellSeq d |
        t < (3 : ℝ) ^ (-(gamma * (j : ℝ))) * ellipBelow_blockMax d m L j omega} := by
    intro omega homega
    obtain ⟨j, hj⟩ := (lt_ciSup_iff (ellipBelow_bddAbove_unionWitness hg0.le omega)).1 homega
    exact Set.mem_iUnion.2 ⟨j, hj⟩
  have hterm : ∀ j : ℕ,
      P.toMeasure.real {omega : ShellSeq d |
        t < (3 : ℝ) ^ (-(gamma * (j : ℝ))) * ellipBelow_blockMax d m L j omega} ≤
      Real.exp (-t) * (3 : ℝ) ^ (d + 1) * q ^ j := by
    intro j
    have hweightpos : (0 : ℝ) < (3 : ℝ) ^ (gamma * (j : ℝ)) := by positivity
    have hkey : ∀ bm : ℝ, (3 : ℝ) ^ (-(gamma * (j : ℝ))) * bm = bm / (3 : ℝ) ^ (gamma * (j : ℝ)) :=
      fun bm => by rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), div_eq_mul_inv, mul_comm]
    have hset : {omega : ShellSeq d |
        t < (3 : ℝ) ^ (-(gamma * (j : ℝ))) * ellipBelow_blockMax d m L j omega} =
        {omega : ShellSeq d | t * (3 : ℝ) ^ (gamma * (j : ℝ)) < ellipBelow_blockMax d m L j omega} := by
      ext omega
      simp only [Set.mem_ofPred_eq, hkey, lt_div_iff₀ hweightpos]
    have h3ge1 : (1 : ℝ) ≤ (3 : ℝ) ^ (gamma * (j : ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hg0.le (Nat.cast_nonneg j))
    have ht0 : (0 : ℝ) ≤ t := by linarith only [ht1]
    have hs1 : 1 ≤ t * (3 : ℝ) ^ (gamma * (j : ℝ)) :=
      le_trans ht1 (le_mul_of_one_le_right ht0 h3ge1)
    have hbase := ellipBelow_measureReal_blockMax_gt_le (m := m) (L := L) (j := j)
      hPrefix hJ2 hJ3 hJ4 hs1
    rw [hset]
    refine hbase.trans ?_
    have hconvex : gamma * (j : ℝ) * Real.log 3 + 1 ≤ (3 : ℝ) ^ (gamma * (j : ℝ)) := by
      have h := Real.add_one_le_exp (Real.log 3 * (gamma * (j : ℝ)))
      rwa [← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), mul_comm (Real.log 3)] at h
    have hexple : t + t * gamma * (j : ℝ) * Real.log 3 ≤ t * (3 : ℝ) ^ (gamma * (j : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hconvex ht0
      have heq : t * (gamma * (j : ℝ) * Real.log 3 + 1) =
          t + t * gamma * (j : ℝ) * Real.log 3 := by ring
      linarith only [h, heq]
    have hexp1 : Real.exp (-(t * (3 : ℝ) ^ (gamma * (j : ℝ)))) ≤
        Real.exp (-t) * Real.exp (-(t * gamma * (j : ℝ) * Real.log 3)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith only [hexple])
    have hexp2 : Real.exp (-(t * gamma * (j : ℝ) * Real.log 3)) =
        (3 : ℝ) ^ (-(t * gamma) * (j : ℝ)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    have hqj : (3 : ℝ) ^ (-(t * gamma) * (j : ℝ)) = ((3 : ℝ) ^ (-(t * gamma))) ^ j := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
    have hprodEq : (3 : ℝ) ^ ((d + 1) * (j + 1)) =
        (3 : ℝ) ^ (d + 1) * ((3 : ℝ) ^ (d + 1)) ^ j := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    calc (3 : ℝ) ^ ((d + 1) * (j + 1)) * Real.exp (-(t * (3 : ℝ) ^ (gamma * (j : ℝ))))
        ≤ (3 : ℝ) ^ ((d + 1) * (j + 1)) *
            (Real.exp (-t) * (3 : ℝ) ^ (-(t * gamma) * (j : ℝ))) := by
          rw [← hexp2]
          exact mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _ = Real.exp (-t) * (3 : ℝ) ^ (d + 1) *
          (((3 : ℝ) ^ (d + 1)) ^ j * ((3 : ℝ) ^ (-(t * gamma))) ^ j) := by
          rw [hprodEq, hqj]; ring
      _ = Real.exp (-t) * (3 : ℝ) ^ (d + 1) * q ^ j := by rw [hqdef, mul_pow]
  have hmeasure : P.toMeasure {omega : ShellSeq d | t < ellipBelow_unionWitness d m L gamma omega} ≤
      ENNReal.ofReal (Real.exp (-t) * (3 : ℝ) ^ (d + 1) * (1 - q)⁻¹) := by
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_iUnion_le _) ?_
    have hstep1 : ∀ j : ℕ, P.toMeasure {omega : ShellSeq d |
        t < (3 : ℝ) ^ (-(gamma * (j : ℝ))) * ellipBelow_blockMax d m L j omega} ≤
        ENNReal.ofReal (Real.exp (-t) * (3 : ℝ) ^ (d + 1) * q ^ j) := by
      intro j
      have hfin : P.toMeasure {omega : ShellSeq d |
          t < (3 : ℝ) ^ (-(gamma * (j : ℝ))) * ellipBelow_blockMax d m L j omega} ≠ ⊤ :=
        measure_ne_top _ _
      calc P.toMeasure {omega : ShellSeq d |
            t < (3 : ℝ) ^ (-(gamma * (j : ℝ))) * ellipBelow_blockMax d m L j omega}
          = ENNReal.ofReal (P.toMeasure.real {omega : ShellSeq d |
              t < (3 : ℝ) ^ (-(gamma * (j : ℝ))) * ellipBelow_blockMax d m L j omega}) := by
            rw [measureReal_def, ENNReal.ofReal_toReal hfin]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (hterm j)
    refine le_trans (ENNReal.tsum_le_tsum hstep1) ?_
    have hgeom : Summable (fun j : ℕ => q ^ j) := summable_geometric_of_lt_one hq0 hqlt
    have hgeomEq : (∑' j : ℕ, q ^ j) = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hqlt
    rw [show (fun j : ℕ => ENNReal.ofReal (Real.exp (-t) * (3 : ℝ) ^ (d + 1) * q ^ j)) =
        fun j => ENNReal.ofReal (Real.exp (-t) * (3 : ℝ) ^ (d + 1)) * ENNReal.ofReal (q ^ j) from
        funext fun j => by rw [← ENNReal.ofReal_mul (by positivity)]]
    rw [ENNReal.tsum_mul_left,
      ← ENNReal.ofReal_tsum_of_nonneg (fun j => pow_nonneg hq0 j) hgeom, hgeomEq,
      ← ENNReal.ofReal_mul (by positivity), mul_assoc]
  have hfinal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  have hinvnn : (0 : ℝ) ≤ (1 - q)⁻¹ := inv_nonneg.2 (by linarith only [hqlt])
  rw [ENNReal.toReal_ofReal (by positivity)] at hfinal
  have hqbound : (1 - q)⁻¹ ≤ 3 / 2 := by
    have h1 : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 : ℝ)) := by
      have h1' : (3 : ℝ) ^ (-(1 : ℝ)) < 1 := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_one]
        norm_num
      linarith only [h1']
    have h2 : (1 - (3 : ℝ) ^ (-(1 : ℝ))) ≤ 1 - q := by linarith only [hqle3]
    have h3 : ((1 : ℝ) - (3 : ℝ) ^ (-(1 : ℝ)))⁻¹ = 3 / 2 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_one]
      norm_num
    calc (1 - q)⁻¹ = 1 / (1 - q) := (one_div _).symm
      _ ≤ 1 / (1 - (3 : ℝ) ^ (-(1 : ℝ))) := one_div_le_one_div_of_le h1 h2
      _ = (1 - (3 : ℝ) ^ (-(1 : ℝ)))⁻¹ := one_div _
      _ = 3 / 2 := h3
  rw [measureReal_def]
  refine hfinal.trans ?_
  have hexpnn : (0 : ℝ) ≤ Real.exp (-t) * (3 : ℝ) ^ (d + 1) := by positivity
  calc Real.exp (-t) * (3 : ℝ) ^ (d + 1) * (1 - q)⁻¹ ≤
        Real.exp (-t) * (3 : ℝ) ^ (d + 1) * (3 / 2) :=
        mul_le_mul_of_nonneg_left hqbound hexpnn
    _ = (3 : ℝ) ^ (d + 1) * (3 / 2) * Real.exp (-t) := by ring

theorem ellipBelow_nonneg_unionWitness {m : ℤ} {L : ℕ} {gamma : ℝ} (hg0 : 0 ≤ gamma)
    (omega : ShellSeq d) :
    0 ≤ ellipBelow_unionWitness d m L gamma omega := by
  have h0 := ellipBelow_le_unionWitness (m := m) (L := L) hg0 omega 0
  have hbm0 : (1 : ℝ) ≤ ellipBelow_blockMax d m L 0 omega := ellipBelow_one_le_blockMax m L 0 omega
  have hweq : (3 : ℝ) ^ (-(gamma * ((0 : ℕ) : ℝ))) = 1 := by norm_num
  rw [hweq, one_mul] at h0
  linarith only [h0, hbm0]

/-- **The `Γ₁(C(d)/gamma)` tail of the union-bound witness.** -/
theorem ellipBelow_isBigOWith_unionWitness {m : ℤ} {L : ℕ} {gamma : ℝ}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (hg0 : 0 < gamma) (hg1 : gamma < 1) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega => ellipBelow_unionWitness d m L gamma omega) (ellipBelow_C0 d / gamma) := by
  intro s hs
  set t : ℝ := ellipBelow_C0 d / gamma * s with htdef
  have hC0_1 : 1 ≤ ellipBelow_C0 d := ellipBelow_one_le_C0 d
  have hC0pos : 0 < ellipBelow_C0 d := lt_of_lt_of_le zero_lt_one hC0_1
  have hginv : 1 ≤ ellipBelow_C0 d / gamma := by
    rw [le_div_iff₀ hg0]
    calc (1 : ℝ) * gamma = gamma := one_mul _
      _ ≤ 1 := hg1.le
      _ ≤ ellipBelow_C0 d := hC0_1
  have ht1 : 1 ≤ t := by
    rw [htdef]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ ellipBelow_C0 d / gamma * s := mul_le_mul hginv hs zero_le_one (by linarith only [hginv])
  have htCs : ellipBelow_C0 d * s ≤ t := by
    rw [htdef]
    have hinv1 : (1 : ℝ) ≤ 1 / gamma := by
      rw [le_div_iff₀ hg0]; linarith only [hg1]
    have hCsnn : (0 : ℝ) ≤ ellipBelow_C0 d * s := by positivity
    calc ellipBelow_C0 d * s = ellipBelow_C0 d * s * 1 := (mul_one _).symm
      _ ≤ ellipBelow_C0 d * s * (1 / gamma) := mul_le_mul_of_nonneg_left hinv1 hCsnn
      _ = ellipBelow_C0 d / gamma * s := by ring
  have htg : (d : ℝ) + 2 ≤ gamma * t := by
    have h1 : gamma * t = ellipBelow_C0 d * s := by
      rw [htdef]; field_simp
    have h2 : (d : ℝ) + 2 ≤ ellipBelow_C0 d := le_max_left _ _
    rw [h1]
    calc (d : ℝ) + 2 ≤ ellipBelow_C0 d := h2
      _ = ellipBelow_C0 d * 1 := (mul_one _).symm
      _ ≤ ellipBelow_C0 d * s := mul_le_mul_of_nonneg_left hs hC0pos.le
  have hK : (3 : ℝ) ^ (d + 1) * (3 / 2) ≤ Real.exp (ellipBelow_C0 d - 1) := by
    have h1 : 1 + Real.log ((3 : ℝ) ^ (d + 1) * (3 / 2)) ≤ ellipBelow_C0 d := le_max_right _ _
    have h2 : Real.log ((3 : ℝ) ^ (d + 1) * (3 / 2)) ≤ ellipBelow_C0 d - 1 := by
      linarith only [h1]
    have h3 := Real.exp_le_exp.2 h2
    rwa [Real.exp_log (by positivity)] at h3
  have hts : ellipBelow_C0 d - 1 ≤ t - s := by
    have h1 : (ellipBelow_C0 d - 1) * s ≤ t - s := by
      have h2 : (ellipBelow_C0 d - 1) * s = ellipBelow_C0 d * s - s := by ring
      linarith only [h2, htCs]
    have h3 : (ellipBelow_C0 d - 1) * 1 ≤ (ellipBelow_C0 d - 1) * s :=
      mul_le_mul_of_nonneg_left hs (by linarith only [hC0_1])
    linarith only [h1, h3]
  have hexp_ts : (3 : ℝ) ^ (d + 1) * (3 / 2) ≤ Real.exp (t - s) :=
    hK.trans (Real.exp_le_exp.2 hts)
  have hbase := ellipBelow_measureReal_unionWitness_gt_le (m := m) (L := L)
    hPrefix hJ2 hJ3 hJ4 hg0 ht1 htg
  have hfinal2 : (3 : ℝ) ^ (d + 1) * (3 / 2) * Real.exp (-t) ≤ Real.exp (-s) := by
    have h1 : (3 : ℝ) ^ (d + 1) * (3 / 2) * Real.exp (-t) ≤ Real.exp (t - s) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hexp_ts (Real.exp_pos _).le
    have h2 : Real.exp (t - s) * Real.exp (-t) = Real.exp (-s) := by
      rw [← Real.exp_add]; congr 1; ring
    linarith only [h1, h2]
  have hgoal : P.toMeasure.real
      (IndependentSums.upperTailEvent (fun omega => ellipBelow_unionWitness d m L gamma omega)
        (ellipBelow_C0 d / gamma * s)) ≤ Real.exp (-s) := by
    have hset : IndependentSums.upperTailEvent
        (fun omega => ellipBelow_unionWitness d m L gamma omega) (ellipBelow_C0 d / gamma * s) =
        {omega : ShellSeq d | t < ellipBelow_unionWitness d m L gamma omega} := by
      rw [htdef]; rfl
    rw [hset]
    exact hbase.trans hfinal2
  simpa only [IndependentSums.gammaSigma_apply, Real.rpow_one, ← Real.exp_neg] using hgoal

theorem ellipBelow_isBigO_unionWitness {m : ℤ} {L : ℕ} {gamma : ℝ}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (hg0 : 0 < gamma) (hg1 : gamma < 1) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega => ellipBelow_unionWitness d m L gamma omega) (ellipBelow_C0 d / gamma) :=
  (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
    (fun omega => ellipBelow_nonneg_unionWitness hg0.le omega)).1
    (ellipBelow_isBigOWith_unionWitness hPrefix hJ2 hJ3 hJ4 hg0 hg1)

/-- **`ellipBelow_union`: the exact `hUnion` hypothesis of `ellipBelow_main`.** -/
theorem ellipBelow_union (d : ℕ) [NeZero d] :
    ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ (P : ProbabilityMeasure (ShellSeq d)),
        ShellLawPrefix d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
        ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
          ∀ m L : ℕ, 1 ≤ L → (L : ℝ) ≤ 4 * (m : ℝ) →
            ∃ X : ShellSeq d → ℝ,
              Measurable X ∧
              IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) X
                  (C0 * gamma⁻¹) ∧
                ∀ (omega : ShellSeq d) (k : ℤ), k ≤ (m : ℤ) →
                  ∀ Q : TriadicCube d, Q.scale = k →
                    cubeCenter Q ∈ cubeSet (originCube d (m : ℤ)) →
                      envelopeRatioOn L (openCubeSet Q) omega ≤
                        (3 : ℝ) ^ (-(gamma * ((k : ℝ) - (m : ℝ)))) * X omega := by
  refine ⟨ellipBelow_C0 d, ellipBelow_one_le_C0 d,
    fun P hPrefix hJ2 hJ3 hJ4 gamma hg0 hg1 m L _hL _hL4 => ?_⟩
  refine ⟨fun omega => ellipBelow_unionWitness d (m : ℤ) L gamma omega,
    ellipBelow_measurable_unionWitness, ?_, ?_⟩
  · have h := ellipBelow_isBigO_unionWitness (m := (m : ℤ)) (L := L)
      hPrefix hJ2 hJ3 hJ4 hg0 hg1
    rwa [div_eq_mul_inv] at h
  · intro omega k hk Q hQscale hQmem
    set j : ℕ := (((m : ℤ) - k)).toNat with hjdef
    have hjcast : (j : ℤ) = (m : ℤ) - k := Int.toNat_of_nonneg (by omega)
    have hQscale' : Q.scale = (m : ℤ) - (j : ℤ) := by rw [hjcast]; omega
    have hQfin : Q ∈ ellipBelowSubCubeFinset d (m : ℤ) j :=
      ellipBelow_mem_subCubeFinset hQscale' hQmem
    have hratio : envelopeRatioOn L (openCubeSet Q) omega ≤ ellipBelow_blockMax d (m : ℤ) L j omega :=
      ellipBelow_le_blockMax (m : ℤ) L j omega hQfin
    have hwitness := ellipBelow_le_unionWitness (m := (m : ℤ)) (L := L) hg0.le omega j
    have hjR : (j : ℝ) = (m : ℝ) - (k : ℝ) := by exact_mod_cast hjcast
    have hweightpos : (0 : ℝ) < (3 : ℝ) ^ (gamma * (j : ℝ)) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hwitness hweightpos.le
    have heq1 : (3 : ℝ) ^ (gamma * (j : ℝ)) * ((3 : ℝ) ^ (-(gamma * (j : ℝ))) *
        ellipBelow_blockMax d (m : ℤ) L j omega) = ellipBelow_blockMax d (m : ℤ) L j omega := by
      rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      norm_num
    rw [heq1] at hmul
    have heq2 : (3 : ℝ) ^ (gamma * (j : ℝ)) = (3 : ℝ) ^ (-(gamma * ((k : ℝ) - (m : ℝ)))) := by
      rw [hjR]; congr 1; ring
    rw [heq2] at hmul
    exact hratio.trans hmul

/-- **`p.ellipticity.Ptwoprime`, outright.** The exact conclusion of
`SuperdiffusionCLT.Frozen.Section4.ellipticity_below_cutoff`, with
no remaining hypothesis: `ellipBelow_main_of_union`
(`EllipticityBelowCutoffMain.lean`) discharged by `ellipBelow_union` above. -/
theorem ellipBelow_main (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P →
          ShellLawJ1Restriction d P →
          ShellLawJ2 d P →
          ShellLawJ3 d P →
          ShellLawJ4 d P →
          ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
            ∀ m L : ℕ, 1 ≤ L → (L : ℝ) ≤ 4 * (m : ℝ) →
              ∃ X : ShellSeq d → ℝ,
                Measurable X ∧
                IndependentSums.IsBigO P.toMeasure
                    (IndependentSums.gammaSigma 1) X
                    (C * gamma⁻¹ * nu ^ (-(2 : ℝ)) * (L : ℝ)) ∧
                  ∀ (omega : ShellSeq d) (k : ℤ), k ≤ (m : ℤ) →
                    ∀ Q : TriadicCube d, Q.scale = k →
                      cubeCenter Q ∈ cubeSet (originCube d (m : ℤ)) →
                        ∀ p q : BlockVec d,
                          2 * blockVecDot p
                                (blockMatVecMul
                                  (coarseBlockMatrix (cubeSet Q)
                                    (coefficientCutoff nu omega L).toCoeffField)
                                  q) ≤
                            (3 : ℝ) ^ (-(gamma * ((k : ℝ) - (m : ℝ)))) * X omega *
                              (blockVecDot p
                                  (blockMatVecMul
                                    (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ))))
                                    p) +
                                blockVecDot q
                                  (blockMatVecMul
                                    (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ))))
                                    q)) :=
  ellipBelow_main_of_union d hd (ellipBelow_union d)

end

end SuperdiffusionCLT.Section4.Ellipticity
