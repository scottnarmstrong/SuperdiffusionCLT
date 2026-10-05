/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Carrier.Integrability
public import SuperdiffusionCLT.AKHC61.Carrier.OrliczMoments
public import SuperdiffusionCLT.AKHC61.Response.CoarseAveragesC
public import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Package A1-sq: square-integrability of the coarse block matrix entries under (P2')

The square-integrable companion to package A1
(`SuperdiffusionCLT.AKHC61.Carrier.akhc_integrable_blockMatEntry_of_P2`,
`Integrability.lean`): every entry of the coarse block matrix `bfA_L(Q)` of the
infrared cutoff field is **square** `P`-integrable, at every triadic cube `Q`,
under `0 < nu` and the (P2') clause of the main statement
`SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3` (the (P2') clause is copied
verbatim below).

## Route

* The (P2') Loewner comparison at the base cube `cu_j`, together with
  unconditional positive semidefiniteness, sandwiches every diagonal entry of
  `bfA_L(Q)` between `0` and `(1 + cX) Aval`, where `Aval` is the fixed real
  number given by the corresponding `annealedBlockMatrix` entry, `c > 0` is a
  fixed real, and `X` is the (P2') tail variable. Squaring and using
  `2|X| ≤ 1 + X²` bounds the diagonal entry's square by an affine function of
  `X²`; this needs no positivity of `Aval`, so **none** of A1's Step D/E
  (deterministic positive-definiteness, integrability-by-contradiction) is
  needed here.
* `X² ∈ L¹` from the (P2') growth condition at the single exponent
  `p := min 3 p_{Ψ_S} > 2` (`p_{Ψ_S} > 2` is a (P2') hypothesis), reusing
  package A3's `akhc_moment_le_of_isBigO`/`akhc_integrable_abs_rpow_of_isBigO`
  (`OrliczMoments.lean`) at `q := 2 < p`. Since those theorems need the growth
  bound on the whole range `(1, p]` while (P2') only supplies `[2, p_{Ψ_S}]`,
  the range `(1, 2)` is filled in by `s^p ≤ s^2` for `s ≥ 1`, `p ≤ 2`
  (`akhcSq_growth_ext`).
* Off-diagonal entries are controlled by the mean of the two diagonal entries
  (the `2×2` positive-semidefinite minor bound
  `abs_blockMatEntry_le_of_isSymmetricBlockMat`, unconditional), so their
  square is bounded by the sum of the two diagonal squares.
* A general triadic cube `Q` is placed inside a large enough base cube `cu_j`
  exactly as in A1 (`akhcSq_exists_j_originCube_mem`, a verbatim copy of A1's
  private `akhc_exists_j_originCube_mem`, since that helper is private to
  `Integrability.lean`).

Every hypothesis is copied **verbatim** from the (P2') clause of the root; no
J3, no `PsiS ≥ 1` addition (the root's own clause already carries it), no
`ShellLawPrefix`/`J2`/`J4`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Carrier

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

variable {d : ℕ}

/-! ## Step 0: a numeric inequality -/

/-- **`(1+cx)² ≤ (1+c) + (c+c²)x²` for `c ≥ 0`.** Uses only `2x ≤ 1+x²`
(`sq_nonneg (x-1)`), scaled by `c ≥ 0`. -/
private theorem akhcSq_sq_one_add_mul_le (c x : ℝ) (hc : 0 ≤ c) :
    (1 + c * x) ^ 2 ≤ (1 + c) + (c + c ^ 2) * x ^ 2 := by
  have hsq : 0 ≤ (x - 1) ^ 2 := sq_nonneg _
  have h2x : 2 * x ≤ 1 + x ^ 2 := by nlinarith only [hsq]
  have hmul : c * (2 * x) ≤ c * (1 + x ^ 2) := mul_le_mul_of_nonneg_left h2x hc
  nlinarith only [hmul]

/-! ## Step 1: extend the (P2') growth condition at `p := 2` to the full range
`(1, min 3 p_{Ψ_S}]`

`akhc_moment_le_of_isBigO`/`akhc_integrable_abs_rpow_of_isBigO`
(`OrliczMoments.lean`) need the growth bound on the whole range
`(1, pPsi]`; (P2') only supplies `[2, pPsiS]`. Since `⌈p⌉₊ = 2` for every
`p ∈ (1, 2]`, the growth bound at `p := 2` gives the bound at any such `p` via
`s^p ≤ s^2` (`s ≥ 1`). -/

/-- The (P2') growth condition, extended from `[2, pPsiS]` to `(1, min 3
pPsiS]` by reducing `p ∈ (1, 2]` to the case `p = 2`. -/
private theorem akhcSq_growth_ext
    {PsiS : ℝ → ℝ} {KPsiS pPsiS : ℝ} (hpPsiS : 2 < pPsiS)
    (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t)) :
    ∀ p : ℝ, 1 < p → p ≤ min (3 : ℝ) pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t) := by
  intro p hp1 hpmin t s ht hs
  rcases le_or_gt p 2 with hple2 | hpgt2
  · have h1 : 1 < ⌈p⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast hp1)
    have h2 : ⌈p⌉₊ ≤ 2 := Nat.ceil_le.2 hple2
    have hceil : ⌈p⌉₊ = 2 := by omega
    have h2ceil : (⌈(2 : ℝ)⌉₊ : ℕ) = 2 := by norm_num
    have h2growth := hGrowth 2 le_rfl hpPsiS.le t s ht hs
    rw [h2ceil] at h2growth
    have hsp_le : s ^ p ≤ s ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hs hple2
    rw [hceil]
    exact hsp_le.trans h2growth
  · have hp2le : (2 : ℝ) ≤ p := hpgt2.le
    have hppsiS : p ≤ pPsiS := le_trans hpmin (min_le_right _ _)
    exact hGrowth p hp2le hppsiS t s ht hs

/-! ## Step 2: `X²` is `P`-integrable, from the (P2') growth condition -/

/-- **The (P2') tail variable `X` has a finite second moment.** Package A3's
`akhc_integrable_abs_rpow_of_isBigO` (`OrliczMoments.lean`) at
`q := 2 < p := min 3 pPsiS`, with the growth condition extended by
`akhcSq_growth_ext`. -/
private theorem akhcSq_integrable_sq_of_isBigO
    {PsiS : ℝ → ℝ} {KPsiS pPsiS A : ℝ} (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
    (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
    (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
    {X : Ω → ℝ} (hA : 0 < A) (hXm : Measurable X)
    (hX : Homogenization.IndependentSums.IsBigO mu PsiS X A) :
    Integrable (fun omega => X omega ^ 2) mu := by
  have hp_gt2 : (2 : ℝ) < min (3 : ℝ) pPsiS := lt_min (by norm_num) hpPsiS
  have hGrowth' := akhcSq_growth_ext hpPsiS hGrowth
  have hInt := akhc_integrable_abs_rpow_of_isBigO hKPsiS hPsiSOne hGrowth' hA hXm hX
    (p := min (3 : ℝ) pPsiS) (q := (2 : ℝ))
    (lt_trans one_lt_two hp_gt2) le_rfl one_le_two hp_gt2
  refine hInt.congr (Filter.Eventually.of_forall fun omega => ?_)
  show |X omega| ^ (2 : ℝ) = X omega ^ 2
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact sq_abs (X omega)

/-! ## Step 3: a general triadic cube lies inside some large enough `cu_j`

Verbatim copy of A1's private `akhc_exists_j_originCube_mem`
(`Integrability.lean`): that helper is private to its file, so it is
re-derived here under a distinct name. -/

/-- Every triadic cube's centre lies in `cubeSet (originCube d j)` for `j`
large enough, and above any given `m2` and the cube's own scale. -/
private theorem akhcSq_exists_j_originCube_mem [NeZero d] (Q : TriadicCube d) (m2 : ℕ) :
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

/-! ## Step 4: diagonal square-integrability at a cube `Q` placed under a base
cube `cu_j` -/

/-- **A diagonal entry of `bfA_L(Q)` is square-`P`-integrable, given
`Q.scale ≤ j`, `cubeCenter Q ∈ cubeSet (originCube d j)`, `m2 ≤ j`.** The
(P2') Loewner comparison sandwiches the (unconditionally nonnegative) entry
between `0` and `(1 + cX)Aval`, `Aval` the fixed real
`blockMatEntry (annealedBlockMatrix ...) alpha alpha`, `c > 0` fixed; squaring
via `akhcSq_sq_one_add_mul_le` bounds the square by an affine function of
`X²`, integrable by `akhcSq_integrable_sq_of_isBigO`. No positivity of `Aval`
is needed. -/
private theorem akhcSq_integrable_blockMatEntry_sq_diag
    [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
    (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
    (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
    (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
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
    {j : ℕ} (hjm2 : m2 ≤ j) (Q : TriadicCube d) (hjscale : Q.scale ≤ (j : ℤ))
    (hjmem : cubeCenter Q ∈ cubeSet (originCube d (j : ℤ))) (alpha : BlockCoord d) :
    Integrable (fun omega => (blockMatEntry
        (Homogenization.coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField)
        alpha alpha) ^ 2) P.toMeasure := by
  obtain ⟨X, hXm, hXbig, hLoewner⟩ := hP2 j hjm2
  set Aval : ℝ := blockMatEntry (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
      nu L P (cubeSet (originCube d (j : ℤ)))) alpha alpha with hAval_def
  set c : ℝ := (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) with hc_def
  have hc_pos : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  set A' : ℝ := max (H * (j : ℝ) ^ D) 1 with hA'_def
  have hA'_pos : 0 < A' := lt_of_lt_of_le zero_lt_one (le_max_right _ 1)
  have hX' : Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X A' :=
    hXbig.mono_scale (le_max_left (H * (j : ℝ) ^ D) 1)
  have hX2 : Integrable (fun omega => X omega ^ 2) P.toMeasure :=
    akhcSq_integrable_sq_of_isBigO hKPsiS hpPsiS hPsiSOne hGrowth hA'_pos hXm hX'
  have hnn : ∀ omega, 0 ≤ blockMatEntry
      (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField) alpha alpha := by
    intro omega
    have h := zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff hnu omega L Q
      (blockBasis alpha)
    rwa [blockBasis_pairing] at h
  have hle : ∀ omega, blockMatEntry
      (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField) alpha alpha ≤
      (1 + c * X omega) * Aval := by
    intro omega
    have h2 := hLoewner omega Q hjscale hjmem (blockBasis alpha)
    rw [blockBasis_pairing, blockBasis_pairing] at h2
    have hsmulEntry : blockMatEntry
        ((1 + c * X omega) •
          SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
            (cubeSet (originCube d (j : ℤ)))) alpha alpha =
        (1 + c * X omega) * Aval := by
      cases alpha with
      | inl i => rfl
      | inr i => rfl
    rw [hsmulEntry] at h2
    linarith only [h2]
  have hM_nonneg : ∀ omega, 0 ≤ (1 + c * X omega) * Aval :=
    fun omega => le_trans (hnn omega) (hle omega)
  have hentry_sq_le : ∀ omega, (blockMatEntry
      (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField) alpha alpha) ^ 2
      ≤ ((1 + c * X omega) * Aval) ^ 2 :=
    fun omega => pow_le_pow_left₀ (hnn omega) (hle omega) 2
  have hmaj : ∀ omega, ((1 + c * X omega) * Aval) ^ 2 ≤
      Aval ^ 2 * (1 + c) + Aval ^ 2 * (c + c ^ 2) * X omega ^ 2 := by
    intro omega
    have h := akhcSq_sq_one_add_mul_le c (X omega) hc_pos.le
    have hstep : (1 + c * X omega) ^ 2 * Aval ^ 2 ≤
        ((1 + c) + (c + c ^ 2) * X omega ^ 2) * Aval ^ 2 :=
      mul_le_mul_of_nonneg_right h (sq_nonneg Aval)
    nlinarith only [hstep]
  have hmajor_int : Integrable
      (fun omega => Aval ^ 2 * (1 + c) + Aval ^ 2 * (c + c ^ 2) * X omega ^ 2) P.toMeasure :=
    (integrable_const (Aval ^ 2 * (1 + c))).add (hX2.const_mul (Aval ^ 2 * (c + c ^ 2)))
  have hmeasPow : Measurable (fun omega => (blockMatEntry
      (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField) alpha alpha) ^ 2) :=
    (measurable_blockMatEntry_coarseBlockMatrix hnu L Q alpha alpha).pow_const 2
  refine Integrable.mono' hmajor_int hmeasPow.aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact le_trans (hentry_sq_le omega) (hmaj omega)

/-! ## Step 5: diagonal square-integrability at a general triadic cube -/

/-- **Every diagonal entry of `bfA_L(Q)` is square-`P`-integrable, at every
triadic cube `Q`.** `Q` is placed inside a large enough base cube `cu_j`
(`akhcSq_exists_j_originCube_mem`), then `akhcSq_integrable_blockMatEntry_sq_diag`
applies. -/
private theorem akhcSq_integrable_blockMatEntry_sq_diag_general
    [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
    (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
    (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
    (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
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
    Integrable (fun omega => (blockMatEntry
        (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField)
        alpha alpha) ^ 2) P.toMeasure := by
  obtain ⟨j, hjm2, hjscale, hjmem⟩ := akhcSq_exists_j_originCube_mem Q m2
  exact akhcSq_integrable_blockMatEntry_sq_diag hnu P L gamma H D m2 PsiS KPsiS pPsiS
    hKPsiS hpPsiS hPsiSOne hGrowth hP2 hjm2 Q hjscale hjmem alpha

/-! ## Step 6: off-diagonal entries, from the `2×2` positive-semidefinite
minor bound -/

/-- **Every entry of `bfA_L(Q)` is square-`P`-integrable, at every triadic
cube `Q` and every pair of block coordinates.** The diagonal case is
`akhcSq_integrable_blockMatEntry_sq_diag_general`; the general case follows
from the `2×2` PSD-minor bound `abs_blockMatEntry_le_of_isSymmetricBlockMat`
(unconditional), which bounds `|bfA_L(Q)_{αβ}|` by the mean of the two
diagonal entries, so its square is at most the sum of the two diagonal
squares. -/
private theorem akhcSq_integrable_blockMatEntry_sq_general
    [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
    (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
    (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
    (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
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
    Integrable (fun omega => (blockMatEntry
        (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField)
        alpha beta) ^ 2) P.toMeasure := by
  have hDiagA := akhcSq_integrable_blockMatEntry_sq_diag_general hnu P L gamma H D m2 PsiS KPsiS
    pPsiS hKPsiS hpPsiS hPsiSOne hGrowth hP2 Q alpha
  have hDiagB := akhcSq_integrable_blockMatEntry_sq_diag_general hnu P L gamma H D m2 PsiS KPsiS
    pPsiS hKPsiS hpPsiS hPsiSOne hGrowth hP2 Q beta
  have hmeasPow : Measurable (fun omega => (blockMatEntry
      (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField) alpha beta) ^ 2) :=
    (measurable_blockMatEntry_coarseBlockMatrix hnu L Q alpha beta).pow_const 2
  refine Integrable.mono' (hDiagA.add hDiagB) hmeasPow.aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  set a : ℝ := blockMatEntry
    (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField) alpha alpha
  set b : ℝ := blockMatEntry
    (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField) beta beta
  set e : ℝ := blockMatEntry
    (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField) alpha beta
  have h1 : |e| ≤ (a + b) / 2 :=
    abs_blockMatEntry_le_of_isSymmetricBlockMat
      (isSymmetricBlockMat_coarseBlockMatrix_coefficientCutoff hnu omega L Q)
      (zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff hnu omega L Q) alpha beta
  have h2 : e ^ 2 ≤ ((a + b) / 2) ^ 2 := by
    have habs := sq_abs e
    rw [← habs]
    exact pow_le_pow_left₀ (abs_nonneg e) h1 2
  have h3 : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by nlinarith only [sq_nonneg (a - b)]
  have h4 : (a ^ 2 + b ^ 2) / 2 ≤ a ^ 2 + b ^ 2 := by nlinarith only [sq_nonneg a, sq_nonneg b]
  linarith only [h2, h3, h4]

/-! ## Target 1: the square-integrable version of package A1 -/

/-- **Target 1.** Every entry of the coarse block matrix `bfA_L(Q)` of the
infrared cutoff field is **square** `P`-integrable, at every triadic cube `Q`
and every pair of block coordinates, under `0 < nu` and the (P2') clause of
the root, copied verbatim from
`SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`.
Same hypothesis list as A1's
`akhc_integrable_blockMatEntry_of_P2`; no J3, no `ShellLawPrefix`/`J2`/`J4`. -/
theorem akhcSq_integrable_blockMatEntrySq_of_P2
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
        (fun omega => (Homogenization.blockMatEntry
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
          alpha beta) ^ 2) P.toMeasure := by
  intro Q alpha beta
  exact akhcSq_integrable_blockMatEntry_sq_general hnu P L gamma H D m2 PsiS KPsiS pPsiS
    hKPsiS hpPsiS hPsiSOne hGrowth hP2 Q alpha beta

/-! ## Target 2: `hIntFluct`

The remaining pieces are general facts about `Matrix.toEuclideanCLM`, not tied
to (P2') at all, mirroring `CoarseGraining`'s own (private)
`Homogenization.Book.Ch05.Section52.norm_toEuclideanCLM_le_sum_abs_entries`/
`norm_toEuclideanCLM_sq_integrable_of_entry_memLp_two`
(`Book/Ch05/Theorems/Section52/P4Integrability.lean`), re-derived under new
names since those are private to their file. -/

/-- The Euclidean operator norm of a matrix is bounded by `card ι` times the
sum of the absolute values of its entries. -/
private theorem akhcSq_norm_toEuclideanCLM_le_sum_abs_entries
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M‖ ≤
      (Fintype.card ι : ℝ) * ∑ i : ι, ∑ j : ι, |M i j| := by
  classical
  let S : ℝ := ∑ i : ι, ∑ j : ι, |M i j|
  have hS_nonneg : 0 ≤ S :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Nat.cast_nonneg _) hS_nonneg) ?_
  intro x
  have hcoord : ∀ i : ι,
      ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x).ofLp i‖ ≤ S * ‖x‖ := by
    intro i
    calc
      ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x).ofLp i‖
          = |∑ j : ι, M i j * x.ofLp j| := by
            simp [Real.norm_eq_abs, Matrix.mulVec, dotProduct]
      _ ≤ ∑ j : ι, |M i j * x.ofLp j| :=
            Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j => M i j * x.ofLp j)
      _ = ∑ j : ι, |M i j| * ‖x.ofLp j‖ := by simp [abs_mul, Real.norm_eq_abs]
      _ ≤ ∑ j : ι, |M i j| * ‖x‖ :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) (abs_nonneg _)
      _ = (∑ j : ι, |M i j|) * ‖x‖ := by rw [Finset.sum_mul]
      _ ≤ S * ‖x‖ :=
            mul_le_mul_of_nonneg_right
              (Finset.single_le_sum
                (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg (M k j))
                (Finset.mem_univ i))
              (norm_nonneg x)
  have hnorm_sq : ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x‖ ^ 2 ≤
      (((Fintype.card ι : ℝ) * S) * ‖x‖) ^ 2 := by
    calc
      ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x‖ ^ 2
          = ∑ i : ι, ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x).ofLp i‖ ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq]
      _ ≤ ∑ i : ι, (S * ‖x‖) ^ 2 :=
            Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
      _ ≤ (∑ _i : ι, S * ‖x‖) ^ 2 :=
            Finset.sum_sq_le_sq_sum_of_nonneg
              (fun _ _ => mul_nonneg hS_nonneg (norm_nonneg x))
      _ = (((Fintype.card ι : ℝ) * S) * ‖x‖) ^ 2 := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hS_nonneg) (norm_nonneg x))).mp hnorm_sq

/-- `Matrix.toEuclideanCLM` on `FullBlockMat d`, repackaged as a plain
(finite-dimensional, hence continuous) linear map, for a measurability
argument. -/
private def akhcSq_toEuclideanCLMLinearMap {d : ℕ} [NeZero d] :
    FullBlockMat d →ₗ[ℝ] (EuclideanSpace ℝ (BlockCoord d) →L[ℝ] EuclideanSpace ℝ (BlockCoord d)) where
  toFun := fun M => Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M
  map_add' := fun A B => map_add (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)) A B
  map_smul' := fun r A => map_smul (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)) r A

/-- **The squared Euclidean operator norm of a random `FullBlockMat d`-valued
observable is integrable, given every entry is square-integrable.** General
fact (no (P2') content), via `memLp_finsetSum` and
`akhcSq_norm_toEuclideanCLM_le_sum_abs_entries`. -/
private theorem akhcSq_norm_toEuclideanCLM_sq_integrable_of_entry_memLp_two
    {d : ℕ} [NeZero d]
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} {Z : Ω → FullBlockMat d}
    (hZ_aemeas : AEMeasurable Z mu)
    (hZ_entry : ∀ alpha beta : BlockCoord d, MemLp (fun a => Z a alpha beta) (2 : ENNReal) mu) :
    Integrable (fun a => ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (Z a)‖ ^ 2) mu := by
  classical
  set S : Ω → ℝ := fun a => ∑ alpha : BlockCoord d, ∑ beta : BlockCoord d, |Z a alpha beta|
    with hS_def
  have hS_mem : MemLp S (2 : ENNReal) mu := by
    rw [hS_def]
    refine memLp_finsetSum _ fun alpha _ha => memLp_finsetSum _ fun beta _hb => ?_
    simpa [Real.norm_eq_abs] using (hZ_entry alpha beta).norm
  have hS_sq_int : Integrable (fun a => S a ^ 2) mu := by
    simpa [Real.norm_eq_abs] using hS_mem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hCS_sq_int : Integrable (fun a => ((Fintype.card (BlockCoord d) : ℝ) * S a) ^ 2) mu := by
    have heq : (fun a => ((Fintype.card (BlockCoord d) : ℝ) * S a) ^ 2) =
        fun a => (Fintype.card (BlockCoord d) : ℝ) ^ 2 * S a ^ 2 := by funext a; ring
    rw [heq]
    exact hS_sq_int.const_mul _
  have hcont : Continuous (fun M : FullBlockMat d => ‖akhcSq_toEuclideanCLMLinearMap M‖) :=
    continuous_norm.comp (akhcSq_toEuclideanCLMLinearMap (d := d)).continuous_of_finiteDimensional
  have hmeasPow : AEStronglyMeasurable
      (fun a => ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (Z a)‖ ^ 2) mu :=
    ((hcont.measurable.comp_aemeasurable hZ_aemeas).pow_const 2).aestronglyMeasurable
  refine Integrable.mono' hCS_sq_int hmeasPow (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (akhcSq_norm_toEuclideanCLM_le_sum_abs_entries (Z a)) 2

/-! ## Target 1, pushed to the coefficient carrier -/

/-- **Target 1, pushed forward to `cutoffLaw` via `integrable_map_measure`.**
Mirrors `akhc_integrable_blockMatEntry_cutoffLaw_of_P2`
(`AKHC61/Carrier/ScalarBlocks.lean`), squared. -/
private theorem akhcSq_integrable_blockMatEntrySq_cutoffLaw_of_P2
    [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
    (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
    (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
    (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
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
    Integrable (fun a : RegCoeffField d =>
      (blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) alpha beta) ^ 2)
      (cutoffLaw (d := d) nu L P) := by
  rw [cutoffLaw]
  have hmeas := (aemeasurable_blockMatEntry_cutoffLaw hnu L P Q alpha beta).pow_const 2
  refine (integrable_map_measure hmeas.aestronglyMeasurable
    (measurable_coefficientCutoff nu L).aemeasurable).2 ?_
  exact akhcSq_integrable_blockMatEntry_sq_general hnu P L gamma H D m2 PsiS KPsiS pPsiS
    hKPsiS hpPsiS hPsiSOne hGrowth hP2 Q alpha beta

/-- Entries of `D * (toFullBlockMat A - toFullBlockMat Abar) * D` for a
diagonal `D`, in terms of `blockMatEntry`. -/
private theorem akhcSq_fluctuationMatrix_entry
    [NeZero d] (Dg : BlockCoord d → ℝ) (A Abar : BlockMat d) (alpha beta : BlockCoord d) :
    (Matrix.diagonal Dg * (toFullBlockMat A - toFullBlockMat Abar) * Matrix.diagonal Dg)
        alpha beta =
      Dg alpha * (blockMatEntry A alpha beta - blockMatEntry Abar alpha beta) * Dg beta := by
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply, toFullBlockMat_eq_blockMatEntry]

/-- **Each entry of the `Ahom(cu_m)`-normalized full-block fluctuation
matrix is square-`cutoffLaw`-integrable.** `MemLp` of the (P2')-integrable
entry (`akhcSq_integrable_blockMatEntrySq_cutoffLaw_of_P2`, converted via
`memLp_two_iff_integrable_sq`), centered at the deterministic constant
`Abar_{αβ}` and scaled by the deterministic constants
`D_α, D_β := akhcFullBlockInvSqrtDiag`. -/
private theorem akhcSq_memLp_fluctuationMatrixEntry_cutoffLaw_of_P2
    [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
    (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
    (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
    (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
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
    (m : ℤ) (R : TriadicCube d) (alpha beta : BlockCoord d) :
    MemLp (fun a : RegCoeffField d =>
      SuperdiffusionCLT.AKHC61.Response.akhcFullBlockInvSqrtDiag nu L P m alpha *
        (blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta -
          blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d m))) alpha beta) *
        SuperdiffusionCLT.AKHC61.Response.akhcFullBlockInvSqrtDiag nu L P m beta)
      (2 : ENNReal) (cutoffLaw (d := d) nu L P) := by
  have hentrySq := akhcSq_integrable_blockMatEntrySq_cutoffLaw_of_P2 hnu P L gamma H D m2 PsiS
    KPsiS pPsiS hKPsiS hpPsiS hPsiSOne hGrowth hP2 R alpha beta
  have hentryMeasAE := aemeasurable_blockMatEntry_cutoffLaw hnu L P R alpha beta
  have hentryMemLp : MemLp (fun a : RegCoeffField d =>
      blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta)
      (2 : ENNReal) (cutoffLaw (d := d) nu L P) := by
    rw [memLp_two_iff_integrable_sq hentryMeasAE.aestronglyMeasurable]
    exact hentrySq
  have hconstMemLp : MemLp (fun _ : RegCoeffField d =>
      blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d m))) alpha beta)
      (2 : ENNReal) (cutoffLaw (d := d) nu L P) := memLp_const _
  have hsubMemLp := hentryMemLp.sub hconstMemLp
  have hscaledMemLp := hsubMemLp.const_mul
    (SuperdiffusionCLT.AKHC61.Response.akhcFullBlockInvSqrtDiag nu L P m alpha *
      SuperdiffusionCLT.AKHC61.Response.akhcFullBlockInvSqrtDiag nu L P m beta)
  have heq : (fun a : RegCoeffField d =>
      (SuperdiffusionCLT.AKHC61.Response.akhcFullBlockInvSqrtDiag nu L P m alpha *
        SuperdiffusionCLT.AKHC61.Response.akhcFullBlockInvSqrtDiag nu L P m beta) *
        (blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta -
          blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d m))) alpha beta)) =ᵐ[
      cutoffLaw (d := d) nu L P]
      (fun a : RegCoeffField d =>
        SuperdiffusionCLT.AKHC61.Response.akhcFullBlockInvSqrtDiag nu L P m alpha *
          (blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta -
            blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d m))) alpha beta) *
          SuperdiffusionCLT.AKHC61.Response.akhcFullBlockInvSqrtDiag nu L P m beta) :=
    Filter.Eventually.of_forall fun a => by ring
  exact MemLp.ae_eq heq hscaledMemLp

/-! ## Target 2: `hIntFluct` -/

/-- **Target 2.** The integrability hypothesis `hIntFluct` of the expectation estimates of
`AKHC61/Response/CoarseAveragesC.lean`, for a fixed `m R`:
`akhcFullBlockNormalizedFluctuationAtScale nu L P m R` is `cutoffLaw`-integrable.
Route: its entries are `Dg_α (entry_αβ - Abar_αβ) Dg_β`
(`akhcSq_fluctuationMatrix_entry`), each square-`cutoffLaw`-integrable
(`akhcSq_memLp_fluctuationMatrixEntry_cutoffLaw_of_P2`, target 1 pushed
forward), so `akhcSq_norm_toEuclideanCLM_sq_integrable_of_entry_memLp_two`
applies. -/
theorem akhcSq_integrable_fullBlockNormalizedFluctuationAtScale_of_P2
    [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
    (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
    (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
    (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
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
    (m : ℤ) (R : TriadicCube d) :
    Integrable (fun a : RegCoeffField d =>
      SuperdiffusionCLT.AKHC61.Response.akhcFullBlockNormalizedFluctuationAtScale
        nu L P m R a) (cutoffLaw (d := d) nu L P) := by
  set Dg : BlockCoord d → ℝ :=
    SuperdiffusionCLT.AKHC61.Response.akhcFullBlockInvSqrtDiag nu L P m with hDg_def
  set Abar : BlockMat d :=
    SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
      (cubeSet (originCube d m)) with hAbar_def
  set Z : RegCoeffField d → FullBlockMat d := fun a =>
    Matrix.diagonal Dg * (toFullBlockMat (coarseBlockMatrix (cubeSet R) a.toFun) -
      toFullBlockMat Abar) * Matrix.diagonal Dg with hZ_def
  have hZ_entry : ∀ alpha beta : BlockCoord d,
      MemLp (fun a : RegCoeffField d => Z a alpha beta) (2 : ENNReal)
        (cutoffLaw (d := d) nu L P) := by
    intro alpha beta
    have hform : (fun a : RegCoeffField d => Z a alpha beta) =
        fun a : RegCoeffField d => Dg alpha *
          (blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta -
            blockMatEntry Abar alpha beta) * Dg beta := by
      funext a
      rw [hZ_def]
      exact akhcSq_fluctuationMatrix_entry Dg (coarseBlockMatrix (cubeSet R) a.toFun) Abar
        alpha beta
    rw [hform, hAbar_def]
    exact akhcSq_memLp_fluctuationMatrixEntry_cutoffLaw_of_P2 hnu P L gamma H D m2 PsiS KPsiS
      pPsiS hKPsiS hpPsiS hPsiSOne hGrowth hP2 m R alpha beta
  have hZ_aemeas : AEMeasurable Z (cutoffLaw (d := d) nu L P) := by
    refine AEMeasurable.of_eval fun alpha => AEMeasurable.of_eval fun beta => ?_
    have hform : (fun a : RegCoeffField d => Z a alpha beta) =
        fun a : RegCoeffField d => Dg alpha *
          (blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta -
            blockMatEntry Abar alpha beta) * Dg beta := by
      funext a
      rw [hZ_def]
      exact akhcSq_fluctuationMatrix_entry Dg (coarseBlockMatrix (cubeSet R) a.toFun) Abar
        alpha beta
    rw [hform]
    exact (((aemeasurable_blockMatEntry_cutoffLaw hnu L P R alpha beta).sub
      aemeasurable_const).const_mul (Dg alpha)).mul_const (Dg beta)
  have hInt := akhcSq_norm_toEuclideanCLM_sq_integrable_of_entry_memLp_two hZ_aemeas hZ_entry
  refine hInt.congr (Filter.Eventually.of_forall fun a => ?_)
  rfl

end

end SuperdiffusionCLT.AKHC61.Carrier
