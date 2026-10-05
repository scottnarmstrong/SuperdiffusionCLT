/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.EnvelopeDomain
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolumeBelow
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction

/-!
# The three ellipticity assertions for `bfA_m`

Lemma `l.bfAm.ellip` states three things about the infrared cutoff
`a_m = nu Id + k_m`, all normalized by the deterministic envelope `bfE_m` of
`e.Enaught.mixing`:

* `e.Enaught.vs.A.and.Ahom`: for every bounded domain `U`, the
  rescaled coarse block matrix `bfE_m^{-1/2} bfA_m(U) bfE_m^{-1/2}` has
  Euclidean operator norm `O_{Γ₁}(1)`;
* the second assertion: `bfE_m^{-1/2} bfAhom_m bfE_m^{-1/2} ≤
  bfE_m^{-1/2} bfAhom_m(cu_n) bfE_m^{-1/2} ≤ I_{2d}` for every `n`;
* `e.Smgamma.integ` and `e.bfAm.ellip`: for every
  `gamma ∈ (0,1)` a random minimal scale with a Γ_γ tail at amplitude
  `C exp(C |log gamma| / gamma) 3^m` above which every sub-cube of `cu_n`
  satisfies `3^{-gamma(n-l)} bfE_m^{-1/2} bfA_m(z + cu_l) bfE_m^{-1/2} ≤
  2 I_{2d}`.

The envelope, its constant, the normalization `envelopeRescale` and the
quadratic-form bounds behind them are `Section2/Annealed/Envelope.lean`; the
sandwich of the second assertion is
`Section2/Annealed/InfiniteVolumeBelow.lean`; the passage of the first
assertion to a general bounded domain is
`Section2/Annealed/EnvelopeDomain.lean`.

## The two inputs taken as hypotheses

Two ingredients of the printed lemma are taken in this module as explicit hypotheses, named at
the point of use.

* **The measurability of `Mu` on a general domain.** `CoarseGraining` makes
  `omega ↦ Mu U P a(omega)` measurable through the quantitative a.e.-ellipticity
  slices, and that engine is indexed by triadic cubes
  (`Section2/Annealed/Measurability.lean`, `measurable_Mu_cubeSet_of_source`).
  Everything else in the measurability of the printed observable is supplied
  here: `measurable_blockMatrixOperatorNorm_of_entries` and
  `measurable_blockMatEntry_envelopeRescale` reduce the observable to the four
  blocks, and `measurable_blockMatEntry_coarseBlockMatrix_of_measurable_Mu`
  reduces those to `Mu` on `U`.
* **The minimal scale of `e.Smgamma.integ`.** The printed proof obtains it from
  the local square bound `e.km.square.bound` by a union bound over all scales `l ≤ n` and all
  `3^{d(n-l)}` sub-cubes of `cu_n`. That estimate is assumed here.
  The matrix form of `e.bfAm.ellip` reduces to the scalar statement about the
  random factor `envelopeRatio` of `Envelope.lean`, which is exactly what the
  union bound produces.

## Main results

* `isBigOWith_gammaSigma_envelopeRatioOn`,
  `isBigOWith_gammaSigma_blockMatrixOperatorNorm_envelopeRescale`: the tail half
  of the first assertion, for every bounded domain.
* `measurable_blockMatrixOperatorNorm_envelopeRescale_of_measurable_Mu`: its
  measurability half from the measurability of `Mu` on the domain.
* `blockMatLoewnerLE_envelopeRescale_annealed_sandwich`: the second assertion.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The Γ₁ tail and the first assertion -/

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- `e.km.Ltwo.size` on a general set, read at the scale of the envelope
constant. -/
theorem isBigOWith_gammaSigma_volumeAverage_sq_envelopeScaleOn
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m : ℕ) {U : Set (Vec d)}
    (hU0 : MeasureTheory.volume U ≠ 0) (hUtop : MeasureTheory.volume U ≠ ⊤) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega => volumeAverage U
        (fun x => Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2))
      (cutoffEnvelopeConst d * max 1 (m : ℝ)) := by
  refine (isBigOWith_gammaSigma_volumeAverage_sq_streamCutoff_max hPrefix hJ2 hJ3 hJ4 m
    hU0 hUtop).mono_scale ?_
  have hmax : (0 : ℝ) ≤ max 1 (m : ℝ) := le_trans zero_le_one (le_max_left _ _)
  exact mul_le_mul_of_nonneg_right
    (two_mul_cutoffL2Const_le_cutoffEnvelopeConst d) hmax

/-- The random factor of the first assertion has a Γ₁ tail at amplitude
`1` on every set of positive finite volume. -/
theorem isBigOWith_gammaSigma_envelopeRatioOn
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m : ℕ) {U : Set (Vec d)}
    (hU0 : MeasureTheory.volume U ≠ 0) (hUtop : MeasureTheory.volume U ≠ ⊤) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega => envelopeRatioOn m U omega) 1 := by
  have hZ := isBigOWith_gammaSigma_volumeAverage_sq_envelopeScaleOn
    hPrefix hJ2 hJ3 hJ4 m hU0 hUtop
  intro t ht
  refine (measureReal_mono ?_).trans (hZ ht)
  intro omega hom
  have hlt : (1 : ℝ) * t < envelopeRatioOn m U omega := hom
  rw [one_mul] at hlt
  rcases lt_max_iff.1 hlt with h1 | h2
  · exact absurd ht (not_le.2 h1)
  · have hmul := (lt_div_iff₀ (cutoffEnvelopeScale_pos d m)).1 h2
    show cutoffEnvelopeConst d * max 1 (m : ℝ) * t <
      volumeAverage U
        (fun x => Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)
    linarith only [hmul]

/-- **The tail half of the first assertion**, `e.Enaught.vs.A.and.Ahom`, for every bounded
domain. -/
theorem isBigOWith_gammaSigma_blockMatrixOperatorNorm_envelopeRescale
    {nu : ℝ} (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m : ℕ)
    (U : Book.Ch02.Domain d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d =>
        Carriers.blockMatrixOperatorNorm
          (envelopeRescale d nu m
            (coarseBlockMatrix (U : Set (Vec d))
              (coefficientCutoff nu omega m).toCoeffField)))
      1 :=
  (isBigOWith_gammaSigma_envelopeRatioOn hPrefix hJ2 hJ3 hJ4 m
      (volume_domain_ne_zero U) (volume_domain_ne_top U)).of_le
    fun omega => blockMatrixOperatorNorm_envelopeRescale_coarseBlockMatrix_le U hnu omega m

/-! ## The second assertion -/

/-- **The second assertion of `l.bfAm.ellip`**:
`bfE_m^{-1/2} bfAhom_m bfE_m^{-1/2} ≤ bfE_m^{-1/2} bfAhom_m(cu_n) bfE_m^{-1/2}
≤ I_{2d}`. -/
theorem blockMatLoewnerLE_envelopeRescale_annealed_sandwich [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m n : ℕ) :
    BlockMatLoewnerLE
        (envelopeRescale d nu m (Carriers.annealedBlockMatInfinite nu m P))
        (envelopeRescale d nu m
          (annealedBlockMatrix nu m P (cubeSet (originCube d (n : ℤ))))) ∧
      BlockMatLoewnerLE
        (envelopeRescale d nu m
          (annealedBlockMatrix nu m P (cubeSet (originCube d (n : ℤ)))))
        (Book.Ch02.blockIdentity d) :=
  ⟨blockMatLoewnerLE_envelopeRescale_annealedBlockMatInfinite_originCube hnu m
      hPrefix hJ2 hJ3 hJ4 n,
    blockMatLoewnerLE_envelopeRescale_annealedBlockMatrix hnu m
      (originCube d (n : ℤ)) hPrefix hJ2 hJ3 hJ4⟩

/-! ## Measurability of the printed observable

The observable of the first assertion is `omega ↦
|bfE_m^{-1/2} bfA_m(U) bfE_m^{-1/2}|`. Its measurability reduces, in two
unconditional steps, to the measurability of `Homogenization.Mu` on `U`:
the Euclidean operator norm is a continuous function of the `2d`-by-`2d`
entries, the entries of the rescaled matrix are fixed multiples of the entries
of the coarse block matrix, and those are polarization combinations of `Mu`. -/

private def euclideanBlockCLMLinear (d : ℕ) :
    FullBlockMat d →ₗ[ℝ]
      (EuclideanSpace ℝ (BlockCoord d) →L[ℝ] EuclideanSpace ℝ (BlockCoord d)) where
  toFun := fun M => Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M
  map_add' := fun M N => map_add _ M N
  map_smul' := fun c M => map_smul _ c M

private theorem continuousBlockOperatorNorm (d : ℕ) :
    Continuous
      (fun M : FullBlockMat d =>
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖) :=
  continuous_norm.comp (euclideanBlockCLMLinear d).continuous_of_finiteDimensional

/-- The Euclidean operator norm of a doubled block matrix is measurable as soon
as its `2d`-by-`2d` entries are. -/
theorem measurable_blockMatrixOperatorNorm_of_entries {Omega : Type*}
    [MeasurableSpace Omega] {F : Omega → BlockMat d}
    (hF : ∀ alpha beta : BlockCoord d,
      Measurable fun w => blockMatEntry (F w) alpha beta) :
    Measurable fun w => Carriers.blockMatrixOperatorNorm (F w) := by
  have hmat : Measurable fun w => toFullBlockMat (F w) :=
    Measurable.of_eval fun alpha => Measurable.of_eval fun beta => hF alpha beta
  exact (continuousBlockOperatorNorm d).measurable.comp hmat

/-- Each entry of the rescaled matrix is a fixed multiple of the corresponding
entry of the original one. -/
theorem measurable_blockMatEntry_envelopeRescale {Omega : Type*}
    [MeasurableSpace Omega] {F : Omega → BlockMat d}
    (hF : ∀ alpha beta : BlockCoord d,
      Measurable fun w => blockMatEntry (F w) alpha beta)
    (nu : ℝ) (m : ℕ) (alpha beta : BlockCoord d) :
    Measurable fun w => blockMatEntry (envelopeRescale d nu m (F w)) alpha beta := by
  have hup := (Real.sqrt (envelopeUpperScalar d nu m))⁻¹
  cases alpha with
  | inl i =>
    cases beta with
    | inl j =>
      have hEq : (fun w => blockMatEntry (envelopeRescale d nu m (F w))
            (Sum.inl i) (Sum.inl j)) =
          fun w => ((Real.sqrt (envelopeUpperScalar d nu m))⁻¹ *
            (Real.sqrt (envelopeUpperScalar d nu m))⁻¹) *
              blockMatEntry (F w) (Sum.inl i) (Sum.inl j) := by
        funext w
        rw [envelopeRescale_eq]
        rfl
      rw [hEq]
      exact (hF _ _).const_mul _
    | inr j =>
      have hEq : (fun w => blockMatEntry (envelopeRescale d nu m (F w))
            (Sum.inl i) (Sum.inr j)) =
          fun w => ((Real.sqrt (envelopeUpperScalar d nu m))⁻¹ *
            (Real.sqrt (envelopeLowerScalar d nu))⁻¹) *
              blockMatEntry (F w) (Sum.inl i) (Sum.inr j) := by
        funext w
        rw [envelopeRescale_eq]
        rfl
      rw [hEq]
      exact (hF _ _).const_mul _
  | inr i =>
    cases beta with
    | inl j =>
      have hEq : (fun w => blockMatEntry (envelopeRescale d nu m (F w))
            (Sum.inr i) (Sum.inl j)) =
          fun w => ((Real.sqrt (envelopeUpperScalar d nu m))⁻¹ *
            (Real.sqrt (envelopeLowerScalar d nu))⁻¹) *
              blockMatEntry (F w) (Sum.inr i) (Sum.inl j) := by
        funext w
        rw [envelopeRescale_eq]
        rfl
      rw [hEq]
      exact (hF _ _).const_mul _
    | inr j =>
      have hEq : (fun w => blockMatEntry (envelopeRescale d nu m (F w))
            (Sum.inr i) (Sum.inr j)) =
          fun w => ((Real.sqrt (envelopeLowerScalar d nu))⁻¹ *
            (Real.sqrt (envelopeLowerScalar d nu))⁻¹) *
              blockMatEntry (F w) (Sum.inr i) (Sum.inr j) := by
        funext w
        rw [envelopeRescale_eq]
        rfl
      rw [hEq]
      exact (hF _ _).const_mul _

/-- The `2d`-by-`2d` entries of the coarse block matrix are polarization
combinations of `Homogenization.Mu`, hence measurable as soon as `Mu` is. -/
theorem measurable_blockMatEntry_coarseBlockMatrix_of_measurable_Mu
    {Omega : Type*} [MeasurableSpace Omega] {a : Omega → CoeffField d}
    {U : Set (Vec d)} (hMu : ∀ P0 : BlockVec d, Measurable fun w => Mu U P0 (a w))
    (alpha beta : BlockCoord d) :
    Measurable fun w => blockMatEntry (coarseBlockMatrix U (a w)) alpha beta := by
  classical
  cases alpha with
  | inl i =>
    cases beta with
    | inl j =>
      by_cases hij : i = j
      · subst hij
        have hEq : (fun w => blockMatEntry (coarseBlockMatrix U (a w))
              (Sum.inl i) (Sum.inl i)) =
            fun w => 2 * Mu U (Pi.single i 1, 0) (a w) := by
          funext w
          show (coarseBlockMatrix U (a w)).upperLeft i i = _
          rw [coarseBlockMatrix_upperLeft_apply, ite_eq_left rfl]
        rw [hEq]
        exact (hMu _).const_mul _
      · have hEq : (fun w => blockMatEntry (coarseBlockMatrix U (a w))
              (Sum.inl i) (Sum.inl j)) =
            fun w => Mu U ((Pi.single i 1, 0) + (Pi.single j 1, 0)) (a w)
              - Mu U (Pi.single i 1, 0) (a w) - Mu U (Pi.single j 1, 0) (a w) := by
          funext w
          show (coarseBlockMatrix U (a w)).upperLeft i j = _
          rw [coarseBlockMatrix_upperLeft_apply, ite_eq_right hij]
        rw [hEq]
        exact ((hMu _).sub (hMu _)).sub (hMu _)
    | inr j =>
      have hEq : (fun w => blockMatEntry (coarseBlockMatrix U (a w))
            (Sum.inl i) (Sum.inr j)) =
          fun w => Mu U ((Pi.single i 1, 0) + (0, Pi.single j 1)) (a w)
            - Mu U (Pi.single i 1, 0) (a w) - Mu U (0, Pi.single j 1) (a w) := by
        funext w
        show (coarseBlockMatrix U (a w)).upperRight i j = _
        rw [coarseBlockMatrix_upperRight_apply]
      rw [hEq]
      exact ((hMu _).sub (hMu _)).sub (hMu _)
  | inr i =>
    cases beta with
    | inl j =>
      have hEq : (fun w => blockMatEntry (coarseBlockMatrix U (a w))
            (Sum.inr i) (Sum.inl j)) =
          fun w => Mu U ((0, Pi.single i 1) + (Pi.single j 1, 0)) (a w)
            - Mu U (0, Pi.single i 1) (a w) - Mu U (Pi.single j 1, 0) (a w) := by
        funext w
        show (coarseBlockMatrix U (a w)).lowerLeft i j = _
        rw [coarseBlockMatrix_lowerLeft_apply]
      rw [hEq]
      exact ((hMu _).sub (hMu _)).sub (hMu _)
    | inr j =>
      by_cases hij : i = j
      · subst hij
        have hEq : (fun w => blockMatEntry (coarseBlockMatrix U (a w))
              (Sum.inr i) (Sum.inr i)) =
            fun w => 2 * Mu U (0, Pi.single i 1) (a w) := by
          funext w
          show (coarseBlockMatrix U (a w)).lowerRight i i = _
          rw [coarseBlockMatrix_lowerRight_apply, ite_eq_left rfl]
        rw [hEq]
        exact (hMu _).const_mul _
      · have hEq : (fun w => blockMatEntry (coarseBlockMatrix U (a w))
              (Sum.inr i) (Sum.inr j)) =
            fun w => Mu U ((0, Pi.single i 1) + (0, Pi.single j 1)) (a w)
              - Mu U (0, Pi.single i 1) (a w) - Mu U (0, Pi.single j 1) (a w) := by
          funext w
          show (coarseBlockMatrix U (a w)).lowerRight i j = _
          rw [coarseBlockMatrix_lowerRight_apply, ite_eq_right hij]
        rw [hEq]
        exact ((hMu _).sub (hMu _)).sub (hMu _)

/-- **The measurability half of the first assertion**, from the measurability
of `Homogenization.Mu` on the domain. -/
theorem measurable_blockMatrixOperatorNorm_envelopeRescale_of_measurable_Mu
    {nu : ℝ} (m : ℕ) {U : Set (Vec d)}
    (hMu : ∀ P0 : BlockVec d,
      Measurable fun omega : ShellSeq d =>
        Mu U P0 (coefficientCutoff nu omega m).toCoeffField) :
    Measurable fun omega : ShellSeq d =>
      Carriers.blockMatrixOperatorNorm
        (envelopeRescale d nu m
          (coarseBlockMatrix U (coefficientCutoff nu omega m).toCoeffField)) :=
  measurable_blockMatrixOperatorNorm_of_entries
    (measurable_blockMatEntry_envelopeRescale
      (measurable_blockMatEntry_coarseBlockMatrix_of_measurable_Mu hMu) nu m)

/-! ## The third assertion from the scalar minimal-scale bound -/

private theorem blockVecDotSmulBlockIdentityD (c : ℝ) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (c • Book.Ch02.blockIdentity d) X) =
      c * blockVecDot X X := by
  rw [blockMatVecMul_blockSMul, blockVecDot_smul_right,
    Carriers.blockMatVecMul_blockIdentity]

/-- Scaling a Loewner bound against a multiple of the doubled identity. -/
theorem blockMatLoewnerLE_two_smul_blockIdentity_of_mul_le {A : BlockMat d}
    {s c : ℝ} (hs : 0 ≤ s)
    (hA : BlockMatLoewnerLE A (c • Book.Ch02.blockIdentity d)) (hsc : s * c ≤ 2) :
    BlockMatLoewnerLE (s • A) ((2 : ℝ) • Book.Ch02.blockIdentity d) := by
  intro X
  have hX : 0 ≤ blockVecDot X X := Carriers.blockVecDot_self_nonneg X
  have hAX := hA X
  rw [blockVecDotSmulBlockIdentityD] at hAX
  have hquad : blockVecDot X (blockMatVecMul A X) ≤ c * blockVecDot X X := by
    linarith only [hAX]
  have hleft : blockVecDot X (blockMatVecMul (s • A) X) =
      s * blockVecDot X (blockMatVecMul A X) := by
    rw [blockMatVecMul_blockSMul, blockVecDot_smul_right]
  have hstep : s * blockVecDot X (blockMatVecMul A X) ≤ s * (c * blockVecDot X X) :=
    mul_le_mul_of_nonneg_left hquad hs
  have hfinal : s * (c * blockVecDot X X) ≤ 2 * blockVecDot X X := by
    have hmul := mul_le_mul_of_nonneg_right hsc hX
    calc s * (c * blockVecDot X X) = s * c * blockVecDot X X := by ring
      _ ≤ 2 * blockVecDot X X := hmul
  show (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (s • A) X) ≤
    (1 / 2 : ℝ) *
      blockVecDot X (blockMatVecMul ((2 : ℝ) • Book.Ch02.blockIdentity d) X)
  rw [blockVecDotSmulBlockIdentityD, hleft]
  linarith only [hstep, hfinal]

/-! ## The three assertions assembled -/

end

end SuperdiffusionCLT.Section2.Annealed
