/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Envelope
public import SuperdiffusionCLT.Section2.Carriers.BlockOperatorNorm
public import SuperdiffusionCLT.Section2.Cutoff.CenteredCoeffOn

/-!
# The rescaled coarse block matrix of the cutoff on a general bounded domain

Lemma `l.bfAm.ellip` states its first assertion `e.Enaught.vs.A.and.Ahom` for **every bounded
domain** `U`:

`|bfE_m^{-1/2} bfA_m(U) bfE_m^{-1/2}| ≤ O_{Gamma_1}(1)`.

`Section2/Annealed/Envelope.lean` proves the deterministic half of it on a
triadic cube, because the passage from the raw carrier
`Homogenization.coarseBlockMatrix (U : Set (Vec d))` to the Chapter 2 pair
`Book.Ch02.Domain d`, `Book.Ch02.CoeffOn U`, where the variational bound
`e.CG.bounds.2` lives, is available there only for cubes. This module supplies
that passage on a general domain and carries the deterministic half of the
first assertion there.

## The passage

A coarse block matrix is unique
(`Homogenization.eq_coarseBlockMatrix_of_isCoarseBlockMatrix`), and the
Chapter 2 coarse block matrix of a `CoeffOn U` satisfies the characterizing
quadratic identity for `Homogenization.Mu` by the two Chapter 2 theorems
`doubledMu_eq_Mu` and the quadratic formula of `doubledMuTheory`. That gives
`coarseBlockMatrix_domain_eq_ch02` for an arbitrary Chapter 2 domain. The
Chapter 2 coefficient object of the cutoff field on such a domain is
`cutoffDomainCoeffOn`, built from the entry bound of
`exists_entryBound_domain`: every shell of the carrier stores a
continuous value map, so `a_m(omega)` is bounded on a bounded domain for
every shell sequence, and its symmetric part is the constant `nu Id`.

## Main results

* `coarseBlockMatrix_domain_eq_ch02`, `cutoffDomainCoeffOn`,
  `coarseBlockMatrix_domain_coefficientCutoff_eq_ch02`: the passage.
* `blockVecDot_coarseBlockMatrix_coefficientCutoff_domain_le`: the first
  display of the printed proof, on a general domain.
* `cutoffEnvelopeScale_pos`, `envelopeRatioOn`: the random factor of `e.Enaught.vs.A.and.Ahom` on a
  general set; on a triadic cube it is the `envelopeRatio` of `Envelope.lean`.
* `blockMatLoewnerLE_envelopeRescale_coarseBlockMatrix_domain`: the
  deterministic Loewner form of the first assertion on a general domain.
* `isSymmetricBlockMat_envelopeRescale`,
  `blockVecDot_envelopeRescale_nonneg`: the normalization preserves symmetry
  and positive semidefiniteness.
* `blockMatrixOperatorNorm_envelopeRescale_coarseBlockMatrix_le`: the Loewner
  form read as the printed Euclidean operator-norm bound.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The coarse block matrix of the cutoff field on a general domain -/

/-- On a Chapter 2 domain the raw coarse block matrix of a coefficient object
is its Chapter 2 coarse block matrix. Both are characterized by the same
quadratic identity for `Homogenization.Mu`, and a coarse block matrix is
unique. -/
theorem coarseBlockMatrix_domain_eq_ch02 (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) :
    coarseBlockMatrix (U : Set (Vec d)) a.toCoeffField =
      Book.Ch02.coarseBlockMatrix U a := by
  refine (eq_coarseBlockMatrix_of_isCoarseBlockMatrix ?_).symm
  refine ⟨Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix U a, fun P => ?_⟩
  rw [← Book.Ch02.doubledMu_eq_Mu U a P]
  exact (Book.Ch02.doubledMuTheory U a).mu_quadratic P

/-- The cutoff field is bounded on a bounded domain, with a sample-dependent
constant: every shell of the carrier stores a continuous value map. -/
theorem exists_entryBound_domain (nu : ℝ) (omega : ShellSeq d) (m : ℕ)
    (U : Book.Ch02.Domain d) :
    ∃ C : ℝ, ∀ x ∈ (U : Set (Vec d)), ∀ i j : Fin d,
      |(coefficientCutoff nu omega m).toCoeffField x i j| ≤ C := by
  classical
  set a : Vec d → Mat d := (coefficientCutoff nu omega m).toCoeffField with ha
  set g : Vec d → ℝ := fun x => ∑ i : Fin d, ∑ j : Fin d, |a x i j| with hg
  have hcoef : Continuous a :=
    Continuous.add (M := Mat d) continuous_const (continuous_streamCutoff_apply omega m)
  have hcont : Continuous g := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    refine continuous_abs.comp ?_
    exact (continuous_apply j).comp ((continuous_apply i).comp hcoef)
  have hUb : Bornology.IsBounded (U : Set (Vec d)) :=
    U.isDomain.isBoundedDomain.isBounded
  obtain ⟨C, hC⟩ := hUb.isCompact_closure.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, fun x hx i j => ?_⟩
  have hle : ‖g x‖ ≤ C := hC x (subset_closure hx)
  rw [Real.norm_eq_abs] at hle
  have hsingle : |a x i j| ≤ g x := by
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i' : Fin d => ∑ j' : Fin d, |a x i' j'|)
      (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j' : Fin d => |a x i j'|)
      (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
  exact hsingle.trans ((le_abs_self (g x)).trans hle)

/-- The Chapter 2 coefficient object of the cutoff field on a general domain,
built from the entry bound of `exists_entryBound_domain`. -/
def cutoffDomainCoeffOn (U : Book.Ch02.Domain d) {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) : Book.Ch02.CoeffOn U :=
  SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn U hnu omega m
    (Classical.choose_spec (exists_entryBound_domain nu omega m U))

/-- The coarse block matrix of the cutoff field on a domain is the Chapter 2
object attached to `cutoffDomainCoeffOn`. -/
theorem coarseBlockMatrix_domain_coefficientCutoff_eq_ch02 (U : Book.Ch02.Domain d)
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) :
    coarseBlockMatrix (U : Set (Vec d)) (coefficientCutoff nu omega m).toCoeffField =
      Book.Ch02.coarseBlockMatrix U (cutoffDomainCoeffOn U hnu omega m) :=
  coarseBlockMatrix_domain_eq_ch02 U (cutoffDomainCoeffOn U hnu omega m)

/-- The pointwise squared size of the cutoff field is integrable on a bounded
set: it is continuous and the set has compact closure. -/
theorem integrableOn_sq_streamCutoff_of_isBounded (omega : ShellSeq d) (m : ℕ)
    {U : Set (Vec d)} (hUb : Bornology.IsBounded U) :
    IntegrableOn
      (fun x => Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) U := by
  have hcont : Continuous
      (fun x : Vec d => Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) :=
    (ShellField.continuous_matrixOperatorNorm.comp
      (continuous_streamCutoff_apply omega m)).pow 2
  exact (hcont.continuousOn.integrableOn_compact hUb.isCompact_closure
    (μ := MeasureTheory.volume)).mono_set subset_closure

private theorem volumeAverageMonoD {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf0 : 0 ≤ᵐ[volumeMeasureOn U] f) (hg : IntegrableOn g U)
    (hfg : f ≤ᵐ[volumeMeasureOn U] g) :
    volumeAverage U f ≤ volumeAverage U g := by
  have hint : ∫ x in U, f x ≤ ∫ x in U, g x := integral_mono_of_nonneg hf0 hg hfg
  have hvol : (0 : ℝ) ≤ (MeasureTheory.volume U).toReal⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hint hvol
  unfold volumeAverage
  linarith only [hmul]

private theorem volumeAverageAffineD {U : Set (Vec d)}
    (hU0 : MeasureTheory.volume U ≠ 0) (hUtop : MeasureTheory.volume U ≠ ⊤)
    {Y : Vec d → ℝ} (hY : IntegrableOn Y U) (alpha beta : ℝ) :
    volumeAverage U (fun x => alpha * Y x + beta) =
      alpha * volumeAverage U Y + beta := by
  have hfin : IsFiniteMeasure (volumeMeasureOn U) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hUtop
  have hc : 0 < (MeasureTheory.volume U).toReal := ENNReal.toReal_pos hU0 hUtop
  have hconst : ∫ _x in U, beta ∂MeasureTheory.volume =
      (MeasureTheory.volume U).toReal * beta := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, measureReal_def]
  have hsplit : ∫ x in U, (alpha * Y x + beta) ∂MeasureTheory.volume =
      alpha * (∫ x in U, Y x ∂MeasureTheory.volume) +
        (MeasureTheory.volume U).toReal * beta := by
    rw [integral_add (hY.const_mul alpha) (integrable_const beta), integral_const_mul,
      hconst]
  unfold volumeAverage
  rw [hsplit]
  field_simp

theorem volume_domain_ne_zero (U : Book.Ch02.Domain d) :
    MeasureTheory.volume (U : Set (Vec d)) ≠ 0 :=
  (IsOpen.measure_pos MeasureTheory.volume U.isOpen U.nonempty).ne'

theorem volume_domain_ne_top (U : Book.Ch02.Domain d) :
    MeasureTheory.volume (U : Set (Vec d)) ≠ ⊤ :=
  volume_ne_top_of_isBounded U.isDomain.isBoundedDomain.isBounded

/-- **The first display of the printed proof**, on a general bounded domain: `(p,q) · bfA_m(U) (p,q)
≤ (nu + 2 nu⁻¹ ‖k_m‖²_{L²(U)}) |p|² + 2 nu⁻¹ |q|²`. -/
theorem blockVecDot_coarseBlockMatrix_coefficientCutoff_domain_le
    (U : Book.Ch02.Domain d) {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ)
    (p q : Vec d) :
    blockVecDot (p, q)
        (blockMatVecMul
          (coarseBlockMatrix (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField) (p, q)) ≤
      (nu + 2 * nu⁻¹ * volumeAverage (U : Set (Vec d))
          (fun x => Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2)) *
          vecNormSq p + 2 * nu⁻¹ * vecNormSq q := by
  have hUb : Bornology.IsBounded (U : Set (Vec d)) :=
    U.isDomain.isBoundedDomain.isBounded
  have hY := integrableOn_sq_streamCutoff_of_isBounded omega m hUb
  have hvar := blockVecDot_coarseBlockMatrix_le_volumeAverage U
    (cutoffDomainCoeffOn U hnu omega m) (p, q)
  rw [coarseBlockMatrix_domain_coefficientCutoff_eq_ch02 U hnu omega m]
  refine hvar.trans ?_
  have hfield : ∀ x : Vec d,
      Book.Ch02.blockMatrixField (cutoffDomainCoeffOn U hnu omega m) x =
        blockMatrixOfCoeff ((coefficientCutoff nu omega m).toCoeffField x) := fun _ => rfl
  simp only [hfield]
  have hmaj : volumeAverage (U : Set (Vec d))
      (fun x => blockVecDot (p, q) (blockMatVecMul
        (blockMatrixOfCoeff ((coefficientCutoff nu omega m).toCoeffField x)) (p, q))) ≤
      volumeAverage (U : Set (Vec d))
        (fun x => (2 * nu⁻¹ * vecNormSq p) *
            Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2 +
          (nu * vecNormSq p + 2 * nu⁻¹ * vecNormSq q)) := by
    refine volumeAverageMonoD ?_ ?_ ?_
    · filter_upwards [(cutoffDomainCoeffOn U hnu omega m).aeElliptic] with x hx
      exact blockMatrixOfCoeff_quadratic_nonneg hx (p, q)
    · have hfin : IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d))) := by
        refine ⟨?_⟩
        rw [MeasureTheory.Measure.restrict_apply_univ]
        exact lt_top_iff_ne_top.2 (volume_domain_ne_top U)
      exact ((hY.const_mul (2 * nu⁻¹ * vecNormSq p)).add
        (integrable_const (nu * vecNormSq p + 2 * nu⁻¹ * vecNormSq q)))
    · refine Filter.Eventually.of_forall fun x => ?_
      have h := blockQuadratic_coefficientCutoff_le hnu omega m x p q
      linarith only [h]
  refine hmaj.trans ?_
  rw [volumeAverageAffineD (volume_domain_ne_zero U) (volume_domain_ne_top U) hY]
  exact le_of_eq (by ring)

/-! ## The random factor of `e.Enaught.vs.A.and.Ahom` on a general domain -/

private theorem vecNormSqSmulD (c : ℝ) (x : Vec d) :
    vecNormSq (c • x) = c ^ 2 * vecNormSq x := by
  show vecDot (c • x) (c • x) = c ^ 2 * vecDot x x
  rw [vecDot_smul_left, vecDot_smul_right]
  ring

private theorem invSqrtSqD {e : ℝ} (he : 0 < e) : ((Real.sqrt e)⁻¹) ^ 2 = e⁻¹ := by
  rw [inv_pow, Real.sq_sqrt he.le]

private theorem blockVecDotBlockIdentityD (p q : Vec d) :
    blockVecDot (p, q) (blockMatVecMul (Book.Ch02.blockIdentity d) (p, q)) =
      vecNormSq p + vecNormSq q := by
  rw [Carriers.blockMatVecMul_blockIdentity]
  exact Carriers.blockVecDot_self (p, q)

/-- The deterministic scale against which the `L²` size of `k_m` is measured in
`envelopeRatioOn` is positive. -/
theorem cutoffEnvelopeScale_pos (d : ℕ) (m : ℕ) :
    0 < cutoffEnvelopeConst d * max 1 (m : ℝ) := by
  have hC := cutoffEnvelopeConst_pos d
  have hmax : (0 : ℝ) < max 1 (m : ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact mul_pos hC hmax

/-- The random factor of `e.Enaught.vs.A.and.Ahom` on a general set: the
normalized `L²` size of `k_m`, measured against the deterministic scale of the
envelope and truncated below at `1`. On a triadic cube it is the
`envelopeRatio` of `Envelope.lean`. -/
def envelopeRatioOn (m : ℕ) (U : Set (Vec d)) (omega : ShellSeq d) : ℝ :=
  max 1 (volumeAverage U
      (fun x => Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) /
    (cutoffEnvelopeConst d * max 1 (m : ℝ)))

theorem one_le_envelopeRatioOn (m : ℕ) (U : Set (Vec d)) (omega : ShellSeq d) :
    1 ≤ envelopeRatioOn m U omega :=
  le_max_left _ _

/-- **The first assertion in deterministic form on a general domain**: the
normalized coarse block matrix of the cutoff is bounded by `envelopeRatioOn`
times the doubled identity. -/
theorem blockMatLoewnerLE_envelopeRescale_coarseBlockMatrix_domain
    (U : Book.Ch02.Domain d) {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) :
    BlockMatLoewnerLE
      (envelopeRescale d nu m
        (coarseBlockMatrix (U : Set (Vec d))
          (coefficientCutoff nu omega m).toCoeffField))
      (envelopeRatioOn m (U : Set (Vec d)) omega • Book.Ch02.blockIdentity d) := by
  set Z : ℝ := volumeAverage (U : Set (Vec d))
    (fun x => Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) ^ 2) with hZdef
  set S : ℝ := cutoffEnvelopeConst d * max 1 (m : ℝ) with hSdef
  set rho : ℝ := envelopeRatioOn m (U : Set (Vec d)) omega with hrhodef
  have hSpos : 0 < S := cutoffEnvelopeScale_pos d m
  have hrho : 1 ≤ rho := one_le_envelopeRatioOn m (U : Set (Vec d)) omega
  have hZS : Z ≤ rho * S := by
    have hdiv : Z / S ≤ rho := le_max_right _ _
    exact (div_le_iff₀ hSpos).1 hdiv
  have hupPos := envelopeUpperScalar_pos hnu d m
  have hlowPos := envelopeLowerScalar_pos hnu d
  have hkey1 : (nu + 2 * nu⁻¹ * Z) * (envelopeUpperScalar d nu m)⁻¹ ≤ rho := by
    have hupEq : envelopeUpperScalar d nu m = nu + 2 * nu⁻¹ * S := by
      rw [hSdef]
      unfold envelopeUpperScalar
      ring
    have hnuinv : (0 : ℝ) < 2 * nu⁻¹ := by positivity
    have hstep : nu + 2 * nu⁻¹ * Z ≤ rho * envelopeUpperScalar d nu m := by
      rw [hupEq, mul_add]
      have h1 : 2 * nu⁻¹ * Z ≤ 2 * nu⁻¹ * (rho * S) :=
        mul_le_mul_of_nonneg_left hZS hnuinv.le
      have h2 : nu ≤ rho * nu := le_mul_of_one_le_left hnu.le hrho
      have h3 : 2 * nu⁻¹ * (rho * S) = rho * (2 * nu⁻¹ * S) := by ring
      linarith only [h1, h2, h3]
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ hupPos).2 hstep
  have hkey2 : 2 * nu⁻¹ * (envelopeLowerScalar d nu)⁻¹ ≤ rho := by
    have hCne : cutoffEnvelopeConst d ≠ 0 := (cutoffEnvelopeConst_pos d).ne'
    have hEq : 2 * nu⁻¹ * (envelopeLowerScalar d nu)⁻¹ =
        (cutoffEnvelopeConst d)⁻¹ := by
      unfold envelopeLowerScalar
      field_simp
    have hle : (cutoffEnvelopeConst d)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_cutoffEnvelopeConst d)
    rw [hEq]
    linarith only [hle, hrho]
  rintro ⟨p, q⟩
  rw [blockVecDot_envelopeRescale, blockMatVecMul_blockSMul, blockVecDot_smul_right,
    blockVecDotBlockIdentityD]
  have hbound := blockVecDot_coarseBlockMatrix_coefficientCutoff_domain_le U hnu omega m
    ((Real.sqrt (envelopeUpperScalar d nu m))⁻¹ • p)
    ((Real.sqrt (envelopeLowerScalar d nu))⁻¹ • q)
  rw [vecNormSqSmulD, vecNormSqSmulD, invSqrtSqD hupPos, invSqrtSqD hlowPos,
    ← hZdef] at hbound
  have hp := vecNormSq_nonneg p
  have hq := vecNormSq_nonneg q
  have hA : (nu + 2 * nu⁻¹ * Z) * ((envelopeUpperScalar d nu m)⁻¹ * vecNormSq p) ≤
      rho * vecNormSq p := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hkey1 hp
  have hB : 2 * nu⁻¹ * ((envelopeLowerScalar d nu)⁻¹ * vecNormSq q) ≤
      rho * vecNormSq q := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hkey2 hq
  have hfinal : rho * (vecNormSq p + vecNormSq q) =
      rho * vecNormSq p + rho * vecNormSq q := by ring
  linarith only [hbound, hA, hB, hfinal]

/-! ## Symmetry, positivity and the printed norm form -/

theorem isSymmetricBlockMat_envelopeRescale {M : BlockMat d}
    (hM : IsSymmetricBlockMat M) (nu : ℝ) (m : ℕ) :
    IsSymmetricBlockMat (envelopeRescale d nu m M) := by
  intro alpha beta
  rw [envelopeRescale_eq]
  cases alpha with
  | inl i =>
    cases beta with
    | inl j => exact congrArg _ (hM (Sum.inl i) (Sum.inl j))
    | inr j => exact congrArg _ (hM (Sum.inl i) (Sum.inr j))
  | inr i =>
    cases beta with
    | inl j => exact congrArg _ (hM (Sum.inr i) (Sum.inl j))
    | inr j => exact congrArg _ (hM (Sum.inr i) (Sum.inr j))

theorem isSymmetricBlockMat_coarseBlockMatrix_domain (U : Book.Ch02.Domain d)
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) :
    IsSymmetricBlockMat
      (coarseBlockMatrix (U : Set (Vec d))
        (coefficientCutoff nu omega m).toCoeffField) := by
  rw [coarseBlockMatrix_domain_coefficientCutoff_eq_ch02 U hnu omega m]
  exact Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix U _

theorem blockVecDot_coarseBlockMatrix_domain_nonneg (U : Book.Ch02.Domain d)
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) (Z : BlockVec d) :
    0 ≤ blockVecDot Z
      (blockMatVecMul
        (coarseBlockMatrix (U : Set (Vec d))
          (coefficientCutoff nu omega m).toCoeffField) Z) := by
  rw [coarseBlockMatrix_domain_coefficientCutoff_eq_ch02 U hnu omega m]
  rcases eq_or_ne Z 0 with rfl | hZ
  · show (0 : ℝ) ≤ vecDot (0 : Vec d) _ + vecDot (0 : Vec d) _
    rw [vecDot_zero_left, vecDot_zero_left, add_zero]
  · exact ((Book.Ch02.blockCoarseMatrixTheory U
      (cutoffDomainCoeffOn U hnu omega m)).block_matrix_posDef Z hZ).le

theorem blockVecDot_envelopeRescale_nonneg {M : BlockMat d}
    (hM : ∀ Z : BlockVec d, 0 ≤ blockVecDot Z (blockMatVecMul M Z))
    (nu : ℝ) (m : ℕ) (Z : BlockVec d) :
    0 ≤ blockVecDot Z (blockMatVecMul (envelopeRescale d nu m M) Z) := by
  obtain ⟨p, q⟩ := Z
  rw [blockVecDot_envelopeRescale]
  exact hM _

/-- **The printed norm form of `e.Enaught.vs.A.and.Ahom`**: on every bounded
domain the Euclidean operator norm of the rescaled coarse block matrix is
bounded by the random factor. -/
theorem blockMatrixOperatorNorm_envelopeRescale_coarseBlockMatrix_le
    (U : Book.Ch02.Domain d) {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) :
    Carriers.blockMatrixOperatorNorm
        (envelopeRescale d nu m
          (coarseBlockMatrix (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField)) ≤
      envelopeRatioOn m (U : Set (Vec d)) omega :=
  Carriers.blockMatrixOperatorNorm_le_of_blockMatLoewnerLE_blockIdentity
    (le_trans zero_le_one (one_le_envelopeRatioOn m (U : Set (Vec d)) omega))
    (isSymmetricBlockMat_envelopeRescale
      (isSymmetricBlockMat_coarseBlockMatrix_domain U hnu omega m) nu m)
    (blockVecDot_envelopeRescale_nonneg
      (blockVecDot_coarseBlockMatrix_domain_nonneg U hnu omega m) nu m)
    (blockMatLoewnerLE_envelopeRescale_coarseBlockMatrix_domain U hnu omega m)

end

end SuperdiffusionCLT.Section2.Annealed
