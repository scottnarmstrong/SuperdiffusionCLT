/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationEnvelopeCarrier
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT2Inputs
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageAssembly
public import SuperdiffusionCLT.Section2.Annealed.EnvelopeDomain
public import SuperdiffusionCLT.Section2.Annealed.Measurability
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers

/-!
# The normalized perturbation `V_z`: which coordinates it reads, and the four
displayed inputs of the second summand

The printed proof of `l.localization.average` estimates the second summand of
`e.localization.average.oneshot`.  The printed lines read, verbatim:

```
W_z \coloneqq \bigl|\bfE_\ell^{\nf12}\G_{-\h_z}P\bigr|^2
\qquad \mbox{and}\qquad
Z_z \coloneqq \G_{-\h_z}P\cdot\bigl(\bfA_\ell(z+\cu_n)-\bfAhom_\ell(\cu_n)\bigr)\G_{-\h_z}P\,,
```
```
so that~$W_z$ is~$\mathcal{F}_>$-measurable,~$\E[Z_z\mid\mathcal{F}_>]=0$ by stationarity, and~$T_2 = \bigl|\avsum_{z\in 3^n\Zd\cap\cu_m} Z_z\bigr|$. By~\eqref{e.Enaught.vs.A.and.Ahom}, we have~$|\bfE_\ell^{-\nf12}\bfAhom_\ell(\cu_n)\bfE_\ell^{-\nf12}|\leq 1$ deterministically and~$|\bfE_\ell^{-\nf12}\bfA_\ell(z+\cu_n)\bfE_\ell^{-\nf12}|\leq\O_{\Gamma_1}(C)$ conditionally on~$\mathcal{F}_>$,
```
```
|Z_z| \leq W_z\cdot\bigl|\bfE_\ell^{-\nf12}\bigl(\bfA_\ell(z+\cu_n)-\bfAhom_\ell(\cu_n)\bigr)\bfE_\ell^{-\nf12}\bigr| \leq W_z\cdot\O_{\Gamma_1}(C)
\qquad \mbox{conditionally on~$\mathcal{F}_>$.}
```
```
Apply Proposition~\ref{p.concentration} with~$\sigma=1$ to the conditionally independent centered variables~$\overline W^{-1}Z_z$ on each of the~$\sim 3^{d(\ell-n)}$ sublattices used above
```

## Which coordinates `V_z` reads

`V_z` is our name for the normalized perturbation
`bfE_\ell^{-1/2}(bfA_\ell(z+cu_n) - bfAhom_\ell(cu_n))bfE_\ell^{-1/2}`, the
carrier `localizationV nu l P n R` at `R = z + cu_n`.  Its `omega`-dependence enters only
through `bfA_\ell = coefficientCutoff nu · l`, which is
`nu · 1 + sum_{r in range (l+1)} shellReg (· r)`: **`V_z` reads exactly the lower
shell coordinates `{r | r ≤ l}`, and nothing above them.**  The annealed matrix
`bfAhom_\ell(cu_n)` is a constant in `omega`, and the envelope factors `bfE_\ell`
are deterministic.  This is the print's "`bfA_\ell` is `{r ≤ ℓ}`-measurable", and it settles
`h_compl`: the full `RegCoeffField`-valued cutoff field is measurable for any coordinate
family containing the shells `0, …, L` (`measurable_SS_coefficientCutoff_full`).

The same fact is the obstruction for `h_indep`.  **Every** member of the family
`{‖V_z‖}_z`, over cubes at *any* scale, is a functional of the *same* coordinate
block `{r | r ≤ l}`, so an independence of the family cannot come from any law that
separates *coordinates*: the `ShellLawJ2` route
(`indep_shellSigma_of_shellLawJ2`) separates *coordinate families* `{r ≤ l}` and
`{l < r}`, not distinct members of one and the same block.  This is a statement about
what the law hypotheses supply, not a refutation: two functions of a common coordinate
can be independent (for a uniform variable on four points, `X mod 2` and `floor (X/2)` are), so no
contradiction follows and `h_indep` must be reported as unprovable *from the law
hypotheses* rather than false.

## Status of the displayed inputs

* `hV` (printed: `|bfE^{-1/2} A_\ell bfE^{-1/2}| = O_{Γ_1}(C)` and
  `|bfE^{-1/2} Ahom bfE^{-1/2}| ≤ 1`): **proved** unconditionally at `K = 2`
  (`isBigO_gammaSigma_localizationV_opNorm`; the printed `C` is `2`, and the second bound
  is the deterministic `opNorm_localizationV_le_envelopeRatio` term `1`).
* `h_compl` (printed: `bfA_\ell` is `{r ≤ ℓ}`-measurable): **proved** at the matrix level in
  `0 < nu` (`measurable_SS_coefficientCutoff_full`).
* `h_mean` (printed: `E[Z_z | F_>] = 0` by stationarity): **not provable in the carried
  form**: the carried `∫ ‖V_z‖ = 0` would be the a.e. vanishing of `V_z`, not a centring.
* `h_indep` (printed: *conditionally* independent given `F_>`): **not proved**: the carried
  unconditional `iIndepFun` is strictly stronger than the print and is supplied by no law
  hypothesis (see the coordinate reading above).

## Main results

* `measurable_SS_coefficientCutoff_full`: the full `RegCoeffField`-valued cutoff
  is measurable for any coordinate family containing the shells `0, …, L`.
* `opNorm_localizationV_le_envelopeRatio`: the deterministic per-sample bound
  `‖V_z‖ ≤ envelopeRatio l R + 1`.
* `isBigO_gammaSigma_localizationV_opNorm`: the printed `|V_z| = O_{Γ_1}(2)`, i.e. `hV`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## `h_compl`: lower-shell measurability

The print records that `bfA_\ell` is measurable with respect to the lower
coordinates.  The result below proves this at the level of the full cutoff field, which is
the form the matrix-level measurability of `V_z` consumes. -/

/-- The full `RegCoeffField`-valued cutoff field is measurable for the
σ-algebra of any coordinate family containing the shells `0, …, L`. -/
theorem measurable_SS_coefficientCutoff_full {S : Set ℕ} {L : ℕ}
    (hS : ∀ n ≤ L, n ∈ S) (nu : ℝ) :
    Measurable[SuperdiffusionCLT.Probability.shellSigma (d := d) S]
      (fun omega : ShellSeq d =>
        SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L) := by
  have hstr : Measurable[SuperdiffusionCLT.Probability.shellSigma (d := d) S]
      (fun omega : ShellSeq d =>
        SuperdiffusionCLT.Frozen.Section2.streamCutoff omega L) := by
    unfold SuperdiffusionCLT.Frozen.Section2.streamCutoff
    refine Finset.measurable_sum _ fun n hn => ?_
    exact ShellField.measurable_forgetShell.comp
      (SuperdiffusionCLT.Section2.Localization.shellSigma_coordinate_measurable
        (hS n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))))
  have hconst : Measurable[SuperdiffusionCLT.Probability.shellSigma (d := d) S]
      (fun _ : ShellSeq d =>
        Homogenization.RegCoeffField.constRegCoeffField (nu • (1 : Homogenization.Mat d))) :=
    measurable_const
  exact hconst.add hstr

/-! ### A block-matrix measurability engine at the lower-shell σ-algebra -/

private theorem toFullBlockMat_blockMatMul_local (A B : BlockMat d) :
    toFullBlockMat (blockMatMul A B) = toFullBlockMat A * toFullBlockMat B := by
  ext α β
  cases α <;> cases β <;>
    simp only [toFullBlockMat, blockMatMul, Matrix.mul_apply, Matrix.add_apply,
      Fintype.sum_sum_type]

/-! ## `hV`: the printed `Γ_1` bound of `|V_z|`

The print's `e.Enaught.vs.A.and.Ahom` supplies two deterministic
bounds: `|bfE_ℓ^{-1/2} bfAhom_ℓ(cu_n) bfE_ℓ^{-1/2}| ≤ 1`, which is
`blockMatLoewnerLE_envelopeRescale_annealedBlockMatrix` on the origin cube, and
the `Γ_1` bound of the cutoff term, which is
`isBigOWith_gammaSigma_envelopeRatio` at the cube.  Both are read at `cubeSet`,
so the open-cube passage of `e.Enaught.vs.A.and.Ahom` is not needed.  The two
together give `‖V_z‖ ≤ envelopeRatio l R + 1` per sample and hence
`|V_z| = O_{Γ_1}(2)`. -/

/-- `envelopeRescale` expands as the two-sided product with the inverse square
root of the envelope. -/
private theorem toFullBlockMat_envelopeRescale_eq (nu : ℝ) (m : ℕ) (M : BlockMat d) :
    toFullBlockMat (envelopeRescale d nu m M) =
      toFullBlockMat (envelopeInvSqrt d nu m) * toFullBlockMat M *
        toFullBlockMat (envelopeInvSqrt d nu m) := by
  unfold envelopeRescale
  rw [toFullBlockMat_blockMatMul_local, toFullBlockMat_blockMatMul_local, Matrix.mul_assoc]

/-- The doubled matrix of `V_z` is the difference of the two rescaled factors. -/
private theorem toFullBlockMat_localizationV (nu : ℝ) (l : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (n : ℕ) (R : TriadicCube d) (omega : ShellSeq d) :
    toFullBlockMat (localizationV nu l P n R omega) =
      toFullBlockMat (envelopeRescale d nu l
        (Homogenization.coarseBlockMatrix (cubeSet R)
          (coefficientCutoff nu omega l).toCoeffField)) -
      toFullBlockMat (envelopeRescale d nu l
        (annealedBlockMatrix nu l P (cubeSet (originCube d (n : ℤ))))) := by
  unfold localizationV localizationPerturbationMatrix
  simp only [toFullBlockMat_envelopeRescale_eq, toFullBlockMat_ofFullBlockMat,
    Matrix.mul_sub, Matrix.sub_mul]

/-- The annealed block matrix on a cube is symmetric. -/
private theorem isSymmetricBlockMat_annealedBlockMatrix_cubeSet [NeZero d] {nu : ℝ}
    (l : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (Q : TriadicCube d) :
    IsSymmetricBlockMat (annealedBlockMatrix nu l P (cubeSet Q)) := by
  intro α β
  cases α with
  | inl i =>
    cases β with
    | inl j =>
      show (annealedBlockMatrix nu l P (cubeSet Q)).upperLeft i j =
        (annealedBlockMatrix nu l P (cubeSet Q)).upperLeft j i
      simp only [annealedBlockMatrix_upperLeft_apply]
      refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
      simpa only [Matrix.transpose_apply] using
        (congrFun (congrFun (isSymm_coarseBlockMatrix_upperLeft (cubeSet Q)
          (coefficientCutoff nu omega l).toFun) i) j).symm
    | inr j =>
      show (annealedBlockMatrix nu l P (cubeSet Q)).upperRight i j =
        (annealedBlockMatrix nu l P (cubeSet Q)).lowerLeft j i
      have h := congrFun (congrFun
        (annealedBlockMatrix_upperRight_eq_transpose_lowerLeft (nu := nu) (m := l) (P := P)
          (U := cubeSet Q)) i) j
      simpa only [matTranspose, Matrix.transpose_apply] using h
  | inr i =>
    cases β with
    | inl j =>
      show (annealedBlockMatrix nu l P (cubeSet Q)).lowerLeft i j =
        (annealedBlockMatrix nu l P (cubeSet Q)).upperRight j i
      have h := congrFun (congrFun
        (annealedBlockMatrix_upperRight_eq_transpose_lowerLeft (nu := nu) (m := l) (P := P)
          (U := cubeSet Q)) j) i
      simpa only [matTranspose, Matrix.transpose_apply] using h.symm
    | inr j =>
      show (annealedBlockMatrix nu l P (cubeSet Q)).lowerRight i j =
        (annealedBlockMatrix nu l P (cubeSet Q)).lowerRight j i
      simp only [annealedBlockMatrix_lowerRight_apply]
      refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
      simpa only [Matrix.transpose_apply] using
        (congrFun (congrFun (isSymm_coarseBlockMatrix_lowerRight (cubeSet Q)
          (coefficientCutoff nu omega l).toFun) i) j).symm

/-- The annealed block matrix on a cube is positive semidefinite. -/
private theorem zero_le_blockVecDot_annealedBlockMatrix_cubeSet [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (l : ℕ) (Q : TriadicCube d) (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul (annealedBlockMatrix nu l P (cubeSet Q)) X) := by
  rw [blockVecDot_annealedBlockMatrix (hnu := hnu) (m := l) (Q := Q)
    (hPrefix := hPrefix) (hJ2 := hJ2) (hJ3 := hJ3) (hJ4 := hJ4) (P := P) X]
  exact integral_nonneg fun omega =>
    zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff (hnu := hnu) (omega := omega)
      (m := l) (Q := Q) X

/-- **The deterministic per-sample `hV` bound**: `‖V_z‖ ≤ envelopeRatio l R + 1`.
The first term is the printed `Γ_1` bound of the cutoff contribution, the second
the deterministic `≤ 1` of `bfE_ℓ^{-1/2} bfAhom_ℓ bfE_ℓ^{-1/2}`. -/
theorem opNorm_localizationV_le_envelopeRatio [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (l : ℕ) (n : ℕ) (R : TriadicCube d) (omega : ShellSeq d) :
    blockMatrixOperatorNorm (localizationV nu l P n R omega) ≤
      envelopeRatio l R omega + 1 := by
  have hM : blockMatrixOperatorNorm
      (envelopeRescale d nu l (Homogenization.coarseBlockMatrix (cubeSet R)
        (coefficientCutoff nu omega l).toCoeffField)) ≤ envelopeRatio l R omega :=
    blockMatrixOperatorNorm_le_of_blockMatLoewnerLE_blockIdentity
      (le_trans zero_le_one (one_le_envelopeRatio l R omega))
      (isSymmetricBlockMat_envelopeRescale
        (isSymmetricBlockMat_coarseBlockMatrix_coefficientCutoff (hnu := hnu) (omega := omega)
          (m := l) (Q := R)) nu l)
      (blockVecDot_envelopeRescale_nonneg
        (zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff (hnu := hnu) (omega := omega)
          (m := l) (Q := R)) nu l)
      (blockMatLoewnerLE_envelopeRescale_coarseBlockMatrix hnu omega l R)
  have hone : (1 : ℝ) • Book.Ch02.blockIdentity d = Book.Ch02.blockIdentity d := by
    refine blockMat_ext ?_ ?_ ?_ ?_ <;> simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag]
  have hN : blockMatrixOperatorNorm
      (envelopeRescale d nu l
        (annealedBlockMatrix nu l P (cubeSet (originCube d (n : ℤ))))) ≤ 1 :=
    blockMatrixOperatorNorm_le_of_blockMatLoewnerLE_blockIdentity zero_le_one
      (isSymmetricBlockMat_envelopeRescale
        (isSymmetricBlockMat_annealedBlockMatrix_cubeSet l P (originCube d (n : ℤ))) nu l)
      (blockVecDot_envelopeRescale_nonneg
        (zero_le_blockVecDot_annealedBlockMatrix_cubeSet hnu P hPrefix hJ2 hJ3 hJ4 l
          (originCube d (n : ℤ))) nu l)
      (by
        rw [hone]
        exact blockMatLoewnerLE_envelopeRescale_annealedBlockMatrix (nu := nu) (m := l)
          (P := P) (Q := originCube d (n : ℤ)) hnu hPrefix hJ2 hJ3 hJ4)
  calc blockMatrixOperatorNorm (localizationV nu l P n R omega)
      = ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (toFullBlockMat (localizationV nu l P n R omega))‖ := rfl
    _ = ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (toFullBlockMat (envelopeRescale d nu l (Homogenization.coarseBlockMatrix (cubeSet R)
            (coefficientCutoff nu omega l).toCoeffField)) -
           toFullBlockMat (envelopeRescale d nu l
            (annealedBlockMatrix nu l P (cubeSet (originCube d (n : ℤ))))))‖ := by
        rw [toFullBlockMat_localizationV]
    _ = ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (toFullBlockMat (envelopeRescale d nu l (Homogenization.coarseBlockMatrix (cubeSet R)
            (coefficientCutoff nu omega l).toCoeffField))) -
         Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (toFullBlockMat (envelopeRescale d nu l
            (annealedBlockMatrix nu l P (cubeSet (originCube d (n : ℤ))))))‖ := by
        rw [map_sub]
    _ ≤ ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (toFullBlockMat (envelopeRescale d nu l (Homogenization.coarseBlockMatrix (cubeSet R)
            (coefficientCutoff nu omega l).toCoeffField)))‖ +
         ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (toFullBlockMat (envelopeRescale d nu l
            (annealedBlockMatrix nu l P (cubeSet (originCube d (n : ℤ))))))‖ :=
        norm_sub_le _ _
    _ = blockMatrixOperatorNorm (envelopeRescale d nu l
          (Homogenization.coarseBlockMatrix (cubeSet R)
            (coefficientCutoff nu omega l).toCoeffField)) +
        blockMatrixOperatorNorm (envelopeRescale d nu l
          (annealedBlockMatrix nu l P (cubeSet (originCube d (n : ℤ))))) := rfl
    _ ≤ envelopeRatio l R omega + 1 := add_le_add hM hN

/-- **The printed `hV` at the carrier `localizationV`**: `|V_z| = O_{Γ_1}(2)`, for every
cube `R`, unconditional in `0 < nu`.  The printed `e.Enaught.vs.A.and.Ahom`
supplies the cutoff factor `≤ envelopeRatio l R` (its `Γ_1` bound, by
`isBigOWith_gammaSigma_envelopeRatio`) and the annealed factor `≤ 1`
deterministically; the sum is `≤ 2 · envelopeRatio l R`, so the tail at scale
`2t` is contained in the tail of `envelopeRatio` at `t`. -/
theorem isBigO_gammaSigma_localizationV_opNorm [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (l n : ℕ) (R : TriadicCube d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d => blockMatrixOperatorNorm (localizationV nu l P n R omega)) 2 := by
  intro t ht
  refine (measureReal_mono ?_).trans
    (isBigOWith_gammaSigma_envelopeRatio hPrefix hJ2 hJ3 hJ4 l R ht)
  intro omega hom
  have hVnn : 0 ≤ blockMatrixOperatorNorm (localizationV nu l P n R omega) :=
    blockMatrixOperatorNorm_nonneg _
  have hom' : (2 : ℝ) * t < blockMatrixOperatorNorm (localizationV nu l P n R omega) := by
    simpa only [IndependentSums.upperTailEvent, Set.mem_ofPred_eq, abs_of_nonneg hVnn] using hom
  have hle := opNorm_localizationV_le_envelopeRatio hnu P hPrefix hJ2 hJ3 hJ4 l n R omega
  have hρ := one_le_envelopeRatio l R omega
  show (1 : ℝ) * t < envelopeRatio l R omega
  rw [one_mul]
  linarith only [hom', hle, hρ]

end SuperdiffusionCLT.Section2.Localization
