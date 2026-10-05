/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Variance.ThreeScale
public import SuperdiffusionCLT.AKHC61.Carrier.Integrability
public import SuperdiffusionCLT.AKHC61.Carrier.OrliczMoments
public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocks
public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocksB
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Package C4: `e.CFS.weaker.applied`, the linear-average second moment

The (P3') clause `a.CFS.weaker` of
`SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`
is copied verbatim below. For scales `k ≤ n` in the window `beta * n < k < n - L1 * log(L2 * k)`
(the bound variables `j, n` of the clause instantiated at `j := n`, `n := k`, matching
`SuperdiffusionCLT.AKHC61.Variance.akhc_variance_threeScale`'s own naming
in `AKHC61/Variance/ThreeScaleC.lean`, its `hLinInt` hypothesis), (P3') gives a
polarized bilinear bound on the averaged difference matrix

`H := avsum_{R} (bfA(R) - bfAhom(cu_k))`, `R` ranging over the depth-`(n-k)`
descendants of `cu_n`:

`2 * p·Hq ≤ X(omega) * (p·bfAhom(cu_k) p + q·bfAhom(cu_k) q)`  for all `p q`,

with `X` a witness for `IsBigO P Psi X (omegaSeq k)`. This file extracts the
**second moment** of `H`'s `W`-relative squared Frobenius norm, `W := bfAhom(cu_k)`
read entrywise as `w := akhcMatDiag W`, in exactly the form
`akhc_variance_threeScale` consumes as its `hLinInt` hypothesis:

`E[akhcRelFrobSq w H] ≤ (2d)² · (pPsi/(pPsi-2)) · KPsi^(3⌈pPsi⌉₊²) · omegaSeq(k)²`.

## Route

The (P3') bound holds for *every* pair `(p, q) : BlockVec d × BlockVec d`, not
merely as a positive-semidefinite quadratic-form test. Choosing
`p := c • blockBasis α`, `q := blockBasis β` for a free real `c` turns it into
a one-parameter family of scalar inequalities in `c`, whose associated
quadratic `X wα · (c·c) - 2 L · c + X wβ ≥ 0` (`L` the `(α, β)` entry of `H`)
has non-positive discriminant (`discrim_le_zero`, mirroring the `2×2`-minor
argument of `ThreeScale.lean`'s `akhc_sq_blockMatEntry_le_mul_diag`), giving
the *entrywise, uniform-in-`(α,β)`* bound `L² ≤ X² wα wβ`, i.e.
`L²/(wα wβ) ≤ X²`. Summing over the `(2d)²` pairs `(α, β) : BlockCoord d ×
BlockCoord d` and taking expectations (A3's `akhc_moment_le_of_isBigO` at
`q := 2`, `p := pPsi`) gives the target. This route needs no symmetry of `H`
and no diagonality of `bfAhom(cu_k)`: `w := akhcMatDiag W` is simply `W`'s
diagonal readout, for **any** block matrix `W`, and the bound is entrywise
sharp (no cross-block blow-up), unlike the naive `|H_{αβ}| ≤ (X/2)(wα+wβ)`
polarization.

## Hypotheses

`0 < nu`, `ShellLawJ4` (for `w`'s positivity, via package A2's
`akhc_annealedBlockMatrix_originCube_eq_blockDiag` and
`akhc_sigmaBarSeq_pos_of_P2`/`akhc_sigmaBarStarInvSeq_pos_of_P2`), the (P2')
clause (for package A1's entrywise integrability, needed for measurability of
the linear average), `2 ≤ d` (root scope, needed only to get `2 < pPsi` from
(P3')'s own `(d : ℝ) < pPsi`), and the (P3') clause verbatim. No
`ShellLawPrefix`/`ShellLawJ2`/`ShellLawJ3`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Variance

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## Small algebraic and block-matrix helper lemmas -/

/-- The diagonal readout of a block matrix, as a function on `BlockCoord d`. -/
def akhcMatDiag (M : BlockMat d) : BlockCoord d → ℝ := fun α => blockMatEntry M α α

/-- The `(k, n)`-linear descendant average `avsum_{R} (bfA(R) - bfAhom(cu_k))`,
entrywise: `R` ranges over the depth-`(n - k)` descendants of `cu_n`. This is
exactly the integrand of `SuperdiffusionCLT.AKHC61.Variance.akhc_variance_threeScale`'s
`hLinInt` hypothesis (`ThreeScaleC.lean`). -/
def akhcCFSLinEntry (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (k n : ℕ)
    (omega : ShellSeq d) : BlockCoord d → BlockCoord d → ℝ :=
  fun α β => ((descendantsAtDepth (originCube d (n : ℤ)) (n - k)).card : ℝ)⁻¹ *
    ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
      (blockMatEntry (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField)
          α β -
        blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) α β)

/-- Entrywise identity for the difference of two block matrices formed via
`ofFullBlockMat`/`toFullBlockMat`. -/
theorem akhc_blockMatEntry_ofFullBlockMat_sub (A B : BlockMat d) (α β : BlockCoord d) :
    blockMatEntry (ofFullBlockMat (toFullBlockMat A - toFullBlockMat B)) α β =
      blockMatEntry A α β - blockMatEntry B α β := by
  cases α <;> cases β <;> rfl

/-- The `(α, β)` bilinear pairing of a scaled basis vector against a
difference matrix, read off via `blockBasis_pairing`. -/
theorem akhc_blockVecDot_smul_basis_ofFullBlockMat_sub (A B : BlockMat d) (c : ℝ)
    (α β : BlockCoord d) :
    blockVecDot (c • blockBasis α)
        (blockMatVecMul (ofFullBlockMat (toFullBlockMat A - toFullBlockMat B))
          (blockBasis β)) =
      c * (blockMatEntry A α β - blockMatEntry B α β) := by
  rw [blockVecDot_smul_left, blockBasis_pairing, akhc_blockMatEntry_ofFullBlockMat_sub]

/-- The `(α, α)` quadratic pairing of a scaled basis vector against a matrix. -/
theorem akhc_blockVecDot_smul_basis_self (W : BlockMat d) (c : ℝ) (α : BlockCoord d) :
    blockVecDot (c • blockBasis α) (blockMatVecMul W (c • blockBasis α)) =
      c ^ 2 * blockMatEntry W α α := by
  rw [blockMatVecMul_smul, blockVecDot_smul_left, blockVecDot_smul_right, blockBasis_pairing]
  ring

/-- **Polarization.** A bilinear bound `2 (c L) ≤ X (c² wα + wβ)`, valid for
every real `c`, forces the entrywise squared bound `L² ≤ X² wα wβ`. This is
the quadratic-discriminant argument, exactly as in `ThreeScale.lean`'s
`akhc_sq_blockMatEntry_le_mul_diag`, applied to the quadratic
`(X wα)(c·c) - (2L) c + X wβ ≥ 0`. -/
theorem akhc_sq_le_mul_of_forall_c {wα wβ X L : ℝ}
    (h : ∀ c : ℝ, 2 * (c * L) ≤ X * (c ^ 2 * wα + wβ)) :
    L ^ 2 ≤ X ^ 2 * wα * wβ := by
  have hq : ∀ c : ℝ, 0 ≤ (X * wα) * (c * c) + (-(2 * L)) * c + X * wβ := by
    intro c
    have hc := h c
    have heq : (X * wα) * (c * c) + (-(2 * L)) * c + X * wβ =
        X * (c ^ 2 * wα + wβ) - 2 * (c * L) := by ring
    rw [heq]
    linarith only [hc]
  have hdisc := discrim_le_zero hq
  have heq2 : discrim (X * wα) (-(2 * L)) (X * wβ) = 4 * L ^ 2 - 4 * (X ^ 2 * wα * wβ) := by
    unfold discrim
    ring
  rw [heq2] at hdisc
  linarith only [hdisc]

/-! ## Package C4: `e.CFS.weaker.applied` -/

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : ProbabilityMeasure (ShellSeq d)) (hJ4 : ShellLawJ4 d P) (L : ℕ)
  (hd : 2 ≤ d)
  -- (P2') `a.ellipticity.weaker`, needed for A1's integrability
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hDnn : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowthP2 : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
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
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
  -- (P3') `a.CFS.weaker`, copied verbatim from the main statement
  (beta L1 L2 : ℝ) (m3 : ℕ) (omegaSeq : ℕ → ℝ) (Psi : ℝ → ℝ) (KPsi pPsi : ℝ)
  (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2)
  (homegaPos : ∀ k' : ℕ, 0 < omegaSeq k') (homegaAnti : Antitone omegaSeq)
  (homegaTendsto : Filter.Tendsto omegaSeq Filter.atTop (nhds 0))
  (hPsiMono : StrictMonoOn Psi (Set.Ici 0)) (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t)
  (hKPsi : 1 ≤ KPsi) (hpPsi : (d : ℝ) < pPsi)
  (hGrowthP3 : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t))
  (hP3 : ∀ j n : ℕ, m3 ≤ n → beta * (j : ℝ) < (n : ℝ) →
    (n : ℝ) < (j : ℝ) - L1 * Real.log (L2 * (n : ℝ)) →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure Psi X (omegaSeq n) ∧
      ∀ (omega : ShellSeq d) (p q : BlockVec d),
        2 *
            (((descendantsAtDepth (originCube d (j : ℤ)) (j - n)).card : ℝ)⁻¹ *
              ∑ R ∈ descendantsAtDepth (originCube d (j : ℤ)) (j - n),
                blockVecDot p
                  (blockMatVecMul
                    (ofFullBlockMat
                      (toFullBlockMat
                          (coarseBlockMatrix (cubeSet R)
                            (coefficientCutoff nu omega L).toCoeffField) -
                        toFullBlockMat
                          (annealedBlockMatrix nu L P
                            (cubeSet (originCube d (n : ℤ))))))
                    q)) ≤
          X omega *
            (blockVecDot p
                (blockMatVecMul
                  (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
              blockVecDot q
                (blockMatVecMul
                  (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q)))

include hnu hJ4 hd hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2
  hpPsi homegaPos hPsiOne hKPsi hGrowthP3 hP3

/-- **`e.CFS.weaker.applied`, second-moment form.** For scales
`k ≤ n` in the window `beta * n < k < n - L1 * log(L2 * k)` (the `(P3')`
window, its own bound variables `j, n` instantiated `j := n`, `n := k`), the
`W`-relative squared Frobenius norm of the linear descendant average
`avsum_R (bfA(R) - bfAhom(cu_k))`, `W := bfAhom(cu_k)` read entrywise via
`akhcMatDiag`, `R` ranging over the depth-`(n - k)` descendants of `cu_n`, is
integrable and its expectation is at most
`(2d)² · (pPsi/(pPsi-2)) · KPsi^(3⌈pPsi⌉₊²) · omegaSeq(k)²`. This is exactly
the `hLinInt` hypothesis of
`SuperdiffusionCLT.AKHC61.Variance.akhc_variance_threeScale`
(`ThreeScaleC.lean`), with `w := akhcMatDiag (annealedBlockMatrix nu L P
(cubeSet (originCube d k)))`. -/
theorem akhc_CFS_weaker_applied {k n : ℕ} (hm3 : m3 ≤ k)
    (hwin1 : beta * (n : ℝ) < (k : ℝ))
    (hwin2 : (k : ℝ) < (n : ℝ) - L1 * Real.log (L2 * (k : ℝ))) :
    Integrable (fun omega => akhcRelFrobSq
        (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))))
        (akhcCFSLinEntry nu L P k n omega)) P.toMeasure ∧
    ∫ omega, akhcRelFrobSq
        (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))))
        (akhcCFSLinEntry nu L P k n omega) ∂P.toMeasure ≤
      (2 * (d : ℝ)) ^ 2 * ((pPsi / (pPsi - 2)) * KPsi ^ (3 * ⌈pPsi⌉₊ ^ 2)) *
        omegaSeq k ^ 2 := by
  obtain ⟨X, hXm, hXbig, hbil⟩ := hP3 n k hm3 hwin1 hwin2
  -- Positivity of `w := akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d k)))`,
  -- from package A2's block-diagonal identity and scalar positivity (`ShellLawJ4`).
  have hwpos : ∀ α : BlockCoord d,
      0 < akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) α := by
    intro α
    unfold akhcMatDiag
    rw [SuperdiffusionCLT.AKHC61.Carrier.akhc_annealedBlockMatrix_originCube_eq_blockDiag
      hnu L hJ4 (k : ℤ)]
    cases α with
    | inl i =>
        show 0 < (Book.Ch02.blockDiag
          (sigmaBarScalar nu L P (cubeSet (originCube d (k : ℤ))) • (1 : Mat d))
          (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (k : ℤ))) • (1 : Mat d))).upperLeft
          i i
        rw [Book.Ch02.blockDiag]
        show 0 < (sigmaBarScalar nu L P (cubeSet (originCube d (k : ℤ))) • (1 : Mat d)) i i
        rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        exact SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D
          m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS
          hGrowthP2 hP2 k
    | inr i =>
        show 0 < (Book.Ch02.blockDiag
          (sigmaBarScalar nu L P (cubeSet (originCube d (k : ℤ))) • (1 : Mat d))
          (sigmaBarStarInvScalar nu L P
            (cubeSet (originCube d (k : ℤ))) • (1 : Mat d))).lowerRight i i
        rw [Book.Ch02.blockDiag]
        show 0 < (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (k : ℤ))) • (1 : Mat d)) i i
        rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        exact SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4
          gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS
          hpPsiS hGrowthP2 hP2 k
  -- Entrywise integrability of the coarse block matrix, from (P2') (package A1).
  have hIntA1 := SuperdiffusionCLT.AKHC61.Carrier.akhc_integrable_blockMatEntry_of_P2 d hnu P
    L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS
    hGrowthP2 hP2
  have hLinMeas : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun omega => akhcCFSLinEntry nu L P k n omega α β) P.toMeasure := by
    intro α β
    unfold akhcCFSLinEntry
    have hSumMeas : AEStronglyMeasurable (fun omega =>
        ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
          (blockMatEntry (coarseBlockMatrix (cubeSet R)
              (coefficientCutoff nu omega L).toCoeffField) α β -
            blockMatEntry (annealedBlockMatrix nu L P
              (cubeSet (originCube d (k : ℤ)))) α β)) P.toMeasure :=
      Finset.aestronglyMeasurable_fun_sum _ fun R _ =>
        (hIntA1 R α β).aestronglyMeasurable.sub aestronglyMeasurable_const
    exact hSumMeas.const_mul _
  have hFrobMeas : AEStronglyMeasurable (fun omega => akhcRelFrobSq
      (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))))
      (akhcCFSLinEntry nu L P k n omega)) P.toMeasure := by
    unfold akhcRelFrobSq
    refine Finset.aestronglyMeasurable_fun_sum _ fun α _ => ?_
    refine Finset.aestronglyMeasurable_fun_sum _ fun β _ => ?_
    exact ((continuous_pow 2).div_const _).comp_aestronglyMeasurable (hLinMeas α β)
  -- The second moment of `X`, from (P3')'s growth condition at `q := 2`, `p := pPsi`
  -- (package A3).
  have hAkey : (0 : ℝ) < omegaSeq k := homegaPos k
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h2ltpPsi : (2 : ℝ) < pPsi := by linarith only [hpPsi, hd2]
  have hp1 : (1 : ℝ) < pPsi := by linarith only [h2ltpPsi]
  have hq1 : (1 : ℝ) ≤ 2 := by norm_num
  have hXsqAbsInt := SuperdiffusionCLT.AKHC61.Carrier.akhc_integrable_abs_rpow_of_isBigO
    hKPsi hPsiOne hGrowthP3 hAkey hXm hXbig hp1 (le_refl pPsi) hq1 h2ltpPsi
  have hXsqBoundAbs := SuperdiffusionCLT.AKHC61.Carrier.akhc_moment_le_of_isBigO
    hKPsi hPsiOne hGrowthP3 hAkey hXm hXbig hp1 (le_refl pPsi) hq1 h2ltpPsi
  simp only [Real.rpow_two, sq_abs] at hXsqAbsInt hXsqBoundAbs
  -- The entrywise polarization bound, samplewise: `L(α,β)²/(wα wβ) ≤ X²`.
  have hFrobPtwise : ∀ omega : ShellSeq d,
      akhcRelFrobSq (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))))
          (akhcCFSLinEntry nu L P k n omega) ≤
        (2 * (d : ℝ)) ^ 2 * (X omega) ^ 2 := by
    intro omega
    have hptwise : ∀ α β : BlockCoord d,
        (akhcCFSLinEntry nu L P k n omega α β) ^ 2 /
            (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) α *
              akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) β) ≤
          (X omega) ^ 2 := by
      intro α β
      have hkey : ∀ c : ℝ, 2 * (c * akhcCFSLinEntry nu L P k n omega α β) ≤
          X omega * (c ^ 2 *
              akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) α +
            akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) β) := by
        intro c
        have h := hbil omega (c • blockBasis α) (blockBasis β)
        have hsumEq : (∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
            blockVecDot (c • blockBasis α) (blockMatVecMul (ofFullBlockMat
              (toFullBlockMat (coarseBlockMatrix (cubeSet R)
                  (coefficientCutoff nu omega L).toCoeffField) -
                toFullBlockMat (annealedBlockMatrix nu L P
                  (cubeSet (originCube d (k : ℤ)))))) (blockBasis β))) =
            c * ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
              (blockMatEntry (coarseBlockMatrix (cubeSet R)
                  (coefficientCutoff nu omega L).toCoeffField) α β -
                blockMatEntry (annealedBlockMatrix nu L P
                  (cubeSet (originCube d (k : ℤ)))) α β) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun R _ =>
            akhc_blockVecDot_smul_basis_ofFullBlockMat_sub _ _ c α β
        rw [hsumEq, akhc_blockVecDot_smul_basis_self, blockBasis_pairing] at h
        unfold akhcCFSLinEntry akhcMatDiag
        have hre : ((descendantsAtDepth (originCube d (n : ℤ)) (n - k)).card : ℝ)⁻¹ *
            (c * ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
              (blockMatEntry (coarseBlockMatrix (cubeSet R)
                  (coefficientCutoff nu omega L).toCoeffField) α β -
                blockMatEntry (annealedBlockMatrix nu L P
                  (cubeSet (originCube d (k : ℤ)))) α β)) =
            c * (((descendantsAtDepth (originCube d (n : ℤ)) (n - k)).card : ℝ)⁻¹ *
              ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
                (blockMatEntry (coarseBlockMatrix (cubeSet R)
                    (coefficientCutoff nu omega L).toCoeffField) α β -
                  blockMatEntry (annealedBlockMatrix nu L P
                    (cubeSet (originCube d (k : ℤ)))) α β)) := by ring
        rw [hre] at h
        exact h
      have hsq := akhc_sq_le_mul_of_forall_c
        (wα := akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) α)
        (wβ := akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) β)
        (X := X omega) (L := akhcCFSLinEntry nu L P k n omega α β) hkey
      rw [div_le_iff₀ (mul_pos (hwpos α) (hwpos β)), ← mul_assoc]
      exact hsq
    unfold akhcRelFrobSq
    calc ∑ α : BlockCoord d, ∑ β : BlockCoord d, (akhcCFSLinEntry nu L P k n omega α β) ^ 2 /
            (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) α *
              akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) β)
        ≤ ∑ _α : BlockCoord d, ∑ _β : BlockCoord d, (X omega) ^ 2 :=
          Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hptwise α β
      _ = (2 * (d : ℝ)) ^ 2 * (X omega) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, akhc_card_blockCoord, nsmul_eq_mul]
          push_cast
          ring
  have hMajInt : Integrable (fun omega => (2 * (d : ℝ)) ^ 2 * (X omega) ^ 2) P.toMeasure :=
    hXsqAbsInt.const_mul _
  have hFrobInt : Integrable (fun omega => akhcRelFrobSq
      (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))))
      (akhcCFSLinEntry nu L P k n omega)) P.toMeasure := by
    refine hMajInt.mono' hFrobMeas (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_of_nonneg (akhc_relFrobSq_nonneg hwpos _)]
    exact hFrobPtwise omega
  refine ⟨hFrobInt, ?_⟩
  calc ∫ omega, akhcRelFrobSq
          (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))))
          (akhcCFSLinEntry nu L P k n omega) ∂P.toMeasure
      ≤ ∫ omega, (2 * (d : ℝ)) ^ 2 * (X omega) ^ 2 ∂P.toMeasure :=
        integral_mono hFrobInt hMajInt hFrobPtwise
    _ = (2 * (d : ℝ)) ^ 2 * ∫ omega, (X omega) ^ 2 ∂P.toMeasure := integral_const_mul _ _
    _ ≤ (2 * (d : ℝ)) ^ 2 * ((pPsi / (pPsi - 2)) * KPsi ^ (3 * ⌈pPsi⌉₊ ^ 2) * omegaSeq k ^ 2) :=
        mul_le_mul_of_nonneg_left hXsqBoundAbs (by positivity)
    _ = (2 * (d : ℝ)) ^ 2 * ((pPsi / (pPsi - 2)) * KPsi ^ (3 * ⌈pPsi⌉₊ ^ 2)) * omegaSeq k ^ 2 := by
        ring

end

end SuperdiffusionCLT.AKHC61.Variance
