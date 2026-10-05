/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.Term2ScaleComparison
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section4.Mixing.AnnealedComparison
public import SuperdiffusionCLT.Section4.Mixing.TermsCombined

/-!
# mixTail: the deterministic per-cube bilinear bound for the gauge term

In the proof of
Proposition `p.mixing.P.three.prime`: the block form of the gauge term
`G_{-h}^t Aell(cu_n) G_{-h} - Aell(cu_n)` (`Term2ScaleComparison.lean`'s
`mixTerms_gaugeTermBlockForm` composed with `mixTerms_annealedBlockDiag`) is
tested against the `Aell`-normalized bilinear sandwich, using **only**
elementary Cauchy-Schwarz and the annealed contrast inequality `1 ≤
shom_ell(cu_n) * shom_{ell,*}^{-1}(cu_n)` (`one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar`,
proved unconditionally in `Section2/Annealed/InfiniteVolume.lean`) to absorb
the upper-block scalar `shom_ell(cu_n)` entirely -- no matrix square root, no
operator-norm bound on `hᵀh` beyond the elementary `vecDot_matVecMul_transpose`
identity.

## Main result

* `mixTail_gaugeTermMatrix_bilinear_le`: for every descendant cube `R` and
  test pair `(p, q)`,
  `2 p . (gaugeTermMatrix R) q ≤
    (4 * t * ‖h_R‖ + 2 * t^2 * ‖h_R‖^2) * (p . Aell p + q . Aell q)`,
  with `t := sigmaBarStarInvScalar nu ell P (cu_n)` and `h_R` the averaged
  stream increment on `R`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq finiteShellIncrement)

noncomputable section

variable {d : ℕ}

/-! ## Elementary bounds on the four bilinear pieces -/

private theorem mixTail_abs_vecDot_matVecMul_matTranspose_le (h : Mat d) (x y : Vec d) :
    |vecDot x (matVecMul (matTranspose h) y)| ≤ matrixOperatorNorm h * vecNorm x * vecNorm y := by
  rw [vecDot_matVecMul_transpose]
  calc |vecDot (matVecMul h x) y| ≤ vecNorm (matVecMul h x) * vecNorm y :=
        (abs_vecDot_le_vecNorm_mul_vecNorm (matVecMul h x) y)
    _ ≤ (matrixOperatorNorm h * vecNorm x) * vecNorm y :=
        mul_le_mul_of_nonneg_right (vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm h x)
          (vecNorm_nonneg y)
    _ = matrixOperatorNorm h * vecNorm x * vecNorm y := by ring

private theorem mixTail_abs_vecDot_matVecMul_le (h : Mat d) (x y : Vec d) :
    |vecDot x (matVecMul h y)| ≤ matrixOperatorNorm h * vecNorm x * vecNorm y := by
  calc |vecDot x (matVecMul h y)| ≤ vecNorm x * vecNorm (matVecMul h y) :=
        (abs_vecDot_le_vecNorm_mul_vecNorm x (matVecMul h y))
    _ ≤ vecNorm x * (matrixOperatorNorm h * vecNorm y) :=
        mul_le_mul_of_nonneg_left (vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm h y)
          (vecNorm_nonneg x)
    _ = matrixOperatorNorm h * vecNorm x * vecNorm y := by ring

private theorem mixTail_abs_vecDot_matVecMul_matTranspose_mul_le (h : Mat d) (x y : Vec d) :
    |vecDot x (matVecMul (matTranspose h * h) y)| ≤
      matrixOperatorNorm h * vecNorm x * (matrixOperatorNorm h * vecNorm y) := by
  rw [← matVecMul_mul, vecDot_matVecMul_transpose]
  calc |vecDot (matVecMul h x) (matVecMul h y)| ≤
        vecNorm (matVecMul h x) * vecNorm (matVecMul h y) :=
        (abs_vecDot_le_vecNorm_mul_vecNorm (matVecMul h x) (matVecMul h y))
    _ ≤ (matrixOperatorNorm h * vecNorm x) * (matrixOperatorNorm h * vecNorm y) :=
        mul_le_mul (vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm h x)
          (vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm h y) (vecNorm_nonneg _)
          (mul_nonneg (matrixOperatorNorm_nonneg h) (vecNorm_nonneg x))

/-! ## The explicit block form of the gauge term at a descendant cube -/

private theorem mixTail_gaugeTermMatrix_eq [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (ell L : ℕ) {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hJ4 : ShellLawJ4 d P) (n : ℤ) (R : Homogenization.TriadicCube d) :
    mixTerms_gaugeTermMatrix nu omega ell L P n R =
      { upperLeft :=
          sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) •
            (matTranspose (volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y)) *
              volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y))
        upperRight :=
          -(sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) •
            matTranspose (volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y)))
        lowerLeft :=
          -(sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) •
            volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y))
        lowerRight := 0 } := by
  show
    ofFullBlockMat
        (toFullBlockMat
            (blockMatMul (blockMatTranspose (blockG (-(volumeAverageMat (cubeSet R)
                  (fun y ↦ finiteShellIncrement omega ell L y)))))
              (blockMatMul (annealedBlockMatrix nu ell P (cubeSet (originCube d n)))
                (blockG (-(volumeAverageMat (cubeSet R)
                    (fun y ↦ finiteShellIncrement omega ell L y))))))
          - toFullBlockMat (annealedBlockMatrix nu ell P (cubeSet (originCube d n)))) = _
  rw [mixTerms_annealedBlockDiag hnu ell hJ4 n, mixTerms_gaugeTermBlockForm]

/-! ## The bilinear cross-term bound -/

/-- Real AM-GM for two nonnegative reals: `sqrt (a * b) ≤ (a + b) / 2`. -/
private theorem mixTail_sqrt_mul_le_add_div_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  rw [Real.sqrt_mul ha]
  nlinarith only [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- The cross-weighted Cauchy-Schwarz bound: if `vecNormSq x ≤ Ex / a`,
`vecNormSq y ≤ Ey / b` with `a, b > 0`, `a * b ≥ 1`, then
`M * ‖x‖ * ‖y‖ ≤ M * (Ex + Ey) / 2` for any `M ≥ 0`. -/
private theorem mixTail_cross_le {a b Ex Ey M : ℝ} (ha : 0 < a) (_hb : 0 < b) (hab : 1 ≤ a * b)
    (hEx : 0 ≤ Ex) (hEy : 0 ≤ Ey) (hM : 0 ≤ M) {x y : Vec d}
    (hx : vecNormSq x ≤ Ex / a) (hy : vecNormSq y ≤ Ey / b) :
    M * vecNorm x * vecNorm y ≤ M * (Ex + Ey) / 2 := by
  have hxs : vecNorm x ≤ Real.sqrt (Ex / a) := by
    rw [← Real.sqrt_sq (vecNorm_nonneg x)]
    exact Real.sqrt_le_sqrt (by rw [vecNorm_sq_eq_vecNormSq]; exact hx)
  have hys : vecNorm y ≤ Real.sqrt (Ey / b) := by
    rw [← Real.sqrt_sq (vecNorm_nonneg y)]
    exact Real.sqrt_le_sqrt (by rw [vecNorm_sq_eq_vecNormSq]; exact hy)
  have hprod : vecNorm x * vecNorm y ≤ Real.sqrt (Ex / a) * Real.sqrt (Ey / b) :=
    mul_le_mul hxs hys (vecNorm_nonneg y) (Real.sqrt_nonneg _)
  have heq : Real.sqrt (Ex / a) * Real.sqrt (Ey / b) = Real.sqrt (Ex / a * (Ey / b)) :=
    (Real.sqrt_mul (by positivity) _).symm
  have hle : Ex / a * (Ey / b) ≤ Ex * Ey := by
    rw [div_mul_div_comm]
    exact div_le_self (mul_nonneg hEx hEy) hab
  have hsqrtle : Real.sqrt (Ex / a * (Ey / b)) ≤ Real.sqrt (Ex * Ey) := Real.sqrt_le_sqrt hle
  have hamgm : Real.sqrt (Ex * Ey) ≤ (Ex + Ey) / 2 := mixTail_sqrt_mul_le_add_div_two hEx hEy
  have hstep : vecNorm x * vecNorm y ≤ (Ex + Ey) / 2 := by
    rw [heq] at hprod
    exact hprod.trans (hsqrtle.trans hamgm)
  calc M * vecNorm x * vecNorm y = M * (vecNorm x * vecNorm y) := by ring
    _ ≤ M * ((Ex + Ey) / 2) := mul_le_mul_of_nonneg_left hstep hM
    _ = M * (Ex + Ey) / 2 := by ring

/-- The equal-weight (diagonal) Cauchy-Schwarz bound: if `vecNormSq x ≤ Ex / a`,
`vecNormSq y ≤ Ey / a` with `a > 0`, then `M * ‖x‖ * ‖y‖ ≤ M * (Ex + Ey) / (2 * a)`
for any `M ≥ 0`. -/
private theorem mixTail_diag_le {a Ex Ey M : ℝ} (ha : 0 < a) (_hEx : 0 ≤ Ex) (_hEy : 0 ≤ Ey)
    (hM : 0 ≤ M) {x y : Vec d} (hx : vecNormSq x ≤ Ex / a) (hy : vecNormSq y ≤ Ey / a) :
    M * vecNorm x * vecNorm y ≤ M * (Ex + Ey) / (2 * a) := by
  have hxy : vecNorm x * vecNorm y ≤ (vecNormSq x + vecNormSq y) / 2 := by
    nlinarith only [sq_nonneg (vecNorm x - vecNorm y), vecNorm_sq_eq_vecNormSq x,
      vecNorm_sq_eq_vecNormSq y]
  have h2 : (vecNormSq x + vecNormSq y) / 2 ≤ (Ex / a + Ey / a) / 2 := by
    linarith only [hx, hy]
  have h3 : (Ex / a + Ey / a) / 2 = (Ex + Ey) / (2 * a) := by field_simp
  calc M * vecNorm x * vecNorm y = M * (vecNorm x * vecNorm y) := by ring
    _ ≤ M * ((Ex + Ey) / (2 * a)) := mul_le_mul_of_nonneg_left (hxy.trans (h2.trans_eq h3)) hM
    _ = M * (Ex + Ey) / (2 * a) := by ring

/-- **The fully abstract bilinear assembly.** Pure algebra, independent of the
gauge term / `Aell` machinery: given `s, t > 0` with `s * t ≥ 1`, and `Ep, Eqq
≥ 0` dominating the four block components of `p, q` in the stated weighted
sense, the `t`-scaled antisymmetric combination of the three Cauchy-Schwarz
pieces of the gauge term is controlled by `(4 t ‖h‖ + 2 t² ‖h‖²) (Ep + Eqq)`. -/
private theorem mixTail_bilinear_assembly {h : Mat d} {s t Ep Eqq : ℝ} (hspos : 0 < s)
    (htpos : 0 < t) (hst : 1 ≤ s * t) (hEpnn : 0 ≤ Ep) (hEqnn : 0 ≤ Eqq) {p1 p2 q1 q2 : Vec d}
    (hp1 : vecNormSq p1 ≤ Ep / s) (hp2 : vecNormSq p2 ≤ Ep / t) (hq1 : vecNormSq q1 ≤ Eqq / s)
    (hq2 : vecNormSq q2 ≤ Eqq / t) :
    2 * (t * vecDot p1 (matVecMul (matTranspose h * h) q1) -
        t * vecDot p1 (matVecMul (matTranspose h) q2) -
        t * vecDot p2 (matVecMul h q1)) ≤
      (4 * t * matrixOperatorNorm h + 2 * t ^ 2 * matrixOperatorNorm h ^ 2) * (Ep + Eqq) := by
  have hts : 1 ≤ t * s := by rwa [mul_comm]
  have hd1 : |vecDot p1 (matVecMul (matTranspose h * h) q1)| ≤
      matrixOperatorNorm h * vecNorm p1 * (matrixOperatorNorm h * vecNorm q1) :=
    mixTail_abs_vecDot_matVecMul_matTranspose_mul_le h p1 q1
  have hd2 : |vecDot p1 (matVecMul (matTranspose h) q2)| ≤
      matrixOperatorNorm h * vecNorm p1 * vecNorm q2 :=
    mixTail_abs_vecDot_matVecMul_matTranspose_le h p1 q2
  have hd3 : |vecDot p2 (matVecMul h q1)| ≤ matrixOperatorNorm h * vecNorm p2 * vecNorm q1 :=
    mixTail_abs_vecDot_matVecMul_le h p2 q1
  have hMnn : 0 ≤ matrixOperatorNorm h := matrixOperatorNorm_nonneg h
  have hcross1 : matrixOperatorNorm h * vecNorm p1 * vecNorm q2 ≤
      matrixOperatorNorm h * (Ep + Eqq) / 2 :=
    mixTail_cross_le hspos htpos hst hEpnn hEqnn hMnn hp1 hq2
  have hcross2 : matrixOperatorNorm h * vecNorm p2 * vecNorm q1 ≤
      matrixOperatorNorm h * (Ep + Eqq) / 2 :=
    mixTail_cross_le htpos hspos hts hEpnn hEqnn hMnn hp2 hq1
  have hdiag : matrixOperatorNorm h * vecNorm p1 * (matrixOperatorNorm h * vecNorm q1) ≤
      matrixOperatorNorm h ^ 2 * (Ep + Eqq) / (2 * s) := by
    have := mixTail_diag_le (a := s) (Ex := Ep) (Ey := Eqq) (M := matrixOperatorNorm h ^ 2)
      hspos hEpnn hEqnn (sq_nonneg (matrixOperatorNorm h)) hp1 hq1
    nlinarith only [this]
  have hXnn : 0 ≤ matrixOperatorNorm h ^ 2 * (Ep + Eqq) :=
    mul_nonneg (sq_nonneg (matrixOperatorNorm h)) (add_nonneg hEpnn hEqnn)
  have h2spos : 0 < 2 * s := by linarith only [hspos]
  have hdiag2 : matrixOperatorNorm h ^ 2 * (Ep + Eqq) / (2 * s) ≤
      t * (matrixOperatorNorm h ^ 2 * (Ep + Eqq)) := by
    rw [div_le_iff₀ h2spos]
    have hstX := mul_le_mul_of_nonneg_left hst hXnn
    nlinarith only [hstX, hXnn]
  have hbound1 := abs_le.mp hd1
  have hbound2 := abs_le.mp hd2
  have hbound3 := abs_le.mp hd3
  have hA : t * vecDot p1 (matVecMul (matTranspose h * h) q1) ≤
      t * (matrixOperatorNorm h * vecNorm p1 * (matrixOperatorNorm h * vecNorm q1)) :=
    mul_le_mul_of_nonneg_left hbound1.2 htpos.le
  have hB : -(t * vecDot p1 (matVecMul (matTranspose h) q2)) ≤
      t * (matrixOperatorNorm h * vecNorm p1 * vecNorm q2) := by
    have := mul_le_mul_of_nonneg_left (neg_le.mp hbound2.1) htpos.le
    linarith only [this]
  have hC : -(t * vecDot p2 (matVecMul h q1)) ≤
      t * (matrixOperatorNorm h * vecNorm p2 * vecNorm q1) := by
    have := mul_le_mul_of_nonneg_left (neg_le.mp hbound3.1) htpos.le
    linarith only [this]
  have hAle : t * (matrixOperatorNorm h * vecNorm p1 * (matrixOperatorNorm h * vecNorm q1)) ≤
      t * (matrixOperatorNorm h ^ 2 * (Ep + Eqq) / (2 * s)) :=
    mul_le_mul_of_nonneg_left hdiag htpos.le
  have hBle : t * (matrixOperatorNorm h * vecNorm p1 * vecNorm q2) ≤
      t * (matrixOperatorNorm h * (Ep + Eqq) / 2) :=
    mul_le_mul_of_nonneg_left hcross1 htpos.le
  have hCle : t * (matrixOperatorNorm h * vecNorm p2 * vecNorm q1) ≤
      t * (matrixOperatorNorm h * (Ep + Eqq) / 2) :=
    mul_le_mul_of_nonneg_left hcross2 htpos.le
  have hAle2 : t * (matrixOperatorNorm h ^ 2 * (Ep + Eqq) / (2 * s)) ≤
      t * (t * (matrixOperatorNorm h ^ 2 * (Ep + Eqq))) :=
    mul_le_mul_of_nonneg_left hdiag2 htpos.le
  have hAle2' : t * (t * (matrixOperatorNorm h ^ 2 * (Ep + Eqq))) =
      t ^ 2 * matrixOperatorNorm h ^ 2 * (Ep + Eqq) := by ring
  rw [hAle2'] at hAle2
  nlinarith only [hA, hB, hC, hAle, hBle, hCle, hAle2,
    mul_nonneg (mul_nonneg htpos.le hMnn) (add_nonneg hEpnn hEqnn)]

/-- **The deterministic per-cube bilinear bound.** For every descendant cube
`R` and test pair `(p, q)`, writing `t := sigmaBarStarInvScalar nu ell P
(cu_n)` and `‖h_R‖` for the operator norm of the averaged stream increment on
`R`:

`2 p . (gaugeTermMatrix R) q ≤
  (4 * t * ‖h_R‖ + 2 * t ^ 2 * ‖h_R‖ ^ 2) * (p . Aell p + q . Aell q)`.

Route: the explicit block form (`mixTail_gaugeTermMatrix_eq`), elementary
Cauchy-Schwarz on the three nonzero blocks, and the annealed contrast
inequality `1 ≤ shom_ell(cu_n) * shom_{ell,*}^{-1}(cu_n)`
(`one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar`) to eliminate the upper
block scalar `shom_ell(cu_n)` from the final bound entirely. -/
theorem mixTail_gaugeTermMatrix_bilinear_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (ell L : ℕ) {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (n : ℤ) (R : Homogenization.TriadicCube d) (p q : BlockVec d) :
    2 * blockVecDot p (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P n R) q) ≤
      (4 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) *
            matrixOperatorNorm (volumeAverageMat (cubeSet R)
              (fun y ↦ finiteShellIncrement omega ell L y)) +
          2 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) ^ 2 *
            matrixOperatorNorm (volumeAverageMat (cubeSet R)
              (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2) *
        (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P n) p) +
          blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P n) q)) := by
  set h : Mat d := volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y)
    with hhdef
  set s : ℝ := sigmaBarScalar nu ell P (cubeSet (originCube d n)) with hsdef
  set t : ℝ := sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) with htdef
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  have hspos : 0 < s := sigmaBarScalar_originCube_pos hnu ell hPrefix hJ2 hJ3 hJ4 n
  have htpos : 0 < t := sigmaBarStarInvScalar_pos_cutoff hnu ell hPrefix hJ2 hJ3 hJ4 n
  have hst : 1 ≤ s * t := one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar hnu ell hPrefix hJ2
    hJ3 hJ4 n
  have hts : 1 ≤ t * s := by rwa [mul_comm]
  clear_value h s t
  -- The bilinear value of the gauge term, explicitly.
  have hval :
      blockVecDot (p1, p2) (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P n R)
        (q1, q2)) =
        t * vecDot p1 (matVecMul (matTranspose h * h) q1) -
          t * vecDot p1 (matVecMul (matTranspose h) q2) -
          t * vecDot p2 (matVecMul h q1) := by
    rw [mixTail_gaugeTermMatrix_eq hnu omega ell L hJ4 n R]
    have hzero : matVecMul (0 : Mat d) q2 = 0 := by
      change (0 : Mat d).mulVec q2 = 0
      exact Matrix.zero_mulVec q2
    simp only [← hhdef, ← htdef, blockVecDot, blockMatVecMul_fst, blockMatVecMul_snd,
      vecDot_add_right, neg_matVecMul, vecDot_neg_right, smul_matVecMul, vecDot_smul_right,
      hzero, vecDot_zero_right]
    ring
  -- The `Aell` energy of `p` and `q`.
  have hEp : blockVecDot (p1, p2) (blockMatVecMul (mixTerms_Aell nu ell P n) (p1, p2)) =
      s * vecNormSq p1 + t * vecNormSq p2 := by
    rw [hsdef, htdef]
    unfold mixTerms_Aell
    exact mixMain_annealedBilinear_eq hnu ell hJ4 n (p1, p2)
  have hEq : blockVecDot (q1, q2) (blockMatVecMul (mixTerms_Aell nu ell P n) (q1, q2)) =
      s * vecNormSq q1 + t * vecNormSq q2 := by
    rw [hsdef, htdef]
    unfold mixTerms_Aell
    exact mixMain_annealedBilinear_eq hnu ell hJ4 n (q1, q2)
  set Ep : ℝ := blockVecDot (p1, p2) (blockMatVecMul (mixTerms_Aell nu ell P n) (p1, p2))
    with hEpdef
  set Eqq : ℝ := blockVecDot (q1, q2) (blockMatVecMul (mixTerms_Aell nu ell P n) (q1, q2))
    with hEqdef
  have hp1 : vecNormSq p1 ≤ Ep / s := by
    rw [hEp, le_div_iff₀ hspos]; nlinarith only [vecNormSq_nonneg p2, htpos.le]
  have hp2 : vecNormSq p2 ≤ Ep / t := by
    rw [hEp, le_div_iff₀ htpos]; nlinarith only [vecNormSq_nonneg p1, hspos.le]
  have hq1 : vecNormSq q1 ≤ Eqq / s := by
    rw [hEq, le_div_iff₀ hspos]; nlinarith only [vecNormSq_nonneg q2, htpos.le]
  have hq2 : vecNormSq q2 ≤ Eqq / t := by
    rw [hEq, le_div_iff₀ htpos]; nlinarith only [vecNormSq_nonneg q1, hspos.le]
  have hEpnn : 0 ≤ Ep := by
    rw [hEp]; exact add_nonneg (mul_nonneg hspos.le (vecNormSq_nonneg p1))
      (mul_nonneg htpos.le (vecNormSq_nonneg p2))
  have hEqnn : 0 ≤ Eqq := by
    rw [hEq]; exact add_nonneg (mul_nonneg hspos.le (vecNormSq_nonneg q1))
      (mul_nonneg htpos.le (vecNormSq_nonneg q2))
  clear_value Ep Eqq
  have hfinal := mixTail_bilinear_assembly (h := h) hspos htpos hst hEpnn hEqnn hp1 hp2 hq1 hq2
  rw [hval]
  linarith only [hfinal]

end

end SuperdiffusionCLT.Section4.Mixing
