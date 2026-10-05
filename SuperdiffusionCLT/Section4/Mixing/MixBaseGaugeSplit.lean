/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.TermGaugeFinalB
public import SuperdiffusionCLT.Section4.Mixing.MixBaseSplit

/-!
# `hBase` ingredient: the separate Cauchy-Schwarz bounds for `MixBaseSplit.lean`'s `F1`/`F2`

This file belongs to the proof of `p.mixing.P.three.prime` (Section 4): it is a step in `hBase`,
the bounded-gap base case of `mixWlog_smallGapFromBaseB` (`Section4/Mixing/MixWlogWrapperB.lean`).
`Section4/Mixing/MixBaseSplit.lean` provides the full pointwise `F1 + F2 + F3 =` (coarse-vs-`AL`)
decomposition (`mixBase_sum_eq`) and translation covariance for the pieces `F1`, `F2`
(`mixBase_F1_hFcov`, `mixBase_F2_hFcov`). The analytic (`IsBigO`) half is not part of that
file: the deterministic per-cube (or per-average) `Γ2`/`Γ1` bilinear bounds
`2 * avg F1 ≤ X1 * Q_ell`, `2 * avg F2 ≤ X2 * Q_ell` separately need a fresh Cauchy-Schwarz
argument.

This file supplies exactly that piece, directly for `MixBaseSplit.lean`'s `mixBase_F1`,
`mixBase_F2`.

`TermGaugeAssembly.lean`/`TermGaugeFinalB.lean` bound the WHOLE gauge term
`mixTerms_gaugeTermMatrix` by a coefficient SUM `(X1g+X2g+X3g)* (Aell-energy)`, not by
separately-bounded matrix pieces; collapsing `F1`, `F2` into one witness would lose the sharper
`Γ₂`/`Γ₁` rates that the statement of `p.mixing.P.three.prime` separately requires
(see `MixWlogWrapperB.lean`). `MixBaseSplit.lean`'s `mixBase_F2 := t·⟪p1, hᵀh q1⟫`
(quadratic in `h`) and `mixBase_F1 := -t·(⟪p1, hᵀ q2⟫ + ⟪p2, h q1⟫)` (linear in `h`), with
`t := sigmaBarStarInvScalar nu ell P (cu_n)`,
`h := volumeAverageMat (cubeSet R) (finiteShellIncrement omega ell L)`.

`Step 3` reproves the Cauchy-Schwarz cross/diagonal bounds of `TermGaugeBilinear.lean` (there
`private`, hence file-scoped) under this file's own names, then assembles TWO separate per-cube
bilinear bounds (rather than `TermGaugeBilinear.lean`'s one combined bound): `2·F2 ≤
2t²‖h‖²·(Ep+Eqq)` (sharp) and `2·F1 ≤ 4t‖h‖·(Ep+Eqq)` (the coefficient `4t‖h‖` of the combined
bound, though the tight bound from the two cross terms alone is `2t‖h‖`; `4t‖h‖` is kept so that
the `X1`-side coefficient matches `mixGaugeFinal_Y1_isBigO`'s `4·Y1` convention exactly).

`Step 4` averages each per-cube bound over `R ∈ descendantsAtDepth (originCube d m) (m-n)` by
plain `Finset` algebra (no need for the `IsBigO`-averaging machinery: the averaged bound is stated
at the *raw* `mixGaugeFinal_Y1`/`Y2` coefficients, whose `Γ₂`/`Γ₁` Orlicz bounds are
`TermGaugeFinal.lean`'s `mixGaugeFinal_Y1_isBigO`/`mixGaugeFinal_Y2_isBigO`). This gives the
`descendantsAverage`-shaped bilinear bound that `hBase`'s conclusion needs for `F1`, `F2`
separately, at `Aell`-normalization. The `ell → L` scalar and quadratic-form conversions,
`MixBaseSplit.lean`'s `F3` bound, the choice of `ell`, and the final `hBase` assembly are
separate steps, not carried out in this file.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq finiteShellIncrement)

noncomputable section

variable {d : ℕ}

/-! ## Step 3: the per-cube Cauchy-Schwarz bounds, split -/

private theorem mixBase_abs_vecDot_matVecMul_matTranspose_le (h : Mat d) (x y : Vec d) :
    |vecDot x (matVecMul (matTranspose h) y)| ≤ matrixOperatorNorm h * vecNorm x * vecNorm y := by
  rw [vecDot_matVecMul_transpose]
  calc |vecDot (matVecMul h x) y| ≤ vecNorm (matVecMul h x) * vecNorm y :=
        (abs_vecDot_le_vecNorm_mul_vecNorm (matVecMul h x) y)
    _ ≤ (matrixOperatorNorm h * vecNorm x) * vecNorm y :=
        mul_le_mul_of_nonneg_right (vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm h x)
          (vecNorm_nonneg y)
    _ = matrixOperatorNorm h * vecNorm x * vecNorm y := by ring

private theorem mixBase_abs_vecDot_matVecMul_le (h : Mat d) (x y : Vec d) :
    |vecDot x (matVecMul h y)| ≤ matrixOperatorNorm h * vecNorm x * vecNorm y := by
  calc |vecDot x (matVecMul h y)| ≤ vecNorm x * vecNorm (matVecMul h y) :=
        (abs_vecDot_le_vecNorm_mul_vecNorm x (matVecMul h y))
    _ ≤ vecNorm x * (matrixOperatorNorm h * vecNorm y) :=
        mul_le_mul_of_nonneg_left (vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm h y)
          (vecNorm_nonneg x)
    _ = matrixOperatorNorm h * vecNorm x * vecNorm y := by ring

private theorem mixBase_abs_vecDot_matVecMul_matTranspose_mul_le (h : Mat d) (x y : Vec d) :
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

private theorem mixBase_sqrt_mul_le_add_div_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  rw [Real.sqrt_mul ha]
  nlinarith only [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]

private theorem mixBase_cross_le {a b Ex Ey M : ℝ} (ha : 0 < a) (_hb : 0 < b) (hab : 1 ≤ a * b)
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
  have hamgm : Real.sqrt (Ex * Ey) ≤ (Ex + Ey) / 2 := mixBase_sqrt_mul_le_add_div_two hEx hEy
  have hstep : vecNorm x * vecNorm y ≤ (Ex + Ey) / 2 := by
    rw [heq] at hprod
    exact hprod.trans (hsqrtle.trans hamgm)
  calc M * vecNorm x * vecNorm y = M * (vecNorm x * vecNorm y) := by ring
    _ ≤ M * ((Ex + Ey) / 2) := mul_le_mul_of_nonneg_left hstep hM
    _ = M * (Ex + Ey) / 2 := by ring

private theorem mixBase_diag_le {a Ex Ey M : ℝ} (ha : 0 < a) (_hEx : 0 ≤ Ex) (_hEy : 0 ≤ Ey)
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

/-- **The quadratic-piece per-cube bound.** `2·(t·⟪p1, hᵀh q1⟫) ≤
2t²‖h‖²·(Ep+Eqq)`, sharp (this is exactly the diagonal step of
`TermGaugeBilinear.lean`'s combined `mixTail_bilinear_assembly`, isolated). -/
private theorem mixBase_quadPart_bound {h : Mat d} {s t Ep Eqq : ℝ} (hspos : 0 < s)
    (htpos : 0 < t) (hst : 1 ≤ s * t) (hEpnn : 0 ≤ Ep) (hEqnn : 0 ≤ Eqq) {p1 q1 : Vec d}
    (hp1 : vecNormSq p1 ≤ Ep / s) (hq1 : vecNormSq q1 ≤ Eqq / s) :
    2 * (t * vecDot p1 (matVecMul (matTranspose h * h) q1)) ≤
      2 * t ^ 2 * matrixOperatorNorm h ^ 2 * (Ep + Eqq) := by
  have hd1 : |vecDot p1 (matVecMul (matTranspose h * h) q1)| ≤
      matrixOperatorNorm h * vecNorm p1 * (matrixOperatorNorm h * vecNorm q1) :=
    mixBase_abs_vecDot_matVecMul_matTranspose_mul_le h p1 q1
  have hdiag : matrixOperatorNorm h * vecNorm p1 * (matrixOperatorNorm h * vecNorm q1) ≤
      matrixOperatorNorm h ^ 2 * (Ep + Eqq) / (2 * s) := by
    have := mixBase_diag_le (a := s) (Ex := Ep) (Ey := Eqq) (M := matrixOperatorNorm h ^ 2)
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
  have hA : t * vecDot p1 (matVecMul (matTranspose h * h) q1) ≤
      t * (matrixOperatorNorm h * vecNorm p1 * (matrixOperatorNorm h * vecNorm q1)) :=
    mul_le_mul_of_nonneg_left hbound1.2 htpos.le
  have hAle : t * (matrixOperatorNorm h * vecNorm p1 * (matrixOperatorNorm h * vecNorm q1)) ≤
      t * (matrixOperatorNorm h ^ 2 * (Ep + Eqq) / (2 * s)) :=
    mul_le_mul_of_nonneg_left hdiag htpos.le
  have hAle2 : t * (matrixOperatorNorm h ^ 2 * (Ep + Eqq) / (2 * s)) ≤
      t * (t * (matrixOperatorNorm h ^ 2 * (Ep + Eqq))) :=
    mul_le_mul_of_nonneg_left hdiag2 htpos.le
  have hAle2' : t * (t * (matrixOperatorNorm h ^ 2 * (Ep + Eqq))) =
      t ^ 2 * matrixOperatorNorm h ^ 2 * (Ep + Eqq) := by ring
  nlinarith only [hA, hAle, hAle2, hAle2']

/-- **The linear-piece per-cube bound.** `2·(-t·(⟪p1,hᵀq2⟫+⟪p2,hq1⟫)) ≤
4t‖h‖·(Ep+Eqq)` (the tight bound from the two cross terms alone is
`2t‖h‖·(Ep+Eqq)`; stated here at `4t‖h‖` — a valid weakening — to match
`mixGaugeFinal_Y1_isBigO`'s `4·Y1` convention exactly). -/
private theorem mixBase_linPart_bound {h : Mat d} {s t Ep Eqq : ℝ} (hspos : 0 < s)
    (htpos : 0 < t) (hst : 1 ≤ s * t) (hts : 1 ≤ t * s) (hEpnn : 0 ≤ Ep) (hEqnn : 0 ≤ Eqq)
    {p1 p2 q1 q2 : Vec d} (hp1 : vecNormSq p1 ≤ Ep / s) (hp2 : vecNormSq p2 ≤ Ep / t)
    (hq1 : vecNormSq q1 ≤ Eqq / s) (hq2 : vecNormSq q2 ≤ Eqq / t) :
    2 * (-t * (vecDot p1 (matVecMul (matTranspose h) q2) + vecDot p2 (matVecMul h q1))) ≤
      4 * t * matrixOperatorNorm h * (Ep + Eqq) := by
  have hd2 : |vecDot p1 (matVecMul (matTranspose h) q2)| ≤
      matrixOperatorNorm h * vecNorm p1 * vecNorm q2 :=
    mixBase_abs_vecDot_matVecMul_matTranspose_le h p1 q2
  have hd3 : |vecDot p2 (matVecMul h q1)| ≤ matrixOperatorNorm h * vecNorm p2 * vecNorm q1 :=
    mixBase_abs_vecDot_matVecMul_le h p2 q1
  have hMnn : 0 ≤ matrixOperatorNorm h := matrixOperatorNorm_nonneg h
  have hcross1 : matrixOperatorNorm h * vecNorm p1 * vecNorm q2 ≤
      matrixOperatorNorm h * (Ep + Eqq) / 2 :=
    mixBase_cross_le hspos htpos hst hEpnn hEqnn hMnn hp1 hq2
  have hcross2 : matrixOperatorNorm h * vecNorm p2 * vecNorm q1 ≤
      matrixOperatorNorm h * (Ep + Eqq) / 2 :=
    mixBase_cross_le htpos hspos hts hEpnn hEqnn hMnn hp2 hq1
  have hbound2 := abs_le.mp hd2
  have hbound3 := abs_le.mp hd3
  have hB : -(t * vecDot p1 (matVecMul (matTranspose h) q2)) ≤
      t * (matrixOperatorNorm h * vecNorm p1 * vecNorm q2) := by
    have := mul_le_mul_of_nonneg_left (neg_le.mp hbound2.1) htpos.le
    linarith only [this]
  have hC : -(t * vecDot p2 (matVecMul h q1)) ≤
      t * (matrixOperatorNorm h * vecNorm p2 * vecNorm q1) := by
    have := mul_le_mul_of_nonneg_left (neg_le.mp hbound3.1) htpos.le
    linarith only [this]
  have hBle : t * (matrixOperatorNorm h * vecNorm p1 * vecNorm q2) ≤
      t * (matrixOperatorNorm h * (Ep + Eqq) / 2) :=
    mul_le_mul_of_nonneg_left hcross1 htpos.le
  have hCle : t * (matrixOperatorNorm h * vecNorm p2 * vecNorm q1) ≤
      t * (matrixOperatorNorm h * (Ep + Eqq) / 2) :=
    mul_le_mul_of_nonneg_left hcross2 htpos.le
  nlinarith only [hB, hC, hBle, hCle,
    mul_nonneg (mul_nonneg htpos.le hMnn) (add_nonneg hEpnn hEqnn)]

/-- **The per-cube `F2` bilinear bound**, in the `BlockVec`/`Aell` carrier:
`2·F2(R,ω,p,q) ≤ 2t²‖h_R‖²·(Ep+Eqq)`, `t := sigmaBarStarInvScalar nu ell P
(cu_n)`, `Ep, Eqq` the `Aell`-energies of `p, q`, `F2 := MixBaseSplit.lean`'s
`mixBase_F2`. Same route as `TermGaugeBilinear.lean`'s
`mixTail_gaugeTermMatrix_bilinear_le`, isolating the diagonal contribution. -/
theorem mixBase_F2_bilinear_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (ell L : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (n : ℤ) (R : Homogenization.TriadicCube d) (p q : BlockVec d) :
    2 * mixBase_F2 nu ell L P n R omega p q ≤
      2 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) ^ 2 *
          matrixOperatorNorm (volumeAverageMat (cubeSet R)
            (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2 *
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
  clear_value h s t
  have hEp : blockVecDot (p1, p2) (blockMatVecMul (mixTerms_Aell nu ell P n) (p1, p2)) =
      s * vecNormSq p1 + t * vecNormSq p2 := by
    rw [hsdef, htdef]; unfold mixTerms_Aell
    exact mixMain_annealedBilinear_eq hnu ell hJ4 n (p1, p2)
  have hEq : blockVecDot (q1, q2) (blockMatVecMul (mixTerms_Aell nu ell P n) (q1, q2)) =
      s * vecNormSq q1 + t * vecNormSq q2 := by
    rw [hsdef, htdef]; unfold mixTerms_Aell
    exact mixMain_annealedBilinear_eq hnu ell hJ4 n (q1, q2)
  set Ep : ℝ := blockVecDot (p1, p2) (blockMatVecMul (mixTerms_Aell nu ell P n) (p1, p2))
    with hEpdef
  set Eqq : ℝ := blockVecDot (q1, q2) (blockMatVecMul (mixTerms_Aell nu ell P n) (q1, q2))
    with hEqdef
  have hp1 : vecNormSq p1 ≤ Ep / s := by
    rw [hEp, le_div_iff₀ hspos]; nlinarith only [vecNormSq_nonneg p2, htpos.le]
  have hq1 : vecNormSq q1 ≤ Eqq / s := by
    rw [hEq, le_div_iff₀ hspos]; nlinarith only [vecNormSq_nonneg q2, htpos.le]
  have hEpnn : 0 ≤ Ep := by
    rw [hEp]; exact add_nonneg (mul_nonneg hspos.le (vecNormSq_nonneg p1))
      (mul_nonneg htpos.le (vecNormSq_nonneg p2))
  have hEqnn : 0 ≤ Eqq := by
    rw [hEq]; exact add_nonneg (mul_nonneg hspos.le (vecNormSq_nonneg q1))
      (mul_nonneg htpos.le (vecNormSq_nonneg q2))
  clear_value Ep Eqq
  have hfinal := mixBase_quadPart_bound (h := h) hspos htpos hst hEpnn hEqnn hp1 hq1
  show 2 * mixBase_F2 nu ell L P n R omega (p1, p2) (q1, q2) ≤
    2 * t ^ 2 * matrixOperatorNorm h ^ 2 * (Ep + Eqq)
  unfold mixBase_F2
  simp only [← hhdef, ← htdef]
  linarith only [hfinal]

/-- **The per-cube `F1` bilinear bound**, in the `BlockVec`/`Aell` carrier:
`2·F1(R,ω,p,q) ≤ 4t‖h_R‖·(Ep+Eqq)`, `F1 := MixBaseSplit.lean`'s
`mixBase_F1`. -/
theorem mixBase_F1_bilinear_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (ell L : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (n : ℤ) (R : Homogenization.TriadicCube d) (p q : BlockVec d) :
    2 * mixBase_F1 nu ell L P n R omega p q ≤
      4 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) *
          matrixOperatorNorm (volumeAverageMat (cubeSet R)
            (fun y ↦ finiteShellIncrement omega ell L y)) *
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
  have hEp : blockVecDot (p1, p2) (blockMatVecMul (mixTerms_Aell nu ell P n) (p1, p2)) =
      s * vecNormSq p1 + t * vecNormSq p2 := by
    rw [hsdef, htdef]; unfold mixTerms_Aell
    exact mixMain_annealedBilinear_eq hnu ell hJ4 n (p1, p2)
  have hEq : blockVecDot (q1, q2) (blockMatVecMul (mixTerms_Aell nu ell P n) (q1, q2)) =
      s * vecNormSq q1 + t * vecNormSq q2 := by
    rw [hsdef, htdef]; unfold mixTerms_Aell
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
  have hfinal := mixBase_linPart_bound (h := h) hspos htpos hst hts hEpnn hEqnn hp1 hp2 hq1 hq2
  show 2 * mixBase_F1 nu ell L P n R omega (p1, p2) (q1, q2) ≤
    4 * t * matrixOperatorNorm h * (Ep + Eqq)
  unfold mixBase_F1
  simp only [← hhdef, ← htdef]
  linarith only [hfinal]

/-! ## Step 4: averaging over `R`, at the raw `Y1`/`Y2` coefficients -/

/-- **The `R`-averaged `F2` bound**, at the raw `mixGaugeFinal_Y2`
coefficient (`Aell`-normalized; the `ell → L` conversion is a separate, later
step). Plain `Finset` algebra from `mixBase_F2_bilinear_le`, no
`IsBigO`-averaging machinery needed. -/
theorem mixBase_F2_avg_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (ell L n m : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (p q : BlockVec d) :
    2 * descendantsAverage (originCube d (m : ℤ)) (m - n)
        (fun R ↦ mixBase_F2 nu ell L P (n : ℤ) R omega p q) ≤
      2 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) ^ 2 *
          mixGaugeFinal_Y2 omega ell L n m *
        (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
          blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := by
  set s := descendantsAtDepth (originCube d (m : ℤ)) (m - n) with hsdef
  have hpc : ∀ R ∈ s, 2 * mixBase_F2 nu ell L P (n : ℤ) R omega p q ≤
      2 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) ^ 2 *
          matrixOperatorNorm (volumeAverageMat (cubeSet R)
            (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2 *
        (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
          blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := fun R _ ↦
    mixBase_F2_bilinear_le hnu omega ell L hPrefix hJ2 hJ3 hJ4 (n : ℤ) R p q
  have hsum : ∑ R ∈ s, 2 * mixBase_F2 nu ell L P (n : ℤ) R omega p q ≤
      ∑ R ∈ s, 2 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) ^ 2 *
          matrixOperatorNorm (volumeAverageMat (cubeSet R)
            (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2 *
        (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
          blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) :=
    Finset.sum_le_sum hpc
  have hrw2 : ∑ R ∈ s, 2 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) ^ 2 *
          matrixOperatorNorm (volumeAverageMat (cubeSet R)
            (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2 *
        (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
          blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) =
      (∑ R ∈ s, matrixOperatorNorm (volumeAverageMat (cubeSet R)
          (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2) *
        (2 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) ^ 2 *
          (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
            blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q))) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun R _ ↦ by ring
  rw [hrw2] at hsum
  have hcard_inv_nonneg : (0 : ℝ) ≤ (s.card : ℝ)⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hcard_inv_nonneg
  have hlhs : (s.card : ℝ)⁻¹ * ∑ R ∈ s, 2 * mixBase_F2 nu ell L P (n : ℤ) R omega p q =
      2 * ((s.card : ℝ)⁻¹ * ∑ R ∈ s, mixBase_F2 nu ell L P (n : ℤ) R omega p q) := by
    rw [← Finset.mul_sum]; ring
  rw [hlhs] at hscaled
  show 2 * ((s.card : ℝ)⁻¹ * ∑ R ∈ s, mixBase_F2 nu ell L P (n : ℤ) R omega p q) ≤ _
  rw [show mixGaugeFinal_Y2 omega ell L n m =
      (s.card : ℝ)⁻¹ * ∑ R ∈ s, matrixOperatorNorm (volumeAverageMat (cubeSet R)
        (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2 from rfl]
  calc 2 * ((s.card : ℝ)⁻¹ * ∑ R ∈ s, mixBase_F2 nu ell L P (n : ℤ) R omega p q) ≤
      (s.card : ℝ)⁻¹ *
        ((∑ R ∈ s, matrixOperatorNorm (volumeAverageMat (cubeSet R)
            (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2) *
          (2 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) ^ 2 *
            (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
              blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)))) := hscaled
    _ = 2 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) ^ 2 *
          ((s.card : ℝ)⁻¹ * ∑ R ∈ s, matrixOperatorNorm (volumeAverageMat (cubeSet R)
            (fun y ↦ finiteShellIncrement omega ell L y)) ^ 2) *
        (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
          blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := by ring

/-- **The `R`-averaged `F1` bound**, at the raw `mixGaugeFinal_Y1`
coefficient (`Aell`-normalized). Same route as `mixBase_F2_avg_le`. -/
theorem mixBase_F1_avg_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (ell L n m : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (p q : BlockVec d) :
    2 * descendantsAverage (originCube d (m : ℤ)) (m - n)
        (fun R ↦ mixBase_F1 nu ell L P (n : ℤ) R omega p q) ≤
      4 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
          mixGaugeFinal_Y1 omega ell L n m *
        (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
          blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := by
  set s := descendantsAtDepth (originCube d (m : ℤ)) (m - n) with hsdef
  have hpc : ∀ R ∈ s, 2 * mixBase_F1 nu ell L P (n : ℤ) R omega p q ≤
      4 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
          matrixOperatorNorm (volumeAverageMat (cubeSet R)
            (fun y ↦ finiteShellIncrement omega ell L y)) *
        (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
          blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := fun R _ ↦
    mixBase_F1_bilinear_le hnu omega ell L hPrefix hJ2 hJ3 hJ4 (n : ℤ) R p q
  have hsum : ∑ R ∈ s, 2 * mixBase_F1 nu ell L P (n : ℤ) R omega p q ≤
      ∑ R ∈ s, 4 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
          matrixOperatorNorm (volumeAverageMat (cubeSet R)
            (fun y ↦ finiteShellIncrement omega ell L y)) *
        (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
          blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) :=
    Finset.sum_le_sum hpc
  have hrw2 : ∑ R ∈ s, 4 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
          matrixOperatorNorm (volumeAverageMat (cubeSet R)
            (fun y ↦ finiteShellIncrement omega ell L y)) *
        (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
          blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) =
      (∑ R ∈ s, matrixOperatorNorm (volumeAverageMat (cubeSet R)
          (fun y ↦ finiteShellIncrement omega ell L y))) *
        (4 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
          (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
            blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q))) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun R _ ↦ by ring
  rw [hrw2] at hsum
  have hcard_inv_nonneg : (0 : ℝ) ≤ (s.card : ℝ)⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hcard_inv_nonneg
  have hlhs : (s.card : ℝ)⁻¹ * ∑ R ∈ s, 2 * mixBase_F1 nu ell L P (n : ℤ) R omega p q =
      2 * ((s.card : ℝ)⁻¹ * ∑ R ∈ s, mixBase_F1 nu ell L P (n : ℤ) R omega p q) := by
    rw [← Finset.mul_sum]; ring
  rw [hlhs] at hscaled
  show 2 * ((s.card : ℝ)⁻¹ * ∑ R ∈ s, mixBase_F1 nu ell L P (n : ℤ) R omega p q) ≤ _
  rw [show mixGaugeFinal_Y1 omega ell L n m =
      (s.card : ℝ)⁻¹ * ∑ R ∈ s, matrixOperatorNorm (volumeAverageMat (cubeSet R)
        (fun y ↦ finiteShellIncrement omega ell L y)) from rfl]
  calc 2 * ((s.card : ℝ)⁻¹ * ∑ R ∈ s, mixBase_F1 nu ell L P (n : ℤ) R omega p q) ≤
      (s.card : ℝ)⁻¹ *
        ((∑ R ∈ s, matrixOperatorNorm (volumeAverageMat (cubeSet R)
            (fun y ↦ finiteShellIncrement omega ell L y))) *
          (4 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
            (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
              blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)))) := hscaled
    _ = 4 * sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
          ((s.card : ℝ)⁻¹ * ∑ R ∈ s, matrixOperatorNorm (volumeAverageMat (cubeSet R)
            (fun y ↦ finiteShellIncrement omega ell L y))) *
        (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
          blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := by ring

end

end SuperdiffusionCLT.Section4.Mixing
