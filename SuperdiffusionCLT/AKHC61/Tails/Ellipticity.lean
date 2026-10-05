/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocks
public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocksB

/-!
# Package C1: the (P2')-driven ellipticity tail of `M_{n,ρ}`

The ellipticity tail of [AK], `e.this.is.so.nice.again#tail-ellipticity-weaker` (in the proof
of `l.weaknorms.prime`), together with the definition `e.event.moreproto` of the event
quantity.

## Why the one-sided reading of `M_{n,ρ}` is used

The source's `M_{n,ρ}` displays (`e.event.moreproto`) only ever need the **one-sided** positive
part `|(S-I)_+|`, not a two-sided operator norm `|E^{-1/2} H E^{-1/2}|`. The two-sided norm cannot
be bounded from (P2') alone: (P2') (`a.ellipticity.weaker`, carried verbatim below as `hP2`) is a
**one-sided** Loewner bound — `BlockMatLoewnerLE (bfA(Q)) ((1+t)•bfAhom(cu_j))`, an upper bound
only. The two-sided operator norm `|M^{-1/2}EM^{-1/2}|` needs a **matching lower** Loewner bound
(`bfA(Q) ⪰ (1-t)•bfAhom(cu_j)`-shaped) to control the *smallest* eigenvalue of the conjugated
matrix, and (P2') supplies no such thing. This is a structural fact about the two-sided
definition.

**What this file proves instead.** The source's own `M_{n,ρ}` displays only ever need the
*one-sided* excess `|(S-I)_+|`, which is exactly what a one-sided Loewner bound controls, with no
matrix square root: in the statement of the main theorem the positive part in (P2') is
read as a one-sided Loewner bound, `|(S-I)_+| ≤ t ⟺ 0 ≤ t ∧ bfA ≤ (1+t)•bfAhom` for `t ≥ 0`.
This file formalizes that one-sided excess directly via a Loewner infimum (`akhcTailEll_excess`, no
`CFC.sqrt`), proves the source's tail-ellipticity-weaker chain for it (monotonicity of `Ahom` in
scale, from package A2, plus (P2') itself), and packages the result in the exact shape node 14
needs: a bound uniform in the summation scale `k`, ready for the second-moment step of
`EllipticityB.lean`.

**How this feeds C3.** C3's target (`E[M_{n,ρ}²]`, nodes 11/12) needs an upper bound on the
ellipticity part of `M_{n,ρ}`'s defining sSup, for the range of scales `k ≤ h'` (`h' := h + L1 log
(L2 h)` in the source). `akhcTailEll_normalized_excess_le` below supplies exactly this, *per term*:
for every sample and every cube `Q` with `Q.scale ≤ h'`, the `3^{-ρ(n-Q.scale)}`-weighted one-sided
excess relative to `bfAhom(cu_h)` is at most `3^{-(ρ-γ)(n-h')}·|X(ω)|`, uniformly in `Q`. With the
one-sided (print-faithful) reading of `M_{n,ρ}`, this closes node 14 completely after
`EllipticityB.lean`'s second-moment step. A two-sided reading would need an *additional*
lower-Loewner ellipticity ingredient that (P2') does not supply.

## Main results

* `akhcTailEll_excess`: the one-sided Loewner excess of `E` relative to `M`, `sInf {t ≥ 0 :
  E ≤ (1+t)•M}` — no matrix square root.
* `akhcTailEll_excess_le_of_blockMatLoewnerLE`: extracting an excess bound from a Loewner witness.
* `akhcTailEll_blockMatLoewnerLE_of_scale_le`: the pointwise (every sample) Loewner chain from
  (P2') at scale `n` plus A2's monotonicity of `Ahom`, transferred to reference scale `h`, for
  every cube `Q` with `Q.scale ≤ h'` (`h'` generic, any real `hprime` with `Q.scale ≤ hprime`).
* `akhcTailEll_normalized_excess_le`: the `3^{-ρ(n-Q.scale)}`-normalized, `Q`-uniform excess bound
  that is package C1's deliverable for C3.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Tails

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

/-! ## The one-sided Loewner excess, no matrix square root -/

/-- **The one-sided Loewner excess** of `E` relative to a reference `M`: the least `t ≥ 0` with
`E ≤ (1+t)•M` in the block Loewner order. For `M` positive-definite this equals the source's
`|(M^{-1/2}EM^{-1/2}-I)_+|` (the largest eigenvalue of the conjugated matrix, clipped at `0`),
by the standard correspondence the docstring of `Frozen.Section4.akhc_weakerP3` records;
that equivalence is not formalized here (it would reintroduce the eigenvalue/`CFC.sqrt`
machinery this file avoids), only
the one direction this package needs: a Loewner witness gives an excess bound. -/
def akhcTailEll_excess {d : ℕ} (M E : BlockMat d) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ BlockMatLoewnerLE E ((1 + t) • M)}

theorem akhcTailEll_excess_le_of_blockMatLoewnerLE {d : ℕ} {M E : BlockMat d} {t : ℝ}
    (ht : 0 ≤ t) (hL : BlockMatLoewnerLE E ((1 + t) • M)) :
    akhcTailEll_excess M E ≤ t := by
  have hbdd : BddBelow {t : ℝ | 0 ≤ t ∧ BlockMatLoewnerLE E ((1 + t) • M)} :=
    ⟨0, fun t' ht' => ht'.1⟩
  exact csInf_le hbdd ⟨ht, hL⟩

theorem akhcTailEll_excess_nonneg {d : ℕ} (M E : BlockMat d) :
    0 ≤ akhcTailEll_excess M E :=
  Real.sInf_nonneg fun _ ht => ht.1

/-! ## Section variables: the shell law, (P2') carried verbatim, and the shared scalars -/

variable {d : ℕ} [NeZero d] {nu : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {L : ℕ}
  (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  -- (P2') `a.ellipticity.weaker`, copied verbatim from
  -- `SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`.
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        cubeCenter Q ∈ cubeSet (originCube d (j : ℤ)) →
          BlockMatLoewnerLE
            (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              annealedBlockMatrix nu L P (cubeSet (originCube d (j : ℤ)))))

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

/-! ## The reference-transfer helper: same base scale, two coefficients or two scales -/

omit hPrefix hJ2 in
/-- **Scaling `Ahom(cu_j)` by two coefficients `c1 ≤ c2`** keeps the Loewner order, using A2's
block-diagonal decomposition (`akhc_annealedBlockMatrix_originCube_eq_blockDiag`) and the scalar
comparison `akhc_blockMatLoewnerLE_blockDiag_smul_one_iff`; no PSD-ness of `Ahom` needs to be
proved separately, since positivity of the two scalars (A2) is enough. -/
private theorem akhcTailEll_smul_annealed_le_smul_annealed {j : ℤ} {c1 c2 : ℝ} (hc : c1 ≤ c2) :
    BlockMatLoewnerLE (c1 • annealedBlockMatrix nu L P (cubeSet (originCube d j)))
      (c2 • annealedBlockMatrix nu L P (cubeSet (originCube d j))) := by
  have ha : 0 ≤ sigmaBarScalar nu L P (cubeSet (originCube d j)) :=
    (SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarScalar_originCube_pos_of_P2
      hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
      hpPsiS hGrowth hP2 j).le
  have hb : 0 ≤ sigmaBarStarInvScalar nu L P (cubeSet (originCube d j)) :=
    (SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarStarInvScalar_pos_of_P2
      hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
      hpPsiS hGrowth hP2 j).le
  rw [SuperdiffusionCLT.AKHC61.Carrier.akhc_annealedBlockMatrix_originCube_eq_blockDiag
        hnu L hJ4 j,
    blockSMul_blockDiag_smul_one, blockSMul_blockDiag_smul_one]
  exact SuperdiffusionCLT.AKHC61.Carrier.akhc_blockMatLoewnerLE_blockDiag_smul_one_iff.2
    ⟨mul_le_mul_of_nonneg_right hc ha, mul_le_mul_of_nonneg_right hc hb⟩

/-! ## The main pointwise Loewner chain -/

/-- **Package C1's core theorem.** From (P2') at scale `n` and A2's monotonicity of `Ahom` in
scale (`h ≤ n`), transferred to reference `Ahom(cu_h)`: for every sample and every cube `Q` with
`Q.scale ≤ n`, centre in `cu_n`, and `Q.scale ≤ hprime` (any real bound; the source's own choice
is `hprime := h + L1 log(L2 h)`, but nothing here needs that specific form), the ellipticity
excess of `bfA(Q)` relative to `Ahom(cu_h)`, weighted by `3^{ρ(n-Q.scale)}`, is at most
`3^{-(ρ-γ)(n-hprime)}·|X(ω)|`. This is the exact chain of
(`e.this.is.so.nice.again#tail-ellipticity-weaker`): the reference transfer uses
`bfAhom(cu_h) ⪰ bfAhom(cu_n)` (A2), and the exponent inequality uses only `γ ≤ ρ` and
`Q.scale ≤ hprime`. -/
theorem akhcTailEll_blockMatLoewnerLE_of_scale_le
    {n h : ℕ} (hhn : h ≤ n) (hn_m2 : m2 ≤ n) {rho hprime : ℝ} (hgammarho : gamma ≤ rho) :
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (n : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : TriadicCube d),
        Q.scale ≤ (n : ℤ) → (Q.scale : ℝ) ≤ hprime →
        cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) →
          BlockMatLoewnerLE
            (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^
                  (rho * ((n : ℝ) - (Q.scale : ℝ)) - (rho - gamma) * ((n : ℝ) - hprime)) *
                |X omega|) •
              annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ)))) := by
  obtain ⟨X, hXm, hXbig, hXloewner⟩ := hP2 n hn_m2
  refine ⟨X, hXm, hXbig, ?_⟩
  intro omega Q hQn hQhprime hQcenter
  set e1 : ℝ := -(gamma * ((Q.scale : ℝ) - (n : ℝ))) with he1
  set e2 : ℝ := rho * ((n : ℝ) - (Q.scale : ℝ)) - (rho - gamma) * ((n : ℝ) - hprime) with he2
  have hstep0 := hXloewner omega Q hQn hQcenter
  -- Step 1: `e1 ≤ e2`, from `γ ≤ ρ` and `Q.scale ≤ hprime`.
  have he12 : e1 ≤ e2 := by
    have hprod : (0 : ℝ) ≤ (rho - gamma) * (hprime - (Q.scale : ℝ)) :=
      mul_nonneg (by linarith only [hgammarho]) (by linarith only [hQhprime])
    have hexpand : e2 - e1 = (rho - gamma) * (hprime - (Q.scale : ℝ)) := by rw [he1, he2]; ring
    linarith only [hprod, hexpand]
  have hrpow_mono : (3 : ℝ) ^ e1 ≤ (3 : ℝ) ^ e2 :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) he12
  have hrpow1_nonneg : (0 : ℝ) ≤ (3 : ℝ) ^ e1 := Real.rpow_nonneg (by norm_num) _
  -- Step 2: `X ω ≤ |X ω|`, so `(3:ℝ)^e1 * X ω ≤ (3:ℝ)^e2 * |X ω|`.
  have hcoef_le : (3 : ℝ) ^ e1 * X omega ≤ (3 : ℝ) ^ e2 * |X omega| := by
    calc (3 : ℝ) ^ e1 * X omega ≤ (3 : ℝ) ^ e1 * |X omega| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hrpow1_nonneg
      _ ≤ (3 : ℝ) ^ e2 * |X omega| :=
          mul_le_mul_of_nonneg_right hrpow_mono (abs_nonneg _)
  -- Step 3: transfer from `(1 + ·)•Ahom(cu_n)` to `(1 + ·)•Ahom(cu_n)` with the larger coefficient.
  have hstep1 :
      BlockMatLoewnerLE ((1 + (3 : ℝ) ^ e1 * X omega) • annealedBlockMatrix nu L P
          (cubeSet (originCube d (n : ℤ))))
        ((1 + (3 : ℝ) ^ e2 * |X omega|) • annealedBlockMatrix nu L P
          (cubeSet (originCube d (n : ℤ)))) :=
    akhcTailEll_smul_annealed_le_smul_annealed hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
      hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
      (by linarith only [hcoef_le])
  -- Step 4: transfer the reference scale `n → h` (A2 monotonicity, scaled by the nonneg coefficient).
  have hmono :
      BlockMatLoewnerLE (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
        (annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ)))) :=
    SuperdiffusionCLT.AKHC61.Carrier.akhc_blockMatLoewnerLE_annealedBlockMatrix_originCube_of_P2
      hnu hPrefix hJ2 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne
      hKPsiS hpPsiS hGrowth hP2 (Int.natCast_nonneg h) (by exact_mod_cast hhn)
  have hcoef2_nonneg : (0 : ℝ) ≤ 1 + (3 : ℝ) ^ e2 * |X omega| := by
    have : (0 : ℝ) ≤ (3 : ℝ) ^ e2 * |X omega| :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (abs_nonneg _)
    linarith only [this]
  have hstep2 :
      BlockMatLoewnerLE ((1 + (3 : ℝ) ^ e2 * |X omega|) • annealedBlockMatrix nu L P
          (cubeSet (originCube d (n : ℤ))))
        ((1 + (3 : ℝ) ^ e2 * |X omega|) • annealedBlockMatrix nu L P
          (cubeSet (originCube d (h : ℤ)))) :=
    Homogenization.blockMatLoewnerLE_smul hcoef2_nonneg hmono
  have hfinal := hstep0.trans (hstep1.trans hstep2)
  rwa [he2] at hfinal

/-! ## The excess-valued corollaries -/

/-- **The excess-valued version** of `akhcTailEll_blockMatLoewnerLE_of_scale_le`, via
`akhcTailEll_excess_le_of_blockMatLoewnerLE`. -/
theorem akhcTailEll_excess_le
    {n h : ℕ} (hhn : h ≤ n) (hn_m2 : m2 ≤ n) {rho hprime : ℝ} (hgammarho : gamma ≤ rho) :
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (n : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : TriadicCube d),
        Q.scale ≤ (n : ℤ) → (Q.scale : ℝ) ≤ hprime →
        cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) →
          akhcTailEll_excess (annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ))))
              (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField) ≤
            (3 : ℝ) ^
              (rho * ((n : ℝ) - (Q.scale : ℝ)) - (rho - gamma) * ((n : ℝ) - hprime)) *
              |X omega| := by
  obtain ⟨X, hXm, hXbig, hloewner⟩ :=
    akhcTailEll_blockMatLoewnerLE_of_scale_le hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS
      hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hhn hn_m2 hgammarho
  refine ⟨X, hXm, hXbig, ?_⟩
  intro omega Q hQn hQhprime hQcenter
  have ht_nonneg :
      (0 : ℝ) ≤
        (3 : ℝ) ^ (rho * ((n : ℝ) - (Q.scale : ℝ)) - (rho - gamma) * ((n : ℝ) - hprime)) *
          |X omega| :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (abs_nonneg _)
  exact akhcTailEll_excess_le_of_blockMatLoewnerLE ht_nonneg
    (hloewner omega Q hQn hQhprime hQcenter)

/-- **Package C1's deliverable for C3.** The `3^{-ρ(n-Q.scale)}`-normalized excess — the exact
per-`Q` contribution to `M_{n,ρ}`'s defining sSup on the ellipticity range `Q.scale ≤ hprime` — is
bounded *uniformly in `Q`* by `3^{-(ρ-γ)(n-hprime)}·|X(ω)|`. The `3^{ρ(n-Q.scale)}` and
`3^{-ρ(n-Q.scale)}` factors cancel exactly (`Real.rpow_add`), which is why the bound no longer
depends on `Q.scale`: this is the mechanism the source's choice of `ρ` (with `ρ > γ`) is designed
for, restated with `γ ≤ ρ` generic. -/
theorem akhcTailEll_normalized_excess_le
    {n h : ℕ} (hhn : h ≤ n) (hn_m2 : m2 ≤ n) {rho hprime : ℝ} (hgammarho : gamma ≤ rho) :
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (n : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : TriadicCube d),
        Q.scale ≤ (n : ℤ) → (Q.scale : ℝ) ≤ hprime →
        cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) →
          (3 : ℝ) ^ (-(rho * ((n : ℝ) - (Q.scale : ℝ)))) *
              akhcTailEll_excess (annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ))))
                (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField) ≤
            (3 : ℝ) ^ (-(rho - gamma) * ((n : ℝ) - hprime)) * |X omega| := by
  obtain ⟨X, hXm, hXbig, hexcess⟩ :=
    akhcTailEll_excess_le hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
      hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hhn hn_m2 hgammarho
  refine ⟨X, hXm, hXbig, ?_⟩
  intro omega Q hQn hQhprime hQcenter
  have he := hexcess omega Q hQn hQhprime hQcenter
  have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-(rho * ((n : ℝ) - (Q.scale : ℝ)))) :=
    Real.rpow_nonneg (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_left he hw
  have hcombine :
      (3 : ℝ) ^ (-(rho * ((n : ℝ) - (Q.scale : ℝ)))) *
          ((3 : ℝ) ^
              (rho * ((n : ℝ) - (Q.scale : ℝ)) - (rho - gamma) * ((n : ℝ) - hprime)) *
            |X omega|) =
        (3 : ℝ) ^ (-(rho - gamma) * ((n : ℝ) - hprime)) * |X omega| := by
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 2
    ring
  rwa [hcombine] at hmul

end

end SuperdiffusionCLT.AKHC61.Tails
