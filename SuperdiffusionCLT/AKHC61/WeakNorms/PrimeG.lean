/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.PrimeF

/-!
# Package C6, part 7: the Step 2 `J`-bound in the source's `M₀` normalization

The Step 2 skeleton (`AKHC61/Step2/JBoundSkeleton.lean`) measures the weak norms by
`W = σ̄_k E[G²] + σ̄*⁻¹_k E[F²]`. The source's weight is `M₀ = diag(m₀, m₀⁻¹)` with
`m₀ = b₀ # s_{*,0}`, i.e. `W_src = σ̂_k E[G²] + σ̂_k⁻¹ E[F²]`, and
`W = Θ_k^{1/2} W_src`. The source proves only `W_src ≤ C δσ² Θ_m`, so the
skeleton's `hWeak : W ≤ K_w δσ² Θ_m` asks for `Θ_k^{1/2}` more than the manuscript gives.

This file re-runs the skeleton's closing arithmetic with the sharp centering bounds
`|q₀|² ≤ Θ^{1/2} σ̄ = Θ σ̂`, `|p₀|² ≤ Θ σ̂⁻¹` and the product bound
`√(E G²) √(E F²) ≤ σ̂ E G² + σ̂⁻¹ E F²`, so that the Step 2 bound closes from `W_src`:
`akhcPrime_jBound_src` and `akhcPrime_step2_thetaBound_src`, with `hWeak` replaced by
`W_src ≤ K_w δσ² Θ_m`, which is what `akhcPrime_step2_energy_le` delivers.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

open Homogenization MeasureTheory

noncomputable section

/-- The route-W weak-norm energy in the source's normalization, at the special vectors of
package B1: `σ̂_k E[G²] + σ̂_k⁻¹ E[F²]`. -/
noncomputable def akhcPrime_srcEnergy {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (k : ℕ)
    (e : Vec d) : ℝ :=
  SuperdiffusionCLT.AKHC61.Response.akhc_sigmaHatScalar nu L P k *
      ∫ a, (Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
          (Homogenization.originCube d (k : ℤ)) (1 / 2 : ℝ)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e)
          (SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P k e) a.toFun) ^ 2
        ∂(SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P) +
    (SuperdiffusionCLT.AKHC61.Response.akhc_sigmaHatScalar nu L P k)⁻¹ *
      ∫ a, (Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
          (Homogenization.originCube d (k : ℤ)) (1 / 2 : ℝ)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e)
          (SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P k e) a.toFun) ^ 2
        ∂(SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P)

section Law

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (L : ℕ)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
      Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X
        (H * (j : ℝ) ^ D) ∧
      ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
        (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                  omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) *
                  X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet
                  (Homogenization.originCube d (j : ℤ)))))
  (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 in
/-- **The route-W Step 2 `J`-bound skeleton** (nodes 31-35).

The source's `EJ.minus.PQ` display, in route-W form: `CoarseGraining`'s
normalized-cutoff div-curl bound (package B2) at parent `cu_k`, children at scale `k - ell`,
`s = t = 1/2`, with the special vectors of package B1 and the centering vectors `p₀`, `q₀`.
Inputs beyond the standing binders: `hPigeon` (D1, node 28) and `hGradSq`, `hFluxSq` (C3). -/
theorem akhcPrime_jBound_src
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (k ell : ℕ) (hell : ell ≤ k)
    (delta sigma : ℝ) (hdelta : 0 ≤ delta) (hsigma : 0 ≤ sigma)
    (hsmall : delta * sigma ^ 2 ≤ 1)
    (hPigeon :
      Homogenization.BlockMatLoewnerLE
        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
          (Homogenization.cubeSet (Homogenization.originCube d ((k - ell : ℕ) : ℤ))))
        ((1 + delta * sigma ^ 2) •
          SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
            (Homogenization.cubeSet (Homogenization.originCube d (k : ℤ)))))
    (e : Vec d) (he : vecNormSq e = 1)
    (hGradSq :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          (Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
            (Homogenization.originCube d (k : ℤ)) (1 / 2 : ℝ)
            (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
            (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e)
            (SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P k e) a.toFun) ^ 2)
        (SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P))
    (hFluxSq :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          (Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
            (Homogenization.originCube d (k : ℤ)) (1 / 2 : ℝ)
            (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
            (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e)
            (SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P k e) a.toFun) ^ 2)
        (SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P)) :
    Homogenization.Book.Ch04.expectedResponseJCubeSet
          (SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P)
          (Homogenization.originCube d (k : ℤ))
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e) -
        SuperdiffusionCLT.AKHC61.Response.akhc_centeringTerm
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P k)
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P k)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e) ≤
      SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d *
        (sigma * Real.sqrt delta *
            Real.sqrt (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k) +
          ((3 : ℝ) ^ ell)⁻¹ *
            Real.sqrt (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k) +
          Real.sqrt (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k *
            akhcPrime_srcEnergy nu L P k e) +
          akhcPrime_srcEnergy nu L P k e) := by
  have hB2 := SuperdiffusionCLT.AKHC61.Response.akhc_jUpperBound_of_cutoffLaw d hnu P L
    hPrefix hJ2 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
    hpPsiS hGrowth hP2 (k := ((k - ell : ℕ) : ℤ)) (m := (k : ℤ)) (Int.natCast_nonneg _)
    (by exact_mod_cast Nat.sub_le k ell) _ _ _ _ hGradSq hFluxSq
  unfold Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.jUpperWeakNormManuscriptExpectedRHSAtScale
    at hB2
  dsimp only at hB2
  have hj : Int.toNat ((k : ℤ) - ((k - ell : ℕ) : ℤ)) = ell := by omega
  rw [hj, Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant_mul_scaleSep_eq]
    at hB2
  refine hB2.trans ?_
  -- abbreviations for the two annealed scalars at scale `k`
  have hA : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P k :=
    SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2
      PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 k
  have hB : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P k :=
    SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2
      PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 k
  have hTheta1 : 1 ≤ SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k :=
    SuperdiffusionCLT.AKHC61.Carrier.akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2
      PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 k
  have hPig := (SuperdiffusionCLT.AKHC61.Carrier.akhc_blockMatLoewnerLE_annealedBlockMatrix_smul_iff
    hnu L hJ4 ((k - ell : ℕ) : ℤ) (k : ℤ) (1 + delta * sigma ^ 2)).1 hPigeon
  generalize hAdef : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P k = A
    at hA
  generalize hBdef : SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P k = B at hB
  have hTheta : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k = B * A := by
    rw [← hAdef, ← hBdef]; rfl
  rw [hTheta] at hTheta1 ⊢
  -- the geometric-mean parametrization
  obtain ⟨hAc, hBc⟩ := SuperdiffusionCLT.AKHC61.Step2.akhcJB_param hA hB
  generalize hudef : Real.sqrt (B * A) = u at hAc hBc ⊢
  have hu1 : 1 ≤ u := by
    rw [← hudef, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hTheta1
  have hu0 : 0 ≤ u := by linarith only [hu1]
  have huu : u * u = B * A := by rw [← hudef]; exact Real.mul_self_sqrt (by positivity)
  have hcpos : 0 < Real.sqrt (B / A) := Real.sqrt_pos.2 (div_pos hB hA)
  have hsigHat : SuperdiffusionCLT.AKHC61.Response.akhc_sigmaHatScalar nu L P k =
      Real.sqrt (B / A) := by
    rw [SuperdiffusionCLT.AKHC61.Response.akhc_sigmaHatScalar, hAdef, hBdef]
  generalize hcdef : Real.sqrt (B / A) = c at hcpos hAc hBc hsigHat
  have hr : 0 < c ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hcpos _
  have hrr : c ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) = c := SuperdiffusionCLT.AKHC61.Step2.akhcJB_rpow_half_mul_self hcpos
  have hp : SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e =
      (c ^ (1 / 2 : ℝ))⁻¹ • e := by
    rw [SuperdiffusionCLT.AKHC61.Response.akhc_specialP, hsigHat,
      SuperdiffusionCLT.AKHC61.Step2.akhcJB_rpow_neg_half hcpos]
  have hq : SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e =
      c ^ (1 / 2 : ℝ) • e := by
    rw [SuperdiffusionCLT.AKHC61.Response.akhc_specialQ, hsigHat]
  generalize hrdef : c ^ (1 / 2 : ℝ) = r at hr hrr hp hq
  rw [← hrr] at hAc hBc
  have hrinv : 0 < r⁻¹ := inv_pos.2 hr
  have hrr1 : r * r * (r⁻¹ * r⁻¹) = 1 := by field_simp
  have hBr : B * (r⁻¹ * r⁻¹) = u := by
    rw [hBc, mul_assoc, hrr1, mul_one]
  have hAinv : A = u * (r⁻¹ * r⁻¹) := by
    rw [← hAc, mul_assoc, hrr1, mul_one]
  -- the expected response at the parent and child scales
  have hEJ : ∀ n : ℕ,
      Homogenization.Book.Ch04.expectedResponseJCubeSet
          (SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P)
          (Homogenization.originCube d (n : ℤ))
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e) =
        (1 / 2 : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n *
            (r * r) - 1 +
          (1 / 2 : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P n *
            (r⁻¹ * r⁻¹) := by
    intro n
    rw [SuperdiffusionCLT.AKHC61.Step2.akhcJB_expectedJ_originCube_eq hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
      hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 n, hp, hq]
    exact SuperdiffusionCLT.AKHC61.Step2.akhcJB_quadratic_special he hr _ _
  have hEJk :
      Homogenization.Book.Ch04.expectedResponseJCubeSet
          (SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P)
          (Homogenization.originCube d (k : ℤ))
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e) = u - 1 := by
    rw [hEJ k, hAdef, hBdef]
    linarith only [hAc, hBr]
  have hPigB : SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P (k - ell) ≤
      (1 + delta * sigma ^ 2) * B := by
    rw [← hBdef]; exact hPig.1
  have hPigA : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P (k - ell) ≤
      (1 + delta * sigma ^ 2) * A := by
    rw [← hAdef]; exact hPig.2
  have hA'r : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P (k - ell) *
      (r * r) ≤ (1 + delta * sigma ^ 2) * u := by
    calc _ ≤ (1 + delta * sigma ^ 2) * A * (r * r) :=
          mul_le_mul_of_nonneg_right hPigA (mul_self_nonneg r)
      _ = (1 + delta * sigma ^ 2) * u := by rw [mul_assoc, hAc]
  have hB'r : SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P (k - ell) *
      (r⁻¹ * r⁻¹) ≤ (1 + delta * sigma ^ 2) * u := by
    calc _ ≤ (1 + delta * sigma ^ 2) * B * (r⁻¹ * r⁻¹) :=
          mul_le_mul_of_nonneg_right hPigB (mul_self_nonneg r⁻¹)
      _ = (1 + delta * sigma ^ 2) * u := by rw [mul_assoc, hBr]
  have hEJc :
      Homogenization.Book.Ch04.expectedResponseJCubeSet
          (SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P)
          (Homogenization.originCube d ((k - ell : ℕ) : ℤ))
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e) ≤
        (1 + delta * sigma ^ 2) * u - 1 := by
    rw [hEJ (k - ell)]
    linarith only [hA'r, hB'r]
  have hτ : Homogenization.Book.Ch05.tauAtScale
      (SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P) (k : ℤ)
      ((k - ell : ℕ) : ℤ)
      (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
      (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e) ≤
        delta * sigma ^ 2 * u := by
    have hτeq : Homogenization.Book.Ch05.tauAtScale
        (SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P) (k : ℤ)
        ((k - ell : ℕ) : ℤ)
        (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
        (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e) =
      Homogenization.Book.Ch04.expectedResponseJCubeSet
          (SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P)
          (Homogenization.originCube d ((k - ell : ℕ) : ℤ))
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e) -
        Homogenization.Book.Ch04.expectedResponseJCubeSet
          (SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P)
          (Homogenization.originCube d (k : ℤ))
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e) := rfl
    rw [hτeq, hEJk]
    linarith only [hEJc]
  -- term 1: the additivity defect
  have hbound := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound_le_two_pow_card
    (Homogenization.originCube d (k : ℤ))
  have hT1 := SuperdiffusionCLT.AKHC61.Step2.akhcJB_tau_term_le d hbound hdelta hsigma hsmall hu0 hτ hEJc
  -- term 2: the cutoff oscillation
  rw [hEJk]
  have hT2 := SuperdiffusionCLT.AKHC61.Step2.akhcJB_osc_term_le d (quantitativeCubeCutoffGradientConst_nonneg d)
    (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound_nonneg
      (Homogenization.originCube d (k : ℤ))) hbound
    (t := ((3 : ℝ) ^ ell)⁻¹) (by positivity) hu1
  -- the centering vectors
  have hur : r ≤ u * r := by
    have h := mul_le_mul_of_nonneg_right hu1 hr.le
    rwa [one_mul] at h
  have hurinv : r⁻¹ ≤ u * r⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hu1 hrinv.le
    rwa [one_mul] at h
  have huu1 : u ≤ u * u := by
    have h := mul_le_mul_of_nonneg_right hu1 hu0
    rwa [one_mul] at h
  have hq0 : ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P k e‖ ≤ r * u := by
    have hBr1 : B * r⁻¹ = u * r := by rw [hBc]; field_simp
    rw [SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0, hq, hp, hBdef, smul_smul, ← sub_smul, hBr1]
    refine (SuperdiffusionCLT.AKHC61.Step2.akhcJB_norm_smul_le he _).trans (abs_le.2 ⟨?_, ?_⟩)
    · linarith only [hr, hur]
    · linarith only [hr, hur]
  have hp0 : ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P k e‖ ≤ u * r⁻¹ := by
    have hAr1 : A * r = u * r⁻¹ := by rw [hAinv]; field_simp
    rw [SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0, hq, hp, hAdef, smul_smul, ← sub_smul, hAr1]
    refine (SuperdiffusionCLT.AKHC61.Step2.akhcJB_norm_smul_le he _).trans (abs_le.2 ⟨?_, ?_⟩)
    · linarith only [hrinv, hurinv]
    · linarith only [hrinv, hurinv]
  have hq0sq : ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P k e‖ * ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P k e‖ ≤ B * A * B := by
    calc _ ≤ (r * u) * (r * u) := mul_self_le_mul_self (norm_nonneg _) hq0
      _ = u * B := by rw [hBc]; ring
      _ ≤ (u * u) * B := mul_le_mul_of_nonneg_right huu1 hB.le
      _ = B * A * B := by rw [huu]
  have hp0sq : ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P k e‖ * ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P k e‖ ≤ B * A * A := by
    calc _ ≤ (u * r⁻¹) * (u * r⁻¹) := mul_self_le_mul_self (norm_nonneg _) hp0
      _ = u * A := by rw [hAinv]; ring
      _ ≤ (u * u) * A := mul_le_mul_of_nonneg_right huu1 hA.le
      _ = B * A * A := by rw [huu]
  -- the weak-norm integrals
  have hIG := SuperdiffusionCLT.AKHC61.Step2.akhcJB_integral_le_sqrt_integral_sq hGradSq
  have hIF := SuperdiffusionCLT.AKHC61.Step2.akhcJB_integral_le_sqrt_integral_sq hFluxSq
  have hW : akhcPrime_srcEnergy nu L P k e =
      c * ∫ a, (Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
          (Homogenization.originCube d (k : ℤ)) (1 / 2 : ℝ)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e)
          (SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P k e) a.toFun) ^ 2
        ∂(SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P) +
      c⁻¹ * ∫ a, (Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
          (Homogenization.originCube d (k : ℤ)) (1 / 2 : ℝ)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e)
          (SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P k e) a.toFun) ^ 2
        ∂(SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P) := by
    rw [akhcPrime_srcEnergy, hsigHat]
  rw [hW, ← hrr]
  have hG2 : 0 ≤ ∫ a, (Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
          (Homogenization.originCube d (k : ℤ)) (1 / 2 : ℝ)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e)
          (SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P k e) a.toFun) ^ 2
        ∂(SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P) :=
    MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hF2 : 0 ≤ ∫ a, (Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
          (Homogenization.originCube d (k : ℤ)) (1 / 2 : ℝ)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e)
          (SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P k e) a.toFun) ^ 2
        ∂(SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P) :=
    MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  generalize hG2def : (∫ a, (Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
          (Homogenization.originCube d (k : ℤ)) (1 / 2 : ℝ)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e)
          (SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P k e) a.toFun) ^ 2
        ∂(SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P)) = G2
    at hG2 hIG ⊢
  generalize hF2def : (∫ a, (Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
          (Homogenization.originCube d (k : ℤ)) (1 / 2 : ℝ)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e)
          (SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e)
          (SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P k e) a.toFun) ^ 2
        ∂(SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P)) = F2
    at hF2 hIF ⊢
  have hBA0 : 0 ≤ B * A := by linarith only [hTheta1]
  have hrr0 : 0 < r * r := mul_pos hr hr
  have hri : (r * r)⁻¹ = r⁻¹ * r⁻¹ := mul_inv r r
  rw [hri]
  have hBG : 0 ≤ r * r * G2 := mul_nonneg hrr0.le hG2
  have hAF : 0 ≤ r⁻¹ * r⁻¹ * F2 := mul_nonneg (mul_self_nonneg _) hF2
  have hq0sq' : ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P k e‖ * ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P k e‖ ≤ u * u * (r * r) := by
    calc _ ≤ (r * u) * (r * u) := mul_self_le_mul_self (norm_nonneg _) hq0
      _ = u * u * (r * r) := by ring
  have hp0sq' : ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P k e‖ * ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P k e‖ ≤
      u * u * (r⁻¹ * r⁻¹) := by
    calc _ ≤ (u * r⁻¹) * (u * r⁻¹) := mul_self_le_mul_self (norm_nonneg _) hp0
      _ = u * u * (r⁻¹ * r⁻¹) := by ring
  have hZg : ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P k e‖ * ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P k e‖ * G2 ≤
      B * A * (r * r * G2 + r⁻¹ * r⁻¹ * F2) := by
    calc _ ≤ u * u * (r * r) * G2 := mul_le_mul_of_nonneg_right hq0sq' hG2
      _ = B * A * (r * r * G2) := by rw [← huu]; ring
      _ ≤ B * A * (r * r * G2 + r⁻¹ * r⁻¹ * F2) :=
          mul_le_mul_of_nonneg_left (by linarith only [hAF]) hBA0
  have hZf : ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P k e‖ * ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P k e‖ * F2 ≤
      B * A * (r * r * G2 + r⁻¹ * r⁻¹ * F2) := by
    calc _ ≤ u * u * (r⁻¹ * r⁻¹) * F2 := mul_le_mul_of_nonneg_right hp0sq' hF2
      _ = B * A * (r⁻¹ * r⁻¹ * F2) := by rw [← huu]; ring
      _ ≤ B * A * (r * r * G2 + r⁻¹ * r⁻¹ * F2) :=
          mul_le_mul_of_nonneg_left (by linarith only [hBG]) hBA0
  -- term 3: the two linear weak-norm terms
  have hcg0 : 0 ≤ (Fintype.card (Fin d) : ℝ) *
      ((3 : ℝ) ^ ((d : ℝ) + 1 / 2) *
          Homogenization.cubeBesovScaleWeight (-(1 / 2 : ℝ)) (Homogenization.originCube d (k : ℤ)) *
        Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound
          (Homogenization.originCube d (k : ℤ)) (1 / 2 : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (by positivity)
      (Homogenization.cubeBesovScaleWeight_nonneg _ _))
      (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound_nonneg
        _ _))
  have hcg : (Fintype.card (Fin d) : ℝ) *
      ((3 : ℝ) ^ ((d : ℝ) + 1 / 2) *
          Homogenization.cubeBesovScaleWeight (-(1 / 2 : ℝ)) (Homogenization.originCube d (k : ℤ)) *
        Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound
          (Homogenization.originCube d (k : ℤ)) (1 / 2 : ℝ)) ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53_linearCutoffCoeff_le_dimensional
      (Homogenization.originCube d (k : ℤ)) (by norm_num) (by norm_num)
  have hT3g := SuperdiffusionCLT.AKHC61.Step2.akhcJB_linear_term_le (norm_nonneg _) hcg0 hcg hIG hZg
  have hT3f := SuperdiffusionCLT.AKHC61.Step2.akhcJB_linear_term_le (norm_nonneg _) hcg0 hcg hIF hZf
  -- term 4: the product term
  have hone : 1 ≤ r * r * (r⁻¹ * r⁻¹) := by
    rw [show r * r * (r⁻¹ * r⁻¹) = (r * r⁻¹) * (r * r⁻¹) by ring, mul_inv_cancel₀ hr.ne', one_mul]
  have hCprod :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff_origin_le_dimensional
      (d := d) k (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num)
  have hCprod0 :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff_nonneg
      (Homogenization.originCube d (k : ℤ)) (1 / 2 : ℝ) (1 / 2 : ℝ)
  have hT4 : Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff
        (Homogenization.originCube d (k : ℤ)) (1 / 2 : ℝ) (1 / 2 : ℝ) *
        (Real.sqrt G2 * Real.sqrt F2) ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d * (r * r * G2 + r⁻¹ * r⁻¹ * F2) :=
    mul_le_mul hCprod (SuperdiffusionCLT.AKHC61.Step2.akhcJB_sqrt_mul_sqrt_le (mul_self_nonneg r⁻¹) hrr0.le hone hG2 hF2)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (hCprod0.trans hCprod)
  -- assembly
  have hK1 : 0 ≤ 4 * (1 + (2 : ℝ) ^ d) := by positivity
  have hK2 : 0 ≤ 8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d :=
    mul_nonneg (mul_nonneg (by norm_num) (quantitativeCubeCutoffGradientConst_nonneg d))
      (by positivity)
  have hK3 : 0 ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d := hcg0.trans hcg
  have hK4 : 0 ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d := hCprod0.trans hCprod
  have hK : SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d = 4 * (1 + (2 : ℝ) ^ d) +
      8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d + SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d +
        SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d := rfl
  have hx1 : 0 ≤ sigma * Real.sqrt delta * u :=
    mul_nonneg (mul_nonneg hsigma (Real.sqrt_nonneg _)) hu0
  have hx2 : 0 ≤ ((3 : ℝ) ^ ell)⁻¹ * u := mul_nonneg (by positivity) hu0
  have hx3 : 0 ≤ Real.sqrt (B * A * (r * r * G2 + r⁻¹ * r⁻¹ * F2)) := Real.sqrt_nonneg _
  have hx4 : 0 ≤ r * r * G2 + r⁻¹ * r⁻¹ * F2 := add_nonneg hBG hAF
  have hk1 : 4 * (1 + (2 : ℝ) ^ d) * (sigma * Real.sqrt delta * u) ≤
      SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d * (sigma * Real.sqrt delta * u) :=
    mul_le_mul_of_nonneg_right (by linarith only [hK, hK2, hK3, hK4]) hx1
  have hk2 : 8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d *
      (((3 : ℝ) ^ ell)⁻¹ * u) ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d * (((3 : ℝ) ^ ell)⁻¹ * u) :=
    mul_le_mul_of_nonneg_right (by linarith only [hK, hK1, hK3, hK4]) hx2
  have hk3 : SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d * Real.sqrt (B * A * (r * r * G2 + r⁻¹ * r⁻¹ * F2)) ≤
      SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d * Real.sqrt (B * A * (r * r * G2 + r⁻¹ * r⁻¹ * F2)) :=
    mul_le_mul_of_nonneg_right (by linarith only [hK, hK1, hK2, hK4]) hx3
  have hk4 : SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d * (r * r * G2 + r⁻¹ * r⁻¹ * F2) ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d * (r * r * G2 + r⁻¹ * r⁻¹ * F2) :=
    mul_le_mul_of_nonneg_right (by linarith only [hK, hK1, hK2, hK3]) hx4
  have hsum : SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d * (sigma * Real.sqrt delta * u + ((3 : ℝ) ^ ell)⁻¹ * u +
      Real.sqrt (B * A * (r * r * G2 + r⁻¹ * r⁻¹ * F2)) + (r * r * G2 + r⁻¹ * r⁻¹ * F2)) =
      SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d * (sigma * Real.sqrt delta * u) +
        SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d * (((3 : ℝ) ^ ell)⁻¹ * u) +
        SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d * Real.sqrt (B * A * (r * r * G2 + r⁻¹ * r⁻¹ * F2)) +
        SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d * (r * r * G2 + r⁻¹ * r⁻¹ * F2) := by ring
  rw [hsum]
  linarith only [hT1, hT2, hT3g, hT3f, hT4, hk1, hk2, hk3, hk4]

end Law

end

end SuperdiffusionCLT.AKHC61.WeakNorms
