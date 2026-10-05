/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step2.JBoundSkeleton

/-!
# Package D2a, continued: the closing arithmetic of the Step 2 `Θ` bound

Package B1's identity `Θ_k - 1 = 2 (E J(cu_k, p_e, q_e) - ½ p₀·q₀)` turns the `J`-bound of
`JBoundSkeleton.lean` into a bound on `Θ_k - 1`. The final Step 2 display of the paper is
`Θ_k - 1 ≤ C (σ δ^{1/2} + 3^{-L}) Θ_m`. It follows from one further input, the route-W form of
the weak-norm estimate at `n = k`, `h = k - L`,
`σ̄_k E[G²] + σ̄*⁻¹_k E[F²] ≤ K_w δσ² Θ_m`, which is the target of the weak-norm
packages (C6 with B3, B4, C3). The source's `3^{-L} Θ_m^{1/2} Θ_m` is improved here to
`3^{-L} Θ_m`.

This file proves the closing arithmetic, `akhcJB_close_arith`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step2

open Homogenization MeasureTheory

noncomputable section

/-- The Step 2 closing arithmetic: under the weak-norm bound `W ≤ K_w s² Θ_m`, the four
route-W terms at scale `k` are at most `(1 + √K_w + K_w)(s + t) Θ_m`. -/
theorem akhcJB_close_arith {K Kw s t Tk Tm W : ℝ} (hK : 0 ≤ K) (hKw : 0 ≤ Kw) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (ht : 0 ≤ t) (h1 : 1 ≤ Tk) (hkm : Tk ≤ Tm) (hW0 : 0 ≤ W)
    (hW : W ≤ Kw * (s * s) * Tm) :
    K * (s * Real.sqrt Tk + t * Real.sqrt Tk + Real.sqrt (Tk * W) + W) ≤
      K * (1 + Real.sqrt Kw + Kw) * (s + t) * Tm := by
  have hTk0 : 0 ≤ Tk := by linarith only [h1]
  have hTm0 : 0 ≤ Tm := by linarith only [h1, hkm]
  have hsq : Real.sqrt Tk ≤ Tm := by
    have hTT : Tk ≤ Tk * Tk := by
      have h := mul_le_mul_of_nonneg_right h1 hTk0
      rwa [one_mul] at h
    calc Real.sqrt Tk ≤ Real.sqrt (Tk * Tk) := Real.sqrt_le_sqrt hTT
      _ = Tk := Real.sqrt_mul_self hTk0
      _ ≤ Tm := hkm
  have ha : s * Real.sqrt Tk ≤ s * Tm := mul_le_mul_of_nonneg_left hsq hs0
  have hb : t * Real.sqrt Tk ≤ t * Tm := mul_le_mul_of_nonneg_left hsq ht
  have hc : Real.sqrt (Tk * W) ≤ Real.sqrt Kw * (s * Tm) := by
    have hprod : Tk * W ≤ Kw * ((s * Tm) * (s * Tm)) := by
      calc Tk * W ≤ Tm * (Kw * (s * s) * Tm) := mul_le_mul hkm hW hW0 hTm0
        _ = Kw * ((s * Tm) * (s * Tm)) := by ring
    calc Real.sqrt (Tk * W) ≤ Real.sqrt (Kw * ((s * Tm) * (s * Tm))) := Real.sqrt_le_sqrt hprod
      _ = Real.sqrt Kw * (s * Tm) := by
          rw [Real.sqrt_mul hKw, Real.sqrt_mul_self (mul_nonneg hs0 hTm0)]
  have hd : W ≤ Kw * (s * Tm) := by
    have hss : s * s ≤ s := by
      have h := mul_le_mul_of_nonneg_left hs1 hs0
      rwa [mul_one] at h
    calc W ≤ Kw * (s * s) * Tm := hW
      _ ≤ Kw * s * Tm :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hss hKw) hTm0
      _ = Kw * (s * Tm) := by ring
  have hextra : 0 ≤ (Real.sqrt Kw + Kw) * (t * Tm) :=
    mul_nonneg (add_nonneg (Real.sqrt_nonneg _) hKw) (mul_nonneg ht hTm0)
  have hinner : s * Real.sqrt Tk + t * Real.sqrt Tk + Real.sqrt (Tk * W) + W ≤
      (1 + Real.sqrt Kw + Kw) * (s + t) * Tm := by
    have hexp : (1 + Real.sqrt Kw + Kw) * (s + t) * Tm =
        s * Tm + t * Tm + Real.sqrt Kw * (s * Tm) + Kw * (s * Tm) +
          (Real.sqrt Kw + Kw) * (t * Tm) := by ring
    rw [hexp]
    linarith only [ha, hb, hc, hd, hextra]
  calc K * (s * Real.sqrt Tk + t * Real.sqrt Tk + Real.sqrt (Tk * W) + W)
      ≤ K * ((1 + Real.sqrt Kw + Kw) * (s + t) * Tm) := mul_le_mul_of_nonneg_left hinner hK
    _ = K * (1 + Real.sqrt Kw + Kw) * (s + t) * Tm := by ring

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

end Law

end

end SuperdiffusionCLT.AKHC61.Step2
