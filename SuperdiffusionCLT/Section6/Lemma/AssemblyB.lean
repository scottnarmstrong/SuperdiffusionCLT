/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Lemma.Assembly
public import SuperdiffusionCLT.Section6.Lemma.RegEllipticityB
public import SuperdiffusionCLT.Section6.Lemma.SstarCloseB
public import SuperdiffusionCLT.Section6.Lemma.WeakGrad

/-!
# Two bullets on a cube: `reg.ellipticity` and `sstar.close`

Deterministic cube forms of the bullets `e.Dir.new.reg.ellipticity` and `e.Dir.new.sstar.close`
of `l.sharp.scale.inputs`, for the translated full centered field, with `σ` standing for `σ̄_m` and
`δ` for the bound `ε m^{-(1-ρ)/2} log m` of the full-field bullet (assumed at most `1`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization

noncomputable section

/-- The homogenization error of a field elliptic on a cube is nonnegative. -/
theorem l9_error_nonneg {d : ℕ} [NeZero d] {lam Lam : ℝ} {a : CoeffField d} (n : ℤ)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d n)) a) (sigma : ℝ) :
    0 ≤ HomogenizationErrorOnCube (originCube d n) (1 / 9) MultiscaleExponent.infinity
      (MultiscaleExponent.finite 2) a (sigma • (1 : Mat d)) := by
  obtain ⟨h0, hle⟩ := l9_ell_pos n hEll
  have h1 := WeakGrad.weakGrad_error_nonneg (originCube d n)
    (HarmonicApprox.paddedFamily (originCube d n) hEll h0 hle) (scalarMatrix (d := d) sigma)
    (s := 1 / 9) (by norm_num)
  rw [← HarmonicApprox.homogenizationErrorOnCube_eq_ch02 hEll h0 hle (1 / 9) 2
    (sigma • (1 : Mat d))] at h1
  exact h1

/-- **`reg.ellipticity` and `sstar.close` on a cube.** -/
theorem l9_reg_sstar_cube (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ C' : ℝ, C ≤ C' → ∀ (nu sigma delta : ℝ)
      (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (m n : ℕ) (k : Fin d → ℤ),
      0 < sigma →
      (∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ)))
        (fun x => nu • (1 : Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
            (cubeSet (originCube d (m : ℤ)))
            ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))) →
      HomogenizationErrorOnCube (originCube d (n : ℤ)) (1 / 9) MultiscaleExponent.infinity
        (MultiscaleExponent.finite 2)
        (fun x => nu • (1 : Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
            (cubeSet (originCube d (m : ℤ)))
            ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) (sigma • (1 : Mat d)) ≤ delta →
      delta ≤ 1 →
      sigma⁻¹ *
            LambdaSq (originCube d (n : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
              (fun x => nu • (1 : Mat d) +
                SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                  (cubeSet (originCube d (m : ℤ)))
                  ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) +
          sigma *
            (lambdaSq (originCube d (n : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
              (fun x => nu • (1 : Mat d) +
                SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                  (cubeSet (originCube d (m : ℤ)))
                  ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)))⁻¹ ≤ C' ∧
      matNorm (sigma⁻¹ • Homogenization.sigmaCoarse (cubeSet (originCube d (n : ℤ)))
          (fun x => nu • (1 : Mat d) +
            SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
              (cubeSet (originCube d (m : ℤ)))
              ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) - 1) +
        matNorm (sigma⁻¹ • Homogenization.sigmaStarCoarse (cubeSet (originCube d (n : ℤ)))
          (fun x => nu • (1 : Mat d) +
            SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
              (cubeSet (originCube d (m : ℤ)))
              ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) - 1) ≤ C' * delta := by
  obtain ⟨Cr, hCr, hreg⟩ := regEllipticity_exists d
  obtain ⟨Cs, hCs, hs⟩ := sstar_close_minimal_scales d
  have h2 : (1 : ℝ) ≤ max (2 * Cr) Cs := le_trans hCs (le_max_right _ _)
  refine ⟨max (2 * Cr) Cs, h2, fun C' hC' nu sigma delta omega m n k hσ hEllF hE hδ => ?_⟩
  obtain ⟨lam, Lam, hEll⟩ := hEllF
  obtain ⟨h0, hle⟩ := l9_ell_pos (n : ℤ) hEll
  have hE0 := l9_error_nonneg (n : ℤ) hEll sigma
  have hE1 : HomogenizationErrorOnCube (originCube d (n : ℤ)) (1 / 9)
      MultiscaleExponent.infinity (MultiscaleExponent.finite 2)
      (fun x => nu • (1 : Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (cubeSet (originCube d (m : ℤ)))
          ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) (sigma • (1 : Mat d)) ≤ 1 :=
    hE.trans hδ
  have hdel0 : 0 ≤ delta := hE0.trans hE
  refine ⟨?_, ?_⟩
  · refine (hreg (originCube d (n : ℤ)) hEll h0 hle hσ).trans ?_
    have hsq : HomogenizationErrorOnCube (originCube d (n : ℤ)) (1 / 9)
        MultiscaleExponent.infinity (MultiscaleExponent.finite 2)
        (fun x => nu • (1 : Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
            (cubeSet (originCube d (m : ℤ)))
            ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) (sigma • (1 : Mat d)) ^ 2 ≤ 1 :=
      pow_le_one₀ hE0 hE1
    have hCr0 : 0 ≤ Cr := by linarith only [hCr]
    have h3 : Cr * (HomogenizationErrorOnCube (originCube d (n : ℤ)) (1 / 9)
        MultiscaleExponent.infinity (MultiscaleExponent.finite 2)
        (fun x => nu • (1 : Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
            (cubeSet (originCube d (m : ℤ)))
            ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) (sigma • (1 : Mat d)) ^ 2 + 1) ≤
        Cr * 2 := mul_le_mul_of_nonneg_left (by linarith only [hsq]) hCr0
    have h4 : 2 * Cr ≤ C' := (le_max_left _ _).trans hC'
    linarith only [h3, h4]
  · have h5 := hs nu sigma delta omega m n k hσ ⟨lam, Lam, hEll⟩ hE hδ
    have h6 : Cs ≤ C' := (le_max_right _ _).trans hC'
    exact h5.trans (mul_le_mul_of_nonneg_right h6 hdel0)

end

end SuperdiffusionCLT.Section6
