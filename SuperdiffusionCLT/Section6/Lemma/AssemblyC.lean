/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Lemma.AssemblyB
public import SuperdiffusionCLT.Section6.Lemma.WeakFluxB
public import SuperdiffusionCLT.Section6.Lemma.HarmonicBullet

/-!
# Three bullets on a cube: weak flux, weak gradient, harmonic approximation

Deterministic cube forms of `e.Dir.new.weak.flux`, `e.Dir.new.weak.grad` and
`e.Dir.new.harmonic.approx` of `l.sharp.scale.inputs` for the translated full centered field, with
`σ` standing for `σ̄_m` and `δ` for the bound `ε m^{-(1-ρ)/2} log m` of the full-field bullet.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization

noncomputable section

/-- **Weak flux, weak gradient and harmonic approximation on a cube.** -/
theorem l9_flux_grad_harm_cube (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ C' : ℝ, C ≤ C' → ∀ (nu sigma delta : ℝ)
      (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (m n : ℕ) (k : Fin d → ℤ),
      0 < nu → 0 < sigma →
      (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d (m : ℤ)) →
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
      ∀ u : AHarmonicFunction
          (fun x => nu • (1 : Mat d) +
            SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
              (cubeSet (originCube d (m : ℤ)))
              ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
          (openCubeSet (originCube d (n : ℤ))),
        ENNReal.ofReal
            (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n : ℤ)) (1 / 4)
              (fun x => matVecMul
                (nu • (1 : Mat d) +
                  SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                    (cubeSet (originCube d (m : ℤ)))
                    ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) - sigma • (1 : Mat d))
                (u.toH1.grad x))) ≤
          ENNReal.ofReal (C' * Real.sqrt sigma * delta * Real.sqrt nu) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
              (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) ∧
        ENNReal.ofReal
            (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n : ℤ)) (1 / 4)
              u.toH1.grad) ≤
          ENNReal.ofReal (C' * (Real.sqrt sigma)⁻¹ * Real.sqrt nu) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
              (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) ∧
        ∃ w : AHarmonicFunction (fun _ => (1 : Mat d))
            (openCubeSet (originCube d ((n : ℤ) - 1))),
          ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d ((n : ℤ) - 1)) 2
                (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤
            ENNReal.ofReal (C' * delta * (Real.sqrt sigma)⁻¹ * Real.sqrt nu) *
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
                (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
  obtain ⟨Cf, hCf, hflux⟩ := WeakFlux.weak_flux_minimal_scales d
  obtain ⟨Cg, hCg, hgrad⟩ := WeakGrad.weakGrad_deterministic_of_le_one d
  obtain ⟨Ch, hCh, hharm⟩ := HarmonicBullet.harmonicBullet_deterministic d
  refine ⟨max (max Cf Cg) (max Ch 1), le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  intro C' hC' nu sigma delta omega m n k hnu hσ himg hEllF hE hδ u
  have hCf' : Cf ≤ C' := (le_max_left _ _).trans ((le_max_left _ _).trans hC')
  have hCg' : Cg ≤ C' := (le_max_right _ _).trans ((le_max_left _ _).trans hC')
  have hCh' : Ch ≤ C' := (le_max_left _ _).trans ((le_max_right _ _).trans hC')
  obtain ⟨lam, Lam, hEll⟩ := hEllF
  have hE0 := l9_error_nonneg (n : ℤ) hEll sigma
  have hdel0 : 0 ≤ delta := hE0.trans hE
  have hE1 := hE.trans hδ
  have hsym : ∀ x ∈ cubeSet (originCube d (n : ℤ)),
      symmPart ((fun x => nu • (1 : Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (cubeSet (originCube d (m : ℤ)))
          ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) x) = nu • (1 : Mat d) :=
    fun x _ => HarmonicApprox.symmPart_centeredStreamField_add nu omega _ _
  refine ⟨?_, ?_, ?_⟩
  · refine (hflux nu sigma delta omega m n k hnu hσ himg ⟨lam, Lam, hEll⟩ hE u).trans ?_
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    have hq : 0 ≤ Real.sqrt sigma * delta * Real.sqrt nu := by positivity
    have h1 := mul_le_mul_of_nonneg_right hCf' hq
    linarith only [h1, mul_assoc Cf (Real.sqrt sigma * delta) (Real.sqrt nu),
      mul_assoc Cf (Real.sqrt sigma) delta, mul_assoc C' (Real.sqrt sigma * delta) (Real.sqrt nu),
      mul_assoc C' (Real.sqrt sigma) delta]
  · refine (hgrad (n : ℤ) hEll hσ hnu hsym hE1 u).trans ?_
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    have hq : 0 ≤ (Real.sqrt sigma)⁻¹ * Real.sqrt nu := by positivity
    have h1 := mul_le_mul_of_nonneg_right hCg' hq
    linarith only [h1, mul_assoc Cg (Real.sqrt sigma)⁻¹ (Real.sqrt nu),
      mul_assoc C' (Real.sqrt sigma)⁻¹ (Real.sqrt nu)]
  · exact hharm C' hCh' (n : ℕ) hEll hσ hnu hsym hE u

end

end SuperdiffusionCLT.Section6
