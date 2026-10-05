/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.HarmonicApprox
public import SuperdiffusionCLT.Section6.Lemma.WeakGrad

/-!
# The harmonic-approximation bullet on a cube

Deterministic form of the harmonic-approximation bullet of the sharp-scale inputs. If a field `a`
is elliptic on `cu_n` with symmetric part `ν Id` and `𝓔_{1/9,∞,2}(cu_n; a, σ Id) ≤ δ`, then
every `a`-harmonic `u` on the open cube `cu_n` has a harmonic `w` on `cu_{n-1}` with
`3^{-n} ‖u - w‖_{L̲²(cu_{n-1})} ≤ C δ σ^{-1/2} ν^{1/2} ‖∇u‖_{L̲²(cu_n)}`, for every
`C` at least a constant `C₀(d)`. The bound `δ` is free: the good-event bullet supplies
`δ = ε m^{-(1-ρ)/2} log m` directly, so no restriction `δ ≤ 1` is needed.

## Main results

* `harmonicBullet_deterministic`: the estimate, with the printed order of constants.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6.HarmonicBullet

open Homogenization SuperdiffusionCLT.Section6.HarmonicApprox

noncomputable section

/-- **Harmonic approximation bullet (deterministic form).** -/
theorem harmonicBullet_deterministic (d : ℕ) [NeZero d] :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ (n : ℕ) {lam Lam : ℝ} {a : CoeffField d}
      {sigma nu delta : ℝ},
      IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ))) a → 0 < sigma → 0 < nu →
      (∀ x ∈ cubeSet (originCube d (n : ℤ)), symmPart (a x) = nu • (1 : Mat d)) →
      HomogenizationErrorOnCube (originCube d (n : ℤ)) (1 / 9) MultiscaleExponent.infinity
        (MultiscaleExponent.finite 2) a (sigma • (1 : Mat d)) ≤ delta →
      ∀ u : AHarmonicFunction a (openCubeSet (originCube d (n : ℤ))),
        ∃ w : AHarmonicFunction (fun _ => (1 : Mat d))
            (openCubeSet (originCube d ((n : ℤ) - 1))),
          ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d ((n : ℤ) - 1)) 2
                (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤
            ENNReal.ofReal (C * delta * (Real.sqrt sigma)⁻¹ * Real.sqrt nu) *
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
                (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
  obtain ⟨C₀, hC₀, h⟩ := harmonic_approximation_deterministic d
  refine ⟨C₀, hC₀, fun C hC n lam Lam a sigma nu delta hEll hs hnu hsym hE u => ?_⟩
  obtain ⟨x0, hx0⟩ := Book.Ch02.openCubeSet_nonempty (originCube d (n : ℤ))
  have hell0 := hEll.2 x0 (openCubeSet_subset_cubeSet _ hx0)
  have h0 : 0 < lam := hell0.1
  have hle : lam ≤ Lam := hell0.2.1
  have hE0 : 0 ≤ delta := by
    have h1 := WeakGrad.weakGrad_error_nonneg (originCube d (n : ℤ))
      (paddedFamily (originCube d (n : ℤ)) hEll h0 hle) (scalarMatrix (d := d) sigma)
      (s := 1 / 9) (by norm_num)
    rw [← homogenizationErrorOnCube_eq_ch02 hEll h0 hle (1 / 9) 2 (sigma • (1 : Mat d))] at h1
    exact h1.trans hE
  obtain ⟨w, hw⟩ := h (n : ℤ) hEll hs hnu hsym hE u
  refine ⟨w, ?_⟩
  have hp : (3 : ℝ) ^ (-(n : ℝ)) = (3 : ℝ) ^ (-(n : ℤ)) := by
    rw [← Real.rpow_intCast]
    norm_num
  rw [hp]
  refine hw.trans ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  have hq : 0 ≤ delta * (Real.sqrt sigma)⁻¹ * Real.sqrt nu := by positivity
  nlinarith only [mul_le_mul_of_nonneg_right hC hq]

end
end SuperdiffusionCLT.Section6.HarmonicBullet
