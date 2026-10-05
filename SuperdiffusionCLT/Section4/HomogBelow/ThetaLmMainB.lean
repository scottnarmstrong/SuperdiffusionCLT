/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmMainC
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmSharpInputs

/-!
The bound `e.Theta.Lm.final.bound` at one
fixed `(ν, P, L, m)` and one fixed startup scale `m₀`: the scale choices
`m̃, n = m̃ + 5m₀, m̃' = m - 5m₀`, the two applications of [AK, Theorem 6.1] (through the abstracted
conclusion `hStep`), `e.rats.to.infty` at `n`, the sharp bound on `ω_{m̃'}²`, and the final
rewrites. The startup-scale facts (`hmain`, `hBig`, `hE8`, `hEm`, `hX`) are supplied by the
caller, separately in the two branches `m ≤ L²` and `L² ≤ m`. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

/-- **`e.Theta.Lm.final.bound` at a fixed startup scale `m₀`.** -/
theorem homogBelow_thetaLm_of_m0
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {P : MeasureTheory.ProbabilityMeasure
      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {Cmix : ℝ} (hCmix1 : 1 ≤ Cmix)
    (BIG : ℕ → ℕ → ℝ) (U C61 κ : ℝ) (hU : 0 < U) (m2 m3 : ℕ)
    (hStep : ∀ m m0 : ℕ, max m2 m3 ≤ m →
      homogBelow_omegaSeq nu L Cmix P m ^ 2 ≤ U⁻¹ → BIG m m0 ≤ (m0 : ℝ) →
      ∀ n : ℕ, m + 4 * m0 ≤ n →
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n - 1 ≤
          U * homogBelow_omegaSeq nu L Cmix P m ^ 2 +
            C61 * (3 : ℝ) ^ (-(κ * ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ)))))
    (hm2 : 4 * m2 ≤ L + 3) (hL2m3 : L / 2 ≤ m3)
    {c M' alpha : ℝ}
    (hFact2 : ∀ h : ℕ, (L : ℝ) ≤ 2 * (h : ℝ) → h ≤ L →
      c * (Cmix * M') * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
          (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (2 : ℝ))
    (hm3ge : (L : ℝ) - c * M' * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m3 : ℝ))
    (hSmall : ∀ h : ℕ, m3 + 1 ≤ h → homogBelow_omegaSeq nu L Cmix P h ^ 2 ≤ (8 * U)⁻¹)
    (m m0 : ℕ) (hmain : m3 + 10 * m0 + ⌈Cmix * Real.log (L : ℝ)⌉₊ + 1 ≤ m)
    (hBig : ∀ x : ℕ, x ≤ m → BIG x m0 ≤ (m0 : ℝ))
    (hE8 : C61 * (3 : ℝ) ^ (-(κ * (m0 : ℝ))) ≤ 1 / 8)
    (hEm : C61 * (3 : ℝ) ^ (-(κ * (m0 : ℝ))) ≤ (m : ℝ) ^ (-(3000 : ℝ)))
    (C : ℝ)
    (hX : ∀ mt' : ℕ, m = mt' + 5 * m0 →
      ((L - mt' : ℕ) : ℝ) ≤ max 0 ((L : ℝ) - (m : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)))
    (hC1 : U * (3 * (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3)) ^ 2 *
      (4 * Cmix ^ 2 + 16 * Cmix)) ≤ C)
    (hC2 : U * (3 * (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3)) ^ 2 * 9 *
      Cmix ^ 2) * (2 : ℝ) ^ (6000 : ℝ) + 1 ≤ C) :
    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1 ≤
      (C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
          max 0 ((L : ℝ) - (m : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)) *
          (if (m : ℝ) ≤ (L : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ) then (1 : ℝ) else 0)) +
        C * (m : ℝ) ^ (-(3000 : ℝ)) := by
  obtain ⟨mt, n, mt', e1, e2, e3, e4, -, -, -, -, -, hm3mt, hm3mt', hmt, hmt'⟩ :=
    homogBelow_scaleDefs Cmix L m m0 m2 m3 hm2 hL2m3 hmain
  have hsInf : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu L hPrefix hJ2 hJ3 hJ4
  have h8U : (8 * U)⁻¹ ≤ U⁻¹ := inv_anti₀ hU (by linarith only [hU])
  have hcore := homogBelow_twoCalls_core
    (fun k => SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k)
    (homogBelow_omegaSeq nu L Cmix P) BIG U C61 κ m2 m3 hU hStep mt mt' m0 hmt hmt'
    (hSmall mt hm3mt) (le_trans (hSmall mt' hm3mt') h8U)
    (hBig mt (by omega)) (hBig mt' (by omega)) hE8 _
    (fun hθ => homogBelow_omegaSeq_sharp_bound nu hnu L Cmix P hPrefix hJ2 hJ3 hJ4 hCmix1 mt'
      (homogBelow_sharpInput_hSge hnu L hPrefix hJ2 hJ3 hJ4 (mt + 5 * m0) mt' (by omega) hθ)
      (homogBelow_sharpInput_hAbound hnu L hPrefix hJ2 hJ3 hJ4 hCmix1 hFact2 m3 hm3ge mt'
        (by omega)))
  have hθ : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1 ≤
      U * (3 * (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3)) ^ 2 *
          (4 * Cmix ^ 2 + 16 * Cmix) * ((L - mt' : ℕ) : ℝ) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) +
        3 * (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3)) ^ 2 * 9 *
          Cmix ^ 2 * (max 1 (mt' : ℝ)) ^ (-(6000 : ℝ))) +
        C61 * (3 : ℝ) ^ (-(κ * (m0 : ℝ))) := by
    rw [e4]; exact hcore
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hmt2 : (m : ℝ) ≤ 2 * (mt' : ℝ) := by exact_mod_cast (show m ≤ 2 * mt' by omega)
  exact homogBelow_finalShape (by linarith only [hU]) (by positivity) (by positivity) hsInf hθ
    (hX mt' e4) hm1 hmt2 hEm hC1 hC2

end SuperdiffusionCLT.Section4.HomogBelow
