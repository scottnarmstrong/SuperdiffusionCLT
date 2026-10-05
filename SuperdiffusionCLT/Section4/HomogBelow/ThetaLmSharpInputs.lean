/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmFinalQuantBound
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmFinalScaleDefs

/-!
The two inputs of `homogBelow_omegaSeq_sharp_bound` at the scale `h := m̃'`:

* `homogBelow_sharpInput_hSge`: `σ∞/2 ≤ S(h)`, from the first output of [AK, Theorem 6.1],
  `Θ_{L,n} - 1 ≤ 1/4` at some `n ≤ h` (`e.rats.to.infty` plus monotonicity of `S`);
* `homogBelow_sharpInput_hAbound`: `(L-h)_+ ≤ σ∞^2/Cmix`, from the headroom facts
  of `homogBelow_m3_headroom` and `homogBelow_headroom_sq_le`.

The input from [AK, Theorem 6.1] enters as a hypothesis (`hTheta`, the output of the first
`hStep` call, folded to `1/4` by the caller). -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

/-- **`hSge`.** If `Θ_{L,n} - 1 ≤ 1/4` at a scale `n ≤ h`, then `σ∞/2 ≤ S(h)`. -/
theorem homogBelow_sharpInput_hSge
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {P : MeasureTheory.ProbabilityMeasure
      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (n h : ℕ) (hnh : n ≤ h)
    (hTheta : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n - 1 ≤ 1 / 4) :
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P / 2 ≤
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) := by
  obtain ⟨h1, -⟩ := homogBelow_ratsToInfty hnu L hPrefix hJ2 hJ3 hJ4 n hTheta
  have heq : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))) =
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n)⁻¹ :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar_eq_inv hnu L hJ4 (n : ℤ)
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq_pos
        hnu L hPrefix hJ2 hJ3 hJ4 n)
  have hmono := homogBelow_sigmaBarStarScalar_mono nu hnu L _ hPrefix hJ2 hJ3 hJ4 hnh
  dsimp only at hmono
  rw [heq] at hmono
  linarith only [h1, hmono]

/-- **`hAbound`.** From the `S(L)^2` lower bound (`hFact2` at `h := L`, shape of
`homogBelow_m3_headroom`'s second output with `M' = M * max 1 (3/c)`), and the
`m₃`-headroom `hm3`, every `h ≥ m₃` has `((L - h : ℕ) : ℝ) ≤ σ∞^2 / Cmix`. -/
theorem homogBelow_sharpInput_hAbound
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {P : MeasureTheory.ProbabilityMeasure
      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {Cmix c M' alpha : ℝ} (hCmix1 : 1 ≤ Cmix)
    (hFact2 : ∀ h : ℕ, (L : ℝ) ≤ 2 * (h : ℝ) → h ≤ L →
      c * (Cmix * M') * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
          (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (2 : ℝ))
    (m3 : ℕ)
    (hm3 : (L : ℝ) - c * M' * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m3 : ℝ))
    (h : ℕ) (hm3h : m3 ≤ h) :
    ((L - h : ℕ) : ℝ) ≤
      SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P ^ (2 : ℝ) / Cmix := by
  have hCmixpos : 0 < Cmix := lt_of_lt_of_le zero_lt_one hCmix1
  have hF := hFact2 L (by have : (0 : ℝ) ≤ L := Nat.cast_nonneg L; linarith only [this]) le_rfl
  have hSLle := homogBelow_sigmaBarStarScalar_le_sigmaBarInfinite hnu L hPrefix hJ2 hJ3 hJ4 L
  have hSLnn : 0 ≤ SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
      (Homogenization.cubeSet (Homogenization.originCube d (L : ℤ))) :=
    (homogBelow_sigmaBarStarScalar_pos nu hnu L P hPrefix hJ2 hJ3 hJ4 L).le
  have hfull := homogBelow_headroom_sq_le (c := c) (Mthr := M') (Lr := (L : ℝ) ^ alpha *
      Real.log (L : ℝ) ^ (3 : ℝ)) (h := (h : ℝ)) (m3 := (m3 : ℝ)) (L := (L : ℝ)) hCmixpos
    (by have e : c * (Cmix * M') * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) =
          c * (Cmix * M') * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by ring
        rw [e]; exact hF) hSLle
    (by have e : c * M' * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) =
          c * M' * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by ring
        rw [e]; linarith only [hm3]) hSLnn (by exact_mod_cast hm3h)
  have hsInf : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu L hPrefix hJ2 hJ3 hJ4
  rcases le_or_gt h L with hle | hlt
  · rw [Nat.cast_sub hle]; exact hfull
  · rw [Nat.sub_eq_zero_of_le hlt.le, Nat.cast_zero]
    exact div_nonneg (Real.rpow_nonneg hsInf.le _) hCmixpos.le

/-- Scale facts at `L = 7`, `n = 1`: the scale definitions are satisfiable with
`m₂ = 2`, `m₃ = 4`, `m₀ = 1`, `m = 40`, and the headroom arithmetic for
`h = m̃'` (`≥ m₃ + 1`) is consistent with `n ≤ h`. -/
example : ∃ n mtilde' : ℕ, 1 ≤ n ∧ n ≤ mtilde' ∧ 4 + 1 ≤ mtilde' ∧
    (7 - mtilde' : ℕ) = 0 := by
  have hceil : ⌈(1 : ℝ) * Real.log (7 : ℕ)⌉₊ ≤ 10 := by
    rw [Nat.ceil_le]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((7 : ℕ) : ℝ) by norm_num)
    norm_num at this ⊢; linarith only [this]
  obtain ⟨mt, n, mt', e1, e2, e3, e4, l1, l2, p1, p2, p3, a, b, c, d⟩ :=
    homogBelow_scaleDefs 1 7 40 1 2 4 (by norm_num) (by norm_num) (by omega)
  exact ⟨n, mt', p2, by omega, b, by omega⟩

end SuperdiffusionCLT.Section4.HomogBelow
