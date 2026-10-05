/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Section4.ThetaCutoff

@[expose] public section

/-- **`e.rats.to.infty`** (proof in the paper's treatment of
`p.homog.below`): once the renormalized ellipticity ratio
`Θ_{L,n} = thetaCutoff nu L P n` is within `1/4` of `1` at some scale `n`
(the conclusion of `e.Theta.convergence.prime.simplified`,
taken here as the hypothesis `hTheta`), the annealed lower block
`shom_{L,*}(cu_n)` is comparable to the infinite-volume limit `shom_{L}`:
`(1/2) shom_L ≤ shom_{L,*}(cu_n) ≤ shom_L`, with `shom_{L,*}(cu_n)` read as
`(sigmaBarStarInvSeq nu L P n)⁻¹` (the carrier convention of
`Frozen/Section4/ThetaCutoff.lean`).

The proof packages **`e.going.in.a.circle`**: from the
monotonicity of the two scalar diagonal blocks of `bfAhom_L(cu_h)`
(`sigmaBarUpperLimit_le`, `sigmaBarStarInvLimit_le`, both
`Section2/Annealed/InfiniteVolume.lean`), `shom_L ≤ shom_L(cu_n)` and
`shom_{L,*}(cu_n) ≤ shom_L` always hold unconditionally (`hUpper`, `hLower`);
the lower bound on `shom_{L,*}(cu_n)` additionally uses `hTheta` via the
literal definition `Θ_{L,n} · shom_{L,*}(cu_n) = shom_L(cu_n)`
(`x.AK.HC.Theta` of the paper, `Frozen/Section4/ThetaCutoff.lean`), which gives
`shom_L ≤ shom_L(cu_n) ≤ (5/4) shom_{L,*}(cu_n)`, hence
`(4/5) shom_L ≤ shom_{L,*}(cu_n)`, stronger than the printed `1/2`. -/
theorem SuperdiffusionCLT.Section4.HomogBelow.homogBelow_ratsToInfty
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {P : MeasureTheory.ProbabilityMeasure
      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (n : ℕ)
    (hTheta : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n - 1 ≤ 1 / 4) :
    (1 / 2) * SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P ≤
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n)⁻¹ ∧
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n)⁻¹ ≤
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P := by
  have hs : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu L hPrefix hJ2 hJ3 hJ4
  have hSInv_pos :
      0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq_pos
      hnu L hPrefix hJ2 hJ3 hJ4 n
  have hUpper : SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P ≤
      SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P n := by
    calc
      SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P ≤
          SuperdiffusionCLT.Section2.Annealed.sigmaBarUpperLimit nu L P :=
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_le_sigmaBarUpperLimit
          hnu L hPrefix hJ2 hJ3 hJ4
      _ ≤ SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P n :=
        SuperdiffusionCLT.Section2.Annealed.sigmaBarUpperLimit_le
          hnu L hPrefix hJ2 hJ3 hJ4 n
  have hLimitPos :
      0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvLimit nu L P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvLimit_pos
      hnu L hPrefix hJ2 hJ3 hJ4
  have hLimitLe :
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvLimit nu L P ≤
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvLimit_le
      hnu L hPrefix hJ2 hJ3 hJ4 n
  have hLower :
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n)⁻¹ ≤
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P :=
    (inv_le_inv₀ hSInv_pos hLimitPos).2 hLimitLe
  refine ⟨?_, hLower⟩
  have hΘunfold :
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n =
        SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P n *
          SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n :=
    rfl
  have hΘeq :
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n)⁻¹ =
        SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P n := by
    rw [hΘunfold, mul_assoc, mul_inv_cancel₀ hSInv_pos.ne', mul_one]
  have hΘle : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n ≤ (5 : ℝ) / 4 := by
    linarith only [hTheta]
  have hvnonneg :
      0 ≤ (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n)⁻¹ :=
    (inv_pos.2 hSInv_pos).le
  have hstep :
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n)⁻¹ ≤
        (5 / 4 : ℝ) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n)⁻¹ :=
    mul_le_mul_of_nonneg_right hΘle hvnonneg
  have hfinal :
      SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P n ≤
        (5 / 4 : ℝ) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n)⁻¹ := by
    rw [← hΘeq]; exact hstep
  have hchain : SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P ≤
      (5 / 4 : ℝ) *
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n)⁻¹ :=
    le_trans hUpper hfinal
  linarith only [hchain, hs.le]

/-- **The easy half of `e.rats.to.infty`, unconditional, at any scale `n`**:
`shom_{L,*}(cu_n) ≤ shom_L`, i.e. `S(n) ≤ sigmaBarInfinite`, with NO `hTheta`
hypothesis. This is the `hLower`-adjacent chase
(`sigmaBarStarInvLimit_le` + `sigmaBarStarScalar_eq_inv` + `inv_le_inv₀`)
inside `homogBelow_ratsToInfty`'s own proof, extracted as its own public
lemma since the sharp `omegaSeq` bound (`ThetaLmFinalQuantBound.lean`) also
needs it, at `n := L` itself. -/
theorem SuperdiffusionCLT.Section4.HomogBelow.homogBelow_sigmaBarStarScalar_le_sigmaBarInfinite
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {P : MeasureTheory.ProbabilityMeasure
      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (n : ℕ) :
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))) ≤
      SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P := by
  have hSInv_pos :
      0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq_pos
      hnu L hPrefix hJ2 hJ3 hJ4 n
  have hLimitPos :
      0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvLimit nu L P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvLimit_pos
      hnu L hPrefix hJ2 hJ3 hJ4
  have hLimitLe :
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvLimit nu L P ≤
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvLimit_le
      hnu L hPrefix hJ2 hJ3 hJ4 n
  have hLower :
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n)⁻¹ ≤
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P :=
    (inv_le_inv₀ hSInv_pos hLimitPos).2 hLimitLe
  have heq : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))) =
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n)⁻¹ :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar_eq_inv hnu L hJ4 (n : ℤ) hSInv_pos
  rw [heq]
  exact hLower
