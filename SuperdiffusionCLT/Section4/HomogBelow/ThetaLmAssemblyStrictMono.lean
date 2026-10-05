/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.WeakOrlicz

/-!
Stage 4 (task `sc2`), first piece: AK.HC's (P3') binder for `akhc_weakerP3`
needs `StrictMonoOn Psi (Set.Ici 0)` for the chosen `Psi := Γ_σ`
(`gammaSigma`, `Homogenization.Probability.IndependentSums.WeakOrlicz`), a
strictly stronger requirement than the `MonotoneOn` already proved by the
library's own `gammaSigma_monotoneOn`. Since `Γ_σ(t) = exp(t^σ)` and `t ↦ t^σ`
is strictly increasing on `t ≥ 0` for `σ > 0` (`Real.rpow_lt_rpow`), composed
with the strictly increasing `Real.exp`, `Γ_σ` is strictly monotone on
`t ≥ 0`. -/

@[expose] public section

/-- **`Γ_σ` is strictly monotone on `[0,∞)`, for `σ > 0`.** -/
theorem SuperdiffusionCLT.Section4.HomogBelow.homogBelow_gammaSigma_strictMonoOn
    {sigma : ℝ} (hsigma : 0 < sigma) :
    StrictMonoOn (Homogenization.IndependentSums.gammaSigma sigma) (Set.Ici (0 : ℝ)) := by
  intro x hx y _hy hxy
  simp only [Homogenization.IndependentSums.gammaSigma_apply]
  exact Real.exp_lt_exp.mpr (Real.rpow_lt_rpow hx hxy hsigma)
