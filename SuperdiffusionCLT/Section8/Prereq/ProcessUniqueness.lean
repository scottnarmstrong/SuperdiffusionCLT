/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusion
public import MarkovProcess.Feller.Resolvent
public import MarkovProcess.Kernel.PositiveC0Resolvent
public import SuperdiffusionCLT.Section8.Brownian.HeatCoreC

/-!
# Uniqueness of the divergence-form Feller semigroup from regularity of the minimal resolvent

Let `R` be a positive contractive `C₀` resolvent (the minimal one, in the application) such that,
for every smooth compactly supported datum `g` and every shift `μ > 0`, the function
`u = R_μ g` is `C²` and solves `μ u - ∇·(a∇u) = g` pointwise.  Then every conservative Feller
kernel semigroup `S` whose generator acts as `∇·(a∇·)` on `C² ∩ C₀` (with `C₀` image) is the kernel
semigroup of `R`: `u` lies in the generator domain of `S` with `(μ - L_S) u = g`, so the resolvent
of `S` agrees with `R_μ` on the dense set of smooth compactly supported data, hence everywhere,
hence the semigroups and the kernels coincide.
-/

@[expose] public section

open scoped ZeroAtInfty NNReal ENNReal ContDiff

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess

variable {d : ℕ}

/-- The resolvent of a specification semigroup agrees with `R` on smooth compactly supported
data. -/
theorem procUniq_resolvent_eq_on_smooth (a : CoeffField d)
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hreg : ∀ (mu : Semigroup.PositiveShift) (g : C₀(Vec d, ℝ)), ContDiff ℝ ∞ (⇑g) →
        HasCompactSupport (⇑g) →
        ContDiff ℝ 2 (⇑(R.toContractiveResolvent.operator mu g)) ∧
          ∀ x, divForm 1 a (⇑(R.toContractiveResolvent.operator mu g)) x =
            (mu : ℝ) * R.toContractiveResolvent.operator mu g x - g x)
    {S : SubMarkovKernelSemigroup (Vec d)} (hF : S.IsFellerKernelSemigroup)
    (hspec : ∀ u v : C₀(Vec d, ℝ), ContDiff ℝ 2 (⇑u) → (∀ x, v x = divForm 1 a (⇑u) x) →
      ∃ hu : u ∈ hF.c0Semigroup.generatorDomain, hF.c0Semigroup.generator ⟨u, hu⟩ = v)
    (mu : Semigroup.PositiveShift) (g : C₀(Vec d, ℝ)) (hg : ContDiff ℝ ∞ (⇑g))
    (hc : HasCompactSupport (⇑g)) :
    hF.c0Semigroup.resolvent mu g = R.toContractiveResolvent.operator mu g := by
  obtain ⟨h1, h2⟩ := hreg mu g hg hc
  set u := R.toContractiveResolvent.operator mu g with hu
  obtain ⟨hdom, hgen⟩ := hspec u ((mu : ℝ) • u - g) h1 (fun x ↦ by
    rw [h2 x]; simp)
  have h3 := hF.c0Semigroup.resolvent_smul_sub_generator mu ⟨u, hdom⟩
  have h4 : (mu : ℝ) • (⟨u, hdom⟩ : hF.c0Semigroup.generatorDomain).1 -
      hF.c0Semigroup.generator ⟨u, hdom⟩ = g := by
    rw [hgen]
    simp
  rw [h4] at h3
  exact h3

end SuperdiffusionCLT.Section8
