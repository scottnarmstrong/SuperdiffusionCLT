/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.ProcessUniqueness
public import SuperdiffusionCLT.Section8.Prereq.HeatWitnessC
public import SuperdiffusionCLT.Section8.Convergence.InvariancePrinciple

/-!
# Uniqueness of the divergence-form Feller semigroup and of its path laws

Continuation of `ProcessUniqueness.lean`: the resolvent of a specification semigroup is `R_μ`
on all of `C₀`, so the semigroup is the kernel semigroup of `R`; path laws with the same
finite-dimensional distributions coincide.
-/

@[expose] public section

open scoped ZeroAtInfty NNReal ENNReal ContDiff

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess

variable {d : ℕ}

theorem procUniq_contractiveResolvent_ext
    (X Y : Semigroup.ContractiveResolvent C₀(Vec d, ℝ)) (h : X.operator = Y.operator) :
    X = Y := by
  obtain ⟨_, _, _, _⟩ := X
  obtain ⟨_, _, _, _⟩ := Y
  cases h
  rfl

theorem procUniq_positiveResolvent_ext
    (X Y : PositiveC0ContractiveResolvent (Vec d))
    (h : X.toContractiveResolvent.operator = Y.toContractiveResolvent.operator) :
    X = Y := by
  obtain ⟨X, hX⟩ := X
  obtain ⟨Y, hY⟩ := Y
  have := procUniq_contractiveResolvent_ext X Y h
  cases this
  rfl

/-- The resolvent of a specification semigroup is `R_μ` on all of `C₀`. -/
theorem procUniq_resolvent_eq (a : CoeffField d)
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hreg : ∀ (mu : Semigroup.PositiveShift) (g : C₀(Vec d, ℝ)), ContDiff ℝ ∞ (⇑g) →
        HasCompactSupport (⇑g) →
        ContDiff ℝ 2 (⇑(R.toContractiveResolvent.operator mu g)) ∧
          ∀ x, divForm 1 a (⇑(R.toContractiveResolvent.operator mu g)) x =
            (mu : ℝ) * R.toContractiveResolvent.operator mu g x - g x)
    {S : SubMarkovKernelSemigroup (Vec d)} (hF : S.IsFellerKernelSemigroup)
    (hspec : ∀ u v : C₀(Vec d, ℝ), ContDiff ℝ 2 (⇑u) → (∀ x, v x = divForm 1 a (⇑u) x) →
      ∃ hu : u ∈ hF.c0Semigroup.generatorDomain, hF.c0Semigroup.generator ⟨u, hu⟩ = v)
    (mu : Semigroup.PositiveShift) :
    hF.c0Semigroup.resolvent mu = R.toContractiveResolvent.operator mu := by
  have hfun : (⇑(hF.c0Semigroup.resolvent mu) : C₀(Vec d, ℝ) → C₀(Vec d, ℝ)) =
      ⇑(R.toContractiveResolvent.operator mu) :=
    Continuous.ext_on (Brownian.heatCore_dense_smooth d)
      (hF.c0Semigroup.resolvent mu).continuous
      (R.toContractiveResolvent.operator mu).continuous
      (fun g hg ↦ procUniq_resolvent_eq_on_smooth a R hreg hF hspec mu g hg.1 hg.2)
  exact ContinuousLinearMap.ext (congrFun hfun)

/-- **Uniqueness of the semigroup.**  If the resolvent `R` has `C²` regularity on smooth compactly
supported data, then every divergence-form Feller semigroup is the kernel semigroup of `R`. -/
theorem procUniq_kernelSemigroup_eq (a : CoeffField d)
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hreg : ∀ (mu : Semigroup.PositiveShift) (g : C₀(Vec d, ℝ)), ContDiff ℝ ∞ (⇑g) →
        HasCompactSupport (⇑g) →
        ContDiff ℝ 2 (⇑(R.toContractiveResolvent.operator mu g)) ∧
          ∀ x, divForm 1 a (⇑(R.toContractiveResolvent.operator mu g)) x =
            (mu : ℝ) * R.toContractiveResolvent.operator mu g x - g x)
    {S : SubMarkovKernelSemigroup (Vec d)} (hS : IsDivergenceFormFeller a S) :
    S = R.kernelSemigroup := by
  obtain ⟨-, hF, hspec⟩ := hS
  have hR : hF.positiveC0ContractiveResolvent = R := by
    refine procUniq_positiveResolvent_ext _ _ ?_
    funext mu
    exact procUniq_resolvent_eq a R hreg hF hspec mu
  rw [← hF.kernelSemigroup_positiveC0ContractiveResolvent, hR]

/-- **Path laws are determined by their finite-dimensional distributions.**  Two probability laws
on continuous paths with the same finite-dimensional distributions coincide. -/
theorem procUniq_measure_eq_of_map_finsetEvaluation
    {P P' : Measure (ContinuousPath (Vec d))} [IsFiniteMeasure P]
    (h : ∀ I : Finset ℝ≥0, P.map (ContinuousPath.finsetEvaluation I) =
      P'.map (ContinuousPath.finsetEvaluation I)) : P = P' := by
  have hk := Kernel.eq_of_map_denseFiniteEvaluation_eq
    (ProbabilityTheory.Kernel.const Unit P) (ProbabilityTheory.Kernel.const Unit P')
    (fun I ↦ by
      have hm : Measurable (ContinuousPath.finsetEvaluation (alpha := Vec d)
          (SubMarkovKernelSemigroup.denseTimePhysicalSet I)) :=
        measurable_pi_iff.mpr fun t ↦ ContinuousPath.measurable_coordinateProcess (t : ℝ≥0)
      rw [ProbabilityTheory.Kernel.map_const _ hm, ProbabilityTheory.Kernel.map_const _ hm]
      exact congrArg (ProbabilityTheory.Kernel.const Unit) (h _))
  simpa using DFunLike.congr_fun hk ()

/-- **Uniqueness of the path laws of a semigroup.** -/
theorem procUniq_pathLaw_eq {S : SubMarkovKernelSemigroup (Vec d)}
    {Q Q' : Vec d → Measure (ContinuousPath (Vec d))} (hQ : IsContinuousPathLaw S Q)
    (hQ' : IsContinuousPathLaw S Q') : Q = Q' := by
  funext x
  obtain ⟨hp, hf⟩ := hQ x
  obtain ⟨-, hf'⟩ := hQ' x
  have : IsFiniteMeasure (Q x) := inferInstance
  exact procUniq_measure_eq_of_map_finsetEvaluation fun I ↦ (hf I).trans (hf' I).symm

/-- **Uniqueness of the process.**  Under the regularity of `R`, the pair of a divergence-form
Feller semigroup and a continuous-path law is unique once it exists. -/
theorem procUniq_existsUnique (a : CoeffField d)
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hreg : ∀ (mu : Semigroup.PositiveShift) (g : C₀(Vec d, ℝ)), ContDiff ℝ ∞ (⇑g) →
        HasCompactSupport (⇑g) →
        ContDiff ℝ 2 (⇑(R.toContractiveResolvent.operator mu g)) ∧
          ∀ x, divForm 1 a (⇑(R.toContractiveResolvent.operator mu g)) x =
            (mu : ℝ) * R.toContractiveResolvent.operator mu g x - g x)
    (hex : ∃ (S : SubMarkovKernelSemigroup (Vec d))
        (Q : Vec d → Measure (ContinuousPath (Vec d))),
        IsDivergenceFormFeller a S ∧ IsContinuousPathLaw S Q) :
    ∃! p : SubMarkovKernelSemigroup (Vec d) × (Vec d → Measure (ContinuousPath (Vec d))),
      IsDivergenceFormFeller a p.1 ∧ IsContinuousPathLaw p.1 p.2 := by
  obtain ⟨S, Q, hS, hQ⟩ := hex
  refine ⟨(S, Q), ⟨hS, hQ⟩, fun ⟨S', Q'⟩ ⟨hS', hQ'⟩ ↦ ?_⟩
  have hSS : S' = S :=
    (procUniq_kernelSemigroup_eq a R hreg hS').trans
      (procUniq_kernelSemigroup_eq a R hreg hS).symm
  subst hSS
  exact Prod.ext rfl (procUniq_pathLaw_eq hQ' hQ)

/-! ## Satisfiability witness: the heat semigroup -/

end SuperdiffusionCLT.Section8
