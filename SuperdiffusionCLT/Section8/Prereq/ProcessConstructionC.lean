/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.ProcessConstructionB
public import SuperdiffusionCLT.Section8.Prereq.FieldProcessInputL
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusion

/-!
# The Feller process of the marginal field on `ℝ^d`

The continuous process of the one-point compactification, which almost surely stays in `ℝ^d`
when started there, is read back in `ℝ^d`.  For almost every sample, the kernel semigroup of the
analytic minimal resolvent of `∇·(ν Id + k - k(0))∇` is a conservative Feller kernel semigroup
which carries a continuous-path law from every starting point.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess MarkovProcess.Semigroup
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section8.DivergenceForm
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-- At a live point the compactified kernels of a conservative resolvent are the original kernels
pushed into the compactification. -/
theorem procConstr_onePointKernelSemigroup_coe {R : PositiveC0ContractiveResolvent (Vec d)}
    (hcons : R.kernelSemigroup.IsConservative) (t : ℝ≥0) (x : Vec d) :
    R.onePointKernelSemigroup t (x : OnePoint (Vec d)) =
      (R.kernelSemigroup t x).map ((↑) : Vec d → OnePoint (Vec d)) := by
  rw [R.onePointKernelSemigroup_apply_coe t x, hcons t x]
  simp

/-- **A continuous-path law of the kernel semigroup of a resolvent with a tail input.**  If the
kernel semigroup of the positive contractive resolvent `R` is conservative and the resolvent
carries the variable exhaustion-tail input, then there is a probability law on continuous paths of
`ℝ^d`, from every starting point, with the finite-dimensional distributions of the kernel
semigroup. -/
theorem procConstr_exists_isContinuousPathLaw {R : PositiveC0ContractiveResolvent (Vec d)}
    (H : WholeSpaceVariableExhaustionResolventTailInput R)
    (hcons : R.kernelSemigroup.IsConservative) :
    ∃ Q : Vec d → Measure (ContinuousPath (Vec d)), IsContinuousPathLaw R.kernelSemigroup Q := by
  have hemb : Topology.IsOpenEmbedding ((↑) : Vec d → OnePoint (Vec d)) :=
    OnePoint.isOpenEmbedding_coe
  exact letI := H.toOnePointRegular.metricSpace
    letI := H.toOnePointRegular.completeSpace
    procConstr_exists_pathLaw hemb.isEmbedding hemb.measurableEmbedding hcons
      R.isConservative_onePointKernelSemigroup (procConstr_onePointKernelSemigroup_coe hcons)
      H.wholeSpaceProcess H.wholeSpaceProcess_spec.1 H.wholeSpaceProcess_spec.2
      (fun x ↦ H.wholeSpaceProcess_ae_stays_live hcons x)

/-- **Existence of the process of the marginal field, construction part.**  For almost every
sample, the kernel semigroup `S` of the analytic minimal resolvent of `∇·(nu Id + k - k(0))∇` is a
conservative Feller kernel semigroup on `C₀(ℝ^d)` with a continuous-path law `Q x` from every
starting point `x`, and its resolvent is identified with the analytic minimal resolvent. -/
theorem procConstr_ae_exists_process [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∃ (S : SubMarkovKernelSemigroup (Vec d))
        (Q : Vec d → Measure (ContinuousPath (Vec d))),
        S.IsFellerKernelSemigroup ∧ S.IsConservative ∧ IsContinuousPathLaw S Q ∧
          ∃ (A : WholeSpaceAnalyticData d) (R : PositiveC0ContractiveResolvent (Vec d)),
            A.a = fullCoefficientRecentered nu omega ∧ A.nu = nu ∧ S = R.kernelSemigroup ∧
              A.KernelResolventIdentifiesAnalyticMinimal R := by
  filter_upwards [fieldInput_ae_processInput hPrefix hJ3 hnu] with omega hω
  obtain ⟨A, R, hA, hAnu, hcons, hid, ⟨H⟩⟩ := hω
  obtain ⟨Q, hQ⟩ := procConstr_exists_isContinuousPathLaw H hcons
  exact ⟨R.kernelSemigroup, Q, R.isFellerKernelSemigroup_kernelSemigroup, hcons, hQ,
    A, R, hA, hAnu, rfl, hid⟩

/-! ## Satisfiability witness -/

/-- The packaged statement holds for the law concentrated on the zero shell sequence. -/
example [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∃ (S : SubMarkovKernelSemigroup (Vec d))
        (Q : Vec d → Measure (ContinuousPath (Vec d))),
        S.IsFellerKernelSemigroup ∧ S.IsConservative ∧ IsContinuousPathLaw S Q ∧
          ∃ (A : WholeSpaceAnalyticData d) (R : PositiveC0ContractiveResolvent (Vec d)),
            A.a = fullCoefficientRecentered nu omega ∧ A.nu = nu ∧ S = R.kernelSemigroup ∧
              A.KernelResolventIdentifiesAnalyticMinimal R :=
  procConstr_ae_exists_process
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu

end

end SuperdiffusionCLT.Section8
