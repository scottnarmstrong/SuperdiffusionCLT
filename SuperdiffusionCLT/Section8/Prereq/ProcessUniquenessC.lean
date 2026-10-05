/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.ProcessUniquenessB
public import SuperdiffusionCLT.Section8.Prereq.DomainIdentificationD
public import SuperdiffusionCLT.Section8.Prereq.ResolventWeakEquation
public import SuperdiffusionCLT.Section8.Prereq.InteriorC2K
public import SuperdiffusionCLT.Section8.Prereq.FieldRegularity

/-!
# Regularity of the minimal resolvent, and almost-sure uniqueness of the process

For a whole-space analytic datum `A` with `C²` coefficient and a positive contractive `C₀`
resolvent `R` identified with the analytic minimal resolvent, `R_μ g` is `C²` and solves
`μ u - ∇·(a∇u) = g` pointwise for every smooth compactly supported `g`.  Hence the process of the
marginal field is unique almost surely.
-/

@[expose] public section

open scoped ZeroAtInfty NNReal ENNReal ContDiff Matrix.Norms.Elementwise

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess
open SuperdiffusionCLT.Section8.DivergenceForm

variable {d : ℕ}

/-- The resolvent `R_μ g` is, pointwise, the analytic minimal resolvent of `g`. -/
theorem procUniq_operator_eq_analytic [NeZero d] (A : WholeSpaceAnalyticData d)
    {R : PositiveC0ContractiveResolvent (Vec d)} (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    (mu : Semigroup.PositiveShift) (g : C₀(Vec d, ℝ)) (x : Vec d) :
    R.toContractiveResolvent.operator mu g x =
      A.analyticMinimalResolventReal mu (fun y ↦ g y) g.continuous.measurable (D := ‖g‖)
        (fun y ↦ domId_abs_le_norm g y) x := by
  have hF := R.isFellerKernelSemigroup_kernelSemigroup
  have h1 := hF.kernelResolventReal_eq_resolvent mu g x
  have h2 := A.kernelResolventReal_eq_analyticMinimalResolventReal R hid mu
    g.continuous.measurable (D := ‖g‖) (fun y ↦ domId_abs_le_norm g y) x
  have h3 : hF.c0Semigroup.resolvent mu g = R.toContractiveResolvent.operator mu g := by
    rw [R.c0Semigroup_kernelSemigroup]
    exact congrArg (fun T ↦ T g) (Semigroup.ContractiveResolvent.resolvent_generatedSemigroup
      R.toContractiveResolvent mu)
  rw [← h3, ← h1]
  exact h2

theorem procUniq_skew [NeZero d] (A : WholeSpaceAnalyticData d) (y : Vec d) (i j : Fin d) :
    A.a y i j + A.a y j i = if i = j then 2 * A.nu else 0 := by
  have h := congrFun (congrFun (A.hsymm y) i) j
  simp only [symmPart, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, mul_one] at h ⊢
    linarith only [h]
  · simp only [hij, ↓reduceIte, mul_zero] at h ⊢
    linarith only [h]

theorem procUniq_exists_cube (x : Vec d) : ∃ m : ℕ, x ∈ wholeSpaceCube d m := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖x‖ (by norm_num : (1 : ℝ) < 3)
  exact ⟨N, domId_mem_cube hN⟩

/-- **Regularity of the minimal resolvent.**  For a `C²` coefficient `A.a`, the resolvent `R_μ g` of
a smooth compactly supported datum is `C²` and solves `μ u - ∇·(a∇u) = g` pointwise. -/
theorem procUniq_hreg [NeZero d] (A : WholeSpaceAnalyticData d)
    (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ A.a y i j) {R : PositiveC0ContractiveResolvent (Vec d)}
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R) (mu : Semigroup.PositiveShift)
    (g : C₀(Vec d, ℝ)) (hg : ContDiff ℝ ∞ (⇑g)) (_hc : HasCompactSupport (⇑g)) :
    ContDiff ℝ 2 (⇑(R.toContractiveResolvent.operator mu g)) ∧
      ∀ x, divForm 1 A.a (⇑(R.toContractiveResolvent.operator mu g)) x =
        (mu : ℝ) * R.toContractiveResolvent.operator mu g x - g x := by
  have hg1 : ContDiff ℝ 1 (⇑g) := hg.of_le (by simp)
  have hmu : (0 : ℝ) < mu := mu.2
  have hcube : ∀ m : ℕ, ∃ um : H1Function (wholeSpaceCube d m),
      um.toFun = ⇑(R.toContractiveResolvent.operator mu g) ∧
      (∀ x, |um.toFun x| ≤ ‖g‖ / mu) ∧ intC2_Weak A.a mu g (wholeSpaceCube d m) um := by
    intro m
    obtain ⟨um, hum, hbd, hweak⟩ := resWeak_exists A m mu g.continuous.measurable
      (norm_nonneg g) (fun y ↦ domId_abs_le_norm g y)
      (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen subset_rfl
    refine ⟨um, ?_, hbd, hweak⟩
    rw [hum]
    funext x
    exact (procUniq_operator_eq_analytic A hid mu g x).symm
  have h2 : ∀ x, ContDiffAt ℝ 2 (⇑(R.toContractiveResolvent.operator mu g)) x := fun x ↦ by
    obtain ⟨m, hm⟩ := procUniq_exists_cube x
    obtain ⟨um, hum, hbd, hweak⟩ := hcube m
    have := intC2_contDiffAt A.hd (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen A.hnu
      (procUniq_skew A) ha hg1 hweak (M := ‖g‖ / mu)
      (by rw [hum]; exact (R.toContractiveResolvent.operator mu g).continuous.continuousOn)
      (fun y _ ↦ hbd y) hm
    rwa [hum] at this
  have hu2 : ContDiff ℝ 2 (⇑(R.toContractiveResolvent.operator mu g)) :=
    contDiff_iff_contDiffAt.2 h2
  refine ⟨hu2, fun x ↦ ?_⟩
  obtain ⟨m, hm⟩ := procUniq_exists_cube x
  obtain ⟨um, hum, hbd, hweak⟩ := hcube m
  have := intC2_pointwise (isOpenBoundedConvexDomain_wholeSpaceCube d m).isOpen
    (isOpenBoundedConvexDomain_wholeSpaceCube d m).isBoundedDomain.isBounded ha g.continuous
    hweak (by rw [hum]; exact hu2) hm
  rwa [hum] at this

open SuperdiffusionCLT.Frozen.Assumptions SuperdiffusionCLT.Section2.Cutoff
  SuperdiffusionCLT.Section6 in
/-- **Almost-sure uniqueness of the process of the marginal field.**  For almost every sample of the
shell field, the pair (conservative divergence-form Feller semigroup, continuous-path law) with
generator `∇·(ν Id + k - k(0))∇` on `C² ∩ C₀` exists and is unique. -/
theorem procUniq_ae_existsUnique [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∃! p : SubMarkovKernelSemigroup (Vec d) × (Vec d → Measure (ContinuousPath (Vec d))),
        IsDivergenceFormFeller (fullCoefficientRecentered nu omega) p.1 ∧
          IsContinuousPathLaw p.1 p.2 := by
  filter_upwards [procConstr_ae_exists_process hPrefix hJ3 hnu,
    fieldReg_ae_contDiff_two_fullStreamRecentered hJ3, domId_ae_exists_process hPrefix hJ3 hnu]
    with omega hω hreg hex
  obtain ⟨S, Q, -, hcons, hQ, A, R, hA, hAnu, rfl, hid⟩ := hω
  have h2 : ContDiff ℝ 2 (fullCoefficientRecentered nu omega) := contDiff_const.add hreg
  have ha : ∀ i j, ContDiff ℝ 2 fun y ↦ A.a y i j := fun i j ↦ by
    rw [hA]; exact contDiff_pi.1 (contDiff_pi.1 h2 i) j
  refine procUniq_existsUnique (fullCoefficientRecentered nu omega) R (fun mu g hg hc ↦ ?_) hex
  have := procUniq_hreg A ha hid mu g hg hc
  rwa [hA] at this

open SuperdiffusionCLT.Frozen.Assumptions SuperdiffusionCLT.Section2.Cutoff
  SuperdiffusionCLT.Section6 in
/-- **Satisfiability witness.**  The statement holds for the law concentrated on the zero shell
sequence (the constant field `ν Id`). -/
example [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∃! p : SubMarkovKernelSemigroup (Vec d) × (Vec d → Measure (ContinuousPath (Vec d))),
        IsDivergenceFormFeller (fullCoefficientRecentered nu omega) p.1 ∧
          IsContinuousPathLaw p.1 p.2 :=
  procUniq_ae_existsUnique
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu

end SuperdiffusionCLT.Section8
