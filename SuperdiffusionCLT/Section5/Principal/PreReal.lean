/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.FiniteToInfiniteB
public import SuperdiffusionCLT.Section5.Principal.FiniteToInfiniteC
public import SuperdiffusionCLT.Section5.Principal.AverageMomentF

/-!
# The pre-average inequality in the form fed by the conditional

Integrability inputs and quadratic-form identities for the pre-average chain: for one subcube `R`,
an `F_new`-measurable upper bound `D'` of `D_z` and an `F_new`-measurable vector `P̂`, the printed
chain
`E[P·A_m P] ≤ E[(1+D')P̂·A_{m-h} P̂] = E[(1+D')P̂·bfAhom_{m-h}(R) P̂] ≤ (1+ε) E[(1+D')|bfAhom^{1/2} P̂|²]`
(`e.principal.switch`, `e.principal.conditional`, `e.principal.fv.to.inf`) in `ℝ≥0∞`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Probability (shellSigma shellSigma_le_ambient)
open scoped ENNReal

variable {d : ℕ}

/-- The weighted quadratic form of a constant matrix is integrable if the weights are. -/
theorem integrable_weight_quad {μ : Measure (ShellSeq d)} {D : ShellSeq d → ℝ}
    {Phat : ShellSeq d → BlockVec d}
    (hint : ∀ α β : BlockCoord d, Integrable
      (fun ω => (1 + D ω) * (toFullBlockVec (Phat ω) α * toFullBlockVec (Phat ω) β)) μ)
    (M : BlockMat d) :
    Integrable (fun ω => (1 + D ω) * blockVecDot (Phat ω) (blockMatVecMul M (Phat ω))) μ := by
  have hrw : ∀ ω, (1 + D ω) * blockVecDot (Phat ω) (blockMatVecMul M (Phat ω)) =
      ∑ α : BlockCoord d, ∑ β : BlockCoord d,
        ((1 + D ω) * (toFullBlockVec (Phat ω) α * toFullBlockVec (Phat ω) β)) *
          blockMatEntry M α β := by
    intro ω
    rw [SuperdiffusionCLT.Section3.HighContrast.blockVecDot_blockMatVecMul_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  simp only [hrw]
  exact integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
    (hint α β).mul_const _

/-- Integrability of the weighted old quadratic form, from the independence of the fresh and old
shells. -/
theorem principal_old_integrable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m h : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (R : TriadicCube d)
    {D : ShellSeq d → ℝ} {Phat : ShellSeq d → BlockVec d}
    (hD : Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)] D)
    (hPhat : ∀ α : BlockCoord d,
      Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)] (fun ω => toFullBlockVec (Phat ω) α))
    (hint : ∀ α β : BlockCoord d, Integrable
      (fun ω => (1 + D ω) * (toFullBlockVec (Phat ω) α * toFullBlockVec (Phat ω) β))
      P.toMeasure) :
    Integrable (fun ω => (1 + D ω) * blockVecDot (Phat ω)
        (blockMatVecMul (localizationCoarseAt nu (m - h) R ω) (Phat ω))) P.toMeasure := by
  set w : BlockCoord d → BlockCoord d → ShellSeq d → ℝ := fun α β ω =>
    (1 + D ω) * (toFullBlockVec (Phat ω) α * toFullBlockVec (Phat ω) β) with hw
  set E : BlockCoord d → BlockCoord d → ShellSeq d → ℝ := fun α β ω =>
    blockMatEntry (localizationCoarseAt nu (m - h) R ω) α β with hE
  have hEint : ∀ α β, Integrable (E α β) P.toMeasure := fun α β =>
    integrable_blockMatEntry_coarseBlockMatrix hnu (m - h) R hPrefix hJ2 hJ3 hJ4 α β
  have hEmeas : ∀ α β, Measurable[shellSigma (d := d) (localizationLowerShells (m - h))]
      (E α β) := by
    intro α β
    have := measurable_coarseEntry_oldShells hnu (m - h) R α β
    cases α <;> cases β <;> exact this
  have hwmeas : ∀ α β, Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)] (w α β) := by
    intro α β
    exact (measurable_const.add hD).mul ((hPhat α).mul (hPhat β))
  have hindep : ∀ α β, ProbabilityTheory.IndepFun (w α β) (E α β) P.toMeasure := fun α β =>
    indepFun_newShells_oldShells hJ2 m h (hwmeas α β) (hEmeas α β)
  have hLeft : ∀ ω, (1 + D ω) * blockVecDot (Phat ω)
      (blockMatVecMul (localizationCoarseAt nu (m - h) R ω) (Phat ω)) =
        ∑ α : BlockCoord d, ∑ β : BlockCoord d, w α β ω * E α β ω := by
    intro ω
    rw [SuperdiffusionCLT.Section3.HighContrast.blockVecDot_blockMatVecMul_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [hw, hE]
    ring
  simp only [hLeft]
  exact integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
    (hindep α β).integrable_mul (hint α β) (hEint α β)

/-- The quadratic form of the diagonal matrix `Ā_L` is the squared length of
`Ā_L^{1/2} X`. -/
theorem ahomInfinite_quad [NeZero d] (nu : ℝ) (L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (hσ : 0 < sigmaBarInfinite nu L P) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (ahomInfinite nu L P) X) =
      blockLenSq (ahomSqrtApply nu L P X) := by
  obtain ⟨p, q⟩ := X
  unfold ahomInfinite blockLenSq ahomSqrtApply
  rw [blockVecDot_blockMatVecMul_blockDiag_smul_one]
  simp only [vecNormSq_smul]
  have h1 : (sigmaBarInfinite nu L P ^ ((1 : ℝ) / 2)) ^ 2 = sigmaBarInfinite nu L P := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hσ.le]; norm_num
  have h2 : (sigmaBarInfinite nu L P ^ (-(1 : ℝ) / 2)) ^ 2 = (sigmaBarInfinite nu L P)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hσ.le]
    norm_num
    exact Real.rpow_neg_one _
  rw [h1, h2]

end SuperdiffusionCLT.Section5
