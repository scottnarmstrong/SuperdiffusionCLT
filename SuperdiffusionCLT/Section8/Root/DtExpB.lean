/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.DtExp
public import SuperdiffusionCLT.Section8.Common.Regularity.Ported.HarmonicReplacement

/-!
# The stopped solution on a ball as a Dirichlet solution

For the process input `D` of the sample, a ball `B_R` and a `C²` compactly supported datum `b`,
the function `b + w - σ τ` (with `w` the zero-trace solution of `-L w = L b` and `τ` the torsion
function) is an `H¹(B_R)` Dirichlet solution of `-∇·(a∇v) = -σ` with trace `b`, and the stopped
identity holds for it.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section7
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open scoped Pointwise ENNReal NNReal

variable {d : ℕ} [NeZero d] {nu : ℝ}

/-- **The stopped solution on a ball.** -/
theorem dtExp_ball_solution {omega : ShellSeq d}
    (D : FieldInputData d nu (fullStreamRecentered omega))
    (hDa : D.analyticData.a = fullCoefficientRecentered nu omega)
    (ha : ∀ i j, ContDiff ℝ 1 fun y => fullCoefficientRecentered nu
      omega y i j)
    {R : ℝ} (hR : 0 < R) {b : Vec d → ℝ} (hb : ContDiff ℝ 2 b) (hbc : HasCompactSupport b)
    (σ : ℝ) :
    ∃ (w τ : Vec d → ℝ) (g v : H1Function (euclideanBall (0 : Vec d) R)),
      Continuous w ∧ Continuous τ ∧ (∀ y, y ∉ euclideanBall (0 : Vec d) R → w y = 0) ∧
      (∀ y, y ∉ euclideanBall (0 : Vec d) R → τ y = 0) ∧ (∀ y, 0 ≤ τ y) ∧
      IsDirichletSolution (fullCoefficientRecentered nu omega)
        (euclideanBall (0 : Vec d) R) (fun _ => -σ) g v ∧
      (∀ x, g.toFun x = b x) ∧ (∀ x, g.grad x = fun i => fderiv ℝ b x (basisVec i)) ∧
      (∀ᵐ x ∂(volume.restrict (euclideanBall (0 : Vec d) R)),
        v.toFun x = b x + w x - σ * τ x) ∧
      ∀ {Q : Vec d → Measure (ContinuousPath (Vec d))},
        IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q →
        ∀ (t : NNReal),
        ∫ path, (fun z => b z + w z - σ * τ z)
            (path (ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d) R) t path)) ∂(Q 0) =
          (b 0 + w 0 - σ * τ 0) +
            σ * ∫ path, ((ContinuousPath.exitTimeTrunc (euclideanBall (0 : Vec d) R) t path :
              NNReal) : ℝ) ∂(Q 0) := by
  have hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    (0 : Vec d) hR
  obtain ⟨w, uw, hwc, hwoff, hwu, hsol, hQ⟩ := dirRep_stopped D (0 : Vec d) hR hb hbc
  obtain ⟨uτ, hτu, hτsol⟩ := dirRep_h10_solution D (0 : Vec d) hR (f := fun _ : Vec d => (1 : ℝ))
    measurable_const (M := 1) (fun _ => by simp) (fun _ => zero_le_one)
  have hEll := partEllipticity D.analyticData hV
  rw [hDa] at hEll hsol hτsol
  have h0 : (0 : Vec d) ∈ euclideanBall (0 : Vec d) R := by
    simp only [euclideanBall, euclideanSqDist, Set.mem_ofPred_eq, sub_self]
    simpa [vecNormSq, vecDot] using pow_pos hR 2
  have hbw := domId_weak_of_classical hV ha (hb.of_le (by norm_num))
  have h1 := dtExp_forced_add hEll hbw hsol
  have h2 := dtExp_forced_smul (-σ) hτsol
  have h3 := dtExp_forced_add hEll h1 h2
  set gB : H1Function (euclideanBall (0 : Vec d) R) :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hV (hb.of_le (by norm_num)) with hgB
  have hgBf : ∀ x, gB.toFun x = b x := fun x => rfl
  refine ⟨w, dirRep_torsion D (0 : Vec d) hR, gB, (gB + uw.toH1Function) + (-σ) • uτ.toH1Function,
    hwc, dirRep_torsion_continuous D (0 : Vec d) hR, hwoff,
    fun y hy => dirRep_torsion_off D (0 : Vec d) hR hy, dirRep_torsion_nonneg D (0 : Vec d) hR,
    ⟨?_, ?_⟩, hgBf, fun x => rfl, ?_, fun {Q} hQ' t => ?_⟩
  · intro φ
    have := h3.2 φ
    have z : (∫ x in euclideanBall (0 : Vec d) R, vecDot ((fun _ => (0 : Vec d)) x)
        (φ.toH1Function.grad x)) = 0 := by simp [vecDot]
    rw [z, add_zero]
    refine this.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
    simp only [neg_add_cancel, zero_add]
    ring
  · have := memH10_add (uw.memH10) (memH10_smul (-σ) (uτ.memH10))
    convert this using 1
    funext x
    simp only [H1Function.add_toFun, H1Function.smul_toFun, hgBf]
    ring
  · filter_upwards [hwu, hτu] with x h1 h2
    simp only [H1Function.add_toFun, H1Function.smul_toFun, hgBf, ← h1, ← h2, dirRep_torsion]
    ring
  · exact hQ hQ' (y := 0) h0 t σ

end SuperdiffusionCLT.Section8
