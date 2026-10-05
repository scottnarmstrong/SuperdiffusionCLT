/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.DivergenceForm.Decay.MaximumPrinciple
public import SuperdiffusionCLT.Section8.DivergenceForm.ScalarWeakSolutionRestriction
public import SuperdiffusionCLT.Section8.DivergenceForm.Regularity.ScalarWeakMaximumPrinciple
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitMeanValueIdentificationGreen
public import Homogenization.Sobolev.Truncation.MatchedTrace

/-!
# The shifted weak maximum principle with matched boundary data

On a bounded open convex domain `U`, let `ψ` be an `H¹(U)` function which solves the shifted
equation `-div (a ∇ψ) = g_ψ` weakly, and let `v ∈ H¹₀(U)` solve `-div (a ∇v) = g_v` weakly, with
`g_ψ - g_v = -α (ψ - v)` almost everywhere.  If the truncations `(ψ - M)₊` and `(-ψ - M)₊` lie in
`H¹₀(U)` then `|ψ - v| ≤ M` almost everywhere.  The comparison is the weak maximum principle of
`Decay.ae_le_of_positivePart_zeroTrace` (zero potential, shift `α > 0`), run for `ψ - v` and
`v - ψ`, with the zero-trace hypothesis on the truncation of `ψ - v` obtained from the matched-trace
truncation lemma.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section8.DivergenceForm

variable {d : ℕ} {U : Set (Vec d)}

/-- One-sided bound: the upper truncation of `ψ` has zero trace and `ψ - v ∈ H¹`-matches. -/
theorem domId_ae_le_of_matched (hU : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam alpha M : ℝ} (halpha : 0 < alpha) (hM : 0 ≤ M)
    (hEll : IsEllipticFieldOn lam Lam U a) {w ψ : H1Function U}
    (hsol : IsScalarForcedWeakSolution a U (fun x ↦ -(alpha * w.toFun x)) w)
    (hmatch : MemH10 U fun x ↦ w.toFun x - ψ.toFun x)
    (hψ : MemH10 U fun x ↦ max (ψ.toFun x - M) 0) :
    ∀ᵐ x ∂volumeMeasureOn U, w.toFun x ≤ M := by
  have h1 := memH10_max_sub_matched hU w ψ hmatch M
  have h2 : MemH10 U fun x ↦ max (w.toFun x - M) 0 := by
    have h3 := memH10_add h1 hψ
    refine (congrArg (MemH10 U) ?_).mp h3
    funext x
    ring
  refine Decay.ae_le_of_positivePart_zeroTrace hU (q := fun _ ↦ 0) halpha hM hEll
    (Filter.Eventually.of_forall fun _ ↦ le_rfl) ?_ h2
  simpa only [add_zero] using hsol

/-- **The shifted weak maximum principle with matched boundary data.** -/
theorem domId_abs_sub_le_of_matched (hU : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam alpha M : ℝ} (halpha : 0 < alpha) (hM : 0 ≤ M)
    (hEll : IsEllipticFieldOn lam Lam U a) {ψ v : H1Function U} {gψ gv : Vec d → ℝ}
    (hψsol : IsScalarForcedWeakSolution a U gψ ψ) (hvsol : IsScalarForcedWeakSolution a U gv v)
    (hrel : (fun x ↦ gψ x - gv x) =ᵐ[volumeMeasureOn U]
      fun x ↦ -(alpha * (ψ.toFun x - v.toFun x)))
    (hv : MemH10 U v.toFun)
    (hψ : MemH10 U fun x ↦ max (ψ.toFun x - M) 0)
    (hψ' : MemH10 U fun x ↦ max (-ψ.toFun x - M) 0) :
    ∀ᵐ x ∂volumeMeasureOn U, |ψ.toFun x - v.toFun x| ≤ M := by
  have hdiff := (hψsol.sub hEll hvsol).congr_datum
    (g' := fun x ↦ -(alpha * ((ψ - v).toFun x))) (by
      filter_upwards [hrel] with x hx
      rw [H1Function.sub_toFun]
      exact hx.symm)
  have hupper := domId_ae_le_of_matched hU halpha hM hEll hdiff
    (ψ := ψ) (by
      have hn := memH10_neg hv
      refine (congrArg (MemH10 U) ?_).mp hn
      funext x
      rw [H1Function.sub_toFun]
      ring) hψ
  have hneg := hdiff.neg
  have hneg' : IsScalarForcedWeakSolution a U
      (fun x ↦ -(alpha * ((-(ψ - v)).toFun x))) (-(ψ - v)) := by
    refine hneg.congr_datum ?_
    filter_upwards with x
    rw [H1Function.neg_toFun]
    ring
  have hlower := domId_ae_le_of_matched hU halpha hM hEll hneg'
    (ψ := -ψ) (by
      have hn := hv
      refine (congrArg (MemH10 U) ?_).mp hn
      funext x
      rw [H1Function.neg_toFun, H1Function.sub_toFun, H1Function.neg_toFun]
      ring) (by
      refine (congrArg (MemH10 U) ?_).mp hψ'
      funext x
      rw [H1Function.neg_toFun]) 
  filter_upwards [hupper, hlower] with x h1 h2
  rw [H1Function.sub_toFun] at h1
  rw [H1Function.neg_toFun, H1Function.sub_toFun] at h2
  exact abs_le.mpr ⟨by linarith only [h2], by linarith only [h1]⟩

end SuperdiffusionCLT.Section8
