/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import SuperdiffusionCLT.Assumptions.ShellField.Basic
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.LawUniqueness

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions

open scoped Matrix.Norms.Elementwise

variable {d : ℕ}

/-- Real-valued evaluation functionals of the shell carrier: matrix entries at points. -/
def nv_shellEv (d : ℕ) : (Vec d × Fin d × Fin d) → ShellField d → ℝ :=
  fun p j => j p.1 p.2.1 p.2.2

theorem nv_sc1 (d : ℕ) : SecondCountableTopology (Vec d →L[ℝ] Mat d) := by
  have : FiniteDimensional ℝ (Vec d →L[ℝ] Mat d) := inferInstance
  have : ProperSpace (Vec d →L[ℝ] Mat d) := FiniteDimensional.proper_real (Vec d →L[ℝ] Mat d)
  exact secondCountable_of_proper

theorem nv_sc2 (d : ℕ) : SecondCountableTopology (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := by
  have : FiniteDimensional ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance
  have : ProperSpace (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := FiniteDimensional.proper_real _
  exact secondCountable_of_proper

theorem nv_borel_ambient (d : ℕ) : BorelSpace (ShellAmbient d) := by
  have h0 : SecondCountableTopology (Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  have h1 := nv_sc1 d
  have h2 := nv_sc2 d
  have e1 : SecondCountableTopology C(Vec d, Mat d) := inferInstance
  have e2 : SecondCountableTopology C(Vec d, Vec d →L[ℝ] Mat d) := inferInstance
  have e3 : SecondCountableTopology C(Vec d, Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance
  have e4 : SecondCountableTopology (C(Vec d, Vec d →L[ℝ] Mat d) ×
      C(Vec d, Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))) := inferInstance
  exact Prod.borelSpace

theorem nv_shellField_ms_eq (d : ℕ) :
    shellFieldMeasurableSpace d =
      MeasurableSpace.comap (Subtype.val : ShellField d → ShellAmbient d) inferInstance := by
  have := nv_borel_ambient d
  rw [BorelSpace.measurable_eq (α := ShellAmbient d)]
  have ht : (shellFieldTopologicalSpace d) =
      TopologicalSpace.induced (Subtype.val : ShellField d → ShellAmbient d) inferInstance := rfl
  unfold shellFieldMeasurableSpace shellFieldBorelMeasurableSpace
  exact borel_comap (f := (Subtype.val : ShellField d → ShellAmbient d))

/-- Directional derivatives of a pointwise-measurable family are measurable. -/
theorem nv_measurable_dirDeriv {α V E : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (hB : BorelSpace E) (hS : SecondCountableTopology E)
    (g : α → V → E) (D : α → V → (V →L[ℝ] E)) (hg : ∀ a x, HasFDerivAt (g a) (D a x) x)
    (hm : ∀ x, Measurable fun a => g a x) (x v : V) : Measurable fun a => D a x v := by
  have := hB
  have := hS
  have hlim : ∀ a, Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) + 1) • (g a (x + (1 / ((n : ℝ) + 1)) • v) - g a x))
      Filter.atTop (nhds (D a x v)) := by
    intro a
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have h2 : HasFDerivAt (g a) (D a x) (x + (0 : ℝ) • v) := by simpa using hg a x
    have h3 : HasDerivAt (fun t : ℝ => g a (x + t • v)) (D a x v) 0 := h2.comp_hasDerivAt 0 h1
    have h4 := h3.tendsto_slope_zero
    have h5 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop
        (nhdsWithin 0 {0}ᶜ) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Filter.Eventually.of_forall fun n => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; positivity⟩
    refine (h4.comp h5).congr fun n => ?_
    simp
  refine measurable_of_tendsto_metrizable (fun n => ?_) (tendsto_pi_nhds.2 hlim)
  exact ((hm _).sub (hm x)).const_smul _

/-- A family of continuous linear maps out of `Vec d` is measurable once every application is. -/
theorem nv_measurable_clm_of_apply {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] (hB : BorelSpace E) (hS : SecondCountableTopology E)
    (F : α → (Vec d →L[ℝ] E)) (h : ∀ v, Measurable fun a => F a v) : Measurable F := by
  have := hB
  have := hS
  have hsum : F = fun a => ∑ i : Fin d,
      (ContinuousLinearMap.smulRightL ℝ (Vec d) E (ContinuousLinearMap.proj i))
        (F a (Pi.single i 1)) := by
    funext a
    ext v
    have hv : v = ∑ i : Fin d, v i • (Pi.single i (1 : ℝ) : Vec d) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    simp [map_sum]
  rw [hsum]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (ContinuousLinearMap.continuous _).measurable.comp (h _)

theorem nv_shellEv_measurable (d : ℕ) (i : Vec d × Fin d × Fin d) :
    Measurable (nv_shellEv d i) :=
  ShellField.measurable_eval_entry i.1 i.2.1 i.2.2

/-- The sigma-algebra generated by the matrix-entry evaluations at all points. -/
abbrev nv_shellEvalSigma (d : ℕ) : MeasurableSpace (ShellField d) :=
  ⨆ i, MeasurableSpace.comap (nv_shellEv d i) inferInstance

theorem nv_shellEvalSigma_le (d : ℕ) : nv_shellEvalSigma d ≤ shellFieldMeasurableSpace d :=
  iSup_le fun i => (nv_shellEv_measurable d i).comap_le

theorem nv_val_measurable (d : ℕ) :
    Measurable[nv_shellEvalSigma d] (Subtype.val : ShellField d → ShellAmbient d) := by
  let _ : MeasurableSpace (ShellField d) := nv_shellEvalSigma d
  have h0 : SecondCountableTopology (Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  have h1 := nv_sc1 d
  have h2 := nv_sc2 d
  have hB0 : BorelSpace (Mat d) := inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))
  borelize (Vec d →L[ℝ] Mat d) (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))
  have hB1 : BorelSpace (Vec d →L[ℝ] Mat d) := inferInstance
  have hv : ∀ x : Vec d, Measurable fun j : ShellField d => j x := fun x =>
    Measurable.of_eval_matrix _ fun i k =>
      (comap_measurable (nv_shellEv d (x, i, k))).mono
        (le_iSup (fun i => MeasurableSpace.comap (nv_shellEv d i) inferInstance) (x, i, k)) le_rfl
  have hD1 : ∀ x : Vec d, Measurable fun j : ShellField d => ShellField.deriv j x := fun x =>
    nv_measurable_clm_of_apply (by exact hB0) (by exact h0) _ fun v =>
      nv_measurable_dirDeriv (by exact hB0) (by exact h0) (fun (j : ShellField d) (y : Vec d) => j y)
        (fun j y => ShellField.deriv j y) ShellField.hasFDerivAt hv x v
  have hD2 : ∀ x : Vec d, Measurable fun j : ShellField d => ShellField.secondDeriv j x :=
    fun x => nv_measurable_clm_of_apply (by exact hB1) (by exact h1) _ fun v =>
      nv_measurable_dirDeriv (by exact hB1) (by exact h1)
        (fun (j : ShellField d) (y : Vec d) => ShellField.deriv j y)
        (fun j y => ShellField.secondDeriv j y) ShellField.deriv_hasFDerivAt hD1 x v
  exact (ContinuousMap.measurable_iff_eval.2 hv).prodMk
    ((ContinuousMap.measurable_iff_eval.2 hD1).prodMk (ContinuousMap.measurable_iff_eval.2 hD2))

/-- The shell carrier's sigma-algebra is generated by the matrix-entry evaluations. -/
theorem nv_shellField_generatedBy_eval (d : ℕ) :
    shellFieldMeasurableSpace d =
      ⨆ i, MeasurableSpace.comap (nv_shellEv d i) (inferInstance : MeasurableSpace ℝ) := by
  refine le_antisymm ?_ (nv_shellEvalSigma_le d)
  rw [nv_shellField_ms_eq d]
  exact (measurable_iff_comap_le (m₁ := nv_shellEvalSigma d)).1 (nv_val_measurable d)

/-- Two-measure transport form on the shell carrier. -/
theorem nv_shellField_map_eq (d : ℕ) (T : ShellField d → ShellField d) (hT : Measurable T)
    (μ ν : MeasureTheory.Measure (ShellField d)) [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.IsProbabilityMeasure ν]
    (h : ∀ s : Finset (Vec d × Fin d × Fin d),
      μ.map (fun j (i : s) => nv_shellEv d i (T j)) =
        ν.map (fun j (i : s) => nv_shellEv d i j)) :
    μ.map T = ν :=
  nv_map_eq_of_evaluation_marginals (nv_shellEv d) (nv_shellField_generatedBy_eval d) T hT μ ν h

/-- Invariance form on the shell carrier. -/
theorem nv_shellField_map_eq_self (d : ℕ) (T : ShellField d → ShellField d)
    (hT : Measurable T) (μ : MeasureTheory.Measure (ShellField d))
    [MeasureTheory.IsProbabilityMeasure μ]
    (h : ∀ s : Finset (Vec d × Fin d × Fin d),
      μ.map (fun j (i : s) => nv_shellEv d i (T j)) =
        μ.map (fun j (i : s) => nv_shellEv d i j)) :
    μ.map T = μ :=
  nv_shellField_map_eq d T hT μ μ h

/-- Witness: the identity and a translation preserve a Dirac law on a shell field, through the
transport form. -/
example (d : ℕ) (j : ShellField d) :
    (MeasureTheory.Measure.dirac j).map (id : ShellField d → ShellField d) =
      MeasureTheory.Measure.dirac j := by
  have : MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.dirac j) := inferInstance
  exact nv_shellField_map_eq_self d id measurable_id _ (fun _ => rfl)

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
