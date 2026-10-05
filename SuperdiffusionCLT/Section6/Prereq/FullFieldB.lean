/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.FullField
public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity
public import Homogenization.Probability.RegCoeffField.EllipticSet
public import SuperdiffusionCLT.Section2.Cutoff.CenteredCoeffOn

/-!
# The infinite-volume stream matrix: skewness, measurability, witnesses
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open scoped Matrix.Norms.Elementwise
open SuperdiffusionCLT.Section2.Carriers

noncomputable section

variable {d : ℕ}

/-- Anti-symmetry of a `tsum` of anti-symmetric matrices (the junk value `0`
is anti-symmetric as well). -/
theorem tsum_skew_entry (f : ℕ → Mat d)
    (hf : ∀ n i k, f n i k = -f n k i) (i k : Fin d) :
    (∑' n, f n) i k = -(∑' n, f n) k i := by
  by_cases hs : Summable f
  · rw [tsum_matrix_apply hs, tsum_matrix_apply hs, ← tsum_neg]
    exact tsum_congr fun n => hf n i k
  · rw [tsum_eq_zero_of_not_summable hs]
    simp

theorem fullStreamRecentered_skew_entry (omega : ShellSeq d) (x : Vec d) (i k : Fin d) :
    fullStreamRecentered omega x i k = -fullStreamRecentered omega x k i := by
  refine tsum_skew_entry _ (fun n i k => ?_) i k
  have h1 := ShellField.skew_entry (omega n) x i k
  have h2 := ShellField.skew_entry (omega n) 0 i k
  simp only [Matrix.sub_apply, shellReg, ShellField.forgetShell_apply]
  linarith only [h1, h2]

/-- Measurability of the real summability set. -/
theorem measurableSet_summable_real {β : Type*} [MeasurableSpace β] (f : ℕ → β → ℝ)
    (hf : ∀ n, Measurable (f n)) : MeasurableSet {p | Summable fun n => f n p} := by
  have hset : {p | Summable fun n => f n p} =
      {p | ∑' n, ENNReal.ofReal |f n p| ≠ ⊤} := by
    ext p
    simp only [Set.mem_ofPred_eq]
    rw [← summable_abs_iff]
    constructor
    · intro h
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => abs_nonneg _) h]
      exact ENNReal.ofReal_ne_top
    · intro h
      have := ENNReal.summable_toReal h
      refine this.congr fun n => ?_
      simp [ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [hset]
  exact (Measurable.tsum fun n => (continuous_abs.measurable.comp (hf n)).ennreal_ofReal)
    (measurableSet_singleton ⊤).compl

/-- Measurability of a `tsum` of measurable matrix-valued maps (entrywise). -/
theorem measurable_tsum_mat {β : Type*} [MeasurableSpace β] (F : ℕ → β → Mat d)
    (hF : ∀ n, Measurable (F n)) : Measurable fun p => ∑' n, F n p := by
  classical
  have hent : ∀ (n : ℕ) (i k : Fin d), Measurable fun p => F n p i k := fun n i k =>
    (measurable_pi_apply k).comp ((measurable_pi_apply i).comp (hF n))
  have hsumm : ∀ p, Summable (fun n => F n p) ↔ ∀ i k, Summable fun n => F n p i k := by
    intro p
    constructor
    · intro h i k
      exact (Pi.summable.1 (Pi.summable.1 h i) k)
    · intro h
      exact Pi.summable.2 fun i => Pi.summable.2 fun k => h i k
  have hS : MeasurableSet {p | Summable fun n => F n p} := by
    have : {p | Summable fun n => F n p} =
        ⋂ i, ⋂ k, {p | Summable fun n => F n p i k} := by
      ext p; simp [hsumm p]
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k =>
      measurableSet_summable_real (fun n p => F n p i k) (fun n => hent n i k)
  refine measurable_matrix_of_entries fun i k => ?_
  have hfun : (fun p => (∑' n, F n p) i k) =
      fun p => if Summable (fun n => F n p) then ∑' n, F n p i k else 0 := by
    funext p
    by_cases h : Summable fun n => F n p
    · simp only [h, ite_true]
      exact tsum_matrix_apply h i k
    · simp only [h, ite_false]
      rw [tsum_eq_zero_of_not_summable h]
      rfl
  rw [hfun]
  exact Measurable.ite hS (Measurable.tsum fun n => hent n i k) measurable_const

/-- The shell values are jointly measurable in `(x, omega)`. -/
theorem measurable_shellReg_uncurry (n : ℕ) :
    Measurable fun p : Vec d × ShellSeq d => shellReg p.2 n p.1 := by
  refine measurable_matrix_of_entries fun i j => ?_
  have hcont : ∀ omega : ShellSeq d, Continuous fun x : Vec d => shellReg omega n x i j :=
    fun omega => shellReg_entry_continuous omega n i j
  have hmeas : ∀ x : Vec d, Measurable fun omega : ShellSeq d => shellReg omega n x i j :=
    fun x => (measurable_apply_entry x i j).comp (measurable_shellReg n)
  exact measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : Vec d) (omega : ShellSeq d) => shellReg omega n x i j) hcont hmeas

theorem measurable_fullStreamRecentered_uncurry :
    Measurable fun p : Vec d × ShellSeq d => fullStreamRecentered p.2 p.1 := by
  refine measurable_tsum_mat
    (fun n (p : Vec d × ShellSeq d) => shellReg p.2 n p.1 - shellReg p.2 n 0) ?_
  intro n
  refine measurable_matrix_of_entries fun i k => ?_
  have h0 : Measurable fun p : Vec d × ShellSeq d => shellReg p.2 n 0 i k :=
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp
      (measurable_shellReg_uncurry n))).comp
      (measurable_const.prodMk measurable_snd : Measurable fun p : Vec d × ShellSeq d =>
        ((0 : Vec d), p.2))
  exact ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp
    (measurable_shellReg_uncurry n))).sub h0

theorem measurable_fullCoefficientRecentered_uncurry (nu : ℝ) :
    Measurable fun p : Vec d × ShellSeq d => fullCoefficientRecentered nu p.2 p.1 :=
  measurable_matrix_of_entries fun i k => by
    have := (measurable_pi_apply k).comp ((measurable_pi_apply i).comp
      (measurable_fullStreamRecentered_uncurry (d := d)))
    simp only [fullCoefficientRecentered, Matrix.add_apply]
    exact this.const_add _

/-! ## Satisfiability witnesses -/

/-- The zero shell sequence has zero full stream. -/
example (x : Vec d) :
    fullStream (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq d) x = 0 := by
  simp [fullStream, shellReg, SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq,
    ShellField.zero_apply]

example (x : Vec d) :
    fullStreamRecentered (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq d) x = 0 := by
  simp [fullStreamRecentered, shellReg, SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq,
    ShellField.zero_apply]

/-- The a.s. convergence theorem is satisfiable: the Dirac zero law meets `J3`. -/
example :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∀ S : Set (Vec d), Bornology.IsBounded S →
        TendstoUniformlyOn
          (fun (L : ℕ) (x : Vec d) => streamCutoff omega L x - streamCutoff omega L 0)
          (fullStreamRecentered omega) atTop S :=
  ae_tendstoUniformlyOn_streamCutoff_recentered
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw

end

end SuperdiffusionCLT.Section6
