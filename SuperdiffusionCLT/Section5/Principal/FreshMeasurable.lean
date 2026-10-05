/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.LocalizeSwitch
public import SuperdiffusionCLT.Section5.Response.ResponseData
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityD
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Inputs
public import SuperdiffusionCLT.Probability.ConditionalGammaTailShell

/-!
# Measurability for the fresh-shell `σ`-algebra

`principal_conditional` needs the weight `D` and the coordinates of `P̂` to be measurable for
`F_new = σ(j_r : m - h < r ≤ m)` (`shellSigma (Set.Ioc (m - h) m)`).

* `pmeas_measurable_of_depends`: a map that is measurable for the ambient `σ`-algebra and depends
  only on the shells `r ∈ S` is measurable for `shellSigma S` (it factors through the projection
  onto those shells, followed by the fixed extension by a base sample).
* The shell increment `k_m - k_{m-h}`, the stream flux `hshellFlux`, and the boxwise gauge
  `hbar_z = principalGauge m h Q` read only the shells in `(m - h, m]`, hence are fresh-measurable.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Probability (shellSigma shellSigma_le_ambient)

variable {d : ℕ}

/-! ## The factorization lemma -/

open Classical in
/-- Keep the shells in `S` and replace the others by those of the base sample `ω₀`. -/
noncomputable def pmeas_freeze (S : Set ℕ) (ω₀ ω : ShellSeq d) : ShellSeq d :=
  fun n => if n ∈ S then ω n else ω₀ n

theorem pmeas_measurable_freeze (S : Set ℕ) (ω₀ : ShellSeq d) :
    Measurable[shellSigma (d := d) S, inferInstance] (pmeas_freeze S ω₀) := by
  refine @Measurable.of_eval _ _ _ (shellSigma (d := d) S) _ _ fun n => ?_
  by_cases hn : n ∈ S
  · have h1 : (fun ω : ShellSeq d => pmeas_freeze S ω₀ ω n) = fun ω => ω n := by
      funext ω
      simp only [pmeas_freeze, hn, ite_true]
    rw [h1]
    exact Measurable.of_comap_le
      (le_iSup₂ (f := fun n (_ : n ∈ S) =>
        MeasurableSpace.comap (fun F : ShellSeq d => F n) inferInstance) n hn)
  · have h1 : (fun ω : ShellSeq d => pmeas_freeze S ω₀ ω n) = fun _ => ω₀ n := by
      funext ω
      simp only [pmeas_freeze, hn, ite_false]
    rw [h1]
    exact measurable_const

/-- **Fresh-shell measurability from dependence.** A map that is measurable for the ambient
`σ`-algebra of the shell sequence and depends only on the shells `r ∈ S` is measurable for
`shellSigma S`. -/
theorem pmeas_measurable_of_depends {β : Type*} [MeasurableSpace β] {S : Set ℕ}
    {f : ShellSeq d → β} (hf : Measurable f)
    (hdep : ∀ ω ω' : ShellSeq d, (∀ n ∈ S, ω n = ω' n) → f ω = f ω') :
    Measurable[shellSigma (d := d) S] f := by
  rcases isEmpty_or_nonempty (ShellSeq d) with hE | ⟨⟨ω₀⟩⟩
  · intro t _
    rw [Set.eq_empty_of_isEmpty (f ⁻¹' t)]
    exact @MeasurableSet.empty _ (shellSigma (d := d) S)
  · have hρ := pmeas_measurable_freeze S ω₀
    intro t ht
    have h2 : f ⁻¹' t = pmeas_freeze S ω₀ ⁻¹' (f ⁻¹' t) := by
      ext ω
      show f ω ∈ t ↔ f (pmeas_freeze S ω₀ ω) ∈ t
      rw [hdep ω (pmeas_freeze S ω₀ ω) (fun n hn => by simp only [pmeas_freeze, hn, ite_true])]
    rw [h2]
    exact hρ (hf ht)

/-! ## Dependence of the increment, the flux and the gauge on the fresh shells -/

theorem pmeas_finiteShellIncrement_congr {n m : ℕ} {ω ω' : ShellSeq d}
    (h : ∀ k ∈ Set.Ioc n m, ω k = ω' k) :
    finiteShellIncrement ω n m = finiteShellIncrement ω' n m := by
  unfold finiteShellIncrement
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [shellReg]
  rw [h k (by simpa only [Set.mem_Ioc, Finset.mem_Ioc] using hk)]

theorem pmeas_dirichletRhsField_congr {l L : ℕ} (hlL : l ≤ L) {ω ω' : ShellSeq d}
    (h : ∀ k ∈ Set.Ioc l L, ω k = ω' k) (p : Vec d) :
    SuperdiffusionCLT.Section3.Setup.dirichletRhsField ω L l p =
      SuperdiffusionCLT.Section3.Setup.dirichletRhsField ω' L l p := by
  funext x
  unfold SuperdiffusionCLT.Section3.Setup.dirichletRhsField
  rw [← finiteShellIncrement_apply_eq_streamCutoff_sub ω hlL x,
    ← finiteShellIncrement_apply_eq_streamCutoff_sub ω' hlL x, pmeas_finiteShellIncrement_congr h]

/-- The stream flux `(k_L - k_l) p` at a point reads only the shells in `(l, L]`. -/
theorem pmeas_measurable_dirichletRhsField_fresh {l L : ℕ} (hlL : l ≤ L) (p x : Vec d) :
    Measurable[shellSigma (d := d) (Set.Ioc l L)]
      (fun ω : ShellSeq d =>
        SuperdiffusionCLT.Section3.Setup.dirichletRhsField ω L l p x) :=
  pmeas_measurable_of_depends
    (SuperdiffusionCLT.Section3.Setup.measurable_dirichletRhsField_apply L l p x)
    (fun _ _ h => congrFun (pmeas_dirichletRhsField_congr hlL h p) x)

/-- The flux `hshellFlux` at a point reads only the fresh shells `(m - h, m]`. -/
theorem pmeas_measurable_hshellFlux_fresh [NeZero d] (nu : ℝ)
    (P : ProbabilityMeasure (ShellSeq d)) (m h : ℕ) (e x : Vec d) :
    Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
      (fun ω : ShellSeq d => hshellFlux nu P m h ω e x) := by
  have hfun : (fun ω : ShellSeq d => hshellFlux nu P m h ω e x) = fun ω : ShellSeq d =>
      SuperdiffusionCLT.Section3.Setup.dirichletRhsField ω m (m - h)
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P)⁻¹ • e) x :=
    funext fun ω => congrFun (responseData_hshellFlux_eq_dirichletRhsField nu P m h ω e) x
  rw [hfun]
  exact pmeas_measurable_dirichletRhsField_fresh (Nat.sub_le m h) _ x

/-- The flux `hshellFlux` is continuous in the space variable, for every sample. -/
theorem pmeas_continuous_hshellFlux [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (m h : ℕ) (ω : ShellSeq d) (e : Vec d) : Continuous (hshellFlux nu P m h ω e) := by
  rw [responseData_hshellFlux_eq_dirichletRhsField]
  exact SuperdiffusionCLT.Section3.Setup.continuous_dirichletRhsField _ _ _ _

/-- **`principalGauge` is fresh-measurable**: the boxwise gauge reads only the shells
`(m - h, m]`. -/
theorem pmeas_measurable_principalGauge_fresh (m h : ℕ) (Q : TriadicCube d) :
    Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
      (fun ω : ShellSeq d => principalGauge m h Q ω) :=
  pmeas_measurable_of_depends
    (SuperdiffusionCLT.Section3.Terms.measurable_volumeAverageMat_finiteShellIncrement
      (m - h) m Q)
    (fun ω ω' hh => by
      show volumeAverageMat (cubeSet Q) (fun y => finiteShellIncrement ω (m - h) m y) =
        volumeAverageMat (cubeSet Q) (fun y => finiteShellIncrement ω' (m - h) m y)
      rw [pmeas_finiteShellIncrement_congr hh])

/-- Entries of `principalGauge` are fresh-measurable. -/
theorem pmeas_measurable_principalGauge_entry_fresh (m h : ℕ) (Q : TriadicCube d)
    (i j : Fin d) :
    Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
      (fun ω : ShellSeq d => principalGauge m h Q ω i j) :=
  ((measurable_pi_apply j).comp
    ((measurable_pi_apply i).comp (pmeas_measurable_principalGauge_fresh m h Q)))

/-! ## Satisfiability -/

/-- Witness: the factorization lemma applies to a function that is not constant, depending on the
shell `r = 3` only (`d = 2`, `S = {3}`). -/
example : Measurable[shellSigma (d := 2) ({3} : Set ℕ)]
    (fun ω : ShellSeq 2 => finiteShellIncrement ω 2 3) :=
  pmeas_measurable_of_depends (measurable_finiteShellIncrement 2 3)
    (fun ω ω' h => pmeas_finiteShellIncrement_congr (fun k hk => h k (by
      have : k = 3 := by
        rcases hk with ⟨h1, h2⟩
        omega
      simp [this])))

/-- Witness for the gauge and flux lemmas: `d = 2`, `m = 5`, `h = 2`, the unit cube. -/
example : Measurable[shellSigma (d := 2) (Set.Ioc (5 - 2) 5)]
    (fun ω : ShellSeq 2 => principalGauge 5 2 (originCube 2 (0 : ℤ)) ω 0 1) :=
  pmeas_measurable_principalGauge_entry_fresh 5 2 _ 0 1

end SuperdiffusionCLT.Section5
