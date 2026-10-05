/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import SuperdiffusionCLT.Section8.Convergence.SemigroupTightnessE

/-!
# Compact containment of the path laws of convergent Feller semigroups

For strongly convergent conservative Feller semigroups and convergent starting points, the path
laws give uniformly small mass to the paths that leave a large ball before time `T`.  The proof
combines the weak convergence of the finite-dimensional distributions on a grid (portmanteau for
a closed set), the oscillation bound `sgConv_modEvent_le_semigroup` and the deterministic
`sgConv_exit_mem_modEvent`: a path that leaves the ball of radius `R + 1` while staying within `R`
on the grid has a large oscillation at the grid scale.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Convergence
open Filter Homogenization MeasureTheory ProbabilityTheory Topology
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty BoundedContinuousFunction

noncomputable section

section Exit

variable {α : Type*} [MetricSpace α] [ProperSpace α]

omit [ProperSpace α] in
/-- If a continuous path starts in the ball of radius `R`, stays within `R` at the grid times
`0, δ, …, Jδ` covering `[0, T]`, and nevertheless leaves the ball of radius `R + 1` before time
`T`, then it has an oscillation larger than `4/5` at scale `δ` while staying in the ball of
radius `R + 1`. -/
theorem sgConv_exit_mem_modEvent (ω : ContinuousPath α) (x₀ : α) (R : ℝ) (T δ : ℝ≥0)
    (hδ : 0 < δ) (J : ℕ) (hTJ : T < ((J : ℝ≥0) + 1) * δ)
    (hgrid : ∀ j ≤ J, dist (ω ((j : ℝ≥0) * δ)) x₀ ≤ R)
    (hexit : ∃ t, t ≤ T ∧ R + 1 < dist (ω t) x₀) :
    ω ∈ sgConv_modEvent (Metric.closedBall x₀ (R + 1)) T δ (4 / 5) := by
  obtain ⟨t₁, ht₁T, ht₁⟩ := hexit
  set f : ℝ≥0 → ℝ := fun u ↦ dist (ω u) x₀ with hf
  have hfc : Continuous f := (ω.continuous).dist continuous_const
  set U : Set ℝ≥0 := {u | u ≤ T ∧ R + 1 ≤ f u} with hU
  have hUclosed : IsClosed U :=
    (isClosed_Iic).inter (isClosed_le continuous_const hfc)
  have hUsub : U ⊆ Set.Icc 0 T := fun u hu ↦ ⟨zero_le, hu.1⟩
  have hUcpt : IsCompact U := isCompact_Icc.of_isClosed_subset hUclosed hUsub
  have hUne : U.Nonempty := ⟨t₁, ht₁T, ht₁.le⟩
  set t := sInf U with ht
  have htU : t ∈ U := hUcpt.sInf_mem hUne
  have hbefore : ∀ u, u < t → f u < R + 1 := by
    intro u hu
    by_contra hcon
    have huU : u ∈ U := ⟨hu.le.trans htU.1, not_lt.mp hcon⟩
    exact absurd (csInf_le (OrderBot.bddBelow U) huU) (not_le.mpr hu)
  have hg0 : f 0 ≤ R := by have := hgrid 0 (Nat.zero_le J); simpa [hf] using this
  have htpos : 0 < t := by
    rcases eq_zero_or_pos t with h | h
    · exfalso
      have := htU.2
      rw [h] at this
      linarith only [this, hg0]
    · exact h
  have hfle : f t ≤ R + 1 := by
    by_contra hcon
    have hgt : R + 1 < f t := not_le.mp hcon
    have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
    have hev : ∀ᶠ u in 𝓝[<] t, R + 1 < f u :=
      eventually_nhdsWithin_of_eventually_nhds
        ((hfc.continuousAt (x := t)).eventually (lt_mem_nhds hgt))
    obtain ⟨u, hu1, hu2⟩ := (hev.and self_mem_nhdsWithin).exists
    have := hbefore u hu2
    linarith only [this, hu1]
  -- the grid cell containing `t`
  set j : ℕ := ⌊t / δ⌋₊ with hj
  have hjt : (j : ℝ≥0) * δ ≤ t := by
    have := Nat.floor_le (zero_le : 0 ≤ t / δ)
    rwa [le_div_iff₀ hδ] at this
  have htj : t < ((j : ℝ≥0) + 1) * δ := by
    have := Nat.lt_floor_add_one (t / δ)
    rwa [div_lt_iff₀ hδ] at this
  have hjJ : j ≤ J := by
    have h1 : (j : ℝ≥0) * δ < ((J : ℝ≥0) + 1) * δ := lt_of_le_of_lt (hjt.trans htU.1) hTJ
    have h2 : (j : ℝ≥0) < (J : ℝ≥0) + 1 := lt_of_mul_lt_mul_right h1 zero_le
    have h3 : j < J + 1 := by exact_mod_cast h2
    omega
  have hfs : f ((j : ℝ≥0) * δ) ≤ R := hgrid j hjJ
  have hst : (j : ℝ≥0) * δ < t := by
    refine lt_of_le_of_ne hjt fun h ↦ ?_
    rw [h] at hfs
    linarith only [hfs, htU.2]
  refine ⟨(j : ℝ≥0) * δ, t, hst, htU.1, ?_, ?_, ?_⟩
  · rw [tsub_le_iff_left]
    exact htj.le.trans_eq (by ring)
  · have h1 := dist_triangle (ω t) (ω ((j : ℝ≥0) * δ)) x₀
    have h2 : f t ≤ dist (ω t) (ω ((j : ℝ≥0) * δ)) + f ((j : ℝ≥0) * δ) := h1
    have h3 := htU.2
    rw [dist_comm] at h2
    linarith only [h2, h3, hfs]
  · intro u hu
    rcases lt_or_eq_of_le hu with h | h
    · exact Metric.mem_closedBall.mpr (hbefore u h).le
    · rw [h]; exact Metric.mem_closedBall.mpr hfle

end Exit

section Containment

variable {α : Type*} [MetricSpace α] [ProperSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α]

/-- Paths that leave the ball of radius `R` before time `T`. -/
def sgConv_exitSet (x₀ : α) (T : ℝ≥0) (R : ℝ) : Set (ContinuousPath α) :=
  {ω | ∃ t, t ≤ T ∧ R < dist (ω t) x₀}

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
omit [ProperSpace α] in
theorem isOpen_sgConv_exitSet (x₀ : α) (T : ℝ≥0) (R : ℝ) :
    IsOpen (sgConv_exitSet (α := α) x₀ T R) := by
  have : sgConv_exitSet (α := α) x₀ T R =
      ⋃ t : ℝ≥0, ⋃ (_ : t ≤ T), {ω : ContinuousPath α | R < dist (ω t) x₀} := by
    ext ω; simp [sgConv_exitSet]
  rw [this]
  refine isOpen_iUnion fun t ↦ isOpen_iUnion fun _ ↦ ?_
  exact isOpen_lt continuous_const ((ContinuousPath.continuous_eval (alpha := α) t).dist
    continuous_const)

omit [SecondCountableTopology α] in
omit [ProperSpace α] [MeasurableSpace α] [BorelSpace α] in
theorem sgConv_exitSet_antitone (x₀ : α) (T : ℝ≥0) : Antitone (sgConv_exitSet (α := α) x₀ T) :=
  fun _ _ hRR' _ hω ↦ by
    obtain ⟨t, ht, h⟩ := hω
    exact ⟨t, ht, lt_of_le_of_lt hRR' h⟩

omit [ProperSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
/-- A path law gives small mass to the paths leaving large balls before time `T`. -/
theorem sgConv_exists_exitSet_le (Q : Measure (ContinuousPath α)) [IsFiniteMeasure Q] (x₀ : α)
    (T : ℝ≥0) {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ R : ℕ, Q (sgConv_exitSet x₀ T R) ≤ ε := by
  have hmeas : ∀ R : ℕ, MeasurableSet (sgConv_exitSet (α := α) x₀ T R) := fun R ↦
    (isOpen_sgConv_exitSet x₀ T R).measurableSet
  have hanti : Antitone (fun R : ℕ ↦ sgConv_exitSet (α := α) x₀ T R) :=
    fun R R' h ↦ sgConv_exitSet_antitone x₀ T (by exact_mod_cast h)
  have h1 := tendsto_measure_iInter_atTop (μ := Q) (fun R ↦ (hmeas R).nullMeasurableSet) hanti
    ⟨0, measure_ne_top Q _⟩
  have hempty : (⋂ R : ℕ, sgConv_exitSet (α := α) x₀ T R) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun ω hω ↦ ?_
    obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).image_of_continuousOn
      (f := fun t ↦ dist (ω t) x₀)
      (ω.continuous.dist continuous_const).continuousOn).bddAbove
    obtain ⟨R, hR⟩ := exists_nat_ge C
    obtain ⟨t, ht, hlt⟩ := Set.mem_iInter.mp hω R
    have := hC ⟨t, ⟨zero_le, ht⟩, rfl⟩
    linarith only [this, hR, hlt]
  rw [hempty, measure_empty] at h1
  obtain ⟨R, hR⟩ := (h1.eventually (ge_mem_nhds hε)).exists
  exact ⟨R, hR⟩

/-- **Compact containment.**  Along strongly convergent conservative Feller semigroups with
convergent starting points, the path laws give uniformly small mass to the paths that leave a
large ball before time `T`. -/
theorem sgConv_compact_containment
    {S : ℕ → SubMarkovKernelSemigroup α} {T₀ : SubMarkovKernelSemigroup α}
    (hS : ∀ n, (S n).IsFellerKernelSemigroup) (hSc : ∀ n, (S n).IsConservative)
    (hT : T₀.IsFellerKernelSemigroup) (hTc : T₀.IsConservative)
    (hconv : ∀ (t : ℝ≥0) (f : C₀(α, ℝ)),
      Tendsto (fun n ↦ (hS n).c0Semigroup t f) atTop (nhds (hT.c0Semigroup t f)))
    {x : ℕ → α} {x₀ : α} (hx : Tendsto x atTop (nhds x₀))
    {Q : ℕ → Measure (ContinuousPath α)} {Q₀ : Measure (ContinuousPath α)}
    [∀ n, IsProbabilityMeasure (Q n)] [IsProbabilityMeasure Q₀]
    (hfdd : ∀ n (I : Finset ℝ≥0), (Q n).map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel (S n) I (x n))
    (hfdd₀ : ∀ I : Finset ℝ≥0, Q₀.map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel T₀ I x₀)
    (T : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, ∃ n₁ : ℕ, ∀ n ≥ n₁, Q n (sgConv_exitSet x₀ T R) ≤ ENNReal.ofReal η := by
  obtain ⟨R0, hR0⟩ := (hx.isCompact_insert_range.isBounded).subset_closedBall x₀
  have hx0 : ∀ n, dist (x n) x₀ ≤ R0 := fun n ↦
    Metric.mem_closedBall.mp (hR0 (Set.mem_insert_of_mem _ (Set.mem_range_self n)))
  have hη4 : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 4) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨R1, hR1⟩ := sgConv_exists_exitSet_le Q₀ x₀ T hη4
  obtain ⟨N0, hN0⟩ := exists_nat_ge R0
  set R1' : ℕ := max R1 N0 with hR1'
  have hR1'le : Q₀ (sgConv_exitSet x₀ T R1') ≤ ENNReal.ofReal (η / 4) :=
    (measure_mono (sgConv_exitSet_antitone x₀ T (by exact_mod_cast le_max_left R1 N0))).trans hR1
  have hR1'R0 : R0 ≤ R1' := hN0.trans (by exact_mod_cast le_max_right R1 N0)
  set R' : ℝ := R1' + 1 with hR'
  set K' : Set α := Metric.closedBall x₀ (R' + 1) with hK'
  have hK'cpt : IsCompact K' := isCompact_closedBall x₀ _
  have hxK' : ∀ n, x n ∈ K' := fun n ↦ Metric.mem_closedBall.mpr (by
    have := hx0 n; rw [hR']; linarith only [this, hR1'R0])
  obtain ⟨δ, hδ, n₀, hn₀⟩ := sgConv_modEvent_le_semigroup hS hSc hT
    hconv (Q := Q) hfdd hK'cpt hxK' (r := 1 / 5) (by norm_num) T (η := η / 2) (by positivity)
  set J : ℕ := ⌊T / δ⌋₊ with hJ
  have hTJ : T < ((J : ℝ≥0) + 1) * δ := sgConv_lt_floor_succ_mul T δ hδ
  set I : Finset ℝ≥0 := (Finset.range (J + 1)).image (fun j : ℕ ↦ (j : ℝ≥0) * δ) with hI
  set C : Set (I → α) := ⋃ i : I, {w | R' ≤ dist (w i) x₀} with hC
  have hCclosed : IsClosed C :=
    isClosed_iUnion_of_finite fun i ↦ isClosed_le continuous_const
      ((continuous_apply i).dist continuous_const)
  have hevalm := ContinuousPath.measurable_finsetEvaluation (alpha := α) I
  have hmuprob : ∀ n, IsProbabilityMeasure ((Q n).map (ContinuousPath.finsetEvaluation I)) :=
    fun n ↦ (Measure.isProbabilityMeasure_map_iff hevalm.aemeasurable).mpr inferInstance
  have hmu0prob : IsProbabilityMeasure (Q₀.map (ContinuousPath.finsetEvaluation I)) :=
    (Measure.isProbabilityMeasure_map_iff hevalm.aemeasurable).mpr inferInstance
  let μs : ℕ → ProbabilityMeasure (I → α) := fun n ↦
    ⟨(Q n).map (ContinuousPath.finsetEvaluation I), hmuprob n⟩
  let μ0 : ProbabilityMeasure (I → α) := ⟨Q₀.map (ContinuousPath.finsetEvaluation I), hmu0prob⟩
  have hlim : Tendsto μs atTop (nhds μ0) := by
    refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr fun f ↦ ?_
    have h := sgConv_tendsto_integral_finsetEvaluation hS hSc hT hTc hconv hx
      (Q := Q) (Q₀ := Q₀) hfdd hfdd₀ I f
    have e : ∀ μ : Measure (ContinuousPath α), ∫ ω, f ω ∂(μ.map (ContinuousPath.finsetEvaluation I))
        = ∫ ω, f (ContinuousPath.finsetEvaluation I ω) ∂μ := fun μ ↦
      integral_map hevalm.aemeasurable f.continuous.aestronglyMeasurable
    show Tendsto (fun i ↦ ∫ ω, f ω ∂((Q i).map (ContinuousPath.finsetEvaluation I))) atTop
      (nhds (∫ ω, f ω ∂(Q₀.map (ContinuousPath.finsetEvaluation I))))
    simp only [e]
    exact h
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hCclosed
  have hCQ₀ : Q₀.map (ContinuousPath.finsetEvaluation I) C ≤ ENNReal.ofReal (η / 4) := by
    rw [Measure.map_apply hevalm hCclosed.measurableSet]
    refine le_trans (measure_mono fun ω hω ↦ ?_) hR1'le
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hω
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp i.2
    refine ⟨i, ?_, ?_⟩
    · rw [← hji]
      have hjle : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hjle' : (j : ℝ≥0) ≤ J := by exact_mod_cast hjle
      exact le_trans (mul_le_mul_of_nonneg_right hjle' zero_le) (sgConv_floor_mul_le T δ hδ)
    · have h' : R' ≤ dist (ω i) x₀ := hi
      linarith only [h', hR']
  have hev : ∀ᶠ n in atTop, Q n (ContinuousPath.finsetEvaluation I ⁻¹' C) <
      ENNReal.ofReal (η / 2) := by
    have h1 : (atTop : Filter ℕ).limsup (fun n ↦ (Q n).map (ContinuousPath.finsetEvaluation I) C) <
        ENNReal.ofReal (η / 2) :=
      lt_of_le_of_lt (hport.trans hCQ₀) ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        (by linarith only [hη]))
    refine (eventually_lt_of_limsup_lt h1).mono fun n hn ↦ ?_
    rwa [Measure.map_apply hevalm hCclosed.measurableSet] at hn
  obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.mp hev
  refine ⟨R' + 1, max n₀ n₂, fun n hn ↦ ?_⟩
  have hn0 : n₀ ≤ n := (le_max_left _ _).trans hn
  have hn2 : n₂ ≤ n := (le_max_right _ _).trans hn
  have hsub : sgConv_exitSet x₀ T (R' + 1) ⊆
      ContinuousPath.finsetEvaluation I ⁻¹' C ∪ sgConv_modEvent K' T δ (4 * (1 / 5)) := by
    intro ω hω
    by_cases hg : ω ∈ ContinuousPath.finsetEvaluation I ⁻¹' C
    · exact Or.inl hg
    · refine Or.inr ?_
      have hgrid : ∀ j ≤ J, dist (ω ((j : ℝ≥0) * δ)) x₀ ≤ R' := by
        intro j hj
        by_contra hcon
        refine hg (Set.mem_iUnion.mpr ⟨⟨(j : ℝ≥0) * δ, Finset.mem_image.mpr
          ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), rfl⟩⟩, ?_⟩)
        exact (not_le.mp hcon).le
      have := sgConv_exit_mem_modEvent ω x₀ R' T δ hδ J hTJ hgrid hω
      rwa [show (4 : ℝ) * (1 / 5) = 4 / 5 by norm_num]
  calc Q n (sgConv_exitSet x₀ T (R' + 1))
      ≤ Q n (ContinuousPath.finsetEvaluation I ⁻¹' C ∪ sgConv_modEvent K' T δ (4 * (1 / 5))) :=
        measure_mono hsub
    _ ≤ Q n (ContinuousPath.finsetEvaluation I ⁻¹' C) + Q n (sgConv_modEvent K' T δ (4 * (1 / 5))) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add (hn₂ n hn2).le (hn₀ n hn0)
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end Containment

section Modulus

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]

omit [MeasurableSpace α] [BorelSpace α] in
theorem sgConv_modulusSet_anti (T : ℝ≥0) {δ δ' r : ℝ≥0∞} (h : δ' ≤ δ) :
    ContinuousPath.modulusSet (alpha := α) T δ r ⊆ ContinuousPath.modulusSet T δ' r :=
  fun _ hω s t hs ht hd ↦ hω s t hs ht (hd.trans h)

omit [MeasurableSpace α] [BorelSpace α] in
/-- Every finite measure on continuous paths gives small mass to the paths whose oscillation at
a small enough scale is large. -/
theorem sgConv_exists_modulus_le (Q : Measure (ContinuousPath α)) [IsFiniteMeasure Q] (T : ℝ≥0)
    {r : ℝ≥0∞} (hr : 0 < r) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ Q (ContinuousPath.modulusSet T δ r)ᶜ ≤ ε := by
  set B : ℕ → Set (ContinuousPath α) := fun k ↦
    (ContinuousPath.modulusSet T (((k : ℝ≥0∞) + 1)⁻¹) r)ᶜ with hB
  have hmeas : ∀ k, MeasurableSet (B k) := fun k ↦
    (ContinuousPath.measurableSet_modulusSet T _ r).compl
  have hanti : Antitone B := fun k k' hkk' ω hω hmem ↦ hω (sgConv_modulusSet_anti T
    (ENNReal.inv_le_inv.mpr (add_le_add_left (by exact_mod_cast hkk') 1)) hmem)
  have h1 := tendsto_measure_iInter_atTop (μ := Q) (fun k ↦ (hmeas k).nullMeasurableSet) hanti
    ⟨0, measure_ne_top Q _⟩
  have hempty : (⋂ k, B k) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun ω hω ↦ ?_
    have huc : UniformContinuousOn ω (Set.Icc (0 : ℝ≥0) T) :=
      isCompact_Icc.uniformContinuousOn_of_continuous ω.continuous.continuousOn
    obtain ⟨δ, hδ, hδω⟩ := EMetric.uniformContinuousOn_iff.mp huc r hr
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hδ.ne'
    have hmem : ω ∈ ContinuousPath.modulusSet T (((k : ℝ≥0∞) + 1)⁻¹) r := by
      intro s t hs ht hd
      refine (hδω ⟨zero_le, hs⟩ ⟨zero_le, ht⟩ ?_).le
      refine lt_of_le_of_lt hd (lt_of_le_of_lt ?_ hk)
      exact ENNReal.inv_le_inv.mpr (by simp)
    exact (Set.mem_iInter.mp hω k) hmem
  rw [hempty, measure_empty] at h1
  obtain ⟨k, hk⟩ := (h1.eventually (ge_mem_nhds hε)).exists
  exact ⟨((k : ℝ≥0∞) + 1)⁻¹, by simp, hk⟩

omit [MeasurableSpace α] [BorelSpace α] in
/-- Reduction of the modulus of continuity to the exit set and the oscillation event. -/
theorem sgConv_modulus_compl_subset (x₀ : α) (R : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (T δ₀ : ℝ≥0) :
    (ContinuousPath.modulusSet (alpha := α) T (δ₀ : ℝ≥0∞) (ENNReal.ofReal κ))ᶜ ⊆
      sgConv_exitSet x₀ T R ∪ sgConv_modEvent (Metric.closedBall x₀ R) T δ₀ κ := by
  intro ω hω
  by_contra hcon
  apply hω
  have hno1 : ω ∉ sgConv_exitSet x₀ T R := fun h ↦ hcon (Or.inl h)
  have hno2 : ω ∉ sgConv_modEvent (Metric.closedBall x₀ R) T δ₀ κ := fun h ↦ hcon (Or.inr h)
  have hin : ∀ u : ℝ≥0, u ≤ T → ω u ∈ Metric.closedBall x₀ R := fun u hu ↦ by
    by_contra h
    exact hno1 ⟨u, hu, not_le.mp (fun h' ↦ h (Metric.mem_closedBall.mpr h'))⟩
  have key : ∀ s t : ℝ≥0, s < t → t ≤ T → t - s ≤ δ₀ → dist (ω s) (ω t) ≤ κ := by
    intro s t hst htT hd
    by_contra hgt
    exact hno2 ⟨s, t, hst, htT, hd, not_le.mp hgt, fun u hu ↦ hin u (hu.trans htT)⟩
  intro s t hs ht hd
  rw [edist_le_ofReal hκ]
  have hnd : nndist s t ≤ δ₀ := edist_le_coe.mp hd
  rw [NNReal.nndist_eq] at hnd
  rcases lt_trichotomy s t with h | h | h
  · exact key s t h ht (le_trans (le_max_right _ _) hnd)
  · rw [h, dist_self]; exact hκ
  · rw [dist_comm]
    exact key t s h hs (le_trans (le_max_left _ _) hnd)

omit [MeasurableSpace α] [BorelSpace α] in
theorem sgConv_modulus_compl_anti (T : ℝ≥0) {δ δ' r : ℝ≥0∞} (h : δ' ≤ δ) :
    (ContinuousPath.modulusSet (alpha := α) T δ' r)ᶜ ⊆ (ContinuousPath.modulusSet T δ r)ᶜ :=
  fun _ hω hmem ↦ hω (sgConv_modulusSet_anti T h hmem)

omit [MeasurableSpace α] [BorelSpace α] in
/-- One scale serves finitely many finite measures. -/
theorem sgConv_exists_modulus_le_finite (Q : ℕ → Measure (ContinuousPath α))
    [∀ n, IsFiniteMeasure (Q n)] (T : ℝ≥0) {r : ℝ≥0∞} (hr : 0 < r) {ε : ℝ≥0∞} (hε : 0 < ε)
    (N : ℕ) : ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ n < N, Q n (ContinuousPath.modulusSet T δ r)ᶜ ≤ ε := by
  induction N with
  | zero => exact ⟨1, one_pos, fun n hn ↦ absurd hn (Nat.not_lt_zero n)⟩
  | succ N ih =>
    obtain ⟨δ, hδ, h⟩ := ih
    obtain ⟨δ', hδ', h'⟩ := sgConv_exists_modulus_le (Q N) T hr hε
    refine ⟨min δ δ', lt_min hδ hδ', fun n hn ↦ ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
    · exact (measure_mono (sgConv_modulus_compl_anti T (min_le_left _ _))).trans (h n hlt)
    · subst heq
      exact (measure_mono (sgConv_modulus_compl_anti T (min_le_right _ _))).trans h'

end Modulus

end
end SuperdiffusionCLT.Section8.Convergence
