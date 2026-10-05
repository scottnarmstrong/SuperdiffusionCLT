/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Convergence.SemigroupFddB

/-!
# From grid chains to the oscillation of paths

A continuous path with an oscillation larger than `4r` at scale `δ` before time `T`, staying in
`K`, produces for every fine enough grid either a wrong starting point, a step of size at least
`r`, or a short gap between markers of the grid chain (`sgConv_modEvent_eventually`).  Steps of
size `r` between grid times disappear as the mesh tends to zero, by path continuity.  Hence the
path-level oscillation event has mass at most any bound valid for the short-gap probabilities of
all fine enough grids (`sgConv_modEvent_le`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Convergence
open Filter Homogenization MeasureTheory ProbabilityTheory Topology
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section

section Wild

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α]

/-- Paths with a step of size at least `r` between consecutive grid times `0, g, …, Jg`. -/
def sgConv_wild (g : ℝ≥0) (J : ℕ) (r : ℝ) : Set (ContinuousPath α) :=
  {ω | ∃ j < J, r ≤ dist (ω (((j + 1 : ℕ) : ℝ≥0) * g)) (ω ((j : ℝ≥0) * g))}

theorem measurableSet_sgConv_wild (g : ℝ≥0) (J : ℕ) (r : ℝ) :
    MeasurableSet (sgConv_wild (α := α) g J r) := by
  have : sgConv_wild (α := α) g J r = ⋃ j ∈ Finset.range J,
      {ω : ContinuousPath α | r ≤ dist (ω (((j + 1 : ℕ) : ℝ≥0) * g)) (ω ((j : ℝ≥0) * g))} := by
    ext ω; simp [sgConv_wild]
  rw [this]
  refine Finset.measurableSet_biUnion _ fun j _ ↦ ?_
  exact measurableSet_le measurable_const
    ((ContinuousPath.measurable_coordinateProcess (alpha := α) _).dist
      (ContinuousPath.measurable_coordinateProcess (alpha := α) _))

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
/-- A continuous path has no large steps between grid times of fine enough mesh. -/
theorem sgConv_eventually_not_wild (ω : ContinuousPath α) {g : ℕ → ℝ≥0}
    (hgt : Tendsto g atTop (nhds 0)) {J : ℕ → ℕ} {T : ℝ≥0} (hJ : ∀ m, (J m : ℝ≥0) * g m ≤ T)
    {r : ℝ} (hr : 0 < r) : ∀ᶠ m in atTop, ω ∉ sgConv_wild (g m) (J m) r := by
  have huc : UniformContinuousOn ω (Set.Icc (0 : ℝ≥0) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous ω.continuous.continuousOn
  obtain ⟨η, hη, hηω⟩ := Metric.uniformContinuousOn_iff.mp huc r hr
  have hev : ∀ᶠ m in atTop, g m < ⟨η, hη.le⟩ := by
    have := (hgt.eventually (gt_mem_nhds (show (0 : ℝ≥0) < ⟨η, hη.le⟩ from hη)))
    exact this
  filter_upwards [hev] with m hm
  rintro ⟨j, hj, hjd⟩
  have h1 : (((j + 1 : ℕ) : ℝ≥0) * g m) ≤ T := by
    calc ((j + 1 : ℕ) : ℝ≥0) * g m ≤ (J m : ℝ≥0) * g m := by
          gcongr; exact_mod_cast hj
      _ ≤ T := hJ m
  have h2 : ((j : ℝ≥0) * g m) ≤ T := by
    refine le_trans ?_ h1
    gcongr; exact_mod_cast Nat.le_succ j
  have hdist : dist (((j + 1 : ℕ) : ℝ≥0) * g m) ((j : ℝ≥0) * g m) < η := by
    rw [NNReal.dist_eq]
    have : (((j + 1 : ℕ) : ℝ≥0) * g m : ℝ≥0) = (j : ℝ≥0) * g m + g m := by push_cast; ring
    rw [this]
    simp only [NNReal.coe_add, add_sub_cancel_left, abs_of_nonneg NNReal.zero_le_coe]
    exact_mod_cast hm
  have := hηω _ ⟨zero_le, h1⟩ _ ⟨zero_le, h2⟩ hdist
  linarith only [this, hjd]

theorem sgConv_tendsto_measure_wild (Q : Measure (ContinuousPath α)) [IsFiniteMeasure Q]
    {g : ℕ → ℝ≥0} (hgt : Tendsto g atTop (nhds 0)) {J : ℕ → ℕ} {T : ℝ≥0}
    (hJ : ∀ m, (J m : ℝ≥0) * g m ≤ T) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun m ↦ Q (sgConv_wild (g m) (J m) r)) atTop (nhds 0) := by
  set U : ℕ → Set (ContinuousPath α) := fun m ↦ ⋃ m', ⋃ (_ : m ≤ m'), sgConv_wild (g m') (J m') r
    with hU
  have hmeas : ∀ m, MeasurableSet (U m) := fun m ↦
    MeasurableSet.iUnion fun m' ↦ MeasurableSet.iUnion fun _ ↦ measurableSet_sgConv_wild _ _ _
  have hanti : Antitone U := fun m m' hmm' ω hω ↦ by
    simp only [hU, Set.mem_iUnion] at hω ⊢
    obtain ⟨m'', hm'', hω⟩ := hω
    exact ⟨m'', hmm'.trans hm'', hω⟩
  have hempty : (⋂ m, U m) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun ω hω ↦ ?_
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (sgConv_eventually_not_wild ω hgt hJ hr)
    have := Set.mem_iInter.mp hω M
    simp only [hU, Set.mem_iUnion] at this
    obtain ⟨m', hm', hω'⟩ := this
    exact hM m' hm' hω'
  have h1 := tendsto_measure_iInter_atTop (μ := Q) (fun m ↦ (hmeas m).nullMeasurableSet) hanti
    ⟨0, measure_ne_top Q _⟩
  rw [hempty, measure_empty] at h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun m ↦ zero_le) fun m ↦ ?_
  exact measure_mono fun ω hω ↦ Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨le_rfl, hω⟩⟩

/-- Paths with an oscillation larger than `κ` at scale `δ` before time `T`, while staying in `K`. -/
def sgConv_modEvent (K : Set α) (T δ : ℝ≥0) (κ : ℝ) : Set (ContinuousPath α) :=
  {ω | ∃ s t : ℝ≥0, s < t ∧ t ≤ T ∧ t - s ≤ δ ∧ κ < dist (ω s) (ω t) ∧ ∀ u, u ≤ t → ω u ∈ K}

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem sgConv_tendsto_floor_mul {g : ℕ → ℝ≥0} (hg0 : ∀ m, 0 < g m)
    (hgt : Tendsto g atTop (nhds 0)) (s : ℝ≥0) :
    Tendsto (fun m ↦ (⌊s / g m⌋₊ : ℝ≥0) * g m) atTop (nhds s) := by
  have hup : ∀ m, (⌊s / g m⌋₊ : ℝ≥0) * g m ≤ s := fun m ↦ by
    have := Nat.floor_le (zero_le : 0 ≤ s / g m)
    rwa [le_div_iff₀ (hg0 m)] at this
  have hlow : ∀ m, s - g m ≤ (⌊s / g m⌋₊ : ℝ≥0) * g m := fun m ↦ by
    have := Nat.lt_floor_add_one (s / g m)
    rw [div_lt_iff₀ (hg0 m)] at this
    rw [tsub_le_iff_right, ← add_one_mul]
    exact this.le
  have hl : Tendsto (fun m ↦ s - g m) atTop (nhds s) := by
    simpa using (tendsto_const_nhds (x := s)).sub hgt
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlow hup

open Classical in
omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
/-- Every path of the oscillation event lies, for all fine enough grids, in the set where the
start is wrong, or a step is large, or the grid chain has a short gap. -/
theorem sgConv_modEvent_eventually {K : Set α} {r : ℝ} (hr : 0 < r) (T δ : ℝ≥0) {x : α}
    {g : ℕ → ℝ≥0} (hg0 : ∀ m, 0 < g m) (hgt : Tendsto g atTop (nhds 0)) {J δs : ℕ → ℕ}
    (hJ2 : ∀ m, T < ((J m : ℝ≥0) + 1) * g m)
    (hδs : ∀ m, δ + g m ≤ ((δs m : ℝ≥0) + 1) * g m) (ω : ContinuousPath α)
    (hω : ω ∈ sgConv_modEvent K T δ (4 * r)) :
    ∀ᶠ m in atTop, ω 0 ≠ x ∨ ω ∈ sgConv_wild (g m) (J m) r ∨
      sgConv_bad K r (δs m) (J m) 0 x (sgConv_grid (g m) (J m) ω) ≠ 0 := by
  obtain ⟨s, t, hst, htT, hdel, hd, hKu⟩ := hω
  have hs := sgConv_tendsto_floor_mul hg0 hgt s
  have ht := sgConv_tendsto_floor_mul hg0 hgt t
  have hdt : Tendsto (fun m ↦ dist (ω ((⌊s / g m⌋₊ : ℝ≥0) * g m))
      (ω ((⌊t / g m⌋₊ : ℝ≥0) * g m))) atTop (nhds (dist (ω s) (ω t))) :=
    ((ω.continuous.tendsto s).comp hs).dist ((ω.continuous.tendsto t).comp ht)
  filter_upwards [hdt.eventually (lt_mem_nhds hd)] with m hm
  by_contra hcon
  have h0 : ω 0 = x := by by_contra h; exact hcon (Or.inl h)
  have hw : ω ∉ sgConv_wild (g m) (J m) r := fun h ↦ hcon (Or.inr (Or.inl h))
  have hb : sgConv_bad K r (δs m) (J m) 0 x (sgConv_grid (g m) (J m) ω) = 0 := by
    by_contra h; exact hcon (Or.inr (Or.inr h))
  set i := ⌊s / g m⌋₊ with hi
  set j := ⌊t / g m⌋₊ with hj
  have hgm := hg0 m
  have hjT : (j : ℝ≥0) * g m ≤ t := by
    have := Nat.floor_le (zero_le : 0 ≤ t / g m)
    rwa [le_div_iff₀ hgm] at this
  have hsi : s < ((i : ℝ≥0) + 1) * g m := by
    have := Nat.lt_floor_add_one (s / g m)
    rwa [div_lt_iff₀ hgm] at this
  have hjJ : j ≤ J m := by
    have h1 : (j : ℝ≥0) * g m < ((J m : ℝ≥0) + 1) * g m := lt_of_le_of_lt (hjT.trans htT) (hJ2 m)
    have h2 : (j : ℝ≥0) < (J m : ℝ≥0) + 1 := lt_of_mul_lt_mul_right h1 zero_le
    have h3 : j < J m + 1 := by exact_mod_cast h2
    omega
  have hij : i ≤ j := Nat.floor_mono (div_le_div_of_nonneg_right hst.le hgm.le)
  have hne : i ≠ j := by
    intro hij'
    rw [hij'] at hm
    simp only [dist_self] at hm
    linarith only [hm, hr]
  have hilt : i < j := lt_of_le_of_ne hij hne
  have hjd : j - i ≤ δs m := by
    have h3 : t ≤ s + δ := tsub_le_iff_left.mp hdel
    have h4 : (j : ℝ≥0) * g m < ((i + δs m + 1 : ℕ) : ℝ≥0) * g m := by
      calc (j : ℝ≥0) * g m ≤ s + δ := hjT.trans h3
        _ < ((i : ℝ≥0) + 1) * g m + δ := add_lt_add_left hsi δ
        _ = (i : ℝ≥0) * g m + (δ + g m) := by ring
        _ ≤ (i : ℝ≥0) * g m + ((δs m : ℝ≥0) + 1) * g m := add_le_add_right (hδs m) _
        _ = ((i + δs m + 1 : ℕ) : ℝ≥0) * g m := by push_cast; ring
    have h5 : (j : ℝ≥0) < ((i + δs m + 1 : ℕ) : ℝ≥0) := lt_of_mul_lt_mul_right h4 zero_le
    have h6 : j < i + δs m + 1 := by exact_mod_cast h5
    omega
  have hKpt : ∀ l ≤ j, sgConv_pt (ω 0) (sgConv_grid (g m) (J m) ω) l ∈ K := by
    intro l hl
    rw [sgConv_pt_grid (g m) (J m) ω (hl.trans hjJ)]
    refine hKu _ ?_
    exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hl) zero_le) hjT
  have hjump : ∀ l < j, dist (sgConv_pt (ω 0) (sgConv_grid (g m) (J m) ω) (l + 1))
      (sgConv_pt (ω 0) (sgConv_grid (g m) (J m) ω) l) < r := by
    intro l hl
    rw [sgConv_pt_grid (g m) (J m) ω (by omega), sgConv_pt_grid (g m) (J m) ω (by omega)]
    by_contra hge
    exact hw ⟨l, by omega, not_lt.mp hge⟩
  have hya : dist (ω 0) x < r := by rw [h0]; simpa using hr
  obtain ⟨-, -, Qc⟩ := sgConv_comb K hr (δs m) (J m) j 0 x (ω 0) (sgConv_grid (g m) (J m) ω) hjJ
    hya hKpt hjump hb
  have := Qc i j hilt le_rfl hjd
  rw [sgConv_pt_grid (g m) (J m) ω (hij.trans hjJ), sgConv_pt_grid (g m) (J m) ω hjJ] at this
  linarith only [this, hm]

open Classical in
/-- **The oscillation event has small mass if the grid chains have no short gaps with high
probability.** -/
theorem sgConv_modEvent_le (Q : Measure (ContinuousPath α)) [IsFiniteMeasure Q] {x : α}
    (hQ0 : Q {ω | ω 0 ≠ x} = 0) {K : Set α} {r : ℝ} (hr : 0 < r) (T δ : ℝ≥0) {g : ℕ → ℝ≥0}
    (hg0 : ∀ m, 0 < g m) (hgt : Tendsto g atTop (nhds 0)) {J δs : ℕ → ℕ}
    (hJ1 : ∀ m, (J m : ℝ≥0) * g m ≤ T) (hJ2 : ∀ m, T < ((J m : ℝ≥0) + 1) * g m)
    (hδs : ∀ m, δ + g m ≤ ((δs m : ℝ≥0) + 1) * g m) {P : ℝ≥0∞}
    (hP : ∀ᶠ m in atTop,
      Q {ω | sgConv_bad K r (δs m) (J m) 0 x (sgConv_grid (g m) (J m) ω) ≠ 0} ≤ P) :
    Q (sgConv_modEvent K T δ (4 * r)) ≤ P := by
  set C : ℕ → Set (ContinuousPath α) := fun L ↦ ⋂ m, ⋂ (_ : L ≤ m),
    ({ω | ω 0 ≠ x} ∪ sgConv_wild (g m) (J m) r ∪
      {ω | sgConv_bad K r (δs m) (J m) 0 x (sgConv_grid (g m) (J m) ω) ≠ 0}) with hC
  have hsub : sgConv_modEvent K T δ (4 * r) ⊆ ⋃ L, C L := by
    intro ω hω
    obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp (sgConv_modEvent_eventually hr T δ hg0 hgt hJ2
      hδs ω hω (x := x))
    refine Set.mem_iUnion.mpr ⟨L, ?_⟩
    simp only [hC, Set.mem_iInter]
    intro m hm
    rcases hL m hm with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hdir : Directed (· ⊆ ·) C := by
    refine Monotone.directed_le fun L L' hLL' ω hω ↦ ?_
    simp only [hC, Set.mem_iInter] at hω ⊢
    exact fun m hm ↦ hω m (hLL'.trans hm)
  refine (measure_mono hsub).trans ?_
  rw [hdir.measure_iUnion]
  refine iSup_le fun L ↦ ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hw := sgConv_tendsto_measure_wild Q hgt hJ1 hr
  obtain ⟨m, hmL, hmw, hmP⟩ := ((Filter.eventually_ge_atTop L).and
    ((hw.eventually (ge_mem_nhds (show (0 : ℝ≥0∞) < ε by exact_mod_cast hε))).and hP)).exists
  calc Q (C L) ≤ Q ({ω | ω 0 ≠ x} ∪ sgConv_wild (g m) (J m) r ∪
        {ω | sgConv_bad K r (δs m) (J m) 0 x (sgConv_grid (g m) (J m) ω) ≠ 0}) := by
        refine measure_mono fun ω hω ↦ ?_
        simp only [hC, Set.mem_iInter] at hω
        exact hω m hmL
    _ ≤ Q ({ω | ω 0 ≠ x} ∪ sgConv_wild (g m) (J m) r) +
        Q {ω | sgConv_bad K r (δs m) (J m) 0 x (sgConv_grid (g m) (J m) ω) ≠ 0} :=
        measure_union_le _ _
    _ ≤ (Q {ω | ω 0 ≠ x} + Q (sgConv_wild (g m) (J m) r)) +
        Q {ω | sgConv_bad K r (δs m) (J m) 0 x (sgConv_grid (g m) (J m) ω) ≠ 0} :=
        add_le_add_left (measure_union_le _ _) _
    _ ≤ (0 + ε) + P := by rw [hQ0]; exact add_le_add (add_le_add le_rfl hmw) hmP
    _ = P + ε := by rw [zero_add, add_comm]

end Wild
end
end SuperdiffusionCLT.Section8.Convergence
