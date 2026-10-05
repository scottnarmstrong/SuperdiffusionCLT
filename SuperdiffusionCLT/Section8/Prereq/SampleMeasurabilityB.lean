/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.SampleMeasurability
public import SuperdiffusionCLT.Section8.Common.Regularity.Freezing.BoundaryFreezingRadius
public import SuperdiffusionCLT.Section8.DivergenceForm.Decay.LocalizedSkewAlgebra
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Measurability in the sample of the weak solution functional

For a jointly measurable family `K ω` of continuous skew fields on a bounded measurable set `U`,
the ball-average functional `θ(ν I + K ω)` of the shifted weak solution is almost everywhere
measurable in `ω`.  The proof approximates `K ω` by piecewise constant fields on dyadic grids; the
functional of such a field is a continuous function (product topology) of the countably many grid
values, which are measurable in `ω`, and the Lipschitz estimate of `SampleMeasurability.lean`
passes to the limit.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section8.DivergenceForm.ZeroTraceSobolev
open scoped RealInnerProductSpace

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- The ball-average functional of the value component of the weak solution for the coefficient
`c`, set to zero when `c` is not elliptic with lower constant `ν` on `U`. -/
def sampleMeas_theta (α ν : ℝ) (hα : 0 < α) (hν : 0 < ν) (f ψ : ScalarL2 U)
    (c : CoeffField d) : ℝ := by
  classical
  exact if h : ∃ Lam, IsEllipticFieldOn ν Lam U c then
    inner ℝ ψ (toL2 (alphaShiftedSolution c hα hν h.choose_spec f)) else 0

theorem sampleMeas_theta_eq {α ν Lam : ℝ} (hα : 0 < α) (hν : 0 < ν) (f ψ : ScalarL2 U)
    {c : CoeffField d} (hE : IsEllipticFieldOn ν Lam U c) :
    sampleMeas_theta α ν hα hν f ψ c = inner ℝ ψ (toL2 (alphaShiftedSolution c hα hν hE f)) := by
  have h : ∃ Lam, IsEllipticFieldOn ν Lam U c := ⟨Lam, hE⟩
  unfold sampleMeas_theta
  simp only [h, ↓reduceDIte]
  have := (isAlphaShiftedWeakSolution_iff_eq c hα hν hE f
    (alphaShiftedSolution c hα hν h.choose_spec f)).1
    (alphaShiftedSolution_isAlphaShiftedWeakSolution c hα hν h.choose_spec f)
  rw [this]

theorem sampleMeas_theta_lipschitz {α ν Lam Lam' δ : ℝ} (hα : 0 < α) (hν : 0 < ν)
    (f ψ : ScalarL2 U) {a b : CoeffField d} (hEa : IsEllipticFieldOn ν Lam U a)
    (hEb : IsEllipticFieldOn ν Lam' U b) (hδ : 0 ≤ δ)
    (hab : ∀ y ∈ U, ∀ i j, |a y i j - b y i j| ≤ δ) :
    |sampleMeas_theta α ν hα hν f ψ a - sampleMeas_theta α ν hα hν f ψ b| ≤
      ‖ψ‖ * ((d : ℝ) * δ * ‖f‖ / (min α ν) ^ 2) := by
  rw [sampleMeas_theta_eq hα hν f ψ hEa, sampleMeas_theta_eq hα hν f ψ hEb, ← inner_sub_right]
  refine (abs_real_inner_le_norm _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (sampleMeas_solution_lipschitz hα hν hEa hEb hδ hab f)
    (norm_nonneg _)

/-- A measurable skew field with bounded entries on a measurable set gives an elliptic
coefficient `ν I + k` with lower constant `ν`. -/
theorem sampleMeas_isElliptic_of_skew {ν B : ℝ} (hν : 0 < ν) (hB : 0 ≤ B) (hU : MeasurableSet U)
    {k : Vec d → Mat d} (hkm : Measurable k) (hskew : ∀ y ∈ U, matTranspose (k y) = -k y)
    (hbd : ∀ y ∈ U, ∀ i j, |k y i j| ≤ B) :
    IsEllipticFieldOn ν ((ν ^ 2 + ((d : ℝ) * B) ^ 2) / ν) U (fun y => ν • (1 : Mat d) + k y) := by
  classical
  refine ⟨?_, fun y hy => ?_⟩
  · have hent : ∀ i j : Fin d, Measurable fun y : Vec d => (ν • (1 : Mat d) + k y) i j :=
      fun i j => by
        simp only [Matrix.add_apply]
        exact measurable_const.add ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hkm))
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    exact Measurable.ite hU (hent i j) measurable_const
  · refine SuperdiffusionCLT.Section8.Common.Regularity.Freezing.isEllipticMatrix_of_symmPart_eq_of_opNorm_le
      hν (DivergenceForm.Decay.symmPart_scalar_add_skew rfl (hskew y hy)) ?_
    have : ν • (1 : Mat d) + k y - ν • (1 : Mat d) = k y := by abel
    rw [this]
    exact sampleMeas_opNorm_applyMat_le hB (hbd y hy)

/-! ## Dyadic rounding and the grid parametrization -/

/-- The dyadic cell index of a point. -/
def sampleMeas_J (n : ℕ) (y : Vec d) : Fin d → ℤ := fun i => ⌊(2 : ℝ) ^ n * y i⌋

/-- The corner of a dyadic cell. -/
def sampleMeas_corner (n : ℕ) (j : Fin d → ℤ) : Vec d := fun i => (j i : ℝ) / (2 : ℝ) ^ n

theorem sampleMeas_measurable_J (n : ℕ) : Measurable (sampleMeas_J (d := d) n) := by
  refine measurable_pi_iff.2 fun i => ?_
  exact Measurable.floor (measurable_const.mul (measurable_pi_apply i))

theorem sampleMeas_dist_corner_J_le (n : ℕ) (y : Vec d) :
    dist (sampleMeas_corner n (sampleMeas_J n y)) y ≤ 1 / (2 : ℝ) ^ n := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  have h1 := Int.floor_le ((2 : ℝ) ^ n * y i)
  have h3 := Int.lt_floor_add_one ((2 : ℝ) ^ n * y i)
  have hq : (⌊(2 : ℝ) ^ n * y i⌋ : ℝ) / (2 : ℝ) ^ n - y i =
      ((⌊(2 : ℝ) ^ n * y i⌋ : ℝ) - (2 : ℝ) ^ n * y i) / (2 : ℝ) ^ n := by
    field_simp
  show |(⌊(2 : ℝ) ^ n * y i⌋ : ℝ) / (2 : ℝ) ^ n - y i| ≤ _
  rw [hq, abs_div, abs_of_pos h2]
  refine div_le_div_of_nonneg_right ?_ h2.le
  rw [abs_le]
  constructor <;> linarith only [h1, h3]

theorem sampleMeas_finite_J {R : ℝ} (hU : U ⊆ Metric.closedBall (0 : Vec d) R) (n : ℕ) :
    (sampleMeas_J n '' U).Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin d => Set.Icc (-⌈(2 : ℝ) ^ n * R⌉) ⌈(2 : ℝ) ^ n * R⌉)
    fun _ => Set.finite_Icc _ _).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  have hyR := mem_closedBall_zero_iff.1 (hU hy)
  have hcoord : ∀ i, |y i| ≤ R := fun i => by
    have := norm_le_pi_norm y i
    rw [Real.norm_eq_abs] at this
    exact this.trans hyR
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  intro i _
  constructor
  · show -⌈(2 : ℝ) ^ n * R⌉ ≤ ⌊(2 : ℝ) ^ n * y i⌋
    rw [Int.le_floor]
    have := (abs_le.1 (hcoord i)).1
    have h3 : -(2 : ℝ) ^ n * R ≤ (2 : ℝ) ^ n * y i := by nlinarith only [this, h2]
    have h4 := Int.le_ceil ((2 : ℝ) ^ n * R)
    push_cast
    linarith only [h3, h4]
  · show ⌊(2 : ℝ) ^ n * y i⌋ ≤ ⌈(2 : ℝ) ^ n * R⌉
    refine (Int.floor_le_ceil _).trans (Int.ceil_mono ?_)
    have := (abs_le.1 (hcoord i)).2
    nlinarith only [this, h2]

/-- The index set of the grid parametrization: a cell and a matrix entry. -/
abbrev SampleMeasIdx (d : ℕ) := (Fin d → ℤ) × Fin d × Fin d

/-- The skew part of the matrix stored at a cell. -/
def sampleMeas_skewOf (p : SampleMeasIdx d → ℝ) (j : Fin d → ℤ) : Mat d :=
  Matrix.of fun a b => (p (j, a, b) - p (j, b, a)) / 2

/-- The piecewise constant coefficient on the dyadic grid at level `n`. -/
def sampleMeas_gridField (ν : ℝ) (n : ℕ) (p : SampleMeasIdx d → ℝ) : CoeffField d :=
  fun y => ν • (1 : Mat d) + sampleMeas_skewOf p (sampleMeas_J n y)

theorem sampleMeas_skewOf_skew (p : SampleMeasIdx d → ℝ) (j : Fin d → ℤ) :
    matTranspose (sampleMeas_skewOf p j) = -sampleMeas_skewOf p j := by
  ext a b
  simp only [matTranspose, Matrix.transpose_apply, sampleMeas_skewOf, Matrix.of_apply,
    Matrix.neg_apply]
  ring

theorem sampleMeas_measurable_skewOfJ (p : SampleMeasIdx d → ℝ) (n : ℕ) :
    Measurable fun y : Vec d => sampleMeas_skewOf p (sampleMeas_J n y) :=
  (measurable_of_countable (sampleMeas_skewOf p)).comp (sampleMeas_measurable_J n)

theorem sampleMeas_exists_bound {R : ℝ} (hU : U ⊆ Metric.closedBall (0 : Vec d) R) (n : ℕ)
    (p : SampleMeasIdx d → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ U, ∀ a b, |sampleMeas_skewOf p (sampleMeas_J n y) a b| ≤ B := by
  have hF := sampleMeas_finite_J hU n
  have hS : ((sampleMeas_J n '' U) ×ˢ (Set.univ : Set (Fin d × Fin d))).Finite :=
    hF.prod Set.finite_univ
  obtain ⟨B0, hB0⟩ := (hS.image fun x : SampleMeasIdx d => |p x|).bddAbove
  refine ⟨max B0 0, le_max_right _ _, fun y hy a b => ?_⟩
  have h1 : |p (sampleMeas_J n y, a, b)| ≤ B0 :=
    hB0 ⟨(sampleMeas_J n y, a, b), ⟨⟨y, hy, rfl⟩, Set.mem_univ _⟩, rfl⟩
  have h2 : |p (sampleMeas_J n y, b, a)| ≤ B0 :=
    hB0 ⟨(sampleMeas_J n y, b, a), ⟨⟨y, hy, rfl⟩, Set.mem_univ _⟩, rfl⟩
  have h3 := abs_le.1 h1
  have h4 := abs_le.1 h2
  simp only [sampleMeas_skewOf, Matrix.of_apply]
  rw [abs_le]
  constructor <;> linarith only [h3.1, h3.2, h4.1, h4.2, le_max_left B0 0]

theorem sampleMeas_gridField_elliptic {R : ℝ} (hU : U ⊆ Metric.closedBall (0 : Vec d) R)
    (hUm : MeasurableSet U) {ν : ℝ} (hν : 0 < ν) (n : ℕ) (p : SampleMeasIdx d → ℝ) :
    ∃ Lam, IsEllipticFieldOn ν Lam U (sampleMeas_gridField ν n p) := by
  obtain ⟨B, hB0, hB⟩ := sampleMeas_exists_bound hU n p
  exact ⟨_, sampleMeas_isElliptic_of_skew hν hB0 hUm (sampleMeas_measurable_skewOfJ p n)
    (fun y _ => sampleMeas_skewOf_skew p _) (fun y hy a b => hB y hy a b)⟩

/-- The grid functional at level `n`, as a function of the cell data. -/
def sampleMeas_thetaN (α ν : ℝ) (hα : 0 < α) (hν : 0 < ν) (f ψ : ScalarL2 U) (n : ℕ)
    (p : SampleMeasIdx d → ℝ) : ℝ :=
  sampleMeas_theta α ν hα hν f ψ (sampleMeas_gridField ν n p)

theorem sampleMeas_continuous_thetaN {R : ℝ} (hU : U ⊆ Metric.closedBall (0 : Vec d) R)
    (hUm : MeasurableSet U) {α ν : ℝ} (hα : 0 < α) (hν : 0 < ν) (f ψ : ScalarL2 U) (n : ℕ) :
    Continuous (sampleMeas_thetaN α ν hα hν f ψ n) := by
  rw [continuous_iff_continuousAt]
  intro q
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set C : ℝ := ‖ψ‖ * ((d : ℝ) * ‖f‖ / (min α ν) ^ 2) with hC
  have hC0 : 0 ≤ C := by positivity
  set δ : ℝ := ε / (2 * (C + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hF := sampleMeas_finite_J hU n
  have hS : ((sampleMeas_J n '' U) ×ˢ (Set.univ : Set (Fin d × Fin d))).Finite :=
    hF.prod Set.finite_univ
  have hopen : IsOpen (⋂ x ∈ hS.toFinset, {p : SampleMeasIdx d → ℝ | |p x - q x| < δ}) := by
    refine isOpen_biInter_finset fun x _ => ?_
    exact isOpen_lt (by fun_prop) continuous_const
  have hmem : q ∈ ⋂ x ∈ hS.toFinset, {p : SampleMeasIdx d → ℝ | |p x - q x| < δ} := by
    refine Set.mem_iInter₂.2 fun x _ => ?_
    simpa using hδ0
  filter_upwards [hopen.mem_nhds hmem] with p hp0
  have hp : ∀ x ∈ hS.toFinset, |p x - q x| < δ := fun x hx => Set.mem_iInter₂.1 hp0 x hx
  obtain ⟨Lp, hLp⟩ := sampleMeas_gridField_elliptic hU hUm hν n p
  obtain ⟨Lq, hLq⟩ := sampleMeas_gridField_elliptic hU hUm hν n q
  have hent : ∀ y ∈ U, ∀ a b, |sampleMeas_gridField ν n p y a b - sampleMeas_gridField ν n q y a b| ≤ δ := by
    intro y hy a b
    have hx1 : (sampleMeas_J n y, a, b) ∈ hS.toFinset := by
      simp only [Set.Finite.mem_toFinset]
      exact ⟨⟨y, hy, rfl⟩, Set.mem_univ _⟩
    have hx2 : (sampleMeas_J n y, b, a) ∈ hS.toFinset := by
      simp only [Set.Finite.mem_toFinset]
      exact ⟨⟨y, hy, rfl⟩, Set.mem_univ _⟩
    have e1 := abs_lt.1 (hp _ hx1)
    have e2 := abs_lt.1 (hp _ hx2)
    simp only [sampleMeas_gridField, sampleMeas_skewOf, Matrix.add_apply, Matrix.of_apply,
      add_sub_add_left_eq_sub]
    rw [abs_le]
    constructor <;> linarith only [e1.1, e1.2, e2.1, e2.2]
  have hlip := sampleMeas_theta_lipschitz hα hν f ψ hLp hLq hδ0.le hent
  rw [Real.dist_eq]
  show |sampleMeas_theta α ν hα hν f ψ (sampleMeas_gridField ν n p) -
    sampleMeas_theta α ν hα hν f ψ (sampleMeas_gridField ν n q)| < ε
  refine lt_of_le_of_lt hlip ?_
  have : ‖ψ‖ * ((d : ℝ) * δ * ‖f‖ / (min α ν) ^ 2) = C * δ := by rw [hC]; ring
  rw [this, hδ]
  have h1 : C * (ε / (2 * (C + 1))) = ε * (C / (2 * (C + 1))) := by ring
  rw [h1]
  have h2 : C / (2 * (C + 1)) < 1 := by
    rw [div_lt_one (by positivity)]; linarith only [hC0]
  nlinarith only [h2, hε]

/-- A continuous skew field is bounded by an entrywise constant on a bounded set. -/
theorem sampleMeas_exists_entry_bound {R : ℝ} (hU : U ⊆ Metric.closedBall (0 : Vec d) R)
    {k : Vec d → Mat d} (hk : Continuous k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ U, ∀ a b, |k y a b| ≤ B := by
  have hent : ∀ a b : Fin d, ∃ B : ℝ, ∀ y ∈ Metric.closedBall (0 : Vec d) R, ‖k y a b‖ ≤ B := by
    intro a b
    have hc : Continuous fun y : Vec d => k y a b :=
      (continuous_apply b).comp ((continuous_apply a).comp hk)
    exact (isCompact_closedBall (0 : Vec d) R).exists_bound_of_continuousOn hc.continuousOn
  choose B hB using hent
  refine ⟨∑ a, ∑ b, max (B a b) 0, by positivity, fun y hy a b => ?_⟩
  have h1 := hB a b y (hU hy)
  rw [Real.norm_eq_abs] at h1
  have h2 : max (B a b) 0 ≤ ∑ b', max (B a b') 0 :=
    Finset.single_le_sum (f := fun b' => max (B a b') 0) (fun _ _ => le_max_right _ _)
      (Finset.mem_univ b)
  have h3 : ∑ b', max (B a b') 0 ≤ ∑ a', ∑ b', max (B a' b') 0 :=
    Finset.single_le_sum (f := fun a' => ∑ b', max (B a' b') 0)
      (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ a)
  linarith only [h1, h2, h3, le_max_left (B a b) 0]

theorem sampleMeas_eventually_grid_close {R : ℝ} {k : Vec d → Mat d} (hk : Continuous k) {δ : ℝ}
    (hδ : 0 < δ) (hU : U ⊆ Metric.closedBall (0 : Vec d) R) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ a b, ∀ y ∈ U,
      |k (sampleMeas_corner n (sampleMeas_J n y)) a b - k y a b| < δ := by
  rw [Filter.eventually_all]; intro a
  rw [Filter.eventually_all]; intro b
  have hc : Continuous fun y : Vec d => k y a b :=
    (continuous_apply b).comp ((continuous_apply a).comp hk)
  have hK := (isCompact_closedBall (0 : Vec d) (R + 1)).uniformContinuousOn_of_continuous
    hc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hK
  obtain ⟨η, hη, hηK⟩ := hK δ hδ
  have hlim : Filter.Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    simpa [one_div, inv_pow] using this
  filter_upwards [hlim.eventually (gt_mem_nhds hη), Filter.eventually_ge_atTop 0] with n hn _
  intro y hy
  have hd := sampleMeas_dist_corner_J_le n y
  have hn1 : 1 / (2 : ℝ) ^ n ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hyR := mem_closedBall_zero_iff.1 (hU hy)
  refine hηK _ ?_ _ ?_ ?_
  · rw [mem_closedBall_zero_iff]
    have := norm_le_norm_add_norm_sub' (sampleMeas_corner n (sampleMeas_J n y)) y
    rw [← dist_eq_norm] at this
    linarith only [this, hd, hn1, hyR]
  · rw [mem_closedBall_zero_iff]; linarith only [hyR]
  · exact lt_of_le_of_lt hd hn

/-- **Measurability in the sample of the ball-average functional.**  If `K` is a jointly
measurable family of fields, continuous and skew on a set `G` of samples, the functional
`ω ↦ θ(ν I + K ω)` is measurable on `G`. -/
theorem sampleMeas_measurable_theta {Ω : Type*} [MeasurableSpace Ω] (G : Set Ω) {R : ℝ}
    (hU : U ⊆ Metric.closedBall (0 : Vec d) R) (hUm : MeasurableSet U) {α ν : ℝ}
    (hα : 0 < α) (hν : 0 < ν) (f ψ : ScalarL2 U) (K : Ω → Vec d → Mat d)
    (hK : Measurable fun q : Vec d × Ω => K q.2 q.1)
    (hgood : ∀ ω ∈ G, Continuous (K ω) ∧ ∀ y, matTranspose (K ω y) = -K ω y) :
    Measurable (fun ω : G =>
      sampleMeas_theta α ν hα hν f ψ (fun y => ν • (1 : Mat d) + K ω y)) := by
  set pn : ℕ → Ω → SampleMeasIdx d → ℝ := fun n ω x =>
    K ω (sampleMeas_corner n x.1) x.2.1 x.2.2 with hpn
  have hpm : ∀ n, Measurable (pn n) := by
    intro n
    refine measurable_pi_iff.2 fun x => ?_
    have h1 : Measurable fun ω : Ω => K ω (sampleMeas_corner n x.1) :=
      hK.comp (measurable_const.prodMk measurable_id)
    exact (measurable_pi_apply x.2.2).comp ((measurable_pi_apply x.2.1).comp h1)
  have hmeas : ∀ n, Measurable fun ω : G => sampleMeas_thetaN α ν hα hν f ψ n (pn n ω) :=
    fun n => (sampleMeas_continuous_thetaN hU hUm hα hν f ψ n).measurable.comp
      ((hpm n).comp measurable_subtype_coe)
  refine measurable_of_tendsto_metrizable hmeas ?_
  rw [tendsto_pi_nhds]
  intro ω
  obtain ⟨hcont, hskew⟩ := hgood ω ω.2
  obtain ⟨B, hB0, hB⟩ := sampleMeas_exists_entry_bound hU hcont
  have hEc : IsEllipticFieldOn ν ((ν ^ 2 + ((d : ℝ) * B) ^ 2) / ν) U
      (fun y => ν • (1 : Mat d) + K ω y) :=
    sampleMeas_isElliptic_of_skew hν hB0 hUm (by
      refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
      exact ((continuous_apply b).comp ((continuous_apply a).comp hcont)).measurable)
      (fun y _ => hskew y) hB
  set C : ℝ := ‖ψ‖ * ((d : ℝ) * ‖f‖ / (min α ν) ^ 2) with hC
  have hC0 : 0 ≤ C := by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (2 * (C + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hev := sampleMeas_eventually_grid_close hcont hδ0 hU
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨Lg, hLg⟩ := sampleMeas_gridField_elliptic hU hUm hν n (pn n ω)
  have hent : ∀ y ∈ U, ∀ a b, |sampleMeas_gridField ν n (pn n ω) y a b -
      (ν • (1 : Mat d) + K ω y) a b| ≤ δ := by
    intro y hy a b
    have h1 := hN n hn a b y hy
    have h2 : sampleMeas_gridField ν n (pn n ω) y a b - (ν • (1 : Mat d) + K ω y) a b =
        K ω (sampleMeas_corner n (sampleMeas_J n y)) a b - K ω y a b := by
      have hs : K ω (sampleMeas_corner n (sampleMeas_J n y)) b a =
          -K ω (sampleMeas_corner n (sampleMeas_J n y)) a b := by
        have := congrFun (congrFun (hskew (sampleMeas_corner n (sampleMeas_J n y))) a) b
        simpa [matTranspose] using this
      simp only [sampleMeas_gridField, sampleMeas_skewOf, Matrix.add_apply, Matrix.of_apply, hpn,
        add_sub_add_left_eq_sub, hs]
      ring
    rw [h2]; exact h1.le
  have hlip := sampleMeas_theta_lipschitz hα hν f ψ hLg hEc hδ0.le hent
  rw [Real.dist_eq]
  show |sampleMeas_theta α ν hα hν f ψ (sampleMeas_gridField ν n (pn n ω)) -
    sampleMeas_theta α ν hα hν f ψ (fun y => ν • (1 : Mat d) + K ω y)| < ε
  refine lt_of_le_of_lt hlip ?_
  have : ‖ψ‖ * ((d : ℝ) * δ * ‖f‖ / (min α ν) ^ 2) = C * δ := by rw [hC]; ring
  rw [this, hδ]
  have h1 : C * (ε / (2 * (C + 1))) = ε * (C / (2 * (C + 1))) := by ring
  rw [h1]
  have h2 : C / (2 * (C + 1)) < 1 := by
    rw [div_lt_one (by positivity)]; linarith only [hC0]
  nlinarith only [h2, hε]

end

end SuperdiffusionCLT.Section8
