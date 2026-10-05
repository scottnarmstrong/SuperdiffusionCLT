/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.Foundations.H10Graph
public import Homogenization.Sobolev.Foundations.CoerciveH10
public import Homogenization.Geometry.ConvexDomain

/-!
# `H¹₀` of a bounded open set: realization and Poincaré inequality

The closed `H¹₀` graph of a bounded open set `U` is realised by honest `H¹₀(U)` functions,
and the zero-trace `L²` Poincaré inequality holds on `U` in every dimension `d ≠ 0`.
Both facts are transported from the convex case: the realization argument uses only that `U`
is open, and the Poincaré inequality is read off on a cube containing `U`.

## Main results

* `Section7.exists_h10Function_of_mem_closedGraph`: closed-graph points are `H¹₀` functions.
* `Section7.h10_poincare_of_bounded`: `‖u‖₂ ≤ C * ∑ᵢ ‖∂ᵢ u‖₂` for `u ∈ H¹₀(U)`.
* `Section7.h10Graph_norm_value_le_of_bounded`: the same estimate on the closed graph.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ} {U : Set (Vec d)}

/-- The `L²` distance between scalar representatives of two `H¹` functions is
the scalar `L²` distance between their `toScalarL2` realisations. -/
private theorem eLpNorm_toFun_sub_eq_edist_toScalarL2
    (u v : H1Function U) :
    MeasureTheory.eLpNorm (fun x => u.toFun x - v.toFun x) 2 (volumeMeasureOn U)
      = edist u.toScalarL2 v.toScalarL2 := by
  rw [MeasureTheory.Lp.edist_def]
  refine (MeasureTheory.eLpNorm_congr_ae ?_).symm
  filter_upwards [u.coeFn_toScalarL2, v.coeFn_toScalarL2] with x hu hv
  simp [Pi.sub_apply, hu, hv]

/-- The coordinate-wise `L²` distance between weak gradients equals the
`ScalarL2` distance between `gradCoordToScalarL2` realisations. -/
private theorem eLpNorm_grad_coord_sub_eq_edist_gradCoordToScalarL2
    (u v : H1Function U) (i : Fin d) :
    MeasureTheory.eLpNorm (fun x => u.grad x i - v.grad x i) 2 (volumeMeasureOn U)
      = edist (u.gradCoordToScalarL2 i) (v.gradCoordToScalarL2 i) := by
  rw [MeasureTheory.Lp.edist_def]
  refine (MeasureTheory.eLpNorm_congr_ae ?_).symm
  filter_upwards [u.coeFn_gradCoordToScalarL2 i, v.coeFn_gradCoordToScalarL2 i]
    with x hu hv
  simp [Pi.sub_apply, hu, hv]

/-- Coordinate-wise `L²` distance of two weak gradients is controlled by the
`HilbertVectorL2` distance of their gradient realisations. -/
private theorem eLpNorm_grad_coord_sub_le_edist_gradToHilbertVectorL2
    (u v : H1Function U) (i : Fin d) :
    MeasureTheory.eLpNorm (fun x => u.grad x i - v.grad x i) 2 (volumeMeasureOn U)
      ≤ edist u.gradToHilbertVectorL2 v.gradToHilbertVectorL2 := by
  have hrhs :
      edist u.gradToHilbertVectorL2 v.gradToHilbertVectorL2
        = MeasureTheory.eLpNorm
            (fun x => HilbertVec.ofVec (u.grad x - v.grad x)) 2
            (volumeMeasureOn U) := by
    rw [MeasureTheory.Lp.edist_def]
    refine MeasureTheory.eLpNorm_congr_ae ?_
    filter_upwards
        [u.coeFn_gradToHilbertVectorL2, v.coeFn_gradToHilbertVectorL2] with x hu hv
    simp [Pi.sub_apply, hu, hv, hilbertifyVecField]
  rw [hrhs]
  refine MeasureTheory.eLpNorm_mono_ae
    ((u.grad_memL2 i).aestronglyMeasurable.sub (v.grad_memL2 i).aestronglyMeasurable)
    (Filter.Eventually.of_forall ?_)
  intro x
  have hcoord : ‖u.grad x i - v.grad x i‖ ≤ ‖u.grad x - v.grad x‖ := by
    simpa [Pi.sub_apply, Real.norm_eq_abs] using
      norm_le_pi_norm (u.grad x - v.grad x) i
  have hVec_le_Hilbert :
      ‖u.grad x - v.grad x‖ ≤ ‖HilbertVec.ofVec (u.grad x - v.grad x)‖ :=
    HilbertVec.norm_le_norm_ofVec (u.grad x - v.grad x)
  exact hcoord.trans hVec_le_Hilbert

/-- `ScalarL2` distance on `gradCoordToScalarL2` is controlled by the
`HilbertVectorL2` distance on `gradToHilbertVectorL2`. -/
private theorem edist_gradCoordToScalarL2_le_edist_gradToHilbertVectorL2
    (u v : H1Function U) (i : Fin d) :
    edist (u.gradCoordToScalarL2 i) (v.gradCoordToScalarL2 i)
      ≤ edist u.gradToHilbertVectorL2 v.gradToHilbertVectorL2 := by
  rw [← eLpNorm_grad_coord_sub_eq_edist_gradCoordToScalarL2]
  exact eLpNorm_grad_coord_sub_le_edist_gradToHilbertVectorL2 u v i

/-- Every point of the closed `H¹₀` graph is realized by an honest `H¹₀`
function on open sets. The witness is obtained by
diagonalising closure approximations against each graph approximant's internal
smooth compactly supported approximation data. -/
theorem exists_h10Function_of_mem_closedGraph
    (hUopen : IsOpen U)
    {z : ScalarL2 U × HilbertVectorL2 U}
    (hz : z ∈ (h10GraphClosedSubmodule U).toSubmodule) :
    ∃ u : H10Function U,
      u.toH1Function.toScalarL2 = z.1
        ∧ u.toH1Function.gradToHilbertVectorL2 = z.2 := by
  classical
  -- (1) H¹ witness from the weaker graph containment.
  have hzH1 : z ∈ h1GraphClosedSubmodule (U := U) :=
    h10GraphClosedSubmodule_le_h1GraphClosedSubmodule (U := U) hz
  set v : H1Function U := toH1FunctionOfMemH1Graph (U := U) z hzH1 with v_def
  have hv_val : v.toScalarL2 = z.1 :=
    toH1FunctionOfMemH1Graph_toScalarL2 (U := U) z hzH1
  have hv_grad : v.gradToHilbertVectorL2 = z.2 :=
    toH1FunctionOfMemH1Graph_gradToHilbertVectorL2 (U := U) z hzH1
  -- (2) Closure → approximating sequence of graph points.
  have hz_closure :
      z ∈ closure ((h10GraphSubmodule U : Submodule ℝ
        (ScalarL2 U × HilbertVectorL2 U)) : Set (ScalarL2 U × HilbertVectorL2 U)) := by
    have hzSub : z ∈ (h10GraphSubmodule U).topologicalClosure := hz
    simpa [Submodule.topologicalClosure_coe] using! hzSub
  obtain ⟨ψ, hψ_mem, hψ_tendsto⟩ := mem_closure_iff_seq_limit.mp hz_closure
  choose φ hφ_val hφ_grad using hψ_mem
  -- (3) Component-wise convergence.
  have hval_tendsto :
      Filter.Tendsto (fun n => (φ n).toH1Function.toScalarL2) Filter.atTop
        (nhds v.toScalarL2) := by
    rw [hv_val]
    exact hψ_tendsto.fst_nhds.congr'
      (Filter.Eventually.of_forall fun n => (hφ_val n).symm)
  have hgrad_tendsto :
      Filter.Tendsto (fun n => (φ n).toH1Function.gradToHilbertVectorL2) Filter.atTop
        (nhds v.gradToHilbertVectorL2) := by
    rw [hv_grad]
    exact hψ_tendsto.snd_nhds.congr'
      (Filter.Eventually.of_forall fun n => (hφ_grad n).symm)
  -- (4) Convergence of `gradCoordToScalarL2 i` for each `i`, via the coord bound.
  have hgrad_edist_zero :
      Filter.Tendsto
        (fun n => edist (φ n).toH1Function.gradToHilbertVectorL2 v.gradToHilbertVectorL2)
        Filter.atTop (nhds 0) := by
    rw [← edist_self v.gradToHilbertVectorL2]
    exact (continuous_id.edist continuous_const).continuousAt.tendsto.comp hgrad_tendsto
  have hgradcoord_edist_zero :
      ∀ i : Fin d, Filter.Tendsto
        (fun n => edist ((φ n).toH1Function.gradCoordToScalarL2 i)
          (v.gradCoordToScalarL2 i))
        Filter.atTop (nhds 0) := by
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ => (0 : ENNReal))
      (h := fun n =>
        edist (φ n).toH1Function.gradToHilbertVectorL2 v.gradToHilbertVectorL2)
      tendsto_const_nhds hgrad_edist_zero (fun _ => bot_le) ?_
    intro n
    exact edist_gradCoordToScalarL2_le_edist_gradToHilbertVectorL2
      (φ n).toH1Function v i
  have hgradcoord_tendsto :
      ∀ i : Fin d, Filter.Tendsto
        (fun n => (φ n).toH1Function.gradCoordToScalarL2 i) Filter.atTop
        (nhds (v.gradCoordToScalarL2 i)) := by
    intro i
    refine (EMetric.tendsto_nhds).mpr ?_
    intro ε hε
    exact (hgradcoord_edist_zero i).eventually (gt_mem_nhds hε)
  -- (5) Reformulate: we want convergence in `ScalarL2 U` of
  -- `(approxH1 hUopen (φ n) m).toScalarL2 → (φ n).toScalarL2`, which is
  -- directly the content of `tendsto_approxH1_toScalarL2` from `CoerciveH10`.
  have happroxH1_val :
      ∀ n : ℕ, Filter.Tendsto
        (fun m => (H10Function.approxH1 hUopen (φ n) m).toScalarL2)
        Filter.atTop (nhds (φ n).toH1Function.toScalarL2) :=
    fun n => H10Function.tendsto_approxH1_toScalarL2 hUopen (φ n)
  have happroxH1_gradcoord :
      ∀ n : ℕ, ∀ i : Fin d, Filter.Tendsto
        (fun m => (H10Function.approxH1 hUopen (φ n) m).gradCoordToScalarL2 i)
        Filter.atTop (nhds ((φ n).toH1Function.gradCoordToScalarL2 i)) :=
    fun n i =>
      H10Function.tendsto_approxH1_gradCoordToScalarL2 hUopen (φ n) i
  -- (6) Diagonal: for each n, choose m n so that
  --     dist ((approxH1 (φ n) (m n)).toScalarL2) ((φ n).toScalarL2) ≤ 1/(n+1)
  --     dist ((approxH1 (φ n) (m n)).gradCoordToScalarL2 i) ((φ n).gradCoordToScalarL2 i) ≤ 1/(n+1)
  have diagonal :
      ∀ n : ℕ, ∃ m : ℕ,
        dist (H10Function.approxH1 hUopen (φ n) m).toScalarL2
            (φ n).toH1Function.toScalarL2 ≤ ((n : ℝ) + 1)⁻¹ ∧
        (∀ i : Fin d,
          dist ((H10Function.approxH1 hUopen (φ n) m).gradCoordToScalarL2 i)
            ((φ n).toH1Function.gradCoordToScalarL2 i) ≤ ((n : ℝ) + 1)⁻¹) := by
    intro n
    have hε_pos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by
      refine inv_pos.mpr ?_
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith only [hn]
    have hscalar := (Metric.tendsto_atTop.mp (happroxH1_val n)) _ hε_pos
    have hcoords : ∀ i : Fin d, ∃ N : ℕ, ∀ m ≥ N,
        dist ((H10Function.approxH1 hUopen (φ n) m).gradCoordToScalarL2 i)
          ((φ n).toH1Function.gradCoordToScalarL2 i) < ((n : ℝ) + 1)⁻¹ := fun i =>
      (Metric.tendsto_atTop.mp (happroxH1_gradcoord n i)) _ hε_pos
    choose Nc hNc using hcoords
    obtain ⟨Nv, hNv⟩ := hscalar
    let M : ℕ := max Nv ((Finset.univ : Finset (Fin d)).sup Nc)
    have hMv : Nv ≤ M := le_max_left _ _
    have hMc : ∀ i : Fin d, Nc i ≤ M := by
      intro i
      refine le_max_of_le_right ?_
      exact Finset.le_sup (f := Nc) (Finset.mem_univ i)
    refine ⟨M, (hNv M hMv).le, ?_⟩
    intro i
    exact (hNc i M (hMc i)).le
  choose m hm_val hm_grad using diagonal
  -- (7) Build the H¹₀ function whose approximants are the chosen diagonal.
  -- First produce `a n : H1Function U` as the diagonal smooth H¹-packaging.
  let a : ℕ → H1Function U := fun n => H10Function.approxH1 hUopen (φ n) (m n)
  -- (a n).toScalarL2 → v.toScalarL2
  -- Helper: 1/(n+1) is small eventually.
  have hinv_small : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ((n : ℝ) + 1)⁻¹ < ε := by
    intro ε hε
    have htend_one_div :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have heq : (fun n : ℕ => 1 / ((n : ℝ) + 1)) =
        fun n : ℕ => ((n : ℝ) + 1)⁻¹ := by
      funext n; rw [one_div]
    rw [heq] at htend_one_div
    have hev := Metric.tendsto_atTop.mp htend_one_div ε hε
    obtain ⟨N, hN⟩ := hev
    refine ⟨N, fun n hn => ?_⟩
    have hnn := hN n hn
    have hpos : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by
      refine inv_nonneg.mpr ?_
      have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith only [hcast]
    calc ((n : ℝ) + 1)⁻¹ = |((n : ℝ) + 1)⁻¹| := (abs_of_nonneg hpos).symm
      _ = dist (((n : ℝ) + 1)⁻¹) 0 := by rw [Real.dist_eq, sub_zero]
      _ < ε := hnn
  have ha_val :
      Filter.Tendsto (fun n => (a n).toScalarL2) Filter.atTop (nhds v.toScalarL2) := by
    refine Metric.tendsto_atTop.mpr ?_
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    obtain ⟨N₁, hN₁⟩ := hinv_small (ε / 2) hε2
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hval_tendsto (ε / 2) hε2
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hn1 : N₁ ≤ n := le_of_max_le_left hn
    have hn2 : N₂ ≤ n := le_of_max_le_right hn
    have htri : dist (a n).toScalarL2 v.toScalarL2 ≤
        dist (a n).toScalarL2 (φ n).toH1Function.toScalarL2
          + dist (φ n).toH1Function.toScalarL2 v.toScalarL2 := dist_triangle _ _ _
    have hm_val_n : dist (a n).toScalarL2 (φ n).toH1Function.toScalarL2
        ≤ ((n : ℝ) + 1)⁻¹ := hm_val n
    have hN₂_n : dist (φ n).toH1Function.toScalarL2 v.toScalarL2 < ε / 2 := hN₂ n hn2
    have hN₁_n : ((n : ℝ) + 1)⁻¹ < ε / 2 := hN₁ n hn1
    linarith only [htri, hm_val_n, hN₂_n, hN₁_n]
  have ha_gradcoord :
      ∀ i : Fin d, Filter.Tendsto (fun n => (a n).gradCoordToScalarL2 i)
        Filter.atTop (nhds (v.gradCoordToScalarL2 i)) := by
    intro i
    refine Metric.tendsto_atTop.mpr ?_
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    obtain ⟨N₁, hN₁⟩ := hinv_small (ε / 2) hε2
    obtain ⟨N₂, hN₂⟩ :=
      Metric.tendsto_atTop.mp (hgradcoord_tendsto i) (ε / 2) hε2
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hn1 : N₁ ≤ n := le_of_max_le_left hn
    have hn2 : N₂ ≤ n := le_of_max_le_right hn
    have htri : dist ((a n).gradCoordToScalarL2 i) (v.gradCoordToScalarL2 i) ≤
        dist ((a n).gradCoordToScalarL2 i) ((φ n).toH1Function.gradCoordToScalarL2 i)
          + dist ((φ n).toH1Function.gradCoordToScalarL2 i) (v.gradCoordToScalarL2 i) :=
      dist_triangle _ _ _
    have hm_grad_n :
        dist ((a n).gradCoordToScalarL2 i) ((φ n).toH1Function.gradCoordToScalarL2 i)
          ≤ ((n : ℝ) + 1)⁻¹ := hm_grad n i
    have hN₂_n : dist ((φ n).toH1Function.gradCoordToScalarL2 i)
        (v.gradCoordToScalarL2 i) < ε / 2 := hN₂ n hn2
    have hN₁_n : ((n : ℝ) + 1)⁻¹ < ε / 2 := hN₁ n hn1
    linarith only [htri, hm_grad_n, hN₂_n, hN₁_n]
  -- Convert these ScalarL2 tendsto's to the eLpNorm tendsto required by H10Function.
  have htendsto_val_eLpNorm :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun x => (φ n).approx (m n) x - v.toFun x) 2 (volumeMeasureOn U))
        Filter.atTop (nhds 0) := by
    -- (a n).toScalarL2 = ((φ n).approx (m n)).toScalarL2 via ofContDiff.
    -- Use edist characterization.
    have hedist :
        Filter.Tendsto (fun n => edist (a n).toScalarL2 v.toScalarL2) Filter.atTop
          (nhds 0) := by
      rw [← edist_self v.toScalarL2]
      exact (continuous_id.edist continuous_const).continuousAt.tendsto.comp ha_val
    refine hedist.congr ?_
    intro n
    -- edist (a n).toScalarL2 v.toScalarL2
    --   = eLpNorm ((a n).toFun - v.toFun) 2 μ
    --   = eLpNorm ((φ n).approx (m n) - v.toFun) 2 μ
    rw [← eLpNorm_toFun_sub_eq_edist_toScalarL2]
    -- (a n).toFun = (φ n).approx (m n)
    rfl
  have htendsto_grad_eLpNorm :
      ∀ i : Fin d, Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun x =>
              (fderiv ℝ ((φ n).approx (m n)) x) (basisVec i) -
                v.grad x i) 2 (volumeMeasureOn U))
        Filter.atTop (nhds 0) := by
    intro i
    have hedist :
        Filter.Tendsto
          (fun n => edist ((a n).gradCoordToScalarL2 i) (v.gradCoordToScalarL2 i))
          Filter.atTop (nhds 0) := by
      rw [← edist_self (v.gradCoordToScalarL2 i)]
      exact (continuous_id.edist continuous_const).continuousAt.tendsto.comp
        (ha_gradcoord i)
    refine hedist.congr ?_
    intro n
    rw [← eLpNorm_grad_coord_sub_eq_edist_gradCoordToScalarL2]
    -- (a n).grad x i = (fderiv ℝ ((φ n).approx (m n)) x) (basisVec i)
    rfl
  -- Now assemble the H¹₀ function.
  let u : H10Function U :=
    { toH1Function := v
      approx := fun n => (φ n).approx (m n)
      approx_smooth := fun n => (φ n).approx_smooth (m n)
      approx_hasCompactSupport := fun n => (φ n).approx_hasCompactSupport (m n)
      approx_support_subset := fun n => (φ n).approx_support_subset (m n)
      tendsto_approx := htendsto_val_eLpNorm
      tendsto_approx_grad := htendsto_grad_eLpNorm }
  exact ⟨u, hv_val, hv_grad⟩

/-- A bounded set lies in a sup-norm ball, which is a bounded open convex domain. -/
theorem exists_ball_superset_of_isBoundedDomain (hU : IsBoundedDomain U) :
    ∃ R : ℝ, 0 < R ∧ U ⊆ Metric.ball (0 : Vec d) R := by
  rcases hU with ⟨R, hR, hbd⟩
  refine ⟨R + 1, by linarith only [hR], fun x hx => ?_⟩
  rw [mem_ball_zero_iff, pi_norm_lt_iff (by linarith only [hR])]
  intro i
  have := hbd x hx i
  rw [Real.norm_eq_abs]
  linarith only [this]

theorem isOpenBoundedConvexDomain_ball_zero (R : ℝ) :
    IsOpenBoundedConvexDomain (Metric.ball (0 : Vec d) R) :=
  ⟨Metric.isOpen_ball, (Metric.isBounded_ball).isBoundedDomain, convex_ball _ _⟩

/-- Norms of a function supported in `S` do not see the ambient measure restriction. -/
theorem eLpNorm_restrict_eq_of_tsupport {S : Set (Vec d)} 
    {f : Vec d → ℝ} (hc : Continuous f) (hf : tsupport f ⊆ S) (p : ENNReal) :
    MeasureTheory.eLpNorm f p (volumeMeasureOn S) =
      MeasureTheory.eLpNorm f p MeasureTheory.volume :=
  MeasureTheory.eLpNorm_restrict_eq_of_support_subset hc.aestronglyMeasurable
    ((subset_tsupport f).trans hf)

/-- The `L²` norm of the value class is the `L²` norm of the representative. -/
theorem norm_toScalarL2_eq {S : Set (Vec d)} (u : H1Function S) :
    ‖u.toScalarL2‖ = (MeasureTheory.eLpNorm u.toFun 2 (volumeMeasureOn S)).toReal := by
  simp [H1Function.toScalarL2, Homogenization.toScalarL2, MeasureTheory.Lp.norm_toLp]

/-- The coordinate gradient sum as a sum of `L²` norms. -/
theorem gradientCoordL2NormSum_eq {S : Set (Vec d)} (u : H1Function S) :
    u.gradientCoordL2NormSum = ∑ i : Fin d,
      (MeasureTheory.eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn S)).toReal := by
  simp [H1Function.gradientCoordL2NormSum, H1Function.gradCoordToScalarL2,
    Homogenization.toScalarL2, MeasureTheory.Lp.norm_toLp]

/-- A Poincaré inequality on `B ⊇ U` transfers to the smooth approximants of `H¹₀(U)`. -/
theorem approxH1_poincare_of_subset {B : Set (Vec d)} (hB : IsOpen B) (hUo : IsOpen U)
    (hUB : U ⊆ B) {C : ℝ}
    (hC : ∀ v : H10Function B,
      ‖v.toH1Function.toScalarL2‖ ≤ C * v.toH1Function.gradientCoordL2NormSum)
    (u : H10Function U) (n : ℕ) :
    ‖(H10Function.approxH1 hUo u n).toScalarL2‖ ≤
      C * (H10Function.approxH1 hUo u n).gradientCoordL2NormSum := by
  have hsub : tsupport (u.approx n) ⊆ B := (u.approx_support_subset n).trans hUB
  have hsm : ContDiff ℝ 1 (u.approx n) := (u.approx_smooth n).of_le (by simp)
  have hcont : Continuous (u.approx n) := hsm.continuous
  have hv := hC (H10Function.ofContDiff hB (u.approx_smooth n) (u.approx_hasCompactSupport n) hsub)
  have hdc : ∀ i : Fin d, Continuous (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) := fun i => by
    simpa using (hsm.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdsub : ∀ S : Set (Vec d), tsupport (u.approx n) ⊆ S → ∀ i : Fin d,
      tsupport (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) ⊆ S := by
    intro S hS i
    refine (closure_minimal ?_ (isClosed_tsupport _)).trans hS
    intro x hx
    apply support_fderiv_subset ℝ
    simp only [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    simp [h0]
  have hval : ‖(H10Function.approxH1 hUo u n).toScalarL2‖ =
      ‖(H10Function.ofContDiff hB (u.approx_smooth n) (u.approx_hasCompactSupport n)
        hsub).toH1Function.toScalarL2‖ := by
    rw [norm_toScalarL2_eq, norm_toScalarL2_eq]
    change (MeasureTheory.eLpNorm (u.approx n) 2 (volumeMeasureOn U)).toReal =
      (MeasureTheory.eLpNorm (u.approx n) 2 (volumeMeasureOn B)).toReal
    rw [eLpNorm_restrict_eq_of_tsupport hcont (u.approx_support_subset n),
      eLpNorm_restrict_eq_of_tsupport hcont hsub]
  have hgrad : (H10Function.approxH1 hUo u n).gradientCoordL2NormSum =
      (H10Function.ofContDiff hB (u.approx_smooth n) (u.approx_hasCompactSupport n)
        hsub).toH1Function.gradientCoordL2NormSum := by
    rw [gradientCoordL2NormSum_eq, gradientCoordL2NormSum_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (MeasureTheory.eLpNorm (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) 2
        (volumeMeasureOn U)).toReal =
      (MeasureTheory.eLpNorm (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) 2
        (volumeMeasureOn B)).toReal
    rw [eLpNorm_restrict_eq_of_tsupport (hdc i) (hdsub U (u.approx_support_subset n) i),
      eLpNorm_restrict_eq_of_tsupport (hdc i) (hdsub B hsub i)]
  rw [hval, hgrad]
  exact hv

/-- Zero-trace `L²` Poincaré inequality on a bounded open set, in every dimension. -/
theorem h10_poincare_of_bounded [NeZero d] (hUo : IsOpen U) (hUb : IsBoundedDomain U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H10Function U,
      ‖u.toH1Function.toScalarL2‖ ≤ C * u.toH1Function.gradientCoordL2NormSum := by
  rcases exists_ball_superset_of_isBoundedDomain hUb with ⟨R, -, hUB⟩
  have hB := isOpenBoundedConvexDomain_ball_zero (d := d) R
  rcases H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hB with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, fun u => ?_⟩
  have hleft : Filter.Tendsto (fun n => ‖(H10Function.approxH1 hUo u n).toScalarL2‖)
      Filter.atTop (nhds ‖u.toH1Function.toScalarL2‖) :=
    (continuous_norm.tendsto _).comp (H10Function.tendsto_approxH1_toScalarL2 hUo u)
  have hright : Filter.Tendsto
      (fun n => C * (H10Function.approxH1 hUo u n).gradientCoordL2NormSum) Filter.atTop
      (nhds (C * u.toH1Function.gradientCoordL2NormSum)) :=
    tendsto_const_nhds.mul (H10Function.tendsto_approxH1_gradientCoordL2NormSum hUo u)
  exact le_of_tendsto_of_tendsto' hleft hright
    (approxH1_poincare_of_subset hB.isOpen hUo hUB hC u)

/-- The Poincaré inequality on the closed `H¹₀` graph of a bounded open set. -/
theorem h10Graph_norm_value_le_of_bounded [NeZero d] (hUo : IsOpen U)
    (hUb : IsBoundedDomain U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ScalarL2 U × HilbertVectorL2 U,
      z ∈ h10GraphClosedSubmodule U → ‖z.1‖ ≤ C * ‖z.2‖ := by
  rcases h10_poincare_of_bounded hUo hUb with ⟨C0, hC0, hC0_bound⟩
  refine ⟨C0 * d, by positivity, fun z hz => ?_⟩
  refine h10GraphClosedSubmodule_norm_value_le_of_forall_h10 (U := U) (fun u => ?_) hz
  calc
    ‖u.toH1Function.toScalarL2‖ ≤ C0 * u.toH1Function.gradientCoordL2NormSum := hC0_bound u
    _ ≤ C0 * (d * ‖u.toH1Function.gradToHilbertVectorL2‖) := by
          refine mul_le_mul_of_nonneg_left ?_ hC0
          exact u.toH1Function.gradientCoordL2NormSum_le.trans
            (mul_le_mul_of_nonneg_left
              (H1Function.norm_gradToVectorL2_le_norm_gradToHilbertVectorL2 u.toH1Function)
              (Nat.cast_nonneg d))
    _ = (C0 * d) * ‖u.toH1Function.gradToHilbertVectorL2‖ := by ring

end SuperdiffusionCLT.Section7
