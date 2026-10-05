/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Limits of sequences with summable `L²` increments on the origin cubes

A sequence whose increments are summable in `L²` of every origin cube converges almost
everywhere, and in `L²` of every origin cube, with the usual tail bound.
-/

@[expose] public section

open scoped ENNReal Topology

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory Filter

variable {d : ℕ}

theorem e0e_normalizedCube_ac (Q : TriadicCube d) :
    normalizedCubeMeasure Q ≪ (volume : Measure (Vec d)) := by
  unfold normalizedCubeMeasure cubeMeasure
  exact Measure.AbsolutelyContinuous.smul_left Measure.restrict_le_self.absolutelyContinuous _

theorem e0e_ae_normalized_iff (Q : TriadicCube d) (P : Vec d → Prop) :
    (∀ᵐ x ∂(normalizedCubeMeasure Q), P x) ↔ ∀ᵐ x ∂(volume : Measure (Vec d)), x ∈ cubeSet Q → P x := by
  unfold normalizedCubeMeasure cubeMeasure
  have hc : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (inv_pos.2 (cubeVolume_pos Q))
  rw [← ae_restrict_iff' (measurableSet_cubeSet Q)]
  simp only [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or]


theorem e0e_exists_cube (x : Vec d) : ∃ k : ℕ, x ∈ cubeSet (originCube d (k : ℤ)) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 * ∑ i, |x i| + 1) (by norm_num : (1 : ℝ) < 3)
  refine ⟨k, ?_⟩
  rw [mem_cubeSet_originCube_iff]
  intro i
  have hi : |x i| ≤ ∑ j, |x j| :=
    Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have h3 : ((3 : ℝ) ^ (k : ℤ)) = 3 ^ k := zpow_natCast _ _
  rw [h3]
  have := abs_le.1 (hi.trans (by linarith only [hk] : ∑ j, |x j| ≤ 3 ^ k / 2))
  have h4 : x i < 3 ^ k / 2 := by
    have := abs_lt.1 (lt_of_le_of_lt hi (by linarith only [hk] : ∑ j, |x j| < 3 ^ k / 2))
    exact this.2
  constructor
  · linarith only [this.1]
  · linarith only [h4]

theorem e0e_tail_tsum [NeZero d] {fm : ℕ → Vec d → ℝ}
    (hmem : ∀ m k : ℕ, MemLp (fm m) 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hsum : ∀ k : ℕ, Summable fun m => cubeL2 k (fun x => fm (m + 1) x - fm m x)) (k m : ℕ) :
    ∑' i, eLpNorm (fun x => fm (m + i + 1) x - fm (m + i) x) 2
        (normalizedCubeMeasure (originCube d (k : ℤ))) =
      ENNReal.ofReal (∑' i, cubeL2 k (fun x => fm (m + i + 1) x - fm (m + i) x)) := by
  have hs : Summable fun i => cubeL2 k (fun x => fm (m + i + 1) x - fm (m + i) x) :=
    (hsum k).comp_injective (add_right_injective m)
  refine Eq.trans (tsum_congr fun i => ?_)
    (ENNReal.ofReal_tsum_of_nonneg (fun i => ENNReal.toReal_nonneg) hs).symm
  exact (ENNReal.ofReal_toReal ((((hmem (m + i + 1) k).sub (hmem (m + i) k))).eLpNorm_ne_top)).symm

/-- A sequence with summable increments in `L²` of every origin cube converges almost
everywhere and in `L²` of every origin cube to its pointwise limit. -/
theorem exists_limit_of_summable_cubeL2 [NeZero d] {fm : ℕ → Vec d → ℝ}
    (hmem : ∀ m k : ℕ, MemLp (fm m) 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hsum : ∀ k : ℕ, Summable fun m => cubeL2 k (fun x => fm (m + 1) x - fm m x)) :
    ∃ f : Vec d → ℝ, (∀ᵐ x ∂volume, Filter.Tendsto (fun m => fm m x) Filter.atTop (nhds (f x))) ∧
      ∀ k : ℕ, MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ))) ∧
        Filter.Tendsto (fun m => cubeL2 k (fun x => fm m x - f x)) Filter.atTop (nhds 0) ∧
        ∀ m : ℕ, cubeL2 k (fun x => f x - fm m x) ≤
          ∑' i : ℕ, cubeL2 k (fun x => fm (m + i + 1) x - fm (m + i) x) := by
  classical
  let flim : Vec d → ℝ := fun x =>
    if h : ∃ l, Tendsto (fun m => fm m x) atTop (𝓝 l) then h.choose else 0
  have hflim : ∀ x, (∃ l, Tendsto (fun m => fm m x) atTop (𝓝 l)) →
      Tendsto (fun m => fm m x) atTop (𝓝 (flim x)) := fun x h => by
    simp only [flim, h, dite_true]
    exact h.choose_spec
  have hcube : ∀ k : ℕ, ∀ᵐ x ∂(normalizedCubeMeasure (originCube d (k : ℤ))),
      ∃ l, Tendsto (fun m => fm m x) atTop (𝓝 l) := by
    intro k
    have hb := e0e_tail_tsum hmem hsum k 0
    simp only [zero_add] at hb
    have hb' : ∑' i, eLpNorm (fun x => fm (i + 1) x - fm i x) 2
        (normalizedCubeMeasure (originCube d (k : ℤ))) ≠ ∞ := by
      rw [hb]; exact ENNReal.ofReal_ne_top
    filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top (p := 2) (by norm_num) hb'] with x hx
    have hs : Summable (fun i => fm (i + 1) x - fm i x) := hx.of_norm
    refine ⟨fm 0 x + ∑' i, (fm (i + 1) x - fm i x), ?_⟩
    have h2 := hs.hasSum.tendsto_sum_nat.const_add (fm 0 x)
    refine h2.congr (fun n => ?_)
    rw [Finset.sum_range_sub (fun i => fm i x) n]
    ring
  have hae : ∀ᵐ x ∂(volume : Measure (Vec d)), ∃ l, Tendsto (fun m => fm m x) atTop (𝓝 l) := by
    have h1 : ∀ k : ℕ, ∀ᵐ x ∂(volume : Measure (Vec d)), x ∈ cubeSet (originCube d (k : ℤ)) →
        ∃ l, Tendsto (fun m => fm m x) atTop (𝓝 l) :=
      fun k => (e0e_ae_normalized_iff _ _).1 (hcube k)
    filter_upwards [ae_all_iff.2 h1] with x hx
    obtain ⟨k, hk⟩ := e0e_exists_cube x
    exact hx k hk
  refine ⟨flim, hae.mono (fun x hx => hflim x hx), fun k => ?_⟩
  have hacs : ∀ᵐ x ∂(normalizedCubeMeasure (originCube d (k : ℤ))),
      Tendsto (fun m => fm m x) atTop (𝓝 (flim x)) :=
    (e0e_normalizedCube_ac _).ae_le (hae.mono (fun x hx => hflim x hx))
  have hmeas : AEStronglyMeasurable flim (normalizedCubeMeasure (originCube d (k : ℤ))) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun m => (hmem m k).aestronglyMeasurable) hacs
  have htail : ∀ m : ℕ, eLpNorm (fun x => flim x - fm m x) 2
      (normalizedCubeMeasure (originCube d (k : ℤ))) ≤
      ENNReal.ofReal (∑' i, cubeL2 k (fun x => fm (m + i + 1) x - fm (m + i) x)) := by
    intro m
    rw [← e0e_tail_tsum hmem hsum k m]
    refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
      (f := fun n x => fm (m + n) x - fm m x) (g := fun x => flim x - fm m x) ?_
      (fun n => ((hmem (m + n) k).sub (hmem m k)).aestronglyMeasurable)
      (hmeas.sub (hmem m k).aestronglyMeasurable) ?_
    · refine Filter.Eventually.of_forall fun n => ?_
      have hfun : (fun x => fm (m + n) x - fm m x) =
          ∑ i ∈ Finset.range n, fun x => fm (m + i + 1) x - fm (m + i) x := by
        funext x
        rw [Finset.sum_apply]
        exact (Finset.sum_range_sub (fun i => fm (m + i) x) n).symm
      rw [hfun]
      refine (eLpNorm_sum_le (by norm_num)).trans ?_
      exact ENNReal.sum_le_tsum _
    · filter_upwards [hacs] with x hx
      have h5 : Tendsto (fun n => fm (m + n) x) atTop (𝓝 (flim x)) :=
        hx.comp (tendsto_atTop_mono (fun n => Nat.le_add_left n m) tendsto_id)
      exact h5.sub_const _
  have hmemf : MemLp flim 2 (normalizedCubeMeasure (originCube d (k : ℤ))) := by
    have h0 : MemLp (fun x => flim x - fm 0 x) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) := by
      exact lt_of_le_of_lt (htail 0) ENNReal.ofReal_lt_top
    have h1 := h0.add (hmem 0 k)
    have h2 : (fun x => flim x - fm 0 x) + fm 0 = flim := by funext x; simp
    rwa [h2] at h1
  have hreal : ∀ m : ℕ, cubeL2 k (fun x => flim x - fm m x) ≤
      ∑' i, cubeL2 k (fun x => fm (m + i + 1) x - fm (m + i) x) := by
    intro m
    have hnn : 0 ≤ ∑' i, cubeL2 k (fun x => fm (m + i + 1) x - fm (m + i) x) :=
      tsum_nonneg fun i => ENNReal.toReal_nonneg
    unfold cubeL2 cubeLpNorm
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (htail m)
    rwa [ENNReal.toReal_ofReal hnn] at this
  refine ⟨hmemf, ?_, hreal⟩
  have hsw : ∀ m : ℕ, cubeL2 k (fun x => fm m x - flim x) = cubeL2 k (fun x => flim x - fm m x) := by
    intro m
    unfold cubeL2 cubeLpNorm
    rw [← eLpNorm_neg]
    congr 2
    funext x
    simp
  simp_rw [hsw]
  refine squeeze_zero (fun m => ENNReal.toReal_nonneg) hreal ?_
  have := tendsto_sum_nat_add (fun i => cubeL2 k (fun x => fm (i + 1) x - fm i x))
  refine this.congr (fun m => ?_)
  refine tsum_congr fun i => ?_
  rw [add_comm i m]

/-- Witness: a constant sequence has zero increments, and the theorem applies to it. -/
example [NeZero d] (c : Vec d → ℝ) (hc : ∀ k : ℕ,
    MemLp c 2 (normalizedCubeMeasure (originCube d (k : ℤ)))) :
    ∃ f : Vec d → ℝ, (∀ᵐ x ∂volume, Filter.Tendsto (fun _ : ℕ => c x) Filter.atTop (nhds (f x))) ∧
      ∀ k : ℕ, MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ))) := by
  obtain ⟨f, h1, h2⟩ := exists_limit_of_summable_cubeL2 (fm := fun _ => c)
    (fun _ k => hc k) (fun k => by simp [cubeL2, cubeLpNorm])
  exact ⟨f, h1, fun k => (h2 k).1⟩

end SuperdiffusionCLT.Section6
