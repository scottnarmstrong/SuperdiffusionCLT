/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliD
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryD
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit

/-!
# Geometry of the grid cubes cut by a domain

The grid is the set of descendants of the origin cube at a fixed depth.  A grid cube is *good* when
it lies in the support zone of the cutoff (`|shift| + 3/2 ℓ ≤ a`) and inside the open set `W`.
The part of the support zone not covered by good cubes lies in a slab at the edge of the cutoff
support together with the boundary layer of `W`.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ca2_mem_cubeSet_iff (R : TriadicCube d) (x : Vec d) :
    x ∈ cubeSet R ↔ ∀ k, triadicCubeShift R k - cubeScaleFactor R / 2 ≤ x k ∧
      x k < triadicCubeShift R k + cubeScaleFactor R / 2 := by
  rw [cubeSet_eq_pi_Ico]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico, triadicCubeShift]
  refine forall_congr' fun k => ?_
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]
  · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]

theorem ca2_abs_sub_le_of_mem_cubeSet (R : TriadicCube d) {x : Vec d} (hx : x ∈ cubeSet R) (k : Fin d) :
    |x k - triadicCubeShift R k| ≤ cubeScaleFactor R / 2 := by
  have h := (ca2_mem_cubeSet_iff R x).1 hx k
  rw [abs_le]; constructor <;> linarith only [h.1, h.2]

theorem ca2_abs_sub_lt_of_mem_cubeSet (R : TriadicCube d) {x y : Vec d} (hx : x ∈ cubeSet R)
    (hy : y ∈ cubeSet R) (k : Fin d) : |x k - y k| < cubeScaleFactor R := by
  have h := (ca2_mem_cubeSet_iff R x).1 hx k
  have h' := (ca2_mem_cubeSet_iff R y).1 hy k
  rw [abs_lt]; constructor <;> linarith only [h.1, h.2, h'.1, h'.2]

theorem ca2_openCubeSet_subset_cubeSet (R : TriadicCube d) : openCubeSet R ⊆ cubeSet R :=
  openCubeSet_subset_cubeSet R

/-- The cutoff support zone: the open sup-norm ball. -/
theorem ca2_mem_ball_iff {a : ℝ} (ha : 0 < a) (x : Vec d) :
    x ∈ Metric.ball (0 : Vec d) a ↔ ∀ k, |x k| < a := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff ha]
  simp only [Real.norm_eq_abs]

theorem ca2_pow_sub_pow_le {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (n : ℕ) :
    x ^ (n + 1) - y ^ (n + 1) ≤ (n + 1) * (x - y) * x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx : 0 ≤ x := hy.trans hxy
    have h1 : x ^ (n + 1 + 1) - y ^ (n + 1 + 1) = x * (x ^ (n + 1) - y ^ (n + 1)) + y ^ (n + 1) * (x - y) := by
      ring
    have h2 : y ^ (n + 1) ≤ x ^ (n + 1) := pow_le_pow_left₀ hy hxy _
    have h3 : x * (x ^ (n + 1) - y ^ (n + 1)) ≤ x * ((n + 1) * (x - y) * x ^ n) :=
      mul_le_mul_of_nonneg_left ih hx
    have h4 : y ^ (n + 1) * (x - y) ≤ x ^ (n + 1) * (x - y) :=
      mul_le_mul_of_nonneg_right h2 (by linarith only [hxy])
    have e : x * ((n + 1) * (x - y) * x ^ n) + x ^ (n + 1) * (x - y) =
        ((n + 1 : ℕ) + 1) * (x - y) * x ^ (n + 1) := by push_cast; ring
    push_cast at e ⊢
    linarith only [h1, h3, h4, e]

/-- The slab at the edge of the cutoff support has small measure. -/
theorem ca2_vol_slab [NeZero d] {a ℓ : ℝ} (hℓ : 0 < ℓ) (ha : 2 * ℓ < a) :
    volume (Metric.closedBall (0 : Vec d) (a + ℓ) \ Metric.ball (0 : Vec d) (a - 2 * ℓ)) ≤
      ENNReal.ofReal (3 * d * ℓ * 2 ^ d * (a + ℓ) ^ (d - 1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  have hy : 0 < a - 2 * ℓ := by linarith only [ha]
  have hsub : Metric.ball (0 : Vec (n + 1)) (a - 2 * ℓ) ⊆ Metric.closedBall 0 (a + ℓ) :=
    (Metric.ball_subset_closedBall).trans (Metric.closedBall_subset_closedBall (by linarith only [hℓ]))
  have hfin : volume (Metric.ball (0 : Vec (n + 1)) (a - 2 * ℓ)) ≠ ⊤ :=
    (Metric.isBounded_ball.measure_lt_top).ne
  rw [measure_sdiff hsub Metric.isOpen_ball.measurableSet.nullMeasurableSet hfin]
  rw [Real.volume_pi_closedBall _ (by linarith only [hℓ, ha]), Real.volume_pi_ball _ hy]
  simp only [Fintype.card_fin]
  rw [← ENNReal.ofReal_sub _ (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := ca2_pow_sub_pow_le (x := 2 * (a + ℓ)) (y := 2 * (a - 2 * ℓ)) (by positivity)
    (by linarith only [hℓ]) n
  simp only [Nat.succ_sub_one]
  have e : (((n + 1 : ℕ) : ℝ) * (2 * (a + ℓ) - 2 * (a - 2 * ℓ)) * (2 * (a + ℓ)) ^ n) =
      3 * ((n.succ : ℕ) : ℝ) * ℓ * 2 ^ n.succ * (a + ℓ) ^ n := by
    push_cast; rw [mul_pow, Nat.succ_eq_add_one, pow_succ]; ring
  push_cast at e h ⊢
  linarith only [h, e]

/-- A grid cube is *good* when it lies in the support zone of the cutoff and inside `W`. -/
def ca2_good (a : ℝ) (W : Set (Vec d)) (R : TriadicCube d) : Prop :=
  (∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a) ∧ openCubeSet R ⊆ W

theorem ca2_convex_cubeSet (R : TriadicCube d) : Convex ℝ (cubeSet R) := by
  rw [cubeSet_eq_pi_Ico]
  exact convex_pi fun i _ => convex_Ico _ _

theorem ca2_layer_of_not_subset {W : Set (Vec d)} {R : TriadicCube d} (hWo : IsOpen W) {x : Vec d}
    (hx : x ∈ cubeSet R) (hxW : x ∈ W) (hR : ¬ openCubeSet R ⊆ W) :
    x ∈ boundaryLayer W (cubeScaleFactor R) := by
  rw [Set.not_subset] at hR
  obtain ⟨y, hyR, hyW⟩ := hR
  have hs : IsPreconnected (cubeSet R) := (ca2_convex_cubeSet R).isPreconnected
  have hyc : y ∈ cubeSet R := ca2_openCubeSet_subset_cubeSet R hyR
  obtain ⟨p, hp, hpF⟩ : ∃ p ∈ cubeSet R, p ∈ frontier W := by
    by_contra hcon
    push Not at hcon
    have hcov : cubeSet R ⊆ W ∪ (closure W)ᶜ := by
      intro z hz
      by_cases hzW : z ∈ W
      · exact Or.inl hzW
      · right
        intro hzc
        refine hcon z hz ?_
        rw [frontier, hWo.interior_eq]
        exact ⟨hzc, hzW⟩
    obtain ⟨q, -, hqW, hqc⟩ := hs W (closure W)ᶜ hWo isClosed_closure.isOpen_compl hcov ⟨x, hx, hxW⟩
      ⟨y, hyc, fun hyc' => hcon y hyc (by rw [frontier, hWo.interior_eq]; exact ⟨hyc', hyW⟩)⟩
    exact hqc (subset_closure hqW)
  refine ⟨hxW, ?_⟩
  have hℓ : 0 < cubeScaleFactor R := by simp [cubeScaleFactor]; positivity
  have hd : dist x p < cubeScaleFactor R := by
    rw [dist_eq_norm, pi_norm_lt_iff hℓ]
    intro k
    rw [Real.norm_eq_abs]
    exact ca2_abs_sub_lt_of_mem_cubeSet R hx hp k
  exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hpF) hd

/-- The part of the support zone not covered by good grid cubes lies in a slab at the edge of the
support together with the boundary layer of `W`. -/
theorem ca2_uncovered_subset (m : ℤ) (h : ℕ) {W : Set (Vec d)} (hWo : IsOpen W) {a ℓ : ℝ}
    (ha : 0 < a) (hℓa : 2 * ℓ < a)
    (hℓ : ∀ R ∈ descendantsAtDepth (originCube d m) h, cubeScaleFactor R = ℓ)
    {x : Vec d} (hxQ : x ∈ openCubeSet (originCube d m)) (hxW : x ∈ W)
    (hxa : x ∈ Metric.ball (0 : Vec d) a)
    (hx𝒢 : ∀ R ∈ descendantsAtDepth (originCube d m) h, ca2_good a W R → x ∉ cubeSet R) :
    x ∈ (Metric.closedBall (0 : Vec d) (a + ℓ) \ Metric.ball (0 : Vec d) (a - 2 * ℓ)) ∪
      boundaryLayer W ℓ := by
  obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet h
    (openCubeSet_subset_cubeSet _ hxQ)
  have hRℓ := hℓ R hR
  have hng : ¬ ca2_good a W R := fun hg => hx𝒢 R hR hg hxR
  unfold ca2_good at hng
  rw [not_and_or] at hng
  rcases hng with hint | hsub
  · left
    push Not at hint
    obtain ⟨k, hk⟩ := hint
    have h1 := ca2_abs_sub_le_of_mem_cubeSet R hxR k
    have h2 := abs_sub_abs_le_abs_sub (triadicCubeShift R k) (x k)
    rw [abs_sub_comm] at h2
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hb := (ca2_mem_ball_iff ha x).1 hxa
      refine (pi_norm_le_iff_of_nonneg (by linarith only [ha, (show 0 ≤ ℓ from by
        rw [← hRℓ]; simp [cubeScaleFactor]; positivity)])).2 fun j => ?_
      rw [Real.norm_eq_abs]
      have := (hb j).le
      have hℓ0 : 0 ≤ ℓ := by rw [← hRℓ]; simp [cubeScaleFactor]; positivity
      linarith only [this, hℓ0]
    · intro hmem
      have hℓ0 : 0 < ℓ := by rw [← hRℓ]; simp [cubeScaleFactor]; positivity
      rw [ca2_mem_ball_iff (by linarith only [hℓa])] at hmem
      have := hmem k
      rw [hRℓ] at hk h1
      rw [abs_lt] at this
      have h3 := abs_nonneg (x k)
      have h4 : |triadicCubeShift R k| - ℓ / 2 ≤ |x k| := by
        have := abs_sub_abs_le_abs_sub (triadicCubeShift R k) (x k)
        rw [abs_sub_comm] at this
        linarith only [this, h1]
      rcases abs_cases (x k) with ⟨h5, _⟩ | ⟨h5, _⟩ <;> linarith only [this.1, this.2, hk, h4, h5]
  · right
    rw [← hRℓ]
    exact ca2_layer_of_not_subset hWo hxR hxW hsub

open Classical in
/-- The good grid cubes. -/
noncomputable def ca2_Zi (m : ℤ) (h : ℕ) (a : ℝ) (W : Set (Vec d)) : Finset (TriadicCube d) :=
  (descendantsAtDepth (originCube d m) h).filter (ca2_good a W)

/-- The part of the support zone inside the domain that is not covered by good grid cubes. -/
def ca2_Bset (m : ℤ) (h : ℕ) (a : ℝ) (W : Set (Vec d)) : Set (Vec d) :=
  {x | x ∈ openCubeSet (originCube d m) ∩ W ∧ x ∈ Metric.ball (0 : Vec d) a ∧
    ∀ R ∈ ca2_Zi m h a W, x ∉ cubeSet R}

theorem ca2_Bset_measurable (m : ℤ) (h : ℕ) (a : ℝ) {W : Set (Vec d)} (hWo : IsOpen W) :
    MeasurableSet (ca2_Bset m h a W) := by
  have h1 : ca2_Bset m h a W = ((openCubeSet (originCube d m) ∩ W) ∩ Metric.ball (0 : Vec d) a) \
      ⋃ R ∈ ca2_Zi m h a W, cubeSet R := by
    ext x
    simp only [ca2_Bset, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_iUnion,
      exists_prop, not_exists, not_and]
    tauto
  rw [h1]
  refine MeasurableSet.diff ?_ (Finset.measurableSet_biUnion _ fun R _ => measurableSet_cubeSet R)
  exact (((isOpen_openCubeSet _).inter hWo).inter Metric.isOpen_ball).measurableSet

theorem ca2_vol_Bset [NeZero d] (m : ℤ) (h : ℕ) {W : Set (Vec d)} (hWo : IsOpen W) {a ℓ : ℝ}
    (ha : 0 < a) (hℓa : 2 * ℓ < a)
    (hℓ : ∀ R ∈ descendantsAtDepth (originCube d m) h, cubeScaleFactor R = ℓ) {Lb : ℝ}
    (hlayer : volume (boundaryLayer W ℓ ∩ openCubeSet (originCube d m)) ≤ ENNReal.ofReal Lb)
    (hℓ0 : 0 < ℓ) (hLb : 0 ≤ Lb) :
    volume (ca2_Bset m h a W) ≤
      ENNReal.ofReal (3 * d * ℓ * 2 ^ d * (a + ℓ) ^ (d - 1) + Lb) := by
  classical
  have hsub : ca2_Bset m h a W ⊆
      (Metric.closedBall (0 : Vec d) (a + ℓ) \ Metric.ball (0 : Vec d) (a - 2 * ℓ)) ∪
        (boundaryLayer W ℓ ∩ openCubeSet (originCube d m)) := by
    intro x hx
    obtain ⟨⟨hxQ, hxW⟩, hxa, hx𝒢⟩ := hx
    have := ca2_uncovered_subset m h hWo ha hℓa hℓ hxQ hxW hxa (fun R hR hg hxR =>
      hx𝒢 R (by unfold ca2_Zi; exact Finset.mem_filter.2 ⟨hR, hg⟩) hxR)
    rcases this with h1 | h2
    · exact Or.inl h1
    · exact Or.inr ⟨h2, hxQ⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [ENNReal.ofReal_add (by positivity) hLb]
  exact add_le_add (ca2_vol_slab hℓ0 hℓa) hlayer

theorem ca2_good_subset_ball {a : ℝ} (ha : 0 < a) {W : Set (Vec d)} {R : TriadicCube d}
    (hg : ca2_good a W R) : openCubeSet R ⊆ Metric.ball (0 : Vec d) a := by
  intro x hx
  rw [ca2_mem_ball_iff ha]
  intro k
  have h1 := (ca1_mem_openCube_iff R x).1 hx k
  have hℓ : 0 < cubeScaleFactor R := by simp [cubeScaleFactor]; positivity
  have h2 := abs_sub_abs_le_abs_sub (x k) (triadicCubeShift R k)
  have h3 := hg.1 k
  linarith only [h1, h2, h3, hℓ]

/-- The integral over the domain splits into the good grid cubes and the uncovered part. -/
theorem ca2_integral_decomp (m : ℤ) (h : ℕ) {W : Set (Vec d)} (hWo : IsOpen W) {a : ℝ} (ha : 0 < a)
    {g : Vec d → ℝ} (hg : IntegrableOn g (openCubeSet (originCube d m) ∩ W) volume)
    (hg0 : ∀ x ∈ openCubeSet (originCube d m) ∩ W, x ∉ Metric.ball (0 : Vec d) a → g x = 0) :
    ∫ x in openCubeSet (originCube d m) ∩ W, g x =
      (∑ R ∈ ca2_Zi m h a W, ∫ x in openCubeSet R, g x) + ∫ x in ca2_Bset m h a W, g x := by
  classical
  set E : Set (Vec d) := openCubeSet (originCube d m) ∩ W with hE
  have hEm : MeasurableSet E := ((isOpen_openCubeSet _).inter hWo).measurableSet
  set Eb : Set (Vec d) := E ∩ Metric.ball (0 : Vec d) a with hEb
  have hEbm : MeasurableSet Eb := hEm.inter Metric.isOpen_ball.measurableSet
  set 𝒢 : Set (Vec d) := ⋃ R ∈ ca2_Zi m h a W, cubeSet R with h𝒢
  have h𝒢m : MeasurableSet 𝒢 := Finset.measurableSet_biUnion _ fun R _ => measurableSet_cubeSet R
  have step1 : ∫ x in E, g x = ∫ x in Eb, g x := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hEm Set.inter_subset_left fun x hx => ?_
    exact hg0 x hx.1 (fun hb => hx.2 ⟨hx.1, hb⟩)
  have hgEb : IntegrableOn g Eb volume := hg.mono_set Set.inter_subset_left
  have hdisj : Disjoint (Eb ∩ 𝒢) (ca2_Bset m h a W) := by
    rw [Set.disjoint_left]
    rintro x ⟨hx1, hx2⟩ hx3
    obtain ⟨R, hR, hxR⟩ := Set.mem_iUnion₂.1 hx2
    exact hx3.2.2 R hR hxR
  have hunion : Eb = (Eb ∩ 𝒢) ∪ ca2_Bset m h a W := by
    ext x
    constructor
    · intro hx
      by_cases hx𝒢 : x ∈ 𝒢
      · exact Or.inl ⟨hx, hx𝒢⟩
      · right
        refine ⟨hx.1, hx.2, fun R hR hxR => hx𝒢 (Set.mem_iUnion₂.2 ⟨R, hR, hxR⟩)⟩
    · rintro (⟨hx, -⟩ | hx)
      · exact hx
      · exact ⟨hx.1, hx.2.1⟩
  have hBm := ca2_Bset_measurable m h a hWo
  have step2 : ∫ x in Eb, g x = (∫ x in Eb ∩ 𝒢, g x) + ∫ x in ca2_Bset m h a W, g x := by
    have := setIntegral_union hdisj hBm (hgEb.mono_set Set.inter_subset_left)
      (hgEb.mono_set (fun x hx => ⟨hx.1, hx.2.1⟩))
    rwa [← hunion] at this
  have hcube : ∀ R ∈ ca2_Zi m h a W, openCubeSet R ⊆ Eb := by
    intro R hR
    have hg' : ca2_good a W R := (Finset.mem_filter.1 hR).2
    have hRd := (Finset.mem_filter.1 hR).1
    exact fun x hx => ⟨⟨openCubeSet_subset_of_mem_descendantsAtDepth hRd hx, hg'.2 hx⟩,
      ca2_good_subset_ball ha hg' hx⟩
  have step3 : ∫ x in Eb ∩ 𝒢, g x = ∑ R ∈ ca2_Zi m h a W, ∫ x in openCubeSet R, g x := by
    have hset : Eb ∩ 𝒢 = ⋃ R ∈ ca2_Zi m h a W, (Eb ∩ cubeSet R) := by
      ext x; simp only [h𝒢, Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hx, R, hR, hxR⟩; exact ⟨R, hR, hx, hxR⟩
      · rintro ⟨R, hR, hx, hxR⟩; exact ⟨hx, R, hR, hxR⟩
    rw [hset, integral_biUnion_finset _ (fun R _ => hEbm.inter (measurableSet_cubeSet R))]
    · refine Finset.sum_congr rfl fun R hR => ?_
      have hRd := (Finset.mem_filter.1 hR).1
      have e1 : volume.restrict (Eb ∩ cubeSet R) = volume.restrict (openCubeSet R) := by
        rw [← Measure.restrict_restrict hEbm, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
          Measure.restrict_restrict hEbm, Set.inter_eq_right.2 (hcube R hR)]
      simp only [MeasureTheory.integral, e1]
    · intro R hR R' hR' hne
      have h1 := (pairwiseDisjoint_descendantsAtDepth (originCube d m) h)
        (Finset.mem_filter.1 hR).1 (Finset.mem_filter.1 hR').1 (fun e => hne e)
      exact (h1.mono Set.inter_subset_right Set.inter_subset_right)
    · intro R hR
      exact hgEb.mono_set Set.inter_subset_left
  rw [step1, step2, step3]

end SuperdiffusionCLT.Section7
