/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.SmoothingD
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform
public import SuperdiffusionCLT.Section7.Prereq.LinftyReduction
public import SuperdiffusionCLT.Section7.Prereq.L2AssemblyE

/-!
# The `L^∞` homogenization proposition: the datum

* `linf_global_lipschitz`: on a dilate of a smooth bounded domain, an `H¹` function with bounded
  gradient has a representative extending to a globally Lipschitz function, with a constant
  independent of the dilation factor.
* `linf_datum`: the smooth datum with bounds on the whole space.

The constant is independent of the dilation factor because a chain of overlapping pieces of
bounded length joins any two points of the (connected) domain at scale one.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

/-- `linf_Reach U ρ k x y`: `y` is reached from `x` by at most `k` steps of length `< ρ`, all
inside `U`. -/
def linf_Reach (U : Set (Vec d)) (ρ : ℝ) : ℕ → Vec d → Vec d → Prop
  | 0, x, y => x = y
  | k + 1, x, y => linf_Reach U ρ k x y ∨
      ∃ z ∈ U, linf_Reach U ρ k x z ∧ ‖z - y‖ < ρ ∧ y ∈ U

theorem linf_reach_mono_succ {U : Set (Vec d)} {ρ : ℝ} {k : ℕ} {x y : Vec d}
    (h : linf_Reach U ρ k x y) : linf_Reach U ρ (k + 1) x y := Or.inl h

theorem linf_reach_mono {U : Set (Vec d)} {ρ : ℝ} {k m : ℕ} (hkm : k ≤ m) {x y : Vec d}
    (h : linf_Reach U ρ k x y) : linf_Reach U ρ m x y := by
  induction m, hkm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact linf_reach_mono_succ ih

theorem linf_reach_trans {U : Set (Vec d)} {ρ : ℝ} {k : ℕ} {x y : Vec d}
    (h : linf_Reach U ρ k x y) (m : ℕ) : ∀ {z : Vec d}, linf_Reach U ρ m y z →
      linf_Reach U ρ (k + m) x z := by
  induction m with
  | zero =>
    intro z hz
    have : y = z := hz
    subst this
    exact h
  | succ m ih =>
    intro z hz
    rcases hz with hz | ⟨w, hw, h1, h2, hzU⟩
    · exact linf_reach_mono_succ (ih hz)
    · exact Or.inr ⟨w, hw, ih h1, h2, hzU⟩

theorem linf_reach_one {U : Set (Vec d)} {ρ : ℝ} {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U)
    (h : ‖x - y‖ < ρ) : linf_Reach U ρ 1 x y :=
  Or.inr ⟨x, hx, rfl, h, hy⟩

/-- Connectedness: any two points of a preconnected set are joined by a finite chain. -/
theorem linf_reach_exists {U : Set (Vec d)} {ρ : ℝ} (hρ : 0 < ρ) (hc : IsPreconnected U)
    {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) : ∃ k, linf_Reach U ρ k x y := by
  by_contra hno
  push Not at hno
  set S : Set (Vec d) := {z | z ∈ U ∧ ∃ k, linf_Reach U ρ k x z} with hS
  set T : Set (Vec d) := {z | z ∈ U ∧ ∀ k, ¬ linf_Reach U ρ k x z} with hT
  have hu : IsOpen (⋃ a ∈ S, Metric.ball a ρ) := isOpen_biUnion fun _ _ => Metric.isOpen_ball
  have hv : IsOpen (⋃ a ∈ T, Metric.ball a ρ) := isOpen_biUnion fun _ _ => Metric.isOpen_ball
  have hcov : U ⊆ (⋃ a ∈ S, Metric.ball a ρ) ∪ ⋃ a ∈ T, Metric.ball a ρ := by
    intro z hz
    by_cases hzS : ∃ k, linf_Reach U ρ k x z
    · exact Or.inl (Set.mem_biUnion (x := z) ⟨hz, hzS⟩ (Metric.mem_ball_self hρ))
    · push Not at hzS
      exact Or.inr (Set.mem_biUnion (x := z) ⟨hz, hzS⟩ (Metric.mem_ball_self hρ))
  have hxu : (U ∩ ⋃ a ∈ S, Metric.ball a ρ).Nonempty :=
    ⟨x, hx, Set.mem_biUnion (x := x) ⟨hx, 0, rfl⟩ (Metric.mem_ball_self hρ)⟩
  have hyv : (U ∩ ⋃ a ∈ T, Metric.ball a ρ).Nonempty :=
    ⟨y, hy, Set.mem_biUnion (x := y) ⟨hy, hno⟩ (Metric.mem_ball_self hρ)⟩
  obtain ⟨q, hqU, hqu, hqv⟩ := hc _ _ hu hv hcov hxu hyv
  obtain ⟨a, ⟨haU, k, hk⟩, hqa⟩ := Set.mem_iUnion₂.1 hqu
  obtain ⟨b, ⟨hbU, hb⟩, hqb⟩ := Set.mem_iUnion₂.1 hqv
  have h1 : linf_Reach U ρ (k + 1) x q :=
    Or.inr ⟨a, haU, hk, by rw [← dist_eq_norm, dist_comm]; exact Metric.mem_ball.1 hqa, hqU⟩
  have h2 : linf_Reach U ρ (k + 1 + 1) x b :=
    Or.inr ⟨q, hqU, h1, by rw [← dist_eq_norm]; exact Metric.mem_ball.1 hqb, hbU⟩
  exact hb _ h2

/-- A uniform bound on the length of chains in a bounded connected set. -/
theorem linf_reach_bound {U : Set (Vec d)} {ρ : ℝ} (hρ : 0 < ρ) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) :
    ∃ N : ℕ, ∀ x ∈ U, ∀ y ∈ U, linf_Reach U ρ N x y := by
  obtain ⟨T, hTU, hTf, hcov⟩ := (Metric.finite_approx_of_totallyBounded
    (hb.isCompact_closure.totallyBounded.subset subset_closure)) ρ hρ
  have hk : ∀ a ∈ U, ∀ b ∈ U, ∃ k, linf_Reach U ρ k a b :=
    fun a ha b hb' => linf_reach_exists hρ hc ha hb'
  choose! K hK using hk
  set N0 : ℕ := (hTf.toFinset ×ˢ hTf.toFinset).sup (fun p => K p.1 p.2) with hN0
  refine ⟨1 + N0 + 1, fun x hx y hy => ?_⟩
  obtain ⟨c, hcT, hxc⟩ := Set.mem_iUnion₂.1 (hcov hx)
  obtain ⟨c', hcT', hyc⟩ := Set.mem_iUnion₂.1 (hcov hy)
  have h1 : linf_Reach U ρ 1 x c :=
    linf_reach_one hx (hTU hcT) (by rw [← dist_eq_norm]; exact Metric.mem_ball.1 hxc)
  have hle : K c c' ≤ N0 :=
    Finset.le_sup (f := fun p : Vec d × Vec d => K p.1 p.2) (b := (c, c'))
      (Finset.mem_product.2 ⟨hTf.mem_toFinset.2 hcT, hTf.mem_toFinset.2 hcT'⟩)
  have h2 : linf_Reach U ρ N0 c c' := linf_reach_mono hle (hK c (hTU hcT) c' (hTU hcT'))
  have h3 : linf_Reach U ρ 1 c' y :=
    linf_reach_one (hTU hcT') hy (by rw [← dist_eq_norm, dist_comm]; exact Metric.mem_ball.1 hyc)
  exact linf_reach_trans (linf_reach_trans h1 N0 h2) 1 h3

theorem linf_isBounded_of_isBoundedDomain {U : Set (Vec d)} (hU : IsBoundedDomain U) :
    Bornology.IsBounded U := by
  obtain ⟨R, hR0, hR⟩ := hU
  refine (Metric.isBounded_closedBall (x := (0 : Vec d)) (r := R)).subset fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg hR0.le).2 fun i => by simpa using hR y hy i

theorem linf_sup_le_eucNorm_eLpNorm {V : Set (Vec d)} (g : H1Function V) :
    eLpNorm (fun x => ‖g.grad x‖) ⊤ (volume.restrict V) ≤
      eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict V) := by
  have hmeas : AEStronglyMeasurable (fun x => ‖g.grad x‖) (volume.restrict V) :=
    (aemeasurable_pi_iff.2 fun i =>
      (g.gradMemL2 i).aestronglyMeasurable.aemeasurable).norm.aestronglyMeasurable
  refine eLpNorm_mono hmeas fun x => ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact (l2d_norm_le_eucNorm _).trans (le_abs_self _)

/-- **Global Lipschitz representative**: on a dilate of a smooth bounded
(connected) domain, an `H¹` function with bounded gradient has a representative that extends to a
Lipschitz function on the whole space, with constant `C(U) ‖∇g‖_∞`. -/
theorem linf_global_lipschitz {U : Set (Vec d)} (hU : IsSmoothBoundedDomain U) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ g : H1Function (t • U),
      eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (t • U)) < ⊤ →
      ∃ g' : Vec d → ℝ, g' =ᵐ[volume.restrict (t • U)] g.toFun ∧
        ∀ x y : Vec d, |g' x - g' y| ≤
          C * (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (t • U))).toReal *
            ‖x - y‖ := by
  obtain ⟨r, M₁, M₂, D, hUC⟩ := exists_isUniformC11Domain_of_isSmoothBoundedDomain hU
  obtain ⟨C0, hC0, hloc⟩ := exists_localLipschitz_representative d M₁
  have hr : 0 < r := hUC.2.1
  set ρ : ℝ := r / C0 with hρdef
  have hρ : 0 < ρ := div_pos hr hC0
  obtain ⟨N, hN⟩ := linf_reach_bound hρ hU.2.1.isPreconnected
    (linf_isBounded_of_isBoundedDomain hU.2.2.1)
  refine ⟨max 1 (C0 * ((N : ℝ) + 1)), le_max_left _ _, fun t ht g hg => ?_⟩
  have hUt := hUC.smul ht
  have hgs : eLpNorm (fun x => ‖g.grad x‖) ⊤ (volume.restrict (t • U)) < ⊤ :=
    lt_of_le_of_lt (linf_sup_le_eucNorm_eLpNorm g) hg
  obtain ⟨g', hae, hl⟩ := hloc hUt g hgs
  set G : ℝ := (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (t • U))).toReal
    with hG
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hGs : (eLpNorm (fun x => ‖g.grad x‖) ⊤ (volume.restrict (t • U))).toReal ≤ G :=
    ENNReal.toReal_mono hg.ne (linf_sup_le_eucNorm_eLpNorm g)
  have hGs0 : 0 ≤ (eLpNorm (fun x => ‖g.grad x‖) ⊤ (volume.restrict (t • U))).toReal :=
    ENNReal.toReal_nonneg
  have htr : t * r / C0 = t * ρ := by rw [hρdef]; ring
  have hpiece : ∀ x y z : Vec d, y ∈ t • U → z ∈ t • U → y ∈ Metric.ball x (t * r / C0) →
      z ∈ Metric.ball x (t * r / C0) → |g' y - g' z| ≤ C0 * G * ‖y - z‖ := by
    intro x y z hy hz hyb hzb
    have h := (hl x).dist_le_mul y ⟨hy, hyb⟩ z ⟨hz, hzb⟩
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left hGs hC0.le
  have hc0 : 0 ≤ C0 * G * (t * ρ) := by positivity
  have hch : ∀ k : ℕ, ∀ x y : Vec d, x ∈ U → y ∈ U → linf_Reach U ρ k x y →
      |g' (t • x) - g' (t • y)| ≤ k * (C0 * G * (t * ρ)) := by
    intro k
    induction k with
    | zero =>
      intro x y _ _ h
      have : x = y := h
      subst this
      simp
    | succ k ih =>
      intro x y hx hy h
      rcases h with h | ⟨z, hz, h1, h2, -⟩
      · refine (ih x y hx hy h).trans ?_
        push_cast
        nlinarith only [hc0, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      · have e1 := ih x z hx hz h1
        have hmz : t • z ∈ t • U := Set.smul_mem_smul_set hz
        have hmy : t • y ∈ t • U := Set.smul_mem_smul_set hy
        have hball : t • z ∈ Metric.ball (t • y) (t * r / C0) := by
          rw [Metric.mem_ball, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg ht.le,
            htr]
          exact mul_lt_mul_of_pos_left h2 ht
        have e2 : |g' (t • z) - g' (t • y)| ≤ C0 * G * (t * ρ) := by
          refine (hpiece (t • y) _ _ hmz hmy hball (Metric.mem_ball_self (by positivity))).trans ?_
          rw [← smul_sub, norm_smul, Real.norm_of_nonneg ht.le]
          have : t * ‖z - y‖ ≤ t * ρ := mul_le_mul_of_nonneg_left h2.le ht.le
          exact mul_le_mul_of_nonneg_left this (by positivity)
        calc |g' (t • x) - g' (t • y)|
            = |(g' (t • x) - g' (t • z)) + (g' (t • z) - g' (t • y))| := by ring_nf
          _ ≤ |g' (t • x) - g' (t • z)| + |g' (t • z) - g' (t • y)| := abs_add_le _ _
          _ ≤ k * (C0 * G * (t * ρ)) + C0 * G * (t * ρ) := add_le_add e1 e2
          _ = ((k + 1 : ℕ) : ℝ) * (C0 * G * (t * ρ)) := by push_cast; ring
  set C : ℝ := max 1 (C0 * ((N : ℝ) + 1)) with hCdef
  have hCge : C0 * ((N : ℝ) + 1) ≤ C := le_max_right _ _
  have hlipOn : LipschitzOnWith (Real.toNNReal (C * G)) g' (t • U) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity [hCdef])]
    have hCG : C0 * ((N : ℝ) + 1) * G ≤ C * G := mul_le_mul_of_nonneg_right hCge hG0
    by_cases hnear : ‖x - y‖ < t * ρ
    · have hxb : x ∈ Metric.ball x (t * r / C0) := Metric.mem_ball_self (by rw [htr]; positivity)
      have hyb : y ∈ Metric.ball x (t * r / C0) := by
        rw [Metric.mem_ball, dist_comm, dist_eq_norm, htr]; exact hnear
      refine (hpiece x x y hx hy hxb hyb).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have : C0 * G ≤ C0 * ((N : ℝ) + 1) * G :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hC0, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]) hG0
      linarith only [this, hCG]
    · push Not at hnear
      obtain ⟨x0, hx0, rfl⟩ := Set.mem_smul_set.1 hx
      obtain ⟨y0, hy0, rfl⟩ := Set.mem_smul_set.1 hy
      have h1 := hch N x0 y0 hx0 hy0 (hN x0 hx0 y0 hy0)
      refine h1.trans ?_
      have h2 : (N : ℝ) * (C0 * G * (t * ρ)) ≤ (N : ℝ) * (C0 * G * ‖t • x0 - t • y0‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnear (by positivity))
          (Nat.cast_nonneg N)
      have h3 : (N : ℝ) * (C0 * G) ≤ C * G := by
        have : (N : ℝ) * (C0 * G) ≤ C0 * ((N : ℝ) + 1) * G := by
          nlinarith only [mul_nonneg hC0.le hG0]
        linarith only [this, hCG]
      refine h2.trans ?_
      calc (N : ℝ) * (C0 * G * ‖t • x0 - t • y0‖)
          = ((N : ℝ) * (C0 * G)) * ‖t • x0 - t • y0‖ := by ring
        _ ≤ (C * G) * ‖t • x0 - t • y0‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
  obtain ⟨ge, hge, heq⟩ := hlipOn.extend_real
  refine ⟨ge, ?_, fun x y => ?_⟩
  · filter_upwards [hae, ae_restrict_mem hUt.1.measurableSet] with x hx hxm
    rw [← hx]
    exact (heq hxm).symm
  · have := hge.dist_le_mul x y
    rwa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity [hCdef])] at this

end SuperdiffusionCLT.Section7
