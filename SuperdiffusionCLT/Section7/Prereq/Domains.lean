/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Homogenization.Geometry.ConvexDomain
public import Homogenization.Geometry.CubeMetric
public import SuperdiffusionCLT.Section6.Prereq.EuclidBall

/-!
# Bounded Lipschitz, `C^{1,1}` and smooth domains

A bounded domain is *graph-regular* of some regularity if near each boundary point it is the
region below the graph of a function over a hyperplane. This is the usual definition of a
Lipschitz, `C^{1,1}` or smooth boundary, with the graph direction chosen as an arbitrary unit
vector.

## Main definitions

* `Section7.IsGraphBoundedDomain reg U`: the common shape, parametrised by the regularity
  predicate `reg` on the graph function.
* `Section7.IsLipschitzBoundedDomain`, `Section7.IsC11BoundedDomain`,
  `Section7.IsSmoothBoundedDomain`: Lipschitz, `C^{1,1}` and `C^∞` graphs.

## Main results

* `Section7.isLipschitzBoundedDomain_ball`: every sup-norm ball is a bounded Lipschitz domain.
* `Section7.isLipschitzBoundedDomain_openCubeSet`: the open triadic cube is.
* `Section7.isSmoothBoundedDomain_euclidBall`: the open unit Euclidean ball is smooth.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- `U` is a bounded domain (open, connected, bounded) whose boundary is, near each of its
points, the graph over a hyperplane of a function of regularity `reg`: around each boundary
point `x` there are a unit vector `e`, a radius `r` and an open set `W` of base points, such that
on the (sup-norm) ball `B(x, r)` the projection `y - ⟨e, y⟩ e` lands in `W` and `U` is
`{⟨e, y⟩ < ψ(y - ⟨e, y⟩ e)}`, with `reg W ψ`. -/
def IsGraphBoundedDomain (reg : Set (Vec d) → (Vec d → ℝ) → Prop) (U : Set (Vec d)) : Prop :=
  IsOpen U ∧ IsConnected U ∧ IsBoundedDomain U ∧
    ∀ x ∈ frontier U, ∃ (e : Vec d) (ψ : Vec d → ℝ) (W : Set (Vec d)) (r : ℝ),
      vecNormSq e = 1 ∧ 0 < r ∧ IsOpen W ∧ reg W ψ ∧
      ∀ y ∈ Metric.ball x r, (y - vecDot e y • e) ∈ W ∧
        (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))

/-- Bounded Lipschitz domain: locally the region below a Lipschitz graph. -/
def IsLipschitzBoundedDomain (U : Set (Vec d)) : Prop :=
  IsGraphBoundedDomain (fun W ψ => ∃ K : NNReal, LipschitzOnWith K ψ W) U

/-- Bounded `C^{1,1}` domain: locally the region below a `C¹` graph with Lipschitz gradient. -/
def IsC11BoundedDomain (U : Set (Vec d)) : Prop :=
  IsGraphBoundedDomain
    (fun W ψ => ContDiffOn ℝ 1 ψ W ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ ψ) W) U

/-- Bounded smooth domain: locally the region below a `C^∞` graph. -/
def IsSmoothBoundedDomain (U : Set (Vec d)) : Prop :=
  IsGraphBoundedDomain (fun W ψ => ContDiffOn ℝ (⊤ : ℕ∞) ψ W) U

/-- The infimum of finitely many `K`-Lipschitz functions is `K`-Lipschitz. -/
theorem lipschitzWith_finset_inf' {α ι : Type*} [PseudoMetricSpace α] {K : NNReal}
    {S : Finset ι} (hS : S.Nonempty) {f : ι → α → ℝ} (hf : ∀ i, LipschitzWith K (f i)) :
    LipschitzWith K (fun a => S.inf' hS fun i => f i a) := by
  have key : ∀ a b : α, (S.inf' hS fun i => f i a) ≤ (S.inf' hS fun i => f i b) + K * dist a b := by
    intro a b
    obtain ⟨j, hj, hjb⟩ := Finset.exists_mem_eq_inf' hS fun i => f i b
    calc (S.inf' hS fun i => f i a) ≤ f j a := Finset.inf'_le _ hj
      _ ≤ f j b + K * dist a b := by
          have := (hf j).dist_le_mul a b
          rw [Real.dist_eq] at this
          linarith only [(abs_le.1 this).2]
      _ = _ := by rw [← hjb]
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, abs_le]
  constructor
  · have := key b a
    rw [dist_comm] at this
    linarith only [this]
  · have := key a b
    linarith only [this]

/-- Sign of `t`, with `sgn 0 = 1`. -/
noncomputable def sgn (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

theorem sgn_mul_self (t : ℝ) : sgn t * t = |t| := by
  unfold sgn
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [neg_one_mul, abs_of_neg (not_le.1 h), ]

theorem sgn_sq (t : ℝ) : sgn t * sgn t = 1 := by
  unfold sgn
  split_ifs <;> norm_num

/-- Data of a boundary point of a sup-norm ball: the binding faces. -/
theorem exists_binding_face [NeZero d] {c x : Vec d} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ Metric.sphere c ρ) : ∃ i, |x i - c i| = ρ := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ i, |x i - c i| ≤ ρ := fun i => by
    have := norm_le_pi_norm (x - c) i
    rw [Real.norm_eq_abs] at this
    have h2 : ‖x - c‖ = ρ := by rw [← dist_eq_norm]; exact hx
    simpa using this.trans h2.le
  have : ‖x - c‖ < ρ := by
    rw [pi_norm_lt_iff hρ]
    intro i
    rw [Real.norm_eq_abs]
    exact lt_of_le_of_ne (hle i) (hcon i)
  have h2 : ‖x - c‖ = ρ := by rw [← dist_eq_norm]; exact hx
  linarith only [this, h2]

/-- A sup-norm ball is a bounded Lipschitz domain. -/
theorem isLipschitzBoundedDomain_ball [NeZero d] (c : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    IsLipschitzBoundedDomain (Metric.ball c ρ) := by
  classical
  refine ⟨Metric.isOpen_ball, (convex_ball c ρ).isConnected ⟨c, Metric.mem_ball_self hρ⟩,
    Metric.isBounded_ball.isBoundedDomain, ?_⟩
  intro x hx
  have hxs : x ∈ Metric.sphere c ρ := by rwa [frontier_ball c hρ.ne'] at hx
  obtain ⟨i0, hi0⟩ := exists_binding_face hρ hxs
  have hxn : ‖x - c‖ = ρ := by rw [← dist_eq_norm]; exact hxs
  have hle : ∀ i, |x i - c i| ≤ ρ := fun i => by
    have := norm_le_pi_norm (x - c) i
    rw [Real.norm_eq_abs] at this
    simpa using this.trans hxn.le
  set S : Finset (Fin d) := Finset.univ.filter (fun i => |x i - c i| = ρ) with hSdef
  have hS : S.Nonempty := ⟨i0, by simp [hSdef, hi0]⟩
  have hmemS : ∀ i, i ∈ S ↔ |x i - c i| = ρ := fun i => by simp [hSdef]
  set σ : Fin d → ℝ := fun i => sgn (x i - c i) with hσ
  have hσx : ∀ i ∈ S, σ i * (x i - c i) = ρ := fun i hi => by
    rw [hσ]; dsimp only; rw [sgn_mul_self]; exact (hmemS i).1 hi
  have hσσ : ∀ i, σ i * σ i = 1 := fun i => sgn_sq _
  have hσabs : ∀ i, |σ i| = 1 := fun i => by
    have h3 : |σ i| * |σ i| = 1 := by rw [← abs_mul, hσσ i, abs_one]
    nlinarith only [h3, abs_nonneg (σ i)]
  have hn : (0 : ℝ) < S.card := Nat.cast_pos.2 hS.card_pos
  set s : ℝ := Real.sqrt S.card with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hn
  have hss : s * s = S.card := Real.mul_self_sqrt hn.le
  set e : Vec d := fun j => if j ∈ S then σ j / s else 0 with hedef
  have he : vecNormSq e = 1 := by
    unfold vecNormSq vecDot
    have : ∀ j, e j * e j = if j ∈ S then ((S.card : ℝ))⁻¹ else 0 := fun j => by
      by_cases hj : j ∈ S
      · simp only [hedef, hj, ↓reduceIte]
        field_simp
        linear_combination (-(σ j) ^ 2) * hss + s ^ 2 * hσσ j
      · simp [hedef, hj]
    simp only [this]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp [Finset.sum_const]
    field_simp
  set ψ : Vec d → ℝ := fun z => S.inf' hS (fun i => s * (σ i * (x i - z i))) with hψ
  have hψL : LipschitzWith s.toNNReal ψ := by
    refine lipschitzWith_finset_inf' hS (fun i => ?_)
    refine LipschitzWith.of_dist_le_mul fun z z' => ?_
    have h1 : |z' i - z i| ≤ dist z z' := by
      rw [dist_comm, dist_eq_norm]
      have := norm_le_pi_norm (z' - z) i
      simpa [Real.norm_eq_abs, dist_eq_norm] using this
    have h2 : |σ i| = 1 := hσabs i
    rw [Real.dist_eq, show s * (σ i * (x i - z i)) - s * (σ i * (x i - z' i))
      = s * σ i * (z' i - z i) by ring, abs_mul, abs_mul, abs_of_pos hs, h2, mul_one,
      Real.coe_toNNReal _ hs.le]
    exact mul_le_mul_of_nonneg_left h1 hs.le
  have hOopen : IsOpen (⋂ i ∈ (Sᶜ : Finset (Fin d)),
      {y : Vec d | |y i - c i| < ρ}) :=
    isOpen_biInter_finset fun i _ => isOpen_lt (by fun_prop) continuous_const
  have hxO : x ∈ ⋂ i ∈ (Sᶜ : Finset (Fin d)), {y : Vec d | |y i - c i| < ρ} := by
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Finset.mem_compl]
    intro i hi
    exact lt_of_le_of_ne (hle i) (fun h => hi ((hmemS i).2 h))
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hOopen x hxO
  refine ⟨e, ψ, Set.univ, min r ρ, he, lt_min hr hρ, isOpen_univ,
    ⟨s.toNNReal, hψL.lipschitzOnWith⟩, fun y hy => ⟨Set.mem_univ _, ?_⟩⟩
  have hyr : y ∈ Metric.ball x r := Metric.ball_subset_ball (min_le_left _ _) hy
  have hyρ : ∀ i, |y i - x i| < ρ := fun i => by
    have hy' : dist y x < ρ := lt_of_lt_of_le (Metric.mem_ball.1 hy) (min_le_right _ _)
    have := (dist_pi_lt_iff hρ).1 hy' i
    simpa [Real.dist_eq] using this
  have hyO : ∀ i ∉ S, |y i - c i| < ρ := fun i hi => by
    have := hrO hyr
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Finset.mem_compl] at this
    exact this i hi
  have hP : ∀ i ∈ S, σ i * ((y - vecDot e y • e) i) = σ i * y i - vecDot e y / s := by
    intro i hi
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hedef, hi, ↓reduceIte]
    field_simp
    linear_combination (-(vecDot e y)) * hσσ i
  have key : vecDot e y < ψ (y - vecDot e y • e) ↔ ∀ i ∈ S, σ i * y i < σ i * x i := by
    rw [hψ]
    dsimp only
    rw [Finset.lt_inf'_iff]
    refine forall₂_congr fun i hi => ?_
    have : s * (σ i * (x i - (y - vecDot e y • e) i)) =
        s * (σ i * x i - σ i * y i) + vecDot e y := by
      have h := hP i hi
      have : σ i * (x i - (y - vecDot e y • e) i) =
          σ i * x i - σ i * y i + vecDot e y / s := by
        rw [mul_sub, h]; ring
      rw [this]; field_simp
    rw [this]
    constructor
    · intro h
      have h1 : 0 < s * (σ i * x i - σ i * y i) := by linarith only [h]
      have h2 := (mul_pos_iff_of_pos_left hs).1 h1
      linarith only [h2]
    · intro h
      have h1 : 0 < s * (σ i * x i - σ i * y i) := mul_pos hs (by linarith only [h])
      linarith only [h1]
  rw [key, Metric.mem_ball, dist_pi_lt_iff hρ]
  have hdist : ∀ i, dist (y i) (c i) < ρ ↔ |y i - c i| < ρ := fun i => by rw [Real.dist_eq]
  constructor
  · intro h i hi
    have h1 := (hdist i).1 (h i)
    have h2 : σ i * (y i - c i) < ρ := by
      calc σ i * (y i - c i) ≤ |σ i * (y i - c i)| := le_abs_self _
        _ = |y i - c i| := by rw [abs_mul, hσabs, one_mul]
        _ < ρ := h1
    have h3 := hσx i hi
    linarith only [h2, h3]
  · intro h i
    rw [hdist]
    by_cases hi : i ∈ S
    · have h2 := h i hi
      have h3 := hσx i hi
      have h4 : |σ i * (y i - x i)| < ρ := by
        rw [abs_mul, hσabs, one_mul]; exact hyρ i
      have h5 := (abs_lt.1 h4).1
      have h6 : |σ i * (y i - c i)| < ρ := by
        rw [abs_lt]
        constructor
        · linarith only [h3, h5, hρ]
        · linarith only [h2, h3]
      rwa [abs_mul, hσabs, one_mul] at h6
    · exact hyO i hi

/-- The open triadic cube is a bounded Lipschitz domain. -/
theorem isLipschitzBoundedDomain_openCubeSet [NeZero d] (Q : TriadicCube d) :
    IsLipschitzBoundedDomain (openCubeSet Q) := by
  rw [← ball_cubeCenter_eq_openCubeSet]
  exact isLipschitzBoundedDomain_ball _ (cubeRadius_pos Q)

/-! ### The unit Euclidean ball is a smooth bounded domain -/

theorem vecNormSq_sub_proj {x : Vec d} (hx : vecNormSq x = 1) (w : Vec d) :
    vecNormSq (w - vecDot x w • x) = vecNormSq w - vecDot x w ^ 2 := by
  have h1 : ∀ i, (w - vecDot x w • x) i * (w - vecDot x w • x) i =
      w i * w i - 2 * vecDot x w * (x i * w i) + vecDot x w ^ 2 * (x i * x i) := fun i => by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold vecNormSq at hx ⊢
  have h2 : vecDot (w - vecDot x w • x) (w - vecDot x w • x) =
      ∑ i, (w i * w i - 2 * vecDot x w * (x i * w i) + vecDot x w ^ 2 * (x i * x i)) :=
    Finset.sum_congr rfl fun i _ => h1 i
  rw [h2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h3 : ∑ i, x i * w i = vecDot x w := rfl
  have h4 : ∑ i, x i * x i = 1 := hx
  rw [h3, h4]
  show _ = vecDot w w - vecDot x w ^ 2
  unfold vecDot
  ring

theorem convex_euclidBall (r : ℝ) : Convex ℝ (Section6.euclidBall (d := d) r) := by
  intro a ha b hb s t hs ht hst
  have hconv : ∀ i, (s * a i + t * b i) ^ 2 ≤ s * a i ^ 2 + t * b i ^ 2 := fun i => by
    have ht' : t = 1 - s := by linarith only [hst]
    subst ht'
    nlinarith only [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (a i - b i))]
  have hsum : vecNormSq (s • a + t • b) ≤ s * vecNormSq a + t * vecNormSq b := by
    unfold vecNormSq vecDot
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hconv i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith only [this]
  have ha' : vecNormSq a < r ^ 2 := ha
  have hb' : vecNormSq b < r ^ 2 := hb
  have hlt : s * vecNormSq a + t * vecNormSq b < r ^ 2 := by
    rcases hs.eq_or_lt with h0 | h0
    · have ht1 : t = 1 := by linarith only [hst, h0]
      rw [← h0, ht1]
      linarith only [hb']
    · have ht' : t = 1 - s := by linarith only [hst]
      subst ht'
      nlinarith only [mul_pos h0 (sub_pos.2 ha'), mul_nonneg ht (sub_nonneg.2 hb'.le)]
  exact lt_of_le_of_lt hsum hlt

theorem frontier_euclidBall_subset {x : Vec d} (hx : x ∈ frontier (Section6.euclidBall (d := d) 1)) :
    vecNormSq x = 1 := by
  rw [(Section6.isOpen_euclidBall (d := d) 1).frontier_eq] at hx
  have hcl : closure (Section6.euclidBall (d := d) 1) ⊆ {z | vecNormSq z ≤ 1} :=
    closure_minimal (fun z hz => by
      have : vecNormSq z < 1 ^ 2 := hz
      simp only [Set.mem_ofPred_eq]
      linarith only [this])
      (isClosed_le Section6.continuous_vecNormSq continuous_const)
  have h1 : vecNormSq x ≤ 1 := hcl hx.1
  have h2 : ¬ vecNormSq x < 1 ^ 2 := hx.2
  linarith only [h1, not_lt.1 h2]

/-- Local description of the unit Euclidean ball near a boundary point `x`: the ball is the region
below the graph of `√(1 - |z|²)` over the hyperplane orthogonal to `x`. -/
theorem euclidBall_local_graph [NeZero d] {x : Vec d} (hx : vecNormSq x = 1) {y : Vec d}
    (hy : y ∈ Metric.ball x (1 / (4 * (d : ℝ)))) :
    vecNormSq (y - vecDot x y • x) < 1 / 4 ∧
      (y ∈ Section6.euclidBall (d := d) 1 ↔
        vecDot x y < Real.sqrt (1 - vecNormSq (y - vecDot x y • x))) := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  have hd1 : (1 : ℝ) ≤ d := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  set r : ℝ := 1 / (4 * (d : ℝ)) with hr
  have hrpos : 0 < r := by positivity
  have hdr : (d : ℝ) * r = 1 / 4 := by rw [hr]; field_simp
  have hr1 : r ≤ 1 / 4 := by
    rw [hr, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [hd1]
  set v : Vec d := y - x with hv
  have hvi : ∀ i, |v i| < r := fun i => by
    have := (dist_pi_lt_iff hrpos).1 (Metric.mem_ball.1 hy) i
    simpa [Real.dist_eq, hv] using this
  have hxi : ∀ i, |x i| ≤ 1 := fun i => by
    have h := sq_apply_le_vecNormSq x i
    rw [hx] at h
    exact sq_le_one_iff_abs_le_one _ |>.1 h
  have hxv : -(1 / 4 : ℝ) ≤ vecDot x v := by
    have h1 : ∀ i, -r ≤ x i * v i := fun i => by
      have : |x i * v i| ≤ r := by
        rw [abs_mul]
        calc |x i| * |v i| ≤ 1 * r := mul_le_mul (hxi i) (hvi i).le (abs_nonneg _) zero_le_one
          _ = r := one_mul r
      linarith only [(abs_le.1 this).1]
    have : ∑ i : Fin d, (-r) ≤ ∑ i, x i * v i := Finset.sum_le_sum fun i _ => h1 i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    unfold vecDot
    linarith only [this, hdr]
  have hy' : y = x + v := by rw [hv]; abel
  have ht : vecDot x y = 1 + vecDot x v := by
    have h1 : vecDot x y = vecDot x x + vecDot x v := by
      unfold vecDot
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := congrFun hy' i
      simp only [Pi.add_apply] at this
      rw [this]
      ring
    rw [h1]
    have : vecDot x x = 1 := hx
    rw [this]
  have hp : y - vecDot x y • x = v - vecDot x v • x := by
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [ht]
    have := congrFun hy' i
    simp only [Pi.add_apply] at this
    rw [this]
    ring
  have hvv : vecNormSq v ≤ d * r ^ 2 := by
    unfold vecNormSq vecDot
    calc ∑ i, v i * v i ≤ ∑ _i : Fin d, r ^ 2 := Finset.sum_le_sum fun i _ => by
          have := hvi i
          nlinarith only [this, abs_nonneg (v i), sq_abs (v i)]
      _ = d * r ^ 2 := by simp
  have hpn : vecNormSq (y - vecDot x y • x) ≤ d * r ^ 2 := by
    rw [hp, vecNormSq_sub_proj hx]
    linarith only [hvv, sq_nonneg (vecDot x v)]
  have hdr2 : (d : ℝ) * r ^ 2 < 1 / 4 := by
    have : (d : ℝ) * r ^ 2 = (d * r) * r := by ring
    rw [this, hdr]
    linarith only [hr1]
  refine ⟨lt_of_le_of_lt hpn hdr2, ?_⟩
  have ht0 : 0 ≤ vecDot x y := by rw [ht]; linarith only [hxv]
  have hpy := vecNormSq_sub_proj hx y
  have hsq : vecNormSq y = vecDot x y ^ 2 + vecNormSq (y - vecDot x y • x) := by
    linarith only [hpy]
  rw [Real.lt_sqrt ht0]
  show vecNormSq y < 1 ^ 2 ↔ _
  constructor <;> intro h <;> linarith only [h, hsq]

/-- The unit Euclidean ball is a smooth bounded domain. -/
theorem isSmoothBoundedDomain_euclidBall [NeZero d] :
    IsSmoothBoundedDomain (Section6.euclidBall (d := d) 1) := by
  have hd1 : (1 : ℝ) ≤ d := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  refine ⟨Section6.isOpen_euclidBall 1, ?_, ?_, ?_⟩
  · exact (convex_euclidBall 1).isConnected (Section6.euclidBall_nonempty one_pos)
  · exact (Metric.isBounded_ball.subset (Section6.euclidBall_subset_ball one_pos)).isBoundedDomain
  · intro x hx
    have hx1 := frontier_euclidBall_subset hx
    refine ⟨x, fun z => Real.sqrt (1 - vecNormSq z), {z | vecNormSq z < 1 / 4}, 1 / (4 * (d : ℝ)),
      hx1, by positivity, isOpen_lt Section6.continuous_vecNormSq continuous_const, ?_,
      fun y hy => ?_⟩
    · have hq : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec d => vecNormSq z) := by
        unfold vecNormSq vecDot
        fun_prop
      refine ContDiffOn.sqrt (contDiff_const.sub hq).contDiffOn fun z hz => ?_
      have : vecNormSq z < 1 / 4 := hz
      linarith only [this]
    · exact euclidBall_local_graph hx1 hy

end SuperdiffusionCLT.Section7
