/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.ResolventMismatch
public import SuperdiffusionCLT.Section6.Prereq.EuclidBall

/-!
# Exponential decay of the Laplace profile, and the iteration arithmetic

For a `C²` function `w` with `lam w - s Δ w ≤ 0` in a bounded open set and `w ≤ 1` on the
frontier (the profile `1 - lam v` of the exit-time Laplace transform), the sum of the
exponentials `exp (±μ (y_j - x_j) - μ δ/√d)`, `μ² = lam/s`, is a supersolution that dominates
`w` on every Euclidean sphere about `x` inside the set, so that
`w x ≤ 2 d exp (-√(lam/s) δ/√d)`.

* `resMis_exp_decay`: the decay estimate;
* `resMis_chain`, `resMis_pow_half_le`: the geometric chain of the iteration over balls.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Filter Homogenization Topology SuperdiffusionCLT.Section8.Brownian

variable {d : ℕ}

theorem resMis_exp_contDiff (j : Fin d) (a b : ℝ) :
    ContDiff ℝ 2 (fun y : Vec d ↦ Real.exp (a * y j + b)) := by
  fun_prop

theorem resMis_exp_hasFDerivAt (j : Fin d) (a b : ℝ) (y : Vec d) :
    HasFDerivAt (fun z : Vec d ↦ Real.exp (a * z j + b))
      ((Real.exp (a * y j + b) * a) • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)) y := by
  have h1 : HasFDerivAt (fun z : Vec d ↦ a * z j + b)
      (a • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)) y := by
    have := ((ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ).hasFDerivAt (x := y)).const_mul a
    simpa using this.add_const b
  have := h1.exp
  convert this using 1
  rw [smul_smul, mul_comm]

theorem resMis_exp_vecLaplacian (j : Fin d) (a b : ℝ) (y : Vec d) :
    vecLaplacian (fun z : Vec d ↦ Real.exp (a * z j + b)) y =
      a ^ 2 * Real.exp (a * y j + b) := by
  have hfd : fderiv ℝ (fun z : Vec d ↦ Real.exp (a * z j + b)) =
      fun z ↦ (Real.exp (a * z j + b) * a) • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) :=
    funext fun z ↦ (resMis_exp_hasFDerivAt j a b z).fderiv
  rw [vecLaplacian_eq_sum_fderiv, hfd]
  have hc := (resMis_exp_hasFDerivAt j a b y).mul_const a
  have h := hc.smul_const (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)
  rw [h.fderiv]
  rw [Finset.sum_eq_single j]
  · simp
    ring
  · intro i _ hij
    simp [hij.symm]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem resMis_vecLaplacian_add {f g : Vec d → ℝ} {x : Vec d} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    vecLaplacian (fun y ↦ f y + g y) x = vecLaplacian f x + vecLaplacian g x := by
  unfold vecLaplacian
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show (fun y ↦ f y + g y) = f + g from rfl, iteratedFDeriv_add_apply hf hg]
  rfl

theorem resMis_vecLaplacian_sum {ι : Type*} (u : Finset ι) {f : ι → Vec d → ℝ} {x : Vec d}
    (h : ∀ k ∈ u, ContDiffAt ℝ 2 (f k) x) :
    vecLaplacian (fun y ↦ ∑ k ∈ u, f k y) x = ∑ k ∈ u, vecLaplacian (f k) x := by
  unfold vecLaplacian
  simp_rw [iteratedFDeriv_fun_sum_apply h]
  rw [Finset.sum_comm]
  simp

/-- The exponential barrier of the ball `{|y - x| ≤ δ}` with `c = δ/√d`. -/
noncomputable def resMis_barrier (mu c : ℝ) (x : Vec d) (y : Vec d) : ℝ :=
  ∑ j : Fin d, (Real.exp (mu * y j + (-(mu * x j) - mu * c)) +
    Real.exp ((-mu) * y j + (mu * x j - mu * c)))

theorem resMis_barrier_contDiff (mu c : ℝ) (x : Vec d) : ContDiff ℝ 2 (resMis_barrier mu c x) := by
  unfold resMis_barrier
  refine ContDiff.sum fun j _ ↦ ?_
  exact (resMis_exp_contDiff j _ _).add (resMis_exp_contDiff j _ _)

theorem resMis_barrier_vecLaplacian (mu c : ℝ) (x y : Vec d) :
    vecLaplacian (resMis_barrier mu c x) y = mu ^ 2 * resMis_barrier mu c x y := by
  have h : resMis_barrier mu c x = fun y ↦ ∑ j : Fin d, (Real.exp (mu * y j + (-(mu * x j) - mu * c)) +
    Real.exp ((-mu) * y j + (mu * x j - mu * c))) := rfl
  rw [h, resMis_vecLaplacian_sum _ (fun j _ ↦ ((resMis_exp_contDiff j _ _).add
    (resMis_exp_contDiff j _ _)).contDiffAt)]
  beta_reduce
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [resMis_vecLaplacian_add (resMis_exp_contDiff j _ _).contDiffAt
    (resMis_exp_contDiff j _ _).contDiffAt, resMis_exp_vecLaplacian, resMis_exp_vecLaplacian]
  ring_nf

theorem resMis_barrier_at_center (mu c : ℝ) (x : Vec d) :
    resMis_barrier mu c x x = 2 * d * Real.exp (-(mu * c)) := by
  unfold resMis_barrier
  have : ∀ j : Fin d, Real.exp (mu * x j + (-(mu * x j) - mu * c)) +
      Real.exp ((-mu) * x j + (mu * x j - mu * c)) = 2 * Real.exp (-(mu * c)) := by
    intro j
    have e1 : mu * x j + (-(mu * x j) - mu * c) = -(mu * c) := by ring
    have e2 : (-mu) * x j + (mu * x j - mu * c) = -(mu * c) := by ring
    rw [e1, e2]; ring
  rw [Finset.sum_congr rfl fun j _ ↦ this j]
  simp
  ring

theorem resMis_one_le_barrier {mu c : ℝ} (hmu : 0 ≤ mu) {x y : Vec d} {j : Fin d}
    (hj : c ≤ |y j - x j|) : 1 ≤ resMis_barrier mu c x y := by
  unfold resMis_barrier
  have hterm : ∀ k : Fin d, 0 ≤ Real.exp (mu * y k + (-(mu * x k) - mu * c)) +
      Real.exp ((-mu) * y k + (mu * x k - mu * c)) :=
    fun k ↦ add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  refine le_trans ?_ (Finset.single_le_sum (fun k _ ↦ hterm k) (Finset.mem_univ j))
  rcases le_abs'.mp hj with h | h
  · have : 1 ≤ Real.exp ((-mu) * y j + (mu * x j - mu * c)) := by
      rw [Real.one_le_exp_iff]
      nlinarith only [h, hmu]
    linarith only [this, Real.exp_pos (mu * y j + (-(mu * x j) - mu * c))]
  · have : 1 ≤ Real.exp (mu * y j + (-(mu * x j) - mu * c)) := by
      rw [Real.one_le_exp_iff]
      nlinarith only [h, hmu]
    linarith only [this, Real.exp_pos ((-mu) * y j + (mu * x j - mu * c))]

/-- The closed Euclidean ball is bounded: the open ball about `x` of radius `δ`. -/
theorem resMis_ball_open (x : Vec d) (δ : ℝ) : IsOpen {y : Vec d | vecNormSq (y - x) < δ ^ 2} :=
  isOpen_lt (SuperdiffusionCLT.Section6.continuous_vecNormSq.comp (continuous_id.sub continuous_const))
    continuous_const

theorem resMis_ball_bounded (x : Vec d) {δ : ℝ} (hδ : 0 < δ) :
    Bornology.IsBounded {y : Vec d | vecNormSq (y - x) < δ ^ 2} := by
  refine (Metric.isBounded_ball (x := x) (r := δ)).subset fun y hy ↦ ?_
  have h := SuperdiffusionCLT.Section6.euclidBall_subset_ball hδ (show y - x ∈
    SuperdiffusionCLT.Section6.euclidBall (d := d) δ from hy)
  rw [mem_ball_zero_iff, ← dist_eq_norm] at h
  exact h

theorem resMis_frontier_ball {x : Vec d} {δ : ℝ} {y : Vec d}
    (hy : y ∈ frontier {y : Vec d | vecNormSq (y - x) < δ ^ 2}) : vecNormSq (y - x) = δ ^ 2 := by
  rw [frontier, (resMis_ball_open x δ).interior_eq] at hy
  obtain ⟨hcl, hn⟩ := hy
  have hle : closure {y : Vec d | vecNormSq (y - x) < δ ^ 2} ⊆ {y | vecNormSq (y - x) ≤ δ ^ 2} :=
    closure_minimal (fun z (hz : vecNormSq (z - x) < δ ^ 2) ↦ le_of_lt hz)
      (isClosed_le (SuperdiffusionCLT.Section6.continuous_vecNormSq.comp
        (continuous_id.sub continuous_const)) continuous_const)
  exact le_antisymm (hle hcl) (not_lt.mp hn)

theorem resMis_exists_coord {x y : Vec d} {δ : ℝ} (hδ : 0 < δ) (hy : vecNormSq (y - x) = δ ^ 2) :
    ∃ j : Fin d, δ / Real.sqrt d ≤ |y j - x j| := by
  by_contra hcon
  push Not at hcon
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      simp [vecNormSq, vecDot] at hy
      linarith only [hy, sq_pos_of_pos hδ]
    · exact h
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hlt : ∀ j : Fin d, (y j - x j) ^ 2 < (δ / Real.sqrt d) ^ 2 := fun j ↦ by
    have := hcon j
    exact sq_lt_sq' (by linarith only [this, neg_abs_le (y j - x j)])
      (lt_of_le_of_lt (le_abs_self _) this)
  have hsum : vecNormSq (y - x) < ∑ _j : Fin d, (δ / Real.sqrt d) ^ 2 := by
    unfold vecNormSq vecDot
    exact Finset.sum_lt_sum_of_nonempty ⟨⟨0, hd⟩, Finset.mem_univ _⟩ fun j _ ↦ by
      simpa [sq] using hlt j
  have : ∑ _j : Fin d, (δ / Real.sqrt d) ^ 2 = δ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow,
      Real.sq_sqrt (Nat.cast_nonneg d)]
    field_simp
  linarith only [hsum, hy, this]

/-- **Exponential decay of the Laplace profile.**  A `C²` function with `lam w - s Δ w ≤ 0` in a
bounded open set `U` and `w ≤ 1` on the frontier satisfies, at the centre of a Euclidean ball
`{|y - x| < δ} ⊆ U`, `w x ≤ 2 d exp (-√(lam/s) δ/√d)`. -/
theorem resMis_exp_decay {U : Set (Vec d)} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    {w : Vec d → ℝ} (hc : ContinuousOn w (closure U)) (h2 : ∀ x ∈ U, ContDiffAt ℝ 2 w x)
    {lam s : ℝ} (hlam : 0 < lam) (hs : 0 < s)
    (hPDE : ∀ x ∈ U, lam * w x - s * vecLaplacian w x ≤ 0)
    (hfr : ∀ y ∈ frontier U, w y ≤ 1) {x : Vec d} {δ : ℝ} (hδ : 0 < δ)
    (hball : ∀ y : Vec d, vecNormSq (y - x) < δ ^ 2 → y ∈ U) :
    w x ≤ 2 * d * Real.exp (-(Real.sqrt (lam / s) * (δ / Real.sqrt d))) := by
  set V : Set (Vec d) := {y : Vec d | vecNormSq (y - x) < δ ^ 2} with hV
  have hVU : V ⊆ U := fun y hy ↦ hball y hy
  have hw1 : ∀ y ∈ closure U, w y ≤ 1 := by
    intro y hy
    have := resMis_max_principle hU hb hc h2 hlam (le_of_lt hs) (e := 0) (m := 1)
      (fun z hz ↦ by simpa using hPDE z hz) hfr y hy
    simpa using this
  set mu := Real.sqrt (lam / s) with hmu
  have hmu0 : 0 ≤ mu := Real.sqrt_nonneg _
  have hmu2 : mu ^ 2 = lam / s := Real.sq_sqrt (div_nonneg hlam.le hs.le)
  set c := δ / Real.sqrt d with hcdef
  have hψ := resMis_barrier_contDiff (d := d) mu c x
  have hmax := resMis_max_principle (resMis_ball_open x δ) (resMis_ball_bounded x hδ)
    (w := fun y ↦ w y - resMis_barrier mu c x y)
    (hc.mono (closure_mono hVU) |>.sub hψ.continuous.continuousOn)
    (fun y hy ↦ (h2 y (hVU hy)).sub hψ.contDiffAt) hlam (le_of_lt hs) (e := 0) (m := 0)
    (fun y hy ↦ by
      show lam * (w y - resMis_barrier mu c x y) -
        s * vecLaplacian (fun z ↦ w z - resMis_barrier mu c x z) y ≤ 0
      rw [resMis_vecLaplacian_sub (h2 y (hVU hy)) hψ.contDiffAt, resMis_barrier_vecLaplacian, hmu2]
      have := hPDE y (hVU hy)
      have e : s * (lam / s * resMis_barrier mu c x y) = lam * resMis_barrier mu c x y := by
        field_simp
      linarith only [this, e])
    (fun y hy ↦ by
      have hy2 := resMis_frontier_ball hy
      obtain ⟨j, hj⟩ := resMis_exists_coord hδ hy2
      have h1 := resMis_one_le_barrier hmu0 hj
      have hcl : y ∈ closure U := closure_mono hVU (frontier_subset_closure hy)
      have := hw1 y hcl
      linarith only [h1, this])
  have hxV : x ∈ closure V := subset_closure (by simp [hV, vecNormSq, vecDot, sq_pos_of_pos hδ])
  have := hmax x hxV
  rw [max_eq_left (by simp)] at this
  have hcen := resMis_barrier_at_center mu c x
  have : w x ≤ resMis_barrier mu c x x := by linarith only [this]
  rw [hcen] at this
  exact this

/-- Witness: the zero function satisfies the hypotheses of the decay estimate on the unit ball. -/
example : (0 : Vec 2 → ℝ) (0 : Vec 2) ≤
    2 * (2 : ℕ) * Real.exp (-(Real.sqrt (1 / 1) * (1 / Real.sqrt (2 : ℕ)))) :=
  resMis_exp_decay (SuperdiffusionCLT.Section6.isOpen_euclidBall 1)
    (resMis_isBounded_euclidBall one_pos) (w := 0) continuousOn_const (fun _ _ ↦ contDiffAt_const)
    one_pos one_pos
    (fun x _ ↦ by simp [Pi.zero_def, resMis_vecLaplacian_const])
    (fun _ _ ↦ by simp) one_pos
    (fun y hy ↦ by simpa [SuperdiffusionCLT.Section6.euclidBall] using hy)

/-- The geometric chain: `m k ≤ q m (k+1)` for `k < N` and `m N ≤ 1` give `m 0 ≤ q ^ N`. -/
theorem resMis_chain {q : ℝ} (hq : 0 ≤ q) (N : ℕ) (m : ℕ → ℝ)
    (hstep : ∀ k < N, m k ≤ q * m (k + 1)) (hN : m N ≤ 1) : m 0 ≤ q ^ N := by
  have key : ∀ n, n ≤ N → m (N - n) ≤ q ^ n := by
    intro n
    induction n with
    | zero => intro _; simpa using hN
    | succ n ih =>
      intro hn
      have h1 := hstep (N - (n + 1)) (by omega)
      have h2 : N - (n + 1) + 1 = N - n := by omega
      rw [h2] at h1
      calc m (N - (n + 1)) ≤ q * m (N - n) := h1
        _ ≤ q * q ^ n := mul_le_mul_of_nonneg_left (ih (by omega)) hq
        _ = q ^ (n + 1) := by ring
  simpa using key N le_rfl

/-- The factor `q ≤ 1/2` gives `q ^ N ≤ exp (-N log 2)`. -/
theorem resMis_pow_half_le {q : ℝ} (hq : 0 ≤ q) (hq2 : q ≤ 1 / 2) (N : ℕ) :
    q ^ N ≤ Real.exp (-(N * Real.log 2)) := by
  have h1 : q ^ N ≤ (1 / 2 : ℝ) ^ N := pow_le_pow_left₀ hq hq2 N
  have h2 : (1 / 2 : ℝ) ^ N = Real.exp (-(N * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div,
      inv_pow]
  exact h2 ▸ h1

end SuperdiffusionCLT.Section8
