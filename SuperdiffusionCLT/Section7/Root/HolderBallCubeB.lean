/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.EuclidBall
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Round

/-!
# Covering a Euclidean ball by translated cubes

Geometry for the end of the proof of the large-scale Hölder theorem
(the paragraph "We pass from cubes to balls"), including the
repair for radii `r` close to `R/2`: for `r ≤ R/2` the ball `B_r` is covered by finitely many
translated cubes `y + □_n` with centres `y` on the lattice `s ℤ^d`, such that the enlarged cubes
`y + □_{n+1}` lie in `B_R`.  `h1_cube y n` is the open cube `y + □_n` (the sup-norm ball of radius
`3^n / 2` about `y`).

## Main results

* `SuperdiffusionCLT.Section7.h1_covering`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory SuperdiffusionCLT.Section6

variable {d : ℕ}

/-- The translated open cube `y + □_n`, as a sup-norm ball. -/
def h1_cube (y : Vec d) (n : ℕ) : Set (Vec d) := Metric.ball y ((3 : ℝ) ^ n / 2)

/-- The lattice `s ℤ^d`. -/
def h1_lattice (d : ℕ) (s : ℝ) : Set (Vec d) := {y | ∀ i, ∃ k : ℤ, y i = s * k}

theorem h1_exists_lattice {s : ℝ} (hs : 0 < s) (x : Vec d) :
    ∃ y ∈ h1_lattice d s, ∀ i, |x i - y i| ≤ s / 2 := by
  refine ⟨fun i => s * round (x i / s), fun i => ⟨round (x i / s), rfl⟩, fun i => ?_⟩
  have h := abs_sub_round (x i / s)
  have e : x i - s * round (x i / s) = s * (x i / s - round (x i / s)) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hs]
  nlinarith only [h, hs]

theorem h1_mem_cube_iff {y x : Vec d} {n : ℕ} :
    x ∈ h1_cube y n ↔ ∀ i, |x i - y i| < (3 : ℝ) ^ n / 2 := by
  have hp : (0 : ℝ) < (3 : ℝ) ^ n / 2 := by positivity
  unfold h1_cube
  rw [mem_ball_iff_norm, pi_norm_lt_iff hp]
  simp only [Pi.sub_apply, Real.norm_eq_abs]

theorem h1_vecNormSq_le {z : Vec d} {τ : ℝ} (h : ∀ i, |z i| ≤ τ) :
    vecNormSq z ≤ d * τ ^ 2 := by
  unfold vecNormSq vecDot
  have : ∀ i ∈ (Finset.univ : Finset (Fin d)), z i * z i ≤ τ ^ 2 := by
    intro i _
    have := h i
    nlinarith only [this, abs_nonneg (z i), sq_abs (z i)]
  have h2 := Finset.sum_le_sum this
  simpa using h2

theorem h1_euclid_add {y z : Vec d} {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ)
    (hy : vecNormSq y < ρ ^ 2) (hz : ∀ i, |z i| ≤ τ) :
    vecNormSq (y + z) < (ρ + Real.sqrt d * τ) ^ 2 := by
  have hexp : vecNormSq (y + z) = vecNormSq y + 2 * vecDot y z + vecNormSq z := by
    unfold vecNormSq vecDot
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]
    ring
  have hzn : vecNormSq z ≤ (Real.sqrt d * τ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    exact h1_vecNormSq_le hz
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq y z
  have hyn := vecNormSq_nonneg y
  have hzn0 := vecNormSq_nonneg z
  set τ' := Real.sqrt d * τ with hτ'
  have hτ0 : 0 ≤ τ' := by positivity
  have hdot : vecDot y z ≤ ρ * τ' := by
    have h1 : vecDot y z ^ 2 ≤ (ρ * τ') ^ 2 := by
      calc vecDot y z ^ 2 ≤ vecNormSq y * vecNormSq z := hcs
        _ ≤ ρ ^ 2 * τ' ^ 2 := mul_le_mul hy.le hzn hzn0 (by positivity)
        _ = (ρ * τ') ^ 2 := by ring
    exact (abs_le_of_sq_le_sq' h1 (by positivity)).2
  rw [hexp]
  nlinarith only [hy, hzn, hdot]

theorem h1_lattice_finite {s : ℝ} (hs : 0 < s) (ρ : ℝ) :
    {y : Vec d | y ∈ h1_lattice d s ∧ ∀ i, |y i| ≤ ρ}.Finite := by
  set N : ℤ := ⌈ρ / s⌉ with hN
  have hfin : ((fun k : Fin d → ℤ => fun i => s * (k i : ℝ)) ''
      Set.pi Set.univ (fun _ : Fin d => Set.Icc (-N) N)).Finite :=
    (Set.Finite.pi (fun _ => Set.finite_Icc _ _)).image _
  refine hfin.subset ?_
  rintro y ⟨hy, hb⟩
  choose k hk using hy
  refine ⟨k, fun i _ => ?_, funext fun i => (hk i).symm⟩
  have h1 : |s * (k i : ℝ)| ≤ ρ := (hk i) ▸ hb i
  rw [abs_mul, abs_of_pos hs] at h1
  have h2 : |(k i : ℝ)| ≤ ρ / s := by rw [le_div_iff₀ hs]; linarith only [h1, mul_comm s |(k i : ℝ)|]
  have h3 : (|(k i : ℝ)|) ≤ N := h2.trans (Int.le_ceil _)
  have h4 := abs_le.1 h3
  constructor
  · have : (-(N : ℝ)) ≤ k i := h4.1
    exact_mod_cast this
  · exact_mod_cast h4.2

/-- **Covering for the large radius regime.** If `0 < r`, `0 < s < 3^n` and `r + 2 √d 3^n ≤ R`,
then `B_r` is covered by the cubes `y + □_n`, `y ∈ Y ⊆ s ℤ^d` finite, the centres satisfy
`|y_i| ≤ r + 3^n/2`, and each enlarged cube `y + □_{n+1}` lies in `B_R`. -/
theorem h1_covering {r R s : ℝ} {n : ℕ} (hr : 0 < r) (hs : 0 < s) (hsn : s < (3 : ℝ) ^ n)
    (hR : r + 2 * Real.sqrt d * (3 : ℝ) ^ n ≤ R) :
    ∃ Y : Finset (Vec d), (∀ y ∈ Y, y ∈ h1_lattice d s) ∧
      (∀ y ∈ Y, ∀ i, |y i| ≤ r + (3 : ℝ) ^ n / 2) ∧
      euclidBall (d := d) r ⊆ ⋃ y ∈ Y, h1_cube y n ∧
      ∀ y ∈ Y, h1_cube y (n + 1) ⊆ euclidBall (d := d) R := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  set P : Set (Vec d) := {y | y ∈ h1_lattice d s ∧ ∃ x ∈ euclidBall (d := d) r, x ∈ h1_cube y n}
    with hP
  have hsup : ∀ y ∈ P, ∀ i, |y i| ≤ r + (3 : ℝ) ^ n / 2 := by
    rintro y ⟨_, x, hx, hxy⟩ i
    have hx1 := euclidBall_subset_ball hr hx
    rw [mem_ball_zero_iff, pi_norm_lt_iff hr] at hx1
    have h1 := hx1 i
    rw [Real.norm_eq_abs] at h1
    have h2 := (h1_mem_cube_iff.1 hxy) i
    have : |y i| ≤ |x i| + |x i - y i| := by
      have := abs_sub_abs_le_abs_sub (y i) (x i)
      rw [abs_sub_comm (y i) (x i)] at this
      linarith only [this, abs_sub_comm (x i) (y i), abs_add_le (x i) (y i - x i)]
    linarith only [this, h1, h2]
  have hfin : P.Finite := (h1_lattice_finite hs (r + (3 : ℝ) ^ n / 2)).subset
    fun y hy => ⟨hy.1, hsup y hy⟩
  refine ⟨hfin.toFinset, fun y hy => ((hfin.mem_toFinset).1 hy).1,
    fun y hy => hsup y ((hfin.mem_toFinset).1 hy), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := h1_exists_lattice hs x
    simp only [Set.mem_iUnion]
    refine ⟨y, ?_, h1_mem_cube_iff.2 fun i => ?_⟩
    · exact (hfin.mem_toFinset).2 ⟨hy, x, hx, h1_mem_cube_iff.2 fun i =>
        lt_of_le_of_lt (hxy i) (by linarith only [hsn])⟩
    · exact lt_of_le_of_lt (hxy i) (by linarith only [hsn])
  · intro y hy x hx
    obtain ⟨hyl, x0, hx0, hx0y⟩ := (hfin.mem_toFinset).1 hy
    have hx0' := h1_mem_cube_iff.1 hx0y
    have hxy := h1_mem_cube_iff.1 hx
    -- Euclidean norm of y
    have hy2 : vecNormSq y < (r + Real.sqrt d * ((3 : ℝ) ^ n / 2)) ^ 2 := by
      have e : y = x0 + (y - x0) := by ring
      have := h1_euclid_add (z := y - x0) (ρ := r) (τ := (3 : ℝ) ^ n / 2) hr.le (by positivity)
        (by simpa [mem_euclidBall] using hx0) (fun i => by
          have := hx0' i
          simp only [Pi.sub_apply]
          rw [abs_sub_comm]; exact this.le)
      rwa [← e] at this
    have hxe : x = y + (x - y) := by ring
    have := h1_euclid_add (z := x - y) (ρ := r + Real.sqrt d * ((3 : ℝ) ^ n / 2))
      (τ := (3 : ℝ) ^ (n + 1) / 2) (by positivity) (by positivity) hy2 (fun i => by
        have := hxy i
        simp only [Pi.sub_apply]
        exact this.le)
    rw [← hxe] at this
    rw [mem_euclidBall]
    refine this.trans_le ?_
    have e : r + Real.sqrt d * ((3 : ℝ) ^ n / 2) + Real.sqrt d * ((3 : ℝ) ^ (n + 1) / 2)
        = r + 2 * Real.sqrt d * (3 : ℝ) ^ n := by rw [pow_succ]; ring
    rw [e]
    have : 0 ≤ r + 2 * Real.sqrt d * (3 : ℝ) ^ n := by positivity
    exact pow_le_pow_left₀ this hR 2

/-- Satisfiability: `d = 1`, `r = 1`, `s = 1`, `n = 1`, `R = 8`. -/
example : (1 : ℝ) + 2 * Real.sqrt (1 : ℕ) * (3 : ℝ) ^ 1 ≤ 8 := by simp; norm_num

end SuperdiffusionCLT.Section7
