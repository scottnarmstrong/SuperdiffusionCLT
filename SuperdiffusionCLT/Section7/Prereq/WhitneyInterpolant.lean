/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.OpenH10.LipschitzB
public import SuperdiffusionCLT.Section7.Analytic.Geometry.WhitneyBall

/-!
# A tent-function interpolant of cube averages

On the grid `h ℤ^d` the tensor-product hat functions `χ_k(x) = ∏ i, T (x i / h - k i)`,
`T s = max 0 (1 - |s|)`, form a partition of unity with Lipschitz constant `d / h`.  On the cube
`h k₀ + (-h/2, h/2)^d` only the `3^d` hats with `|k - k₀|_∞ ≤ 1` are nonzero, and they sum to one.
For reals `c k`, the interpolant `A = ∑ k ∈ Z, c k * χ_k` is Lipschitz, and on the cube of `k₀`
it satisfies `(u - A)^2 ≤ ∑_{k ~ k₀} (u - c k)^2` pointwise.

## Main definitions and results

* `Section7.wh1_chi`, `Section7.wh1_nbhd`, `Section7.wh1_A`, `Section7.wh1_box`.
* `Section7.wh1_chi_sum`: the partition of unity on a cube.
* `Section7.wh1_chi_lip`: the Lipschitz bound `d / h`.
* `Section7.wh1_sq_sub_A_le`: the pointwise form of the `L²` interpolation estimate.
-/

@[expose] public section

open MeasureTheory Set

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The one-dimensional tent function. -/
noncomputable def wh1_tent (s : ℝ) : ℝ := max 0 (1 - |s|)

/-- The tensor-product hat function at the grid point `h k`. -/
noncomputable def wh1_chi (h : ℝ) (k : Fin d → ℤ) (x : Vec d) : ℝ :=
  ∏ i, wh1_tent (x i / h - (k i : ℝ))

/-- The `3^d` grid indices at sup-distance at most one from `k₀`. -/
def wh1_nbhd (k₀ : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => ({k₀ i - 1, k₀ i, k₀ i + 1} : Finset ℤ)

/-- The interpolant of the values `c k` over the grid indices `Z`. -/
noncomputable def wh1_A (h : ℝ) (Z : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) (x : Vec d) : ℝ :=
  ∑ k ∈ Z, c k * wh1_chi h k x

/-- The grid point `h k`. -/
def wh1_pt (h : ℝ) (k : Fin d → ℤ) : Vec d := fun i => h * (k i : ℝ)

/-- The open cube with centre `y` and half-side `r`. -/
def wh1_box (y : Vec d) (r : ℝ) : Set (Vec d) := {x | ∀ i, |x i - y i| < r}

theorem wh1_tent_nonneg (s : ℝ) : 0 ≤ wh1_tent s := le_max_left _ _

theorem wh1_tent_le_one (s : ℝ) : wh1_tent s ≤ 1 :=
  max_le zero_le_one (by linarith only [abs_nonneg s])

theorem wh1_tent_eq_zero {s : ℝ} (h : 1 ≤ |s|) : wh1_tent s = 0 :=
  max_eq_left (by linarith only [h])

theorem wh1_tent_lip (a b : ℝ) : |wh1_tent a - wh1_tent b| ≤ |a - b| := by
  unfold wh1_tent
  rw [max_comm 0, max_comm 0 (1 - |b|)]
  refine (abs_max_sub_max_le_abs (1 - |a|) (1 - |b|) 0).trans ?_
  have := abs_abs_sub_abs_le_abs_sub a b
  calc |1 - |a| - (1 - |b|)| = |(|a| - |b|)| := by rw [← abs_neg]; congr 1; ring
    _ ≤ |a - b| := this

theorem wh1_tent_sum {t : ℝ} (ht : |t| ≤ 1) :
    wh1_tent (t + 1) + wh1_tent t + wh1_tent (t - 1) = 1 := by
  rw [abs_le] at ht
  unfold wh1_tent
  rcases le_total 0 t with h0 | h0
  · rw [abs_of_nonneg (by linarith only [h0] : (0:ℝ) ≤ t + 1), abs_of_nonneg h0,
      abs_of_nonpos (by linarith only [ht.2] : t - 1 ≤ 0)]
    rw [max_eq_left (by linarith only [h0]), max_eq_right (by linarith only [ht.2]),
      max_eq_right (by linarith only [h0])]
    ring
  · rw [abs_of_nonneg (by linarith only [ht.1] : (0:ℝ) ≤ t + 1), abs_of_nonpos h0,
      abs_of_nonpos (by linarith only [h0] : t - 1 ≤ 0)]
    rw [max_eq_right (by linarith only [h0]), max_eq_right (by linarith only [ht.1]),
      max_eq_left (by linarith only [h0])]
    ring

theorem wh1_tent_arg_le {h : ℝ} (hh : 0 < h) {x : Vec d} {k₀ : Fin d → ℤ}
    (hx : ∀ i, |x i - h * (k₀ i : ℝ)| ≤ h / 2) (i : Fin d) : |x i / h - (k₀ i : ℝ)| ≤ 1 / 2 := by
  have e : x i / h - (k₀ i : ℝ) = (x i - h * (k₀ i : ℝ)) / h := by field_simp
  rw [e, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  linarith only [hx i]

theorem wh1_chi_nonneg (h : ℝ) (k : Fin d → ℤ) (x : Vec d) : 0 ≤ wh1_chi h k x :=
  Finset.prod_nonneg fun _ _ => wh1_tent_nonneg _

theorem wh1_chi_le_one (h : ℝ) (k : Fin d → ℤ) (x : Vec d) : wh1_chi h k x ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => wh1_tent_nonneg _) fun _ _ => wh1_tent_le_one _

/-- The partition of unity on the cube of `k₀`. -/
theorem wh1_chi_sum {h : ℝ} (hh : 0 < h) {x : Vec d} {k₀ : Fin d → ℤ}
    (hx : ∀ i, |x i - h * (k₀ i : ℝ)| ≤ h / 2) :
    ∑ k ∈ wh1_nbhd k₀, wh1_chi h k x = 1 := by
  unfold wh1_nbhd wh1_chi
  have key : ∑ p ∈ Fintype.piFinset (fun i => ({k₀ i - 1, k₀ i, k₀ i + 1} : Finset ℤ)),
      ∏ i, wh1_tent (x i / h - (p i : ℝ)) =
      ∏ i, ∑ j ∈ ({k₀ i - 1, k₀ i, k₀ i + 1} : Finset ℤ), wh1_tent (x i / h - (j : ℝ)) :=
    (Finset.prod_univ_sum (fun i => ({k₀ i - 1, k₀ i, k₀ i + 1} : Finset ℤ))
      (fun i j => wh1_tent (x i / h - (j : ℝ)))).symm
  rw [key]
  refine Finset.prod_eq_one fun i _ => ?_
  have ht := (wh1_tent_arg_le hh hx i).trans (by norm_num : (1 : ℝ) / 2 ≤ 1)
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton]
  have e1 : x i / h - ((k₀ i - 1 : ℤ) : ℝ) = (x i / h - (k₀ i : ℝ)) + 1 := by push_cast; ring
  have e3 : x i / h - ((k₀ i + 1 : ℤ) : ℝ) = (x i / h - (k₀ i : ℝ)) - 1 := by push_cast; ring
  rw [e1, e3]
  have := wh1_tent_sum ht
  linarith only [this]

theorem wh1_chi_eq_zero_of_notMem {h : ℝ} (hh : 0 < h) {x : Vec d} {k₀ k : Fin d → ℤ}
    (hx : ∀ i, |x i - h * (k₀ i : ℝ)| ≤ h / 2) (hk : k ∉ wh1_nbhd k₀) :
    wh1_chi h k x = 0 := by
  unfold wh1_nbhd at hk
  rw [Fintype.mem_piFinset] at hk
  push Not at hk
  obtain ⟨i, hi⟩ := hk
  unfold wh1_chi
  refine Finset.prod_eq_zero (Finset.mem_univ i) (wh1_tent_eq_zero ?_)
  have hc : k i ≤ k₀ i - 2 ∨ k₀ i + 2 ≤ k i := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi; omega
  have ht := abs_le.1 (wh1_tent_arg_le hh hx i)
  rcases hc with h2 | h2
  · have : (k i : ℝ) ≤ (k₀ i : ℝ) - 2 := by exact_mod_cast h2
    exact le_abs.2 (Or.inl (by linarith only [ht.1, ht.2, this]))
  · have : (k₀ i : ℝ) + 2 ≤ (k i : ℝ) := by exact_mod_cast h2
    exact le_abs.2 (Or.inr (by linarith only [ht.1, ht.2, this]))

theorem wh1_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i)
    (ha1 : ∀ i, a i ≤ 1) (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1) [DecidableEq ι] :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have hQ0 : 0 ≤ ∏ i ∈ s, b i := Finset.prod_nonneg fun i _ => hb0 i
    have hQ1 : ∏ i ∈ s, b i ≤ 1 := Finset.prod_le_one₀ (fun i _ => hb0 i) fun i _ => hb1 i
    calc |a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i|
        = |a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i| := by ring_nf
      _ ≤ |a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)| + |(a j - b j) * ∏ i ∈ s, b i| := abs_add_le _ _
      _ = a j * |∏ i ∈ s, a i - ∏ i ∈ s, b i| + |a j - b j| * ∏ i ∈ s, b i := by
          rw [abs_mul, abs_mul, abs_of_nonneg (ha0 j), abs_of_nonneg hQ0]
      _ ≤ 1 * |∏ i ∈ s, a i - ∏ i ∈ s, b i| + |a j - b j| * 1 := by
          gcongr
          · exact ha1 j
      _ ≤ |a j - b j| + ∑ i ∈ s, |a i - b i| := by linarith only [ih]

/-- The hat functions are `d / h`-Lipschitz for the sup norm. -/
theorem wh1_chi_lip {h : ℝ} (hh : 0 < h) (k : Fin d → ℤ) (x y : Vec d) :
    |wh1_chi h k x - wh1_chi h k y| ≤ (d : ℝ) / h * ‖x - y‖ := by
  unfold wh1_chi
  refine (wh1_prod_sub_prod_le Finset.univ _ _ (fun _ => wh1_tent_nonneg _)
    (fun _ => wh1_tent_le_one _) (fun _ => wh1_tent_nonneg _) (fun _ => wh1_tent_le_one _)).trans ?_
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      |wh1_tent (x i / h - (k i : ℝ)) - wh1_tent (y i / h - (k i : ℝ))| ≤ ‖x - y‖ / h := by
    intro i _
    refine (wh1_tent_lip _ _).trans ?_
    have e : x i / h - (k i : ℝ) - (y i / h - (k i : ℝ)) = (x i - y i) / h := by ring
    rw [e, abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right (by simpa using norm_le_pi_norm (x - y) i) hh.le
  refine (Finset.sum_le_sum hi).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [div_mul_eq_mul_div]
  apply le_of_eq
  ring

end SuperdiffusionCLT.Section7
