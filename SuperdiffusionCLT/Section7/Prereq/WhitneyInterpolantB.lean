/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.WhitneyInterpolant

/-!
# The interpolant on a grid cube: boxes, partition of unity and the `L²` interpolation estimate

For the cube `Q(k₀) = wh1_box (wh1_pt h k₀) (h/2)` and averaging cubes `B_k` of half-side `r ≥ 3h/2`
centred at the grid points `h k`, the cube `Q(k₀)` lies in `B_k` for every `k` with
`|k - k₀|_∞ ≤ 1`, and

`∫⁻_{Q(k₀)} (u - A)^2 ≤ ∑_{k ~ k₀} ∫⁻_{B_k} (u - c k)^2`.

## Main results

* `Section7.wh1_box_isOpen`, `Section7.wh1_volume_box`.
* `Section7.wh1_box_subset_nbhd`: boxes around a point lie in the enlarged boxes of its neighbours.
* `Section7.wh1_sq_sub_A_le`: the pointwise estimate `(u - A)^2 ≤ ∑_{k ~ k₀} (u - c k)^2`.
* `Section7.wh1_lintegral_sub_A_le`: the integrated form on the cube of `k₀`.
-/

@[expose] public section

open MeasureTheory Set

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

theorem wh1_box_eq_pi (y : Vec d) (r : ℝ) :
    wh1_box y r = Set.pi univ fun i => Ioo (y i - r) (y i + r) := by
  ext x
  simp only [wh1_box, mem_ofPred_eq, mem_pi, mem_univ, true_implies, mem_Ioo]
  refine forall_congr' fun i => ?_
  rw [abs_sub_lt_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith only [h2], by linarith only [h1]⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith only [h2], by linarith only [h1]⟩

theorem wh1_box_isOpen (y : Vec d) (r : ℝ) : IsOpen (wh1_box y r) := by
  rw [wh1_box_eq_pi]
  exact isOpen_set_pi finite_univ fun i _ => isOpen_Ioo

theorem wh1_box_measurable (y : Vec d) (r : ℝ) : MeasurableSet (wh1_box y r) :=
  (wh1_box_isOpen y r).measurableSet

theorem wh1_volume_box (y : Vec d) {r : ℝ} (hr : 0 ≤ r) :
    volume (wh1_box y r) = ENNReal.ofReal ((2 * r) ^ d) := by
  rw [wh1_box_eq_pi, Real.volume_pi_Ioo]
  have : ∀ i : Fin d, y i + r - (y i - r) = 2 * r := fun i => by ring
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (by linarith only [hr]) d).symm

theorem wh1_box_mono (y : Vec d) {r s : ℝ} (hrs : r ≤ s) : wh1_box y r ⊆ wh1_box y s :=
  fun _ hx i => lt_of_lt_of_le (hx i) hrs

theorem wh1_self_mem_nbhd (k₀ : Fin d → ℤ) : k₀ ∈ wh1_nbhd k₀ := by
  unfold wh1_nbhd
  rw [Fintype.mem_piFinset]
  intro i
  simp

theorem wh1_card_nbhd (k₀ : Fin d → ℤ) : (wh1_nbhd k₀).card = 3 ^ d := by
  unfold wh1_nbhd
  rw [Fintype.card_piFinset]
  have : ∀ i : Fin d, (({k₀ i - 1, k₀ i, k₀ i + 1} : Finset ℤ)).card = 3 := fun i => by
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; omega),
      Finset.card_singleton]
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem wh1_nbhd_abs {k₀ k : Fin d → ℤ} (hk : k ∈ wh1_nbhd k₀) (i : Fin d) :
    |(k i : ℝ) - (k₀ i : ℝ)| ≤ 1 := by
  unfold wh1_nbhd at hk
  rw [Fintype.mem_piFinset] at hk
  have h1 := hk i
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  have hz : |k i - k₀ i| ≤ 1 := by rw [abs_le]; omega
  have : |((k i - k₀ i : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast hz
  push_cast at this
  exact this

/-- A box around the grid point of `k₀` lies in the box of `h` more around any neighbour. -/
theorem wh1_box_subset_nbhd {h : ℝ} (hh : 0 < h) {k₀ k : Fin d → ℤ} (hk : k ∈ wh1_nbhd k₀)
    (ρ : ℝ) : wh1_box (wh1_pt h k₀) ρ ⊆ wh1_box (wh1_pt h k) (ρ + h) := by
  intro x hx i
  have h1 := abs_lt.1 (hx i)
  have h2 := abs_le.1 (wh1_nbhd_abs hk i)
  have a1 := mul_le_mul_of_nonneg_left h2.1 hh.le
  have a2 := mul_le_mul_of_nonneg_left h2.2 hh.le
  show |x i - h * (k i : ℝ)| < ρ + h
  have h1' : -ρ < x i - h * (k₀ i : ℝ) ∧ x i - h * (k₀ i : ℝ) < ρ := h1
  have e : h * ((k i : ℝ) - (k₀ i : ℝ)) = h * (k i : ℝ) - h * (k₀ i : ℝ) := by ring
  rw [abs_lt]
  constructor
  · linarith only [h1'.1, a2, e]
  · linarith only [h1'.2, a1, e]

theorem wh1_cell_le {h : ℝ} {k₀ : Fin d → ℤ} {x : Vec d}
    (hx : x ∈ wh1_box (wh1_pt h k₀) (h / 2)) : ∀ i, |x i - h * (k₀ i : ℝ)| ≤ h / 2 :=
  fun i => (hx i).le

theorem wh1_A_eq_cell {h : ℝ} (hh : 0 < h) {k₀ : Fin d → ℤ} {Z : Finset (Fin d → ℤ)}
    (hZ : wh1_nbhd k₀ ⊆ Z) (c : (Fin d → ℤ) → ℝ) {x : Vec d}
    (hx : ∀ i, |x i - h * (k₀ i : ℝ)| ≤ h / 2) :
    wh1_A h Z c x = ∑ k ∈ wh1_nbhd k₀, c k * wh1_chi h k x := by
  unfold wh1_A
  symm
  refine Finset.sum_subset hZ fun k _ hk => ?_
  rw [wh1_chi_eq_zero_of_notMem hh hx hk, mul_zero]

theorem wh1_sub_A {h : ℝ} (hh : 0 < h) {k₀ : Fin d → ℤ} {Z : Finset (Fin d → ℤ)}
    (hZ : wh1_nbhd k₀ ⊆ Z) (c : (Fin d → ℤ) → ℝ) (u : Vec d → ℝ) {x : Vec d}
    (hx : ∀ i, |x i - h * (k₀ i : ℝ)| ≤ h / 2) :
    u x - wh1_A h Z c x = ∑ k ∈ wh1_nbhd k₀, wh1_chi h k x * (u x - c k) := by
  rw [wh1_A_eq_cell hh hZ c hx]
  have hs := wh1_chi_sum hh hx
  calc u x - ∑ k ∈ wh1_nbhd k₀, c k * wh1_chi h k x
      = (∑ k ∈ wh1_nbhd k₀, wh1_chi h k x) * u x - ∑ k ∈ wh1_nbhd k₀, c k * wh1_chi h k x := by
        rw [hs, one_mul]
    _ = ∑ k ∈ wh1_nbhd k₀, wh1_chi h k x * (u x - c k) := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring

theorem wh1_sq_sum_le {ι : Type*} (s : Finset ι) (w a : ι → ℝ) (hw0 : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) : (∑ i ∈ s, w i * a i) ^ 2 ≤ ∑ i ∈ s, w i * a i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * a i)
  have e1 : ∑ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) * a i) = ∑ i ∈ s, w i * a i :=
    Finset.sum_congr rfl fun i hi => by rw [← mul_assoc, Real.mul_self_sqrt (hw0 i hi)]
  have e2 : ∑ i ∈ s, Real.sqrt (w i) ^ 2 = 1 := by
    rw [← hw1]; exact Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hw0 i hi)
  have e3 : ∑ i ∈ s, (Real.sqrt (w i) * a i) ^ 2 = ∑ i ∈ s, w i * a i ^ 2 :=
    Finset.sum_congr rfl fun i hi => by rw [mul_pow, Real.sq_sqrt (hw0 i hi)]
  rw [e1, e2, e3, one_mul] at h
  exact h

/-- The pointwise `L²` interpolation estimate on the cube of `k₀`. -/
theorem wh1_sq_sub_A_le {h : ℝ} (hh : 0 < h) {k₀ : Fin d → ℤ} {Z : Finset (Fin d → ℤ)}
    (hZ : wh1_nbhd k₀ ⊆ Z) (c : (Fin d → ℤ) → ℝ) (u : Vec d → ℝ) {x : Vec d}
    (hx : ∀ i, |x i - h * (k₀ i : ℝ)| ≤ h / 2) :
    (u x - wh1_A h Z c x) ^ 2 ≤ ∑ k ∈ wh1_nbhd k₀, (u x - c k) ^ 2 := by
  rw [wh1_sub_A hh hZ c u hx]
  refine (wh1_sq_sum_le _ _ _ (fun k _ => wh1_chi_nonneg h k x) (wh1_chi_sum hh hx)).trans ?_
  exact Finset.sum_le_sum fun k _ =>
    mul_le_of_le_one_left (sq_nonneg _) (wh1_chi_le_one h k x)

/-- The integrated interpolation estimate on the cube of `k₀` (the squared form of the printed
`‖u - A‖² ≤ C ∑ ‖u - (u)_{Q⁺}‖²`), with arbitrary reals `c k`. -/
theorem wh1_lintegral_sub_A_le {h r : ℝ} (hh : 0 < h) (hr : 3 * h / 2 ≤ r)
    {k₀ : Fin d → ℤ} {Z : Finset (Fin d → ℤ)} (hZ : wh1_nbhd k₀ ⊆ Z) (c : (Fin d → ℤ) → ℝ)
    (u : Vec d → ℝ) (hu : AEMeasurable u (volume.restrict (wh1_box (wh1_pt h k₀) (h / 2)))) :
    ∫⁻ x in wh1_box (wh1_pt h k₀) (h / 2), ENNReal.ofReal ((u x - wh1_A h Z c x) ^ 2) ≤
      ∑ k ∈ wh1_nbhd k₀,
        ∫⁻ x in wh1_box (wh1_pt h k) r, ENNReal.ofReal ((u x - c k) ^ 2) := by
  have hm : MeasurableSet (wh1_box (wh1_pt h k₀) (h / 2)) := wh1_box_measurable _ _
  calc ∫⁻ x in wh1_box (wh1_pt h k₀) (h / 2), ENNReal.ofReal ((u x - wh1_A h Z c x) ^ 2)
      ≤ ∫⁻ x in wh1_box (wh1_pt h k₀) (h / 2),
          ∑ k ∈ wh1_nbhd k₀, ENNReal.ofReal ((u x - c k) ^ 2) := by
        refine setLIntegral_mono' hm fun x hx => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
        exact ENNReal.ofReal_le_ofReal (wh1_sq_sub_A_le hh hZ c u (wh1_cell_le hx))
    _ = ∑ k ∈ wh1_nbhd k₀,
          ∫⁻ x in wh1_box (wh1_pt h k₀) (h / 2), ENNReal.ofReal ((u x - c k) ^ 2) :=
        lintegral_finsetSum' _ fun k _ =>
          ((hu.sub aemeasurable_const).pow_const 2).ennreal_ofReal
    _ ≤ _ := by
        refine Finset.sum_le_sum fun k hk => lintegral_mono_set ?_
        refine (wh1_box_subset_nbhd hh hk (h / 2)).trans (wh1_box_mono _ ?_)
        linarith only [hr]

end SuperdiffusionCLT.Section7
