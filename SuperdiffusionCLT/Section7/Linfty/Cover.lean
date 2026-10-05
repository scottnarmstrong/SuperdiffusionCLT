/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.InnerBall
public import SuperdiffusionCLT.Section7.Lipschitz.Datum

/-!
# A fine grid covers a dilated smooth domain

For a smooth bounded domain `U` and `W = t • U`, every point of `W` lies within `3 ^ n` of a point
of the fine grid `3 ^ (n - s) ℤ^d` lying in `W`, as long as `3 ^ n ≤ c t`; and the pieces
`(z + □_j) ∩ W`, `z ∈ W`, `3 ^ j ≤ t`, have volume at least `c (3 ^ j) ^ d`.  Both are consequences
of the inner cube of a uniformly `C^{1,1}` domain.
-/

@[expose] public section

open MeasureTheory Homogenization Metric
open scoped Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **E1a — a fine grid reaches every point of a dilated smooth domain** from inside: every point
of `t • U` is within `3^n` of a point of `3^{n-s} ℤ^d ∩ t • U`. -/
theorem linf_fine_cover {U : Set (Vec d)} (hU : IsSmoothBoundedDomain U) :
    ∃ (s : ℕ) (c : ℝ), 0 < c ∧ ∀ (t : ℝ) (n : ℕ), 0 < t → (3 : ℝ) ^ n ≤ c * t →
      ∀ x ∈ t • U, ∃ k : Fin d → ℤ,
        (fun i => (3 : ℝ) ^ ((n : ℤ) - s) * (k i : ℝ)) ∈ t • U ∧
          ‖x - (fun i => (3 : ℝ) ^ ((n : ℤ) - s) * (k i : ℝ))‖ ≤ (3 : ℝ) ^ n := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, 1, one_pos, fun t n _ _ x hx => ⟨fun i => i.elim0, ?_, ?_⟩⟩
    · convert hx using 1
    · have : x - (fun i : Fin 0 => (3 : ℝ) ^ ((n : ℤ) - ((0 : ℕ) : ℤ)) * (((fun i : Fin 0 => i.elim0)
          i : ℤ) : ℝ)) = 0 := Subsingleton.elim _ _
      rw [this, norm_zero]
      positivity
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨r, M₁, M₂, D, hW⟩ := exists_isUniformC11Domain_of_isSmoothBoundedDomain hU
  obtain ⟨c₀, hc₀, -, hq⟩ := lip_inner_ball d M₁
  obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt (1 / c₀) (by norm_num : (1 : ℝ) < 3)
  refine ⟨s, r, hW.2.1, fun t n ht hn x hx => ?_⟩
  have hWt := hW.smul ht
  have hx' : x ∈ t • U := hx
  obtain ⟨q, hqb⟩ := hq (t • U) (t * r) (M₂ / t) (t * D) hWt x hx' ((3 : ℝ) ^ n)
    (by positivity) (by linarith only [hn, mul_comm r t])
  set ρ : ℝ := (3 : ℝ) ^ ((n : ℤ) - s) with hρ
  have hρpos : 0 < ρ := by positivity
  have hρ3 : ρ * (3 : ℝ) ^ s = (3 : ℝ) ^ n := by
    rw [hρ, zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
    field_simp
  have hρlt : ρ / 2 < c₀ * (3 : ℝ) ^ n := by
    have h1 : 1 < c₀ * (3 : ℝ) ^ s := by
      rwa [div_lt_iff₀ hc₀, mul_comm] at hs
    have h2 : ρ < c₀ * (3 : ℝ) ^ n := by
      rw [← hρ3]
      nlinarith only [h1, hρpos]
    linarith only [h2, hρpos]
  refine ⟨fun i => round (q i / ρ), ?_, ?_⟩
  · have hmem : (fun i => ρ * (round (q i / ρ) : ℝ)) ∈ ball q (c₀ * (3 : ℝ) ^ n) := by
      rw [mem_ball, dist_pi_lt_iff (by positivity)]
      intro i
      rw [Real.dist_eq]
      have h := abs_sub_round (q i / ρ)
      have : q i - ρ * (round (q i / ρ) : ℝ) = ρ * (q i / ρ - round (q i / ρ)) := by
        field_simp
      calc |ρ * (round (q i / ρ) : ℝ) - q i| = ρ * |q i / ρ - round (q i / ρ)| := by
            rw [abs_sub_comm, this, abs_mul, abs_of_pos hρpos]
        _ ≤ ρ * (1 / 2) := mul_le_mul_of_nonneg_left h hρpos.le
        _ < c₀ * (3 : ℝ) ^ n := by linarith only [hρlt]
    exact (hqb hmem).2
  · have hmem : (fun i => ρ * (round (q i / ρ) : ℝ)) ∈ ball q (c₀ * (3 : ℝ) ^ n) := by
      rw [mem_ball, dist_pi_lt_iff (by positivity)]
      intro i
      rw [Real.dist_eq]
      have h := abs_sub_round (q i / ρ)
      have : q i - ρ * (round (q i / ρ) : ℝ) = ρ * (q i / ρ - round (q i / ρ)) := by
        field_simp
      calc |ρ * (round (q i / ρ) : ℝ) - q i| = ρ * |q i / ρ - round (q i / ρ)| := by
            rw [abs_sub_comm, this, abs_mul, abs_of_pos hρpos]
        _ ≤ ρ * (1 / 2) := mul_le_mul_of_nonneg_left h hρpos.le
        _ < c₀ * (3 : ℝ) ^ n := by linarith only [hρlt]
    have := (hqb hmem).1
    rw [mem_ball, dist_comm, dist_eq_norm] at this
    exact this.le

/-- **E1b — uniform lower volume bound** for the pieces `(z + □_j) ∩ t • U`, `z ∈ t • U`,
`3^j ≤ t`. -/
theorem linf_density {U : Set (Vec d)} (hU : IsSmoothBoundedDomain U) :
    ∃ c : ℝ, 0 < c ∧ ∀ (t : ℝ) (j : ℕ), (3 : ℝ) ^ j ≤ t → ∀ z ∈ t • U,
      ENNReal.ofReal (c * ((3 : ℝ) ^ j) ^ d) ≤ volume (shiftCube z (j : ℤ) ∩ t • U) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1 / 2, by norm_num, fun t j _ z hz => ?_⟩
    have hz' : z ∈ shiftCube z (j : ℤ) ∩ t • U := by
      refine ⟨?_, hz⟩
      rw [lip_datum_shiftCube_eq]
      exact mem_ball_self (by positivity)
    have hu : shiftCube z (j : ℤ) ∩ t • U = Set.univ :=
      Set.eq_univ_of_forall fun y => by
        rw [Subsingleton.elim y z]; exact hz'
    rw [hu, pow_zero, mul_one]
    rw [volume_pi, Measure.pi_univ]
    simp
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨r, M₁, M₂, D, hW⟩ := exists_isUniformC11Domain_of_isSmoothBoundedDomain hU
  obtain ⟨c₀, hc₀, -, hq⟩ := lip_inner_ball d M₁
  have hm : 0 < min (1 / 2 : ℝ) r := lt_min (by norm_num) hW.2.1
  refine ⟨(2 * c₀ * min (1 / 2 : ℝ) r) ^ d, by positivity, fun t j hj z hz => ?_⟩
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hj
  have hWt := hW.smul ht
  have hz' : z ∈ t • U := hz
  set ρ : ℝ := min ((3 : ℝ) ^ j / 2) (t * r) with hρ
  have hρpos : 0 < ρ := lt_min (by positivity) (mul_pos ht hW.2.1)
  obtain ⟨q, hqb⟩ := hq (t • U) (t * r) (M₂ / t) (t * D) hWt z hz' ρ hρpos (min_le_right _ _)
  have hρge : min (1 / 2 : ℝ) r * (3 : ℝ) ^ j ≤ ρ := by
    refine le_min ?_ ?_
    · nlinarith only [min_le_left (1 / 2 : ℝ) r, pow_pos (by norm_num : (0 : ℝ) < 3) j]
    · calc min (1 / 2 : ℝ) r * (3 : ℝ) ^ j ≤ r * t :=
            mul_le_mul (min_le_right _ _) hj (by positivity) hW.2.1.le
        _ = t * r := mul_comm _ _
  have hsub : ball q (c₀ * ρ) ⊆ shiftCube z (j : ℤ) ∩ t • U := by
    intro y hy
    obtain ⟨h1, h2⟩ := hqb hy
    refine ⟨?_, h2⟩
    rw [lip_datum_shiftCube_eq, zpow_natCast]
    exact ball_subset_ball (min_le_left _ _) h1
  calc ENNReal.ofReal ((2 * c₀ * min (1 / 2 : ℝ) r) ^ d * ((3 : ℝ) ^ j) ^ d)
      ≤ ENNReal.ofReal ((2 * (c₀ * ρ)) ^ d) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_pow]
        apply pow_le_pow_left₀ (by positivity)
        nlinarith only [hρge, hc₀]
    _ = volume (ball q (c₀ * ρ)) := by
        rw [Real.volume_pi_ball q (by positivity), Fintype.card_fin]
    _ ≤ _ := measure_mono hsub

/-- Witness: on the unit Euclidean ball, dilated by `t = 3`, both statements apply, and the
grid point of the first is produced for the centre. -/
example [NeZero d] :
    (∃ (s : ℕ) (c : ℝ), 0 < c ∧ ∀ (t : ℝ) (n : ℕ), 0 < t → (3 : ℝ) ^ n ≤ c * t →
      ∀ x ∈ t • Section6.euclidBall (d := d) 1, ∃ k : Fin d → ℤ,
        (fun i => (3 : ℝ) ^ ((n : ℤ) - s) * (k i : ℝ)) ∈ t • Section6.euclidBall (d := d) 1 ∧
          ‖x - (fun i => (3 : ℝ) ^ ((n : ℤ) - s) * (k i : ℝ))‖ ≤ (3 : ℝ) ^ n) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ z ∈ (3 : ℝ) • Section6.euclidBall (d := d) 1,
      ENNReal.ofReal (c * ((3 : ℝ) ^ 1) ^ d) ≤
        volume (shiftCube z ((1 : ℕ) : ℤ) ∩ (3 : ℝ) • Section6.euclidBall (d := d) 1)) := by
  have hU := isSmoothBoundedDomain_euclidBall (d := d)
  refine ⟨linf_fine_cover hU, ?_⟩
  obtain ⟨c, hc, h⟩ := linf_density hU
  exact ⟨c, hc, fun z hz => h 3 1 (by norm_num) z hz⟩

end SuperdiffusionCLT.Section7
