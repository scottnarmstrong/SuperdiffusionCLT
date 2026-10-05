/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.InteriorPointwiseD

/-!
# Interior pointwise oscillation: the deterministic conclusion

The proof of `l.Dirichlet.interior.pointwise`.

* `ip_dg_real`, `ip_poisson`: the interior estimate for `-σ Δ uhom = f` (De Giorgi on the cells of a
  tiling of `y + □_{k-1}`, the cubes around the cells staying in the ball of radius `3^k / 5` inside
  the rounded cube).
* `ip_step1`, `ip_step2`: from the comparison `‖u - uhom‖_{L^∞(V)}` to the oscillation of `u` on
  `y + □_n`, `k = n + 1`.
* `ip_final_det`: the oscillation estimate between the scales `n` and `m`, from the approximation at
  the scale `k = n + 1` and the Lipschitz estimate between the scales `k` and `m`.  (The printed
  proof takes `k = m ∧ (n + k₀ + 3)`; the constant-coefficient interior estimate has no decay
  requirement here, so `k = n + 1` serves.)
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **De Giorgi for the Poisson equation on a cube, in real form.** -/
theorem ip_dg_real [NeZero d] (hd : 2 ≤ d) :
    ∃ CDG : ℝ, 0 < CDG ∧ ∀ {z : Vec d} {m : ℕ} {σ F : ℝ}, 0 < σ → 0 ≤ F →
      ∀ (w : H1Function (shiftCube z (m : ℤ))) {f : Vec d → ℝ}, Measurable f → (∀ x, |f x| ≤ F) →
      IsWeakSolutionOn (fun _ => σ • (1 : Mat d)) (shiftCube z (m : ℤ)) w f (fun _ => 0) →
      ∀ c : ℝ, ∀ᵐ x ∂(volume.restrict (Metric.ball z ((3 : ℝ) ^ m / 4))),
        |w.toFun x - c| ≤ CDG * (lipL2 (shiftCube z (m : ℤ)) (fun x => w.toFun x - c) +
          (3 : ℝ) ^ (2 * m) / σ * F) := by
  obtain ⟨CDG, hCDG, H⟩ := ip_cell_dg hd
  refine ⟨CDG, hCDG, ?_⟩
  intro z m σ F hσ hF w f hfm hfb hw c
  have hEll : IsEllipticFieldOn σ σ (shiftCube z (m : ℤ)) (fun _ => σ • (1 : Mat d)) :=
    isEllipticFieldOn_constantCoeffField (rc_isOpen_shiftCube z _).measurableSet
      (isEllipticMatrix_scalarMatrix hσ)
  have hDG := H z m hEll f w c hw
  rw [div_self hσ.ne', Real.one_rpow, mul_one] at hDG
  have hfinQ : IsFiniteMeasure (volume.restrict (shiftCube z (m : ℤ))) :=
    ⟨by simpa using (ip_volume_shiftCube_ne z m).2.lt_top⟩
  have hmem : MemLp (fun x => w.toFun x - c) 2 (volume.restrict (shiftCube z (m : ℤ))) :=
    w.memL2.sub (memLp_const c)
  have hne : lpBar (shiftCube z (m : ℤ)) 2 (fun x => w.toFun x - c) ≠ ⊤ :=
    lip_lpBar_ne_top (ip_volume_shiftCube_ne z m).1 hmem
  have hfF : eLpNorm f ⊤ (volume.restrict (shiftCube z (m : ℤ))) ≤ ENNReal.ofReal F := by
    rw [eLpNorm_exponent_top hfm.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hfb x)
  have hl0 : 0 ≤ lipL2 (shiftCube z (m : ℤ)) (fun x => w.toFun x - c) := ENNReal.toReal_nonneg
  have hS0 : 0 ≤ CDG * (lipL2 (shiftCube z (m : ℤ)) (fun x => w.toFun x - c) +
      (3 : ℝ) ^ (2 * m) / σ * F) := by positivity
  refine ip_ae_of_eLpNorm hS0 (hDG.trans ?_)
  have e : lpBar (shiftCube z (m : ℤ)) 2 (fun x => w.toFun x - c) =
      ENNReal.ofReal (lipL2 (shiftCube z (m : ℤ)) (fun x => w.toFun x - c)) :=
    (ENNReal.ofReal_toReal hne).symm
  rw [e]
  calc ENNReal.ofReal CDG * (ENNReal.ofReal (lipL2 (shiftCube z (m : ℤ)) (fun x => w.toFun x - c)) +
        ENNReal.ofReal ((3 : ℝ) ^ (2 * m) / σ) * eLpNorm f ⊤ (volume.restrict (shiftCube z (m : ℤ))))
      ≤ ENNReal.ofReal CDG * (ENNReal.ofReal (lipL2 (shiftCube z (m : ℤ)) (fun x => w.toFun x - c)) +
        ENNReal.ofReal ((3 : ℝ) ^ (2 * m) / σ) * ENNReal.ofReal F) := by gcongr
    _ = ENNReal.ofReal (CDG * (lipL2 (shiftCube z (m : ℤ)) (fun x => w.toFun x - c) +
        (3 : ℝ) ^ (2 * m) / σ * F)) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hl0 (by positivity),
        ← ENNReal.ofReal_mul hCDG.le]

/-- The real normalized oscillation. -/
theorem ip_osc_eq {y : Vec d} {k : ℕ} {v : Vec d → ℝ} (hv : MemLp v 2 (volume.restrict (h1_cube y k))) :
    lipL2 (shiftCube y (k : ℤ)) (fun x => v x - h1_avg (h1_cube y k) v) = h1_l2 (h1_cube y k) v := by
  have e : lpBar (shiftCube y (k : ℤ)) 2 (fun x => v x - h1_avg (h1_cube y k) v) =
      ENNReal.ofReal (h1_l2 (h1_cube y k) v) := by
    rw [hr_shiftCube_eq]
    exact hr_lpBar_eq (h1_vol_cube_ne_top y k) (h1_vol_cube_pos y k) hv
  unfold lipL2
  rw [e, ENNReal.toReal_ofReal (show 0 ≤ h1_l2 (h1_cube y k) v from Real.sqrt_nonneg _)]

/-- The volume of the translated cube. -/
theorem ip_vol_shift (z : Vec d) (m : ℕ) :
    volume (shiftCube z (m : ℤ)) = ENNReal.ofReal (((3 : ℝ) ^ m) ^ d) := by
  rw [hr_shiftCube_eq]; exact h1_vol_cube z m

/-- **The interior estimate for the Poisson equation, from the comparison on the rounded cube.** -/
theorem ip_poisson [NeZero d] (hd : 2 ≤ d) :
    ∃ CP : ℝ, 1 ≤ CP ∧ ∀ {y : Vec d} {k : ℕ}, 6 ≤ k → ∀ {V : Set (Vec d)}, IsOpen V →
      Metric.ball y ((3 : ℝ) ^ k / 5) ⊆ V → V ⊆ shiftCube y (k : ℤ) →
      ∀ {σ F E : ℝ}, 0 < σ → 0 ≤ F → 0 ≤ E → ∀ (uhom : H1Function V) {f' : Vec d → ℝ},
      Measurable f' → (∀ x, |f' x| ≤ F) →
      IsWeakSolutionOn (fun _ => σ • (1 : Mat d)) V uhom f' (fun _ => 0) →
      ∀ (u : H1Function (shiftCube y (k : ℤ))),
      (∀ᵐ x ∂(volume.restrict V), |u.toFun x - uhom.toFun x| ≤ E) →
      ∀ᵐ x ∂(volume.restrict (shiftCube y ((k - 1 : ℕ) : ℤ))),
        |u.toFun x - h1_avg (h1_cube y k) u.toFun| ≤
          E + CP * (h1_l2 (h1_cube y k) u.toFun + E + σ⁻¹ * (3 : ℝ) ^ (2 * k) * F) := by
  obtain ⟨CDG, hCDG, H⟩ := ip_dg_real hd
  set s27 : ℝ := Real.sqrt ((27 : ℝ) ^ d) with hs27
  have hs270 : 0 ≤ s27 := Real.sqrt_nonneg _
  refine ⟨max 1 (CDG * (s27 + 1)), le_max_left _ _, ?_⟩
  intro y k hk V hVo hball hVk σ F E hσ hF hE uhom f' hfm hfb hsol u hae
  set c : ℝ := h1_avg (h1_cube y k) u.toFun with hc
  set Om : ℝ := h1_l2 (h1_cube y k) u.toFun with hOm
  have hOm0 : 0 ≤ Om := Real.sqrt_nonneg _
  obtain ⟨i, hi⟩ : ∃ i : ℕ, k = i + 6 := ⟨k - 6, by omega⟩
  set CP : ℝ := max 1 (CDG * (s27 + 1)) with hCP
  have hCP1 : CDG * (s27 + 1) ≤ CP := le_max_right _ _
  have hcov : shiftCube y ((k - 1 : ℕ) : ℤ) ⊆
      ⋃ j : Fin d → ℤ, (l2b_cell (y + l2b_pt i j) i ∩ shiftCube y ((k - 1 : ℕ) : ℤ)) := by
    intro x hx
    obtain ⟨j, hj⟩ := ip_tiling y x i
    exact Set.mem_iUnion.2 ⟨j, hj, hx⟩
  refine ip_ae_cover hcov (fun j => ?_)
  by_cases hne : (l2b_cell (y + l2b_pt i j) i ∩ shiftCube y ((k - 1 : ℕ) : ℤ)).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]
    simp
  obtain ⟨x0, hx0c, hx0E⟩ := hne
  set z : Vec d := y + l2b_pt i j with hz
  have hT : (0 : ℝ) < 3 ^ i := by positivity
  have h3k : (3 : ℝ) ^ k = 729 * 3 ^ i := by rw [hi, pow_add]; norm_num; ring
  have h3k1 : (3 : ℝ) ^ (k - 1) = 243 * 3 ^ i := by
    have : k - 1 = i + 5 := by omega
    rw [this, pow_add]; norm_num; ring
  have h3k3 : (3 : ℝ) ^ (k - 3) = 27 * 3 ^ i := by
    have : k - 3 = i + 3 := by omega
    rw [this, pow_add]; norm_num; ring
  have hzy : dist z y ≤ (3 : ℝ) ^ (k - 1) / 2 + 3 ^ i / 2 := by
    have h1 := ip_cell_dist hx0c
    have h2 : dist x0 y < (3 : ℝ) ^ (k - 1) / 2 := by
      have := hx0E; rw [ip_shiftCube_ball, Metric.mem_ball] at this; exact this
    calc dist z y ≤ dist z x0 + dist x0 y := dist_triangle _ _ _
      _ ≤ _ := by rw [dist_comm]; linarith only [h1, h2.le]
  have hQsub : shiftCube z ((k - 3 : ℕ) : ℤ) ⊆ V := by
    refine Set.Subset.trans ?_ hball
    rw [ip_shiftCube_ball]
    refine ip_ball_sub ?_
    rw [h3k3]; rw [h3k1] at hzy; rw [h3k]
    linarith only [hzy, hT]
  have hQopen := rc_isOpen_shiftCube z ((k - 3 : ℕ) : ℤ)
  have hQk : shiftCube z ((k - 3 : ℕ) : ℤ) ⊆ shiftCube y (k : ℤ) := hQsub.trans hVk
  have hsolQ := hsol.restrict' hQopen hQsub
  have hdg := H hσ hF (uhom.restrict hQopen hQsub) hfm hfb hsolQ c
  have hfinK : IsFiniteMeasure (volume.restrict (shiftCube y (k : ℤ))) :=
    ⟨by simpa using (ip_volume_shiftCube_ne y k).2.lt_top⟩
  have hum2 : MemLp (fun x => u.toFun x - c) 2 (volume.restrict (shiftCube y (k : ℤ))) :=
    u.memL2.sub (memLp_const c)
  have hu2k : MemLp u.toFun 2 (volume.restrict (h1_cube y k)) := by
    rw [← hr_shiftCube_eq]; exact u.memL2
  have hvolQ : volume (shiftCube y (k : ℤ)) ≤
      ENNReal.ofReal (27 ^ d) * volume (shiftCube z ((k - 3 : ℕ) : ℤ)) := by
    rw [ip_vol_shift, ip_vol_shift, ← ENNReal.ofReal_mul (by positivity)]
    refine le_of_eq (congrArg _ ?_)
    rw [h3k, h3k3, show (729 : ℝ) = 27 * 27 by norm_num, mul_assoc, mul_pow, mul_pow]
  have ha : lipL2 (shiftCube z ((k - 3 : ℕ) : ℤ)) (fun x => u.toFun x - c) ≤
      s27 * lipL2 (shiftCube y (k : ℤ)) (fun x => u.toFun x - c) :=
    lipL2_mono_set (by positivity) hQk (ip_volume_shiftCube_ne z (k - 3)).1
      (ip_volume_shiftCube_ne y k).2 hvolQ hum2
  have hOme : lipL2 (shiftCube y (k : ℤ)) (fun x => u.toFun x - c) = Om := ip_osc_eq hu2k
  have haeQ : ∀ᵐ x ∂(volume.restrict (shiftCube z ((k - 3 : ℕ) : ℤ))), |uhom.toFun x - u.toFun x| ≤ E := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hQsub hae] with x hx
    rw [abs_sub_comm]; exact hx
  have hb : lipL2 (shiftCube z ((k - 3 : ℕ) : ℤ)) (fun x => uhom.toFun x - u.toFun x) ≤ E :=
    lipL2_le_of_ae_abs_le hE (ip_volume_shiftCube_ne z (k - 3)).1 (ip_volume_shiftCube_ne z (k - 3)).2 haeQ
  have hfQ : MemLp (fun x => u.toFun x - c) 2 (volume.restrict (shiftCube z ((k - 3 : ℕ) : ℤ))) :=
    hum2.mono_measure (Measure.restrict_mono hQk le_rfl)
  have hgQ : MemLp (fun x => uhom.toFun x - u.toFun x) 2
      (volume.restrict (shiftCube z ((k - 3 : ℕ) : ℤ))) :=
    (uhom.memL2.mono_measure (Measure.restrict_mono hQsub le_rfl)).sub
      (u.memL2.mono_measure (Measure.restrict_mono hQk le_rfl))
  have hsum := lipL2_add_le (ip_volume_shiftCube_ne z (k - 3)).1 (ip_volume_shiftCube_ne z (k - 3)).2 hfQ hgQ
  have hfun : (fun x => (uhom.restrict hQopen hQsub).toFun x - c) =
      fun x => (u.toFun x - c) + (uhom.toFun x - u.toFun x) := by
    funext x; simp [H1Function.restrict]
  have hw : lipL2 (shiftCube z ((k - 3 : ℕ) : ℤ)) (fun x => (uhom.restrict hQopen hQsub).toFun x - c) ≤
      s27 * Om + E := by
    rw [hfun]
    rw [hOme] at ha
    linarith only [hsum, ha, hb]
  have hS27 : 0 ≤ CDG * (lipL2 (shiftCube z ((k - 3 : ℕ) : ℤ)) (fun x => (uhom.restrict hQopen hQsub).toFun x - c) +
      (3 : ℝ) ^ (2 * (k - 3)) / σ * F) := by
    have : 0 ≤ lipL2 (shiftCube z ((k - 3 : ℕ) : ℤ)) (fun x => (uhom.restrict hQopen hQsub).toFun x - c) :=
      ENNReal.toReal_nonneg
    positivity
  have hbd2 : CDG * (lipL2 (shiftCube z ((k - 3 : ℕ) : ℤ)) (fun x => (uhom.restrict hQopen hQsub).toFun x - c) +
      (3 : ℝ) ^ (2 * (k - 3)) / σ * F) ≤ CP * (Om + E + σ⁻¹ * (3 : ℝ) ^ (2 * k) * F) := by
    have h1 : (3 : ℝ) ^ (2 * (k - 3)) / σ * F ≤ σ⁻¹ * (3 : ℝ) ^ (2 * k) * F := by
      have : (3 : ℝ) ^ (2 * (k - 3)) ≤ 3 ^ (2 * k) := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [div_eq_inv_mul]
      gcongr
    have h2 : lipL2 (shiftCube z ((k - 3 : ℕ) : ℤ)) (fun x => (uhom.restrict hQopen hQsub).toFun x - c) +
        (3 : ℝ) ^ (2 * (k - 3)) / σ * F ≤ (s27 + 1) * (Om + E + σ⁻¹ * (3 : ℝ) ^ (2 * k) * F) := by
      have hs : 0 ≤ σ⁻¹ * (3 : ℝ) ^ (2 * k) * F := by positivity
      nlinarith only [hw, h1, hOm0, hE, hs, hs270]
    calc CDG * (_ + _) ≤ CDG * ((s27 + 1) * (Om + E + σ⁻¹ * (3 : ℝ) ^ (2 * k) * F)) :=
          mul_le_mul_of_nonneg_left h2 hCDG.le
      _ = (CDG * (s27 + 1)) * (Om + E + σ⁻¹ * (3 : ℝ) ^ (2 * k) * F) := by ring
      _ ≤ CP * (Om + E + σ⁻¹ * (3 : ℝ) ^ (2 * k) * F) :=
          mul_le_mul_of_nonneg_right hCP1 (by positivity)
  have hcb : l2b_cell z i ∩ shiftCube y ((k - 1 : ℕ) : ℤ) ⊆ Metric.ball z ((3 : ℝ) ^ (k - 3) / 4) := by
    intro x hx
    rw [Metric.mem_ball]
    have := ip_cell_dist hx.1
    rw [h3k3]; linarith only [this, hT]
  have hcV : l2b_cell z i ∩ shiftCube y ((k - 1 : ℕ) : ℤ) ⊆ V := by
    intro x hx
    have hxQ : x ∈ shiftCube z ((k - 3 : ℕ) : ℤ) := by
      rw [ip_shiftCube_ball]
      exact Metric.ball_subset_ball (by rw [h3k3]; linarith only [hT]) (hcb hx)
    exact hQsub hxQ
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hcb hdg,
    ae_restrict_of_ae_restrict_of_subset hcV hae] with x h1 h2
  have e : u.toFun x - c = (u.toFun x - uhom.toFun x) + (uhom.toFun x - c) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h1' : |uhom.toFun x - c| ≤ CP * (Om + E + σ⁻¹ * (3 : ℝ) ^ (2 * k) * F) :=
    h1.trans hbd2
  linarith only [h1', h2]

/-- **Oscillation about the average, in `L^∞`.** -/
theorem ip_step2 {y : Vec d} {n : ℕ} {u : Vec d → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict (shiftCube y (n : ℤ)))) {c M : ℝ} (hM : 0 ≤ M)
    (h : ∀ᵐ x ∂(volume.restrict (shiftCube y (n : ℤ))), |u x - c| ≤ M) :
    eLpNorm (fun x => u x - ⨍ z in shiftCube y (n : ℤ), u z) ⊤
        (volume.restrict (shiftCube y (n : ℤ))) ≤ ENNReal.ofReal (2 * M) := by
  rw [hr_shiftCube_eq] at hu h ⊢
  rw [hr_avg_eq]
  have hbd : MemLp u ⊤ (volume.restrict (h1_cube y n)) := by
    have := h1_finite_restrict (h1_vol_cube_ne_top y n)
    refine MemLp.of_bound hu (|c| + M) ?_
    filter_upwards [h] with x hx
    rw [Real.norm_eq_abs]
    have := abs_add_le (u x - c) c
    simp only [sub_add_cancel] at this
    linarith only [this, hx]
  have hfin := h1_finite_restrict (h1_vol_cube_ne_top y n)
  have hmem : MemLp (fun x => u x - h1_avg (h1_cube y n) u) ⊤ (volume.restrict (h1_cube y n)) :=
    hbd.sub (memLp_const _)
  have hl := h1_osc_two (h1_vol_cube_ne_top y n) (h1_vol_cube_pos y n) hbd hM h
  have hne : eLpNorm (fun x => u x - h1_avg (h1_cube y n) u) ⊤ (volume.restrict (h1_cube y n)) ≠ ⊤ :=
    hmem.eLpNorm_ne_top
  calc eLpNorm (fun x => u x - h1_avg (h1_cube y n) u) ⊤ (volume.restrict (h1_cube y n))
      = ENNReal.ofReal (eLpNorm (fun x => u x - h1_avg (h1_cube y n) u) ⊤
          (volume.restrict (h1_cube y n))).toReal := (ENNReal.ofReal_toReal hne).symm
    _ ≤ ENNReal.ofReal (2 * M) := ENNReal.ofReal_le_ofReal hl

/-- **From the comparison on the rounded cube to the oscillation on `y + □_n`.** -/
theorem ip_step1 [NeZero d] (hd : 2 ≤ d) {CIA : ℝ} (hCIA : 1 ≤ CIA) {N0 : ℕ} (hN0 : 1 ≤ N0)
    (hdim : (d : ℝ) * (4 / 5 : ℝ) ^ (2 * N0) < 1) :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ {y : Vec d} {n : ℕ}, 5 ≤ n → ∀ {σ δ : ℝ}, 0 < σ → 0 ≤ δ → δ ≤ 1 →
      ∀ (uk : H1Function (shiftCube y ((n + 1 : ℕ) : ℤ))) {f : Vec d → ℝ},
      (∃ (f' : Vec d → ℝ) (uhom : H1Function (ia_V d N0 (n + 1) y)), Measurable f' ∧
        (∀ x, |f' x| ≤ (eLpNorm f ⊤ (volume.restrict (shiftCube y ((n + 1 : ℕ) : ℤ)))).toReal) ∧
        IsWeakSolutionOn (fun _ => σ • (1 : Mat d)) (ia_V d N0 (n + 1) y) uhom f' (fun _ => 0) ∧
        eLpNorm (fun x => uk.toFun x - uhom.toFun x) ⊤ (volume.restrict (ia_V d N0 (n + 1) y)) ≤
          ENNReal.ofReal (CIA * δ * (h1_l2 (h1_cube y (n + 1)) uk.toFun +
            σ⁻¹ * (3 : ℝ) ^ (2 * (n + 1)) *
              (eLpNorm f ⊤ (volume.restrict (shiftCube y ((n + 1 : ℕ) : ℤ)))).toReal))) →
      ∀ᵐ x ∂(volume.restrict (shiftCube y (n : ℤ))),
        |uk.toFun x - h1_avg (h1_cube y (n + 1)) uk.toFun| ≤ C1 * (h1_l2 (h1_cube y (n + 1)) uk.toFun +
          σ⁻¹ * (3 : ℝ) ^ (2 * (n + 1)) *
            (eLpNorm f ⊤ (volume.restrict (shiftCube y ((n + 1 : ℕ) : ℤ)))).toReal) := by
  obtain ⟨CP, hCP, HP⟩ := ip_poisson hd
  refine ⟨CIA + CP * (1 + CIA), by nlinarith only [hCIA, hCP], ?_⟩
  intro y n hn σ δ hσ hδ0 hδ1 uk f ⟨f', uhom, hf'm, hf'b, hhom, hbd⟩
  set F : ℝ := (eLpNorm f ⊤ (volume.restrict (shiftCube y ((n + 1 : ℕ) : ℤ)))).toReal with hF
  have hF0 : 0 ≤ F := ENNReal.toReal_nonneg
  set Om : ℝ := h1_l2 (h1_cube y (n + 1)) uk.toFun with hOm
  have hOm0 : 0 ≤ Om := Real.sqrt_nonneg _
  set R : ℝ := Om + σ⁻¹ * (3 : ℝ) ^ (2 * (n + 1)) * F with hR
  have hR0 : 0 ≤ R := by positivity
  have hE0 : 0 ≤ CIA * δ * R := by
    have : 0 ≤ CIA := by linarith only [hCIA]
    positivity
  have hae : ∀ᵐ x ∂(volume.restrict (ia_V d N0 (n + 1) y)), |uk.toFun x - uhom.toFun x| ≤ CIA * δ * R :=
    ip_ae_of_eLpNorm hE0 hbd
  have h3pos : (0 : ℝ) < 3 ^ (n + 1) := by positivity
  have hP := HP (y := y) (k := n + 1) (by omega) (ia_V_isOpen (n + 1) y)
    (ia_ball_subset_V hN0 hdim (n + 1) y)
    (by
      refine (ia_V_subset_ball hN0 (n + 1) y).trans ?_
      rw [ip_shiftCube_ball]
      exact Metric.ball_subset_ball (by linarith only [h3pos])) hσ hF0 hE0 uhom hf'm hf'b hhom uk hae
  have hnn : n + 1 - 1 = n := by omega
  rw [hnn] at hP
  filter_upwards [hP] with x hx
  refine hx.trans ?_
  have hCIA0 : 0 ≤ CIA := by linarith only [hCIA]
  have hEx : 0 ≤ CIA * R := by positivity
  have hE1 : CIA * δ * R ≤ CIA * R := by
    nlinarith only [hδ1, hδ0, hEx, hR0]
  have hRR : Om + CIA * δ * R + σ⁻¹ * (3 : ℝ) ^ (2 * (n + 1)) * F ≤ R + CIA * R := by
    rw [hR] at hE1 ⊢
    linarith only [hE1]
  calc CIA * δ * R + CP * (Om + CIA * δ * R + σ⁻¹ * (3 : ℝ) ^ (2 * (n + 1)) * F)
      ≤ CIA * R + CP * (R + CIA * R) := add_le_add hE1 (mul_le_mul_of_nonneg_left hRR (by linarith only [hCP]))
    _ = (CIA + CP * (1 + CIA)) * R := by ring

/-- The real algebra of the comparison between the scales `n + 1` and `m`. -/
theorem ip_alg_final {CL q σk σm Omk Omm Fk Fm Tk Tm : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hσk : 0 < σk) (hσm : 0 < σm) (hσ : σm ≤ 2 * σk) (hFk : 0 ≤ Fk) (hFkm : Fk ≤ Fm)
    (hTm : 0 < Tm) (hTk : Tk = q ^ 2 * Tm) (hOmm : 0 ≤ Omm)
    (hl : Omk ≤ CL * q * (Omm + σm⁻¹ * Tm * Fm)) :
    Omk + σk⁻¹ * Tk * Fk ≤ (CL + 2) * q * (Omm + σm⁻¹ * Tm * Fm) := by
  have hFm : 0 ≤ Fm := hFk.trans hFkm
  have hX : 0 ≤ σm⁻¹ * Tm * Fm := by positivity
  have hi : σk⁻¹ ≤ 2 * σm⁻¹ := by
    rw [inv_le_comm₀ hσk (by positivity), mul_inv, inv_inv]
    linarith only [hσ]
  have h1 : σk⁻¹ * Tk * Fk ≤ 2 * σm⁻¹ * (q ^ 2 * Tm) * Fm := by
    rw [hTk]
    have : σk⁻¹ * (q ^ 2 * Tm) ≤ 2 * σm⁻¹ * (q ^ 2 * Tm) :=
      mul_le_mul_of_nonneg_right hi (by positivity)
    calc σk⁻¹ * (q ^ 2 * Tm) * Fk ≤ 2 * σm⁻¹ * (q ^ 2 * Tm) * Fk :=
          mul_le_mul_of_nonneg_right this hFk
      _ ≤ 2 * σm⁻¹ * (q ^ 2 * Tm) * Fm := mul_le_mul_of_nonneg_left hFkm (by positivity)
  have h2 : 2 * σm⁻¹ * (q ^ 2 * Tm) * Fm ≤ 2 * q * (σm⁻¹ * Tm * Fm) := by
    have : q ^ 2 ≤ q := by nlinarith only [hq, hq1]
    have e : 2 * σm⁻¹ * (q ^ 2 * Tm) * Fm = 2 * q ^ 2 * (σm⁻¹ * Tm * Fm) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right this hX
    nlinarith only [this]
  have hq0 := hq.le
  nlinarith only [hl, h1, h2, hX, hq0, hOmm, mul_nonneg hq0 hOmm, mul_nonneg hq0 hX]

theorem ip_rpow_ratio (n m : ℕ) :
    (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ))) = (3 : ℝ) ^ n / 3 ^ m := by
  rw [show -((m : ℝ) - (n : ℝ)) = (n : ℝ) - (m : ℝ) by ring, Real.rpow_sub (by norm_num),
    Real.rpow_natCast, Real.rpow_natCast]

/-- **The deterministic conclusion of the interior pointwise estimate.** -/
theorem ip_final_det [NeZero d] (hd : 2 ≤ d) {CIA CL : ℝ} (hCIA : 1 ≤ CIA) (hCL : 1 ≤ CL) {N0 : ℕ}
    (hN0 : 1 ≤ N0) (hdim : (d : ℝ) * (4 / 5 : ℝ) ^ (2 * N0) < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {y : Vec d} {n m : ℕ}, 5 ≤ n → n < m → ∀ {σk σm δ : ℝ}, 0 < σk → 0 < σm →
      σm ≤ 2 * σk → 0 ≤ δ → δ ≤ 1 →
      ∀ (u : H1Function (shiftCube y (m : ℤ))) {f : Vec d → ℝ},
      eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ))) ≠ ⊤ →
      (∀ hsub : shiftCube y ((n + 1 : ℕ) : ℤ) ⊆ shiftCube y (m : ℤ),
        ∃ (f' : Vec d → ℝ) (uhom : H1Function (ia_V d N0 (n + 1) y)), Measurable f' ∧
          (∀ x, |f' x| ≤ (eLpNorm f ⊤ (volume.restrict (shiftCube y ((n + 1 : ℕ) : ℤ)))).toReal) ∧
          IsWeakSolutionOn (fun _ => σk • (1 : Mat d)) (ia_V d N0 (n + 1) y) uhom f' (fun _ => 0) ∧
          eLpNorm (fun x => (u.restrict (rc_isOpen_shiftCube y ((n + 1 : ℕ) : ℤ)) hsub).toFun x -
              uhom.toFun x) ⊤ (volume.restrict (ia_V d N0 (n + 1) y)) ≤
            ENNReal.ofReal (CIA * δ * (h1_l2 (h1_cube y (n + 1)) u.toFun +
              σk⁻¹ * (3 : ℝ) ^ (2 * (n + 1)) *
                (eLpNorm f ⊤ (volume.restrict (shiftCube y ((n + 1 : ℕ) : ℤ)))).toReal))) →
      (n + 1 < m → ((3 : ℝ) ^ (n + 1))⁻¹ * h1_l2 (h1_cube y (n + 1)) u.toFun ≤
        CL * (((3 : ℝ) ^ m)⁻¹ * h1_l2 (h1_cube y m) u.toFun) +
          CL * (σm⁻¹ * (3 : ℝ) ^ m * (eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ)))).toReal)) →
      eLpNorm (fun x => u.toFun x - ⨍ z in shiftCube y (n : ℤ), u.toFun z) ⊤
          (volume.restrict (shiftCube y (n : ℤ))) ≤
        ENNReal.ofReal (C * (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ)))) *
          (lpBar (shiftCube y (m : ℤ)) 2 (fun x => u.toFun x - ⨍ z in shiftCube y (m : ℤ), u.toFun z) +
            ENNReal.ofReal (σm⁻¹ * (3 : ℝ) ^ (2 * (m : ℝ))) *
              eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ)))) := by
  obtain ⟨C1, hC1, H1⟩ := ip_step1 hd hCIA hN0 hdim
  refine ⟨2 * C1 * (CL + 2) * 3, by nlinarith only [hC1, hCL], ?_⟩
  intro y n m hn hnm σk σm δ hσk hσm hσ hδ0 hδ1 u f hfin hIA hlip
  have hsub : shiftCube y ((n + 1 : ℕ) : ℤ) ⊆ shiftCube y (m : ℤ) := by
    rw [ip_shiftCube_ball, ip_shiftCube_ball]
    have h3 : (3 : ℝ) ^ (n + 1) ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
    exact Metric.ball_subset_ball (by linarith only [h3])
  have hopen := rc_isOpen_shiftCube y ((n + 1 : ℕ) : ℤ)
  have hfink : eLpNorm f ⊤ (volume.restrict (shiftCube y ((n + 1 : ℕ) : ℤ))) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (eLpNorm_mono_measure f (Measure.restrict_mono hsub le_rfl))
  have hae := H1 (y := y) (n := n) hn hσk hδ0 hδ1 (u.restrict hopen hsub) (f := f) (hIA hsub)
  set Fk : ℝ := (eLpNorm f ⊤ (volume.restrict (shiftCube y ((n + 1 : ℕ) : ℤ)))).toReal with hFk
  set Fm : ℝ := (eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ)))).toReal with hFm
  set Omk : ℝ := h1_l2 (h1_cube y (n + 1)) u.toFun with hOmk
  set Omm : ℝ := h1_l2 (h1_cube y m) u.toFun with hOmm
  have hFk0 : 0 ≤ Fk := ENNReal.toReal_nonneg
  have hFm0 : 0 ≤ Fm := ENNReal.toReal_nonneg
  have hFkm : Fk ≤ Fm :=
    ENNReal.toReal_mono hfin (eLpNorm_mono_measure f (Measure.restrict_mono hsub le_rfl))
  have hOmk0 : 0 ≤ Omk := Real.sqrt_nonneg _
  have hOmm0 : 0 ≤ Omm := Real.sqrt_nonneg _
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  set q : ℝ := (3 : ℝ) ^ (n + 1) / 3 ^ m with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one h3m]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hTk : (3 : ℝ) ^ (2 * (n + 1)) = q ^ 2 * (3 : ℝ) ^ (2 * m) := by
    have e1 : (3 : ℝ) ^ (2 * (n + 1)) = ((3 : ℝ) ^ (n + 1)) ^ 2 := by rw [mul_comm, pow_mul]
    have e2 : (3 : ℝ) ^ (2 * m) = ((3 : ℝ) ^ m) ^ 2 := by rw [mul_comm, pow_mul]
    rw [e1, e2, hq, div_pow]; field_simp
  have hl : Omk ≤ CL * q * (Omm + σm⁻¹ * (3 : ℝ) ^ (2 * m) * Fm) := by
    by_cases hlt : n + 1 < m
    · have h := hlip hlt
      have h3k : (0 : ℝ) < 3 ^ (n + 1) := by positivity
      have h' := mul_le_mul_of_nonneg_left h h3k.le
      have e1 : (3 : ℝ) ^ (n + 1) * ((3 : ℝ) ^ (n + 1))⁻¹ * Omk = Omk := by
        rw [mul_inv_cancel₀ h3k.ne', one_mul]
      have e2 : (3 : ℝ) ^ (n + 1) * (CL * (((3 : ℝ) ^ m)⁻¹ * Omm) + CL * (σm⁻¹ * (3 : ℝ) ^ m * Fm)) =
          CL * q * (Omm + σm⁻¹ * (3 : ℝ) ^ (2 * m) * Fm) := by
        rw [hq]
        have : (3 : ℝ) ^ (2 * m) = (3 : ℝ) ^ m * (3 : ℝ) ^ m := by rw [two_mul, pow_add]
        rw [this]; field_simp
      rw [← mul_assoc, e1] at h'
      linarith only [h', e2]
    · have hm : m = n + 1 := by omega
      subst hm
      have hq' : q = 1 := by rw [hq]; exact div_self h3m.ne'
      rw [hq', mul_one]
      have : Omk = Omm := rfl
      rw [this]
      have hX : 0 ≤ σm⁻¹ * (3 : ℝ) ^ (2 * (n + 1)) * Fm := by positivity
      nlinarith only [hCL, hOmm0, hX]
  have halg := ip_alg_final (CL := CL) hq0 hq1 hσk hσm hσ hFk0 hFkm (by positivity) hTk hOmm0 hl
  set M : ℝ := C1 * (Omk + σk⁻¹ * (3 : ℝ) ^ (2 * (n + 1)) * Fk) with hM
  have hM0 : 0 ≤ M := by positivity
  have hae' : ∀ᵐ x ∂(volume.restrict (shiftCube y (n : ℤ))),
      |u.toFun x - h1_avg (h1_cube y (n + 1)) u.toFun| ≤ M := hae
  have hmeas : AEStronglyMeasurable u.toFun (volume.restrict (shiftCube y (n : ℤ))) :=
    u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono (by
      refine Set.Subset.trans ?_ hsub
      rw [ip_shiftCube_ball, ip_shiftCube_ball]
      exact Metric.ball_subset_ball (by
        have : (3 : ℝ) ^ n ≤ 3 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith only [this])) le_rfl)
  have h2 := ip_step2 hmeas hM0 hae'
  refine h2.trans ?_
  have hmm : MemLp u.toFun 2 (volume.restrict (h1_cube y m)) := by
    rw [← hr_shiftCube_eq]; exact u.memL2
  rw [ip_lpBar_osc hmm, ← ENNReal.ofReal_toReal hfin]
  have e3 : (3 : ℝ) ^ (2 * (m : ℝ)) = (3 : ℝ) ^ (2 * m) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  rw [e3, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (show 0 ≤ h1_l2 (h1_cube y m) u.toFun from Real.sqrt_nonneg _)
      (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [ip_rpow_ratio]
  have hqq : (3 : ℝ) ^ n / 3 ^ m * 3 = q := by rw [hq]; field_simp; ring
  have hC : 0 ≤ C1 := by linarith only [hC1]
  calc 2 * M = 2 * C1 * (Omk + σk⁻¹ * (3 : ℝ) ^ (2 * (n + 1)) * Fk) := by rw [hM]; ring
    _ ≤ 2 * C1 * ((CL + 2) * q * (Omm + σm⁻¹ * (3 : ℝ) ^ (2 * m) * Fm)) :=
        mul_le_mul_of_nonneg_left halg (by positivity)
    _ = 2 * C1 * (CL + 2) * 3 * ((3 : ℝ) ^ n / 3 ^ m) * (Omm + σm⁻¹ * (3 : ℝ) ^ (2 * m) * Fm) := by
        rw [← hqq]; ring

end SuperdiffusionCLT.Section7
