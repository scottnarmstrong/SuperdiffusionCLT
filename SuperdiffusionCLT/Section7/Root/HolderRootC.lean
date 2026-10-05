/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.HolderRootB
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxCount
public import SuperdiffusionCLT.Section7.Root.HolderRoot
public import SuperdiffusionCLT.Section7.Root.HolderIterationB

/-!
# One block of the interior estimate for a solution on a ball

A solution on the ball `B_R` restricts to every translated cube `y + □_m ⊆ B_R`; the interior
estimate on the cube then gives, in real terms,
`‖u - (u)_{y+□_n}‖_{L^∞(y+□_n)} ≤ C₀ 3^{-(m-n)} (‖u - (u)_{y+□_m}‖_{L̲²} + shom_m⁻¹ 3^{2m} ‖f‖_{L^∞})`
together with the boundedness of `u` on the inner cube.
-/

@[expose] public section

open MeasureTheory Homogenization SuperdiffusionCLT.Section6
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **One block, in real terms.** -/
theorem hr_step {a : CoeffField d} {shom : ℕ → ℝ} {C0 c N Lhat X0 ε ρ : ℝ} {A : ℕ} {R : ℝ}
    (hIP : ∀ m n : ℕ, n < m →
      ((m : ℝ) - (n : ℝ)) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) ≤ c →
      Lhat ≤ (nK N n : ℝ) → X0 ≤ (3 : ℝ) ^ nK N n →
      ∀ y ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + A)),
        ∀ (f : Vec d → ℝ) (u : H1Function (shiftCube y (m : ℤ))),
          IsWeakSolutionOn a (shiftCube y (m : ℤ)) u f (fun _ => 0) →
          eLpNorm (fun x => u.toFun x - ⨍ z in shiftCube y (n : ℤ), u.toFun z) ⊤
              (volume.restrict (shiftCube y (n : ℤ))) ≤
            ENNReal.ofReal (C0 * (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ)))) *
              (lpBar (shiftCube y (m : ℤ)) 2
                  (fun x => u.toFun x - ⨍ z in shiftCube y (m : ℤ), u.toFun z) +
                ENNReal.ofReal ((shom m)⁻¹ * (3 : ℝ) ^ (2 * (m : ℝ))) *
                  eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ)))))
    (hR : 0 < R) {m n : ℕ} (hnm : n < m)
    (hδ : ((m : ℝ) - (n : ℝ)) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) ≤ c)
    (hL : Lhat ≤ (nK N n : ℝ)) (hX : X0 ≤ (3 : ℝ) ^ nK N n) (hs : 0 < shom m)
    {y : Vec d} (hy : y ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + A)))
    (hsub : h1_cube y m ⊆ euclidBall (d := d) R) (hC0 : 0 ≤ C0)
    {f : Vec d → ℝ} (hf : eLpNorm f ⊤ (volume.restrict (euclidBall (d := d) R)) ≠ ⊤)
    (u : H1Function (euclidBall (d := d) R))
    (hu : IsWeakSolutionOn a (euclidBall (d := d) R) u f (fun _ => 0)) :
    MemLp u.toFun ⊤ (volume.restrict (h1_cube y n)) ∧
      h1_linf (h1_cube y n) u.toFun (h1_avg (h1_cube y n) u.toFun) ≤
        C0 * (3 : ℝ) ^ (-((m : ℤ) - (n : ℤ))) *
          (h1_l2 (h1_cube y m) u.toFun + (shom m)⁻¹ * (3 : ℝ) ^ (2 * (m : ℝ)) *
            (eLpNorm f ⊤ (volume.restrict (h1_cube y m))).toReal) := by
  have hsub' : shiftCube y (m : ℤ) ⊆ euclidBall (d := d) R := by
    rw [hr_shiftCube_eq]; exact hsub
  have hres := wh2_isWeakSolutionOn_restrict (rc_isOpen_shiftCube y (m : ℤ)) hsub' hu
  have hI := hIP m n hnm hδ hL hX y hy f
    (u.restrict (rc_isOpen_shiftCube y (m : ℤ)) hsub') hres
  simp only [H1Function.restrict] at hI
  rw [hr_shiftCube_eq, hr_shiftCube_eq] at hI
  simp only [hr_avg_eq] at hI
  have hfin := h1_vol_ball_ne_top (d := d) hR
  have hu2 : MemLp u.toFun 2 (volume.restrict (euclidBall (d := d) R)) := u.memL2
  have hcm : MemLp u.toFun 2 (volume.restrict (h1_cube y m)) :=
    hu2.mono_measure (Measure.restrict_mono hsub le_rfl)
  rw [hr_lpBar_eq (h1_vol_cube_ne_top y m) (h1_vol_cube_pos y m) hcm] at hI
  have hfm : eLpNorm f ⊤ (volume.restrict (h1_cube y m)) ≠ ⊤ :=
    ne_top_of_le_ne_top hf (eLpNorm_mono_measure f (Measure.restrict_mono hsub le_rfl))
  have hn3 : (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ))) = (3 : ℝ) ^ (-((m : ℤ) - (n : ℤ))) := by
    rw [← Real.rpow_intCast]; push_cast; rfl
  have hl2 : 0 ≤ h1_l2 (h1_cube y m) u.toFun := Real.sqrt_nonneg _
  have hpos : 0 ≤ (shom m)⁻¹ * (3 : ℝ) ^ (2 * (m : ℝ)) := by positivity
  rw [← ENNReal.ofReal_toReal hfm, ← ENNReal.ofReal_mul hpos, ← ENNReal.ofReal_add hl2
    (mul_nonneg hpos ENNReal.toReal_nonneg), ← ENNReal.ofReal_mul (by positivity), hn3] at hI
  set Bd : ℝ := C0 * (3 : ℝ) ^ (-((m : ℤ) - (n : ℤ))) *
    (h1_l2 (h1_cube y m) u.toFun + (shom m)⁻¹ * (3 : ℝ) ^ (2 * (m : ℝ)) *
      (eLpNorm f ⊤ (volume.restrict (h1_cube y m))).toReal) with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  have hne : eLpNorm (fun x => u.toFun x - h1_avg (h1_cube y n) u.toFun) ⊤
      (volume.restrict (h1_cube y n)) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hI
  have hmem : MemLp (fun x => u.toFun x - h1_avg (h1_cube y n) u.toFun) ⊤
      (volume.restrict (h1_cube y n)) := lt_top_iff_ne_top.2 hne
  refine ⟨?_, ?_⟩
  · have := h1_finite_restrict (h1_vol_cube_ne_top y n)
    have h := hmem.add (memLp_const (h1_avg (h1_cube y n) u.toFun))
    have e : ((fun x => u.toFun x - h1_avg (h1_cube y n) u.toFun) +
        fun _ => h1_avg (h1_cube y n) u.toFun) = u.toFun := by
      funext x; simp
    rwa [e] at h
  · unfold h1_linf
    exact ENNReal.toReal_le_of_le_ofReal hBd0 hI

/-- **Cube estimate by iteration of the one-block estimate** (centred cubes). -/
theorem hr_iterate {u : Vec d → ℝ} {R γ C0 φ : ℝ} {Nγ m₀ mT : ℕ} {shom : ℕ → ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hC0 : 1 ≤ C0) (hφ : 0 ≤ φ) (hN : 1 ≤ Nγ)
    (hq : C0 * (3 : ℝ) ^ (-(Nγ : ℤ)) ≤ 1 / 2 * (3 : ℝ) ^ (-γ * (Nγ : ℝ)))
    (hpos : ∀ k : ℕ, m₀ ≤ k → 0 < shom k)
    (hrat : ∀ k m : ℕ, m₀ ≤ k → k ≤ m → shom m ≤ 3 * (1 + ((m : ℝ) - k)) * shom k)
    (hstep : ∀ n k : ℕ, m₀ ≤ n → n < k → k - n ≤ Nγ → h1_cube (0 : Vec d) k ⊆ euclidBall (d := d) R →
      MemLp u ⊤ (volume.restrict (h1_cube (0 : Vec d) n)) ∧
        h1_linf (h1_cube (0 : Vec d) n) u (h1_avg (h1_cube (0 : Vec d) n) u) ≤
          C0 * (3 : ℝ) ^ (-((k : ℤ) - (n : ℤ))) *
            (h1_l2 (h1_cube (0 : Vec d) k) u + (shom k)⁻¹ * (3 : ℝ) ^ (2 * (k : ℝ)) * φ))
    {n m : ℕ} (hn : m₀ ≤ n) (hnm : n < m) (hmT : m ≤ mT)
    (hcube : h1_cube (0 : Vec d) m ⊆ euclidBall (d := d) R) :
    MemLp u ⊤ (volume.restrict (h1_cube (0 : Vec d) n)) ∧
      h1_linf (h1_cube (0 : Vec d) n) u (h1_avg (h1_cube (0 : Vec d) n) u) ≤
        2 * C0 * (3 : ℝ) ^ (γ * (Nγ : ℝ)) * (3 : ℝ) ^ (-γ * ((m : ℝ) - n)) *
          (h1_l2 (h1_cube (0 : Vec d) m) u +
            3 * ((shom mT)⁻¹ * (3 : ℝ) ^ (2 * (mT : ℝ)) * φ)) := by
  have hcm : ∀ k : ℕ, k ≤ m → h1_cube (0 : Vec d) k ⊆ euclidBall (d := d) R := by
    intro k hk x hx
    refine hcube ?_
    unfold h1_cube at hx ⊢
    exact Metric.ball_subset_ball (by
      have : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hk
      linarith only [this]) hx
  have hmem : MemLp u ⊤ (volume.restrict (h1_cube (0 : Vec d) n)) :=
    (hstep n (n + 1) hn (Nat.lt_succ_self n) (by omega) (hcm (n + 1) (by omega))).1
  refine ⟨hmem, ?_⟩
  set G : ℝ := (shom mT)⁻¹ * (3 : ℝ) ^ (2 * (mT : ℝ)) * φ with hG
  have hm₀m : m₀ ≤ m := hn.trans hnm.le
  have hshmT : 0 < shom mT := hpos mT (hm₀m.trans hmT)
  have hG0 : 0 ≤ G := by positivity
  set E : ℤ → ℝ := fun k => max (h1_linf (h1_cube (0 : Vec d) k.toNat) u
    (h1_avg (h1_cube (0 : Vec d) k.toNat) u)) (h1_l2 (h1_cube (0 : Vec d) k.toNat) u) with hE
  set D : ℤ → ℝ := fun k => h1_l2 (h1_cube (0 : Vec d) k.toNat) u with hD
  set F : ℤ → ℝ := fun k => max 0 ((shom k.toNat)⁻¹ * (3 : ℝ) ^ (2 * ((k.toNat : ℕ) : ℝ)) * φ) with hF
  have key := h1_iteration E D F C0 γ 3 G Nγ (m₀ : ℤ) (m : ℤ) (m : ℤ) (n : ℤ) hN hC0 hγ0
    (by norm_num) hG0 (fun k => Real.sqrt_nonneg _) (fun k => le_max_left _ _) le_rfl hq
    ?_ (fun k _ _ => le_max_right _ _) ?_ (by exact_mod_cast hnm) (by exact_mod_cast hn)
  · have h1 : h1_linf (h1_cube (0 : Vec d) n) u (h1_avg (h1_cube (0 : Vec d) n) u) ≤ E (n : ℤ) := by
      simp only [hE, Int.toNat_natCast]; exact le_max_left _ _
    refine h1.trans (key.trans ?_)
    simp only [hD, Int.toNat_natCast]
    have e : (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) = (m : ℝ) - n := by push_cast; ring
    rw [e]
  · intro n' k' hn' hnk hkM hkn
    obtain ⟨n1, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ n')
    obtain ⟨k1, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ k')
    have hn1 : m₀ ≤ n1 := by exact_mod_cast hn'
    have hnk1 : n1 < k1 := by exact_mod_cast hnk
    have hkm1 : k1 ≤ m := by exact_mod_cast hkM
    obtain ⟨hM, hb⟩ := hstep n1 k1 hn1 hnk1 (by omega) (hcm k1 hkm1)
    have hl : h1_l2 (h1_cube (0 : Vec d) n1) u ≤
        h1_linf (h1_cube (0 : Vec d) n1) u (h1_avg (h1_cube (0 : Vec d) n1) u) :=
      hr_l2_le_linf (h1_vol_cube_ne_top 0 n1) (h1_vol_cube_pos 0 n1) hM
    have hC3 : 0 ≤ C0 * (3 : ℝ) ^ (-((k1 : ℤ) - (n1 : ℤ))) := by positivity
    simp only [hE, hD, hF, Int.toNat_natCast]
    refine max_le (hb.trans ?_) (hl.trans (hb.trans ?_)) <;>
      exact mul_le_mul_of_nonneg_left (add_le_add_right
        (le_max_right _ _) _) hC3
  · intro k hk hkm
    obtain ⟨k1, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ k)
    have hk1 : m₀ ≤ k1 := by exact_mod_cast hk
    have hkm1 : k1 ≤ m := by exact_mod_cast hkm
    have hshk := hpos k1 hk1
    have hFb := hr_F_bound hγ1 (hkm1.trans hmT) hshk hshmT (hrat k1 mT hk1 (hkm1.trans hmT))
    have hexp : (3 : ℝ) ^ (-γ * ((mT : ℝ) - k1)) ≤ (3 : ℝ) ^ (-γ * (((m : ℤ) - (k1 : ℤ) : ℤ) : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (m : ℝ) ≤ mT := by exact_mod_cast hmT
      push_cast
      nlinarith only [this, hγ0]
    simp only [hF, Int.toNat_natCast]
    refine max_le (by positivity) ?_
    calc (shom k1)⁻¹ * (3 : ℝ) ^ (2 * (k1 : ℝ)) * φ
        ≤ (3 * (3 : ℝ) ^ (-γ * ((mT : ℝ) - k1)) * ((shom mT)⁻¹ * (3 : ℝ) ^ (2 * (mT : ℝ)))) * φ :=
          mul_le_mul_of_nonneg_right hFb hφ
      _ ≤ (3 * (3 : ℝ) ^ (-γ * (((m : ℤ) - (k1 : ℤ) : ℤ) : ℝ)) *
            ((shom mT)⁻¹ * (3 : ℝ) ^ (2 * (mT : ℝ)))) * φ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp (by norm_num)) (by positivity)) hφ
      _ = _ := by rw [hG]; ring

end SuperdiffusionCLT.Section7
