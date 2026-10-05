/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.InteriorDetB

/-!
# The interior large-scale Lipschitz estimate, deterministic form
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory

variable {d : ℕ}

private theorem lip_int_det_choose_k0 {C₁ : ℝ} (hC₁ : 1 ≤ C₁) :
    ∃ k₀ : ℕ, 3 ≤ k₀ ∧ C₁ * ((3 : ℝ)⁻¹) ^ k₀ ≤ 1 / 4 := by
  have hpos : (0 : ℝ) < 1 / (4 * C₁) := by
    have : (0 : ℝ) < 4 * C₁ := by linarith only [hC₁]
    positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : ((3 : ℝ)⁻¹) < 1)
  refine ⟨max n 3, le_max_right _ _, ?_⟩
  have h1 : ((3 : ℝ)⁻¹) ^ (max n 3) ≤ ((3 : ℝ)⁻¹) ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left _ _)
  have h2 : ((3 : ℝ)⁻¹) ^ (max n 3) < 1 / (4 * C₁) := lt_of_le_of_lt h1 hn
  have hC : (0 : ℝ) < C₁ := by linarith only [hC₁]
  rw [lt_div_iff₀ (by linarith only [hC₁])] at h2
  linarith only [h2]

/-- **The interior large-scale Lipschitz estimate, deterministic form**.
The field `a` is arbitrary; the blocks are assumed on the scales `[n, m]`.  The constants are
bound before the field; the smallness `c` is on `∑ δ`. -/
theorem lip_int_det (d : ℕ) [NeZero d] (Cin : ℝ) (hCin : 1 ≤ Cin) :
    ∃ (C c : ℝ) (k₀ : ℕ), 1 ≤ C ∧ 0 < c ∧
      ∀ (a : CoeffField d) (nu : ℝ) (s δ : ℕ → ℝ) (rc n m : ℕ),
        0 < nu → 1 ≤ rc → rc ≤ 2 → k₀ + 3 ≤ n → n ≤ m →
        (∀ k, n ≤ k → k ≤ m → 0 < s k ∧ s m ≤ 2 * s k ∧ s k ≤ 2 * s m) →
        (∀ k, n ≤ k → k ≤ m → 0 ≤ δ k) →
        ∑ k ∈ Finset.Icc n m, δ k ≤ c →
        (∀ k, n ≤ k → k ≤ m → LipCaccInt a nu (s k) Cin rc k ∧ LipHarmInt a (s k) (δ k) Cin k) →
        ∀ (f : Vec d → ℝ) (F : ℝ) (u : H1Function (Section6.engCube d m)),
          IsWeakSolutionOn a (Section6.engCube d m) u f (fun _ => 0) → 0 ≤ F →
          (∀ᵐ x ∂volume.restrict (Section6.engCube d m), |f x| ≤ F) →
          ∀ j, n ≤ j → j ≤ m →
            Section6.cubeFlat j u.toFun ≤
                C * (Section6.cubeFlat m u.toFun + (s m)⁻¹ * (3 : ℝ) ^ m * F) ∧
              (j + rc ≤ m →
                (Real.sqrt (s m))⁻¹ * Real.sqrt nu * Section6.cubeGradL2 j u.grad ≤
                  C * (Section6.cubeFlat m u.toFun + (s m)⁻¹ * (3 : ℝ) ^ m * F)) := by
  obtain ⟨Ch, hCh, hHA⟩ := Section6.eng_harmonic_affine d
  have hCin2 : 1 ≤ 2 * Cin := by linarith only [hCin]
  obtain ⟨C₁, hC₁, hstep⟩ := lip_int_step d (2 * Cin) Ch hCin2 hCh
  obtain ⟨k₀, hk₀3, hk₀⟩ := lip_int_det_choose_k0 hC₁
  obtain ⟨C₂, hC₂, hstep2⟩ := hstep k₀ hk₀3
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hCr : (1 : ℝ) ≤ (3 : ℝ) ^ (d + 2) := one_le_pow₀ (by norm_num)
  have hCs : 0 ≤ 2 * Real.sqrt 3 * (3 : ℝ) ^ (d + 2) := by positivity
  have hCa : 0 ≤ (2 * Real.sqrt 3)⁻¹ := by positivity
  obtain ⟨Cit, hCit, hit⟩ := lip_iteration (2 * Real.sqrt 3 * (3 : ℝ) ^ (d + 2))
    ((2 * Real.sqrt 3)⁻¹) ((3 : ℝ) ^ (d + 2)) hCs hCa hCr k₀
  set Cs : ℝ := 2 * Real.sqrt 3 * (3 : ℝ) ^ (d + 2) with hCsdef
  have hCs1 : 0 < 8 * (Cs + 1) := by linarith only [hCs]
  have hC₂0 : 0 < C₂ := by linarith only [hC₂]
  have hcpos : 0 < 1 / (8 * C₂ * (Cs + 1)) := by
    have : 0 < 8 * C₂ * (Cs + 1) := by
      have : 0 < Cs + 1 := by linarith only [hCs]
      positivity
    positivity
  have hCC : 1 ≤ Cit * C₂ := one_le_mul_of_one_le_of_one_le hCit hC₂
  refine ⟨2 * Cin * (Cit * C₂ + 1), 1 / (8 * C₂ * (Cs + 1)), k₀, ?_, hcpos, ?_⟩
  · have h1 : 1 ≤ Cit * C₂ + 1 := by linarith only [hCC]
    calc (1 : ℝ) ≤ 2 * Cin * 1 := by linarith only [hCin]
      _ ≤ 2 * Cin * (Cit * C₂ + 1) := by
        refine mul_le_mul_of_nonneg_left h1 (by linarith only [hCin])
  intro a nu s δ rc n m hnu hrc1 hrc2 hn hnm hs hδ hsum hblk f F u hu hF hfF
  have hsm : 0 < s m := by
    obtain ⟨h1, h2, h3⟩ := hs m hnm le_rfl
    exact h1
  have hX : 0 ≤ Section6.cubeFlat m u.toFun + (s m)⁻¹ * (3 : ℝ) ^ m * F := by
    have := Section6.cubeFlat_nonneg m u.toFun
    have h2 : 0 ≤ (s m)⁻¹ * (3 : ℝ) ^ m * F := by positivity
    linarith only [this, h2]
  -- part one, by the iteration
  have hP1 : ∀ j, n ≤ j → j ≤ m →
      Section6.cubeFlat j u.toFun ≤
        (Cit * C₂) * (Section6.cubeFlat m u.toFun + (s m)⁻¹ * (3 : ℝ) ^ m * F) := by
    have hmem : ∀ k, k ≤ m → MemLp u.toFun 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
      fun k hk => lip_int_det_memLp hk u
    have hit' := hit (P := Vec d) Section6.engNorm n m
      (fun j p => Section6.cubeFlat j (fun x => u.toFun x - vecDot p x))
      (fun j => Section6.cubeFlat j u.toFun) (fun k => C₂ * (s m)⁻¹ * (3 : ℝ) ^ k * F)
      (fun k => C₂ * max (δ (k + 1)) 0) 0 hnm
      (fun j p => Section6.cubeFlat_nonneg _ _) (fun p => Section6.engNorm_nonneg p)
      (fun k => by positivity) (fun k => mul_nonneg hC₂0.le (le_max_right _ _))
      ?step ?slope ?restr ?osc ?small
    · intro j hj1 hj2
      have h := hit' j hj1 hj2
      have e1 : (fun x => u.toFun x - vecDot (0 : Vec d) x) = u.toFun := by
        funext x; simp [vecDot]
      have e2 : Section6.engNorm (0 : Vec d) = 0 := by
        simp [Section6.engNorm, vecNormSq, vecDot]
      simp only [e1, e2, add_zero] at h
      have hS : ∑ k ∈ Finset.Icc (n + k₀) (m - 1), C₂ * (s m)⁻¹ * (3 : ℝ) ^ k * F ≤
          C₂ * ((s m)⁻¹ * (3 : ℝ) ^ m * F) := by
        have hg := lip_int_det_geom m (Finset.Icc (n + k₀) (m - 1)) (by
          intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega)
        have hc : 0 ≤ C₂ * ((s m)⁻¹ * F) := by positivity
        calc ∑ k ∈ Finset.Icc (n + k₀) (m - 1), C₂ * (s m)⁻¹ * (3 : ℝ) ^ k * F
            = C₂ * ((s m)⁻¹ * F) * ∑ k ∈ Finset.Icc (n + k₀) (m - 1), (3 : ℝ) ^ k := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
          _ ≤ C₂ * ((s m)⁻¹ * F) * (3 : ℝ) ^ m := mul_le_mul_of_nonneg_left hg hc
          _ = _ := by ring
      have hF0 := Section6.cubeFlat_nonneg m u.toFun
      have h3 : Section6.cubeFlat m u.toFun + ∑ k ∈ Finset.Icc (n + k₀) (m - 1),
          C₂ * (s m)⁻¹ * (3 : ℝ) ^ k * F ≤
          C₂ * (Section6.cubeFlat m u.toFun + (s m)⁻¹ * (3 : ℝ) ^ m * F) := by
        have : Section6.cubeFlat m u.toFun ≤ C₂ * Section6.cubeFlat m u.toFun := by
          calc _ = 1 * Section6.cubeFlat m u.toFun := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hC₂ hF0
        linarith only [this, hS]
      calc Section6.cubeFlat j u.toFun ≤ _ := h
        _ ≤ Cit * (C₂ * (Section6.cubeFlat m u.toFun + (s m)⁻¹ * (3 : ℝ) ^ m * F)) :=
          mul_le_mul_of_nonneg_left h3 (by linarith only [hCit])
        _ = _ := by ring
    · -- the one-step inequality
      intro k hk1 hk2 p
      have hk0 : k₀ ≤ k := by omega
      have hkm : k + 1 ≤ m := hk2
      obtain ⟨hsol, hfk⟩ := lip_int_det_restrict (a := a) hkm hu hfF
      have hblk' := hblk (k + 1) (by omega) hkm
      obtain ⟨hs1, hs2, hs3'⟩ := hs (k + 1) (by omega) hkm
      have hδk : 0 ≤ δ (k + 1) := hδ (k + 1) (by omega) hkm
      have hharm : LipHarmInt a (s m) (δ (k + 1)) (2 * Cin) (k + 1) :=
        hblk'.2.mono hsm hs2 hδk (by linarith only [hδk]) (by linarith only [hCin]) le_rfl
      obtain ⟨p', hp'⟩ := hstep2 a (s m) (δ (k + 1)) k hk0 hsm hδk
        (fun K l hl w gw hw => hHA K l hl w gw hw) hharm f F _ hsol hF hfk p
      refine ⟨p', ?_⟩
      have hδc : δ (k + 1) ≤ 1 / (8 * C₂ * (Cs + 1)) := by
        refine le_trans ?_ hsum
        exact Finset.single_le_sum (f := δ) (fun i hi => by
          rw [Finset.mem_Icc] at hi; exact hδ i hi.1 hi.2) (by rw [Finset.mem_Icc]; omega)
      have hC₂δ : C₂ * δ (k + 1) ≤ 1 / 4 := by
        have h1 : C₂ * δ (k + 1) ≤ C₂ * (1 / (8 * C₂ * (Cs + 1))) :=
          mul_le_mul_of_nonneg_left hδc hC₂0.le
        have h2 : C₂ * (1 / (8 * C₂ * (Cs + 1))) = 1 / (8 * (Cs + 1)) := by
          field_simp
        have h3 : 1 / (8 * (Cs + 1)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ hCs1 (by norm_num)]
          linarith only [hCs]
        linarith only [h1, h2, h3]
      have hmax : max (δ (k + 1)) 0 = δ (k + 1) := max_eq_left hδk
      have hΦ0 := Section6.cubeFlat_nonneg (k + 1) (fun x => u.toFun x - vecDot p x)
      have hcoef : C₁ * ((3 : ℝ)⁻¹) ^ k₀ + C₂ * δ (k + 1) ≤ 1 / 2 := by
        linarith only [hk₀, hC₂δ]
      have hfin := mul_le_mul_of_nonneg_right hcoef hΦ0
      show Section6.cubeFlat (k - k₀) (fun x => u.toFun x - vecDot p' x) ≤
        1 / 2 * Section6.cubeFlat (k + 1) (fun x => u.toFun x - vecDot p x) +
          C₂ * max (δ (k + 1)) 0 * Section6.engNorm p + C₂ * (s m)⁻¹ * (3 : ℝ) ^ k * F
      rw [hmax]
      have hp'' : Section6.cubeFlat (k - k₀) (fun x => u.toFun x - vecDot p' x) ≤
          (C₁ * ((3 : ℝ)⁻¹) ^ k₀ + C₂ * δ (k + 1)) *
              Section6.cubeFlat (k + 1) (fun x => u.toFun x - vecDot p x) +
            C₂ * δ (k + 1) * Section6.engNorm p + C₂ * (s m)⁻¹ * (3 : ℝ) ^ k * F := hp'
      linarith only [hp'', hfin]
    · -- slope comparison
      intro j hj1 hj2 p q
      have h1 := lip_int_det_slope (lip_int_det_memLp (by omega : j ≤ m) u) p q
      have h2 := lip_int_det_restr (f := u.toFun) (lip_int_det_memLp hj2 u) q
      have h3 : 0 ≤ 2 * Real.sqrt 3 := by positivity
      have h4 := mul_le_mul_of_nonneg_left h2 h3
      show Section6.engNorm p ≤ Section6.engNorm q +
        2 * Real.sqrt 3 * (3 : ℝ) ^ (d + 2) * (Section6.cubeFlat j (fun x => u.toFun x - vecDot p x) +
          Section6.cubeFlat (j + 1) (fun x => u.toFun x - vecDot q x))
      have h5 : 2 * Real.sqrt 3 * Section6.cubeFlat j (fun x => u.toFun x - vecDot p x) ≤
          2 * Real.sqrt 3 * (3 : ℝ) ^ (d + 2) *
            Section6.cubeFlat j (fun x => u.toFun x - vecDot p x) := by
        have := Section6.cubeFlat_nonneg j (fun x => u.toFun x - vecDot p x)
        have hle : (2 * Real.sqrt 3) * 1 ≤ (2 * Real.sqrt 3) * (3 : ℝ) ^ (d + 2) :=
          mul_le_mul_of_nonneg_left hCr h3
        calc _ = (2 * Real.sqrt 3) * 1 * Section6.cubeFlat j (fun x => u.toFun x - vecDot p x) := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hle this
      have h6 : 2 * Real.sqrt 3 * (3 : ℝ) ^ (d + 2) *
          Section6.cubeFlat (j + 1) (fun x => u.toFun x - vecDot q x) =
          2 * Real.sqrt 3 * ((3 : ℝ) ^ (d + 2) *
            Section6.cubeFlat (j + 1) (fun x => u.toFun x - vecDot q x)) := by ring
      linarith only [h1, h4, h5, h6]
    · -- restriction
      intro j hj1 hj2 p
      exact lip_int_det_restr (f := u.toFun) (lip_int_det_memLp hj2 u) p
    · -- oscillation
      intro j hj1 hj2 p
      exact lip_int_det_osc (lip_int_det_memLp hj2 u) p
    · -- smallness of the sum
      have hb : ∑ k ∈ Finset.Icc (n + k₀) (m - 1), C₂ * max (δ (k + 1)) 0 ≤
          C₂ * (1 / (8 * C₂ * (Cs + 1))) := by
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ hC₂0.le
        have hr := lip_int_det_reindex δ n m k₀ (by omega) hδ
        have : ∑ k ∈ Finset.Icc (n + k₀) (m - 1), max (δ (k + 1)) 0 =
            ∑ k ∈ Finset.Icc (n + k₀) (m - 1), δ (k + 1) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_Icc] at hk
          exact max_eq_left (hδ (k + 1) (by omega) (by omega))
        linarith only [this, hr, hsum]
      have h2 : C₂ * (1 / (8 * C₂ * (Cs + 1))) = 1 / (8 * (Cs + 1)) := by field_simp
      calc _ ≤ 1 / (8 * (Cs + 1)) * (8 * (Cs + 1)) :=
            mul_le_mul_of_nonneg_right (h2 ▸ hb) hCs1.le
        _ = 1 := by field_simp
  refine fun j hj1 hj2 => ⟨?_, fun hjr => ?_⟩
  · refine (hP1 j hj1 hj2).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hX
    have : 0 ≤ 2 * Cin * 1 := by linarith only [hCin]
    nlinarith only [hCin, hCC, this]
  · have hkm : j + rc ≤ m := hjr
    obtain ⟨hsol, hfk⟩ := lip_int_det_restrict (a := a) hkm hu hfF
    obtain ⟨hk1, hk2, hk3⟩ := hs (j + rc) (by omega) hkm
    have hcacc : LipCaccInt a nu (s m) (2 * Cin) rc (j + rc) :=
      ((hblk (j + rc) (by omega) hkm).1).mono hk1 hk3 hk2 (by linarith only [hCin]) le_rfl
    have h1 := hcacc f F _ hsol hF hfk
    have e : j + rc - rc = j := by omega
    rw [e] at h1
    have hsq : 0 < Real.sqrt (s m) := Real.sqrt_pos.2 hsm
    have hr : 0 ≤ (Real.sqrt (s m))⁻¹ := inv_nonneg.2 hsq.le
    have hrr : (Real.sqrt (s m))⁻¹ * (Real.sqrt (s m))⁻¹ = (s m)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hsm.le]
    have hrs : (Real.sqrt (s m))⁻¹ * Real.sqrt (s m) = 1 := inv_mul_cancel₀ hsq.ne'
    have h2 := mul_le_mul_of_nonneg_left h1 hr
    have h3 : (Real.sqrt (s m))⁻¹ * (2 * Cin * (Real.sqrt (s m) * Section6.cubeFlat (j + rc) u.toFun +
        (Real.sqrt (s m))⁻¹ * (3 : ℝ) ^ (j + rc) * F)) =
        2 * Cin * (Section6.cubeFlat (j + rc) u.toFun +
          (s m)⁻¹ * (3 : ℝ) ^ (j + rc) * F) := by
      rw [← hrr]
      have : (Real.sqrt (s m))⁻¹ * Real.sqrt (s m) = 1 := hrs
      calc _ = 2 * Cin * (((Real.sqrt (s m))⁻¹ * Real.sqrt (s m)) * Section6.cubeFlat (j + rc) u.toFun +
            (Real.sqrt (s m))⁻¹ * (Real.sqrt (s m))⁻¹ * (3 : ℝ) ^ (j + rc) * F) := by ring
        _ = _ := by rw [this, one_mul]
    have hF1 := hP1 (j + rc) (by omega) hkm
    have hF2 : (s m)⁻¹ * (3 : ℝ) ^ (j + rc) * F ≤ (s m)⁻¹ * (3 : ℝ) ^ m * F := by
      have : (3 : ℝ) ^ (j + rc) ≤ (3 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hkm
      have h0 : 0 ≤ (s m)⁻¹ := inv_nonneg.2 hsm.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h0) hF
    have hF0 := Section6.cubeFlat_nonneg m u.toFun
    have h4 : Section6.cubeFlat (j + rc) u.toFun + (s m)⁻¹ * (3 : ℝ) ^ (j + rc) * F ≤
        (Cit * C₂ + 1) * (Section6.cubeFlat m u.toFun + (s m)⁻¹ * (3 : ℝ) ^ m * F) := by
      have h5 : (s m)⁻¹ * (3 : ℝ) ^ m * F ≤
          Section6.cubeFlat m u.toFun + (s m)⁻¹ * (3 : ℝ) ^ m * F := by linarith only [hF0]
      linarith only [hF1, hF2, h5]
    have h6 := mul_le_mul_of_nonneg_left h4 (by linarith only [hCin] : (0 : ℝ) ≤ 2 * Cin)
    have h7 : (Real.sqrt (s m))⁻¹ * (Real.sqrt nu * Section6.cubeGradL2 j u.grad) ≤
        2 * Cin * (Cit * C₂ + 1) * (Section6.cubeFlat m u.toFun + (s m)⁻¹ * (3 : ℝ) ^ m * F) := by
      calc _ ≤ _ := h2
        _ = _ := h3
        _ ≤ _ := h6
        _ = _ := by ring
    calc (Real.sqrt (s m))⁻¹ * Real.sqrt nu * Section6.cubeGradL2 j u.grad
        = (Real.sqrt (s m))⁻¹ * (Real.sqrt nu * Section6.cubeGradL2 j u.grad) := by ring
      _ ≤ _ := h7

/-- Witness: the numerical hypotheses of `lip_int_det` hold together (constant `s`, zero `δ`, one
scale). -/
example (k₀ : ℕ) (c nu : ℝ) (hc : 0 < c) (hnu : 0 < nu) :
    ∃ (s δ : ℕ → ℝ) (rc n m : ℕ), 0 < nu ∧ 1 ≤ rc ∧ rc ≤ 2 ∧ k₀ + 3 ≤ n ∧ n ≤ m ∧
      (∀ k, n ≤ k → k ≤ m → 0 < s k ∧ s m ≤ 2 * s k ∧ s k ≤ 2 * s m) ∧
      (∀ k, n ≤ k → k ≤ m → 0 ≤ δ k) ∧ ∑ k ∈ Finset.Icc n m, δ k ≤ c := by
  refine ⟨fun _ => 1, fun _ => 0, 1, k₀ + 3, k₀ + 3, hnu, le_rfl, by norm_num, le_rfl, le_rfl,
    fun k _ _ => ⟨one_pos, by norm_num, by norm_num⟩, fun k _ _ => le_rfl, ?_⟩
  simpa using hc.le

end SuperdiffusionCLT.Section7
