/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.HarmonicAffineB
public import SuperdiffusionCLT.Section6.Engine.Solutions

/-!
# Harmonic affine approximation on a cube

A solution of the identity field on `□_k` is, on every smaller cube `□_l`, approximated by its
tangent affine function at the origin, with a quadratic gain in the ratio of the side lengths.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open MeasureTheory Homogenization InnerProductSpace
open SuperdiffusionCLT.Section8.Common.ExcessDecay.Schauder
open SuperdiffusionCLT.Section8.Common.Support (normalizedL2On)

variable {d : ℕ}

theorem eh_engCube_mono {m n : ℕ} (h : m ≤ n) : engCube d m ⊆ engCube d n := by
  intro y hy
  have hy' := mem_openCubeSet_originCube_iff.1 hy
  show y ∈ openCubeSet (originCube d (n : ℤ))
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hi := hy' i
  have hle : (3 : ℝ) ^ (m : ℤ) ≤ (3 : ℝ) ^ (n : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact pow_le_pow_right₀ (by norm_num) h
  constructor <;> linarith only [hi.1, hi.2, hle]

theorem eh_coord_lt {n : ℕ} {y : Vec d} (hy : y ∈ engCube d n) (i : Fin d) :
    |y i| < (3 : ℝ) ^ n / 2 := by
  have h := (mem_openCubeSet_originCube_iff.1 hy) i
  rw [zpow_natCast] at h
  rw [abs_lt]
  constructor <;> linarith only [h.1, h.2]

theorem eh_vecNormSq_le {y : Vec d} {s : ℝ} (hy : ∀ i, |y i| ≤ s) : vecNormSq y ≤ d * s ^ 2 := by
  unfold vecNormSq vecDot
  calc ∑ i, y i * y i ≤ ∑ _i : Fin d, s ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := hy i
        have : |y i| * |y i| ≤ s * s := mul_self_le_mul_self (abs_nonneg _) h
        rw [abs_mul_abs_self] at this
        nlinarith only [this]
    _ = d * s ^ 2 := by simp

theorem eh_nL2_congr {W : Set (Vec d)} {f g : Vec d → ℝ}
    (h : ∀ᵐ y ∂(volume.restrict W), f y = g y) : normalizedL2On W f = normalizedL2On W g := by
  have hint : (∫ y in W, f y ^ 2 ∂volume) = ∫ y in W, g y ^ 2 ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [h] with y hy
    rw [hy]
  unfold normalizedL2On volumeAverage
  rw [hint]

theorem eh_continuous_affine (c : ℝ) (p : Vec d) : Continuous (fun y : Vec d => c + vecDot p y) := by
  unfold vecDot
  fun_prop


/-- Quadratic gain on `□_l` for the tangent affine function, in the normalized form. -/
theorem eh_main_aux (d : ℕ) [NeZero d] (C1 : ℝ) (hC1 : 0 ≤ C1)
    (hT : ∀ (k : ℕ), 1 ≤ k → ∀ (v : Vec d → ℝ) (c : ℝ),
      HarmonicOnNhd (v ∘ toEuc.symm) (toEuc '' engCube d k) →
      IntegrableOn (fun y => (v y - c) ^ 2) (engCube d k) volume →
      ∃ p : Vec d, ∀ y : Vec d, (∀ i, |y i| ≤ (3 : ℝ) ^ (k - 1) / 2) →
        |v y - v 0 - vecDot p y| ≤
          C1 * ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹ *
            normalizedL2On (engCube d k) (fun y => v y - c) * vecNormSq y)
    (k : ℕ) (hk : 1 ≤ k) (w : Vec d → ℝ) (gw : Vec d → Vec d)
    (h : IsSolOn (fun _ => (1 : Mat d)) (engCube d k) w gw) :
    ∃ (p : Vec d) (c : ℝ),
      (∀ n : ℕ, n + 1 ≤ k → normalizedL2On (engCube d n) (fun x => w x - c - vecDot p x) ≤
        C1 * ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹ *
          normalizedL2On (engCube d k) (fun x => w x - cubeAverage (originCube d (k : ℤ)) w) *
            (d * ((3 : ℝ) ^ n / 2) ^ 2)) := by
  obtain ⟨v, hharm, hae, hw2⟩ := eh_weyl h
  have : IsFiniteMeasure (volume.restrict (engCube d k)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (eh_volume_engCube_ne_top k)⟩
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = cubeAverage (originCube d (k : ℤ)) w := ⟨_, rfl⟩
  rw [← hc']
  have hg2 : MemLp (fun x => w x - c') 2 (volume.restrict (engCube d k)) :=
    hw2.sub (memLp_const c')
  have hvg : ∀ᵐ y ∂(volume.restrict (engCube d k)), v y - c' = w y - c' := by
    filter_upwards [hae] with y hy
    rw [hy]
  have hvg2 : MemLp (fun y => v y - c') 2 (volume.restrict (engCube d k)) :=
    hg2.ae_eq (hvg.mono fun y hy => hy.symm)
  have hint : IntegrableOn (fun y => (v y - c') ^ 2) (engCube d k) volume :=
    (memLp_two_iff_integrable_sq hvg2.aestronglyMeasurable).1 hvg2
  have hNeq : normalizedL2On (engCube d k) (fun y => v y - c')
      = normalizedL2On (engCube d k) (fun x => w x - c') := eh_nL2_congr hvg
  obtain ⟨p, hp⟩ := hT k hk v c' hharm hint
  refine ⟨p, v 0, ?_⟩
  intro n hn
  have hN0 : 0 ≤ normalizedL2On (engCube d k) (fun x => w x - c') :=
    SuperdiffusionCLT.Section8.Common.Support.normalizedL2On_nonneg _ _
  have hsub : engCube d n ⊆ engCube d k := eh_engCube_mono (by omega)
  refine eh_nL2_le_of_ae_abs_le (eh_volume_engCube_ne_top n) (eh_volume_engCube_pos n)
    (by positivity) ?_
  have h1 : ∀ᵐ x ∂(volume.restrict (engCube d n)), v x = w x :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have h2 : ∀ᵐ x ∂(volume.restrict (engCube d n)), x ∈ engCube d n :=
    ae_restrict_mem (eh_measurableSet_engCube n)
  filter_upwards [h1, h2] with x hx1 hx2
  have hcoord : ∀ i, |x i| ≤ (3 : ℝ) ^ (k - 1) / 2 := by
    intro i
    have h3 := (eh_coord_lt hx2 i).le
    have h4 : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (k - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith only [h3, h4]
  have h5 := hp x hcoord
  rw [hNeq] at h5
  have h6 : vecNormSq x ≤ d * ((3 : ℝ) ^ n / 2) ^ 2 :=
    eh_vecNormSq_le fun i => (eh_coord_lt hx2 i).le
  have hnn : 0 ≤ C1 * ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹ *
      normalizedL2On (engCube d k) (fun x => w x - c') := by positivity
  rw [hx1] at h5
  calc |w x - v 0 - vecDot p x| ≤ _ := h5
    _ ≤ _ := mul_le_mul_of_nonneg_left h6 hnn


theorem eh_pow_identity (k l : ℕ) (hlk : l ≤ k) :
    ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ l) ^ 2 * (9 : ℝ) ^ (k - l) = 1 := by
  have h9 : (9 : ℝ) ^ k = 9 ^ l * 9 ^ (k - l) := by
    rw [← pow_add]
    congr 1
    omega
  have h3k : ((3 : ℝ) ^ k) * (3 : ℝ) ^ k = 9 ^ k := by
    rw [← mul_pow]; norm_num
  have h3l : ((3 : ℝ) ^ l) ^ 2 = 9 ^ l := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h3l, ← mul_inv, h3k, h9]
  have : (9 : ℝ) ^ l ≠ 0 := by positivity
  have : (9 : ℝ) ^ (k - l) ≠ 0 := by positivity
  field_simp

/-- **Harmonic affine approximation on a cube.** -/
theorem eng_harmonic_affine (d : ℕ) [NeZero d] :
    ∃ Ch : ℝ, 1 ≤ Ch ∧
      ∀ (k l : ℕ), l + 1 ≤ k →
        ∀ (w : Vec d → ℝ) (gw : Vec d → Vec d),
          IsSolOn (fun _ => (1 : Mat d)) (engCube d k) w gw →
          ∃ (p : Vec d) (c : ℝ),
            cubeL2 l (fun x => w x - c - vecDot p x) * (9 : ℝ) ^ (k - l) ≤
                Ch * (3 : ℝ) ^ k * cubeFlat k w ∧
              engNorm p ≤ Ch * cubeFlat k w := by
  obtain ⟨C1, hC1, hT⟩ := eh_taylor_vec d
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hs3d : 0 ≤ Real.sqrt ((3 : ℝ) ^ d) := Real.sqrt_nonneg _
  have hextra : 0 ≤ C1 * d / 4 + 6 * Real.sqrt 3 * (Real.sqrt ((3 : ℝ) ^ d) + C1 * d / 36) := by
    positivity
  refine ⟨1 + (C1 * d / 4 + 6 * Real.sqrt 3 * (Real.sqrt ((3 : ℝ) ^ d) + C1 * d / 36)), ?_, ?_⟩
  · linarith only [hextra]
  intro k l hlk w gw h
  have hk : 1 ≤ k := by omega
  obtain ⟨p, c, hsup⟩ := eh_main_aux d C1 hC1 hT k hk w gw h
  obtain ⟨_, _, _, hw2⟩ := eh_weyl h
  have : IsFiniteMeasure (volume.restrict (engCube d k)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (eh_volume_engCube_ne_top k)⟩
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = cubeAverage (originCube d (k : ℤ)) w := ⟨_, rfl⟩
  rw [← hc'] at hsup
  have hg2 : MemLp (fun x => w x - c') 2 (volume.restrict (engCube d k)) :=
    hw2.sub (memLp_const c')
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = normalizedL2On (engCube d k) (fun x => w x - c') := ⟨_, rfl⟩
  rw [← hNdef] at hsup
  have hN0 : 0 ≤ N := by
    rw [hNdef]
    exact SuperdiffusionCLT.Section8.Common.Support.normalizedL2On_nonneg _ _
  have hflat : cubeFlat k w = ((3 : ℝ) ^ k)⁻¹ * N := by
    unfold cubeFlat
    rw [inv_pow, hNdef, ← hc']
    congr 1
    exact eh_cubeL2_eq hg2
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have h3kN : (3 : ℝ) ^ k * cubeFlat k w = N := by
    rw [hflat, ← mul_assoc, mul_inv_cancel₀ h3k.ne', one_mul]
  refine ⟨p, c, ?_, ?_⟩
  · -- the quadratic gain
    have hmem : ∀ n : ℕ, n ≤ k → MemLp w 2 (volume.restrict (engCube d n)) := fun n hn =>
      hw2.mono_measure (Measure.restrict_mono (eh_engCube_mono hn) le_rfl)
    have hf : MemLp (fun x => w x - c - vecDot p x) 2 (volume.restrict (engCube d l)) := by
      have h1 := (hmem l (by omega)).sub (eh_memLp_of_continuous l (eh_continuous_affine c p))
      have h2 : (fun x => w x - c - vecDot p x) = fun x => w x - (c + vecDot p x) := by
        funext x; ring
      rw [h2]
      exact h1
    rw [eh_cubeL2_eq hf]
    have hs := hsup l hlk
    have h9 : 0 ≤ (9 : ℝ) ^ (k - l) := by positivity
    have hkey := eh_pow_identity k l (by omega)
    calc normalizedL2On (engCube d l) (fun x => w x - c - vecDot p x) * (9 : ℝ) ^ (k - l)
        ≤ (C1 * ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹ * N * (d * ((3 : ℝ) ^ l / 2) ^ 2)) *
            (9 : ℝ) ^ (k - l) := mul_le_mul_of_nonneg_right hs h9
      _ = C1 * d / 4 * N * (((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ l) ^ 2 *
            (9 : ℝ) ^ (k - l)) := by ring
      _ = C1 * d / 4 * N := by rw [hkey, mul_one]
      _ ≤ (1 + (C1 * d / 4 + 6 * Real.sqrt 3 * (Real.sqrt ((3 : ℝ) ^ d) + C1 * d / 36))) * N := by
          refine mul_le_mul_of_nonneg_right ?_ hN0
          have : 0 ≤ 6 * Real.sqrt 3 * (Real.sqrt ((3 : ℝ) ^ d) + C1 * d / 36) := by positivity
          linarith only [this]
      _ = _ := by rw [mul_assoc _ ((3 : ℝ) ^ k), h3kN]
  · -- the slope bound
    obtain ⟨n, hn⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have hsupn := hsup n (by omega)
    have hmem : ∀ m : ℕ, m ≤ k → MemLp w 2 (volume.restrict (engCube d m)) := fun m hm =>
      hw2.mono_measure (Measure.restrict_mono (eh_engCube_mono hm) le_rfl)
    have hfn : MemLp (fun x => w x - c - vecDot p x) 2 (volume.restrict (engCube d n)) := by
      have h1 := (hmem n (by omega)).sub (eh_memLp_of_continuous n (eh_continuous_affine c p))
      have h2 : (fun x => w x - c - vecDot p x) = fun x => w x - (c + vecDot p x) := by
        funext x; ring
      rw [h2]
      exact h1
    have hgn : MemLp (fun x => w x - c') 2 (volume.restrict (engCube d n)) :=
      hg2.mono_measure (Measure.restrict_mono (eh_engCube_mono (by omega)) le_rfl)
    have hax := SuperdiffusionCLT.Section8.Common.ExcessDecay.normalizedL2On_axisCube_affineEval_ge
      (fun _ : Fin d => -(1 / 2) * (3 : ℝ) ^ (n : ℤ)) (L := (3 : ℝ) ^ (n : ℤ)) (by positivity)
      (c - c') p
    rw [← SuperdiffusionCLT.Section8.Common.ExcessDecay.openCubeSet_originCube_eq_axisCube d
      (n : ℤ), zpow_natCast] at hax
    have haff : SuperdiffusionCLT.Section8.Common.Support.affineEval (c - c') p
        = fun x => (w x - c') + (-(w x - c - vecDot p x)) := by
      funext x
      simp only [SuperdiffusionCLT.Section8.Common.Support.affineEval]
      ring
    rw [haff] at hax
    have hmink := SuperdiffusionCLT.Section8.Common.Support.normalizedL2On_add_le
      (f := fun x => w x - c') (g := fun x => -(w x - c - vecDot p x)) hgn hfn.neg
    rw [SuperdiffusionCLT.Section8.Common.Support.normalizedL2On_neg] at hmink
    have hsq : IntegrableOn (fun x => (w x - c') ^ 2) (engCube d k) volume :=
      (memLp_two_iff_integrable_sq hg2.aestronglyMeasurable).1 hg2
    have hcmp := SuperdiffusionCLT.Section8.Common.Support.normalizedL2On_le_of_subset
      (f := fun x => w x - c') (eh_engCube_mono (by omega : n ≤ k)) (eh_volume_engCube_pos k)
      (eh_volume_engCube_pos n) hsq
    obtain ⟨T, hT'⟩ : ∃ T : ℝ, T = (3 : ℝ) ^ n := ⟨_, rfl⟩
    have hTpos : 0 < T := by rw [hT']; positivity
    have h3T : (3 : ℝ) ^ k = 3 * T := by rw [hn, pow_succ', hT']
    have hratio : (volume (engCube d k)).toReal / (volume (engCube d n)).toReal = 3 ^ d := by
      rw [eh_volume_engCube, eh_volume_engCube, h3T, ← hT', mul_pow]
      have : T ^ d ≠ 0 := by positivity
      field_simp
    rw [hratio, ← hNdef] at hcmp
    have hsup2 : C1 * ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹ * N * (d * ((3 : ℝ) ^ n / 2) ^ 2)
        = C1 * d * N / 36 := by
      rw [h3T, ← hT']
      field_simp
      ring
    rw [hsup2] at hsupn
    have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have hX : T / (2 * Real.sqrt 3) * engNorm p
        ≤ Real.sqrt ((3 : ℝ) ^ d) * N + C1 * d * N / 36 := by
      rw [← hT'] at hax
      have hsl : SuperdiffusionCLT.Section8.Common.Support.slopeMagnitude p = engNorm p := rfl
      rw [hsl] at hax
      linarith only [hax, hmink, hcmp, hsupn]
    have hs : engNorm p ≤ 2 * Real.sqrt 3 *
        (Real.sqrt ((3 : ℝ) ^ d) * N + C1 * d * N / 36) / T := by
      rw [le_div_iff₀ hTpos]
      have h2 : engNorm p * T = 2 * Real.sqrt 3 * (T / (2 * Real.sqrt 3) * engNorm p) := by
        field_simp
      rw [h2]
      exact mul_le_mul_of_nonneg_left hX (by positivity)
    have hfin : 2 * Real.sqrt 3 * (Real.sqrt ((3 : ℝ) ^ d) * N + C1 * d * N / 36) / T
        = 6 * Real.sqrt 3 * (Real.sqrt ((3 : ℝ) ^ d) + C1 * d / 36) * (((3 : ℝ) ^ k)⁻¹ * N) := by
      rw [h3T]
      field_simp
      ring
    rw [hfin] at hs
    rw [hflat]
    refine hs.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have : 0 ≤ C1 * d / 4 := by positivity
    linarith only [this]

/-- Witness: the hypothesis is met by every affine function (a solution of the identity field),
so the theorem applies to a nonempty class. -/
example (c0 : ℝ) (p0 : Vec d) [NeZero d] :
    ∃ Ch : ℝ, 1 ≤ Ch ∧ ∃ (p : Vec d) (c : ℝ),
      cubeL2 0 (fun x => (c0 + vecDot p0 x) - c - vecDot p x) * (9 : ℝ) ^ (1 - 0) ≤
          Ch * (3 : ℝ) ^ 1 * cubeFlat 1 (fun x => c0 + vecDot p0 x) ∧
        engNorm p ≤ Ch * cubeFlat 1 (fun x => c0 + vecDot p0 x) := by
  obtain ⟨Ch, hCh, H⟩ := eng_harmonic_affine d
  exact ⟨Ch, hCh, H 1 0 le_rfl _ _ (isSolOn_one_affine 1 c0 p0)⟩

end SuperdiffusionCLT.Section6
