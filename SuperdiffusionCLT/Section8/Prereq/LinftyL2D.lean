/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.LinftyL2C
public import SuperdiffusionCLT.Section7.Root.HolderRoot
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxCount
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Probability.IndependentSums.WeakOrlicz

/-!
# `L^∞`-`L²` estimate in the interior

Lemma `l.inproof.Linfty.L2`, the interior case: for `u` a weak solution of `-∇·a∇u = 0` on a
set `W` at distance at least `δ r` from `V ⊆ W`, with `W ⊆ B_{κ r}`, and `r` above a
random scale `X'`, `‖u - (u)_V‖_{L^∞(V)} ≤ C ‖u - (u)_W‖_{L̲²(W)}`.
The interior pointwise estimate is a hypothesis.
-/

@[expose] public section

open MeasureTheory Homogenization SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section7
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

/-- The pointwise-in-the-sample interior estimate. -/
theorem linfL2_at {d : ℕ} [NeZero d] {a : CoeffField d} {shom : ℕ → ℝ}
    {CIP c N Lhat X0 ε ρ : ℝ} {A k0 : ℕ}
    (hIP : ∀ m n : ℕ, n < m →
      ((m : ℝ) - (n : ℝ)) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) ≤ c →
      Lhat ≤ (nK N n : ℝ) → X0 ≤ (3 : ℝ) ^ nK N n →
      ∀ y ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + A)),
        ∀ (f : Vec d → ℝ) (u : H1Function (shiftCube y (m : ℤ))),
          IsWeakSolutionOn a (shiftCube y (m : ℤ)) u f (fun _ => 0) →
          eLpNorm (fun x => u.toFun x - ⨍ z in shiftCube y (n : ℤ), u.toFun z) ⊤
              (volume.restrict (shiftCube y (n : ℤ))) ≤
            ENNReal.ofReal (CIP * (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ)))) *
              (lpBar (shiftCube y (m : ℤ)) 2
                  (fun x => u.toFun x - ⨍ z in shiftCube y (m : ℤ), u.toFun z) +
                ENNReal.ofReal ((shom m)⁻¹ * (3 : ℝ) ^ (2 * (m : ℝ))) *
                  eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ)))))
    (hCIP : 0 ≤ CIP) (hN : 0 ≤ N) (hX0 : 1 ≤ X0)
    (hk : ∀ k : ℕ, k0 ≤ k → ε * (k : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (k : ℝ) ≤ c)
    {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ)
    (hA : 3 * κ * max 1 (2 / δ) + 1 ≤ (3 : ℝ) ^ A) {r : ℝ}
    (hr : max 1 (2 / δ) * (3 : ℝ) ^ ms_star N (max Lhat (k0 : ℝ)) X0 ≤ r)
    {W V : Set (Vec d)} (hVW : V ⊆ W)
    (hball : ∀ x ∈ V, Metric.ball x (δ * r) ⊆ W) (hWsub : W ⊆ Metric.ball 0 (κ * r))
    (u : H1Function W) (hu : IsWeakSolutionOn a W u (fun _ => 0) (fun _ => 0)) :
    eLpNorm (fun x => u.toFun x - ⨍ z in V, u.toFun z) ⊤ (volume.restrict V) ≤
      ENNReal.ofReal (max 1 (2 * (CIP / 3 + 1) * Real.sqrt ((6 * κ * max 1 (2 / δ)) ^ d))) *
        lpBar W 2 (fun x => u.toFun x - ⨍ z in W, u.toFun z) := by
  set C0 : ℝ := max 1 (2 / δ) with hC0def
  have hC0 : 1 ≤ C0 := le_max_left _ _
  have hC0pos : 0 < C0 := by linarith only [hC0]
  have hδC : 2 ≤ δ * C0 := by
    have : 2 / δ ≤ C0 := le_max_right _ _
    rw [div_le_iff₀ hδ] at this; linarith only [this, mul_comm C0 δ]
  obtain ⟨n, hj, hL, hX, h3n, h3n1⟩ := linfL2_scale (L := max Lhat (k0 : ℝ)) hN hX0 hC0 hr
  have hLhat : Lhat ≤ (nK N n : ℝ) := (le_max_left _ _).trans hL
  have hk0n : k0 ≤ n := by
    have h1 : (k0 : ℝ) ≤ (nK N n : ℝ) := (le_max_right _ _).trans hL
    have h2 : (nK N n : ℝ) ≤ n := by exact_mod_cast nK_le N n
    exact_mod_cast h1.trans h2
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hrC : 0 < r / C0 := lt_of_lt_of_le h3pos h3n
  have hr0 : 0 < r := by
    have := (div_pos_iff_of_pos_right hC0pos).1 hrC
    exact this
  have hq : 2 * (r / C0) ≤ δ * r := by
    calc 2 * (r / C0) ≤ δ * C0 * (r / C0) := mul_le_mul_of_nonneg_right hδC hrC.le
      _ = δ * r := by field_simp
  have hrlt : r < 3 * C0 * (3 : ℝ) ^ n := by
    rw [div_lt_iff₀ hC0pos, pow_succ] at h3n1; linarith only [h3n1]
  -- the lattice scale
  set s : ℝ := (3 : ℝ) ^ ((nK N n : ℤ) - 3) with hsdef
  have hs : 0 < s := zpow_pos (by norm_num) _
  have hsn : s < (3 : ℝ) ^ n := by
    have h1 : ((nK N n : ℤ) - 3) < (n : ℤ) := by
      have := nK_le N n
      omega
    have := zpow_lt_zpow_right₀ (show (1 : ℝ) < 3 by norm_num) h1
    rwa [zpow_natCast] at this
  -- volume
  set Kr : ℝ := (6 * κ * C0) ^ d with hKrdef
  have hWvol : volume W ≤ ENNReal.ofReal ((2 * (κ * r)) ^ d) := by
    calc volume W ≤ volume (Metric.ball (0 : Vec d) (κ * r)) := measure_mono hWsub
      _ = _ := by rw [Real.volume_pi_ball _ (by positivity)]; simp
  have hWfin : volume W ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hWvol
  have hKr : (volume W).toReal ≤ Kr * ((3 : ℝ) ^ n) ^ d := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hWvol
    rw [ENNReal.toReal_ofReal (by positivity)] at h1
    refine h1.trans ?_
    rw [hKrdef, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    nlinarith only [hrlt, hκ]
  have hu2 : MemLp u.toFun 2 (volume.restrict W) := u.memL2
  -- the cube estimate
  have hCnn : (0 : ℝ) ≤ CIP / 3 := by positivity
  have hmain := linfL2_core hVW hWfin hu2 (n := n) (s := s) (B := CIP / 3) (Kr := Kr) hs hsn hCnn hKr
    (fun x hx z hz => hball x hx (by
      have hpos : 0 < δ * r := by positivity
      rw [mem_ball_iff_norm, pi_norm_lt_iff hpos]
      intro i
      have := hz i
      rw [Real.norm_eq_abs]
      have h5 : (3 : ℝ) ^ (n + 1) / 2 + s / 2 ≤ δ * r := by
        have : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by ring
        linarith only [this, hsn, h3n, hq]
      exact lt_of_lt_of_le (by simpa only [Pi.sub_apply] using this) h5)) (fun y hy hnear => by
    have hyg : y ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + A)) := by
      obtain ⟨x, hx, hxy⟩ := hnear
      rw [mem_gridPts (by positivity)]
      refine ⟨fun i => (hy i).choose, fun i => ?_, fun i => ?_⟩
      · exact (hy i).choose_spec
      · have h1 := hWsub (hVW hx)
        rw [mem_ball_iff_norm, pi_norm_lt_iff (by positivity)] at h1
        have h2 := h1 i
        simp only [Pi.sub_apply, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at h2
        have h3 := hxy i
        have : |y i| ≤ |x i| + |x i - y i| := by
          have := abs_add_le (x i) (y i - x i)
          rw [abs_sub_comm (y i) (x i)] at this
          simpa using this
        have h4 : (3 : ℝ) ^ (n + A) = (3 : ℝ) ^ n * (3 : ℝ) ^ A := pow_add _ _ _
        nlinarith only [this, h2, h3, hsn, hrlt, hA, h4, h3pos, hκ, hC0pos]
    have hsubQ : h1_cube y (n + 1) ⊆ W := by
      obtain ⟨x, hx, hxy⟩ := hnear
      refine fun z hz => hball x hx ?_
      have hpos : 0 < δ * r := by positivity
      rw [mem_ball_iff_norm, pi_norm_lt_iff hpos]
      intro i
      have h2 := (h1_mem_cube_iff.1 hz) i
      have h3 := hxy i
      have : |z i - x i| ≤ |z i - y i| + |y i - x i| := by
        have := abs_add_le (z i - y i) (y i - x i)
        simpa using this
      rw [abs_sub_comm (y i) (x i)] at this
      rw [Real.norm_eq_abs, Pi.sub_apply]
      have h5 : (3 : ℝ) ^ (n + 1) / 2 + s / 2 ≤ δ * r := by
        have : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by ring
        linarith only [this, hsn, h3n, hq]
      linarith only [this, h2, h3, h5]
    have hwin : (((n + 1 : ℕ) : ℝ) - (n : ℝ)) *
        (ε * ((n + 1 : ℕ) : ℝ) ^ (-((1 - ρ) / 2)) * Real.log ((n + 1 : ℕ) : ℝ)) ≤ c := by
      have := hk (n + 1) (by omega)
      push_cast at this ⊢
      linarith only [this]
    have hst := linfL2_step (shom := shom) (C0 := CIP) (c := c) (N := N) (Lhat := Lhat)
      (X0 := X0) (ε := ε) (ρ := ρ) (A := A) hIP (Nat.lt_succ_self n) hwin hLhat hX hyg hsubQ
      (W := W) (by positivity) u hu
    have e : (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ) - (n : ℤ))) = 1 / 3 := by
      have : (-(((n + 1 : ℕ) : ℤ) - (n : ℤ))) = -1 := by push_cast; ring
      rw [this]; norm_num
    refine ⟨hst.1, ?_⟩
    rw [e] at hst
    have := hst.2
    calc _ ≤ CIP * (1 / 3) * h1_l2 (h1_cube y (n + 1)) u.toFun := this
      _ = _ := by ring)
  by_cases hWpos : 0 < (volume W).toReal
  · have hfinV := h1_finite_restrict (ne_top_of_le_ne_top hWfin (measure_mono hVW))
    have hmem' : MemLp (fun x => u.toFun x - h1_avg V u.toFun) ⊤ (volume.restrict V) :=
      hmain.1.sub (memLp_const _)
    simp only [hr_avg_eq]
    rw [hr_lpBar_eq hWfin hWpos hu2]
    have hL : eLpNorm (fun x => u.toFun x - h1_avg V u.toFun) ⊤ (volume.restrict V) =
        ENNReal.ofReal (h1_linf V u.toFun (h1_avg V u.toFun)) := by
      unfold h1_linf
      rw [ENNReal.ofReal_toReal hmem'.eLpNorm_ne_top]
    rw [hL]
    have hl : 0 ≤ h1_l2 W u.toFun := Real.sqrt_nonneg _
    have hB : 0 ≤ 2 * (CIP / 3 + 1) * Real.sqrt Kr := by positivity
    calc ENNReal.ofReal (h1_linf V u.toFun (h1_avg V u.toFun))
        ≤ ENNReal.ofReal ((2 * (CIP / 3 + 1) * Real.sqrt Kr) * h1_l2 W u.toFun) :=
          ENNReal.ofReal_le_ofReal (by linarith only [hmain.2])
      _ = ENNReal.ofReal (2 * (CIP / 3 + 1) * Real.sqrt Kr) * ENNReal.ofReal (h1_l2 W u.toFun) :=
          ENNReal.ofReal_mul hB
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl
  · have hW0 : volume W = 0 := by
      have h00 : (volume W).toReal = 0 := le_antisymm (not_lt.1 hWpos) ENNReal.toReal_nonneg
      exact (ENNReal.toReal_eq_zero_iff _).1 h00 |>.resolve_right hWfin
    have hV0 : volume V = 0 := measure_mono_null hVW hW0
    have hr : (volume.restrict V : Measure (Vec d)) = 0 := Measure.restrict_eq_zero.2 hV0
    rw [hr]
    simp

/-- **Interior `L^∞`-`L²` estimate** (`l.inproof.Linfty.L2`, interior case). -/
theorem linfL2_interior (d : ℕ) [NeZero d]
    (hIP :
    ∃ C c N : ℝ, 1 ≤ C ∧ 0 < c ∧ 0 ≤ N ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
              ∀ A : ℕ,
                ∃ Lhat : ℝ, 1 ≤ Lhat ∧
                  ∀ (P : MeasureTheory.ProbabilityMeasure
                        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                        hPrefix hJ2 hJ3 →
                    ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                      Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
                      Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma ρ)
                        (fun omega => Real.log (X omega)) Lhat ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                          ∂P.toMeasure,
                        ∀ m n : ℕ,
                          n < m →
                          ((m : ℝ) - (n : ℝ)) *
                              (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) ≤ c →
                          Lhat ≤ (SuperdiffusionCLT.Section7.nK N n : ℝ) →
                          X omega ≤ (3 : ℝ) ^ SuperdiffusionCLT.Section7.nK N n →
                          ∀ y ∈ SuperdiffusionCLT.Section7.gridPts d
                              ((SuperdiffusionCLT.Section7.nK N n : ℤ) - 3)
                              ((3 : ℝ) ^ (n + A)),
                            ∀ (f : Homogenization.Vec d → ℝ)
                              (u : Homogenization.H1Function
                                (SuperdiffusionCLT.Section7.shiftCube y (m : ℤ))),
                              SuperdiffusionCLT.Section7.IsWeakSolutionOn
                                  (SuperdiffusionCLT.Section6.fullCoefficientRecentered
                                    nu omega)
                                  (SuperdiffusionCLT.Section7.shiftCube y (m : ℤ))
                                  u f (fun _ => 0) →
                              -- e.Dir.new.interior.pointwise
                              MeasureTheory.eLpNorm
                                  (fun x => u.toFun x -
                                    ⨍ z in SuperdiffusionCLT.Section7.shiftCube y (n : ℤ),
                                      u.toFun z)
                                  ⊤
                                  (MeasureTheory.volume.restrict
                                    (SuperdiffusionCLT.Section7.shiftCube y (n : ℤ))) ≤
                                ENNReal.ofReal (C * (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ)))) *
                                  (SuperdiffusionCLT.Section7.lpBar
                                      (SuperdiffusionCLT.Section7.shiftCube y (m : ℤ)) 2
                                      (fun x => u.toFun x -
                                        ⨍ z in SuperdiffusionCLT.Section7.shiftCube y
                                            (m : ℤ),
                                          u.toFun z) +
                                    ENNReal.ofReal
                                        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                            nu m P)⁻¹ *
                                          (3 : ℝ) ^ (2 * (m : ℝ))) *
                                      MeasureTheory.eLpNorm f ⊤
                                        (MeasureTheory.volume.restrict
                                          (SuperdiffusionCLT.Section7.shiftCube y
                                            (m : ℤ)))))
    (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K ρ : ℝ, 0 < ρ → ρ < 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
            Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
            (∃ Ct : ℝ, 1 ≤ Ct ∧ ∀ t : ℝ, 1 ≤ t →
              P.toMeasure.real {omega | t ≤ X omega} ≤
                Ct * Real.exp (-(Ct⁻¹ * (Real.log t) ^ ρ))) ∧
            ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
              ∀ r : ℝ, X omega ≤ r → ∀ W V : Set (Vec d), V ⊆ W →
                (∀ x ∈ V, Metric.ball x (δ * r) ⊆ W) → W ⊆ Metric.ball 0 (κ * r) →
                ∀ u : H1Function W,
                  IsWeakSolutionOn (fullCoefficientRecentered nu omega) W u (fun _ => 0)
                    (fun _ => 0) →
                  eLpNorm (fun x => u.toFun x - ⨍ z in V, u.toFun z) ⊤ (volume.restrict V) ≤
                    ENNReal.ofReal C * lpBar W 2 (fun x => u.toFun x - ⨍ z in W, u.toFun z) := by
  obtain ⟨CIP, c, N, hC1, hc, hN, hall⟩ := hIP
  set C0 : ℝ := max 1 (2 / δ) with hC0def
  have hC0 : 1 ≤ C0 := le_max_left _ _
  obtain ⟨A, hA⟩ := pow_unbounded_of_one_lt (3 * κ * C0 + 1) (by norm_num : (1 : ℝ) < 3)
  refine ⟨max 1 (2 * (CIP / 3 + 1) * Real.sqrt ((6 * κ * C0) ^ d)), le_max_left _ _, ?_⟩
  intro nu hnu hnu1 cStar hcs K ρ hρ hρ1 P hPrefix hJ2 hJ3 h1 h4 h5
  obtain ⟨k0, hk0, hkk⟩ := hr_small_delta (β := (1 - ρ) / 2) (c := c) (by linarith only [hρ1]) hc
  obtain ⟨Lhat, hL1, hLall⟩ := hall nu hnu hnu1 cStar hcs K 1 ρ one_pos le_rfl hρ hρ1 A
  obtain ⟨X, hXm, hX1, hXO, hae⟩ := hLall P hPrefix hJ2 hJ3 h1 h4 h5
  have hNN : 0 ≤ N := hN
  have hLnn : 0 ≤ max Lhat (k0 : ℝ) := le_max_of_le_left (by linarith only [hL1])
  refine ⟨fun omega => C0 * (3 : ℝ) ^ ms_star N (max Lhat (k0 : ℝ)) (X omega), ?_, ?_, ?_, ?_⟩
  · exact measurable_const.mul
      ((measurable_from_nat (f := fun k : ℕ => (3 : ℝ) ^ k)).comp
        (ms_star_measurable hNN hX1 hXm))
  · intro omega
    have : (1 : ℝ) ≤ (3 : ℝ) ^ ms_star N (max Lhat (k0 : ℝ)) (X omega) := one_le_pow₀ (by norm_num)
    nlinarith only [hC0, this]
  · exact ms_scale_tail P.toMeasure (L := max Lhat (k0 : ℝ)) hX1 (by linarith only [hL1]) hρ le_rfl
      hNN hLnn hC0 hXO
  · filter_upwards [hae] with omega hω
    intro r hr W V hVW hball hWsub u hu
    exact linfL2_at (shom := fun m => SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)
      (k0 := k0) (A := A) (CIP := CIP) (c := c) (N := N) (Lhat := Lhat) (X0 := X omega)
      (ε := 1) (ρ := ρ)
      (fun m n hnm hw hL hX y hy f u hu => hω m n hnm hw hL hX y hy f u hu)
      (by linarith only [hC1]) hNN (hX1 omega)
      (fun k hk => by
        have := hkk k hk
        linarith only [this])
      hδ hκ hA.le hr hVW hball hWsub u hu

/-- Satisfiability of the geometric and equation hypotheses of `linfL2_interior`: `δ = 1`,
`κ = 2`, `r = 1`, `V = B_1`, `W = B_2`, `u = 0`. -/
example (d : ℕ) (a : CoeffField d) :
    ∃ (W V : Set (Vec d)) (u : H1Function W), V ⊆ W ∧
      (∀ x ∈ V, Metric.ball x ((1 : ℝ) * 1) ⊆ W) ∧ W ⊆ Metric.ball 0 ((2 : ℝ) * 1) ∧
      IsWeakSolutionOn a W u (fun _ => 0) (fun _ => 0) := by
  refine ⟨Metric.ball 0 2, Metric.ball 0 1, 0, ?_, ?_, ?_, ?_⟩
  · exact Metric.ball_subset_ball (by norm_num)
  · intro x hx z hz
    rw [mem_ball_zero_iff] at hx ⊢
    rw [mul_one] at hz
    have h1 := dist_triangle z x 0
    rw [mem_ball_iff_norm] at hz
    simp only [dist_eq_norm, sub_zero] at h1
    linarith only [h1, hx, hz]
  · simp
  · intro φ
    simp [vecDot, matVecMul]

end SuperdiffusionCLT.Section8
