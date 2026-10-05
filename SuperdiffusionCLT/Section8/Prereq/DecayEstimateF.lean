/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DecayEstimateE
public import SuperdiffusionCLT.Section8.Prereq.LinftyL2D

@[expose] public section

namespace SuperdiffusionCLT.Section8

noncomputable section

/-!
# The dual `L²` bound on an annular set

Deterministic core of the duality step in the proof of `l.decay.estimate.Linfty`: for a
zero-trace solution `u` of `-∇·(a∇u) = h` on a ball, with `h` of mean zero supported in `B_ρ`,
and a set `A ⊆ B_b` disjoint from `B_a`, the oscillation
`‖u - (u)_A‖_{L²(A)}` is bounded through the adjoint solution with source `(u - (u)_A) 1_A`, the
Hölder estimate on `B_a` (with `ρ ≤ a`) and the Poincaré inequality on `B_a` and `B_b`.
-/

section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open scoped Pointwise ENNReal

variable {d : ℕ}

theorem decayEst_symmPart_transpose (A : Mat d) : symmPart (matTranspose A) = symmPart A := by
  ext i j
  simp only [symmPart, matTranspose, Matrix.transpose_apply]
  ring

theorem decayEst_int_ind_sq {A S : Set (Vec d)} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (F : Vec d → ℝ) :
    ∫ x in S, (A.indicator F x) ^ 2 = ∫ x in A, F x ^ 2 := by
  have h : (fun x => (A.indicator F x) ^ 2) = A.indicator (fun x => F x ^ 2) := by
    funext x
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx]
      ring
  rw [h, MeasureTheory.integral_indicator hA, Measure.restrict_restrict hA,
    Set.inter_eq_left.mpr hAS]


/-- Squared gradients of an `H¹` function are integrable. -/
theorem decayEst_integrable_grad_sq {U : Set (Vec d)} (u : H1Function U) :
    Integrable (fun x => vecNormSq (u.grad x)) (volume.restrict U) := by
  unfold vecNormSq vecDot
  refine integrable_finsetSum _ fun i _ => ?_
  have := (u.gradMemL2 i).integrable_sq
  simpa [sq] using this

theorem decayEst_grad_sq_nonneg {U : Set (Vec d)} (u : H1Function U) (x : Vec d) :
    0 ≤ vecNormSq (u.grad x) := by
  unfold vecNormSq vecDot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- **The dual `L²` bound.** -/
theorem decayEst_dual_ball [NeZero d] (a : CoeffField d) {ν : ℝ} (hν : 0 < ν)
    (hsym : ∀ x, symmPart (a x) = ν • (1 : Mat d))
    {R ρ aa bb : ℝ} (hρ : 0 < ρ) (hρa : ρ ≤ aa) (hab : aa ≤ bb) (hbR : bb ≤ R)
    (A : Set (Vec d)) (hA : MeasurableSet A) (hAb : A ⊆ euclidBall bb)
    (hAa : ∀ x ∈ A, x ∉ euclidBall aa)
    (u : H10Function (euclidBall (d := d) R)) (h : Vec d → ℝ)
    (hu : IsWeakSolutionOn a (euclidBall R) u.toH1Function h (fun _ => 0))
    (hsupp : ∀ x, x ∉ euclidBall (d := d) ρ → h x = 0)
    (hmean : ∫ x in euclidBall (d := d) ρ, h x = 0)
    (hh : MemLp h 2 (volume.restrict (euclidBall (d := d) ρ)))
    (hexist : ∀ g : Vec d → ℝ, MemLp g 2 (volume.restrict (euclidBall (d := d) R)) →
      ∃ v : H10Function (euclidBall (d := d) R),
        IsWeakSolutionOn (fun x => matTranspose (a x)) (euclidBall R) v.toH1Function g
          (fun _ => 0))
    {Cc κ α₁ β₁ α₂ β₂ : ℝ} (hCc : 0 ≤ Cc) (hα₁ : 0 ≤ α₁) (hβ₁ : 0 ≤ β₁) (hα₂ : 0 ≤ α₂)
    (hβ₂ : 0 ≤ β₂)
    (hHol : ∀ (w : H1Function (euclidBall (d := d) aa)) (f : Vec d → ℝ),
      (∀ x ∈ euclidBall (d := d) aa, f x = 0) →
      IsWeakSolutionOn (fun x => matTranspose (a x)) (euclidBall aa) w f (fun _ => 0) →
      eLpNorm (fun x => w.toFun x - ∫ y, w.toFun y ∂ballMeasure (d := d) ρ) ⊤
          (volume.restrict (euclidBall ρ)) ≤
        ENNReal.ofReal Cc *
          (ballL2 aa (fun x => w.toFun x - ∫ y, w.toFun y ∂ballMeasure (d := d) aa) +
            ENNReal.ofReal κ * eLpNorm f ⊤ (volume.restrict (euclidBall (d := d) aa))))
    (hPo1 : ∀ (w : H1Function (euclidBall (d := d) aa)) (f : Vec d → ℝ),
      IsWeakSolutionOn (fun x => matTranspose (a x)) (euclidBall aa) w f (fun _ => 0) →
      lpBar (euclidBall (d := d) aa) 2 (fun x => w.toFun x - ⨍ z in euclidBall aa, w.toFun z) ≤
        ENNReal.ofReal α₁ * lpBar (euclidBall aa) 2 (fun x => eucNorm (w.grad x)) +
          ENNReal.ofReal β₁ * lpBar (euclidBall aa) 2 f)
    (hPo2 : ∀ (w : H1Function (euclidBall (d := d) bb)) (f : Vec d → ℝ),
      IsWeakSolutionOn (fun x => matTranspose (a x)) (euclidBall bb) w f (fun _ => 0) →
      lpBar (euclidBall (d := d) bb) 2 (fun x => w.toFun x - ⨍ z in euclidBall bb, w.toFun z) ≤
        ENNReal.ofReal α₂ * lpBar (euclidBall bb) 2 (fun x => eucNorm (w.grad x)) +
          ENNReal.ofReal β₂ * lpBar (euclidBall bb) 2 f) :
    Real.sqrt (∫ x in A, (u.toH1Function.toFun x - h1_avg A u.toH1Function.toFun) ^ 2) ≤
      (Cc * Real.sqrt ((volume (euclidBall (d := d) ρ)).toReal /
            (volume (euclidBall (d := d) aa)).toReal) * α₁ * (α₂ / ν + Real.sqrt (β₂ / ν))) *
        Real.sqrt (∫ x in euclidBall (d := d) ρ, h x ^ 2) := by
  have haa : 0 < aa := lt_of_lt_of_le hρ hρa
  have hbb : 0 < bb := lt_of_lt_of_le haa hab
  have hRR : 0 < R := lt_of_lt_of_le hbb hbR
  have hUo : IsOpen (euclidBall (d := d) R) := isOpen_euclidBall R
  have hUm : MeasurableSet (euclidBall (d := d) R) := measurableSet_euclidBall R
  have hBb : euclidBall (d := d) bb ⊆ euclidBall R := euclidBall_mono hbb.le hbR
  have hBa : euclidBall (d := d) aa ⊆ euclidBall bb := euclidBall_mono haa.le hab
  have hBρ : euclidBall (d := d) ρ ⊆ euclidBall aa := euclidBall_mono hρ.le hρa
  have hAU : A ⊆ euclidBall (d := d) R := hAb.trans hBb
  set w : Vec d → ℝ := u.toH1Function.toFun with hw
  have hwL2 : MemLp w 2 (volume.restrict (euclidBall (d := d) R)) := u.toH1Function.memL2
  have hfinA : volume A ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_euclidBall_ne_top hbb) (measure_mono hAb)
  have hfinR : IsFiniteMeasure (volume.restrict (euclidBall (d := d) R)) :=
    h1_finite_restrict (volume_euclidBall_ne_top hRR)
  have hfinA' : IsFiniteMeasure (volume.restrict A) := h1_finite_restrict hfinA
  set m : ℝ := h1_avg A w with hm
  have hwA : MemLp w 2 (volume.restrict A) :=
    hwL2.mono_measure (Measure.restrict_mono hAU le_rfl)
  have hgA : MemLp (fun x => w x - m) 2 (volume.restrict A) := hwA.sub (memLp_const m)
  have hgi : Integrable (fun x => w x - m) (volume.restrict A) := hgA.integrable (by norm_num)
  have hmean0 : ∫ x in A, (w x - m) = 0 := by
    rw [integral_sub (hwA.integrable (by norm_num)) (integrable_const _), setIntegral_const,
      smul_eq_mul, hm]
    unfold h1_avg
    by_cases hV : (volume A).toReal = 0
    · have h0 : volume A = 0 := (ENNReal.toReal_eq_zero_iff _).1 hV |>.resolve_right hfinA
      rw [Measure.real, hV]
      simp [Measure.restrict_eq_zero.2 h0]
    · rw [Measure.real]
      field_simp
      ring
  have hAa' : ∀ x ∈ euclidBall (d := d) aa, x ∉ A := fun x hx hxA => hAa x hxA hx
  -- the source of the adjoint problem
  set g : Vec d → ℝ := A.indicator (fun x => w x - m) with hg
  have hgU : MemLp g 2 (volume.restrict (euclidBall (d := d) R)) :=
    MemLp.indicator hA (hwL2.sub (memLp_const m))
  obtain ⟨v, hv⟩ := hexist g hgU
  have hg0 : ∀ x ∈ euclidBall (d := d) aa, g x = 0 := fun x hx => by
    simp only [hg, Set.indicator_of_notMem (hAa' x hx)]
  have hgB : ∀ x, x ∉ A → g x = 0 := fun x hx => by simp only [hg, Set.indicator_of_notMem hx]
  have hgAeq : ∫ x in A, g x = 0 := by
    have : ∫ x in A, g x = ∫ x in A, (w x - m) := by
      refine setIntegral_congr_fun hA fun x hx => ?_
      simp only [hg, Set.indicator_of_mem hx]
    rw [this, hmean0]
  have hgMemA : MemLp g 2 (volume.restrict A) :=
    hgU.mono_measure (Measure.restrict_mono hAU le_rfl)
  have hgiA : Integrable g (volume.restrict A) := hgMemA.integrable (by norm_num)
  have hgsq : ∀ S : Set (Vec d), A ⊆ S → ∫ x in S, g x ^ 2 = ∫ x in A, (w x - m) ^ 2 :=
    fun S hS => decayEst_int_ind_sq hA hS (fun x => w x - m)
  have hgA2 : ∫ x in A, g x ^ 2 = ∫ x in A, (w x - m) ^ 2 := hgsq A subset_rfl
  -- Poincaré on the large ball
  have hv_bb := decayEst_weak_restrict (isOpen_euclidBall (d := d) bb) hBb hv
  have hfinBb : IsFiniteMeasure (volume.restrict (euclidBall (d := d) bb)) :=
    h1_finite_restrict (volume_euclidBall_ne_top hbb)
  have hP2 := decayEst_poincare_real (volume_euclidBall_ne_top hbb)
    (decayEst_volT_ball_pos hbb) hα₂ hβ₂
    (v.toH1Function.restrict (isOpen_euclidBall bb) hBb)
    (hgU.mono_measure (Measure.restrict_mono hBb le_rfl))
    (hPo2 _ g hv_bb)
  have hP2' : Real.sqrt (∫ x in euclidBall (d := d) bb,
        (v.toH1Function.toFun x - h1_avg (euclidBall bb) v.toH1Function.toFun) ^ 2) ≤
      α₂ * Real.sqrt (∫ x in euclidBall (d := d) bb, vecNormSq (v.toH1Function.grad x)) +
        β₂ * Real.sqrt (∫ x in A, g x ^ 2) := by
    have := hP2
    rw [hgsq _ hAb, ← hgA2] at this
    exact this
  have hsymT : ∀ x ∈ euclidBall (d := d) R,
      symmPart ((fun x => matTranspose (a x)) x) = ν • (1 : Mat d) := fun x _ => by
    simp only [decayEst_symmPart_transpose, hsym x]
  have hvBmem : MemLp (fun x => v.toH1Function.toFun x -
      h1_avg (euclidBall (d := d) bb) v.toH1Function.toFun) 2
      (volume.restrict (euclidBall (d := d) bb)) :=
    (v.toH1Function.memL2.mono_measure (Measure.restrict_mono hBb le_rfl)).sub (memLp_const _)
  have hgrad := decayEst_grad_bound (fun x => matTranspose (a x)) (euclidBall R) A
    (euclidBall bb) hUm hAb hBb hν hsymT v g hv
    (h1_avg (euclidBall (d := d) bb) v.toH1Function.toFun) α₂ β₂ hα₂ hβ₂
    hgB hgAeq hgMemA hgiA hvBmem hP2'
  -- Poincaré and Hölder on the small ball
  have hv_aa := decayEst_weak_restrict (isOpen_euclidBall (d := d) aa) (hBa.trans hBb) hv
  have hfinBa : IsFiniteMeasure (volume.restrict (euclidBall (d := d) aa)) :=
    h1_finite_restrict (volume_euclidBall_ne_top haa)
  have hP1 := decayEst_poincare_real (volume_euclidBall_ne_top haa)
    (decayEst_volT_ball_pos haa) hα₁ hβ₁
    (v.toH1Function.restrict (isOpen_euclidBall aa) (hBa.trans hBb))
    (hgU.mono_measure (Measure.restrict_mono (hBa.trans hBb) le_rfl))
    (hPo1 _ g hv_aa)
  have hgz : ∫ x in euclidBall (d := d) aa, g x ^ 2 = 0 := by
    have : ∫ x in euclidBall (d := d) aa, g x ^ 2 = ∫ x in euclidBall (d := d) aa, (0 : ℝ) :=
      setIntegral_congr_fun (measurableSet_euclidBall aa) fun x hx => by
        simp only [hg0 x hx]; ring
    rw [this]; simp
  rw [hgz, Real.sqrt_zero, mul_zero, add_zero] at hP1
  have hmonoG : Real.sqrt (∫ x in euclidBall (d := d) aa, vecNormSq (v.toH1Function.grad x)) ≤
      Real.sqrt (∫ x in euclidBall (d := d) R, vecNormSq (v.toH1Function.grad x)) := by
    refine Real.sqrt_le_sqrt ?_
    exact setIntegral_mono_set (decayEst_integrable_grad_sq v.toH1Function)
      (Filter.Eventually.of_forall fun x => decayEst_grad_sq_nonneg _ x)
      (Filter.Eventually.of_forall (hBa.trans hBb))
  have hHolR := decayEst_holder_real hρ hρa
    (v.toH1Function.restrict (isOpen_euclidBall aa) (hBa.trans hBb)) hg0 hCc
    (hHol _ g hg0 hv_aa)
  set Kc : ℝ := Cc * Real.sqrt ((volume (euclidBall (d := d) ρ)).toReal /
            (volume (euclidBall (d := d) aa)).toReal) * α₁ *
        (α₂ / ν + Real.sqrt (β₂ / ν)) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  have hdual : Real.sqrt (∫ x in euclidBall (d := d) ρ,
        (v.toH1Function.toFun x - h1_avg (euclidBall ρ) v.toH1Function.toFun) ^ 2) ≤
      Kc * Real.sqrt (∫ x in A, (w x - m) ^ 2) := by
    rw [hgA2] at hgrad
    have hSq : 0 ≤ Cc * Real.sqrt ((volume (euclidBall (d := d) ρ)).toReal /
            (volume (euclidBall (d := d) aa)).toReal) := by positivity
    calc _ ≤ Cc * Real.sqrt ((volume (euclidBall (d := d) ρ)).toReal /
            (volume (euclidBall (d := d) aa)).toReal) *
        Real.sqrt (∫ x in euclidBall (d := d) aa,
          (v.toH1Function.toFun x - h1_avg (euclidBall aa) v.toH1Function.toFun) ^ 2) := hHolR
      _ ≤ Cc * Real.sqrt ((volume (euclidBall (d := d) ρ)).toReal /
            (volume (euclidBall (d := d) aa)).toReal) *
          (α₁ * ((α₂ / ν + Real.sqrt (β₂ / ν)) * Real.sqrt (∫ x in A, (w x - m) ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (hP1.trans ?_) hSq
        exact mul_le_mul_of_nonneg_left (hmonoG.trans hgrad) hα₁
      _ = _ := by rw [hKc]; ring
  have hfinρ : IsFiniteMeasure (volume.restrict (euclidBall (d := d) ρ)) :=
    h1_finite_restrict (volume_euclidBall_ne_top hρ)
  have hvρ : MemLp (fun x => v.toH1Function.toFun x -
      h1_avg (euclidBall (d := d) ρ) v.toH1Function.toFun) 2
      (volume.restrict (euclidBall (d := d) ρ)) :=
    (v.toH1Function.memL2.mono_measure (Measure.restrict_mono (hBρ.trans (hBa.trans hBb)) le_rfl)).sub
      (memLp_const _)
  exact decayEst_dual_l2 a (euclidBall R) A (euclidBall ρ) hUm hA hAU
    (hBρ.trans (hBa.trans hBb)) u v h m (h1_avg (euclidBall (d := d) ρ) v.toH1Function.toFun) Kc
    hKc0 hu hv hsupp hmean hh (hh.integrable (by norm_num)) hvρ hgA hgi hmean0 hdual

end

/-!
# From the `L²` bound on an annulus to an `L^∞` bound

Geometry of the annuli `V_s = {s/2 < |x| < s}`, `W_s = {s/3 < |x| < 4s/3}` for the `L^∞`-`L²` estimate
with `δ = 1/(12 d)` and `κ = 2`, and the almost everywhere bound on `V_s` from an `L²` bound on `W_s`.
-/

section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open scoped Pointwise ENNReal

variable {d : ℕ}

theorem decayEst_ann_V_sub_W {s : ℝ} :
    decayEst_ann (d := d) (s / 2) s ⊆ decayEst_ann (s / 3) (4 * s / 3) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · have h1 := hx.1
    nlinarith only [h1, sq_nonneg s]
  · have h1 := hx.2
    nlinarith only [h1, sq_nonneg s]

theorem decayEst_ann_W_sub_ball {s : ℝ} (hs : 0 < s) :
    decayEst_ann (d := d) (s / 3) (4 * s / 3) ⊆ Metric.ball (0 : Vec d) (2 * s) := by
  intro x hx
  have h1 : x ∈ euclidBall (d := d) (4 * s / 3) := hx.2
  have h2 := euclidBall_subset_ball (d := d) (by positivity : 0 < 4 * s / 3) h1
  exact Metric.ball_subset_ball (by linarith only [hs]) h2

theorem decayEst_sqrt_mul_inv_le [NeZero d] : Real.sqrt d * (1 / (12 * (d : ℝ))) ≤ 1 / 12 := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have h1 : 1 ≤ Real.sqrt d := h1_sqrt_d_pos
  have h2 : Real.sqrt d ≤ d := by
    have := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    nlinarith only [this, h1]
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith only [h2]

theorem decayEst_ann_ball_sub [NeZero d] {s : ℝ} (hs : 0 < s) :
    ∀ x ∈ decayEst_ann (d := d) (s / 2) s,
      Metric.ball x (1 / (12 * (d : ℝ)) * s) ⊆ decayEst_ann (s / 3) (4 * s / 3) := by
  intro x hx z hz
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set τ : ℝ := 1 / (12 * (d : ℝ)) * s with hτ
  have hτ0 : 0 < τ := by positivity
  have hzi : ∀ i, |(z - x) i| ≤ τ := by
    intro i
    have := (dist_pi_lt_iff hτ0).1 (Metric.mem_ball.1 hz) i
    rw [Real.dist_eq] at this
    simpa using this.le
  have hxz : ∀ i, |(x - z) i| ≤ τ := by
    intro i
    have := hzi i
    simp only [Pi.sub_apply] at this ⊢
    rwa [abs_sub_comm]
  have hsq : Real.sqrt d * τ ≤ s / 12 := by
    have := decayEst_sqrt_mul_inv_le (d := d)
    calc Real.sqrt d * τ = (Real.sqrt d * (1 / (12 * (d : ℝ)))) * s := by rw [hτ]; ring
      _ ≤ 1 / 12 * s := mul_le_mul_of_nonneg_right this hs.le
      _ = s / 12 := by ring
  refine ⟨?_, ?_⟩
  · by_contra hcon
    have hz2 : vecNormSq z < (5 * s / 12) ^ 2 := by
      have h1 : vecNormSq z ≤ (s / 3) ^ 2 := not_lt.1 hcon
      nlinarith only [h1, hs]
    have := h1_euclid_add (by positivity) hτ0.le hz2 hxz
    rw [show z + (x - z) = x by abel] at this
    have h3 : (5 * s / 12 + Real.sqrt d * τ) ^ 2 ≤ (s / 2) ^ 2 := by
      have : 5 * s / 12 + Real.sqrt d * τ ≤ s / 2 := by linarith only [hsq]
      exact pow_le_pow_left₀ (by positivity) this 2
    have h4 := hx.1
    linarith only [this, h3, h4]
  · have hx2 := hx.2
    have := h1_euclid_add (by positivity : (0 : ℝ) ≤ s) hτ0.le hx2 hzi
    rw [show x + (z - x) = z by abel] at this
    have h3 : (s + Real.sqrt d * τ) ^ 2 ≤ (4 * s / 3) ^ 2 := by
      have : s + Real.sqrt d * τ ≤ 4 * s / 3 := by linarith only [hsq, hs]
      exact pow_le_pow_left₀ (by positivity) this 2
    linarith only [this, h3]


/-- **`L^∞` bound on `V_s` from an `L²` bound on `W_s`.** -/
theorem decayEst_linf_annulus [NeZero d] {a : CoeffField d} {R ρ s C M : ℝ} (hs : 0 < s)
    (hρ : 0 ≤ ρ) (hρs : ρ ≤ s / 3) (hsR : 4 * s / 3 ≤ R) (hC : 0 ≤ C)
    (hLinf : ∀ W V : Set (Vec d), V ⊆ W →
      (∀ x ∈ V, Metric.ball x (1 / (12 * (d : ℝ)) * s) ⊆ W) → W ⊆ Metric.ball 0 (2 * s) →
      ∀ w : H1Function W, IsWeakSolutionOn a W w (fun _ => 0) (fun _ => 0) →
        eLpNorm (fun x => w.toFun x - ⨍ z in V, w.toFun z) ⊤ (volume.restrict V) ≤
          ENNReal.ofReal C * lpBar W 2 (fun x => w.toFun x - ⨍ z in W, w.toFun z))
    (u : H1Function (euclidBall (d := d) R)) (h : Vec d → ℝ)
    (hu : IsWeakSolutionOn a (euclidBall R) u h (fun _ => 0))
    (hsupp : ∀ x, x ∉ euclidBall (d := d) ρ → h x = 0)
    (hM : Real.sqrt (∫ x in decayEst_ann (d := d) (s / 3) (4 * s / 3),
      (u.toFun x - h1_avg (decayEst_ann (s / 3) (4 * s / 3)) u.toFun) ^ 2) ≤ M) :
    ∀ᵐ x ∂volume.restrict (decayEst_ann (d := d) (s / 2) s),
      |u.toFun x - h1_avg (decayEst_ann (s / 2) s) u.toFun| ≤
        C * M * Real.sqrt (2 / ((volume (euclidBall (d := d) 1)).toReal * s ^ d)) := by
  set W : Set (Vec d) := decayEst_ann (s / 3) (4 * s / 3) with hW
  set V : Set (Vec d) := decayEst_ann (s / 2) s with hV
  have hs43 : 0 < 4 * s / 3 := by positivity
  have hWo : IsOpen W := decayEst_ann_isOpen _ _
  have hWm : MeasurableSet W := hWo.measurableSet
  have hWR : W ⊆ euclidBall (d := d) R :=
    (decayEst_ann_subset _ _).trans (euclidBall_mono hs43.le hsR)
  have hWdisj : ∀ x ∈ W, x ∉ euclidBall (d := d) ρ := by
    intro x hx hxρ
    have h1 := hx.1
    have h2 : vecNormSq x < ρ ^ 2 := hxρ
    have h3 : ρ ^ 2 ≤ (s / 3) ^ 2 := pow_le_pow_left₀ hρ hρs 2
    linarith only [h1, h2, h3]
  set w : H1Function W := u.restrict hWo hWR with hwdef
  have hw0 : IsWeakSolutionOn a W w (fun _ => 0) (fun _ => 0) :=
    decayEst_weak_congr_rhs hWm (fun x hx => hsupp x (hWdisj x hx))
      (decayEst_weak_restrict hWo hWR hu)
  have hmain := hLinf W V decayEst_ann_V_sub_W (decayEst_ann_ball_sub hs)
    (decayEst_ann_W_sub_ball hs) w hw0
  have hWfin : volume W ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_euclidBall_ne_top hs43) (measure_mono (decayEst_ann_subset _ _))
  have hvolW := decayEst_vol_ann_ge (d := d) hs43
  rw [show 4 * s / 3 / 4 = s / 3 by ring] at hvolW
  have hbig : (volume (euclidBall (d := d) (4 * s / 3))).toReal =
      (4 * s / 3) ^ d * (volume (euclidBall (d := d) 1)).toReal := decayEst_volT_ball hs43
  have hΩ := decayEst_volT_ball_pos (d := d) one_pos
  have hsd : s ^ d ≤ (4 * s / 3) ^ d := pow_le_pow_left₀ hs.le (by linarith only [hs]) d
  have hWlow : (volume (euclidBall (d := d) 1)).toReal * s ^ d / 2 ≤ (volume W).toReal := by
    refine le_trans ?_ hvolW
    rw [hbig]
    nlinarith only [hsd, hΩ]
  have hWpos : 0 < (volume W).toReal := lt_of_lt_of_le (by positivity) hWlow
  have hwL2 : MemLp w.toFun 2 (volume.restrict W) := w.memL2
  simp only [hr_avg_eq] at hmain
  rw [hr_lpBar_eq hWfin hWpos hwL2, ← ENNReal.ofReal_mul hC] at hmain
  have hl20 : 0 ≤ h1_l2 W w.toFun := Real.sqrt_nonneg _
  have hmeas : AEStronglyMeasurable (fun x => w.toFun x - h1_avg V w.toFun)
      (volume.restrict V) := by
    have h1 : AEStronglyMeasurable w.toFun (volume.restrict V) :=
      w.memL2.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono decayEst_ann_V_sub_W le_rfl)
    exact h1.sub aestronglyMeasurable_const
  have hae := decayEst_ae_le_of_eLpNorm_top hmeas (by positivity) hmain
  have hI0 : 0 ≤ ∫ x in W, (w.toFun x - h1_avg W w.toFun) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans hM
  have hI : ∫ x in W, (w.toFun x - h1_avg W w.toFun) ^ 2 ≤ M ^ 2 := by
    have := Real.sqrt_le_left hM0 |>.1 hM
    exact this
  have hl2 : h1_l2 W w.toFun ≤ M * Real.sqrt (2 / ((volume (euclidBall (d := d) 1)).toReal * s ^ d)) := by
    unfold h1_l2
    have h1 : (∫ x in W, (w.toFun x - h1_avg W w.toFun) ^ 2) / (volume W).toReal ≤
        M ^ 2 / ((volume (euclidBall (d := d) 1)).toReal * s ^ d / 2) :=
      div_le_div₀ (sq_nonneg M) hI (by positivity) hWlow
    refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
    rw [show M ^ 2 / ((volume (euclidBall (d := d) 1)).toReal * s ^ d / 2) =
        M ^ 2 * (2 / ((volume (euclidBall (d := d) 1)).toReal * s ^ d)) by field_simp,
      Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0]
  filter_upwards [hae] with x hx
  refine hx.trans ?_
  calc C * h1_l2 W w.toFun ≤ C * (M * Real.sqrt (2 / ((volume (euclidBall (d := d) 1)).toReal * s ^ d))) :=
        mul_le_mul_of_nonneg_left hl2 hC
    _ = _ := by ring

end

end

end SuperdiffusionCLT.Section8
