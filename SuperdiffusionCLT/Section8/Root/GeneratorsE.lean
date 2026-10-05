/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.GeneratorsD

/-!
# The local `H¹` limit of the Dirichlet solutions

For the whole-space limit `U` of the Dirichlet solutions `w_m`, on each ball `B_N` the restrictions
of the solutions `u_{m}`, `m` large, have Cauchy gradients (Caccioppoli against the uniform bound
of the differences), so `U` is the value of an `H¹(B_N)` function which is a weak solution of the
same equation (`gen_local_limit`).
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology SuperdiffusionCLT.Section6
  SuperdiffusionCLT.Section7
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem gen_local_limit [NeZero d] {a : CoeffField d} (ha : ∀ i j, Continuous fun y => a y i j)
    (hEll : ∀ s : ℝ, 0 < s → ∃ lam Lam, IsEllipticFieldOn lam Lam (euclidBall (d := d) s) a)
    {G : Vec d → ℝ} (hGc : Continuous G) (hGs : HasCompactSupport G) {n0 : ℕ}
    (w : ℕ → Vec d → ℝ) (uR : ∀ n : ℕ, H10Function (euclidBall (d := d) (n : ℝ)))
    (hae : ∀ n, n0 ≤ n → ∀ᵐ y ∂volume.restrict (euclidBall (d := d) (n : ℝ)),
      w n y = (uR n).toH1Function.toFun y)
    (hsol : ∀ n, n0 ≤ n → IsWeakSolutionOn a (euclidBall (d := d) (n : ℝ)) (uR n).toH1Function G
      (fun _ => 0))
    {ψ : ℕ → ℝ} (hψ : Tendsto ψ atTop (𝓝 0))
    (hcomp : ∀ m n, n0 ≤ m → m ≤ n → ∀ y, |w n y - w m y| ≤ ψ m)
    {U : Vec d → ℝ} (hUc : Continuous U) (hUb : ∀ m, n0 ≤ m → ∀ y, |U y - w m y| ≤ ψ m)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ W : H1Function (euclidBall (d := d) (N : ℝ)), W.toFun = U ∧
      intC2_Weak a 0 G (euclidBall (d := d) (N : ℝ)) W := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h2N : (0 : ℝ) < 2 * N := by linarith only [hNpos]
  obtain ⟨lam, Lam, hE2⟩ := hEll (2 * N) h2N
  obtain ⟨C, hC0, hC⟩ := gen_caccioppoli_ball h2N hE2
  have hhalf : (2 * (N : ℝ)) / 2 = N := by ring
  rw [hhalf] at hC
  set K : ℕ → ℕ := fun k => k + 2 * N + n0 with hK
  have hK1 : ∀ k, n0 ≤ K k := fun k => by simp only [hK]; omega
  have hK2 : ∀ k, 2 * N ≤ K k := fun k => by simp only [hK]; omega
  have hKmono : ∀ k l, k ≤ l → K k ≤ K l := fun k l h => by simp only [hK]; omega
  have hsubN : ∀ k, euclidBall (d := d) (N : ℝ) ⊆ euclidBall (d := d) ((K k : ℕ) : ℝ) := fun k =>
    euclidBall_mono hNpos.le (by exact_mod_cast (by have := hK2 k; omega : N ≤ K k))
  have hsub2N : ∀ k, euclidBall (d := d) (2 * (N : ℝ)) ⊆ euclidBall (d := d) ((K k : ℕ) : ℝ) :=
    fun k => euclidBall_mono h2N.le (by exact_mod_cast hK2 k)
  have hsub2N' : euclidBall (d := d) (N : ℝ) ⊆ euclidBall (d := d) (2 * (N : ℝ)) :=
    euclidBall_mono hNpos.le (by linarith only [hNpos])
  have hGm : ∀ s : ℝ, MemLp G 2 (volume.restrict (euclidBall (d := d) s)) := fun s =>
    (hGc.memLp_of_hasCompactSupport hGs).restrict _
  let f : ℕ → H1Function (euclidBall (d := d) (N : ℝ)) := fun k =>
    (uR (K k)).toH1Function.restrict (isOpen_euclidBall _) (hsubN k)
  -- the gradient bound for a pair of indices
  have hpair : ∀ k l, k ≤ l → ∀ i : Fin d,
      eLpNorm (fun x => (f l).grad x i - (f k).grad x i) 2
        (volume.restrict (euclidBall (d := d) (N : ℝ))) ≤
        ENNReal.ofReal (Real.sqrt (C * ψ (K k) ^ 2)) := by
    intro k l hkl i
    have hm := hK1 k
    have hKkl := hKmono k l hkl
    have hsolK : ∀ j, IsWeakSolutionOn a (euclidBall (d := d) (2 * (N : ℝ)))
        ((uR (K j)).toH1Function.restrict (isOpen_euclidBall _) (hsub2N j)) G (fun _ => 0) :=
      fun j => decayEst_weak_restrict (isOpen_euclidBall _) (hsub2N j) (hsol (K j) (hK1 j))
    set D2 : H1Function (euclidBall (d := d) (2 * (N : ℝ))) :=
      (uR (K l)).toH1Function.restrict (isOpen_euclidBall _) (hsub2N l) -
        (uR (K k)).toH1Function.restrict (isOpen_euclidBall _) (hsub2N k) with hD2
    have hdiff := resEst_weak_sub hE2 (hGm _) (hGm _) (hsolK l) (hsolK k)
    have hD2sol : IsWeakSolutionOn a (euclidBall (d := d) (2 * (N : ℝ))) D2 0 0 :=
      rc_isWeakSolutionOn_congr (fun _ => rfl) (fun x => sub_self (G x)) (fun _ => rfl) hdiff
    have hbd : ∀ᵐ x ∂volume.restrict (euclidBall (d := d) (2 * (N : ℝ))), |D2.toFun x| ≤ ψ (K k) := by
      have h1 := ae_restrict_of_ae_restrict_of_subset (hsub2N l) (hae (K l) (hK1 l))
      have h2 := ae_restrict_of_ae_restrict_of_subset (hsub2N k) (hae (K k) (hK1 k))
      filter_upwards [h1, h2] with x hx1 hx2
      have : D2.toFun x = w (K l) x - w (K k) x := by
        simp [hD2, H1Function.restrict, hx1, hx2]
      rw [this]
      exact hcomp (K k) (K l) hm hKkl x
    have hen := hC D2 (ψ (K k)) hD2sol hbd
    have hg : ∀ j, MemLp (fun x => D2.grad x j) 2 (volume.restrict (euclidBall (d := d) (N : ℝ))) :=
      fun j => (D2.gradMemL2 j).mono_measure (Measure.restrict_mono hsub2N' le_rfl)
    have := gen_coord_energy hg hen i
    have e : (fun x => (f l).grad x i - (f k).grad x i) = fun x => D2.grad x i := by
      funext x; simp [hD2, f, H1Function.restrict]
    rw [e]
    simpa [mul_comm] using this
  have hψK : Tendsto (fun k => ψ (K k)) atTop (𝓝 0) :=
    hψ.comp (tendsto_atTop_mono (fun k => by simp only [hK, id]; omega) tendsto_id)
  have hs : Tendsto (fun k => Real.sqrt (C * ψ (K k) ^ 2)) atTop (𝓝 0) := by
    have h := (hψK.pow 2).const_mul C
    have := (Real.continuous_sqrt.tendsto _).comp h
    have e : Real.sqrt (C * 0 ^ 2) = 0 := by simp
    rw [e] at this
    exact this
  have hcau : ∀ i : Fin d, ∀ ε : ℝ, 0 < ε → ∃ N' : ℕ, ∀ m n, N' ≤ m → N' ≤ n →
      eLpNorm (fun x => (f n).grad x i - (f m).grad x i) 2
        (volume.restrict (euclidBall (d := d) (N : ℝ))) ≤ ENNReal.ofReal ε := by
    intro i ε hε
    obtain ⟨N', hN'⟩ := eventually_atTop.1 (hs.eventually (gt_mem_nhds hε))
    refine ⟨N', fun m n hm hn => ?_⟩
    rcases le_total m n with h | h
    · exact (hpair m n h i).trans (ENNReal.ofReal_le_ofReal (hN' m hm).le)
    · have := (hpair n m h i).trans (ENNReal.ofReal_le_ofReal (hN' n hn).le)
      have e : eLpNorm (fun x => (f n).grad x i - (f m).grad x i) 2
          (volume.restrict (euclidBall (d := d) (N : ℝ))) =
          eLpNorm (fun x => (f m).grad x i - (f n).grad x i) 2
          (volume.restrict (euclidBall (d := d) (N : ℝ))) := by
        rw [← eLpNorm_neg]; congr 1; funext x; simp
      rw [e]; exact this
  have hfm : IsFiniteMeasure (volume.restrict (euclidBall (d := d) (N : ℝ))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (volume_euclidBall_ne_top hNpos)⟩
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Vec d) (N : ℝ)).exists_bound_of_continuousOn
    hUc.continuousOn
  have hF : MemLp U 2 (volume.restrict (euclidBall (d := d) (N : ℝ))) := by
    refine MemLp.of_bound hUc.aestronglyMeasurable B ?_
    refine ae_restrict_of_forall_mem (isOpen_euclidBall _).measurableSet fun x hx => ?_
    exact hB x (Metric.ball_subset_closedBall (euclidBall_subset_ball hNpos hx))
  have hval : Tendsto (fun k => eLpNorm (fun x => (f k).toFun x - U x) 2
      (volume.restrict (euclidBall (d := d) (N : ℝ)))) atTop (𝓝 0) := by
    have hb : ∀ k, eLpNorm (fun x => (f k).toFun x - U x) 2
        (volume.restrict (euclidBall (d := d) (N : ℝ))) ≤
        (volume.restrict (euclidBall (d := d) (N : ℝ))) Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ *
          ENNReal.ofReal (ψ (K k)) := fun k => by
      have h1 := ae_restrict_of_ae_restrict_of_subset (hsubN k) (hae (K k) (hK1 k))
      have hbd : ∀ᵐ x ∂volume.restrict (euclidBall (d := d) (N : ℝ)),
          ‖(f k).toFun x - U x‖ ≤ ψ (K k) := by
        filter_upwards [h1] with x hx
        rw [Real.norm_eq_abs]
        have : (f k).toFun x = w (K k) x := by simp [f, H1Function.restrict, hx]
        rw [this, abs_sub_comm]
        exact hUb (K k) (hK1 k) x
      exact eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) ((f k).memL2.sub hF).aestronglyMeasurable hbd
    have hlim : Tendsto (fun k => (volume.restrict (euclidBall (d := d) (N : ℝ))) Set.univ ^
        (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (ψ (K k))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun k => ENNReal.ofReal (ψ (K k))) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal hψK
      have hfin : (volume.restrict (euclidBall (d := d) (N : ℝ))) Set.univ ^
            (2 : ℝ≥0∞).toReal⁻¹ ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)
      have := ENNReal.Tendsto.const_mul h0 (Or.inr hfin)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hb
  obtain ⟨W, hW1, hW2⟩ := gen_h1_limit f U hF hval hcau
  exact ⟨W, hW1, gen_limit_weak ha f W (fun k => gen_weak_test (isOpen_euclidBall _)
    (decayEst_weak_restrict (isOpen_euclidBall _) (hsubN k) (hsol (K k) (hK1 k)))) hW2⟩

end SuperdiffusionCLT.Section8
