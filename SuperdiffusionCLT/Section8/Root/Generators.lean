/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DecayEstimateK
public import SuperdiffusionCLT.Section8.Prereq.InteriorC2K
public import SuperdiffusionCLT.Section8.Prereq.ResolventEstimateC
public import SuperdiffusionCLT.Section8.Prereq.ExitEstimateC
public import SuperdiffusionCLT.Section7.Analytic.Regularity.MaxPrincipleB

/-!
# Whole-space solutions as limits of Dirichlet solutions: the maximum principle step

For a family of continuous zero-trace solutions `w_R` of the same equation on the balls `B_R`, a
bound `|w_S| ≤ m` outside `B_R` gives `|w_S - w_R| ≤ m` everywhere (`gen_comparison`).

* `gen_cvx`: Euclidean balls are open bounded convex domains;
* `gen_abs_le_of_ae`: an almost-everywhere bound of a continuous function holds pointwise;
* `gen_upper_of_hom`: the one-sided maximum principle for a continuous homogeneous solution;
* `gen_comparison`: the comparison of two Dirichlet solutions on nested balls.
-/

@[expose] public section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open SuperdiffusionCLT.Section8.DivergenceForm

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem gen_cvx {R : ℝ} (hR : 0 < R) : IsOpenBoundedConvexDomain (euclidBall (d := d) R) :=
  ⟨isOpen_euclidBall R, isBoundedDomain_euclidBall hR, convex_euclidBall R⟩

/-- An almost-everywhere bound of a continuous function on an open set holds at every point. -/
theorem gen_abs_le_of_ae {V : Set (Vec d)} (hV : IsOpen V) {f : Vec d → ℝ}
    (hf : Continuous f) {m : ℝ} (h : ∀ᵐ x ∂volume.restrict V, |f x| ≤ m) :
    ∀ x ∈ V, |f x| ≤ m :=
  le_of_ae_le_of_continuousOn hV (p := fun x => |f x|) (q := fun _ => m)
    hf.abs.continuousOn continuousOn_const h

/-- The one-sided weak maximum principle for a continuous homogeneous solution on a ball whose
values outside the ball are bounded by `m`. -/
theorem gen_upper_of_hom [NeZero d] {a : CoeffField d} {lam Lam : ℝ} {R : ℝ} (hR : 0 < R)
    (hEll : IsEllipticFieldOn lam Lam (euclidBall (d := d) R) a)
    {D : Vec d → ℝ} (hDc : Continuous D) (Dh : H1Function (euclidBall (d := d) R))
    (hDh : Dh.toFun = D) (hsol : IsWeakSolutionOn a (euclidBall (d := d) R) Dh 0 0) {m : ℝ}
    (hout : ∀ y, y ∉ euclidBall (d := d) R → D y ≤ m) :
    ∀ x ∈ euclidBall (d := d) R, D x ≤ m := by
  have hcvx := gen_cvx (d := d) hR
  have hfin : volume (euclidBall (d := d) R) ≠ ⊤ :=
    (Metric.isBounded_ball.subset (euclidBall_subset_ball hR)).measure_lt_top.ne
  have key : ∀ δ : ℝ, 0 < δ → ∀ x ∈ euclidBall (d := d) R, D x ≤ m + δ := by
    intro δ hδ
    set M : ℝ := m + δ with hM
    set K : Set (Vec d) := {x | vecNormSq x ≤ R ^ 2 ∧ M ≤ D x} with hK
    have hKc : IsCompact K := by
      refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
      · exact (isClosed_le continuous_vecNormSq continuous_const).inter
          (isClosed_le continuous_const hDc)
      · refine (Metric.isBounded_ball (x := (0 : Vec d)) (r := 2 * R)).subset ?_
        refine fun x hx => euclidBall_subset_ball (by linarith only [hR]) ?_
        have h1 : vecNormSq x ≤ R ^ 2 := hx.1
        show vecNormSq x < (2 * R) ^ 2
        nlinarith only [h1, hR]
    have hKU : K ⊆ euclidBall (d := d) R := by
      intro x hx
      by_contra hxn
      have := hout x hxn
      have h2 := hx.2
      linarith only [this, h2, hδ]
    have hmem := memL2On_positivePart_of_finite Dh hfin M
    set p := positivePartOpen hcvx.1 Dh M hmem with hp
    have hzero : ∀ x, x ∉ K → p.toFun x = 0 := by
      intro x hxK
      have hpx : p.toFun x = max (D x - M) 0 := by rw [hp]; simp [positivePartOpen, hDh]
      rw [hpx]
      by_cases hxB : x ∈ euclidBall (d := d) R
      · have h1 : vecNormSq x ≤ R ^ 2 := le_of_lt hxB
        have h2 : ¬ M ≤ D x := fun h => hxK ⟨h1, h⟩
        exact max_eq_right (by linarith only [not_le.1 h2])
      · have := hout x hxB
        exact max_eq_right (by linarith only [this, hδ])
    have hH10 : MemH10 (euclidBall (d := d) R) (fun x => max (Dh.toFun x - M) 0) :=
      memH10_of_compactSupport hcvx p hKc hKU hzero
    have hae := weakMaxPrinciple_core hcvx.1 hcvx.2.1 hEll Dh hsol hH10
    refine le_of_ae_le_of_continuousOn hcvx.1 (p := D) (q := fun _ => M) hDc.continuousOn
      continuousOn_const ?_
    filter_upwards [hae] with x hx
    rwa [hDh] at hx
  intro x hx
  exact le_of_forall_pos_le_add fun δ hδ => key δ hδ x hx


/-- The negative of a homogeneous weak solution is a homogeneous weak solution. -/
theorem gen_weak_neg_zero {U : Set (Vec d)} {a : CoeffField d} {w : H1Function U}
    (h : IsWeakSolutionOn a U w 0 0) : IsWeakSolutionOn a U (-w) 0 0 :=
  rc_isWeakSolutionOn_congr (fun _ => rfl) (fun _ => by simp) (fun _ => rfl) (resEst_weak_neg h)

/-- **Comparison of two zero-trace solutions on nested balls.**  If `w_R` and `w_S` are continuous
representatives of the zero-trace solutions of the same equation on `B_R ⊆ B_S`, and `|w_S| ≤ m`
outside `B_R`, then `|w_S - w_R| ≤ m` everywhere. -/
theorem gen_comparison [NeZero d] {a : CoeffField d} {lam Lam : ℝ} {G : Vec d → ℝ} {R S : ℝ}
    (hR : 0 < R) (hRS : R ≤ S) (hEll : IsEllipticFieldOn lam Lam (euclidBall (d := d) R) a)
    (hG : MemLp G 2 (volume.restrict (euclidBall (d := d) S)))
    {wR wS : Vec d → ℝ} (hwRc : Continuous wR) (hwSc : Continuous wS)
    (hwR0 : ∀ y, y ∉ euclidBall (d := d) R → wR y = 0)
    (uR : H10Function (euclidBall (d := d) R)) (uS : H1Function (euclidBall (d := d) S))
    (hRae : ∀ᵐ y ∂volume.restrict (euclidBall (d := d) R), wR y = uR.toH1Function.toFun y)
    (hSae : ∀ᵐ y ∂volume.restrict (euclidBall (d := d) S), wS y = uS.toFun y)
    (hsolR : IsWeakSolutionOn a (euclidBall (d := d) R) uR.toH1Function G (fun _ => 0))
    (hsolS : IsWeakSolutionOn a (euclidBall (d := d) S) uS G (fun _ => 0))
    {m : ℝ} (hout : ∀ y, y ∉ euclidBall (d := d) R → |wS y| ≤ m) :
    ∀ y, |wS y - wR y| ≤ m := by
  have hsub : euclidBall (d := d) R ⊆ euclidBall (d := d) S := euclidBall_mono hR.le hRS
  have hRo : IsOpen (euclidBall (d := d) R) := isOpen_euclidBall R
  have hGR : MemLp G 2 (volume.restrict (euclidBall (d := d) R)) :=
    hG.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hsolS' := decayEst_weak_restrict hRo hsub hsolS
  have hdiff := resEst_weak_sub hEll hGR hGR hsolS' hsolR
  have hdiff0 : IsWeakSolutionOn a (euclidBall (d := d) R)
      (uS.restrict hRo hsub - uR.toH1Function) 0 0 :=
    rc_isWeakSolutionOn_congr (fun _ => rfl) (fun x => sub_self (G x)) (fun _ => rfl) hdiff
  set D : Vec d → ℝ := fun x => wS x - wR x with hD
  have hDc : Continuous D := hwSc.sub hwRc
  have hae : D =ᵐ[volume.restrict (euclidBall (d := d) R)]
      (uS.restrict hRo hsub - uR.toH1Function).toFun := by
    have h1 : ∀ᵐ y ∂volume.restrict (euclidBall (d := d) R), wS y = uS.toFun y :=
      ae_restrict_of_ae_restrict_of_subset hsub hSae
    filter_upwards [h1, hRae] with y h1y h2y
    simp [hD, h1y, h2y, H1Function.restrict]
  obtain ⟨Dh, hDhf, hDhg⟩ := exitEst_h1_congr _ hae
  have hsolDh : IsWeakSolutionOn a (euclidBall (d := d) R) Dh 0 0 := by
    intro φ
    have := hdiff0 φ
    simpa only [hDhg] using this
  have hup := gen_upper_of_hom hR hEll hDc Dh hDhf hsolDh (m := m) (fun y hy => by
    have : D y = wS y := by simp [hD, hwR0 y hy]
    rw [this]; exact (le_abs_self _).trans (hout y hy))
  have hup' := gen_upper_of_hom hR hEll hDc.neg (-Dh) (by funext x; simp [hDhf])
    (gen_weak_neg_zero hsolDh) (m := m) (fun y hy => by
      have : D y = wS y := by simp [hD, hwR0 y hy]
      simp only [Pi.neg_apply, this]
      exact (neg_le_abs _).trans (hout y hy))
  intro y
  by_cases hy : y ∈ euclidBall (d := d) R
  · exact abs_le.2 ⟨by have := hup' y hy; simp only [Pi.neg_apply] at this; linarith only [this],
      hup y hy⟩
  · have : wS y - wR y = wS y := by simp [hwR0 y hy]
    rw [this]; exact hout y hy


/-- A sequence of continuous functions with `|w_n - w_m| ≤ ψ_m` for `n ≥ m ≥ n₀` and `ψ_m → 0`
converges uniformly to a continuous limit with `|U - w_m| ≤ ψ_m`. -/
theorem gen_cauchy_limit {w : ℕ → Vec d → ℝ} {ψ : ℕ → ℝ}
    (hψ : Filter.Tendsto ψ Filter.atTop (nhds 0)) {n0 : ℕ} (hw : ∀ n, Continuous (w n))
    (hC : ∀ m n, n0 ≤ m → m ≤ n → ∀ y, |w n y - w m y| ≤ ψ m) :
    ∃ U : Vec d → ℝ, Continuous U ∧ ∀ m, n0 ≤ m → ∀ y, |U y - w m y| ≤ ψ m := by
  have hψ' : Filter.Tendsto (fun k => 2 * ψ (k + n0)) Filter.atTop (nhds 0) := by
    have := (hψ.comp (Filter.tendsto_add_atTop_nat n0)).const_mul 2
    simpa using this
  have hcau : ∀ y, CauchySeq (fun k => w (k + n0) y) := fun y => by
    refine cauchySeq_of_le_tendsto_0 (fun N => 2 * ψ (N + n0)) (fun n m N hn hm => ?_) hψ'
    rw [Real.dist_eq]
    have h1 := hC (N + n0) (n + n0) (by omega) (by omega) y
    have h2 := hC (N + n0) (m + n0) (by omega) (by omega) y
    calc |w (n + n0) y - w (m + n0) y|
        = |(w (n + n0) y - w (N + n0) y) - (w (m + n0) y - w (N + n0) y)| := by ring_nf
      _ ≤ |w (n + n0) y - w (N + n0) y| + |w (m + n0) y - w (N + n0) y| := abs_sub _ _
      _ ≤ 2 * ψ (N + n0) := by linarith only [h1, h2]
  choose L hL using fun y => cauchySeq_tendsto_of_complete (hcau y)
  have hL' : ∀ y, Filter.Tendsto (fun n => w n y) Filter.atTop (nhds (L y)) := fun y =>
    (Filter.tendsto_add_atTop_iff_nat (f := fun n => w n y) n0).1 (hL y)
  have hb : ∀ m, n0 ≤ m → ∀ y, |L y - w m y| ≤ ψ m := fun m hm y => by
    have h1 : Filter.Tendsto (fun n => |w n y - w m y|) Filter.atTop (nhds |L y - w m y|) :=
      ((hL' y).sub_const _).abs
    refine le_of_tendsto h1 ?_
    filter_upwards [Filter.eventually_ge_atTop m] with n hn using hC m n hm hn y
  refine ⟨L, ?_, hb⟩
  have hunif : TendstoUniformly w L Filter.atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have := (hψ.eventually (gt_mem_nhds hε)).and (Filter.eventually_ge_atTop n0)
    filter_upwards [this] with n hn y
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hb n hn.2 y) hn.1
  exact hunif.continuous (Filter.Eventually.of_forall hw).frequently


/-- A continuous function bounded by `ψ_m → 0` outside `B_m` lies in `C₀`. -/
theorem gen_isC0 {U : Vec d → ℝ} (hc : Continuous U) {ψ : ℕ → ℝ}
    (hψ : Filter.Tendsto ψ Filter.atTop (nhds 0)) {n0 : ℕ}
    (hdec : ∀ m : ℕ, n0 ≤ m → ∀ y, y ∉ euclidBall (d := d) (m : ℝ) → |U y| ≤ ψ m) :
    IsC0Function U := by
  refine ⟨⟨⟨U, hc⟩, ?_⟩, rfl⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm1, hm2⟩ := ((hψ.eventually (gt_mem_nhds hε)).and
    (Filter.eventually_ge_atTop (n0 + 1))).exists
  refine Filter.mem_of_superset (isCompact_closedBall (0 : Vec d) (m : ℝ)).compl_mem_cocompact
    (fun y hy => ?_)
  have hmpos : (0 : ℝ) < m := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    linarith only [this]
  have hyn : y ∉ euclidBall (d := d) (m : ℝ) := fun h =>
    hy (Metric.ball_subset_closedBall (euclidBall_subset_ball hmpos h))
  show dist (U y) 0 < ε
  rw [Real.dist_eq, sub_zero]
  exact lt_of_le_of_lt (hdec m (by omega) y hyn) hm1

end SuperdiffusionCLT.Section8
