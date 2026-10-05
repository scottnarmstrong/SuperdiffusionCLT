/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.LocalB
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.H10Limit

/-!
# Local `W^{1,P}` estimates on a triadic cube, by a Sobolev bootstrap

For `P ≥ 2`, a weak solution `v ∈ H¹(Q)` of `-∇·(A∇v) = f - ∇·g` on a triadic cube `Q`, with `A`
entrywise `ε`-close to the identity, `f ∈ L̲² ∩ L̲^{p_*}` (`1/p_* = 1/P + 1/d`) and `g ∈ L̲^P`,
has `∇v ∈ L̲^P` on the concentric box of radius `ℓ/4` around any centre `z₀` whose `ℓ/2`-box has
localized zero trace (`LocalizedZeroTraceFunctionOn`).  This covers both the interior (centre of
the cube, no hypothesis) and a flat boundary piece (centre on a face where `v` has zero trace).

The proof cuts off by a chain of `d + 1` nested smooth box cutoffs `χ₀ ≻ χ₁ ≻ ⋯` and improves the
integrability of `∇(χ_k v)` one Sobolev step at a time (`1/t_{k+1} = max (1/P) (1/t_k - 1/d)`): each
step is the perturbative Calderón–Zygmund estimate for the divergence part plus a Poisson response
for the scalar part (`p12_step`).

## Main results

* `p12_ladder`: the bootstrap.
* `localW1p_flat`, `localW1p_interior`: the local estimates.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The radius of the `k`-th box of a chain of `n + 1` nested boxes around `z₀` whose widest member
has radius `3ℓ/8 - ℓ/(8(n+1))` and whose innermost has radius `ℓ/4`. -/
noncomputable def p12_rad (ℓ : ℝ) (n k : ℕ) : ℝ := ℓ / 4 + ((n : ℝ) - k) * (ℓ / (8 * (n + 1)))

/-- The `k`-th cutoff of the chain: equal to `1` on the box of radius `p12_rad ℓ n k` around `z₀`,
vanishing outside the box of radius `p12_rad ℓ n k + ℓ/(8(n+1))`. -/
noncomputable def p12_cut (z₀ : Vec d) (ℓ : ℝ) (n k : ℕ) : Vec d → ℝ :=
  boxCutoff (fun i => z₀ i - p12_rad ℓ n k) (fun i => z₀ i + p12_rad ℓ n k) (ℓ / (8 * (n + 1)))

theorem p12_step_pos {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) : 0 < ℓ / (8 * ((n : ℝ) + 1)) := by positivity

theorem p12_rad_succ (ℓ : ℝ) (n k : ℕ) :
    p12_rad ℓ n (k + 1) + ℓ / (8 * (n + 1)) = p12_rad ℓ n k := by
  unfold p12_rad
  push_cast
  ring

theorem p12_rad_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    p12_rad ℓ n 0 + ℓ / (8 * (n + 1)) = 3 * ℓ / 8 := by
  unfold p12_rad
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem p12_rad_self (ℓ : ℝ) (n : ℕ) : p12_rad ℓ n n = ℓ / 4 := by
  unfold p12_rad
  ring

theorem p12_cut_contDiff (z₀ : Vec d) (ℓ : ℝ) (n k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (p12_cut z₀ ℓ n k) := boxCutoff_contDiff

theorem p12_cut_01 (z₀ : Vec d) (ℓ : ℝ) (n k : ℕ) (x : Vec d) :
    0 ≤ p12_cut z₀ ℓ n k x ∧ p12_cut z₀ ℓ n k x ≤ 1 :=
  ⟨boxCutoff_nonneg x, boxCutoff_le_one x⟩

theorem p12_cut_eq_one (z₀ : Vec d) {ℓ : ℝ} (hℓ : 0 < ℓ) (n k : ℕ) {x : Vec d}
    (hx : ∀ i, |x i - z₀ i| ≤ p12_rad ℓ n k) : p12_cut z₀ ℓ n k x = 1 := by
  refine boxCutoff_eq_one (p12_step_pos hℓ n) ?_
  rw [Set.mem_Icc]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (abs_le.1 (hx i)).1
    show z₀ i - p12_rad ℓ n k ≤ x i
    linarith only [this]
  · have := (abs_le.1 (hx i)).2
    show x i ≤ z₀ i + p12_rad ℓ n k
    linarith only [this]

theorem p12_cut_tsupport (z₀ : Vec d) {ℓ : ℝ} (hℓ : 0 < ℓ) (n k : ℕ) :
    tsupport (p12_cut z₀ ℓ n k) ⊆
      Set.Icc (fun i => z₀ i - (p12_rad ℓ n k + ℓ / (8 * (n + 1))))
        (fun i => z₀ i + (p12_rad ℓ n k + ℓ / (8 * (n + 1)))) := by
  refine closure_minimal ?_ isClosed_Icc
  intro x hx
  by_contra hxn
  refine hx (boxCutoff_eq_zero (p12_step_pos hℓ n) ?_)
  intro hmem
  refine hxn ?_
  rw [Set.mem_Icc] at hmem ⊢
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := hmem.1 i
    show z₀ i - (p12_rad ℓ n k + ℓ / (8 * (n + 1))) ≤ x i
    linarith only [this]
  · have := hmem.2 i
    show x i ≤ z₀ i + (p12_rad ℓ n k + ℓ / (8 * (n + 1)))
    linarith only [this]

theorem p12_cut_hasCompactSupport (z₀ : Vec d) {ℓ : ℝ} (hℓ : 0 < ℓ) (n k : ℕ) :
    HasCompactSupport (p12_cut z₀ ℓ n k) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (p12_cut_tsupport z₀ hℓ n k)

theorem p12_cut_grad_bound (z₀ : Vec d) {ℓ : ℝ} (hℓ : 0 < ℓ) (n k : ℕ) (x : Vec d) :
    ‖p12_grad (p12_cut z₀ ℓ n k) x‖ ≤ (128 * ((n : ℝ) + 1)) / ℓ := by
  have hb : (0 : ℝ) ≤ (128 * ((n : ℝ) + 1)) / ℓ := by positivity
  refine (pi_norm_le_iff_of_nonneg hb).2 fun i => ?_
  have h := boxCutoff_deriv_bound (lo := fun i => z₀ i - p12_rad ℓ n k)
    (hi := fun i => z₀ i + p12_rad ℓ n k) (p12_step_pos hℓ n) x i
  rw [Real.norm_eq_abs]
  refine h.trans (le_of_eq ?_)
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Nesting of the chain. -/
theorem p12_cut_nest (z₀ : Vec d) {ℓ : ℝ} (hℓ : 0 < ℓ) (n k : ℕ) :
    tsupport (p12_cut z₀ ℓ n (k + 1)) ⊆ {x | p12_cut z₀ ℓ n k x = 1} := by
  intro x hx
  have h := p12_cut_tsupport z₀ hℓ n (k + 1) hx
  rw [p12_rad_succ, Set.mem_Icc] at h
  refine p12_cut_eq_one z₀ hℓ n k fun i => ?_
  rw [abs_le]
  constructor
  · have := h.1 i
    linarith only [this]
  · have := h.2 i
    linarith only [this]

/-- The first cutoff is supported in the open box of radius `ℓ/2`. -/
theorem p12_cut_zero_subset (z₀ : Vec d) {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    tsupport (p12_cut z₀ ℓ n 0) ⊆ {x | ∀ i, |x i - z₀ i| < ℓ / 2} := by
  intro x hx i
  have h := p12_cut_tsupport z₀ hℓ n 0 hx
  rw [p12_rad_zero hℓ, Set.mem_Icc] at h
  rw [abs_lt]
  constructor
  · have := h.1 i
    linarith only [this, hℓ]
  · have := h.2 i
    linarith only [this, hℓ]

theorem p12_cut_last (z₀ : Vec d) {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) {x : Vec d}
    (hx : ∀ i, |x i - z₀ i| ≤ ℓ / 4) : p12_cut z₀ ℓ n n x = 1 :=
  p12_cut_eq_one z₀ hℓ n n fun i => by rw [p12_rad_self]; exact hx i

/-! ### The exponent ladder -/

/-- The `k`-th exponent of the bootstrap ladder: `1/t_k = max (1/P) (1/2 - k/d)`. -/
noncomputable def p12_tk (d : ℕ) (P : ℝ) (k : ℕ) : ℝ := (max P⁻¹ (1 / 2 - (k : ℝ) / d))⁻¹

/-- The datum exponent: `1/p_* = 1/P + 1/d`. -/
noncomputable def p12_pstar (d : ℕ) (P : ℝ) : ℝ := (P⁻¹ + (d : ℝ)⁻¹)⁻¹

/-- The scalar datum exponent of the `k`-th step: `1/c = 1/t_k + 1/d`. -/
noncomputable def p12_ck (d : ℕ) (P : ℝ) (k : ℕ) : ℝ := ((p12_tk d P k)⁻¹ + (d : ℝ)⁻¹)⁻¹

theorem p12_inv_tk (d : ℕ) (P : ℝ) (k : ℕ) :
    (p12_tk d P k)⁻¹ = max P⁻¹ (1 / 2 - (k : ℝ) / d) := by
  unfold p12_tk; rw [inv_inv]

theorem p12_tk_inv_pos {P : ℝ} (hP : 2 < P) (k : ℕ) : 0 < max P⁻¹ (1 / 2 - (k : ℝ) / d) :=
  lt_max_of_lt_left (inv_pos.2 (by linarith only [hP]))

theorem p12_inv_P_le {P : ℝ} (hP : 2 < P) : P⁻¹ ≤ 1 / 2 := by
  rw [one_div]; exact inv_anti₀ (by norm_num) hP.le

theorem p12_tk_inv_le (hd : 2 ≤ d) {P : ℝ} (hP : 2 < P) (k : ℕ) :
    max P⁻¹ (1 / 2 - (k : ℝ) / d) ≤ 1 / 2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have h2 : 1 / 2 - (k : ℝ) / d ≤ 1 / 2 := by
    have : 0 ≤ (k : ℝ) / d := by positivity
    linarith only [this]
  exact max_le (p12_inv_P_le hP) h2

theorem p12_two_le_tk (hd : 2 ≤ d) {P : ℝ} (hP : 2 < P) (k : ℕ) : 2 ≤ p12_tk d P k := by
  have h := p12_tk_inv_le hd hP k
  have hp := p12_tk_inv_pos (d := d) hP k
  unfold p12_tk
  rw [le_inv_comm₀ (by norm_num) hp]
  simpa using h

theorem p12_tk_le {P : ℝ} (hP : 2 < P) (k : ℕ) : p12_tk d P k ≤ P := by
  have hp := p12_tk_inv_pos (d := d) hP k
  have hP0 : 0 < P := by linarith only [hP]
  unfold p12_tk
  rw [inv_le_comm₀ hp hP0]
  exact le_max_left _ _

theorem p12_tk_mono (hd : 2 ≤ d) {P : ℝ} (hP : 2 < P) (k : ℕ) :
    p12_tk d P k ≤ p12_tk d P (k + 1) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hp := p12_tk_inv_pos (d := d) hP (k + 1)
  unfold p12_tk
  rw [inv_le_inv₀ (p12_tk_inv_pos (d := d) hP k) hp]
  refine max_le_max le_rfl ?_
  have : (k : ℝ) / d ≤ ((k + 1 : ℕ) : ℝ) / d := by
    gcongr; linarith only
  linarith only [this]

theorem p12_tk_zero {P : ℝ} (hP : 2 < P) : p12_tk d P 0 = 2 := by
  unfold p12_tk
  simp only [Nat.cast_zero, zero_div, sub_zero]
  rw [max_eq_right (p12_inv_P_le hP)]; norm_num

theorem p12_tk_last (hd : 2 ≤ d) {P : ℝ} (hP : 2 < P) : p12_tk d P d = P := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hP0 : (0 : ℝ) < P⁻¹ := inv_pos.2 (by linarith only [hP])
  unfold p12_tk
  rw [div_self hd0, max_eq_left (by linarith only [hP0]), inv_inv]

theorem p12_inv_d_le (hd : 2 ≤ d) : (d : ℝ)⁻¹ ≤ 1 / 2 := by
  rw [one_div]
  exact inv_anti₀ (by norm_num) (by exact_mod_cast hd)

theorem p12_succ_div (hd : 2 ≤ d) (k : ℕ) : ((k + 1 : ℕ) : ℝ) / d = (k : ℝ) / d + (d : ℝ)⁻¹ := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  push_cast
  field_simp

theorem p12_ck_succ_inv_lt (hd : 2 ≤ d) {P : ℝ} (hP : 2 < P) (k : ℕ) :
    (p12_tk d P (k + 1))⁻¹ + (d : ℝ)⁻¹ < 1 := by
  rw [p12_inv_tk]
  have hd1 := p12_inv_d_le hd
  have hP1 := p12_inv_P_le hP
  have hP2 : P⁻¹ < 1 / 2 := by
    rw [one_div]; exact inv_strictAnti₀ (by norm_num) hP
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hk : 0 ≤ (k : ℝ) / d := by positivity
  rw [p12_succ_div hd]
  rcases le_total P⁻¹ (1 / 2 - ((k : ℝ) / d + (d : ℝ)⁻¹)) with h | h
  · rw [max_eq_right h]; linarith only [hk]
  · rw [max_eq_left h]; linarith only [hP2, hd1]

theorem p12_one_lt_ck (hd : 2 ≤ d) {P : ℝ} (hP : 2 < P) (k : ℕ) : 1 < p12_ck d P (k + 1) := by
  have hd0 : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (by omega : 0 < d))
  have hpos : 0 < (p12_tk d P (k + 1))⁻¹ + (d : ℝ)⁻¹ := by
    have : 0 < (p12_tk d P (k + 1))⁻¹ := by
      rw [p12_inv_tk]; exact p12_tk_inv_pos (d := d) hP _
    linarith only [this, hd0]
  unfold p12_ck
  rw [one_lt_inv₀ hpos]
  exact p12_ck_succ_inv_lt hd hP k

theorem p12_ck_inv (d : ℕ) (P : ℝ) (k : ℕ) :
    (p12_ck d P k)⁻¹ = (p12_tk d P k)⁻¹ + (d : ℝ)⁻¹ := by
  unfold p12_ck; rw [inv_inv]

theorem p12_inv_tk_succ_pos (hd : 2 ≤ d) {P : ℝ} (hP : 2 < P) (k : ℕ) :
    0 < (p12_tk d P (k + 1))⁻¹ + (d : ℝ)⁻¹ := by
  have hd0 : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (by omega : 0 < d))
  have hk1 : 0 < (p12_tk d P (k + 1))⁻¹ := by
    rw [p12_inv_tk]; exact p12_tk_inv_pos (d := d) hP _
  linarith only [hk1, hd0]

theorem p12_ck_le_tk (hd : 2 ≤ d) {P : ℝ} (hP : 2 < P) (k : ℕ) :
    p12_ck d P (k + 1) ≤ p12_tk d P k := by
  have hd0 : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (by omega : 0 < d))
  have hpos := p12_inv_tk_succ_pos hd hP k
  have h0 : 0 < p12_tk d P k := by
    have := p12_two_le_tk hd hP k; linarith only [this]
  unfold p12_ck
  rw [inv_le_comm₀ hpos h0, p12_inv_tk, p12_inv_tk, p12_succ_div hd]
  refine max_le ?_ ?_
  · exact (le_max_left _ _).trans (le_add_of_nonneg_right hd0.le)
  · have := le_max_right P⁻¹ (1 / 2 - ((k : ℝ) / d + (d : ℝ)⁻¹))
    have e : 1 / 2 - (k : ℝ) / d = (1 / 2 - ((k : ℝ) / d + (d : ℝ)⁻¹)) + (d : ℝ)⁻¹ := by ring
    rw [e]
    exact add_le_add_left this _

theorem p12_ck_le_pstar (hd : 2 ≤ d) {P : ℝ} (hP : 2 < P) (k : ℕ) :
    p12_ck d P (k + 1) ≤ p12_pstar d P := by
  have hd0 : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (by omega : 0 < d))
  have hP0 : (0 : ℝ) < P⁻¹ := inv_pos.2 (by linarith only [hP])
  have hpos := p12_inv_tk_succ_pos hd hP k
  unfold p12_ck p12_pstar
  rw [inv_le_inv₀ hpos (by linarith only [hP0, hd0])]
  have : P⁻¹ ≤ (p12_tk d P (k + 1))⁻¹ := by
    rw [p12_inv_tk]; exact le_max_left _ _
  linarith only [this]

/-! ### The base case: localization by the zero-trace hypothesis -/

/-- Base of the bootstrap: a cutoff `χ` supported in the window `T` where `v` has localized zero
trace gives `w = χ v ∈ H¹₀(Q)`, with control by the `L̲²` norms of `v` and `∇v`. -/
theorem p12_base (Q : TriadicCube d) (v : H1Function (openCubeSet Q)) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {Λ₀ : ℝ} (hΛ₀ : 0 ≤ Λ₀)
    (hΛ : ∀ x, ‖p12_grad χ x‖ ≤ Λ₀ / cubeScaleFactor Q) {T : Set (Vec d)}
    (hZ : LocalizedZeroTraceFunctionOn (openCubeSet Q) T v.toFun) (hT : tsupport χ ⊆ T)
    {t : ℝ} (ht : t = 2) :
    ∃ w : H10Function (openCubeSet Q), (∀ x, w.toH1Function.toFun x = χ x * v.toFun x) ∧
      (∀ᵐ x ∂(volume.restrict (openCubeSet Q)),
        w.toH1Function.grad x = χ x • v.grad x + v.toFun x • p12_grad χ x) ∧
      MemLp w.toH1Function.toFun (ENNReal.ofReal t) (normalizedCubeMeasure Q) ∧
      MemLp w.toH1Function.grad (ENNReal.ofReal t) (normalizedCubeMeasure Q) ∧
      ENNReal.ofReal (cubeScaleFactor Q) *
          Section2.Norms.cubeLpENorm Q (ENNReal.ofReal t) w.toH1Function.grad +
        Section2.Norms.cubeLpENorm Q (ENNReal.ofReal t) w.toH1Function.toFun ≤
        ENNReal.ofReal (1 + Λ₀) *
          (ENNReal.ofReal (cubeScaleFactor Q) * Section2.Norms.cubeLpENorm Q 2 v.grad +
            Section2.Norms.cubeLpENorm Q 2 v.toFun) := by
  subst ht
  obtain ⟨w, hw⟩ := hZ χ hχ hχc hT
  have hwf : ∀ x, w.toH1Function.toFun x = χ x * v.toFun x := fun x => congrFun hw x
  have hℓ : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  set ℓ := cubeScaleFactor Q with hℓdef
  set μ := normalizedCubeMeasure Q with hμ
  have h2R : (ENNReal.ofReal 2 : ℝ≥0∞) = 2 := by simp
  rw [h2R]
  have hwL2 : MemLp w.toH1Function.toFun 2 μ := memLp_normalized_of_restrict Q w.toH1Function.memL2
  have hwg2 : MemLp w.toH1Function.grad 2 μ :=
    memLp_normalized_of_memVectorL2 Q w.toH1Function.grad_memVectorL2
  have hvL2 : MemLp v.toFun 2 μ := memLp_normalized_of_restrict Q v.memL2
  have hvg2 : MemLp v.grad 2 μ := memLp_normalized_of_memVectorL2 Q v.grad_memVectorL2
  refine ⟨w, hwf, p12_grad_ae Q hχ hχc v w hwf, hwL2, hwg2, ?_⟩
  unfold Section2.Norms.cubeLpENorm
  have hae : ∀ᵐ x ∂μ, w.toH1Function.grad x = χ x • v.grad x + v.toFun x • p12_grad χ x := by
    rw [hμ, normalizedCubeMeasure_eq_smul]
    exact Measure.ae_smul_measure (p12_grad_ae Q hχ hχc v w hwf) _
  have hb : ∀ᵐ x ∂μ, ‖w.toH1Function.grad x‖ ≤ 1 * ‖v.grad x‖ + (Λ₀ / ℓ) * ‖v.toFun x‖ +
      0 * ‖v.toFun x‖ := by
    filter_upwards [hae] with x hx
    rw [hx]
    calc ‖χ x • v.grad x + v.toFun x • p12_grad χ x‖
        ≤ ‖χ x • v.grad x‖ + ‖v.toFun x • p12_grad χ x‖ := norm_add_le _ _
      _ ≤ 1 * ‖v.grad x‖ + (Λ₀ / ℓ) * ‖v.toFun x‖ + 0 * ‖v.toFun x‖ := by
        have f1 : ‖χ x • v.grad x‖ ≤ 1 * ‖v.grad x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ01 x).1]
          exact mul_le_mul_of_nonneg_right (hχ01 x).2 (norm_nonneg _)
        have f2 : ‖v.toFun x • p12_grad χ x‖ ≤ (Λ₀ / ℓ) * ‖v.toFun x‖ := by
          rw [norm_smul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hΛ x) (norm_nonneg _)
        linarith only [f1, f2]
  obtain ⟨_, hgb⟩ := p12_bound3 (p := 2) (by norm_num) (a := 1) (b := Λ₀ / ℓ) (c := 0)
    (by norm_num) (by positivity) le_rfl hwg2.aestronglyMeasurable hvg2 hvL2 hvL2 hb
  have hwle : ∀ᵐ x ∂μ, ‖w.toH1Function.toFun x‖ ≤ ‖v.toFun x‖ := by
    refine Filter.Eventually.of_forall fun x => ?_
    rw [hwf, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ01 x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ01 x).2
  have hwb : eLpNorm w.toH1Function.toFun 2 μ ≤ eLpNorm v.toFun 2 μ :=
    eLpNorm_mono_ae hwL2.aestronglyMeasurable hwle
  set Lw : ℝ≥0∞ := ENNReal.ofReal ℓ with hLw
  have hstep : Lw * eLpNorm w.toH1Function.grad 2 μ + eLpNorm w.toFun 2 μ ≤
      Lw * eLpNorm v.grad 2 μ + (ENNReal.ofReal Λ₀ * eLpNorm v.toFun 2 μ + eLpNorm v.toFun 2 μ) := by
    calc Lw * eLpNorm w.toH1Function.grad 2 μ + eLpNorm w.toH1Function.toFun 2 μ
        ≤ Lw * (ENNReal.ofReal 1 * eLpNorm v.grad 2 μ +
            ENNReal.ofReal (Λ₀ / ℓ) * eLpNorm v.toFun 2 μ +
            ENNReal.ofReal 0 * eLpNorm v.toFun 2 μ) + eLpNorm v.toFun 2 μ := by gcongr
      _ = Lw * eLpNorm v.grad 2 μ + (Lw * ENNReal.ofReal (Λ₀ / ℓ)) * eLpNorm v.toFun 2 μ +
            eLpNorm v.toFun 2 μ := by
          rw [ENNReal.ofReal_one, ENNReal.ofReal_zero, one_mul, zero_mul, add_zero]; ring
      _ = _ := by rw [hLw, p12_ofReal_mul_ofReal_div hℓ, add_assoc]
  refine hstep.trans ?_
  rw [ENNReal.ofReal_add zero_le_one hΛ₀, ENNReal.ofReal_one]
  calc Lw * eLpNorm v.grad 2 μ + (ENNReal.ofReal Λ₀ * eLpNorm v.toFun 2 μ + eLpNorm v.toFun 2 μ)
      ≤ (Lw * eLpNorm v.grad 2 μ + (ENNReal.ofReal Λ₀ * eLpNorm v.toFun 2 μ +
          eLpNorm v.toFun 2 μ)) + ENNReal.ofReal Λ₀ * (Lw * eLpNorm v.grad 2 μ) := le_self_add
    _ = _ := by ring

/-! ### The bootstrap ladder -/

/-- The bootstrap: after `k` rounds, `w_k = χ_k v ∈ H¹₀(Q)` has gradient and values in `L̲^{t_k}`,
with `ℓ ‖∇w_k‖ + ‖w_k‖` controlled by the `L̲²` norms of `v`, `∇v` and the data. -/
theorem p12_ladder [NeZero d] (hd : 2 ≤ d) {P : ℝ} (hP : 2 < P) (k : ℕ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (Q : TriadicCube d) (z₀ : Vec d) (A : CoeffField d),
      (∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q))) →
      (∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε) →
      ∀ (f : Vec d → ℝ) (g : Vec d → Vec d) (v : H1Function (openCubeSet Q)),
        IsWeakSolutionOn A (openCubeSet Q) v f g →
        MemLp f 2 (normalizedCubeMeasure Q) →
        MemLp f (ENNReal.ofReal (p12_pstar d P)) (normalizedCubeMeasure Q) →
        MemLp g (ENNReal.ofReal P) (normalizedCubeMeasure Q) →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          {x | ∀ i, |x i - z₀ i| < cubeScaleFactor Q / 2} v.toFun →
        ∃ w : H10Function (openCubeSet Q),
          (∀ x, w.toH1Function.toFun x = p12_cut z₀ (cubeScaleFactor Q) d k x * v.toFun x) ∧
          (∀ᵐ x ∂(volume.restrict (openCubeSet Q)), w.toH1Function.grad x =
            p12_cut z₀ (cubeScaleFactor Q) d k x • v.grad x +
              v.toFun x • p12_grad (p12_cut z₀ (cubeScaleFactor Q) d k) x) ∧
          MemLp w.toH1Function.toFun (ENNReal.ofReal (p12_tk d P k)) (normalizedCubeMeasure Q) ∧
          MemLp w.toH1Function.grad (ENNReal.ofReal (p12_tk d P k)) (normalizedCubeMeasure Q) ∧
          ENNReal.ofReal (cubeScaleFactor Q) *
              Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (p12_tk d P k)) w.toH1Function.grad +
            Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (p12_tk d P k)) w.toH1Function.toFun ≤
            ENNReal.ofReal C *
              ((ENNReal.ofReal (cubeScaleFactor Q) * Section2.Norms.cubeLpENorm Q 2 v.grad +
                  Section2.Norms.cubeLpENorm Q 2 v.toFun) +
                ENNReal.ofReal (cubeScaleFactor Q) ^ 2 *
                  Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (p12_pstar d P)) f +
                ENNReal.ofReal (cubeScaleFactor Q) *
                  Section2.Norms.cubeLpENorm Q (ENNReal.ofReal P) g) := by
  have hΛ₀ : (0 : ℝ) ≤ 128 * ((d : ℝ) + 1) := by positivity
  induction k with
  | zero =>
    refine ⟨1, 1 + 128 * ((d : ℝ) + 1), one_pos, by positivity, ?_⟩
    intro Q z₀ A _ _ f g v _ _ _ _ hZ
    have hℓ : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
    obtain ⟨w, hwf, hwg, hw2, hg2, hb⟩ := p12_base Q v (χ := p12_cut z₀ (cubeScaleFactor Q) d 0)
      (p12_cut_contDiff _ _ _ _) (p12_cut_hasCompactSupport z₀ hℓ d 0) (p12_cut_01 _ _ _ _) hΛ₀
      (p12_cut_grad_bound z₀ hℓ d 0) hZ (p12_cut_zero_subset z₀ hℓ d) (t := p12_tk d P 0)
      (p12_tk_zero hP)
    refine ⟨w, hwf, hwg, hw2, hg2, hb.trans ?_⟩
    exact mul_le_mul_right (le_self_add.trans le_self_add) _
  | succ k ih =>
    obtain ⟨ε₁, C₁, hε₁, hC₁, H₁⟩ := ih
    obtain ⟨ε₂, C₂, hε₂, hC₂, H₂⟩ := p12_step hd (t := p12_tk d P k) (a := p12_tk d P (k + 1))
      (c := p12_ck d P (k + 1)) (Ps := P) (pf := p12_pstar d P) hΛ₀ (p12_two_le_tk hd hP k)
      (p12_one_lt_ck hd hP k)
      (lt_of_lt_of_le one_lt_two (p12_two_le_tk hd hP (k + 1)))
      (by rw [p12_ck_inv d P (k + 1)]) (p12_ck_le_tk hd hP k) (p12_tk_mono hd hP k)
      (p12_tk_le hP (k + 1)) (p12_ck_le_pstar hd hP k) hP.le
    refine ⟨min ε₁ ε₂, C₂ * (C₁ + 1), lt_min hε₁ hε₂, by positivity, ?_⟩
    intro Q z₀ A hA hε f g v hv hf2 hfp hgP hZ
    have hℓ : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
    obtain ⟨w, hwf, hwg, hwt, hgt, hwb⟩ := H₁ Q z₀ A hA
      (fun x hx i j => (hε x hx i j).trans (min_le_left _ _)) f g v hv hf2 hfp hgP hZ
    obtain ⟨w', hw'f, hw'g, hw'a, hg'a, hw'b⟩ := H₂ Q A hA
      (fun x hx i j => (hε x hx i j).trans (min_le_right _ _)) f g v hv hf2 hfp hgP
      (p12_cut z₀ (cubeScaleFactor Q) d k) (p12_cut z₀ (cubeScaleFactor Q) d (k + 1))
      (p12_cut_contDiff _ _ _ _) (p12_cut_hasCompactSupport z₀ hℓ d k) (p12_cut_01 _ _ _ _)
      (p12_cut_contDiff _ _ _ _) (p12_cut_hasCompactSupport z₀ hℓ d (k + 1)) (p12_cut_01 _ _ _ _)
      (p12_cut_nest z₀ hℓ d k) (p12_cut_grad_bound z₀ hℓ d (k + 1)) w hwf hwg hwt hgt
    refine ⟨w', hw'f, hw'g, hw'a, hg'a, hw'b.trans ?_⟩
    set D : ℝ≥0∞ := (ENNReal.ofReal (cubeScaleFactor Q) * Section2.Norms.cubeLpENorm Q 2 v.grad +
                  Section2.Norms.cubeLpENorm Q 2 v.toFun) +
                ENNReal.ofReal (cubeScaleFactor Q) ^ 2 *
                  Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (p12_pstar d P)) f +
                ENNReal.ofReal (cubeScaleFactor Q) *
                  Section2.Norms.cubeLpENorm Q (ENNReal.ofReal P) g with hD
    set N0 : ℝ≥0∞ := ENNReal.ofReal (cubeScaleFactor Q) * Section2.Norms.cubeLpENorm Q 2 v.grad +
      Section2.Norms.cubeLpENorm Q 2 v.toFun with hN0
    set F2 : ℝ≥0∞ := ENNReal.ofReal (cubeScaleFactor Q) ^ 2 *
      Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (p12_pstar d P)) f with hF2
    set Gg : ℝ≥0∞ := ENNReal.ofReal (cubeScaleFactor Q) *
      Section2.Norms.cubeLpENorm Q (ENNReal.ofReal P) g with hGg
    set Nk : ℝ≥0∞ := ENNReal.ofReal (cubeScaleFactor Q) *
        Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (p12_tk d P k)) w.toH1Function.grad +
      Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (p12_tk d P k)) w.toH1Function.toFun with hNk
    have hFG : F2 + Gg ≤ D := by
      rw [hD]
      exact add_le_add_left (le_add_self : F2 ≤ N0 + F2) Gg
    have h1 : Nk + F2 + Gg ≤ ENNReal.ofReal (C₁ + 1) * D := by
      calc Nk + F2 + Gg = Nk + (F2 + Gg) := add_assoc _ _ _
        _ ≤ ENNReal.ofReal C₁ * D + D := add_le_add hwb hFG
        _ = ENNReal.ofReal (C₁ + 1) * D := by
          rw [ENNReal.ofReal_add hC₁.le zero_le_one, ENNReal.ofReal_one, add_mul, one_mul]
    calc ENNReal.ofReal C₂ * (Nk + F2 + Gg) ≤ ENNReal.ofReal C₂ * (ENNReal.ofReal (C₁ + 1) * D) :=
          mul_le_mul_right h1 _
      _ = ENNReal.ofReal (C₂ * (C₁ + 1)) * D := by
          rw [ENNReal.ofReal_mul hC₂.le, mul_assoc]

/-! ### The flat local estimate -/

/-- The closed concentric box of radius `r` around `z₀`. -/
def p12_box (z₀ : Vec d) (r : ℝ) : Set (Vec d) := {x | ∀ i, |x i - z₀ i| ≤ r}

theorem p12_box_measurable (z₀ : Vec d) (r : ℝ) : MeasurableSet (p12_box z₀ r) := by
  have : p12_box z₀ r = ⋂ i, {x : Vec d | |x i - z₀ i| ≤ r} := by
    ext x; simp [p12_box]
  rw [this]
  refine (isClosed_iInter fun i => ?_).measurableSet
  exact isClosed_le (by fun_prop) continuous_const

/-- **Flat local `W^{1,P}` estimate.**  Let `Q` be a triadic cube, `A` entrywise `ε`-close to the
identity on `Q`, and `v ∈ H¹(Q)` a weak solution of `-∇·(A∇v) = f - ∇·g` against `H¹₀(Q)`.  If `v`
has localized zero trace in the open box `{|x - z₀|_∞ < ℓ/2}` (automatic when this box lies in `Q`,
and valid for a zero-trace face of `Q` through `z₀`), then `∇v ∈ L̲^P` on the closed box of radius
`ℓ/4` with `ℓ ‖∇v‖_{L̲^P} ≲ ℓ ‖∇v‖_{L̲²} + ‖v‖_{L̲²} + ℓ² ‖f‖_{L̲^{p_*}} + ℓ ‖g‖_{L̲^P}`,
`1/p_* = 1/P + 1/d`. -/
theorem localW1p_flat [NeZero d] (hd : 2 ≤ d) {P : ℝ} (hP : 2 ≤ P) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (Q : TriadicCube d) (z₀ : Vec d) (A : CoeffField d),
      (∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q))) →
      (∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε) →
      ∀ (f : Vec d → ℝ) (g : Vec d → Vec d) (v : H1Function (openCubeSet Q)),
        IsWeakSolutionOn A (openCubeSet Q) v f g →
        MemLp f 2 (normalizedCubeMeasure Q) →
        MemLp f (ENNReal.ofReal (p12_pstar d P)) (normalizedCubeMeasure Q) →
        MemLp g (ENNReal.ofReal P) (normalizedCubeMeasure Q) →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          {x | ∀ i, |x i - z₀ i| < cubeScaleFactor Q / 2} v.toFun →
        MemLp v.grad (ENNReal.ofReal P)
            ((normalizedCubeMeasure Q).restrict (p12_box z₀ (cubeScaleFactor Q / 4))) ∧
          ENNReal.ofReal (cubeScaleFactor Q) *
              eLpNorm v.grad (ENNReal.ofReal P)
                ((normalizedCubeMeasure Q).restrict (p12_box z₀ (cubeScaleFactor Q / 4))) ≤
            ENNReal.ofReal C *
              ((ENNReal.ofReal (cubeScaleFactor Q) * Section2.Norms.cubeLpENorm Q 2 v.grad +
                  Section2.Norms.cubeLpENorm Q 2 v.toFun) +
                ENNReal.ofReal (cubeScaleFactor Q) ^ 2 *
                  Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (p12_pstar d P)) f +
                ENNReal.ofReal (cubeScaleFactor Q) *
                  Section2.Norms.cubeLpENorm Q (ENNReal.ofReal P) g) := by
  rcases hP.eq_or_lt with hP2 | hP2
  · -- `P = 2`: nothing to prove beyond the energy norm
    subst hP2
    refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro Q z₀ A _ _ f g v _ _ _ _ _
    have hvg2 : MemLp v.grad 2 (normalizedCubeMeasure Q) :=
      memLp_normalized_of_memVectorL2 Q v.grad_memVectorL2
    have h2R : (ENNReal.ofReal 2 : ℝ≥0∞) = 2 := by simp
    rw [h2R]
    refine ⟨hvg2.restrict _, ?_⟩
    unfold Section2.Norms.cubeLpENorm
    rw [ENNReal.ofReal_one, one_mul]
    refine mul_le_mul_right (eLpNorm_mono_measure _ Measure.restrict_le_self) _ |>.trans ?_
    exact le_self_add.trans (le_self_add.trans le_self_add)
  · obtain ⟨ε, C, hε, hC, H⟩ := p12_ladder hd hP2 d
    refine ⟨ε, C, hε, hC, ?_⟩
    intro Q z₀ A hA hεA f g v hv hf2 hfp hgP hZ
    have hℓ : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
    obtain ⟨w, hwf, hwg, hwt, hgt, hwb⟩ := H Q z₀ A hA hεA f g v hv hf2 hfp hgP hZ
    rw [p12_tk_last hd hP2] at hgt hwb
    set μ := normalizedCubeMeasure Q with hμ
    set R := p12_box z₀ (cubeScaleFactor Q / 4) with hR
    have hae : ∀ᵐ x ∂(μ.restrict R), w.toH1Function.grad x = v.grad x := by
      have h1 : ∀ᵐ x ∂μ, w.toH1Function.grad x =
          p12_cut z₀ (cubeScaleFactor Q) d d x • v.grad x +
            v.toFun x • p12_grad (p12_cut z₀ (cubeScaleFactor Q) d d) x := by
        rw [hμ, normalizedCubeMeasure_eq_smul]
        exact Measure.ae_smul_measure hwg _
      have h2 := ae_restrict_of_ae (s := R) h1
      filter_upwards [h2, ae_restrict_mem (p12_box_measurable z₀ _)] with x hx hxR
      have h1x : p12_cut z₀ (cubeScaleFactor Q) d d x = 1 := p12_cut_last z₀ hℓ d hxR
      have h0 : p12_grad (p12_cut z₀ (cubeScaleFactor Q) d d) x = 0 :=
        p12_grad_eq_zero_of_eq_one (fun y => (p12_cut_01 _ _ _ _ y).2) h1x
      rw [hx, h1x, h0]; simp
    have hmem : MemLp v.grad (ENNReal.ofReal P) (μ.restrict R) :=
      (hgt.restrict R).ae_eq (hae.mono fun x hx => hx)
    refine ⟨hmem, ?_⟩
    have hle : eLpNorm v.grad (ENNReal.ofReal P) (μ.restrict R) ≤
        eLpNorm w.toH1Function.grad (ENNReal.ofReal P) μ := by
      rw [← eLpNorm_congr_ae hae]
      exact eLpNorm_mono_measure _ Measure.restrict_le_self
    refine (mul_le_mul_right hle _).trans ?_
    exact le_self_add.trans hwb

/-- The interior case: for a box inside the cube no zero-trace hypothesis is needed. -/
theorem localW1p_interior [NeZero d] (hd : 2 ≤ d) {P : ℝ} (hP : 2 ≤ P) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (Q : TriadicCube d) (A : CoeffField d),
      (∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q))) →
      (∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε) →
      ∀ (f : Vec d → ℝ) (g : Vec d → Vec d) (v : H1Function (openCubeSet Q)),
        IsWeakSolutionOn A (openCubeSet Q) v f g →
        MemLp f 2 (normalizedCubeMeasure Q) →
        MemLp f (ENNReal.ofReal (p12_pstar d P)) (normalizedCubeMeasure Q) →
        MemLp g (ENNReal.ofReal P) (normalizedCubeMeasure Q) →
        MemLp v.grad (ENNReal.ofReal P)
            ((normalizedCubeMeasure Q).restrict
              (p12_box (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) (cubeScaleFactor Q / 4))) ∧
          ENNReal.ofReal (cubeScaleFactor Q) *
              eLpNorm v.grad (ENNReal.ofReal P)
                ((normalizedCubeMeasure Q).restrict
                  (p12_box (fun i => (Q.index i : ℝ) * cubeScaleFactor Q)
                    (cubeScaleFactor Q / 4))) ≤
            ENNReal.ofReal C *
              ((ENNReal.ofReal (cubeScaleFactor Q) * Section2.Norms.cubeLpENorm Q 2 v.grad +
                  Section2.Norms.cubeLpENorm Q 2 v.toFun) +
                ENNReal.ofReal (cubeScaleFactor Q) ^ 2 *
                  Section2.Norms.cubeLpENorm Q (ENNReal.ofReal (p12_pstar d P)) f +
                ENNReal.ofReal (cubeScaleFactor Q) *
                  Section2.Norms.cubeLpENorm Q (ENNReal.ofReal P) g) := by
  obtain ⟨ε, C, hε, hC, H⟩ := localW1p_flat hd hP
  refine ⟨ε, C, hε, hC, fun Q A hA hεA f g v hv hf2 hfp hgP => ?_⟩
  refine H Q (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) A hA hεA f g v hv hf2 hfp hgP ?_
  intro η hη hηc hηT
  have hsub : tsupport η ⊆ openCubeSet Q := by
    refine hηT.trans fun x hx i => ?_
    have := abs_lt.1 (hx i)
    constructor <;> linarith only [this.1, this.2]
  have hU : IsOpen (openCubeSet Q) := isOpen_openCubeSet Q
  obtain ⟨u, hu⟩ := exists_h10_of_compact hU (v.mulContDiffHasCompactSupport hη hηc) hsub hηc
    (fun x _ hx => by simp [H1Function.mulContDiffHasCompactSupport, image_eq_zero_of_notMem_tsupport hx])
  exact ⟨u, by rw [hu]; rfl⟩

end SuperdiffusionCLT.Section7
