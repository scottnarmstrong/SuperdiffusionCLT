/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2InteriorB
public import SuperdiffusionCLT.Section7.Prereq.MollifiedFluxC
public import SuperdiffusionCLT.Section7.Analytic.CZ.DualityD
public import SuperdiffusionCLT.Section7.Prereq.MollifiedFluxB
public import SuperdiffusionCLT.Section7.Prereq.WhitneyLocalD

/-!
# The grid bound for the interior error terms

A function bounded on
each mesoscale cell `z + □_n` by the local normalized energy of `v` and `w` on `z + □_{n+1}`
(the cells with `z + □_{n+1} ⊆ W`) has `L^p(S)` norm bounded by the global norms on `W`.

* `Section7.l2b_grid_bound`: the local-to-global bound on the grid.
* `Section7.l2b_E3_core`: the interior flux term `ζ η ∗ D` in `L̲^p(W)`.
* `Section7.l2b_layer_bound`, `Section7.l2b_E2_core`: the layer term `∇ζ · η ∗ F` in
  `W̲^{-1,p}(W)` (`e.Dir.new.boundary.flux.term`); the transition layer is covered
  by good cells, Hölder against a test function and the layer Poincaré inequality
  `‖ψ‖_{L^q(A)} ≤ C r ‖∇ψ‖_{L^q(W)}` give the dual bound.
* `Section7.l2b_avg_eq_cubeLpENorm`, `Section7.l2b_cell_transfer`: transfer of the local bounds of
  `m1_mollified_flux` (origin cube, translated field) to a cell `z + □_{n+1}` of a global solution.
* `Section7.l2b_ae_cell`: the almost-sure per-cell pointwise bound for the mollified flux defect and
  the mollified full flux (the hypothesis `hG` of the cores).
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem l2b_volume_cell' (z : Vec d) (m : ℕ) :
    volume (l2b_cell z m) = ENNReal.ofReal (cubeVolume (originCube d (m : ℤ))) := by
  unfold l2b_cell
  rw [volume_translateSet_eq, ← ENNReal.ofReal_toReal (volume_cubeSet_lt_top _).ne,
    volume_cubeSet_toReal]

theorem l2b_cubeVolume_succ (n : ℕ) :
    ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))) =
      (3 : ℝ≥0∞) ^ d * ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))) := by
  rw [m1_cubeVolume_succ, ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- **The grid bound**.  Let `g` be bounded on each cell `z + □_n` with
`z + □_{n+1} ⊆ W` by `α` times the normalized `L²` average of `v` plus `β` times the normalized
`L^p` average of `w` over `z + □_{n+1}` (`1 ≤ p < 2`), and vanish on `S` off these cells.  Then
`‖g‖_{L^p(S)} ≤ α |S|^{1/p-1/2} ‖v‖_{L²(W)} + β ‖w‖_{L^p(W)}`. -/
theorem l2b_grid_bound (n : ℕ) {W S : Set (Vec d)} (hS : MeasurableSet S)
    (v w : Vec d → ℝ≥0∞) {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) {α β : ℝ≥0∞} {g : Vec d → ℝ≥0∞}
    (hg : ∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ W → ∀ x ∈ l2b_cell (l2b_pt n k) n,
      g x ≤ α * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
          (l2b_cell (l2b_pt n k) (n + 1)) v 2 +
        β * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
          (l2b_cell (l2b_pt n k) (n + 1)) w p)
    (hg0 : ∀ x ∈ S, (∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ W →
      x ∉ l2b_cell (l2b_pt n k) n) → g x = 0) :
    (∫⁻ x in S, g x ^ p) ^ (1 / p) ≤
      α * volume S ^ (1 / p - 1 / 2) * (∫⁻ x in W, v x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) +
        β * (∫⁻ x in W, w x ^ p) ^ (1 / p) := by
  have hpos : 0 < cubeVolume (originCube d (n : ℤ)) := cubeVolume_pos _
  set a : ℝ≥0∞ := ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))) with ha
  set b : ℝ≥0∞ := ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))) with hb
  have ha0 : a ≠ 0 := by rw [ha]; simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hpos
  have haT : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hbm : b = (3 : ℝ≥0∞) ^ d * a := l2b_cubeVolume_succ n
  have hc : a * (3 : ℝ≥0∞) ^ d * b⁻¹ = 1 := by
    rw [hbm, mul_comm ((3 : ℝ≥0∞) ^ d) a]
    exact ENNReal.mul_inv_cancel (mul_ne_zero ha0 (pow_ne_zero _ (by norm_num)))
      (ENNReal.mul_ne_top haT (ENNReal.pow_ne_top (by norm_num)))
  have key := l2b_local_global
    (ι := {k : Fin d → ℤ // l2b_cell (l2b_pt n k) (n + 1) ⊆ W})
    (Q := fun k => l2b_cell (l2b_pt n k.1) n) (P := fun k => l2b_cell (l2b_pt n k.1) (n + 1))
    (fun k => l2b_cell_measurable _ _)
    (fun k k' hkk' => l2b_cell_disjoint n fun h => hkk' (Subtype.ext h)) hS (a := a) (b := b)
    (m := (3 : ℝ≥0∞) ^ d) (fun k => by rw [l2b_volume_cell']) (l2b_overlap n W) v w hp1 hp2
    (α := α) (β := β) (g := g) (fun k x hx => hg k.1 k.2 x hx) (fun x hx hx' =>
      hg0 x hx fun k hk => hx' ⟨k, hk⟩)
  rw [hc] at key
  simpa only [one_div, ENNReal.rpow_ofNat, ge_iff_le, ENNReal.one_rpow, mul_one] using key

/-- The normalized `L^q` norm on `V` in lower-integral form. -/
theorem l2b_lpBar_eq {V : Set (Vec d)} {q : ℝ} (hq : 0 < q) {E : Type*} [NormedAddCommGroup E]
    {F : Vec d → E} (hF : AEStronglyMeasurable F (volume.restrict V)) :
    lpBar V (ENNReal.ofReal q) F =
      (volume V)⁻¹ ^ (1 / q) * (∫⁻ x in V, ‖F x‖ₑ ^ q) ^ (1 / q) := by
  have h0 : ENNReal.ofReal q ≠ 0 := by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hq
  have h1 : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold lpBar
  rw [eLpNorm_smul_measure_of_ne_top h1 F _ hF, smul_eq_mul,
    eLpNorm_eq_lintegral_rpow_enorm_toReal h0 h1 hF, ENNReal.toReal_ofReal hq.le]
  congr 3
  rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hq.le, one_div]

/-- `|W|^{-1/p} |S|^{1/p - 1/2}`-type exponent bookkeeping:
`(|W|⁻¹)^{1/p} |W|^{1/p - 1/2} = (|W|⁻¹)^{1/2}`. -/
theorem l2b_vol_exponent {V : ℝ≥0∞} (h0 : V ≠ 0) (hT : V ≠ ⊤) (p : ℝ) :
    V⁻¹ ^ (1 / p) * V ^ (1 / p - 1 / 2) = V⁻¹ ^ (1 / (2 : ℝ)) := by
  rw [ENNReal.inv_rpow, ENNReal.inv_rpow]
  have : V ^ (1 / p) = V ^ (1 / p - 1 / 2) * V ^ (1 / (2 : ℝ)) := by
    rw [← ENNReal.rpow_add _ _ h0 hT]; congr 1; ring
  have hA0 : V ^ (1 / p - 1 / 2) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 h0) hT).ne'
  have hAT : V ^ (1 / p - 1 / 2) ≠ ⊤ := by
    intro h
    rcases ENNReal.rpow_eq_top_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h0 h1
    · exact hT h1
  have hB0 : V ^ (1 / (2 : ℝ)) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 h0) hT).ne'
  have hBT : V ^ (1 / (2 : ℝ)) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hT
  rw [this, ENNReal.mul_inv (Or.inl hA0) (Or.inl hAT), mul_right_comm,
    ENNReal.inv_mul_cancel hA0 hAT, one_mul]

theorem l2b_enorm_smul_le {ζ : ℝ} (hζ : |ζ| ≤ 1) (G : Vec d) : ‖ζ • G‖ₑ ≤ ‖G‖ₑ := by
  rw [enorm_smul]
  have : ‖ζ‖ₑ ≤ 1 := by
    rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hζ
  calc ‖ζ‖ₑ * ‖G‖ₑ ≤ 1 * ‖G‖ₑ := mul_le_mul' this le_rfl
    _ = ‖G‖ₑ := one_mul _

/-- **The interior flux term** (`e.Dir.new.term.one`), deterministic core.  If the
mollified field `G` is bounded on every good cell `z + □_n` by the local energies on `z + □_{n+1}`
and the cutoff `ζ` is supported where the `2·3^n`-neighbourhood lies in `W`, then
`‖ζ G‖_{L̲^p(W)} ≤ α ‖v‖_{L̲²(W)} + β ‖w‖_{L̲^p(W)}` (`1 ≤ p < 2`). -/
theorem l2b_E3_core (n : ℕ) {W : Set (Vec d)} (hWm : MeasurableSet W) (hW0 : volume W ≠ 0)
    (hWT : volume W ≠ ⊤) {ζ : Vec d → ℝ} (hζ : ∀ x, |ζ x| ≤ 1)
    (hmarg : ∀ x, ζ x ≠ 0 → ∀ y : Vec d, (∀ i, |y i - x i| ≤ 2 * 3 ^ n) → y ∈ W)
    {G : Vec d → Vec d} (hGm : AEStronglyMeasurable (fun x => ζ x • G x) (volume.restrict W))
    {v w : Vec d → ℝ} (hvm : AEStronglyMeasurable v (volume.restrict W))
    (hwm : AEStronglyMeasurable w (volume.restrict W)) {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2)
    {α β : ℝ≥0∞}
    (hG : ∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ W →
      ∀ x ∈ l2b_cell (l2b_pt n k) n, ENNReal.ofReal ‖G x‖ ≤
        α * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
            (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖v x‖ₑ) 2 +
          β * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
            (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖w x‖ₑ) p) :
    lpBar W (ENNReal.ofReal p) (fun x => ζ x • G x) ≤
      α * lpBar W (ENNReal.ofReal 2) v + β * lpBar W (ENNReal.ofReal p) w := by
  have hp0 : 0 < p := by linarith only [hp1]
  have key := l2b_grid_bound n (W := W) (S := W) hWm (fun x => ‖v x‖ₑ) (fun x => ‖w x‖ₑ) hp1 hp2
    (α := α) (β := β) (g := fun x => ‖ζ x • G x‖ₑ)
    (fun k hk x hx => by
      refine le_trans ?_ (hG k hk x hx)
      exact (l2b_enorm_smul_le (hζ x) (G x)).trans (le_of_eq (ofReal_norm _).symm))
    (fun x hx hx' => by
      by_contra hne
      have hz : ζ x ≠ 0 := fun h0 => hne (by simp [h0])
      obtain ⟨k, hk⟩ := l2b_exists_cell n (hmarg x hz)
      exact hx' k.1 k.2 hk)
  rw [l2b_lpBar_eq hp0 hGm, l2b_lpBar_eq (by norm_num) hvm, l2b_lpBar_eq hp0 hwm]
  refine (mul_le_mul' le_rfl key).trans ?_
  rw [mul_add]
  refine le_of_eq (congrArg₂ _ ?_ ?_)
  · rw [← l2b_vol_exponent hW0 hWT p]
    ring
  · ring

theorem l2b_lipGradient_measurable (ζ : Vec d → ℝ) : Measurable (lipGradient ζ) :=
  measurable_pi_iff.2 fun i => measurable_fderiv_apply_const ℝ ζ (basisVec i)

theorem l2b_lpBar_eq_eLpNorm {V : Set (Vec d)} {q : ℝ} (hq : 0 < q) {E : Type*}
    [NormedAddCommGroup E] {F : Vec d → E} (hF : AEStronglyMeasurable F (volume.restrict V)) :
    lpBar V (ENNReal.ofReal q) F =
      (volume V)⁻¹ ^ (1 / q) * eLpNorm F (ENNReal.ofReal q) (volume.restrict V) := by
  have h1 : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold lpBar
  rw [eLpNorm_smul_measure_of_ne_top h1 F _ hF, smul_eq_mul]
  congr 3
  rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hq.le, one_div]

/-- The pairing integrand of the layer term. -/
theorem l2b_pairing_eq {A : Set (Vec d)} {ζ : Vec d → ℝ} (hgrad0 : ∀ x, x ∉ A → lipGradient ζ x = 0)
    (G : Vec d → Vec d) (ψ : Vec d → ℝ) (x : Vec d) :
    vecDot (lipGradient ζ x) (G x) * ψ x =
      vecDot (A.indicator G x) (ψ x • lipGradient ζ x) := by
  by_cases hx : x ∈ A
  · simp only [Set.indicator_of_mem hx, vecDot, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  · simp [hgrad0 x hx, vecDot]

/-- The `ψ ∇ζ` factor is controlled by the layer Poincaré inequality. -/
theorem l2b_lpBar_psi_grad_le {W A : Set (Vec d)} (hAm : MeasurableSet A) (hAW : A ⊆ W)
    {ζ : Vec d → ℝ} {r CP : ℝ} (hr : 0 < r)
    (hgrad : ∀ x, ‖lipGradient ζ x‖ ≤ 1 / r) (hgrad0 : ∀ x, x ∉ A → lipGradient ζ x = 0)
    {q : ℝ} (hq : 0 < q) (ψ : H10Function W)
    (hPoinc : eLpNorm ψ.toH1Function.toFun (ENNReal.ofReal q) (volume.restrict A) ≤
      ENNReal.ofReal (CP * r) * eLpNorm (fun x => ‖ψ.toH1Function.grad x‖) (ENNReal.ofReal q)
        (volume.restrict W)) :
    lpBar W (ENNReal.ofReal q) (fun x => ψ.toH1Function.toFun x • lipGradient ζ x) ≤
      ENNReal.ofReal CP * lpBar W (ENNReal.ofReal q) ψ.toH1Function.grad := by
  have hψm : AEStronglyMeasurable ψ.toH1Function.toFun (volume.restrict W) :=
    ψ.toH1Function.memL2.aestronglyMeasurable
  have hgm : AEStronglyMeasurable ψ.toH1Function.grad (volume.restrict W) :=
    (aemeasurable_pi_iff.2 fun i =>
      (ψ.toH1Function.gradMemL2 i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hgm' : AEStronglyMeasurable (fun x => ψ.toH1Function.toFun x • lipGradient ζ x)
      (volume.restrict W) :=
    hψm.smul (l2b_lipGradient_measurable ζ).aestronglyMeasurable
  rw [l2b_lpBar_eq_eLpNorm hq hgm', l2b_lpBar_eq_eLpNorm hq hgm, mul_left_comm]
  refine mul_le_mul' le_rfl ?_
  have he1 : ‖(1 / r : ℝ)‖ₑ = ENNReal.ofReal (1 / r) := by
    rw [← ofReal_norm, Real.norm_of_nonneg (by positivity)]
  have hpt : ∀ x, ‖ψ.toH1Function.toFun x • lipGradient ζ x‖ₑ ≤
      ‖(1 / r) • A.indicator ψ.toH1Function.toFun x‖ₑ := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      calc ‖ψ.toH1Function.toFun x • lipGradient ζ x‖ₑ
          = ‖ψ.toH1Function.toFun x‖ₑ * ‖lipGradient ζ x‖ₑ := enorm_smul _ _
        _ ≤ ‖ψ.toH1Function.toFun x‖ₑ * ENNReal.ofReal (1 / r) :=
            mul_le_mul' le_rfl (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hgrad x))
        _ = ‖(1 / r) • ψ.toH1Function.toFun x‖ₑ := by
            rw [enorm_smul, mul_comm, he1]
    · simp [hgrad0 x hx]
  refine (eLpNorm_mono_enorm hgm' hpt).trans ?_
  have hcs : eLpNorm (fun x => (1 / r) • A.indicator ψ.toH1Function.toFun x) (ENNReal.ofReal q)
      (volume.restrict W) = ‖(1 / r : ℝ)‖ₑ * eLpNorm (A.indicator ψ.toH1Function.toFun)
        (ENNReal.ofReal q) (volume.restrict W) :=
    eLpNorm_const_smul (1 / r : ℝ) (A.indicator ψ.toH1Function.toFun) (ENNReal.ofReal q)
      (volume.restrict W)
  rw [hcs, eLpNorm_indicator_eq_eLpNorm_restrict hAm,
    Measure.restrict_restrict hAm, Set.inter_eq_left.2 hAW]
  calc ‖(1 / r : ℝ)‖ₑ * eLpNorm ψ.toH1Function.toFun (ENNReal.ofReal q) (volume.restrict A)
      ≤ ‖(1 / r : ℝ)‖ₑ * (ENNReal.ofReal (CP * r) * eLpNorm (fun x => ‖ψ.toH1Function.grad x‖)
          (ENNReal.ofReal q) (volume.restrict W)) := mul_le_mul' le_rfl hPoinc
    _ = ENNReal.ofReal CP * eLpNorm ψ.toH1Function.grad (ENNReal.ofReal q) (volume.restrict W) := by
        have hn : eLpNorm (fun x => ‖ψ.toH1Function.grad x‖) (ENNReal.ofReal q)
            (volume.restrict W) = eLpNorm ψ.toH1Function.grad (ENNReal.ofReal q)
              (volume.restrict W) := eLpNorm_norm _ hgm
        rw [hn, ← mul_assoc, he1, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp


/-- The layer bound for the indicator of `A`: the normalized `L^p(W)` norm of `1_A G`. -/
theorem l2b_layer_bound (n : ℕ) {W A : Set (Vec d)} (hAm : MeasurableSet A) (hAW : A ⊆ W)
    (hW0 : volume W ≠ 0) (hWT : volume W ≠ ⊤)
    (hmarg : ∀ x ∈ A, ∀ y : Vec d, (∀ i, |y i - x i| ≤ 2 * 3 ^ n) → y ∈ W)
    {G : Vec d → Vec d} (hGm : AEStronglyMeasurable G (volume.restrict W))
    {v w : Vec d → ℝ} (hvm : AEStronglyMeasurable v (volume.restrict W))
    (hwm : AEStronglyMeasurable w (volume.restrict W)) {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2)
    {α β : ℝ≥0∞}
    (hG : ∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ W →
      ∀ x ∈ l2b_cell (l2b_pt n k) n, ENNReal.ofReal ‖G x‖ ≤
        α * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
            (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖v x‖ₑ) 2 +
          β * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
            (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖w x‖ₑ) p) :
    lpBar W (ENNReal.ofReal p) (A.indicator G) ≤
      α * (volume A * (volume W)⁻¹) ^ (1 / p - 1 / 2) * lpBar W (ENNReal.ofReal 2) v +
        β * lpBar W (ENNReal.ofReal p) w := by
  have hp0 : 0 < p := by linarith only [hp1]
  have hθ : 0 ≤ 1 / p - 1 / 2 := by
    have : 1 / 2 ≤ 1 / p := by
      rw [div_le_div_iff₀ (by norm_num) hp0]; linarith only [hp2]
    linarith only [this]
  have key := l2b_grid_bound n (W := W) (S := A) hAm (fun x => ‖v x‖ₑ) (fun x => ‖w x‖ₑ) hp1 hp2
    (α := α) (β := β) (g := fun x => ‖G x‖ₑ)
    (fun k hk x hx => by rw [← ofReal_norm]; exact hG k hk x hx)
    (fun x hx hx' => by
      exfalso
      obtain ⟨k, hk⟩ := l2b_exists_cell n (hmarg x hx)
      exact hx' k.1 k.2 hk)
  have hint : ∫⁻ x in W, ‖A.indicator G x‖ₑ ^ p = ∫⁻ x in A, ‖G x‖ₑ ^ p := by
    have : (fun x => ‖A.indicator G x‖ₑ ^ p) = A.indicator (fun x => ‖G x‖ₑ ^ p) := by
      funext x
      by_cases hx : x ∈ A
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hp0]
    rw [this, lintegral_indicator hAm, Measure.restrict_restrict hAm, Set.inter_eq_left.2 hAW]
  rw [l2b_lpBar_eq hp0 (hGm.indicator hAm), hint, l2b_lpBar_eq (by norm_num) hvm,
    l2b_lpBar_eq hp0 hwm]
  refine (mul_le_mul' le_rfl key).trans ?_
  rw [mul_add]
  refine le_of_eq (congrArg₂ _ ?_ ?_)
  · have hs : (volume W)⁻¹ ^ (1 / p) = (volume W)⁻¹ ^ (1 / p - 1 / 2) * (volume W)⁻¹ ^ (1 / (2 : ℝ)) := by
      rw [← ENNReal.rpow_add _ _ (by simpa only [ne_eq, ENNReal.inv_eq_zero] using hWT) (by simpa only [ne_eq, ENNReal.inv_eq_top] using hW0)]; congr 1; ring
    rw [hs, ENNReal.mul_rpow_of_nonneg _ _ hθ]
    ring
  · ring


/-- **The layer term** (`e.Dir.new.boundary.flux.term`), deterministic core.
With `A ⊇ {∇ζ ≠ 0}` a measurable subset of `W`, `|∇ζ| ≤ 1/r`, the layer Poincaré inequality
`‖ψ‖_{L^q(A)} ≤ CP r ‖∇ψ‖_{L^q(W)}` for `ψ ∈ H¹₀(W)` (`q = p/(p-1)`), and the pointwise grid
bound for `G`: `‖∇ζ·G‖_{W̲^{-1,p}(W)} ≤ d CP (α (|A|/|W|)^{1/p-1/2} ‖v‖_{L̲²(W)} + β ‖w‖_{L̲^p(W)})`. -/
theorem l2b_E2_core (n : ℕ) {W A : Set (Vec d)} (hAm : MeasurableSet A) (hAW : A ⊆ W)
    (hW0 : volume W ≠ 0) (hWT : volume W ≠ ⊤) {ζ : Vec d → ℝ} {r CP : ℝ} (hr : 0 < r)
    (hgrad : ∀ x, ‖lipGradient ζ x‖ ≤ 1 / r)
    (hgrad0 : ∀ x, x ∉ A → lipGradient ζ x = 0)
    (hmarg : ∀ x ∈ A, ∀ y : Vec d, (∀ i, |y i - x i| ≤ 2 * 3 ^ n) → y ∈ W)
    {G : Vec d → Vec d} (hGm : AEStronglyMeasurable G (volume.restrict W))
    {v w : Vec d → ℝ} (hvm : AEStronglyMeasurable v (volume.restrict W))
    (hwm : AEStronglyMeasurable w (volume.restrict W)) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    {α β : ℝ≥0∞}
    (hG : ∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ W →
      ∀ x ∈ l2b_cell (l2b_pt n k) n, ENNReal.ofReal ‖G x‖ ≤
        α * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
            (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖v x‖ₑ) 2 +
          β * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
            (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖w x‖ₑ) p)
    (hPoinc : ∀ ψ : H10Function W,
      eLpNorm ψ.toH1Function.toFun (ENNReal.ofReal (p / (p - 1))) (volume.restrict A) ≤
        ENNReal.ofReal (CP * r) * eLpNorm (fun x => ‖ψ.toH1Function.grad x‖)
          (ENNReal.ofReal (p / (p - 1))) (volume.restrict W)) :
    wMinusOneBar W (ENNReal.ofReal p) (fun x => vecDot (lipGradient ζ x) (G x)) ≤
      ENNReal.ofReal (d * CP) *
        (α * (volume A * (volume W)⁻¹) ^ (1 / p - 1 / 2) * lpBar W (ENNReal.ofReal 2) v +
          β * lpBar W (ENNReal.ofReal p) w) := by
  have hp0 : 0 < p := by linarith only [hp1]
  have hP1 : 1 < ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff hp0).2 hp1
  have hQ : (ENNReal.ofReal p).conjExponent = ENNReal.ofReal (p / (p - 1)) := by
    have := p14_conj hP1 ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hp0.le] at this
  have hq0 : 0 < p / (p - 1) := div_pos hp0 (by linarith only [hp1])
  have hlay := l2b_layer_bound n hAm hAW hW0 hWT hmarg hGm hvm hwm hp1.le hp2 hG
  unfold wMinusOneBar
  refine iSup₂_le fun ψ hψ => ?_
  have h1 : ∫ x in W, vecDot (lipGradient ζ x) (G x) * ψ.toH1Function.toFun x =
      ∫ x in W, vecDot (A.indicator G x) (ψ.toH1Function.toFun x • lipGradient ζ x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x =>
      l2b_pairing_eq hgrad0 G ψ.toH1Function.toFun x)
  rw [h1]
  have hψm : AEStronglyMeasurable ψ.toH1Function.toFun (volume.restrict W) :=
    ψ.toH1Function.memL2.aestronglyMeasurable
  have hgm' : AEStronglyMeasurable (fun x => ψ.toH1Function.toFun x • lipGradient ζ x)
      (volume.restrict W) :=
    hψm.smul (l2b_lipGradient_measurable ζ).aestronglyMeasurable
  refine (p14_holder_pairing hW0 hP1 ENNReal.ofReal_ne_top (hGm.indicator hAm) hgm').trans ?_
  rw [hQ] at hψ ⊢
  have hψ' := l2b_lpBar_psi_grad_le hAm hAW hr hgrad hgrad0 hq0 ψ (hPoinc ψ)
  have h2 : lpBar W (ENNReal.ofReal (p / (p - 1))) (fun x => ψ.toH1Function.toFun x • lipGradient ζ x)
      ≤ ENNReal.ofReal CP := by
    refine hψ'.trans ?_
    calc _ ≤ ENNReal.ofReal CP * 1 := mul_le_mul' le_rfl hψ
      _ = _ := mul_one _
  calc ENNReal.ofReal d * lpBar W (ENNReal.ofReal p) (A.indicator G) *
        lpBar W (ENNReal.ofReal (p / (p - 1))) (fun x => ψ.toH1Function.toFun x • lipGradient ζ x)
      ≤ ENNReal.ofReal d * (α * (volume A * (volume W)⁻¹) ^ (1 / p - 1 / 2) *
          lpBar W (ENNReal.ofReal 2) v + β * lpBar W (ENNReal.ofReal p) w) *
        ENNReal.ofReal CP := mul_le_mul' (mul_le_mul' le_rfl hlay) h2
    _ = _ := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg d)]; ring

theorem l2b_conj_exponent {p q : ℝ} (hpq : p.HolderConjugate q) :
    (ENNReal.ofReal p).conjExponent = ENNReal.ofReal q := by
  have hp0 : 0 < p := hpq.pos
  have hP1 : 1 < ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff hp0).2 hpq.lt
  have := p14_conj hP1 ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hp0.le, ← hpq.conjugate_eq] at this
  exact this

/-- The cell average `l2b_avg` is the normalized cube norm of the translated function. -/
theorem l2b_avg_eq_cubeLpENorm (m : ℕ) (z : Vec d) {g : Vec d → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : AEStronglyMeasurable (fun x => g (x + z))
      (volume.restrict (openCubeSet (originCube d (m : ℤ))))) :
    l2b_avg (ENNReal.ofReal (cubeVolume (originCube d (m : ℤ)))) (l2b_cell z m)
        (fun x => ‖g x‖ₑ) r =
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (m : ℤ))
        (ENNReal.ofReal r) (fun x => g (x + z)) := by
  have hv := cubeVolume_pos (originCube d (m : ℤ))
  have h0 : ENNReal.ofReal r ≠ 0 := by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hr
  rw [m1_cubeLpENorm_eq _ hr, eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ENNReal.ofReal_ne_top hg,
    ENNReal.toReal_ofReal hr.le, ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  unfold l2b_avg
  congr 1
  rw [← ENNReal.ofReal_inv_of_pos hv]
  congr 1
  have e1 : ∫⁻ x in openCubeSet (originCube d (m : ℤ)), ‖g (x + z)‖ₑ ^ r =
      ∫⁻ x in cubeSet (originCube d (m : ℤ)), ‖g (x + z)‖ₑ ^ r := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  rw [e1, wh2_lintegral_translate (cubeSet (originCube d (m : ℤ))) z (fun x => ‖g x‖ₑ ^ r)]
  rfl

/-- **Transfer of a local bound on the origin cube to a cell of the global solution.**  If a bound
for the mollified flux on `□_n` holds for every origin-frame solution `v` on `□_{n+1}` of the
field `a'`, then it holds, at `z + x₀`, for the global solution `u` on `W ⊇ z + □_{n+1}`, with the
normalized cell averages of `‖∇u‖` and `‖f‖` on `z + □_{n+1}`. -/
theorem l2b_cell_transfer (n : ℕ) {W : Set (Vec d)} (z : Vec d)
    (hsub : translateSet z (openCubeSet (originCube d ((n + 1 : ℕ) : ℤ))) ⊆ W)
    {a : CoeffField d} {u : H1Function W} {f : Vec d → ℝ}
    (hf : AEMeasurable f (volume.restrict W)) (hsol : IsWeakSolutionOn a W u f (fun _ => 0))
    (M : Vec d → Mat d) {a' : CoeffField d} (hab : ∀ x, a' x = a (x + z)) {h : ℝ}
    {η : Vec d → ℝ} {p : ℝ} (hp : 0 < p) {α β : ℝ≥0∞}
    (hM : ∀ (v : H1Function (openCubeSet (originCube d ((n + 1 : ℕ) : ℤ)))) (g : Vec d → ℝ),
      IsWeakSolutionOn a' (openCubeSet (originCube d ((n + 1 : ℕ) : ℤ))) v g (fun _ => 0) →
      ∀ x0 ∈ cubeSet (originCube d (n : ℤ)),
        ENNReal.ofReal ‖a16_mollify d h η (fun x => matVecMul (M (x + z)) (v.grad x)) x0‖ ≤
          α * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
              (originCube d ((n + 1 : ℕ) : ℤ)) 2 (fun x => eucNorm (v.grad x)) +
            β * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
              (originCube d ((n + 1 : ℕ) : ℤ)) (ENNReal.ofReal p) g) :
    ∀ x0 ∈ cubeSet (originCube d (n : ℤ)),
      ENNReal.ofReal ‖a16_mollify d h η (fun y => matVecMul (M y) (u.grad y)) (z + x0)‖ ≤
        α * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
            (l2b_cell z (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 +
          β * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
            (l2b_cell z (n + 1)) (fun x => ‖f x‖ₑ) p := by
  intro x0 hx0
  set Q := originCube d ((n + 1 : ℕ) : ℤ) with hQ
  set v := wh2_cubeFun Q z hsub u with hv
  have hsol_v : IsWeakSolutionOn a' (openCubeSet Q) v (fun x => f (x + z)) (fun _ => 0) := by
    have : a' = fun x => a (x + z) := funext hab
    rw [this]
    exact wh2_isWeakSolutionOn_cube Q z hsub hsol
  have key := hM v _ hsol_v x0 hx0
  have hfun : (fun y => matVecMul (M (z + y)) (u.grad (z + y))) =
      fun x => matVecMul (M (x + z)) (v.grad x) := by
    funext y
    simp only [hv, wh2_cubeFun_grad, add_comm z y]
  rw [a16_mollify_translate, hfun]
  refine key.trans (le_of_eq ?_)
  have e1 := l2b_avg_eq_cubeLpENorm (n + 1) z (g := fun x => eucNorm (u.grad x)) (r := 2)
    (by norm_num) (wh2_aemeasurable_eucNorm v).aestronglyMeasurable
  have e2 := l2b_avg_eq_cubeLpENorm (n + 1) z (g := f) (r := p) hp
    (wh2_aemeasurable_translate z hsub hf).aestronglyMeasurable
  simp only [ENNReal.ofReal_ofNat] at e1
  rw [e1, e2]
  rfl

/-- **The almost-sure cell bound for the mollified flux** -/
theorem l2b_ae_cell (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hInputs :
        ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ, ∀ ε ρ M : ℝ,
          0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M → ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P :
          MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (hJ2 :
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 :
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 → ∃ X0 :
          SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0
          omega) ∧ Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧ ∀ᵐ
          omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure, ∀ m n : ℕ, X0
          omega ≤ (3 : ℝ) ^ m → Lhat ≤ (m : ℝ) → (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) → n ≤ m
          → (∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆ Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ)) → Homogenization.HomogenizationErrorOnCube
          (Homogenization.originCube d (n : ℤ)) (1 / 9) Homogenization.MultiscaleExponent.infinity
          (Homogenization.MultiscaleExponent.finite 2) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 :
          Homogenization.Mat d)) ≤ ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
          Homogenization.LambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
          (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) + SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
          (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
          (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)))⁻¹ ≤ C ∧ (∀ u : Homogenization.AHarmonicFunction (fun x => nu • (1 :
          Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n :
          ℤ) - 3) * (k i : ℝ)) + x)) (Homogenization.openCubeSet (Homogenization.originCube d (n :
          ℤ))), ENNReal.ofReal
          (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (Homogenization.originCube d (n : ℤ)) (1 / 4) (fun x => Homogenization.matVecMul (nu • (1
          : Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField
          omega (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^
          ((n : ℤ) - 3) * (k i : ℝ)) + x) -
          SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 : Homogenization.Mat
          d)) (u.toH1.grad x))) ≤ ENNReal.ofReal (C * Real.sqrt
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1
          - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
          (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧ ENNReal.ofReal
          (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤ ENNReal.ofReal (C *
          (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
          Real.sqrt nu) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
          (Homogenization.originCube d (n : ℤ)) 2 (fun x => Real.sqrt (Homogenization.vecNormSq
          (u.toH1.grad x))) ∧ ∃ w : Homogenization.AHarmonicFunction (fun _ => (1 :
          Homogenization.Mat d)) (Homogenization.openCubeSet (Homogenization.originCube d ((n : ℤ) -
          1))), ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d ((n : ℤ) -
          1)) 2 (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤ ENNReal.ofReal (C * (ε * (m : ℝ) ^
          (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * (Real.sqrt
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
          (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧ Homogenization.matNorm
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
          Homogenization.sigmaCoarse (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))
          (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) - 1) + Homogenization.matNorm
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
          Homogenization.sigmaStarCoarse (Homogenization.cubeSet (Homogenization.originCube d (n :
          ℤ))) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) - 1) ≤ C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧ ENNReal.ofReal ((m :
          ℝ)⁻¹) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (m
          : ℤ)) ∞ (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) + ENNReal.ofReal ((3 : ℝ)
          ^ (-((1 / 4 : ℝ) * (m : ℝ)))) * SuperdiffusionCLT.Section2.Norms.matHatNegENorm
          (Homogenization.originCube d (m : ℤ)) (1 / 4) 2
          (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤ ENNReal.ofReal ((m : ℝ)
          ^ ρ)) :

    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ, ∀ ε ρ M : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M → ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P), SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P → SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P → SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 → ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧ Homogenization.IndependentSums.IsBigO P.toMeasure (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure, ∀ m n : ℕ, X0 omega ≤ (3 : ℝ) ^ m → Lhat ≤ (m : ℝ) → (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) → n + 1 ≤ m →
      ∀ W : Set (Homogenization.Vec d), W ⊆ Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ)) →
      ∀ (u : Homogenization.H1Function W) (f : Homogenization.Vec d → ℝ), AEMeasurable f (MeasureTheory.volume.restrict W) →
      IsWeakSolutionOn (fun x => nu • (1 : Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) x) W u f (fun _ => 0) →
      ∀ (η : Homogenization.Vec d → ℝ) (A : ℝ) (L : NNReal), (∀ w, |η w| ≤ A) → LipschitzWith L η →
      (∀ w, (∃ i, 1 < |w i|) → η w = 0) →
      ∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ W →
      ∀ x ∈ l2b_cell (l2b_pt n k) n,
        (ENNReal.ofReal ‖a16_mollify d ((3 : ℝ) ^ (n : ℤ)) η (fun y => Homogenization.matVecMul ((nu • (1 : Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) y) - (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Homogenization.Mat d)) (u.grad y)) x‖ ≤
          ENNReal.ofReal (3 ^ d * (6 * (L : ℝ) + A)) *
            (ENNReal.ofReal (C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu) * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ)))) (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 + ENNReal.ofReal ((C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu + C * (|nu - (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)| + (m : ℝ) ^ (1 + ρ))) * (C * (3 : ℝ) ^ ((n + 1 : ℕ) : ℤ) / nu)) * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ)))) (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖f x‖ₑ) (Real.conjExponent (sobStar d)))) ∧
        (ENNReal.ofReal ‖a16_mollify d ((3 : ℝ) ^ (n : ℤ)) η (fun y => Homogenization.matVecMul (nu • (1 : Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) y) (u.grad y)) x‖ ≤
          (ENNReal.ofReal (3 ^ d * (6 * (L : ℝ) + A)) * (ENNReal.ofReal (C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu) * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ)))) (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 + ENNReal.ofReal ((C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu + C * (|nu - (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)| + (m : ℝ) ^ (1 + ρ))) * (C * (3 : ℝ) ^ ((n + 1 : ℕ) : ℤ) / nu)) * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ)))) (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖f x‖ₑ) (Real.conjExponent (sobStar d))) +
            ENNReal.ofReal ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (3 ^ d * (6 * (L : ℝ) + A))) *
              (ENNReal.ofReal (C * (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ)))) (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 + ENNReal.ofReal ((C * (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu + C) * (C * (3 : ℝ) ^ ((n + 1 : ℕ) : ℤ) / nu)) * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ)))) (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖f x‖ₑ) (Real.conjExponent (sobStar d))))) := by
  obtain ⟨C, hC, H⟩ := m1_mollified_flux d hd hInputs
  refine ⟨C, hC, fun nu hnu hnu1 cStar hcStar K ε ρ M hε hε1 hρ hρ1 hCM => ?_⟩
  obtain ⟨Lhat, hL, H2⟩ := H nu hnu hnu1 cStar hcStar K ε ρ M hε hε1 hρ hρ1 hCM
  refine ⟨Lhat, hL, fun P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 => ?_⟩
  obtain ⟨X0, hm, h1, hO, hae⟩ := H2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨X0, hm, h1, hO, ?_⟩
  filter_upwards [hae 0] with omega hω
  intro m n hX hLm hn1 hn2 W hWm u f hf hsol η A L hηA hηL hη0 k hk x hx
  have hX0 : X0 (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence 0 omega) ≤
      (3 : ℝ) ^ m := by rwa [wh2_translateSequence_zero]
  set z : Vec d := l2b_pt n k with hz
  have hsub : translateSet z (openCubeSet (originCube d ((n + 1 : ℕ) : ℤ))) ⊆ W := by
    refine Set.Subset.trans (fun y hy => ?_) hk
    rw [mem_translateSet_iff_sub_mem] at hy
    exact (mem_translateSet_iff_sub_mem (U := cubeSet (originCube d ((n + 1 : ℕ) : ℤ)))).2
      (openCubeSet_subset_cubeSet _ hy)
  have himg := wh2_shift_image_subset (n + 1) m z (hsub.trans hWm)
  have hz9 : (fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (((fun i => 9 * k i) i : ℤ) : ℝ)) = z := by
    funext i
    simp only [hz, l2b_pt]
    have : (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * 9 = 3 ^ n := by
      have e : ((n + 1 : ℕ) : ℤ) - 3 = (n : ℤ) - 2 := by push_cast; ring
      rw [e, zpow_sub₀ (by norm_num)]
      simp only [zpow_natCast]
      norm_num
    have h9 : (((9 * k i : ℤ)) : ℝ) = 9 * (k i : ℝ) := by push_cast; ring
    show (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (((9 * k i : ℤ)) : ℝ) = (3 : ℝ) ^ n * (k i : ℝ)
    rw [h9, ← mul_assoc, this]
  have himg' : (fun x => (fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) *
      (((fun i => 9 * k i) i : ℤ) : ℝ)) + x) '' cubeSet (originCube d ((n + 1 : ℕ) : ℤ)) ⊆
        cubeSet (originCube d (m : ℤ)) := by
    rw [hz9]; exact himg
  have key := hω m n hX0 hLm hn1 hn2 (fun i => 9 * k i) himg'
  have hs : 1 < sobStar d := by linarith only [two_lt_sobStar hd]
  have hHC : (sobStar d).HolderConjugate (Real.conjExponent (sobStar d)) :=
    Real.HolderConjugate.conjExponent hs
  have hconj : (ENNReal.ofReal (sobStar d)).conjExponent =
      ENNReal.ofReal (Real.conjExponent (sobStar d)) := l2b_conj_exponent hHC
  have hp0 : 0 < Real.conjExponent (sobStar d) := hHC.symm.pos
  have hfield : ∀ x, nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega (translateSet 0 (cubeSet (originCube d (m : ℤ))))
        (0 + (fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (((fun i => 9 * k i) i : ℤ) : ℝ)) + x) =
      nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (cubeSet (originCube d (m : ℤ))) (x + z) := by
    intro x
    rw [hz9, translateSet_zero, zero_add, add_comm z x]
  have hfun : (fun x => nu • (1 : Mat d) +
      SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (translateSet 0 (cubeSet (originCube d (m : ℤ))))
        (0 + (fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (((fun i => 9 * k i) i : ℤ) : ℝ)) + x)) =
      fun x => nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (cubeSet (originCube d (m : ℤ))) (x + z) := funext hfield
  have hx0 : x - z ∈ cubeSet (originCube d (n : ℤ)) := (mem_translateSet_iff_sub_mem).1 hx
  have hxz : z + (x - z) = x := add_sub_cancel z x
  have hsol' : IsWeakSolutionOn (fun x => nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x) W u f (fun _ => 0) := hsol
  refine ⟨?_, ?_⟩
  · have b1 := l2b_cell_transfer n z hsub hf hsol'
      (M := fun y => (nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (cubeSet (originCube d (m : ℤ))) y) - (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Mat d))
      (a' := fun x => nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (cubeSet (originCube d (m : ℤ))) (x + z)) (fun x => rfl)
      (h := (3 : ℝ) ^ (n : ℤ)) (η := η) hp0
      (α := ENNReal.ofReal (3 ^ d * (6 * (L : ℝ) + A)) *
        ENNReal.ofReal (C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) *
          (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu))
      (β := ENNReal.ofReal (3 ^ d * (6 * (L : ℝ) + A)) *
        ENNReal.ofReal ((C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) *
          Real.sqrt nu + C * (|nu - (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)| + (m : ℝ) ^ (1 + ρ))) *
          (C * (3 : ℝ) ^ ((n + 1 : ℕ) : ℤ) / nu)))
      (fun v g hv x0 hx0 => by
        have hv' := hv
        rw [← hfun] at hv'
        have := (key v g hv' η A L hηA hηL hη0 x0 hx0).1
        rw [hconj] at this
        refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
        · congr 3
          funext y
          rw [hfield y]
        · simp only [eucNorm]; ring)
      (x - z) hx0
    rw [hxz] at b1
    refine b1.trans (le_of_eq ?_)
    ring
  · have b3 := l2b_cell_transfer n z hsub hf hsol'
      (M := fun y => nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (cubeSet (originCube d (m : ℤ))) y)
      (a' := fun x => nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (cubeSet (originCube d (m : ℤ))) (x + z)) (fun x => rfl)
      (h := (3 : ℝ) ^ (n : ℤ)) (η := η) hp0
      (α := ENNReal.ofReal (3 ^ d * (6 * (L : ℝ) + A)) * ENNReal.ofReal (C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu) + ENNReal.ofReal ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (3 ^ d * (6 * (L : ℝ) + A))) * ENNReal.ofReal (C * (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu))
      (β := ENNReal.ofReal (3 ^ d * (6 * (L : ℝ) + A)) * ENNReal.ofReal ((C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu + C * (|nu - (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)| + (m : ℝ) ^ (1 + ρ))) * (C * (3 : ℝ) ^ ((n + 1 : ℕ) : ℤ) / nu)) + ENNReal.ofReal ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (3 ^ d * (6 * (L : ℝ) + A))) * ENNReal.ofReal ((C * (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu + C) * (C * (3 : ℝ) ^ ((n + 1 : ℕ) : ℤ) / nu)))
      (fun v g hv x0 hx0 => by
        have hv' := hv
        rw [← hfun] at hv'
        have := (key v g hv' η A L hηA hηL hη0 x0 hx0).2.2
        rw [hconj] at this
        refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
        · congr 3
          funext y
          rw [hfield y]
        · simp only [eucNorm]; ring)
      (x - z) hx0
    rw [hxz] at b3
    refine b3.trans (le_of_eq ?_)
    ring

/-- The cell `□_1 ⊆ □_2`. -/
theorem l2b_witness_cell_subset :
    l2b_cell (l2b_pt 0 (0 : Fin 2 → ℤ)) 1 ⊆ openCubeSet (originCube 2 ((2 : ℕ) : ℤ)) := by
  intro x hx
  rw [l2b_mem_cell] at hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have := hx i
  simp only [l2b_pt] at this
  norm_num at this ⊢
  constructor <;> linarith only [this.1, this.2]

/-- Witness for the transfer lemma: the zero solution of any field on `□_2`, the cell `□_1`,
and the zero flux matrix (for which the local bound is immediate). -/
example : True := by
  have hsub : translateSet (l2b_pt 0 (0 : Fin 2 → ℤ)) (openCubeSet (originCube 2 (((0 + 1 : ℕ)) : ℤ))) ⊆
      openCubeSet (originCube 2 ((2 : ℕ) : ℤ)) := by
    refine Set.Subset.trans (fun y hy => ?_) l2b_witness_cell_subset
    rw [mem_translateSet_iff_sub_mem] at hy
    exact (mem_translateSet_iff_sub_mem (U := cubeSet (originCube 2 ((0 + 1 : ℕ) : ℤ)))).2
      (openCubeSet_subset_cubeSet _ hy)
  have h := l2b_cell_transfer (d := 2) 0 (W := openCubeSet (originCube 2 ((2 : ℕ) : ℤ)))
    (l2b_pt 0 (0 : Fin 2 → ℤ)) hsub (a := fun _ => (1 : Mat 2))
    (u := (0 : H10Function (openCubeSet (originCube 2 ((2 : ℕ) : ℤ)))).toH1Function)
    (f := fun _ => 0) aemeasurable_const
    (by
      intro φ
      have h0 : ∀ x, (0 : H10Function (openCubeSet (originCube 2 ((2 : ℕ) : ℤ)))).toH1Function.grad x = 0 :=
        fun _ => rfl
      simp [vecDot, matVecMul, h0])
    (fun _ => 0) (a' := fun _ => (1 : Mat 2)) (fun _ => rfl) (h := 1) (η := fun _ => 0)
    (p := 1) one_pos (α := 0) (β := 0)
    (fun v g hv x0 hx0 => by
      have : a16_mollify 2 1 (fun _ => (0 : ℝ)) (fun x => matVecMul (0 : Mat 2) (v.grad x)) x0 = 0 := by
        funext i
        simp [a16_mollify, a16_kernel]
      simp [this])
  trivial

end SuperdiffusionCLT.Section7
