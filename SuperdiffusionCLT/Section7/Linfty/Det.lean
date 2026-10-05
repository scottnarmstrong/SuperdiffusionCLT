/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.DGInterior
public import SuperdiffusionCLT.Section7.Linfty.DGBoundary
public import SuperdiffusionCLT.Section7.Prereq.WhitneyLocalB
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.IterationB
public import SuperdiffusionCLT.Section7.Prereq.L2InteriorD
public import SuperdiffusionCLT.Section7.Prereq.L2BoundaryC

/-!
# The deterministic assembly of the `L^∞` proposition: the De Giorgi errors

The error carriers `linfDG`, `linfErr`, and the two almost-everywhere De Giorgi bounds used by the
assembly: away from the boundary, `|v - η_h ∗ ũ|` on every cell whose enlarged cell
lies in `W`; near the boundary, `|v - g̃|` on every cell meeting the layer of width `10 h`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The De Giorgi error: the bound of `|v - η ∗ v|` away from the boundary and of `|v - g̃|` near
it, with `q` the power of the ellipticity ratio and `h` the mollification scale. -/
noncomputable def linfDG (q h ν Gb Bb F G : ℝ) : ℝ :=
  q * (h * Gb + h ^ 2 / ν * F + Bb + h * G)

/-- The total error of the deterministic comparison of `v` with the homogenized solution. -/
noncomputable def linfErr (L h s ν Λ q θ α β α' β' Gb Bb F G : ℝ) : ℝ :=
  L * s⁻¹ * (α * Gb + β * F) + linfDG q h ν Gb Bb F G +
    L * θ * (linfDG q h ν Gb Bb F G / h + G + s⁻¹ * (α' * Gb + β' * F)) + L * s⁻¹ * h * F +
    h * (1 + s⁻¹ * Λ) * (Λ / ν * G + L / ν * F)

/-- A mollification with a nonnegative normalized kernel of radius `h` stays within `B` of `c`
when `u` does almost everywhere on the closed sup-ball of radius `h`. -/
theorem linf_det_moll_le {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hηc : Continuous η)
    (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1) (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    {u : Vec d → ℝ} (hu : LocallyIntegrable u volume) {x : Vec d} {c B : ℝ}
    (hb : ∀ᵐ w ∂(volume : Measure (Vec d)), w ∈ Metric.closedBall x h → |u w - c| ≤ B) :
    |l2a_moll d h η u x - c| ≤ B := by
  set k : Vec d → ℝ := fun w => a16_kernel d h η (x - w) with hk
  have hk0 : ∀ w, 0 ≤ k w := fun w =>
    mul_nonneg (pow_nonneg (inv_nonneg.2 hh.le) _) (hη0 _)
  have hkz : ∀ w, w ∉ Metric.closedBall x h → k w = 0 := by
    intro w hw
    rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hw
    have : h < ‖x - w‖ := by rwa [← norm_neg, neg_sub]
    exact l2a_kernel_eq_zero_of_norm hh hηs this
  have hkc : Continuous k := (a16_kernel_continuous hηc).comp (continuous_const.sub continuous_id)
  have hkcs : HasCompactSupport k :=
    (l2a_kernel_compact hh hηs).comp_homeomorph (Homeomorph.subLeft x)
  have hkI : Integrable k := hkc.integrable_of_hasCompactSupport hkcs
  have hkint : ∫ w, k w = 1 := by
    have := integral_sub_left_eq_self (fun t => a16_kernel d h η t) (volume : Measure (Vec d)) x
    rw [hk]
    simp only
    rw [this, linf_dgi_kernel_integral hh, hη1]
  have hku : Integrable (fun w => k w * u w) :=
    (hu.integrable_smul_left_of_hasCompactSupport hkc hkcs : _)
  have hmoll : l2a_moll d h η u x - c = ∫ w, k w * (u w - c) := by
    have e : (fun w => k w * (u w - c)) = fun w => k w * u w - c * k w := by
      funext w; ring
    rw [e, integral_sub hku (hkI.const_mul c), integral_const_mul, hkint, mul_one]
    rfl
  rw [hmoll]
  have hnorm : ‖∫ w, k w * (u w - c)‖ ≤ ∫ w, k w * B := by
    refine norm_integral_le_of_norm_le (hkI.mul_const B) ?_
    filter_upwards [hb] with w hw
    by_cases hwb : w ∈ Metric.closedBall x h
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hk0 w)]
      exact mul_le_mul_of_nonneg_left (hw hwb) (hk0 w)
    · simp [hkz w hwb]
  rw [Real.norm_eq_abs, integral_mul_const, hkint, one_mul] at hnorm
  exact hnorm

/-- The open cube `y + cu_m` lies in the half-open cell `y + □_m`. -/
theorem linf_det_shift_sub_cell (y : Vec d) (m : ℕ) :
    shiftCube y (m : ℤ) ⊆ l2b_cell y m := by
  intro x hx
  rw [rc_mem_shiftCube] at hx
  rw [l2b_mem_cell]
  intro i
  have h := abs_lt.1 (hx i)
  rw [zpow_natCast] at h
  constructor <;> linarith only [h.1, h.2]

/-- A point of the cell `y + □_n` and a point of the cube `y + cu_{n+1}` are within `2·3^n`. -/
theorem linf_det_dist_cell_cube {n : ℕ} {y x w : Vec d} (hx : x ∈ l2b_cell y n)
    (hw : w ∈ shiftCube y ((n : ℤ) + 1)) : dist w x ≤ 2 * (3 : ℝ) ^ n := by
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  rw [dist_pi_le_iff (by positivity)]
  intro i
  rw [Real.dist_eq]
  have a := (l2b_mem_cell.1 hx) i
  have b := abs_lt.1 ((rc_mem_shiftCube.1 hw) i)
  have e : (3 : ℝ) ^ ((n : ℤ) + 1) = 3 * 3 ^ n := by
    rw [zpow_add_one₀ (by norm_num), zpow_natCast, mul_comm]
  rw [e] at b
  rw [abs_le]
  constructor <;> linarith only [a.1, a.2, b.1, b.2]

theorem linf_det_zpow_two (n : ℕ) : (3 : ℝ) ^ ((n : ℤ) + 2) = 9 * 3 ^ n := by
  rw [zpow_add₀ (by norm_num), zpow_natCast, mul_comm]
  norm_num

/-- **Interior De Giorgi bound on the support of the cutoff**: almost every point
`y` with `ζ(y) ≠ 0` satisfies `|v(y) - η_h ∗ ũ(y)| ≤ C (Λ/ν)^p (h Gb + h² F/ν)`, for every
whole-space function `ũ` equal to `v` at distance at least `2 h` from `Wᶜ`. -/
theorem linf_det_int [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ν Λ : ℝ} {a : CoeffField d} {W : Set (Vec d)} {n : ℕ}, IsOpen W →
      0 < ν → IsEllipticFieldOn ν Λ W a → ∀ (f : Vec d → ℝ) (v : H1Function W),
      IsWeakSolutionOn a W v f (fun _ => 0) → AEStronglyMeasurable f (volume.restrict W) →
      ∀ {F Gb : ℝ}, 0 ≤ F → 0 ≤ Gb → (∀ᵐ x ∂volume.restrict W, |f x| ≤ F) →
      (∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ W →
          lpBar (shiftCube (l2b_pt n k) ((n : ℤ) + 1)) 2 (fun x => eucNorm (v.grad x)) ≤
            ENNReal.ofReal Gb) →
      ∀ (ũ : Vec d → ℝ), (∀ y ∈ W, 2 * (3 : ℝ) ^ n ≤ Metric.infDist y Wᶜ → ũ y = v.toFun y) →
      ∀ᵐ y ∂(volume : Measure (Vec d)), l2a_cutoff W (4 * (3 : ℝ) ^ n) y ≠ 0 →
        |v.toFun y - l2a_moll d ((3 : ℝ) ^ n) (li1_bump d) ũ y| ≤
          C * (Λ / ν) ^ deGiorgiPower d * ((3 : ℝ) ^ n * Gb + ((3 : ℝ) ^ n) ^ 2 / ν * F) := by
  obtain ⟨C, hC, HB⟩ := linf_dg_interior hd
  obtain ⟨Bη, hBη⟩ := (li1_bump_contDiff d).continuous.bounded_above_of_compact_support
    (li1_bump_compact d)
  obtain ⟨-, hη0, hη1, hηs⟩ := l2c_mollifier_witness d
  refine ⟨C * (1 + |Bη|), by positivity, ?_⟩
  intro ν Λ a W n hW hν hEll f v hv hfm F Gb hF hGb hfF hGbk ũ hũ
  have h0 : (0 : ℝ) < 3 ^ n := by positivity
  have hr : (0 : ℝ) < 4 * 3 ^ n := by positivity
  have hηB : ∀ w, |li1_bump d w| ≤ |Bη| := fun w =>
    ((Real.norm_eq_abs _).symm.le.trans (hBη w)).trans (le_abs_self _)
  have hall : ∀ k : Fin d → ℤ, ∀ᵐ y ∂(volume : Measure (Vec d)), y ∈ l2b_cell (l2b_pt n k) n →
      l2a_cutoff W (4 * (3 : ℝ) ^ n) y ≠ 0 →
      |v.toFun y - l2a_moll d ((3 : ℝ) ^ n) (li1_bump d) ũ y| ≤
        C * (1 + |Bη|) * (Λ / ν) ^ deGiorgiPower d *
          ((3 : ℝ) ^ n * Gb + ((3 : ℝ) ^ n) ^ 2 / ν * F) := by
    intro k
    by_cases hk : l2b_cell (l2b_pt n k) (n + 1) ⊆ W
    · have hQ : shiftCube (l2b_pt n k) ((n : ℤ) + 1) ⊆ W := by
        have := linf_det_shift_sub_cell (l2b_pt n k) (n + 1)
        push_cast at this
        exact this.trans hk
      have hQo := rc_isOpen_shiftCube (l2b_pt n k) ((n : ℤ) + 1)
      have H := HB n k hν (isEllipticFieldOn_mono hQo.measurableSet hQ hEll)
        (li1_bump_contDiff d).continuous hηB hη0 hη1 hηs f (v.restrict hQo hQ)
        (wh2_isWeakSolutionOn_restrict hQo hQ hv) hF hGb
        (hfm.mono_measure (Measure.restrict_mono hQ le_rfl))
        (ae_restrict_of_ae_restrict_of_subset hQ hfF) (hGbk k hk)
      rw [ae_restrict_iff' (l2b_cell_measurable _ _)] at H
      filter_upwards [H] with y hy hyc hζ
      have e : l2a_moll d ((3 : ℝ) ^ n) (li1_bump d)
          ((shiftCube (l2b_pt n k) ((n : ℤ) + 1)).indicator (v.restrict hQo hQ).toFun) y =
          l2a_moll d ((3 : ℝ) ^ n) (li1_bump d) ũ y := by
        unfold l2a_moll
        refine integral_congr_ae ?_
        filter_upwards [linf_dgi_ball_ae n (l2b_pt n k) hyc] with w hw
        by_cases hwb : w ∈ Metric.closedBall y ((3 : ℝ) ^ n)
        · have hwQ := hw hwb
          rw [Set.indicator_of_mem hwQ]
          have hyd := l2a_cutoff_ne_zero_imp hr hζ
          have hdw := linf_det_dist_cell_cube hyc hwQ
          have htri := Metric.infDist_le_infDist_add_dist (s := Wᶜ) (x := y) (y := w)
          rw [dist_comm] at hdw
          rw [hũ w (hQ hwQ) (by linarith only [hyd, hdw, htri])]
          rfl
        · rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hwb
          have : (3 : ℝ) ^ n < ‖y - w‖ := by rwa [← norm_neg, neg_sub]
          simp [l2a_kernel_eq_zero_of_norm h0 hηs this]
      have hy' := hy hyc
      rw [e] at hy'
      exact hy'
    · refine Filter.Eventually.of_forall fun y hyc hζ => absurd ?_ hk
      obtain ⟨⟨k', hk'⟩, hyk'⟩ := l2b_exists_cell n
        (l2b_cutoff_marg hr (by linarith only [h0]) y hζ)
      by_cases e : k' = k
      · rw [← e]; exact hk'
      · exact (Set.disjoint_left.1 (l2b_cell_disjoint n e) hyk' hyc).elim
  filter_upwards [ae_all_iff.2 hall] with y hy hζ
  refine (hy (l2b_idx n y) (l2b_mem_cell_idx n y) hζ).trans (le_of_eq ?_)
  ring

/-- **Boundary De Giorgi bound near the boundary**: almost every point of `W` at
distance less than `10 h` from `Wᶜ` satisfies `|v - g̃| ≤ C (Λ/ν)^{p+1} (Bb + h² F/ν + h G)`. -/
theorem linf_det_bdry [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ν Λ : ℝ} {a : CoeffField d} {W : Set (Vec d)} {n : ℕ}, IsOpen W →
      IsBoundedDomain W → 0 < ν → ν ≤ Λ → IsEllipticFieldOn ν Λ W a →
      ∀ (f : Vec d → ℝ) (v : H1Function W) {gt : Vec d → ℝ}, ContDiff ℝ 1 gt →
      IsWeakSolutionOn a W v f (fun _ => 0) → MemH10 W (fun x => v.toFun x - gt x) →
      AEStronglyMeasurable f (volume.restrict W) →
      ∀ {F G Bb : ℝ}, 0 ≤ F → 0 ≤ G → 0 ≤ Bb → (∀ᵐ x ∂volume.restrict W, |f x| ≤ F) →
      (∀ x, ‖fderiv ℝ gt x‖ ≤ G) →
      (∀ k : Fin d → ℤ,
          (∃ x ∈ l2b_cell (l2b_pt n k) n ∩ W, Metric.infDist x Wᶜ < 10 * (3 : ℝ) ^ n) →
          eLpNorm (fun x => v.toFun x - gt x) 2
              (volume.restrict (W ∩ shiftCube (l2b_pt n k) ((n : ℤ) + 2))) ≤
            ENNReal.ofReal (((3 : ℝ) ^ (n + 2)) ^ ((d : ℝ) / 2) * Bb)) →
      ∀ᵐ y ∂(volume : Measure (Vec d)), y ∈ W → Metric.infDist y Wᶜ < 10 * (3 : ℝ) ^ n →
        |v.toFun y - gt y| ≤ C * (Λ / ν) ^ (deGiorgiPower d + 1) *
          (Bb + ((3 : ℝ) ^ n) ^ 2 / ν * F + (3 : ℝ) ^ n * G) := by
  obtain ⟨C, hC, HB⟩ := linf_dg_boundary hd
  refine ⟨81 * C, by positivity, ?_⟩
  intro ν Λ a W n hW hWb hν hνΛ hEll f v gt hgt hv hmem hfm F G Bb hF hG hBb hfF hgtG hBbk
  have h0 : (0 : ℝ) < 3 ^ n := by positivity
  have hall : ∀ k : Fin d → ℤ, ∀ᵐ y ∂(volume : Measure (Vec d)), y ∈ l2b_cell (l2b_pt n k) n →
      y ∈ W → Metric.infDist y Wᶜ < 10 * (3 : ℝ) ^ n →
      |v.toFun y - gt y| ≤ C * (Λ / ν) ^ (deGiorgiPower d + 1) *
        (Bb + (9 * (3 : ℝ) ^ n) ^ 2 / ν * F + 9 * (3 : ℝ) ^ n * G) := by
    intro k
    by_cases hk : ∃ x ∈ l2b_cell (l2b_pt n k) n ∩ W, Metric.infDist x Wᶜ < 10 * (3 : ℝ) ^ n
    · have hL9 : (3 : ℝ) ^ (n + 2) = 9 * 3 ^ n := by rw [pow_add]; norm_num; ring
      have hcube : shiftCube (l2b_pt n k) ((n : ℤ) + 2) =
          axisCube (fun i => l2b_pt n k i - 9 * 3 ^ n / 2) (9 * 3 ^ n) := by
        rw [rc_shiftCube_eq_axisCube, linf_det_zpow_two]
      have hsub : W ∩ axisCube (fun i => l2b_pt n k i - 9 * 3 ^ n / 2) (9 * 3 ^ n) ⊆ W :=
        Set.inter_subset_left
      have hBk := hBbk k hk
      rw [hcube, hL9] at hBk
      have H := HB hW hWb hν hνΛ hEll f v hgt hv hmem
        (fun i => l2b_pt n k i - 9 * 3 ^ n / 2) (L := 9 * 3 ^ n) (F := F) (G := G) (Bb := Bb)
        (by positivity) hF hG hBb (hfm.mono_measure (Measure.restrict_mono hsub le_rfl))
        (ae_restrict_of_ae_restrict_of_subset hsub hfF) (fun x _ => hgtG x) hBk
      have hmeas : MeasurableSet
          (W ∩ halfCube (fun i => l2b_pt n k i - 9 * 3 ^ n / 2) (9 * 3 ^ n)) :=
        hW.measurableSet.inter (by
          unfold halfCube axisCube
          exact (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo).measurableSet)
      rw [ae_restrict_iff' hmeas] at H
      filter_upwards [H] with y hy hyc hyW _
      refine hy ⟨hyW, ?_⟩
      have a := l2b_mem_cell.1 hyc
      simp only [halfCube, axisCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo,
        Pi.add_apply]
      intro i
      have ai := a i
      constructor <;> linarith only [ai.1, ai.2, h0]
    · exact Filter.Eventually.of_forall fun y hyc hyW hyd => absurd ⟨y, ⟨hyc, hyW⟩, hyd⟩ hk
  filter_upwards [ae_all_iff.2 hall] with y hy hyW hyd
  refine (hy (l2b_idx n y) (l2b_mem_cell_idx n y) hyW hyd).trans ?_
  have hq : 0 ≤ C * (Λ / ν) ^ (deGiorgiPower d + 1) :=
    mul_nonneg hC.le (Real.rpow_nonneg (div_nonneg (hν.le.trans hνΛ) hν.le) _)
  have h1 : 0 ≤ ((3 : ℝ) ^ n) ^ 2 / ν * F := by positivity
  have h2 : 0 ≤ (3 : ℝ) ^ n * G := by positivity
  have e : (9 * (3 : ℝ) ^ n) ^ 2 / ν * F = 81 * (((3 : ℝ) ^ n) ^ 2 / ν * F) := by ring
  have hb : Bb + (9 * (3 : ℝ) ^ n) ^ 2 / ν * F + 9 * (3 : ℝ) ^ n * G ≤
      81 * (Bb + ((3 : ℝ) ^ n) ^ 2 / ν * F + (3 : ℝ) ^ n * G) := by
    rw [e]; linarith only [h1, h2, hBb]
  calc C * (Λ / ν) ^ (deGiorgiPower d + 1) * (Bb + (9 * (3 : ℝ) ^ n) ^ 2 / ν * F +
        9 * (3 : ℝ) ^ n * G)
      ≤ C * (Λ / ν) ^ (deGiorgiPower d + 1) *
        (81 * (Bb + ((3 : ℝ) ^ n) ^ 2 / ν * F + (3 : ℝ) ^ n * G)) :=
        mul_le_mul_of_nonneg_left hb hq
    _ = _ := by ring

end SuperdiffusionCLT.Section7
