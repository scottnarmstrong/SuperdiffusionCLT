/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2AssemblyD
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Sobolev

/-!
# The deterministic core of the `L²` Dirichlet comparison: the flux and scalar estimates

The deterministic part of the proof of `p.Dirichlet.L2.blackbox`.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The gradient of `u`, cleaned to vanish off `V`. -/
noncomputable def l2d_gradc (V : Set (Vec d)) (u : H1Function V) : Vec d → Vec d :=
  V.indicator u.grad

/-- The flux `a ∇u`, cleaned to vanish off `V`. -/
noncomputable def l2d_flux (a : CoeffField d) (V : Set (Vec d)) (u : H1Function V) :
    Vec d → Vec d :=
  V.indicator fun z => matVecMul (a z) (u.grad z)

theorem l2d_norm_le_eucNorm (v : Vec d) : ‖v‖ ≤ eucNorm v :=
  (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => by
    rw [Real.norm_eq_abs]; exact abs_le_eucNorm v i

/-- Normalized norms of a vector field are bounded by those of its Euclidean length. -/
theorem l2d_lpBar_le_eucNorm {V : Set (Vec d)} {G : Vec d → Vec d}
    (hG : AEStronglyMeasurable G (volume.restrict V)) (p : ℝ≥0∞) :
    lpBar V p G ≤ lpBar V p (fun x => eucNorm (G x)) := by
  unfold lpBar
  refine eLpNorm_mono (hG.smul_measure _) fun x => ?_
  have h0 : 0 ≤ eucNorm (G x) := Real.sqrt_nonneg _
  rw [Real.norm_of_nonneg h0]
  exact l2d_norm_le_eucNorm _

theorem l2d_lpBar_congr {V : Set (Vec d)} (hV : MeasurableSet V) {E : Type*} [NormedAddCommGroup E]
    {F G : Vec d → E} (h : ∀ x ∈ V, F x = G x) (p : ℝ≥0∞) : lpBar V p F = lpBar V p G := by
  unfold lpBar
  refine eLpNorm_congr_ae ?_
  exact ((ae_restrict_iff' hV).2 (Filter.Eventually.of_forall h)).filter_mono
    (Measure.ae_smul_measure_le _)

theorem l2d_lpBar_add_le {V : Set (Vec d)} {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (hp : 1 ≤ p) (F G : Vec d → E) :
    lpBar V p (fun x => F x + G x) ≤ lpBar V p F + lpBar V p G :=
  eLpNorm_add_le (f := F) (g := G) hp

theorem l2d_lpBar_const_smul {V : Set (Vec d)} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℝ) (F : Vec d → E) (p : ℝ≥0∞) :
    lpBar V p (fun x => c • F x) = ENNReal.ofReal |c| * lpBar V p F := by
  unfold lpBar
  have := eLpNorm_const_smul (μ := ((volume V)⁻¹) • volume.restrict V) c F p
  rw [Real.enorm_eq_ofReal_abs] at this
  exact this

/-- **Locality of the cut-off flux defect**: `ζ (η ∗ (F - s ∇ũ)) = ζ (η ∗ (F - s ∇u))` when `∇ũ = ∇u`
on the `h`-neighbourhood of `{ζ ≠ 0}`. -/
theorem l2d_claimA {V : Set (Vec d)} (hV : IsOpen V) (hVb : Bornology.IsBounded V) {r h : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hhr : h ≤ r / 4) {η : Vec d → ℝ}
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) (u : H1Function V) (F : Vec d → Vec d) (s : ℝ)
    (x : Vec d) :
    l2a_cutoff V r x • a16_mollify d h η
        (fun y => F y - s • (l2c_ext hV hVb hr u).grad y) x =
      l2a_cutoff V r x • a16_mollify d h η (fun y => F y - s • l2d_gradc V u y) x := by
  by_cases hx : l2a_cutoff V r x = 0
  · simp [hx]
  congr 1
  funext i
  refine l2a_moll_congr hh hηs fun y hy => ?_
  have h1 : r < Metric.infDist x Vᶜ := l2a_cutoff_ne_zero_imp hr hx
  have h2 := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := Vᶜ)
  have h3 : dist x y ≤ h := by rw [dist_comm]; exact hy
  have h4 : r / 2 < Metric.infDist y Vᶜ := by linarith only [h1, h2, h3, hhr, hr]
  have hyV : y ∈ V := by
    by_contra hyV
    have : Metric.infDist y Vᶜ = 0 := Metric.infDist_zero_of_mem (show y ∈ Vᶜ from hyV)
    linarith only [this, h4, hr]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, l2d_gradc, Set.indicator_of_mem hyV,
    l2c_ext_grad hV hVb hr u hyV h4]


/-- **The flux estimate** (`e.Dir.new.CZ`, the three flux terms): the
interior flux term, the datum term and the boundary term of the flux of the equation for
`w - uhom`. -/
theorem l2d_Fv_bound [NeZero d] (M₁ : ℝ) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ {r₀ : ℝ} {V : Set (Vec d)} {M₂ D : ℝ}
      (hU : IsUniformC11Domain V r₀ M₁ M₂ D) {n : ℕ} {r : ℝ} (hr : 0 < r),
      3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) → 2 * (3 : ℝ) ^ n < r →
      (3 : ℝ) ^ n ≤ r / 4 →
      ∀ {η : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) η → (∀ w, 0 ≤ η w) → ∫ w, η w = 1 →
      (∀ w, (∃ i, 1 < |w i|) → η w = 0) →
      ∀ (u g : H1Function V) (ψ : H10Function V), ψ.toH1Function = u - g →
      ∀ {p : ℝ}, 1 < p → p < 2 → volume V ≠ 0 → ∀ {ϑ : ℝ≥0∞},
      (volume (boundaryLayer V (3 * r)) / volume V) ^ (1 / p - 1 / 2) ≤ ϑ →
      ∀ {F : Vec d → Vec d}, (∀ i, LocallyIntegrable (fun x => F x i) volume) →
      ∀ {s : ℝ}, 0 < s → ∀ {f : Vec d → ℝ}, AEStronglyMeasurable f (volume.restrict V) →
      ∀ {α β : ℝ≥0∞},
      (∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ V →
        ∀ x ∈ l2b_cell (l2b_pt n k) n, ENNReal.ofReal
          ‖a16_mollify d ((3 : ℝ) ^ n) η (fun y => F y - s • l2d_gradc V u y) x‖ ≤
          α * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
              (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 +
            β * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
              (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖f x‖ₑ) p) →
      lpBar V (ENNReal.ofReal p)
          (l2d_Fv V r ((3 : ℝ) ^ n) η s (l2c_ext hU.1 (l2c_bounded hU) hr u) g F) ≤
        ENNReal.ofReal s⁻¹ * (α * lpBar V 2 (fun x => eucNorm (u.grad x)) +
            β * lpBar V (ENNReal.ofReal p) f) +
          ϑ * lpBar V 2 (fun x => eucNorm (g.grad x)) +
          ϑ * (ENNReal.ofReal CE * (lpBar V 2 (fun x => eucNorm (u.grad x)) +
            lpBar V 2 (fun x => eucNorm (g.grad x)))) := by
  obtain ⟨CE, hCE, H5⟩ := l2d_E5_unif (d := d) M₁
  refine ⟨CE, hCE, ?_⟩
  intro r₀ V M₂ D hU n r hr h3r hn hhr η hη hη0 hη1 hηs u g ψ hψ p hp1 hp2 hW0 ϑ hϑ F hFc s hs
    f hfm α β hG3
  have hVb := l2c_bounded hU
  have hVm : MeasurableSet V := hU.1.measurableSet
  have hVT : volume V ≠ ⊤ := hVb.measure_lt_top.ne
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  set h : ℝ := (3 : ℝ) ^ n with hhdef
  set ũ := l2c_ext hU.1 hVb hr u with hũ
  set ζ := l2a_cutoff V r with hζ
  have hζc : Continuous ζ := l2a_cutoff_continuous V hr
  have hζ0 := l2a_cutoff_nonneg V r
  have hζ1 := l2a_cutoff_le_one V r
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le
  -- the cut-off flux defect
  have hG3c : ∀ i, Continuous fun x =>
      a16_mollify d h η (fun y => F y - s • ũ.grad y) x i := by
    intro i
    have hl : LocallyIntegrable (fun y => F y i - s * ũ.grad y i) volume :=
      (hFc i).sub ((l2a_locInt_of_memL2_univ (ũ.gradMemL2 i)).smul s)
    exact (l2a_moll_contDiff h3 hη hηs hl).continuous
  have hG3cv : Continuous fun x => a16_mollify d h η (fun y => F y - s • ũ.grad y) x :=
    continuous_pi hG3c
  have hA := l2d_claimA hU.1 hVb hr h3 hhr hηs u F s
  -- the interior estimate
  have hvm : AEStronglyMeasurable (fun x => eucNorm (u.grad x)) (volume.restrict V) :=
    l2c_continuous_eucNorm.comp_aestronglyMeasurable (l2c_aesm_grad u)
  have hGm : AEStronglyMeasurable (fun x => ζ x •
      a16_mollify d h η (fun y => F y - s • l2d_gradc V u y) x) (volume.restrict V) := by
    have : (fun x => ζ x • a16_mollify d h η (fun y => F y - s • l2d_gradc V u y) x) =
        fun x => ζ x • a16_mollify d h η (fun y => F y - s • ũ.grad y) x :=
      funext fun x => (hA x).symm
    rw [this]
    exact (hζc.smul hG3cv).aestronglyMeasurable
  have e3 := l2b_E3_core n hVm hW0 hVT (fun x => l2a_cutoff_abs_le V r x) (l2b_cutoff_marg hr hn)
    hGm hvm hfm hp1.le hp2 hG3
  have hT1 : lpBar V (ENNReal.ofReal p) (fun x => ((-s⁻¹) * ζ x) •
      a16_mollify d h η (fun y => F y - s • ũ.grad y) x) ≤
      ENNReal.ofReal s⁻¹ * (α * lpBar V 2 (fun x => eucNorm (u.grad x)) +
            β * lpBar V (ENNReal.ofReal p) f) := by
    have e : (fun x => ((-s⁻¹) * ζ x) • a16_mollify d h η (fun y => F y - s • ũ.grad y) x) =
        fun x => (-s⁻¹) • (ζ x • a16_mollify d h η (fun y => F y - s • l2d_gradc V u y) x) := by
      funext x
      rw [mul_smul, hA x]
    rw [e, l2d_lpBar_const_smul, abs_neg, abs_of_pos (inv_pos.2 hs)]
    gcongr
    simpa only [ENNReal.ofReal_ofNat] using e3
  -- the datum term
  have hT2 := l2d_E4 hU hr hp1.le hp2.le hW0 (l2c_aesm_grad g)
  have hT2' : lpBar V (ENNReal.ofReal p) (fun x => (1 - ζ x) • g.grad x) ≤
      ϑ * lpBar V 2 (fun x => eucNorm (g.grad x)) :=
    hT2.trans (mul_le_mul' hϑ (l2d_lpBar_le_eucNorm (l2c_aesm_grad g) 2))
  -- the boundary term
  have hT3 := H5 hU hr h3r h3 hhr hη hη0 hη1 hηs u g ψ hψ hp1.le hp2.le hW0
  have hT3' : lpBar V (ENNReal.ofReal p) (fun x => (l2a_moll d h η ũ.toFun x - g.toFun x) •
      lipGradient ζ x) ≤ ϑ * (ENNReal.ofReal CE * (lpBar V 2 (fun x => eucNorm (u.grad x)) +
        lpBar V 2 (fun x => eucNorm (g.grad x)))) := by
    refine hT3.trans (mul_le_mul' hϑ (mul_le_mul' le_rfl (add_le_add ?_ ?_)))
    · exact l2d_lpBar_le_eucNorm (l2c_aesm_grad u) 2
    · exact l2d_lpBar_le_eucNorm (l2c_aesm_grad g) 2
  -- the triangle inequality
  have hsplit : l2d_Fv V r h η s ũ g F = fun x =>
      (((-s⁻¹) * ζ x) • a16_mollify d h η (fun y => F y - s • ũ.grad y) x +
        (1 - ζ x) • g.grad x) +
      (l2a_moll d h η ũ.toFun x - g.toFun x) • lipGradient ζ x := by
    funext x
    rfl
  rw [hsplit]
  refine (l2d_lpBar_add_le hP1 _ _).trans ?_
  refine (add_le_add (l2d_lpBar_add_le hP1 _ _) le_rfl).trans ?_
  calc _ ≤ (ENNReal.ofReal s⁻¹ * (α * lpBar V 2 (fun x => eucNorm (u.grad x)) +
            β * lpBar V (ENNReal.ofReal p) f) + ϑ * lpBar V 2 (fun x => eucNorm (g.grad x))) +
        ϑ * (ENNReal.ofReal CE * (lpBar V 2 (fun x => eucNorm (u.grad x)) +
          lpBar V 2 (fun x => eucNorm (g.grad x)))) := add_le_add (add_le_add hT1 hT2') hT3'
    _ = _ := by ring


/-- **The scalar estimate** (`e.Dir.new.f.mollification` and `e.Dir.new.boundary.flux.term`):
the `W^{-1,p}` norm of the scalar datum `h = h₁ + h₂`. -/
theorem l2d_h_bound [NeZero d] (M₁ : ℝ) :
    ∃ CP₁ CP₂ : ℝ, 0 ≤ CP₁ ∧ 0 ≤ CP₂ ∧ ∀ {r₀ : ℝ} {V : Set (Vec d)} {M₂ D : ℝ}
      (hU : IsUniformC11Domain V r₀ M₁ M₂ D) {n : ℕ} {r : ℝ} (hr : 0 < r),
      3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) → 2 * (3 : ℝ) ^ n < r →
      volume V ≠ 0 → ∀ {η : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) η → ∀ {Bη : ℝ},
      (∀ w, |η w| ≤ Bη) → (∀ w, 0 ≤ η w) → ∫ w, η w = 1 →
      (∀ w, (∃ i, 1 < |w i|) → η w = 0) → ∀ {p q : ℝ}, p.HolderConjugate q → p < 2 →
      ∀ {ϑ : ℝ≥0∞}, (volume (boundaryLayer V (3 * r)) / volume V) ^ (1 / p - 1 / 2) ≤ ϑ →
      ∀ {s : ℝ}, 0 < s → ∀ {fc f : Vec d → ℝ}, IntegrableOn fc V volume →
      (∀ φ : H10Function V, IntegrableOn (fun x => fc x * φ.toH1Function.toFun x) V volume) →
      AEStronglyMeasurable f (volume.restrict V) → ∀ (u : H1Function V) {F : Vec d → Vec d},
      (∀ i, LocallyIntegrable (fun x => F x i) volume) →
      (∀ ψ : H10Function V, IntegrableOn
        (fun x => l2d_h1 V r ((3 : ℝ) ^ n) η s fc x * ψ.toH1Function.toFun x) V) →
      (∀ ψ : H10Function V, IntegrableOn
        (fun x => l2d_h2 V r ((3 : ℝ) ^ n) η s F x * ψ.toH1Function.toFun x) V) →
      ∀ {α β : ℝ≥0∞},
      (∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ V →
        ∀ x ∈ l2b_cell (l2b_pt n k) n, ENNReal.ofReal
          ‖a16_mollify d ((3 : ℝ) ^ n) η F x‖ ≤
          α * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
              (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 +
            β * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
              (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖f x‖ₑ) p) →
      wMinusOneBar V (ENNReal.ofReal p)
          (fun x => l2d_h1 V r ((3 : ℝ) ^ n) η s fc x + l2d_h2 V r ((3 : ℝ) ^ n) η s F x) ≤
        ENNReal.ofReal s⁻¹ *
          (ENNReal.ofReal (d * (3 : ℝ) ^ n + CP₁ * r) * lpBar V (ENNReal.ofReal p) fc +
            ENNReal.ofReal (d * CP₂) * (α * ϑ * lpBar V 2 (fun x => eucNorm (u.grad x)) +
              β * lpBar V (ENNReal.ofReal p) f)) := by
  obtain ⟨CP₁, hCP₁, H1⟩ := l2d_E1_cutoff (d := d) M₁
  obtain ⟨CP₂, hCP₂, H2⟩ := l2d_E2_cutoff (d := d) M₁
  refine ⟨CP₁, CP₂, hCP₁, hCP₂, ?_⟩
  intro r₀ V M₂ D hU n r hr h3r hn hW0 η hη Bη hηA hη0 hη1 hηs p q hpq hp2 ϑ hϑ s hs fc f hfi hfψ
    hfm u F hFc hI1 hI2 α β hG2
  have hVb := l2c_bounded hU
  have hVT : volume V ≠ ⊤ := hVb.measure_lt_top.ne
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hp1 : 1 < p := hpq.lt
  have hsum := s12_wMinusOneBar_add_le V (ENNReal.ofReal p) hI1 hI2
  -- the mollification error
  have e1 : wMinusOneBar V (ENNReal.ofReal p) (fun x => l2d_h1 V r ((3 : ℝ) ^ n) η s fc x) ≤
      ENNReal.ofReal s⁻¹ * (ENNReal.ofReal (d * (3 : ℝ) ^ n + CP₁ * r) *
        lpBar V (ENNReal.ofReal p) fc) := by
    have := s12_wMinusOneBar_const_mul V (ENNReal.ofReal p) s⁻¹
      (fun x => l2a_cutoff V r x * l2a_moll d ((3 : ℝ) ^ n) η fc x - fc x)
    rw [abs_of_pos (inv_pos.2 hs)] at this
    show wMinusOneBar V (ENNReal.ofReal p) (fun x => s⁻¹ * _) ≤ _
    rw [this]
    exact mul_le_mul' le_rfl (H1 hU n hr h3r hn hW0 hVT hη.continuous hηA hη0 hη1 hηs hpq hfi hfψ)
  -- the layer term
  have hGc : Continuous fun x => a16_mollify d ((3 : ℝ) ^ n) η F x :=
    continuous_pi fun i => (l2a_moll_contDiff h3 hη hηs (hFc i)).continuous
  have hvm : AEStronglyMeasurable (fun x => eucNorm (u.grad x)) (volume.restrict V) :=
    l2c_continuous_eucNorm.comp_aestronglyMeasurable (l2c_aesm_grad u)
  have e2 : wMinusOneBar V (ENNReal.ofReal p) (fun x => l2d_h2 V r ((3 : ℝ) ^ n) η s F x) ≤
      ENNReal.ofReal s⁻¹ * (ENNReal.ofReal (d * CP₂) *
        (α * ϑ * lpBar V 2 (fun x => eucNorm (u.grad x)) +
          β * lpBar V (ENNReal.ofReal p) f)) := by
    have := s12_wMinusOneBar_const_mul V (ENNReal.ofReal p) (-s⁻¹)
      (fun x => vecDot (lipGradient (l2a_cutoff V r) x)
        (a16_mollify d ((3 : ℝ) ^ n) η F x))
    rw [abs_neg, abs_of_pos (inv_pos.2 hs)] at this
    show wMinusOneBar V (ENNReal.ofReal p) (fun x => (-s⁻¹) * _) ≤ _
    rw [this]
    refine mul_le_mul' le_rfl ((H2 hU n hr h3r hn hW0 hVT hGc.aestronglyMeasurable hvm hfm hp1 hp2
      hG2).trans (mul_le_mul' le_rfl (add_le_add ?_ le_rfl)))
    have hr' : (volume (boundaryLayer V (3 * r)) * (volume V)⁻¹) ^ (1 / p - 1 / 2) ≤ ϑ := by
      rw [← div_eq_mul_inv]; exact hϑ
    simp only [ENNReal.ofReal_ofNat]
    exact mul_le_mul' (mul_le_mul' le_rfl hr') le_rfl
  calc _ ≤ _ := hsum
    _ ≤ _ := add_le_add e1 e2
    _ = _ := by ring


/-- The elementary combination of the flux and scalar bounds into one expression. -/
theorem l2d_combine (sI α β α' β' ϑ X Y Fn : ℝ≥0∞) {CE CP₁ CP₂ h r dd : ℝ} (hCE : 0 ≤ CE)
    (hCP₁ : 0 ≤ CP₁) (hCP₂ : 0 ≤ CP₂) (hh : 0 ≤ h) (hr : 0 ≤ r) (hdd : 0 ≤ dd) :
    sI * (α * X + β * Fn) + ϑ * Y + ϑ * (ENNReal.ofReal CE * (X + Y)) +
        sI * (ENNReal.ofReal (dd * h + CP₁ * r) * Fn +
          ENNReal.ofReal (dd * CP₂) * (α' * ϑ * X + β' * Fn)) ≤
      ENNReal.ofReal (1 + CE + dd + CP₁ + dd * CP₂) *
        (sI * (α * X + β * Fn) + ϑ * Y + ϑ * (X + Y) +
          sI * (ENNReal.ofReal (h + r) * Fn + α' * ϑ * X + β' * Fn)) := by
  set K : ℝ := 1 + CE + dd + CP₁ + dd * CP₂ with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ dd * CP₂ := mul_nonneg hdd hCP₂
    linarith only [hK, hCE, hdd, hCP₁, this]
  have hK1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal K := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hK1
  have e1 : ENNReal.ofReal (dd * h + CP₁ * r) ≤ ENNReal.ofReal K * ENNReal.ofReal (h + r) := by
    rw [← ENNReal.ofReal_mul (by linarith only [hK1])]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : 0 ≤ dd * CP₂ := mul_nonneg hdd hCP₂
    nlinarith only [hK, hCE, hdd, hCP₁, h2, hh, hr, mul_nonneg hdd hh, mul_nonneg hCP₁ hr,
      mul_nonneg hCE hh, mul_nonneg hCE hr, mul_nonneg h2 hh, mul_nonneg h2 hr]
  have e2 : ENNReal.ofReal (dd * CP₂) ≤ ENNReal.ofReal K := by
    refine ENNReal.ofReal_le_ofReal ?_
    linarith only [hK, hCE, hdd, hCP₁, mul_nonneg hdd hCP₂]
  have e3 : ENNReal.ofReal CE ≤ ENNReal.ofReal K := by
    refine ENNReal.ofReal_le_ofReal ?_
    linarith only [hK, hCE, hdd, hCP₁, mul_nonneg hdd hCP₂]
  set a1 := sI * (α * X + β * Fn)
  set a2 := ϑ * Y
  set a3 := ϑ * (X + Y)
  set a4 := sI * (ENNReal.ofReal (h + r) * Fn + α' * ϑ * X + β' * Fn)
  have t1 : a1 ≤ ENNReal.ofReal K * a1 := le_mul_of_one_le_left zero_le hK1'
  have t2 : a2 ≤ ENNReal.ofReal K * a2 := le_mul_of_one_le_left zero_le hK1'
  have t3 : ϑ * (ENNReal.ofReal CE * (X + Y)) ≤ ENNReal.ofReal K * a3 := by
    calc ϑ * (ENNReal.ofReal CE * (X + Y)) ≤ ϑ * (ENNReal.ofReal K * (X + Y)) := by gcongr
      _ = _ := by simp only [a3]; ring
  have t4 : sI * (ENNReal.ofReal (dd * h + CP₁ * r) * Fn +
      ENNReal.ofReal (dd * CP₂) * (α' * ϑ * X + β' * Fn)) ≤ ENNReal.ofReal K * a4 := by
    have e1' : ENNReal.ofReal (dd * h + CP₁ * r) * Fn ≤
        ENNReal.ofReal K * (ENNReal.ofReal (h + r) * Fn) := by
      rw [← mul_assoc]; exact mul_le_mul' e1 le_rfl
    calc _ ≤ sI * (ENNReal.ofReal K * (ENNReal.ofReal (h + r) * Fn) +
          ENNReal.ofReal K * (α' * ϑ * X + β' * Fn)) :=
          mul_le_mul' le_rfl (add_le_add e1' (mul_le_mul' e2 le_rfl))
      _ = _ := by simp only [a4]; ring
  calc _ ≤ ENNReal.ofReal K * a1 + ENNReal.ofReal K * a2 + ENNReal.ofReal K * a3 +
        ENNReal.ofReal K * a4 := add_le_add (add_le_add (add_le_add t1 t2) t3) t4
    _ = _ := by ring


theorem l2d_matVecMul_smul_one (s : ℝ) (v : Vec d) : matVecMul (s • (1 : Mat d)) v = s • v := by
  funext i
  simp [matVecMul, Matrix.one_apply]

theorem l2d_vecDot_smul_left (s : ℝ) (X Y : Vec d) : vecDot (s • X) Y = s * vecDot X Y := by
  simp [vecDot, Finset.mul_sum, mul_assoc]

theorem l2d_indicator_apply (V : Set (Vec d)) (G : Vec d → Vec d) (x : Vec d) (i : Fin d) :
    V.indicator G x i = V.indicator (fun z => G z i) x := by
  by_cases hx : x ∈ V <;> simp [hx]

/-- **The deterministic core** of `p.Dirichlet.L2.blackbox`: the five-term
comparison of `u` with `uhom` on a uniformly `C^{1,1}` domain. -/
theorem l2d_core [NeZero d] (hd : 2 ≤ d) (M₁ κ ρ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r₀ : ℝ} {V : Set (Vec d)} {M₂ D : ℝ},
      IsUniformC11Domain V r₀ M₁ M₂ D → r₀ * M₂ ≤ κ → D ≤ ρ * r₀ →
      ∀ {n : ℕ} {r : ℝ}, 0 < r →
      3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) → 2 * (3 : ℝ) ^ n < r →
      (3 : ℝ) ^ n ≤ r / 4 → volume V ≠ 0 → ∀ {Λ : ℝ}, 0 ≤ Λ →
      volume V ^ (1 / (d : ℝ)) ≤ ENNReal.ofReal Λ →
      ∀ {η : Vec d → ℝ} {Bη : ℝ}, ContDiff ℝ (⊤ : ℕ∞) η → (∀ w, |η w| ≤ Bη) → (∀ w, 0 ≤ η w) →
      ∫ w, η w = 1 → (∀ w, (∃ i, 1 < |w i|) → η w = 0) →
      ∀ {ϑ : ℝ≥0∞}, (volume (boundaryLayer V (3 * r)) / volume V) ^
        (1 / Real.conjExponent (sobStar d) - 1 / 2) ≤ ϑ →
      ∀ (a : CoeffField d) {s : ℝ}, 0 < s → ∀ (u g ub : H1Function V) (f : Vec d → ℝ),
      MemLp f (ENNReal.ofReal (Real.conjExponent (sobStar d))) (volume.restrict V) →
      MemVectorL2 V (fun x => matVecMul (a x) (u.grad x)) →
      IsWeakSolutionOn a V u f (fun _ => 0) →
      IsWeakSolutionOn (fun _ => s • (1 : Mat d)) V ub f (fun _ => 0) →
      MemH10 V (fun x => u.toFun x - g.toFun x) → MemH10 V (fun x => ub.toFun x - g.toFun x) →
      ∀ {α β α' β' : ℝ≥0∞},
      (∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ V →
        ∀ x ∈ l2b_cell (l2b_pt n k) n, ENNReal.ofReal
          ‖a16_mollify d ((3 : ℝ) ^ n) η
            (fun y => l2d_flux a V u y - s • l2d_gradc V u y) x‖ ≤
          α * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
              (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 +
            β * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
              (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖f x‖ₑ)
              (Real.conjExponent (sobStar d))) →
      (∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ V →
        ∀ x ∈ l2b_cell (l2b_pt n k) n, ENNReal.ofReal
          ‖a16_mollify d ((3 : ℝ) ^ n) η (l2d_flux a V u) x‖ ≤
          α' * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
              (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 +
            β' * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
              (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖f x‖ₑ)
              (Real.conjExponent (sobStar d))) →
      lpBar V 2 (fun x => u.toFun x - ub.toFun x) ≤
        ENNReal.ofReal C *
          (ENNReal.ofReal ((3 : ℝ) ^ n + r) *
              (lpBar V 2 (fun x => eucNorm (u.grad x)) + lpBar V 2 (fun x => eucNorm (g.grad x))) +
            ENNReal.ofReal Λ *
              (ENNReal.ofReal s⁻¹ * (α * lpBar V 2 (fun x => eucNorm (u.grad x)) +
                  β * lpBar V (ENNReal.ofReal (Real.conjExponent (sobStar d))) f) +
                ϑ * lpBar V 2 (fun x => eucNorm (g.grad x)) +
                ϑ * (lpBar V 2 (fun x => eucNorm (u.grad x)) +
                  lpBar V 2 (fun x => eucNorm (g.grad x))) +
                ENNReal.ofReal s⁻¹ * (ENNReal.ofReal ((3 : ℝ) ^ n + r) *
                    lpBar V (ENNReal.ofReal (Real.conjExponent (sobStar d))) f +
                  α' * ϑ * lpBar V 2 (fun x => eucNorm (u.grad x)) +
                  β' * lpBar V (ENNReal.ofReal (Real.conjExponent (sobStar d))) f))) := by
  obtain ⟨hp1, hp2, hpd, q, hq2, hq⟩ := l2d_exponents hd
  set p : ℝ := Real.conjExponent (sobStar d) with hpdef
  have hs1 : 1 < sobStar d := by linarith only [two_lt_sobStar hd]
  have hHC : (sobStar d).HolderConjugate p := Real.HolderConjugate.conjExponent hs1
  obtain ⟨CS, hCS, HS⟩ := l2d_sobolev_norm hd hp1 hp2.le hpd hq hq2
  have hP1 : (1 : ℝ≥0∞) < ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hp1])).2 hp1
  have hP2 : ENNReal.ofReal p ≤ 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]; exact ENNReal.ofReal_le_ofReal hp2.le
  obtain ⟨CZ, hCZ, HZ⟩ := p14g_low hd hP1 hP2 M₁ κ ρ
  obtain ⟨Cw, hCw, HW⟩ := l2d_wu_unif (d := d) M₁
  obtain ⟨CE, hCE, HF⟩ := l2d_Fv_bound (d := d) M₁
  obtain ⟨CP₁, CP₂, hCP₁, hCP₂, HH⟩ := l2d_h_bound (d := d) M₁
  refine ⟨Cw + CS * CZ * (1 + CE + d + CP₁ + d * CP₂), by positivity, ?_⟩
  intro r₀ V M₂ D hU hκ hρ n r hr h3r hn hhr hW0 Λ hΛ hvol η Bη hη hηB hη0 hη1 hηs ϑ hϑ a s hs
    u g ub f hfP hflux hu hub hu10 hub10 α β α' β' hG3 hG2
  have hVb := l2c_bounded hU
  have hVm : MeasurableSet V := hU.1.measurableSet
  have hVT : volume V ≠ ⊤ := hVb.measure_lt_top.ne
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hs0 : s ≠ 0 := hs.ne'
  have hfin : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hVb.measure_lt_top⟩
  obtain ⟨ψu, hψu⟩ := l2d_h10_of_mem hU.1 u g hu10
  obtain ⟨ψb, hψb⟩ := l2d_h10_of_mem hU.1 ub g hub10
  have hP1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := hP1.le
  -- the cleaned data
  have hfint : Integrable f (volume.restrict V) := hfP.integrable hP1'
  have hfcI : Integrable (V.indicator f) volume := (integrable_indicator_iff hVm).2 hfint
  have hFi : ∀ i, LocallyIntegrable (fun x => l2d_flux a V u x i) volume := by
    intro i
    have h1 : Integrable (fun z => matVecMul (a z) (u.grad z) i) (volume.restrict V) :=
      ((MeasureTheory.memLp_pi_iff.1 hflux i).integrable (by norm_num))
    have h2 := (integrable_indicator_iff hVm).2 h1
    have e : (fun x => l2d_flux a V u x i) =
        V.indicator (fun z => matVecMul (a z) (u.grad z) i) :=
      funext fun x => l2d_indicator_apply V _ x i
    rw [e]
    exact h2.locallyIntegrable
  have hweak : ∀ φ : H10Function V, ∫ x in V, vecDot (l2d_flux a V u x) (φ.toH1Function.grad x) =
      ∫ x in V, V.indicator f x * φ.toH1Function.toFun x := by
    intro φ
    have h0 := hu φ
    have hz : ∫ x in V, vecDot ((fun _ : Vec d => (0 : Vec d)) x) (φ.toH1Function.grad x) = 0 := by
      simp [vecDot]
    rw [hz, add_zero] at h0
    calc ∫ x in V, vecDot (l2d_flux a V u x) (φ.toH1Function.grad x)
        = ∫ x in V, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) :=
          setIntegral_congr_fun hVm fun x hx => by simp [l2d_flux, Set.indicator_of_mem hx]
      _ = ∫ x in V, f x * φ.toH1Function.toFun x := h0
      _ = _ := setIntegral_congr_fun hVm fun x hx => by simp [Set.indicator_of_mem hx]
  have hhom : ∀ φ : H10Function V, s * ∫ x in V, vecDot (ub.grad x) (φ.toH1Function.grad x) =
      ∫ x in V, V.indicator f x * φ.toH1Function.toFun x := by
    intro φ
    have h0 := hub φ
    have hz : ∫ x in V, vecDot ((fun _ : Vec d => (0 : Vec d)) x) (φ.toH1Function.grad x) = 0 := by
      simp [vecDot]
    rw [hz, add_zero] at h0
    simp only [l2d_matVecMul_smul_one, l2d_vecDot_smul_left] at h0
    rw [integral_const_mul] at h0
    rw [h0]
    exact setIntegral_congr_fun hVm fun x hx => by simp [Set.indicator_of_mem hx]
  have hfcP : MemLp (V.indicator f) (ENNReal.ofReal p) (volume.restrict V) := by
    refine hfP.ae_eq ?_
    exact (ae_restrict_iff' hVm).2 (Filter.Eventually.of_forall fun x hx => by
      simp [Set.indicator_of_mem hx])
  have hfφ : ∀ φ : H10Function V,
      IntegrableOn (fun x => V.indicator f x * φ.toH1Function.toFun x) V :=
    fun φ => l2d_integrableOn_mul_H10 hd hVb hfcP φ
  have hh : 0 < (3 : ℝ) ^ n := h3
  obtain ⟨v, hvH, hsol, hFvL2, hI1, hI2⟩ := l2d_equation hU.1 hVb hr hh hhr hη hηs
    (l2c_ext hU.1 hVb hr u) g ub ⟨ψb, hψb⟩ (F := l2d_flux a V u) (f := V.indicator f) hFi
    hfcI.locallyIntegrable hweak hs0 hhom hfφ
  set ũ := l2c_ext hU.1 hVb hr u with hũ
  set X := lpBar V 2 (fun x => eucNorm (u.grad x)) with hX
  set Y := lpBar V 2 (fun x => eucNorm (g.grad x)) with hY
  set Fn := lpBar V (ENNReal.ofReal p) f with hFn
  have hfm : AEStronglyMeasurable f (volume.restrict V) := hfP.aestronglyMeasurable
  -- the flux
  have hFB := HF hU hr h3r hn hhr hη hη0 hη1 hηs u g ψu hψu hp1 hp2 hW0 hϑ hFi hs hfm hG3
  -- the scalar datum
  have hHB := HH hU hr h3r hn hW0 hη hηB hη0 hη1 hηs hHC.symm hp2 hϑ hs hfcI.integrableOn hfφ
    hfm u hFi hI1 hI2 hG2
  have hfcn : lpBar V (ENNReal.ofReal p) (V.indicator f) = Fn :=
    l2d_lpBar_congr hVm (fun x hx => by simp [Set.indicator_of_mem hx]) _
  rw [hfcn] at hHB
  -- Calderón-Zygmund
  have hCZ' := HZ hU hκ hρ (l2d_Fv V r ((3 : ℝ) ^ n) η s ũ g (l2d_flux a V u)) _ v hFvL2 hsol
  have hSob := HS hVm hVb hW0 v
  have hvfun : v.toH1Function.toFun = fun x =>
      (l2d_w hU.1 hVb hr hh hη hηs ũ g).toFun x - ub.toFun x := by
    rw [hvH, H1Function.sub_toFun]
  rw [hvfun] at hSob
  have hvol : volume V ^ (1 / (d : ℝ)) ≤ ENNReal.ofReal Λ := hvol
  have hvG : lpBar V 2 (fun x => (l2d_w hU.1 hVb hr hh hη hηs ũ g).toFun x - ub.toFun x) ≤
      ENNReal.ofReal CS * (ENNReal.ofReal Λ * (ENNReal.ofReal CZ *
        ((ENNReal.ofReal s⁻¹ * (α * X + β * Fn) + ϑ * Y +
            ϑ * (ENNReal.ofReal CE * (X + Y))) +
          ENNReal.ofReal s⁻¹ * (ENNReal.ofReal (d * (3 : ℝ) ^ n + CP₁ * r) * Fn +
            ENNReal.ofReal (d * CP₂) * (α' * ϑ * X + β' * Fn))))) := by
    refine hSob.trans (mul_le_mul' le_rfl (mul_le_mul' hvol (hCZ'.trans (mul_le_mul' le_rfl ?_))))
    exact add_le_add hFB hHB
  -- `w - u`
  have huw := HW hU hr h3r hh hhr hη hη0 hη1 hηs u g ψu hψu
  have huw' : lpBar V 2 (fun x => (l2d_w hU.1 hVb hr hh hη hηs ũ g).toFun x - u.toFun x) ≤
      ENNReal.ofReal (Cw * ((3 : ℝ) ^ n + r)) * (X + Y) := by
    refine huw.trans (mul_le_mul' le_rfl (add_le_add ?_ ?_))
    · exact l2d_lpBar_le_eucNorm (l2c_aesm_grad u) 2
    · exact l2d_lpBar_le_eucNorm (l2c_aesm_grad g) 2
  have hsymm : lpBar V 2 (fun x => u.toFun x - (l2d_w hU.1 hVb hr hh hη hηs ũ g).toFun x) =
      lpBar V 2 (fun x => (l2d_w hU.1 hVb hr hh hη hηs ũ g).toFun x - u.toFun x) := by
    unfold lpBar
    exact eLpNorm_sub_comm (E := ℝ) u.toFun (l2d_w hU.1 hVb hr hh hη hηs ũ g).toFun 2 _
  have htri : lpBar V 2 (fun x => u.toFun x - ub.toFun x) ≤
      lpBar V 2 (fun x => u.toFun x - (l2d_w hU.1 hVb hr hh hη hηs ũ g).toFun x) +
        lpBar V 2 (fun x => (l2d_w hU.1 hVb hr hh hη hηs ũ g).toFun x - ub.toFun x) := by
    have e : (fun x => u.toFun x - ub.toFun x) = fun x =>
        (u.toFun x - (l2d_w hU.1 hVb hr hh hη hηs ũ g).toFun x) +
          ((l2d_w hU.1 hVb hr hh hη hηs ũ g).toFun x - ub.toFun x) := by
      funext x; ring
    rw [e]
    exact l2d_lpBar_add_le (by norm_num) _ _
  -- the algebra
  have hcomb := l2d_combine (ENNReal.ofReal s⁻¹) α β α' β' ϑ X Y Fn hCE hCP₁ hCP₂ h3.le hr.le
    (Nat.cast_nonneg d)
  set K : ℝ := 1 + CE + d + CP₁ + d * CP₂ with hK
  have hK0 : 0 ≤ K := by positivity
  set Qu := ENNReal.ofReal s⁻¹ * (α * X + β * Fn) + ϑ * Y + ϑ * (X + Y) +
    ENNReal.ofReal s⁻¹ * (ENNReal.ofReal ((3 : ℝ) ^ n + r) * Fn + α' * ϑ * X + β' * Fn) with hQu
  have hT2 : ENNReal.ofReal CS * (ENNReal.ofReal Λ * (ENNReal.ofReal CZ *
        ((ENNReal.ofReal s⁻¹ * (α * X + β * Fn) + ϑ * Y +
            ϑ * (ENNReal.ofReal CE * (X + Y))) +
          ENNReal.ofReal s⁻¹ * (ENNReal.ofReal (d * (3 : ℝ) ^ n + CP₁ * r) * Fn +
            ENNReal.ofReal (d * CP₂) * (α' * ϑ * X + β' * Fn))))) ≤
      ENNReal.ofReal (CS * CZ * K) * (ENNReal.ofReal Λ * Qu) := by
    calc _ ≤ ENNReal.ofReal CS * (ENNReal.ofReal Λ * (ENNReal.ofReal CZ *
          (ENNReal.ofReal K * Qu))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hcomb))
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCS]
        ring
  have hCw' : ENNReal.ofReal (Cw * ((3 : ℝ) ^ n + r)) = ENNReal.ofReal Cw *
      ENNReal.ofReal ((3 : ℝ) ^ n + r) := ENNReal.ofReal_mul hCw
  have hCsum : ENNReal.ofReal (Cw + CS * CZ * K) =
      ENNReal.ofReal Cw + ENNReal.ofReal (CS * CZ * K) :=
    ENNReal.ofReal_add hCw (by positivity)
  set P := ENNReal.ofReal ((3 : ℝ) ^ n + r) * (X + Y) with hP
  set Q := ENNReal.ofReal Λ * Qu with hQ
  calc lpBar V 2 (fun x => u.toFun x - ub.toFun x)
      ≤ ENNReal.ofReal Cw * P + ENNReal.ofReal (CS * CZ * K) * Q := by
        refine htri.trans (add_le_add ?_ ?_)
        · rw [hsymm]
          refine huw'.trans (le_of_eq ?_)
          rw [hCw', hP]; ring
        · exact hvG.trans hT2
    _ ≤ (ENNReal.ofReal Cw * P + ENNReal.ofReal Cw * Q) +
          (ENNReal.ofReal (CS * CZ * K) * P + ENNReal.ofReal (CS * CZ * K) * Q) :=
        add_le_add le_self_add le_add_self
    _ = _ := by rw [hCsum]; ring


theorem l2d_matVecMul_zero (A : Mat d) : matVecMul A (0 : Vec d) = 0 := by
  funext i; simp [matVecMul]

theorem l2d_mollify_zero (h : ℝ) (η : Vec d → ℝ) (x : Vec d) :
    a16_mollify d h η (fun _ => (0 : Vec d)) x = 0 := by
  funext i; simp [a16_mollify]

/-- A domain with margin `r = 4`, scale `n = 0`: a dilate of the unit Euclidean ball. -/
theorem l2d_witness_domain4 [NeZero d] :
    ∃ (W : Set (Vec d)) (r₀ M₁ M₂ D : ℝ), IsUniformC11Domain W r₀ M₁ M₂ D ∧
      3 * (4 : ℝ) ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) ∧ volume W ≠ 0 := by
  obtain ⟨r₁, M₁, M₂, D, hU⟩ := isUniformC11Domain_euclidBall (d := d)
  have hr1 : 0 < r₁ := hU.2.1
  set κ : ℝ := (d : ℝ) + (1 + d) * max M₁ 0 with hκ
  have hκ0 : 0 ≤ κ := by
    have : 0 ≤ max M₁ 0 := le_max_right _ _
    positivity
  set R : ℝ := 12 * (3 * κ + 4) / r₁ + 1 with hR
  have hR0 : 0 < R := by positivity
  have hRU := hU.smul hR0
  have hne : (R • Section6.euclidBall (d := d) 1).Nonempty :=
    ⟨R • (0 : Vec d), Set.smul_mem_smul_set (by simp [Section6.euclidBall, vecNormSq, vecDot])⟩
  refine ⟨_, _, _, _, _, hRU, ?_, (hRU.1.measure_pos volume hne).ne'⟩
  rw [le_div_iff₀ (by positivity)]
  have : 12 * (3 * κ + 4) ≤ R * r₁ := by
    rw [hR, add_mul, div_mul_cancel₀ _ hr1.ne']; linarith only [hr1]
  linarith only [this, hκ]

/-- **Satisfiability of `l2d_core`**: zero data and the identity field on a dilate of the unit
ball, with the standard bump, so that `u = uhom` and the left side is `0`. -/
example : True := by
  obtain ⟨V, r₀, M₁, M₂, D, hU, h3r, hW0⟩ := l2d_witness_domain4 (d := 2)
  have hr0 : 0 < r₀ := hU.2.1
  obtain ⟨C, hC, H⟩ := l2d_core (d := 2) le_rfl M₁ (r₀ * M₂) (D / r₀)
  have hVb := l2c_bounded hU
  have hVT : volume V ≠ ⊤ := hVb.measure_lt_top.ne
  have hfin : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hVb.measure_lt_top⟩
  obtain ⟨B, hB⟩ := (li1_bump_contDiff 2).continuous.bounded_above_of_compact_support
    (li1_bump_compact 2)
  obtain ⟨hη, hη0, hη1, hηs⟩ := l2c_mollifier_witness 2
  have hvolf : volume V ^ (1 / ((2 : ℕ) : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hVT
  have _ := H hU le_rfl (div_mul_cancel₀ D hr0.ne').ge (n := 0) (r := 4) (by norm_num) h3r
    (by norm_num) (by norm_num) hW0 (Λ := (volume V ^ (1 / ((2 : ℕ) : ℝ))).toReal)
    ENNReal.toReal_nonneg (ENNReal.ofReal_toReal hvolf).ge (η := li1_bump 2) (Bη := B) hη
    (fun w => by simpa [Real.norm_eq_abs] using hB w) hη0 hη1 hηs (ϑ := ⊤) le_top
    (fun _ => (1 : Mat 2)) (s := 1) one_pos (0 : H1Function V) (0 : H1Function V)
    (0 : H1Function V) (fun _ => 0) (memLp_const 0) ((MeasureTheory.memLp_pi_iff).2 fun i => by simp [matVecMul])
    (fun φ => by simp [vecDot, matVecMul]) (fun φ => by simp [vecDot, matVecMul])
    ⟨0, by funext x; simp only [sub_self]; rfl⟩ ⟨0, by funext x; simp only [sub_self]; rfl⟩ (α := 0) (β := 0) (α' := 0) (β' := 0)
    (fun k _ x _ => by
      simp [l2d_flux, l2d_gradc, l2d_matVecMul_zero, Set.indicator_zero', l2d_mollify_zero])
    (fun k _ x _ => by
      simp [l2d_flux, l2d_matVecMul_zero, l2d_mollify_zero])
  trivial

end SuperdiffusionCLT.Section7
