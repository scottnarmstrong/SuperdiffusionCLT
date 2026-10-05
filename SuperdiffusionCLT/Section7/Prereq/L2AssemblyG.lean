/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2AssemblyF
public import SuperdiffusionCLT.Section7.Prereq.WhitneyLocalD
public import SuperdiffusionCLT.Section7.Prereq.FieldBridge
public import SuperdiffusionCLT.Section7.MinimalScale.Translate

/-!
# The `L²` Dirichlet homogenization proposition `l2_prop`

Proof of `p.Dirichlet.L2.blackbox`.  The
deterministic assembly `l2e_det` combines the five-term comparison `l2d_core` with the parameter
bounds `l2e_block_ineq`, given the almost-sure cell bounds of the mollified flux for the centred
field; `l2_prop` supplies them from the sharp inputs on a probability one event for every centre
`y`, and the window of `σ̄` from `lip_sigma_window`.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The constants of the cell bounds: `C σ^{1/2} δ ν^{1/2}`. -/
noncomputable def l2e_aC (Cin σ ν δ : ℝ) : ℝ := Cin * Real.sqrt σ * δ * Real.sqrt ν

/-- The constant `C σ^{-1/2} ν^{1/2}` of the gradient bound. -/
noncomputable def l2e_e (Cin σ ν : ℝ) : ℝ := Cin * (Real.sqrt σ)⁻¹ * Real.sqrt ν

/-- The coefficient of the right-hand side in the flux bound. -/
noncomputable def l2e_b (Cin σ ν ρ δ k : ℝ) (n : ℕ) : ℝ :=
  (l2e_aC Cin σ ν δ + Cin * (|ν - σ| + k ^ (1 + ρ))) * (Cin * (3 * (3 : ℝ) ^ n) / ν)

/-- The coefficient of the right-hand side in the gradient bound. -/
noncomputable def l2e_g (Cin σ ν : ℝ) (n : ℕ) : ℝ :=
  (l2e_e Cin σ ν + Cin) * (Cin * (3 * (3 : ℝ) ^ n) / ν)

theorem l2e_matVecMul_sub_smul_one (A : Mat d) (σ : ℝ) (v : Vec d) :
    matVecMul (A - σ • (1 : Mat d)) v = matVecMul A v - σ • v := by
  funext i
  simp only [matVecMul, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  congr 1
  simp [Matrix.one_apply]

/-- **The deterministic assembly of the `L²` block**: given the almost-sure cell bounds for the
field `a` on the good cells of `V`, the block `LipL2Block` holds for the field `ã` with the same
solutions. -/
theorem l2e_det [NeZero d] (hd : 2 ≤ d) (r' M₁' M₂' D' Cin : ℝ) (hCin : 1 ≤ Cin) (A : ℕ) :
    ∃ Cf : ℝ, 1 ≤ Cf ∧ ∀ {ν ε ρ σ : ℝ} {k n : ℕ} {V : Set (Vec d)} (a ã : CoeffField d),
      0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → ν ≤ σ → σ ≤ (k : ℝ) → 3 ≤ (k : ℝ) →
      1 ≤ (k : ℝ) * ε * ν ^ 2 → n + 1 ≤ k →
      3 * (4 * (3 : ℝ) ^ n) ≤
        ((3 : ℝ) ^ k * r') / (3 * ((d : ℝ) + (1 + d) * max M₁' 0) + 4) →
      ((3 : ℝ) ^ n / (3 : ℝ) ^ k) ^ (1 / Real.conjExponent (sobStar d) - 1 / 2) *
        (k : ℝ) ^ (A + 3) ≤ 1 →
      V ⊆ Section6.engCube d k → IsUniformC11Domain (((3 : ℝ) ^ k)⁻¹ • V) r' M₁' M₂' D' →
      (∀ u : H1Function V, MemVectorL2 V (fun x => matVecMul (a x) (u.grad x))) →
      (∀ (u : H1Function V) (f : Vec d → ℝ),
        IsWeakSolutionOn ã V u f (fun _ => 0) → IsWeakSolutionOn a V u f (fun _ => 0)) →
      (∀ (u : H1Function V) (f : Vec d → ℝ), AEMeasurable f (volume.restrict V) →
        IsWeakSolutionOn a V u f (fun _ => 0) →
        ∀ kk : Fin d → ℤ, l2b_cell (l2b_pt n kk) (n + 1) ⊆ V →
        ∀ x ∈ l2b_cell (l2b_pt n kk) n,
          ENNReal.ofReal ‖a16_mollify d ((3 : ℝ) ^ n) (li1_bump d)
              (fun y => matVecMul (a y - σ • (1 : Mat d)) (u.grad y)) x‖ ≤
            (ENNReal.ofReal (l2e_Kp d) * ENNReal.ofReal (l2e_aC Cin σ ν (deltaScale ε ρ k))) *
                l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                  (l2b_cell (l2b_pt n kk) (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 +
              (ENNReal.ofReal (l2e_Kp d) *
                  ENNReal.ofReal (l2e_b Cin σ ν ρ (deltaScale ε ρ k) k n)) *
                l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                  (l2b_cell (l2b_pt n kk) (n + 1)) (fun x => ‖f x‖ₑ)
                  (Real.conjExponent (sobStar d)) ∧
          ENNReal.ofReal ‖a16_mollify d ((3 : ℝ) ^ n) (li1_bump d)
              (fun y => matVecMul (a y) (u.grad y)) x‖ ≤
            (ENNReal.ofReal (l2e_Kp d) * ENNReal.ofReal (l2e_aC Cin σ ν (deltaScale ε ρ k)) +
                ENNReal.ofReal (σ * l2e_Kp d) * ENNReal.ofReal (l2e_e Cin σ ν)) *
                l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                  (l2b_cell (l2b_pt n kk) (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 +
              (ENNReal.ofReal (l2e_Kp d) *
                    ENNReal.ofReal (l2e_b Cin σ ν ρ (deltaScale ε ρ k) k n) +
                  ENNReal.ofReal (σ * l2e_Kp d) * ENNReal.ofReal (l2e_g Cin σ ν n)) *
                l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                  (l2b_cell (l2b_pt n kk) (n + 1)) (fun x => ‖f x‖ₑ)
                  (Real.conjExponent (sobStar d))) →
      LipL2Block ã ν σ (deltaScale ε ρ k) Cf A k V := by
  obtain ⟨hp1, hp2, hpd, -⟩ := l2d_exponents hd
  set p : ℝ := Real.conjExponent (sobStar d) with hpdef
  set θ : ℝ := 1 / p - 1 / 2 with hθdef
  have hp0 : 0 < p := by linarith only [hp1]
  have hθ0 : 0 < θ := by
    have : 1 / 2 < 1 / p := by
      rw [div_lt_div_iff₀ (by norm_num) hp0]; linarith only [hp2]
    linarith only [this, hθdef]
  have hθ1 : θ ≤ 1 := by
    have : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp1
    have : (0:ℝ) < 1 / 2 := by norm_num
    linarith only [this, hθdef, ‹1 / p < 1›]
  obtain ⟨C0, hC0, Hcore⟩ := l2d_core hd M₁' (r' * M₂') (D' / r')
  obtain ⟨cvol, hcvol, Hgeom⟩ := l2e_geom (d := d) r' M₁' D'
  have hKp0 : 0 ≤ l2e_Kp d := by
    have hB : 0 ≤ l2e_bumpB d := (abs_nonneg _).trans (l2e_bump_bound d 0)
    unfold l2e_Kp
    positivity
  set cv : ℝ := cvol ^ θ with hcv
  set Cs : ℝ := C0 * (10 + 3 * cv + l2e_Kp d * Cin * (1 + 2 * cv) + 24 * l2e_Kp d * Cin ^ 2)
    with hCs
  refine ⟨max 1 Cs, le_max_left _ _, ?_⟩
  intro ν ε ρ σ k n V a ã hν0 hν1 hε0 hε1 hρ0 hρ1 hσν hσk hk3 hthr hnk hgeo hsep hVsub hVuni hfl
    hequiv hcell f g u ub hu hub hu10 hub10
  -- the degenerate case
  by_cases hV0 : volume V = 0
  · have : lpBar V 2 (fun x => u.toFun x - ub.toFun x) = 0 := by
      unfold lpBar
      rw [Measure.restrict_eq_zero.2 hV0, smul_zero, eLpNorm_measure_zero]
    rw [this, mul_zero]
    exact bot_le
  have hne : V.Nonempty := nonempty_of_measure_ne_zero hV0
  have hr'0 : 0 < r' := hVuni.2.1
  have h12 : 12 * (3 : ℝ) ^ n ≤ (3 : ℝ) ^ k * r' := by
    have hκ4 : (4 : ℝ) ≤ 3 * ((d : ℝ) + (1 + d) * max M₁' 0) + 4 := by
      have : 0 ≤ max M₁' 0 := le_max_right _ _
      have : (0 : ℝ) ≤ 3 * ((d : ℝ) + (1 + d) * max M₁' 0) := by positivity
      linarith only [this]
    have h1 : ((3 : ℝ) ^ k * r') / (3 * ((d : ℝ) + (1 + d) * max M₁' 0) + 4) ≤
        (3 : ℝ) ^ k * r' / 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hκ4
    have h2 : 12 * (3 : ℝ) ^ n ≤ (3 : ℝ) ^ k * r' / 4 := by linarith only [hgeo, h1]
    have h3 : 0 ≤ (3 : ℝ) ^ k * r' := by positivity
    linarith only [h2, h3]
  obtain ⟨hUV, hVne, hvolΛ, hratio⟩ := Hgeom hVsub hVuni hne h12
  have hVo : IsOpen V := hUV.1
  have hVb := l2c_bounded hUV
  have hVm : MeasurableSet V := hVo.measurableSet
  have hVT : volume V ≠ ⊤ := hVb.measure_lt_top.ne
  have hconj : (ENNReal.ofReal (sobStar d)).conjExponent = ENNReal.ofReal p := by
    have hs : 1 < sobStar d := by linarith only [two_lt_sobStar hd]
    exact l2b_conj_exponent (Real.HolderConjugate.conjExponent hs)
  rw [hconj]
  set Fn := lpBar V (ENNReal.ofReal p) f with hFn
  set X := lpBar V 2 (fun x => eucNorm (u.grad x)) with hX
  set Y := lpBar V 2 (fun x => eucNorm (g.grad x)) with hY
  have hkpos : (0 : ℝ) < k := by linarith only [hk3]
  have hCf0 : 0 < max 1 Cs := lt_of_lt_of_le one_pos (le_max_left _ _)
  by_cases hFt : Fn = ⊤
  · have hQ : 0 < max 1 Cs * ((k : ℝ) ^ A)⁻¹ := by positivity
    have : ENNReal.ofReal (max 1 Cs * ((k : ℝ) ^ A)⁻¹) *
        (Y + ENNReal.ofReal ((3 : ℝ) ^ k) * Fn) = ⊤ := by
      rw [hFt, ENNReal.mul_top (by simp), add_top]
      exact ENNReal.mul_top (by simpa only [le_max_iff, zero_le_one, true_or, ENNReal.ofReal_mul, ENNReal.ofReal_max, ENNReal.ofReal_one, ne_eq, mul_eq_zero, max_eq_zero, one_ne_zero, ENNReal.ofReal_eq_zero, false_and, inv_nonpos, false_or, not_le, lt_max_iff, zero_lt_one, mul_pos_iff_of_pos_left, inv_pos] using hQ)
    rw [this]
    simp
  -- `f ∈ L^p(V)`
  have hfs : AEStronglyMeasurable f (volume.restrict V) := by
    by_contra hna
    have h1 : ¬ AEStronglyMeasurable f (((volume V)⁻¹) • volume.restrict V) := by
      intro h
      apply hna
      have e : volume.restrict V = (volume V) • (((volume V)⁻¹) • volume.restrict V) := by
        rw [smul_smul, ENNReal.mul_inv_cancel hV0 hVT, one_smul]
      rw [e]
      exact h.smul_measure _
    exact hFt (eLpNorm_of_not_aestronglyMeasurable h1)
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le
  have hfP : MemLp f (ENNReal.ofReal p) (volume.restrict V) := by
    show eLpNorm f (ENNReal.ofReal p) (volume.restrict V) < ⊤
    have h := l2c_lpBar_eq (V := V) (p := p) hp1.le hfs
    rw [← hFn] at h
    by_contra hlt
    have htop : eLpNorm f (ENNReal.ofReal p) (volume.restrict V) = ⊤ := not_lt_top_iff.1 hlt
    rw [htop] at h
    apply hFt
    rw [h]
    exact ENNReal.mul_top
      (ENNReal.rpow_pos (ENNReal.inv_pos.2 hVT) (ENNReal.inv_ne_top.2 hV0)).ne'
  -- the application of the core
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  set R : ℝ := (3 : ℝ) ^ n / (3 : ℝ) ^ k with hR
  have hR0 : 0 < R := by positivity
  have hR1 : R ≤ 1 := by
    rw [hR, div_le_one h3k]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  set t : ℝ := (cvol * R) ^ θ with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by positivity) _
  have hϑ : (volume (boundaryLayer V (3 * (4 * (3 : ℝ) ^ n))) / volume V) ^ θ ≤
      ENNReal.ofReal t :=
    (ENNReal.rpow_le_rpow hratio hθ0.le).trans
      (le_of_eq (ENNReal.ofReal_rpow_of_nonneg (by positivity) hθ0.le))
  have hηs : ∀ w : Vec d, (∃ i, 1 < |w i|) → li1_bump d w = 0 := (l2c_mollifier_witness d).2.2.2
  have hfaem : AEMeasurable f (volume.restrict V) := hfs.aemeasurable
  have hu' := hequiv u f hu
  have hclean3 : ∀ kk : Fin d → ℤ, l2b_cell (l2b_pt n kk) (n + 1) ⊆ V →
      ∀ x ∈ l2b_cell (l2b_pt n kk) n,
        a16_mollify d ((3 : ℝ) ^ n) (li1_bump d)
          (fun y => l2d_flux a V u y - σ • l2d_gradc V u y) x =
        a16_mollify d ((3 : ℝ) ^ n) (li1_bump d)
          (fun y => matVecMul (a y - σ • (1 : Mat d)) (u.grad y)) x := by
    intro kk hcs x hx
    refine l2e_mollify_congr hcs hx hηs fun y hy => ?_
    simp only [l2d_flux, l2d_gradc, Set.indicator_of_mem hy, l2e_matVecMul_sub_smul_one]
  have hclean2 : ∀ kk : Fin d → ℤ, l2b_cell (l2b_pt n kk) (n + 1) ⊆ V →
      ∀ x ∈ l2b_cell (l2b_pt n kk) n,
        a16_mollify d ((3 : ℝ) ^ n) (li1_bump d) (l2d_flux a V u) x =
        a16_mollify d ((3 : ℝ) ^ n) (li1_bump d) (fun y => matVecMul (a y) (u.grad y)) x := by
    intro kk hcs x hx
    refine l2e_mollify_congr hcs hx hηs fun y hy => ?_
    simp only [l2d_flux, Set.indicator_of_mem hy]
  have hcore := Hcore hUV (n := n) (r := 4 * (3 : ℝ) ^ n) (le_of_eq (by field_simp))
    (le_of_eq (by field_simp)) (by positivity) hgeo (by linarith only [h3]) (by linarith only [h3])
    hVne (Λ := (3 : ℝ) ^ k) h3k.le hvolΛ (η := li1_bump d) (Bη := l2e_bumpB d)
    (li1_bump_contDiff d) (l2e_bump_bound d) (li1_bump_nonneg d) (li1_bump_integral d) hηs
    (ϑ := ENNReal.ofReal t) hϑ a (s := σ) (lt_of_lt_of_le hν0 hσν) u g ub f hfP (hfl u) hu' hub
    hu10 hub10
    (α := ENNReal.ofReal (l2e_Kp d) * ENNReal.ofReal (l2e_aC Cin σ ν (deltaScale ε ρ k)))
    (β := ENNReal.ofReal (l2e_Kp d) *
      ENNReal.ofReal (l2e_b Cin σ ν ρ (deltaScale ε ρ k) k n))
    (α' := ENNReal.ofReal (l2e_Kp d) * ENNReal.ofReal (l2e_aC Cin σ ν (deltaScale ε ρ k)) +
      ENNReal.ofReal (σ * l2e_Kp d) * ENNReal.ofReal (l2e_e Cin σ ν))
    (β' := ENNReal.ofReal (l2e_Kp d) * ENNReal.ofReal (l2e_b Cin σ ν ρ (deltaScale ε ρ k) k n) +
      ENNReal.ofReal (σ * l2e_Kp d) * ENNReal.ofReal (l2e_g Cin σ ν n))
    (fun kk hcs x hx => by
      rw [hclean3 kk hcs x hx]; exact (hcell u f hfaem hu' kk hcs x hx).1)
    (fun kk hcs x hx => by
      rw [hclean2 kk hcs x hx]; exact (hcell u f hfaem hu' kk hcs x hx).2)
  -- the parameters
  have hRθ : R ≤ R ^ θ := by
    have := Real.rpow_le_rpow_of_exponent_ge hR0 hR1 hθ1
    simpa only [ge_iff_le, Real.rpow_one] using this
  have hkN : 0 ≤ (k : ℝ) ^ (A + 3) := by positivity
  have hRk : R * (k : ℝ) ^ (A + 3) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hRθ hkN).trans hsep
  have htk : t * (k : ℝ) ^ (A + 3) ≤ cv := by
    have e : t = cvol ^ θ * R ^ θ := Real.mul_rpow hcvol.le hR0.le
    rw [e, hcv]
    calc cvol ^ θ * R ^ θ * (k : ℝ) ^ (A + 3) = cvol ^ θ * (R ^ θ * (k : ℝ) ^ (A + 3)) := by ring
      _ ≤ cvol ^ θ * 1 := mul_le_mul_of_nonneg_left hsep (Real.rpow_nonneg hcvol.le _)
      _ = cvol ^ θ := mul_one _
  have hcv0 : 0 ≤ cv := Real.rpow_nonneg hcvol.le _
  have hc3 : ((3 : ℝ)⁻¹) ^ k * (3 : ℝ) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  have hblock := l2e_block_ineq X Y Fn (k := (k : ℝ)) (ν := ν) (ε := ε) (ρ := ρ) (σ := σ)
    (δ := deltaScale ε ρ k) (C := Cin) (K' := l2e_Kp d) (c0 := C0) (cv := cv) (R := R) (t := t)
    (c3 := ((3 : ℝ)⁻¹) ^ k) (L3 := (3 : ℝ) ^ k) (Pn := (3 : ℝ) ^ n)
    (p := (3 : ℝ) ^ n + 4 * (3 : ℝ) ^ n) (aC := l2e_aC Cin σ ν (deltaScale ε ρ k))
    (e := l2e_e Cin σ ν) (b := l2e_b Cin σ ν ρ (deltaScale ε ρ k) k n)
    (g := l2e_g Cin σ ν n) (A := A) hk3 hε0 hε1 hρ0 hρ1 hν0 hν1 hσν hσk rfl hthr
    (by linarith only [hCin]) hKp0 hC0 hcv0 hc3 h3k (by rw [hR]; field_simp) (by ring) hR0 hRk
    ht0 htk rfl rfl rfl rfl
  have hmul := mul_le_mul' (le_refl (ENNReal.ofReal (((3 : ℝ)⁻¹) ^ k))) hcore
  have hCsle : Cs ≤ max 1 Cs := le_max_right _ _
  have hδ0 : 0 ≤ deltaScale ε ρ k := by
    have := (l2e_delta_bounds hk3 hε0 hε1 hρ0 hρ1).1
    have h0 : 0 ≤ ε * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    linarith only [this, h0]
  have hT0 : 0 ≤ deltaScale ε ρ k * (Real.sqrt σ)⁻¹ * Real.sqrt ν := by positivity
  have hQ0 : 0 ≤ ((k : ℝ) ^ A)⁻¹ := by positivity
  refine hmul.trans (hblock.trans ?_)
  gcongr

theorem l2e_ceil_facts {M : ℝ} {k : ℕ} (hM : 0 < M) (hM3 : 1 ≤ M * Real.log 3) (hk : 3 ≤ (k : ℝ))
    (hk4 : 4 * M ^ 2 ≤ (k : ℝ)) :
    1 ≤ ⌈M * Real.log (k : ℝ)⌉₊ ∧ ⌈M * Real.log (k : ℝ)⌉₊ ≤ k ∧
      (k : ℝ) ≤ (3 : ℝ) ^ ⌈M * Real.log (k : ℝ)⌉₊ := by
  have hk0 : 0 < (k : ℝ) := by linarith only [hk]
  have hlog0 : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith only [hk])
  have hMl : 0 < M * Real.log (k : ℝ) := mul_pos hM hlog0
  refine ⟨Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 hMl)), ?_, ?_⟩
  · rw [Nat.ceil_le]
    have h1 : Real.log (k : ℝ) ≤ (k : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
      Real.log_le_rpow_div hk0.le (by norm_num)
    have hs : (k : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt k := (Real.sqrt_eq_rpow _).symm
    rw [hs] at h1
    have hsq : 2 * M ≤ Real.sqrt k := by
      rw [Real.le_sqrt (by positivity)]
      · nlinarith only [hk4]
      · exact hk0.le
    have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
    have h2 : M * Real.log (k : ℝ) ≤ M * (Real.sqrt k / (1 / 2)) := mul_le_mul_of_nonneg_left h1 hM.le
    have h3 : M * (Real.sqrt k / (1 / 2)) = 2 * M * Real.sqrt k := by ring
    have h4 : 2 * M * Real.sqrt k ≤ Real.sqrt k * Real.sqrt k :=
      mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)
    linarith only [h2, h3, h4, hsk]
  · have hc : M * Real.log (k : ℝ) ≤ (⌈M * Real.log (k : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    have h1 : (3 : ℝ) ^ (M * Real.log (k : ℝ)) ≤ (3 : ℝ) ^ (⌈M * Real.log (k : ℝ)⌉₊ : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hc
    rw [Real.rpow_natCast] at h1
    refine le_trans ?_ h1
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    calc (k : ℝ) = Real.exp (Real.log k) := (Real.exp_log hk0).symm
      _ ≤ Real.exp (Real.log 3 * (M * Real.log (k : ℝ))) := by
        apply Real.exp_le_exp.2
        nlinarith only [hM3, hlog0]


theorem l2e_sep {θ : ℝ} {k n N : ℕ} (hk1 : 1 ≤ (k : ℝ))
    (h : (3 : ℝ) ^ (θ * ((n : ℝ) - k)) ≤ ((k : ℝ) ^ N)⁻¹) :
    ((3 : ℝ) ^ n / (3 : ℝ) ^ k) ^ θ * (k : ℝ) ^ N ≤ 1 := by
  have hk0 : 0 < (k : ℝ) := by linarith only [hk1]
  have e : (3 : ℝ) ^ n / (3 : ℝ) ^ k = (3 : ℝ) ^ ((n : ℝ) - k) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_natCast]
  rw [e, ← Real.rpow_mul (by norm_num), mul_comm ((n : ℝ) - k) θ]
  have hN : 0 < (k : ℝ) ^ N := pow_pos hk0 N
  calc (3 : ℝ) ^ (θ * ((n : ℝ) - k)) * (k : ℝ) ^ N ≤ ((k : ℝ) ^ N)⁻¹ * (k : ℝ) ^ N :=
        mul_le_mul_of_nonneg_right h hN.le
    _ = 1 := inv_mul_cancel₀ hN.ne'

/-- Satisfiability of the window facts: `M = 1`, `k = 100`. -/
example : True := by
  have hl3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith only [this]
  have _ := l2e_ceil_facts (M := 1) (k := 100) one_pos (by linarith only [hl3]) (by norm_num)
    (by norm_num)
  trivial

end SuperdiffusionCLT.Section7

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal Pointwise
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- **`p.Dirichlet.L2.blackbox` on the uniform `C^{1,1}` class**, in
the frame of the centre `y`: the field is the recentered field of the translated sample, the domain
`V` lies in the origin cube `□_k` and is uniformly `C^{1,1}` after the rescaling by `3^{-k}`. -/
theorem l2_prop (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hInputs :
        ∃ C : ℝ, 1 ≤ C ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
        ∀ ε ρ M : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M →
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
        ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
        Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ρ)
        (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
        ∀ m n : ℕ,
        X0 omega ≤ (3 : ℝ) ^ m →
        Lhat ≤ (m : ℝ) →
        (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) →
        n ≤ m →
        (∀ k : Fin d → ℤ,
        (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
        Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
        Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
        -- e.Dir.new.full.good
        Homogenization.HomogenizationErrorOnCube
        (Homogenization.originCube d (n : ℤ)) (1 / 9)
        Homogenization.MultiscaleExponent.infinity
        (Homogenization.MultiscaleExponent.finite 2)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
        (1 : Homogenization.Mat d)) ≤
        ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
        -- e.Dir.new.reg.ellipticity
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
        Homogenization.LambdaSq (Homogenization.originCube d (n : ℤ))
        (1 / 4) (Homogenization.MultiscaleExponent.finite 1)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) +
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
        (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ))
        (1 / 4) (Homogenization.MultiscaleExponent.finite 1)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)))⁻¹ ≤
        C ∧
        -- e.Dir.new.weak.flux, e.Dir.new.weak.grad, e.Dir.new.harmonic.approx
        (∀ u : Homogenization.AHarmonicFunction
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (Homogenization.openCubeSet (Homogenization.originCube d (n : ℤ))),
        ENNReal.ofReal
        (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (Homogenization.originCube d (n : ℤ)) (1 / 4)
        (fun x => Homogenization.matVecMul
        (nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) -
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P • (1 : Homogenization.Mat d))
        (u.toH1.grad x))) ≤
        ENNReal.ofReal
        (C *
        Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P) *
        (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧
        ENNReal.ofReal
        (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤
        ENNReal.ofReal
        (C *
        (Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P))⁻¹ *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧
        ∃ w : Homogenization.AHarmonicFunction
        (fun _ => (1 : Homogenization.Mat d))
        (Homogenization.openCubeSet
        (Homogenization.originCube d ((n : ℤ) - 1))),
        ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d ((n : ℤ) - 1)) 2
        (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤
        ENNReal.ofReal
        (C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) *
        (Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P))⁻¹ *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x =>
        Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧
        -- e.Dir.new.sstar.close
        Homogenization.matNorm
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P)⁻¹ •
        Homogenization.sigmaCoarse
        (Homogenization.cubeSet
        (Homogenization.originCube d (n : ℤ)))
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) -
        1) +
        Homogenization.matNorm
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P)⁻¹ •
        Homogenization.sigmaStarCoarse
        (Homogenization.cubeSet
        (Homogenization.originCube d (n : ℤ)))
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) -
        1) ≤
        C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧
        -- e.Dir.new.k.bounds
        ENNReal.ofReal ((m : ℝ)⁻¹) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (m : ℤ)) ∞
        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) +
        ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 4 : ℝ) * (m : ℝ)))) *
        SuperdiffusionCLT.Section2.Norms.matHatNegENorm
        (Homogenization.originCube d (m : ℤ)) (1 / 4) 2
        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤
        ENNReal.ofReal ((m : ℝ) ^ ρ))
    (hS5 :
        ∃ C : ℝ, 1 ≤ C ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
        ∃ M : ℕ,
        ∀ (P : MeasureTheory.ProbabilityMeasure
        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
        hPrefix hJ2 hJ3 →
        ∀ m : ℕ, M ≤ m →
        |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P -
        (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
        C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K))
    (r' M₁' M₂' D' : ℝ) (A : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
      ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
        (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∃ X0 : ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ y : Vec d, ∀ᵐ omega ∂P.toMeasure, ∀ k : ℕ,
          X0 (ShellField.translateSequence y omega) ≤ (3 : ℝ) ^ k → Lhat ≤ (k : ℝ) →
          ∀ V : Set (Vec d), V ⊆ Section6.engCube d k →
            IsUniformC11Domain (((3 : ℝ) ^ k)⁻¹ • V) r' M₁' M₂' D' →
            LipL2Block
              (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega)) nu
              (sigmaBarInfinite nu k P) (deltaScale ε ρ (k : ℝ)) C A k V := by
  obtain ⟨Cin, hCin1, Hin⟩ := l2b_ae_cell d hd hInputs
  obtain ⟨hp1, hp2, -, -⟩ := l2d_exponents hd
  have hp0 : 0 < Real.conjExponent (sobStar d) := by linarith only [hp1]
  set θ : ℝ := 1 / Real.conjExponent (sobStar d) - 1 / 2 with hθdef
  have hθ0 : 0 < θ := by
    have : 1 / 2 < 1 / Real.conjExponent (sobStar d) := by
      rw [div_lt_div_iff₀ (by norm_num) hp0]; linarith only [hp2]
    linarith only [this, hθdef]
  obtain ⟨M₀, Hsep⟩ := scale_separation_ceil 0 θ (A + 3) le_rfl hθ0
  obtain ⟨Cf, hCf1, Hdet⟩ := l2e_det hd r' M₁' M₂' D' Cin hCin1 A
  refine ⟨Cf, hCf1, ?_⟩
  intro nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set M : ℝ := max (max Cin M₀) (1 / Real.log 3) with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hM3 : 1 ≤ M * Real.log 3 := by
    have : 1 / Real.log 3 ≤ M := le_max_right _ _
    rw [div_le_iff₀ hl3] at this
    exact this
  have hMC : Cin ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hMM₀ : M₀ ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨Lhat1, hL1, H2⟩ := Hin nu hnu hnu1 cStar hcStar K ε ρ M hε hε1 hρ hρ1 hMC
  obtain ⟨L₀σ, hσwin⟩ := lip_sigma_window d hd hS5 nu hnu hnu1 cStar hcStar K
  obtain ⟨Ls, hLs1, hLs⟩ := Hsep 1 1 one_pos one_pos
  set κd : ℝ := (d : ℝ) + (1 + d) * max M₁' 0 with hκd
  set Nthr : ℝ := max Lhat1 (max (L₀σ : ℝ) (max Ls (max (1 / (ε * nu ^ 2)) (max 3
    (max (12 * (3 * κd + 4) / r') (max (4 * M ^ 2) 1)))))) with hNthr
  have hall : Lhat1 ≤ Nthr ∧ (L₀σ : ℝ) ≤ Nthr ∧ Ls ≤ Nthr ∧ 1 / (ε * nu ^ 2) ≤ Nthr ∧
      (3 : ℝ) ≤ Nthr ∧ 12 * (3 * κd + 4) / r' ≤ Nthr ∧ 4 * M ^ 2 ≤ Nthr := by
    simp only [hNthr, le_max_iff, le_refl, true_or, or_true, and_self]
  obtain ⟨hN1, hN2, hN3', hN4, hN3, hN6, hN7⟩ := hall
  refine ⟨Nthr, hL1.trans hN1, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X0, hX0m, hX01, hX0O, hae⟩ := H2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨X0, hX0m, hX01, hX0O.mono_scale hN1, fun y => ?_⟩
  have hqmp := (translateSequence_measurePreserving hPrefix hJ2 y).quasiMeasurePreserving
  filter_upwards [hqmp.ae hae, hqmp.ae (Section6.ae_centered_eq_recentered_add_skew hJ3 nu),
    hqmp.ae (Section6.l9_ae_exists_ell_centered hJ3 hnu)] with ω hω hskew hell
  intro k hXk hLk V hVsub hVuni
  have hkN : Nthr ≤ (k : ℝ) := hLk
  have hk3 : (3 : ℝ) ≤ k := hN3.trans hkN
  have hk1 : (1 : ℝ) ≤ k := by linarith only [hk3]
  have hk0 : (0 : ℝ) < k := by linarith only [hk3]
  have hk4 : 4 * M ^ 2 ≤ (k : ℝ) := hN7.trans hkN
  obtain ⟨hκ1, hκk, hk3κ⟩ := l2e_ceil_facts hMpos hM3 hk3 hk4
  set κm : ℕ := ⌈M * Real.log (k : ℝ)⌉₊ with hκm
  set n : ℕ := k - κm with hndef
  have hn1 : n + 1 ≤ k := by omega
  have hnκ : n + κm = k := by omega
  have hn_int : (k : ℤ) - ⌈M * Real.log (k : ℝ)⌉ ≤ (n : ℤ) := by
    have : ((κm : ℕ) : ℤ) = ⌈M * Real.log (k : ℝ)⌉ :=
      Int.natCast_ceil_eq_ceil (by positivity)
    rw [← this]; omega
  -- the window of `σ̄`
  obtain ⟨hσ1, hσk, -, -⟩ := hσwin P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 k k
    (by exact_mod_cast (hN2.trans hkN)) le_rfl (by omega)
  set σ : ℝ := sigmaBarInfinite nu k P with hσdef
  have hσν : nu ≤ σ := hnu1.trans hσ1
  -- the scale separation
  have hsep : ((3 : ℝ) ^ n / (3 : ℝ) ^ k) ^ θ * (k : ℝ) ^ (A + 3) ≤ 1 := by
    have h := hLs M hMM₀ (k : ℝ) (n : ℤ) 1 (hN3'.trans hkN) zero_le_one (by linarith only [hk1])
      (by
        have : ((n : ℤ) : ℝ) = (k : ℝ) - (κm : ℝ) := by
          have : (n : ℝ) = (k : ℝ) - (κm : ℝ) := by
            rw [hndef, Nat.cast_sub (by omega)]
          simpa only [Int.cast_natCast] using this
        have hci : ((κm : ℕ) : ℤ) = ⌈M * Real.log (k : ℝ)⌉ :=
          Int.natCast_ceil_eq_ceil (by positivity)
        have hc : (κm : ℝ) = ((⌈M * Real.log (k : ℝ)⌉ : ℤ) : ℝ) := by
          rw [← hci]; push_cast; rfl
        rw [this, hc])
    simp only [Real.rpow_zero, neg_zero, mul_one, one_mul, Int.cast_natCast] at h
    exact l2e_sep hk1 h
  -- the geometric condition
  have hr'0 : 0 < r' := hVuni.2.1
  have hgeo : 3 * (4 * (3 : ℝ) ^ n) ≤
      ((3 : ℝ) ^ k * r') / (3 * ((d : ℝ) + (1 + d) * max M₁' 0) + 4) := by
    have hκ0 : 0 ≤ max M₁' 0 := le_max_right _ _
    have hκpos : 0 < 3 * ((d : ℝ) + (1 + d) * max M₁' 0) + 4 := by positivity
    rw [le_div_iff₀ hκpos]
    have h1 : 12 * (3 * κd + 4) ≤ (k : ℝ) * r' := by
      have := hN6.trans hkN
      rw [div_le_iff₀ hr'0] at this
      exact this
    have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
    have h2 : (3 : ℝ) ^ k = (3 : ℝ) ^ n * (3 : ℝ) ^ κm := by rw [← pow_add, hnκ]
    calc 3 * (4 * (3 : ℝ) ^ n) * (3 * ((d : ℝ) + (1 + d) * max M₁' 0) + 4)
        = (3 : ℝ) ^ n * (12 * (3 * κd + 4)) := by rw [hκd]; ring
      _ ≤ (3 : ℝ) ^ n * ((k : ℝ) * r') := mul_le_mul_of_nonneg_left h1 h3.le
      _ ≤ (3 : ℝ) ^ n * ((3 : ℝ) ^ κm * r') := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk3κ hr'0.le) h3.le
      _ = (3 : ℝ) ^ k * r' := by rw [h2]; ring
  -- the fields
  have hVo : IsOpen V := by
    have h3k : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
    have := (hVuni.smul h3k).1
    rwa [l2e_smul_inv_smul h3k] at this
  have hVm : MeasurableSet V := hVo.measurableSet
  have hVb : Bornology.IsBounded V :=
    (isBounded_openCubeSet (originCube d (k : ℤ))).subset hVsub
  have : IsFiniteMeasure (volumeMeasureOn V) :=
    ⟨by simpa only [volumeMeasureOn, MeasurableSet.univ, Measure.restrict_apply, univ_inter] using hVb.measure_lt_top⟩
  set ω' := ShellField.translateSequence y ω with hω'
  set a : CoeffField d := fun x => nu • (1 : Mat d) +
    SuperdiffusionCLT.Section2.Carriers.centeredStreamField ω'
      (cubeSet (originCube d (k : ℤ))) x with hadef
  obtain ⟨lam, Lam, hl⟩ := hell k k 0
  have hEll : IsEllipticFieldOn lam Lam V a := by
    have := wh2_isEllipticFieldOn_mono hVm (hVsub.trans (openCubeSet_subset_cubeSet _)) hl
    simpa only [zero_add] using this
  have hfl : ∀ u : H1Function V, MemVectorL2 V (fun x => matVecMul (a x) (u.grad x)) :=
    fun u => memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  obtain ⟨K0, hK0, hKx⟩ := hskew k
  have hequiv : ∀ (u : H1Function V) (f : Vec d → ℝ),
      IsWeakSolutionOn (Section6.fullCoefficientRecentered nu ω') V u f (fun _ => 0) →
        IsWeakSolutionOn a V u f (fun _ => 0) := by
    intro u f hsol
    have hflux : MemVectorL2 V (fun x => matVecMul
        (Section6.fullCoefficientRecentered nu ω' x) (u.grad x)) := by
      have h2 := (hfl u).sub (SuperdiffusionCLT.Section2.CoarseGraining.memVectorL2_matVecMul_const
        K0 u.grad_memVectorL2)
      have e : (fun x => matVecMul (Section6.fullCoefficientRecentered nu ω' x) (u.grad x)) =
          ((fun x => matVecMul (a x) (u.grad x)) - fun x => matVecMul K0 (u.grad x)) := by
        funext x
        rw [Pi.sub_apply]
        simp only [hadef]
        rw [hKx x, add_matVecMul]
        abel
      rw [e]
      exact h2
    exact (isWeakSolutionOn_congr_const_skew hVo hK0
      (a := Section6.fullCoefficientRecentered nu ω') (b := a) (fun x => hKx x) hflux).2 hsol
  have hηs : ∀ w : Vec d, (∃ i, 1 < |w i|) → li1_bump d w = 0 := (l2c_mollifier_witness d).2.2.2
  have hcell : ∀ (u : H1Function V) (f : Vec d → ℝ), AEMeasurable f (volume.restrict V) →
      IsWeakSolutionOn a V u f (fun _ => 0) →
      ∀ kk : Fin d → ℤ, l2b_cell (l2b_pt n kk) (n + 1) ⊆ V →
      ∀ x ∈ l2b_cell (l2b_pt n kk) n,
        ENNReal.ofReal ‖a16_mollify d ((3 : ℝ) ^ n) (li1_bump d)
            (fun y => matVecMul (a y - σ • (1 : Mat d)) (u.grad y)) x‖ ≤
          (ENNReal.ofReal (l2e_Kp d) * ENNReal.ofReal (l2e_aC Cin σ nu (deltaScale ε ρ k))) *
              l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                (l2b_cell (l2b_pt n kk) (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 +
            (ENNReal.ofReal (l2e_Kp d) *
                ENNReal.ofReal (l2e_b Cin σ nu ρ (deltaScale ε ρ k) k n)) *
              l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                (l2b_cell (l2b_pt n kk) (n + 1)) (fun x => ‖f x‖ₑ)
                (Real.conjExponent (sobStar d)) ∧
        ENNReal.ofReal ‖a16_mollify d ((3 : ℝ) ^ n) (li1_bump d)
            (fun y => matVecMul (a y) (u.grad y)) x‖ ≤
          (ENNReal.ofReal (l2e_Kp d) * ENNReal.ofReal (l2e_aC Cin σ nu (deltaScale ε ρ k)) +
              ENNReal.ofReal (σ * l2e_Kp d) * ENNReal.ofReal (l2e_e Cin σ nu)) *
              l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                (l2b_cell (l2b_pt n kk) (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 +
            (ENNReal.ofReal (l2e_Kp d) *
                  ENNReal.ofReal (l2e_b Cin σ nu ρ (deltaScale ε ρ k) k n) +
                ENNReal.ofReal (σ * l2e_Kp d) * ENNReal.ofReal (l2e_g Cin σ nu n)) *
              l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                (l2b_cell (l2b_pt n kk) (n + 1)) (fun x => ‖f x‖ₑ)
                (Real.conjExponent (sobStar d)) := by
    intro u f hfm hsol kk hcs x hx
    obtain ⟨b1, b3⟩ := hω k n hXk (hN1.trans hkN) hn_int hn1 V hVsub u f hfm hsol (li1_bump d)
      (l2e_bumpB d) (l2e_bumpL d) (l2e_bump_bound d) (l2e_bump_lipschitz d) hηs kk hcs x hx
    simp only [zpow_natCast] at b1 b3
    rw [← hσdef] at b1 b3
    constructor
    · refine b1.trans (le_of_eq ?_)
      simp only [l2e_b, l2e_aC, deltaScale, l2e_Kp, pow_succ]
      ring_nf
    · refine b3.trans (le_of_eq ?_)
      simp only [l2e_b, l2e_aC, l2e_e, l2e_g, deltaScale, l2e_Kp, pow_succ]
      ring_nf
  have hthr : 1 ≤ (k : ℝ) * ε * nu ^ 2 := by
    have := hN4.trans hkN
    rw [div_le_iff₀ (by positivity)] at this
    linarith only [this]
  exact Hdet a (Section6.fullCoefficientRecentered nu ω') hnu hnu1 hε hε1 hρ hρ1 hσν hσk hk3 hthr
    hn1 hgeo hsep hVsub hVuni hfl hequiv hcell

end SuperdiffusionCLT.Section7
