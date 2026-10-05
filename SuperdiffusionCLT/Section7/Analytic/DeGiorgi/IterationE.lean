/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.IterationB

/-!
# Algebra of the De Giorgi recursion
-/

@[expose] public section

open Homogenization MeasureTheory

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The one-step estimate, after the substitutions `δ² = L²/(64 F)` and `h² = M²/(4 F)`, gives
the normalised superlinear recursion. -/
theorem recursion_algebra {Cs c K0 L M r F δ h a a' T β e dd Ed a1 : ℝ}
    (hCs : 0 ≤ Cs) (hK0 : 0 ≤ K0) (hL : 0 < L) (hM : 0 < M) (hr : 1 ≤ r)
    (hF : 0 < F) (hβ : 0 ≤ β) (he : e + dd * β = 2)
    (hδ2 : δ ^ 2 = L ^ 2 / (64 * F)) (hh2 : h ^ 2 = M ^ 2 / (4 * F))
    (ha' : 0 ≤ a') (hT0 : 0 ≤ T) (ha'a : a' ≤ a) (hTa : h ^ 2 * T ≤ a)
    (hEd : Ed ≤ M ^ 2 / L ^ 2)
    (ha1 : a1 ≤ Cs * L ^ e * (2 * K0 * (r ^ 2 * (c / δ) ^ 2 * a' + Ed * T) +
      2 * (c / δ) ^ 2 * a') * T ^ β) :
    a1 / (L ^ dd * M ^ 2) ≤ (Cs * (2 * K0 * (64 * c ^ 2 + 4) + 128 * c ^ 2) * 4 ^ β) * r ^ 2 *
      F ^ (1 + β) * (a / (L ^ dd * M ^ 2)) ^ (1 + β) := by
  have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have ha0 : 0 ≤ a := ha'.trans ha'a
  have hL2 : 0 < L ^ 2 := by positivity
  have hM2 : 0 < M ^ 2 := by positivity
  have hG2 : (c / δ) ^ 2 = 64 * F * c ^ 2 / L ^ 2 := by
    rw [div_pow, hδ2]; field_simp
  have hTle : T ≤ 4 * F * a / M ^ 2 := by
    rw [hh2] at hTa
    rw [le_div_iff₀ hM2]
    have : M ^ 2 / (4 * F) * T ≤ a := hTa
    have h2 : M ^ 2 * T ≤ 4 * F * a := by
      have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 4 * F)
      have e : 4 * F * (M ^ 2 / (4 * F) * T) = M ^ 2 * T := by field_simp
      linarith only [this, e]
    linarith only [h2]
  have hEdT : Ed * T ≤ 4 * F * a / L ^ 2 := by
    calc Ed * T ≤ (M ^ 2 / L ^ 2) * (4 * F * a / M ^ 2) :=
          mul_le_mul hEd hTle hT0 (by positivity)
      _ = 4 * F * a / L ^ 2 := by field_simp
  set K1 : ℝ := 2 * K0 * (64 * c ^ 2 + 4) + 128 * c ^ 2 with hK1
  set P : ℝ := F * a / L ^ 2 with hP
  have hP0 : 0 ≤ P := by positivity
  have hbr : 2 * K0 * (r ^ 2 * (c / δ) ^ 2 * a' + Ed * T) + 2 * (c / δ) ^ 2 * a' ≤
      P * (K1 * r ^ 2) := by
    have e1 : r ^ 2 * (c / δ) ^ 2 * a' ≤ 64 * c ^ 2 * r ^ 2 * P := by
      rw [hG2]
      calc r ^ 2 * (64 * F * c ^ 2 / L ^ 2) * a' ≤ r ^ 2 * (64 * F * c ^ 2 / L ^ 2) * a :=
            mul_le_mul_of_nonneg_left ha'a (by positivity)
        _ = 64 * c ^ 2 * r ^ 2 * P := by rw [hP]; field_simp
    have e2 : 2 * (c / δ) ^ 2 * a' ≤ 128 * c ^ 2 * P := by
      rw [hG2]
      calc 2 * (64 * F * c ^ 2 / L ^ 2) * a' ≤ 2 * (64 * F * c ^ 2 / L ^ 2) * a :=
            mul_le_mul_of_nonneg_left ha'a (by positivity)
        _ = 128 * c ^ 2 * P := by rw [hP]; field_simp; ring
    have e3 : Ed * T ≤ 4 * P := by
      have : 4 * F * a / L ^ 2 = 4 * P := by rw [hP]; ring
      linarith only [hEdT, this]
    have e4 : 2 * K0 * (r ^ 2 * (c / δ) ^ 2 * a' + Ed * T) ≤
        2 * K0 * (64 * c ^ 2 * r ^ 2 * P + 4 * P) :=
      mul_le_mul_of_nonneg_left (add_le_add e1 e3) (by positivity)
    have e5 : 0 ≤ P * ((r ^ 2 - 1) * (8 * K0 + 128 * c ^ 2)) :=
      mul_nonneg hP0 (mul_nonneg (by linarith only [hr2]) (by positivity))
    rw [hK1]
    linarith only [e2, e4, e5]
  have hTβ : T ^ β ≤ (4 * F * a / M ^ 2) ^ β := Real.rpow_le_rpow hT0 hTle hβ
  have hCL0 : 0 ≤ Cs * L ^ e := by positivity
  have ha2 : a1 ≤ Cs * L ^ e * (P * (K1 * r ^ 2)) * (4 * F * a / M ^ 2) ^ β :=
    ha1.trans (mul_le_mul (mul_le_mul_of_nonneg_left hbr hCL0) hTβ (by positivity) (by positivity))
  have hLdd : 0 < L ^ dd := Real.rpow_pos_of_pos hL dd
  set X : ℝ := a / (L ^ dd * M ^ 2) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have haX : a = X * (L ^ dd * M ^ 2) := by rw [hXdef]; field_simp
  have h4 : 4 * F * a / M ^ 2 = 4 * F * L ^ dd * X := by rw [haX]; field_simp
  have hPdiv : P / (L ^ dd * M ^ 2) = F * X / L ^ 2 := by rw [hP, haX]; field_simp
  have hLe : L ^ e * (L ^ dd) ^ β = L ^ 2 := by
    rw [← Real.rpow_mul hL.le, ← Real.rpow_add hL, he]
    norm_num
  rw [h4] at ha2
  have hF1 : F ^ (1 + β) = F * F ^ β := by rw [Real.rpow_add hF, Real.rpow_one]
  have hX1 : X ^ (1 + β) = X * X ^ β := by
    rw [Real.rpow_add' hX0 (by linarith only [hβ]), Real.rpow_one]
  calc a1 / (L ^ dd * M ^ 2)
      ≤ (Cs * L ^ e * (P * (K1 * r ^ 2)) * (4 * F * L ^ dd * X) ^ β) / (L ^ dd * M ^ 2) :=
        div_le_div_of_nonneg_right ha2 (by positivity)
    _ = Cs * L ^ e * (K1 * r ^ 2) * (4 * F * L ^ dd * X) ^ β * (P / (L ^ dd * M ^ 2)) := by ring
    _ = (Cs * K1 * 4 ^ β) * r ^ 2 * (F * F ^ β) * (X * X ^ β) * ((L ^ e * (L ^ dd) ^ β) / L ^ 2) := by
        rw [hPdiv, Real.mul_rpow (by positivity) hX0, Real.mul_rpow (by positivity) hLdd.le,
          Real.mul_rpow (by positivity) hF.le]
        field_simp
    _ = _ := by rw [hLe, div_self hL2.ne', mul_one, hF1, hX1]

theorem volume_axisCube_lt_top (z : Vec d) (L : ℝ) : volume (axisCube z L) < ⊤ := by
  have := measure_univ_axisCube z L
  rw [Measure.restrict_apply_univ] at this
  rw [this]
  exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

theorem integrable_sq_max_sub {z : Vec d} {L : ℝ} (u : H1Function (axisCube z L)) (k : ℝ) :
    Integrable (fun x => max (u.toFun x - k) 0 ^ 2) (volume.restrict (axisCube z L)) := by
  obtain ⟨v, hv, -⟩ := exists_h1_max_sub_const (isOpenBoundedConvexDomain_axisCube z L) u k
  have := v.memL2.integrable_sq
  rw [hv] at this
  exact this

theorem level_mass_anti {z : Vec d} {L : ℝ} (u : H1Function (axisCube z L)) {k k' : ℝ}
    (hk : k ≤ k') {s : ℝ} (hs : 0 ≤ s) :
    ∫ x in subCube z L s, max (u.toFun x - k') 0 ^ 2 ≤
      ∫ x in subCube z L s, max (u.toFun x - k) 0 ^ 2 := by
  have hmono : volume.restrict (subCube z L s) ≤ volume.restrict (axisCube z L) :=
    Measure.restrict_mono (subCube_subset hs) le_rfl
  refine integral_mono ((integrable_sq_max_sub u k').mono_measure hmono)
    ((integrable_sq_max_sub u k).mono_measure hmono) fun x => ?_
  exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max (by linarith only [hk]) le_rfl) 2

theorem chebyshev_level {z : Vec d} {L : ℝ} (u : H1Function (axisCube z L)) (k : ℝ) {h : ℝ}
    (hh : 0 < h) {s : ℝ} (hs : 0 ≤ s) :
    h ^ 2 * (volume ({x | k + h < u.toFun x} ∩ subCube z L s)).toReal ≤
      ∫ x in subCube z L s, max (u.toFun x - k) 0 ^ 2 := by
  have hmono : volume.restrict (subCube z L s) ≤ volume.restrict (axisCube z L) :=
    Measure.restrict_mono (subCube_subset hs) le_rfl
  have hQsm : MeasurableSet (subCube z L s) := (isOpen_subCube z L s).measurableSet
  set μ : Measure (Vec d) := volume.restrict (subCube z L s) with hμ
  have : IsFiniteMeasure μ := ⟨by
    rw [hμ, Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono (subCube_subset hs)) (volume_axisCube_lt_top z L)⟩
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (f := fun x => max (u.toFun x - k) 0 ^ 2)
    (Filter.Eventually.of_forall fun x => sq_nonneg _)
    ((integrable_sq_max_sub u k).mono_measure hmono) (h ^ 2)
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg h)) hM
  rw [measureReal_def]
  refine ENNReal.toReal_mono (measure_ne_top μ _) ?_
  rw [hμ, Measure.restrict_apply' hQsm]
  refine measure_mono (Set.inter_subset_inter_left _ fun x hx => ?_)
  have hx' : k + h < u.toFun x := hx
  have : h ≤ max (u.toFun x - k) 0 := le_trans (by linarith only [hx']) (le_max_left _ _)
  exact pow_le_pow_left₀ hh.le this 2

/-- The geometric margin sequence `s_j = (L/4)(1 - 2^{-j})`. -/
noncomputable def sLev (L : ℝ) (j : ℕ) : ℝ := L / 4 * (1 - (1 / 2 : ℝ) ^ j)

/-- The geometric level sequence `k_j = M (1 - 2^{-j})`. -/
noncomputable def kLev (M : ℝ) (j : ℕ) : ℝ := M * (1 - (1 / 2 : ℝ) ^ j)

/-- The right side of the one-step estimate (`deGiorgi_step`). -/
noncomputable def stepRhs (Cs c : ℝ) (d : ℕ) (L lam Lam Fb Gb δ A T : ℝ) : ℝ :=
  Cs * L ^ (2 * ((d : ℝ) / sobStar d) + 2 - d) *
    (2 * (8 * d ^ 2 + 4) * ((Lam / lam) ^ 2 * (c / δ) ^ 2 * A +
      (1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) * T) + 2 * (c / δ) ^ 2 * A) *
    T ^ (1 - 2 / sobStar d)

theorem sLev_nonneg {L : ℝ} (hL : 0 ≤ L) (j : ℕ) : 0 ≤ sLev L j := by
  unfold sLev
  have : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have : 0 ≤ 1 - (1 / 2 : ℝ) ^ j := by linarith only [this]
  positivity

theorem sLev_le {L : ℝ} (hL : 0 ≤ L) (j : ℕ) : sLev L j ≤ L / 4 := by
  unfold sLev
  have h0 : 0 ≤ (1 / 2 : ℝ) ^ j := by positivity
  have := mul_nonneg (by positivity : 0 ≤ L / 4) h0
  linarith only [this]

theorem kLev_nonneg {M : ℝ} (hM : 0 ≤ M) (j : ℕ) : 0 ≤ kLev M j := by
  unfold kLev
  have : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have : 0 ≤ 1 - (1 / 2 : ℝ) ^ j := by linarith only [this]
  positivity

theorem kLev_le {M : ℝ} (hM : 0 ≤ M) (j : ℕ) : kLev M j ≤ M := by
  unfold kLev
  have h0 : 0 ≤ (1 / 2 : ℝ) ^ j := by positivity
  have := mul_nonneg hM h0
  linarith only [this]

theorem normalized_recursion (hd : 2 ≤ d) {Cs c lam Lam Fb Gb L M : ℝ} {z : Vec d}
    (hL : 0 < L) (hM : 0 < M) (hCs : 0 ≤ Cs) (hr : 1 ≤ Lam / lam)
    (hEd : (1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) ≤ M ^ 2 / L ^ 2)
    (u : H1Function (axisCube z L))
    (hstep : ∀ k : ℝ, 0 ≤ k → ∀ s δ : ℝ, 0 ≤ s → 0 < δ →
      ∫ x in subCube z L (s + δ), max (u.toFun x - k) 0 ^ 2 ≤
        stepRhs Cs c d L lam Lam Fb Gb δ (∫ x in subCube z L s, max (u.toFun x - k) 0 ^ 2)
          (volume ({x | k < u.toFun x} ∩ subCube z L s)).toReal) (j : ℕ) :
    (∫ x in subCube z L (sLev L (j + 1)), max (u.toFun x - kLev M (j + 1)) 0 ^ 2) /
        (L ^ (d : ℝ) * M ^ 2) ≤
      ((Cs + 1) * (2 * (8 * d ^ 2 + 4) * (64 * c ^ 2 + 4) + 128 * c ^ 2) *
          (4 : ℝ) ^ (1 - 2 / sobStar d)) * (Lam / lam) ^ 2 *
        ((4 : ℝ) ^ (1 + (1 - 2 / sobStar d))) ^ (j : ℝ) *
        ((∫ x in subCube z L (sLev L j), max (u.toFun x - kLev M j) 0 ^ 2) /
          (L ^ (d : ℝ) * M ^ 2)) ^ (1 + (1 - 2 / sobStar d)) := by
  have hp : 2 < sobStar d := two_lt_sobStar hd
  have hβ : 0 ≤ 1 - 2 / sobStar d := by
    have : 2 / sobStar d ≤ 1 := by
      rw [div_le_one (by linarith only [hp])]; exact hp.le
    linarith only [this]
  set β : ℝ := 1 - 2 / sobStar d with hβdef
  have hq : 0 < (1 / 2 : ℝ) ^ j := by positivity
  have hq4 : (4 : ℝ) ^ j * ((1 / 2 : ℝ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm j 2, pow_mul, ← mul_pow]
    norm_num
  set s : ℝ := sLev L j with hsdef
  set δ : ℝ := L / 4 * (1 / 2 : ℝ) ^ (j + 1) with hδdef
  set h : ℝ := M * (1 / 2 : ℝ) ^ (j + 1) with hhdef
  have hsd : sLev L (j + 1) = s + δ := by
    rw [hsdef, hδdef]; unfold sLev; ring
  have hkh : kLev M (j + 1) = kLev M j + h := by
    rw [hhdef]; unfold kLev; ring
  have hs : 0 ≤ s := sLev_nonneg hL.le j
  have hδ : 0 < δ := by positivity
  have hh : 0 < h := by positivity
  have hk1 : 0 ≤ kLev M (j + 1) := kLev_nonneg hM.le (j + 1)
  have hst := hstep (kLev M (j + 1)) hk1 s δ hs hδ
  rw [hsd]
  set a : ℝ := ∫ x in subCube z L s, max (u.toFun x - kLev M j) 0 ^ 2 with hadef
  set a' : ℝ := ∫ x in subCube z L s, max (u.toFun x - kLev M (j + 1)) 0 ^ 2 with ha'def
  set T : ℝ := (volume ({x | kLev M (j + 1) < u.toFun x} ∩ subCube z L s)).toReal with hTdef
  have ha'a : a' ≤ a := level_mass_anti u (by rw [hkh]; linarith only [hh]) hs
  have ha'0 : 0 ≤ a' := integral_nonneg fun x => sq_nonneg _
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  have hTa : h ^ 2 * T ≤ a := by
    have := chebyshev_level u (kLev M j) hh hs
    rw [← hkh] at this
    exact this
  have hF : (0 : ℝ) < 4 ^ j := by positivity
  have hδ2 : δ ^ 2 = L ^ 2 / (64 * 4 ^ j) := by
    rw [eq_div_iff (by positivity), hδdef]
    linear_combination L ^ 2 * hq4
  have hh2 : h ^ 2 = M ^ 2 / (4 * 4 ^ j) := by
    rw [eq_div_iff (by positivity), hhdef]
    linear_combination M ^ 2 * hq4
  have he : (2 * ((d : ℝ) / sobStar d) + 2 - d) + (d : ℝ) * β = 2 := by
    rw [hβdef]; ring
  have hY : 0 ≤ L ^ (2 * ((d : ℝ) / sobStar d) + 2 - d) *
      (2 * (8 * (d : ℝ) ^ 2 + 4) * ((Lam / lam) ^ 2 * (c / δ) ^ 2 * a' +
        (1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) * T) + 2 * (c / δ) ^ 2 * a') * T ^ β := by
    positivity
  have ha1 : (∫ x in subCube z L (s + δ), max (u.toFun x - kLev M (j + 1)) 0 ^ 2) ≤
      (Cs + 1) * L ^ (2 * ((d : ℝ) / sobStar d) + 2 - d) *
        (2 * (8 * (d : ℝ) ^ 2 + 4) * ((Lam / lam) ^ 2 * (c / δ) ^ 2 * a' +
          (1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) * T) + 2 * (c / δ) ^ 2 * a') * T ^ β := by
    refine hst.trans ?_
    unfold stepRhs
    have := mul_le_mul_of_nonneg_right (by linarith only [hCs] : Cs ≤ Cs + 1) hY
    linarith only [this]
  have key := recursion_algebra (Cs := Cs + 1) (c := c) (K0 := 8 * (d : ℝ) ^ 2 + 4) (L := L)
    (M := M) (r := Lam / lam) (F := 4 ^ j) (δ := δ) (h := h) (a := a) (a' := a') (T := T)
    (β := β) (e := 2 * ((d : ℝ) / sobStar d) + 2 - d) (dd := (d : ℝ)) (Ed := (1 / lam) ^ 2 *
      (Gb ^ 2 + L ^ 2 * Fb ^ 2)) (a1 := ∫ x in subCube z L (s + δ),
        max (u.toFun x - kLev M (j + 1)) 0 ^ 2) (by linarith only [hCs]) (by positivity) hL hM hr
    hF hβ he hδ2 hh2 ha'0 hT0 ha'a hTa hEd ha1
  have hFB : ((4 : ℝ) ^ j) ^ (1 + β) = ((4 : ℝ) ^ (1 + β)) ^ (j : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [hFB] at key
  exact key

end SuperdiffusionCLT.Section7
