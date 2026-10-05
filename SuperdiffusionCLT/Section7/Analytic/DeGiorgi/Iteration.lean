/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.IterationE
public import Homogenization.HighContrast.Coupled.IterationLemma

/-!
# The De Giorgi `L^∞` iteration

The level-set iteration `k_j = M (1 - 2^{-j})`, `s_j = (L/4)(1 - 2^{-j})` closes, by the geometric
decay lemma `Homogenization.iteration_geometric_decay_tendsto_zero`, into a bound
`u ≤ M` almost everywhere on the half cube, with the power of the ellipticity ratio
`deGiorgiPower d = (1 - 2/2^*)⁻¹` (`= d/2` for `d ≥ 3`, `3/2` for `d = 2`).
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The power of the ellipticity ratio in the `L^∞–L²` bound: `(1 - 2/2^*)⁻¹`. -/
noncomputable def deGiorgiPower (d : ℕ) : ℝ := (1 - 2 / sobStar d)⁻¹

theorem deGiorgiPower_two : deGiorgiPower 2 = 3 / 2 := by
  unfold deGiorgiPower
  rw [sobStar_two]
  norm_num

theorem deGiorgiPower_of_three_le (hd : 3 ≤ d) : deGiorgiPower d = d / 2 := by
  unfold deGiorgiPower
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (d : ℝ) - 2 ≠ 0 := by linarith only [h3]
  have hd0 : (d : ℝ) ≠ 0 := by linarith only [h3]
  have : d ≠ 2 := by omega
  simp only [sobStar, this, ite_false]
  field_simp
  ring

theorem one_sub_two_div_sobStar_pos (hd : 2 ≤ d) : 0 < 1 - 2 / sobStar d := by
  have hp : 2 < sobStar d := two_lt_sobStar hd
  have : 2 / sobStar d < 1 := by
    rw [div_lt_one (by linarith only [hp])]; exact hp
  linarith only [this]

/-- The sequence closing: a normalised superlinear recursion with a small enough initial value
tends to zero. The threshold is `C² r^{2/β}` with `C² = (A₀ B^{1/β})^{1/β}`. -/
theorem normalized_decay {β A0 r : ℝ} (hβ : 0 < β) (hA0 : 0 < A0) (hr : 0 < r) {X : ℕ → ℝ}
    (hX0 : ∀ n, 0 ≤ X n)
    (hrec : ∀ n : ℕ, X (n + 1) ≤ A0 * r ^ 2 * ((4 : ℝ) ^ (1 + β)) ^ (n : ℝ) * X n ^ (1 + β))
    (hinit : Real.sqrt ((A0 * ((4 : ℝ) ^ (1 + β)) ^ (1 / β)) ^ (1 / β)) ^ 2 * (r ^ (1 / β)) ^ 2 *
      X 0 ≤ 1) :
    Tendsto X atTop (𝓝 0) := by
  set B : ℝ := (4 : ℝ) ^ (1 + β) with hB
  have hB1 : 1 < B := Real.one_lt_rpow (by norm_num) (by linarith only [hβ])
  have hB0 : 0 < B := by linarith only [hB1]
  have hβ0 : β ≠ 0 := hβ.ne'
  set C2 : ℝ := (A0 * B ^ (1 / β)) ^ (1 / β) with hC2
  have hC2pos : 0 < C2 := by positivity
  have hsq : Real.sqrt C2 ^ 2 = C2 := Real.sq_sqrt hC2pos.le
  rw [hsq] at hinit
  set D : ℝ := C2 * (r ^ (1 / β)) ^ 2 with hD
  have hDpos : 0 < D := by positivity
  have hDβ : D ^ β = A0 * r ^ 2 * B ^ (1 / β) := by
    rw [hD, Real.mul_rpow hC2pos.le (by positivity), hC2, ← Real.rpow_mul (by positivity),
      one_div_mul_cancel hβ0, Real.rpow_one, rpow_sq_eq hr, ← Real.rpow_mul hr.le]
    have : 2 * (1 / β) * β = 2 := by field_simp
    rw [this]
    simp only [Real.rpow_two]
    ring
  set Z : ℕ → ℝ := fun n => D * X n with hZ
  have hDβpos : 0 < D ^ β := Real.rpow_pos_of_pos hDpos β
  have hAiter : A0 * r ^ 2 / D ^ β = B ^ (-(1 / β)) := by
    rw [hDβ, Real.rpow_neg hB0.le]
    field_simp
  have hAB : A0 * r ^ 2 / D ^ β ≤ B ^ (-(1 / β)) := hAiter.le
  have hdecay := Homogenization.iteration_geometric_decay_tendsto_zero (Y := Z)
    (A := A0 * r ^ 2 / D ^ β) (B := B) (β := β) (by simpa [hZ] using hinit)
    (fun n => mul_nonneg hDpos.le (hX0 n)) hβ hB1 (by positivity) hAB (fun n => ?_)
  · have := hdecay.div_const D
    simpa [hZ, mul_div_assoc, mul_div_cancel_left₀ _ hDpos.ne'] using this
  · have h1 : Z (n + 1) ≤ D * (A0 * r ^ 2 * B ^ (n : ℝ) * X n ^ (1 + β)) :=
      mul_le_mul_of_nonneg_left (hrec n) hDpos.le
    have h2 : A0 * r ^ 2 / D ^ β * B ^ (n : ℝ) * Z n ^ (1 + β) =
        D * (A0 * r ^ 2 * B ^ (n : ℝ) * X n ^ (1 + β)) := by
      rw [hZ]
      simp only
      rw [Real.mul_rpow hDpos.le (hX0 n), Real.rpow_add hDpos, Real.rpow_one]
      field_simp
    rw [h2]
    exact h1

/-- **De Giorgi `L^∞` bound from the level inequalities.** If `u ∈ H¹(Q)` satisfies the weak form
tested by `(u - k)₊ η²` (the hypothesis `hlevel`, for every level `k ≥ 0` and every smooth cutoff
with compact support in `Q`), then `u ≤ M` almost everywhere on the concentric half cube as soon
as `M` dominates the data term `L (Gb + L Fb) / lam` and `C (Λ/λ)^N L^{-d/2} ‖u₊‖_{L²}`, with
`N = deGiorgiPower d`. -/
theorem deGiorgi_sup_bound (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {lam Lam : ℝ} {a : CoeffField d} (z : Vec d) {L : ℝ}, 0 < L →
      IsEllipticFieldOn lam Lam (axisCube z L) a →
      ∀ (u : H1Function (axisCube z L)) (f : Vec d → ℝ) (g : Vec d → Vec d) {Fb Gb : ℝ},
        AEStronglyMeasurable f (volume.restrict (axisCube z L)) →
        AEStronglyMeasurable g (volume.restrict (axisCube z L)) →
        (∀ᵐ x ∂(volume.restrict (axisCube z L)), |f x| ≤ Fb) →
        (∀ᵐ x ∂(volume.restrict (axisCube z L)), eucNorm (g x) ≤ Gb) →
        (∀ k : ℝ, 0 ≤ k → ∀ {η : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
          tsupport η ⊆ axisCube z L →
          ∫ x in axisCube z L, vecDot (matVecMul (a x) (u.grad x)) (levelTest u k η x) =
            (∫ x in axisCube z L, f x * (η x ^ 2 * max (u.toFun x - k) 0)) +
              ∫ x in axisCube z L, vecDot (g x) (levelTest u k η x)) →
        ∀ {M : ℝ}, 0 < M →
          (1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) * L ^ 2 ≤ M ^ 2 →
          C * (Lam / lam) ^ deGiorgiPower d *
            (L ^ (-(d : ℝ) / 2) * (∫ x in axisCube z L, max (u.toFun x) 0 ^ 2) ^ (1 / 2 : ℝ)) ≤ M →
          ∀ᵐ x ∂(volume.restrict (halfCube z L)), u.toFun x ≤ M := by
  obtain ⟨Cs, c, hCs, hc, hstepGen⟩ := deGiorgi_step hd
  have hβ : 0 < 1 - 2 / sobStar d := one_sub_two_div_sobStar_pos hd
  set β : ℝ := 1 - 2 / sobStar d with hβdef
  set K1 : ℝ := 2 * (8 * (d : ℝ) ^ 2 + 4) * (64 * c ^ 2 + 4) + 128 * c ^ 2 with hK1
  have hK1pos : 0 < K1 := by positivity
  set A0 : ℝ := (Cs + 1) * K1 * (4 : ℝ) ^ β with hA0
  have hA0pos : 0 < A0 := by positivity
  set B : ℝ := (4 : ℝ) ^ (1 + β) with hB
  have hC2pos : 0 < (A0 * B ^ (1 / β)) ^ (1 / β) := by positivity
  set Cfin : ℝ := Real.sqrt ((A0 * B ^ (1 / β)) ^ (1 / β)) with hCfin
  have hCfinpos : 0 < Cfin := Real.sqrt_pos.2 hC2pos
  refine ⟨Cfin, hCfinpos, ?_⟩
  intro lam Lam a z L hL hEll u f g Fb Gb hfm hgm hf hg hlevel M hM hM1 hM2
  have hQm : MeasurableSet (axisCube z L) := (isOpen_axisCube z L).measurableSet
  -- ellipticity ratio
  have hx0 : (z + fun _ => L / 2) ∈ axisCube z L := by
    intro j _
    simp only [Set.mem_Ioo, Pi.add_apply]
    constructor <;> linarith only [hL]
  obtain ⟨hlam, hlamLam, -, -⟩ := hEll.2 _ hx0
  have hr1 : 1 ≤ Lam / lam := (one_le_div hlam).2 hlamLam
  have hr0 : 0 < Lam / lam := by linarith only [hr1]
  have hEd : (1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) ≤ M ^ 2 / L ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; exact hM1
  have hstep : ∀ k : ℝ, 0 ≤ k → ∀ s δ : ℝ, 0 ≤ s → 0 < δ →
      ∫ x in subCube z L (s + δ), max (u.toFun x - k) 0 ^ 2 ≤
        stepRhs Cs c d L lam Lam Fb Gb δ (∫ x in subCube z L s, max (u.toFun x - k) 0 ^ 2)
          (volume ({x | k < u.toFun x} ∩ subCube z L s)).toReal :=
    fun k hk s δ hs hδ => hstepGen z hL hEll u f g hfm hgm hf hg k (hlevel k hk) s δ hs hδ
  set X : ℕ → ℝ := fun j => (∫ x in subCube z L (sLev L j), max (u.toFun x - kLev M j) 0 ^ 2) /
    (L ^ (d : ℝ) * M ^ 2) with hX
  have hLd : 0 < L ^ (d : ℝ) := Real.rpow_pos_of_pos hL _
  have hX0 : ∀ n, 0 ≤ X n := fun n => by
    simp only [hX]
    exact div_nonneg (integral_nonneg fun x => sq_nonneg _) (by positivity)
  have hrec : ∀ n : ℕ, X (n + 1) ≤ A0 * (Lam / lam) ^ 2 * ((4 : ℝ) ^ (1 + β)) ^ (n : ℝ) *
      X n ^ (1 + β) := fun n => normalized_recursion hd hL hM hCs hr1 hEd u hstep n
  have hs0 : sLev L 0 = 0 := by simp [sLev]
  have hk0 : kLev M 0 = 0 := by simp [kLev]
  set I : ℝ := ∫ x in axisCube z L, max (u.toFun x) 0 ^ 2 with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  have hX00 : X 0 = I / (L ^ (d : ℝ) * M ^ 2) := by
    simp only [hX, hs0, hk0, subCube_zero, sub_zero, hI]
  have hinit : Real.sqrt ((A0 * ((4 : ℝ) ^ (1 + β)) ^ (1 / β)) ^ (1 / β)) ^ 2 *
      ((Lam / lam) ^ (1 / β)) ^ 2 * X 0 ≤ 1 := by
    set W : ℝ := L ^ (-(d : ℝ) / 2) * I ^ (1 / 2 : ℝ) with hW
    have hW0 : 0 ≤ W := by positivity
    have hN : deGiorgiPower d = 1 / β := by rw [deGiorgiPower, one_div]
    rw [hN] at hM2
    have hprod0 : 0 ≤ Cfin * (Lam / lam) ^ (1 / β) * W := by positivity
    have hsqM : (Cfin * (Lam / lam) ^ (1 / β) * W) ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ hprod0 hM2 2
    have hW2 : W ^ 2 = L ^ (-(d : ℝ)) * I := by
      have e1 : 2 * (-(d : ℝ) / 2) = -(d : ℝ) := by ring
      have e2 : (I ^ (1 / 2 : ℝ)) ^ 2 = I := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hI0]
        norm_num
      rw [hW, mul_pow, rpow_sq_eq hL, e1, e2]
    have hLL : L ^ (-(d : ℝ)) * L ^ (d : ℝ) = 1 := by
      rw [← Real.rpow_add hL]; simp
    have hexp : Cfin ^ 2 * ((Lam / lam) ^ (1 / β)) ^ 2 * (L ^ (-(d : ℝ)) * I) ≤ M ^ 2 := by
      have : (Cfin * (Lam / lam) ^ (1 / β) * W) ^ 2 =
          Cfin ^ 2 * ((Lam / lam) ^ (1 / β)) ^ 2 * (L ^ (-(d : ℝ)) * I) := by
        rw [← hW2]; ring
      linarith only [hsqM, this]
    rw [hX00, ← mul_div_assoc, div_le_one (by positivity)]
    have := mul_le_mul_of_nonneg_right hexp hLd.le
    have e : Cfin ^ 2 * ((Lam / lam) ^ (1 / β)) ^ 2 * (L ^ (-(d : ℝ)) * I) * L ^ (d : ℝ) =
        Cfin ^ 2 * ((Lam / lam) ^ (1 / β)) ^ 2 * I * (L ^ (-(d : ℝ)) * L ^ (d : ℝ)) := by ring
    rw [e, hLL, mul_one] at this
    linarith only [this, mul_comm (M ^ 2) (L ^ (d : ℝ))]
  have hlim : Tendsto X atTop (𝓝 0) := normalized_decay hβ hA0pos hr0 hX0 hrec hinit
  have hq4 : 0 ≤ L / 4 := by positivity
  have hmono4 : volume.restrict (subCube z L (L / 4)) ≤ volume.restrict (axisCube z L) :=
    Measure.restrict_mono (subCube_subset hq4) le_rfl
  have hle : ∀ n, ∫ x in subCube z L (L / 4), max (u.toFun x - M) 0 ^ 2 ≤
      ∫ x in subCube z L (sLev L n), max (u.toFun x - kLev M n) 0 ^ 2 := by
    intro n
    refine (level_mass_anti u (kLev_le hM.le n) hq4).trans ?_
    have hsn : subCube z L (L / 4) ⊆ subCube z L (sLev L n) := subCube_anti (sLev_le hL.le n)
    exact setIntegral_mono_set
      ((integrable_sq_max_sub u (kLev M n)).mono_measure
        (Measure.restrict_mono (subCube_subset (sLev_nonneg hL.le n)) le_rfl))
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hsn hx)
  have hlimA : Tendsto (fun n => ∫ x in subCube z L (sLev L n),
      max (u.toFun x - kLev M n) 0 ^ 2) atTop (𝓝 0) := by
    have := hlim.mul_const (L ^ (d : ℝ) * M ^ 2)
    rw [zero_mul] at this
    refine this.congr fun n => ?_
    simp only [hX]
    field_simp
  have hzero : ∫ x in subCube z L (L / 4), max (u.toFun x - M) 0 ^ 2 ≤ 0 :=
    ge_of_tendsto' hlimA hle
  have heq : ∫ x in subCube z L (L / 4), max (u.toFun x - M) 0 ^ 2 = 0 :=
    le_antisymm hzero (integral_nonneg fun x => sq_nonneg _)
  rw [integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
    ((integrable_sq_max_sub u M).mono_measure hmono4)] at heq
  rw [halfCube_eq_subCube]
  filter_upwards [heq] with x hx
  have h2 : max (u.toFun x - M) 0 ^ 2 = 0 := hx
  have h0 : max (u.toFun x - M) 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1 h2
  linarith only [le_max_left (u.toFun x - M) 0, h0]

theorem aestronglyMeasurable_of_eLpNorm_top_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : eLpNorm f ⊤ μ ≠ ⊤) : AEStronglyMeasurable f μ := by
  by_contra h
  exact hf (eLpNorm_of_not_aestronglyMeasurable h)

theorem ae_abs_le_toReal_eLpNorm_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : eLpNorm f ⊤ μ ≠ ⊤) : ∀ᵐ x ∂μ, |f x| ≤ (eLpNorm f ⊤ μ).toReal := by
  have hfm := aestronglyMeasurable_of_eLpNorm_top_ne_top hf
  have h := enorm_ae_le_eLpNormEssSup f μ
  rw [← eLpNorm_exponent_top hfm] at h
  filter_upwards [h] with x hx
  have := ENNReal.toReal_mono hf hx
  rwa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] at this

theorem memLp_two_max_zero {z : Vec d} {L : ℝ} (u : H1Function (axisCube z L)) :
    MemLp (fun x => max (u.toFun x) 0) 2 (volume.restrict (axisCube z L)) := by
  obtain ⟨v, hv, -⟩ := exists_h1_max_sub_const (isOpenBoundedConvexDomain_axisCube z L) u 0
  have := v.memL2
  rw [hv] at this
  simpa only [sub_zero] using this

/-- **De Giorgi `L^∞–L²` bound with right-hand side (consumer form).**
`sup_{Q/2} u₊ ≤ C (Λ/λ)^N (L^{-d/2} ‖u₊‖_{L²(Q)} + L²/λ ‖f‖_∞ + L/λ ‖g‖_∞)`, with
`N = deGiorgiPower d`, from the level inequalities. -/
theorem deGiorgi_eLpNorm_bound (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {lam Lam : ℝ} {a : CoeffField d} (z : Vec d) {L : ℝ}, 0 < L →
      IsEllipticFieldOn lam Lam (axisCube z L) a →
      ∀ (u : H1Function (axisCube z L)) (f : Vec d → ℝ) (g : Vec d → Vec d),
        AEStronglyMeasurable g (volume.restrict (axisCube z L)) →
        (∀ k : ℝ, 0 ≤ k → ∀ {η : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
          tsupport η ⊆ axisCube z L →
          ∫ x in axisCube z L, vecDot (matVecMul (a x) (u.grad x)) (levelTest u k η x) =
            (∫ x in axisCube z L, f x * (η x ^ 2 * max (u.toFun x - k) 0)) +
              ∫ x in axisCube z L, vecDot (g x) (levelTest u k η x)) →
        eLpNorm (fun x => max (u.toFun x) 0) ⊤ (volume.restrict (halfCube z L)) ≤
          ENNReal.ofReal (C * (Lam / lam) ^ deGiorgiPower d) *
            (ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) *
                eLpNorm (fun x => max (u.toFun x) 0) 2 (volume.restrict (axisCube z L)) +
              ENNReal.ofReal (L ^ 2 / lam) * eLpNorm f ⊤ (volume.restrict (axisCube z L)) +
              ENNReal.ofReal (L / lam) *
                eLpNorm (fun x => eucNorm (g x)) ⊤ (volume.restrict (axisCube z L))) := by
  obtain ⟨C0, hC0, hsup⟩ := deGiorgi_sup_bound hd
  refine ⟨C0 + 1, by positivity, ?_⟩
  intro lam Lam a z L hL hEll u f g hgm hlevel
  have hx0 : (z + fun _ => L / 2) ∈ axisCube z L := by
    intro j _
    simp only [Set.mem_Ioo, Pi.add_apply]
    constructor <;> linarith only [hL]
  obtain ⟨hlam, hlamLam, -, -⟩ := hEll.2 _ hx0
  have hr1 : 1 ≤ Lam / lam := (one_le_div hlam).2 hlamLam
  have hN0 : 0 ≤ deGiorgiPower d := by
    unfold deGiorgiPower
    exact inv_nonneg.2 (one_sub_two_div_sobStar_pos hd).le
  set μ : Measure (Vec d) := volume.restrict (axisCube z L) with hμ
  set Rr : ℝ := (Lam / lam) ^ deGiorgiPower d with hRr
  have hRr1 : 1 ≤ Rr := Real.one_le_rpow hr1 hN0
  set Cc : ℝ := (C0 + 1) * Rr with hCc
  have hCc1 : 1 ≤ Cc := by
    have : (1 : ℝ) ≤ C0 + 1 := by linarith only [hC0]
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (C0 + 1) * Rr := mul_le_mul this hRr1 zero_le_one (by linarith only [hC0])
  have hCcpos : 0 < Cc := by linarith only [hCc1]
  set RHS : ℝ≥0∞ := ENNReal.ofReal Cc * (ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) *
        eLpNorm (fun x => max (u.toFun x) 0) 2 μ + ENNReal.ofReal (L ^ 2 / lam) * eLpNorm f ⊤ μ +
      ENNReal.ofReal (L / lam) * eLpNorm (fun x => eucNorm (g x)) ⊤ μ) with hRHS
  show _ ≤ RHS
  by_cases hR : RHS = ⊤
  · rw [hR]; exact le_top
  have hc0 : ENNReal.ofReal Cc ≠ 0 := (ENNReal.ofReal_pos.2 hCcpos).ne'
  have hsum : (ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) * eLpNorm (fun x => max (u.toFun x) 0) 2 μ +
      ENNReal.ofReal (L ^ 2 / lam) * eLpNorm f ⊤ μ +
        ENNReal.ofReal (L / lam) * eLpNorm (fun x => eucNorm (g x)) ⊤ μ) ≠ ⊤ := by
    intro h
    exact hR (by rw [hRHS, h, ENNReal.mul_top hc0])
  have hs12 := (ENNReal.add_ne_top.1 hsum).1
  have hs3 := (ENNReal.add_ne_top.1 hsum).2
  have hs1 := (ENNReal.add_ne_top.1 hs12).1
  have hs2 := (ENNReal.add_ne_top.1 hs12).2
  have hfin : eLpNorm f ⊤ μ ≠ ⊤ := by
    intro h; apply hs2
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
  have hGfin : eLpNorm (fun x => eucNorm (g x)) ⊤ μ ≠ ⊤ := by
    intro h; apply hs3
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
  have hU : eLpNorm (fun x => max (u.toFun x) 0) 2 μ ≠ ⊤ := (memLp_two_max_zero u).eLpNorm_ne_top
  have hfm : AEStronglyMeasurable f μ := aestronglyMeasurable_of_eLpNorm_top_ne_top hfin
  set Fb : ℝ := (eLpNorm f ⊤ μ).toReal with hFb
  set Gb : ℝ := (eLpNorm (fun x => eucNorm (g x)) ⊤ μ).toReal with hGb
  set Uq : ℝ := (eLpNorm (fun x => max (u.toFun x) 0) 2 μ).toReal with hUq
  have hFb0 : 0 ≤ Fb := ENNReal.toReal_nonneg
  have hGb0 : 0 ≤ Gb := ENNReal.toReal_nonneg
  have hUq0 : 0 ≤ Uq := ENNReal.toReal_nonneg
  have hf : ∀ᵐ x ∂μ, |f x| ≤ Fb := ae_abs_le_toReal_eLpNorm_top hfin
  have hg : ∀ᵐ x ∂μ, eucNorm (g x) ≤ Gb := by
    filter_upwards [ae_abs_le_toReal_eLpNorm_top hGfin] with x hx
    rwa [abs_of_nonneg (eucNorm_nonneg _)] at hx
  have hI : ∫ x in axisCube z L, max (u.toFun x) 0 ^ 2 = Uq ^ 2 :=
    (eLpNorm_two_toReal_sq (memLp_two_max_zero u)).symm
  have hI12 : (∫ x in axisCube z L, max (u.toFun x) 0 ^ 2) ^ (1 / 2 : ℝ) = Uq := by
    rw [hI, ← Real.rpow_natCast, ← Real.rpow_mul hUq0]
    norm_num
  set M0 : ℝ := Cc * (L ^ (-(d : ℝ) / 2) * Uq + L ^ 2 / lam * Fb + L / lam * Gb) with hM0
  have hM00 : 0 ≤ M0 := by positivity
  have hRHS_eq : RHS = ENNReal.ofReal M0 := by
    have e1 : eLpNorm (fun x => max (u.toFun x) 0) 2 μ = ENNReal.ofReal Uq :=
      (ENNReal.ofReal_toReal hU).symm
    have e2 : eLpNorm f ⊤ μ = ENNReal.ofReal Fb := (ENNReal.ofReal_toReal hfin).symm
    have e3 : eLpNorm (fun x => eucNorm (g x)) ⊤ μ = ENNReal.ofReal Gb :=
      (ENNReal.ofReal_toReal hGfin).symm
    rw [hRHS, e1, e2, e3, hM0, ENNReal.ofReal_mul hCcpos.le, ENNReal.ofReal_add (by positivity)
      (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity : 0 ≤ L / lam)]
  have hbound : ∀ ε : ℝ, 0 < ε →
      eLpNorm (fun x => max (u.toFun x) 0) ⊤ (volume.restrict (halfCube z L)) ≤
        ENNReal.ofReal (M0 + ε) := by
    intro ε hε
    have hM : 0 < M0 + ε := by linarith only [hM00, hε]
    have hxy : L / lam * Gb + L ^ 2 / lam * Fb ≤ M0 + ε := by
      have h1 : L / lam * Gb + L ^ 2 / lam * Fb ≤ Cc * (L ^ (-(d : ℝ) / 2) * Uq +
          L ^ 2 / lam * Fb + L / lam * Gb) := by
        have h0 : 0 ≤ L ^ (-(d : ℝ) / 2) * Uq := by positivity
        have h2 : 0 ≤ L / lam * Gb + L ^ 2 / lam * Fb := by positivity
        have := mul_le_mul_of_nonneg_right hCc1 (by positivity : 0 ≤ L ^ (-(d : ℝ) / 2) * Uq +
          L ^ 2 / lam * Fb + L / lam * Gb)
        linarith only [this, h0, h2]
      linarith only [h1, hε]
    have hM1 : (1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) * L ^ 2 ≤ (M0 + ε) ^ 2 := by
      have e : (1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) * L ^ 2 =
          (L / lam * Gb) ^ 2 + (L ^ 2 / lam * Fb) ^ 2 := by field_simp
      have h3 : 0 ≤ L / lam * Gb := by positivity
      have h4 : 0 ≤ L ^ 2 / lam * Fb := by positivity
      have : (L / lam * Gb + L ^ 2 / lam * Fb) ^ 2 ≤ (M0 + ε) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hxy 2
      have h5 : 0 ≤ (L / lam * Gb) * (L ^ 2 / lam * Fb) := mul_nonneg h3 h4
      rw [e]
      linarith only [this, h5]
    have hM2 : C0 * (Lam / lam) ^ deGiorgiPower d *
        (L ^ (-(d : ℝ) / 2) * (∫ x in axisCube z L, max (u.toFun x) 0 ^ 2) ^ (1 / 2 : ℝ)) ≤
        M0 + ε := by
      rw [hI12]
      have h0 : 0 ≤ L ^ (-(d : ℝ) / 2) * Uq := by positivity
      have h1 : C0 * Rr * (L ^ (-(d : ℝ) / 2) * Uq) ≤ Cc * (L ^ (-(d : ℝ) / 2) * Uq) := by
        refine mul_le_mul_of_nonneg_right ?_ h0
        rw [hCc]
        exact mul_le_mul_of_nonneg_right (by linarith only [hC0]) (by linarith only [hRr1])
      have h2 : Cc * (L ^ (-(d : ℝ) / 2) * Uq) ≤ M0 := by
        rw [hM0]
        refine mul_le_mul_of_nonneg_left ?_ hCcpos.le
        have : 0 ≤ L ^ 2 / lam * Fb + L / lam * Gb := by positivity
        linarith only [this]
      linarith only [h1, h2, hε]
    have hae := hsup z hL hEll u f g hfm hgm hf hg hlevel hM hM1 hM2
    have hmeas : AEStronglyMeasurable (fun x => max (u.toFun x) 0)
        (volume.restrict (halfCube z L)) :=
      ((memLp_two_max_zero u).aestronglyMeasurable).mono_measure
        (Measure.restrict_mono (halfCube_subset z L) le_rfl)
    rw [eLpNorm_exponent_top hmeas]
    refine eLpNormEssSup_le_of_ae_bound ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le hx hM.le
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  refine (hbound ε (by exact_mod_cast hε)).trans ?_
  rw [ENNReal.ofReal_add hM00 (by positivity), hRHS_eq, ENNReal.ofReal_coe_nnreal]

/-! ### Satisfiability witnesses

The constant function `1` on the unit square for the identity coefficient field, zero data and
`λ = Λ = 1` meets every non-law hypothesis of the theorems above. -/

theorem witness_ellipticField :
    IsEllipticFieldOn (1 : ℝ) 1 (axisCube (0 : Vec 2) 1) (fun _ => (1 : Mat 2)) :=
  ⟨measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ =>
      Measurable.ite (isOpen_axisCube (0 : Vec 2) 1).measurableSet measurable_const measurable_const,
    fun _ _ => Homogenization.isEllipticMatrix_one_one le_rfl⟩

/-- The constant function one, as an `H¹` function on the unit square. -/
noncomputable def witnessOne : H1Function (axisCube (0 : Vec 2) 1) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_axisCube (0 : Vec 2) 1) (f := fun _ => (1 : ℝ)) contDiff_const

theorem witnessOne_grad (x : Vec 2) : witnessOne.grad x = 0 := by
  funext i
  simp [witnessOne, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain]

theorem witnessOne_weak :
    IsWeakSolutionOn (fun _ => (1 : Mat 2)) (axisCube (0 : Vec 2) 1) witnessOne (fun _ => 0)
      (fun _ => 0) := by
  intro φ
  simp [witnessOne_grad, vecDot, matVecMul]

theorem witnessOne_level (k : ℝ) {η : Vec 2 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ axisCube (0 : Vec 2) 1) :
    ∫ x in axisCube (0 : Vec 2) 1, vecDot (matVecMul ((fun _ => (1 : Mat 2)) x)
        (witnessOne.grad x)) (levelTest witnessOne k η x) =
      (∫ x in axisCube (0 : Vec 2) 1, (fun _ => (0 : ℝ)) x *
        (η x ^ 2 * max (witnessOne.toFun x - k) 0)) +
        ∫ x in axisCube (0 : Vec 2) 1, vecDot ((fun _ => (0 : Vec 2)) x)
          (levelTest witnessOne k η x) :=
  level_inequality_of_isWeakSolutionOn (a := fun _ => (1 : Mat 2)) (0 : Vec 2) witnessOne
    (fun _ => 0) (fun _ => 0) witnessOne_weak k hη hηc hηs

/-- Witness for `deGiorgi_eLpNorm_bound`. -/
example : True := by
  obtain ⟨C, -, hmain⟩ := deGiorgi_eLpNorm_bound (d := 2) le_rfl
  have := hmain (lam := 1) (Lam := 1) (a := fun _ => (1 : Mat 2)) (0 : Vec 2) one_pos
    witness_ellipticField witnessOne (fun _ => 0) (fun _ => 0) aestronglyMeasurable_const
    fun k _ _ hη hηc hηs => witnessOne_level k hη hηc hηs
  trivial

/-- Witness for `deGiorgi_sup_bound`, with a level `M` meeting both lower bounds. -/
example : True := by
  obtain ⟨C, -, hmain⟩ := deGiorgi_sup_bound (d := 2) le_rfl
  set X : ℝ := C * ((1 : ℝ) / 1) ^ deGiorgiPower 2 *
    ((1 : ℝ) ^ (-((2 : ℕ) : ℝ) / 2) * (∫ x in axisCube (0 : Vec 2) 1,
      max (witnessOne.toFun x) 0 ^ 2) ^ (1 / 2 : ℝ)) with hX
  have := hmain (lam := 1) (Lam := 1) (a := fun _ => (1 : Mat 2)) (0 : Vec 2) one_pos
    witness_ellipticField witnessOne (fun _ => 0) (fun _ => 0) (Fb := 0) (Gb := 0)
    aestronglyMeasurable_const aestronglyMeasurable_const
    (Filter.Eventually.of_forall fun _ => by simp)
    (Filter.Eventually.of_forall fun _ => by simp [eucNorm, vecNormSq, vecDot])
    (fun k _ _ hη hηc hηs => witnessOne_level k hη hηc hηs) (M := |X| + 1)
    (by positivity) (by simp; positivity) (by rw [← hX]; linarith only [le_abs_self X])
  trivial

/-- Witness for `normalized_decay`: the zero sequence. -/
example : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) :=
  normalized_decay (β := 1) (A0 := 1) (r := 1) one_pos one_pos one_pos (fun _ => le_rfl)
    (fun n => by simp) (by simp)

/-- Witness for `sobolev_holder_sq` and `exists_cube_cutoff`. -/
example : True := by
  obtain ⟨C, -, h⟩ := sobolev_holder_sq (d := 2) le_rfl
  have := h (0 : Vec 2) 1 one_pos 0 ∅ (Set.empty_subset _) (by
    intro x hx
    exact (hx rfl).elim)
  obtain ⟨c, -, hc⟩ := exists_cube_cutoff 2
  have := hc (0 : Vec 2) 1 (1 / 4) (by norm_num)
  trivial

end SuperdiffusionCLT.Section7
