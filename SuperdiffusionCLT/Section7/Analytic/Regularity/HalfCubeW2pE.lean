/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.HalfCubeW2pD

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Half cube: one Neumann step and the Hessian of the series

The `L̲²` contraction of the Neumann iteration, the Jacobian of the perturbation datum
`(A - 1) ∇v`, the step estimate (`hc_step_exists`), and the weak Hessian of a geometrically
convergent series of `H¹₀` functions (`hc_hessian_of_series`), all on the half cube.
-/

namespace SuperdiffusionCLT.Section7

open SuperdiffusionCLT.Sobolev

variable {d : ℕ}

theorem hc_l2_tendsto_of_contraction [NeZero d] (e : Fin d) (m : ℤ) {A : CoeffField d}
    (hA : ∀ i j, Continuous (fun x => A x i j))
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ x ∈ flatHalfCube e m, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε)
    {C₂ : ℝ}
    (hC₂ : ∀ f : Vec d → Vec d, MemLp f 2 (flatHalfMeasure e m) →
      ∀ u : H10Function (flatHalfCube e m), HalfDivProblem e m u f →
        MemLp u.toH1Function.grad 2 (flatHalfMeasure e m) ∧
          flatHalfNorm e m 2 u.toH1Function.grad ≤ C₂ * flatHalfNorm e m 2 f)
    (hC₂0 : 0 ≤ C₂) (hcontr : C₂ * (d * ε) ≤ 1 / 2)
    {G : Vec d → Vec d} (hG2 : MemLp G 2 (flatHalfMeasure e m))
    {w : H10Function (flatHalfCube e m)} (s : ℕ → H10Function (flatHalfCube e m))
    (hw : HalfDivProblem e m w (fun x => G x + pert A w.toH1Function.grad x))
    (hs : ∀ n, HalfDivProblem e m (s (n + 1))
      (fun x => G x + pert A (s n).toH1Function.grad x)) :
    Tendsto (fun n => eLpNorm (fun x => (s n).toH1Function.grad x - w.toH1Function.grad x) 2
      (flatHalfMeasure e m)) atTop (𝓝 0) := by
  have hpert2 : ∀ F : Vec d → Vec d, MemLp F 2 (flatHalfMeasure e m) →
      MemLp (pert A F) 2 (flatHalfMeasure e m) ∧
        flatHalfNorm e m 2 (pert A F) ≤ d * ε * flatHalfNorm e m 2 F :=
    fun F hF => hc_memLp_pert_and_norm_le e m hA hε0 hε hF
  have hfun : ∀ n, (fun x => (G x + pert A w.toH1Function.grad x) -
      (G x + pert A (s n).toH1Function.grad x)) =
      pert A (w - s n).toH1Function.grad := by
    intro n
    funext x
    simp only [pert, hc_grad_sub, matVecMul_sub_right]
    abel
  have hrec : ∀ n, HalfDivProblem e m (w - s (n + 1))
      (pert A (w - s n).toH1Function.grad) := by
    intro n
    have m1 : MemLp (fun x => G x + pert A w.toH1Function.grad x) 2 (flatHalfMeasure e m) :=
      hG2.add (hpert2 _ (hc_gradL2 e m w)).1
    have m2 : MemLp (fun x => G x + pert A (s n).toH1Function.grad x) 2
        (flatHalfMeasure e m) := hG2.add (hpert2 _ (hc_gradL2 e m (s n))).1
    have := hc_problem_sub m1 m2 hw (hs n)
    rwa [hfun] at this
  set a : ℕ → ℝ := fun n => flatHalfNorm e m 2 (w - s n).toH1Function.grad with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => ENNReal.toReal_nonneg
  have hstep : ∀ n, a (n + 1) ≤ 1 / 2 * a n := by
    intro n
    have h1 := (hC₂ _ (hpert2 _ (hc_gradL2 e m (w - s n))).1 (w - s (n + 1))
      (hrec n)).2
    have h2 := (hpert2 _ (hc_gradL2 e m (w - s n))).2
    have h3 : C₂ * flatHalfNorm e m 2 (pert A (w - s n).toH1Function.grad) ≤ C₂ * (d * ε * a n) :=
      mul_le_mul_of_nonneg_left h2 hC₂0
    have h4 : C₂ * (d * ε * a n) ≤ 1 / 2 * a n := by
      calc C₂ * (d * ε * a n) = (C₂ * (d * ε)) * a n := by ring
        _ ≤ 1 / 2 * a n := mul_le_mul_of_nonneg_right hcontr (ha0 n)
    exact le_trans h1 (le_trans h3 h4)
  have hgeo : ∀ n, a n ≤ (1 / 2) ^ n * a 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc a (n + 1) ≤ 1 / 2 * a n := hstep n
        _ ≤ 1 / 2 * ((1 / 2) ^ n * a 0) := by gcongr
        _ = (1 / 2) ^ (n + 1) * a 0 := by ring
  have hlim : Tendsto a atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * a 0) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).mul_const (a 0)
    exact squeeze_zero ha0 hgeo h0
  have hnorm : ∀ n, eLpNorm (fun x => (s n).toH1Function.grad x - w.toH1Function.grad x) 2
      (flatHalfMeasure e m) = ENNReal.ofReal (a n) := by
    intro n
    have hm := hc_gradL2 e m (w - s n)
    have : (fun x => (s n).toH1Function.grad x - w.toH1Function.grad x) =
        -(fun x => w.toH1Function.grad x - (s n).toH1Function.grad x) := by
      funext x
      simp
    rw [this, eLpNorm_neg, ha]
    simp only [hc_grad_sub]
    exact (ENNReal.ofReal_toReal (by simpa only [hc_grad_sub] using hm.eLpNorm_lt_top.ne)).symm
  simp_rw [hnorm]
  simpa using ENNReal.tendsto_ofReal hlim

theorem hc_aesm_jac (e : Fin d) (m : ℤ) {A : CoeffField d}
    (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) {g : Vec d → Vec d}
    {h : Fin d → Fin d → Vec d → ℝ} (hg : AEStronglyMeasurable g (flatHalfMeasure e m))
    (hh : ∀ i j, AEStronglyMeasurable (h i j) (flatHalfMeasure e m)) :
    AEStronglyMeasurable (jacobianHilbertMat (flatPertJac A g h)) (flatHalfMeasure e m) := by
  have hentry : ∀ i k, AEStronglyMeasurable (fun x => flatPertJac A g h i x k)
      (flatHalfMeasure e m) := by
    intro i k
    refine (Finset.univ : Finset (Fin d)).aestronglyMeasurable_fun_sum fun l _ => ?_
    have c1 : Continuous (fun x => A x i l - (1 : Mat d) i l) :=
      ((hA i l).continuous).sub continuous_const
    have c2 : Continuous (fun x => fderiv ℝ (fun y => A y i l) x (basisVec k)) :=
      ((hA i l).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have g1 : AEStronglyMeasurable (fun x => g x l) (flatHalfMeasure e m) :=
      (continuous_apply l).comp_aestronglyMeasurable hg
    exact (c1.aestronglyMeasurable.mul (hh l k)).add (g1.mul c2.aestronglyMeasurable)
  have hmat' : AEStronglyMeasurable
      (fun x => (fun i k => flatPertJac A g h i x k : Fin d → Fin d → ℝ))
      (flatHalfMeasure e m) :=
    AEMeasurable.aestronglyMeasurable (aemeasurable_pi_iff.2 fun i =>
      aemeasurable_pi_iff.2 fun k => (hentry i k).aemeasurable)
  have hmat : AEStronglyMeasurable (fun x => (fun i k => flatPertJac A g h i x k : Mat d))
      (flatHalfMeasure e m) := hmat'
  exact (HilbertMat.continuousLinearEquivMat d).symm.continuous.comp_aestronglyMeasurable hmat

theorem hc_jac_memLp_norm_le [NeZero d] (e : Fin d) (m : ℤ) {A : CoeffField d} {ε K : ℝ}
    (hε0 : 0 ≤ ε) (hK0 : 0 ≤ K) (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j))
    (hAε : ∀ x ∈ flatHalfCube e m, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε)
    (hAK : ∀ x ∈ flatHalfCube e m, ∀ i j k, |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {g : Vec d → Vec d} {h : Fin d → Fin d → Vec d → ℝ}
    (hg : MemLp g q (flatHalfMeasure e m))
    (hH : MemLp (fun x => HilbertMat.ofMat (fun i j => h i j x)) q (flatHalfMeasure e m)) :
    MemLp (jacobianHilbertMat (flatPertJac A g h)) q (flatHalfMeasure e m) ∧
      flatHalfNorm e m q (jacobianHilbertMat (flatPertJac A g h)) ≤
        (d : ℝ) ^ 3 * ε * flatHalfNorm e m q (fun x => HilbertMat.ofMat (fun i j => h i j x)) +
          (d : ℝ) ^ 3 * K * flatHalfNorm e m q g := by
  have hhm : ∀ i j, AEStronglyMeasurable (h i j) (flatHalfMeasure e m) := by
    intro i j
    have := (HilbertMat.entryL i j).continuous.comp_aestronglyMeasurable hH.aestronglyMeasurable
    simpa [Function.comp_def] using this
  have hJm := hc_aesm_jac e m hA hg.aestronglyMeasurable hhm
  have hd0 : (0 : ℝ) ≤ (d : ℝ) ^ 3 := by positivity
  set c₁ : ℝ := (d : ℝ) ^ 3 * ε with hc₁
  set c₂ : ℝ := (d : ℝ) ^ 3 * K with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  set Φ₁ : Vec d → ℝ := fun x => c₁ * ‖HilbertMat.ofMat (fun i j => h i j x)‖ with hΦ₁def
  set Φ₂ : Vec d → ℝ := fun x => c₂ * ‖g x‖ with hΦ₂def
  have hΦ₁ : MemLp Φ₁ q (flatHalfMeasure e m) := hH.norm.const_mul c₁
  have hΦ₂ : MemLp Φ₂ q (flatHalfMeasure e m) := hg.norm.const_mul c₂
  have hbd : ∀ᵐ x ∂(flatHalfMeasure e m),
      ‖jacobianHilbertMat (flatPertJac A g h) x‖ ≤ ‖(Φ₁ + Φ₂) x‖ := by
    filter_upwards [hc_ae_mem e m] with x hx
    have := flatW2p_norm_jac_le (g := g) (h := h) (hAε x hx) (hAK x hx)
    have hnn : 0 ≤ (Φ₁ + Φ₂) x := by simp only [Pi.add_apply, hΦ₁def, hΦ₂def]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc _ ≤ _ := this
      _ = (Φ₁ + Φ₂) x := by simp only [Pi.add_apply, hΦ₁def, hΦ₂def, hc₁, hc₂]; ring
  have hmem := (hΦ₁.add hΦ₂).mono hJm hbd
  refine ⟨hmem, ?_⟩
  have h1 : eLpNorm (jacobianHilbertMat (flatPertJac A g h)) q (flatHalfMeasure e m) ≤
      eLpNorm Φ₁ q (flatHalfMeasure e m) + eLpNorm Φ₂ q (flatHalfMeasure e m) :=
    (eLpNorm_mono_ae hJm hbd).trans
      (eLpNorm_add_le hq)
  have e1 : eLpNorm Φ₁ q (flatHalfMeasure e m) = ENNReal.ofReal c₁ *
      eLpNorm (fun x => HilbertMat.ofMat (fun i j => h i j x)) q (flatHalfMeasure e m) := by
    have : Φ₁ = c₁ • fun x => ‖HilbertMat.ofMat (fun i j => h i j x)‖ := rfl
    rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal hc₁0]
    congr 1
    exact eLpNorm_norm _ hH.aestronglyMeasurable
  have e2 : eLpNorm Φ₂ q (flatHalfMeasure e m) = ENNReal.ofReal c₂ *
      eLpNorm g q (flatHalfMeasure e m) := by
    have : Φ₂ = c₂ • fun x => ‖g x‖ := rfl
    rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal hc₂0]
    congr 1
    exact eLpNorm_norm _ hg.aestronglyMeasurable
  rw [e1, e2] at h1
  have hfin : ENNReal.ofReal c₁ * eLpNorm (fun x => HilbertMat.ofMat (fun i j => h i j x)) q
        (flatHalfMeasure e m) + ENNReal.ofReal c₂ * eLpNorm g q (flatHalfMeasure e m) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH.eLpNorm_lt_top.ne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_lt_top.ne⟩
  have h2 := ENNReal.toReal_mono hfin h1
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH.eLpNorm_lt_top.ne)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_lt_top.ne), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₁0, ENNReal.toReal_ofReal hc₂0] at h2
  exact h2

/-- The step estimate for the Neumann iteration on the half cube: the response to
`(A - 1) ∇v`. -/
theorem hc_step_exists (hd : 2 ≤ d) (e : Fin d) {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hpt : p < ⊤) :
    ∃ Cg Ch : ℝ, 0 < Cg ∧ 0 < Ch ∧
      ∀ (m : ℤ) (A : CoeffField d) (ε K : ℝ), 0 ≤ ε → 0 ≤ K →
        (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) →
        (∀ x ∈ flatHalfCube e m, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε) →
        (∀ x ∈ flatHalfCube e m, ∀ i j k,
          |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K) →
        ∀ (v : H10Function (flatHalfCube e m))
          (Hv : HasWeakHessianOn (flatHalfCube e m) v.toH1Function),
          MemLp v.toH1Function.grad p (flatHalfMeasure e m) →
          MemLp (flatHessMat Hv) p (flatHalfMeasure e m) →
          ∃ (y : H10Function (flatHalfCube e m))
            (Hy : HasWeakHessianOn (flatHalfCube e m) y.toH1Function),
            HalfDivProblem e m y (pert A v.toH1Function.grad) ∧
            MemLp y.toH1Function.grad p (flatHalfMeasure e m) ∧
            MemLp (flatHessMat Hy) p (flatHalfMeasure e m) ∧
            flatHalfNorm e m p y.toH1Function.grad ≤
              Cg * ((d : ℝ) * ε * flatHalfNorm e m p v.toH1Function.grad) ∧
            flatHalfNorm e m p (flatHessMat Hy) ≤
              Ch * ((d : ℝ) ^ 3 * ε * flatHalfNorm e m p (flatHessMat Hv) +
                (d : ℝ) ^ 3 * K * flatHalfNorm e m p v.toH1Function.grad) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Cg, Ch, hCg, hCh, hbase⟩ := hc_base_div hd e hp2 hpt
  refine ⟨Cg, Ch, hCg, hCh, ?_⟩
  intro m A ε K hε0 hK0 hA hAε hAK v Hv hvg hvH
  have hAc : ∀ i j, Continuous (fun x => A x i j) := fun i j => (hA i j).continuous
  obtain ⟨hPp, hPn⟩ := hc_memLp_pert_and_norm_le e m hAc hε0 hAε hvg
  have hJ := hc_jac_memLp_norm_le e m hε0 hK0 hA hAε hAK (le_trans (by norm_num) hp2) hvg hvH
  have hweak := flatW2p_hasWeakJacobian_pert (measurableSet_flatHalfCube e m) hA hAε hAK Hv
  obtain ⟨y, Hy, hy, hgy, hHy, hgb, hHb⟩ := hbase m (pert A v.toH1Function.grad)
    (flatPertJac A v.toH1Function.grad Hv.hess) hPp hweak hJ.1
  refine ⟨y, Hy, hy, hgy, hHy, ?_, ?_⟩
  · calc flatHalfNorm e m p y.toH1Function.grad
        ≤ Cg * flatHalfNorm e m p (pert A v.toH1Function.grad) := hgb
      _ ≤ Cg * ((d : ℝ) * ε * flatHalfNorm e m p v.toH1Function.grad) :=
          mul_le_mul_of_nonneg_left hPn hCg.le
  · calc flatHalfNorm e m p (flatHessMat Hy)
        ≤ Ch * flatHalfNorm e m p (jacobianHilbertMat (flatPertJac A v.toH1Function.grad Hv.hess)) :=
          hHb
      _ ≤ Ch * ((d : ℝ) ^ 3 * ε * flatHalfNorm e m p (flatHessMat Hv) +
            (d : ℝ) ^ 3 * K * flatHalfNorm e m p v.toH1Function.grad) :=
          mul_le_mul_of_nonneg_left hJ.2 hCh.le

theorem eLpNorm_restrict_flatHalf (e : Fin d) (m : ℤ) (f : Vec d → ℝ) (p : ℝ≥0∞) :
    eLpNorm f p (volume.restrict (flatHalfCube e m)) =
      ENNReal.ofReal ((cubeVolume (originCube d m)) ^ p.toReal⁻¹) *
        eLpNorm f p (flatHalfMeasure e m) := by
  have hV : 0 < cubeVolume (originCube d m) := cubeVolume_pos _
  have h : volume.restrict (flatHalfCube e m) =
      ENNReal.ofReal (cubeVolume (originCube d m)) • flatHalfMeasure e m := by
    rw [flatHalfMeasure_eq, smul_smul, ← ENNReal.ofReal_mul hV.le,
      mul_inv_cancel₀ hV.ne', ENNReal.ofReal_one, one_smul]
  rw [h]
  exact eLpNorm_ofReal_smul hV f p _

theorem flatHalfMeasure_univ_le_one (e : Fin d) (m : ℤ) : flatHalfMeasure e m Set.univ ≤ 1 := by
  have : flatHalfMeasure e m Set.univ ≤ normalizedCubeMeasure (originCube d m) Set.univ :=
    flatHalfMeasure_le e m _
  rwa [normalizedCubeMeasure_apply_univ] at this

/-- `L̲²` closeness in terms of `L̲^p` closeness on the half cube. -/
theorem hc_restrict_two_le (e : Fin d) (m : ℤ) {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hpt : p < ⊤)
    {E : Type*} [NormedAddCommGroup E] {F : Vec d → ℝ} {Φ : Vec d → E}
    (hF : AEStronglyMeasurable F (flatHalfMeasure e m)) (hΦ : AEStronglyMeasurable Φ (flatHalfMeasure e m))
    (hle : ∀ y, ‖F y‖ ≤ ‖Φ y‖) :
    eLpNorm F 2 (volume.restrict (flatHalfCube e m)) ≤
      ENNReal.ofReal ((cubeVolume (originCube d m)) ^ (2 : ℝ≥0∞).toReal⁻¹) *
        eLpNorm Φ p (flatHalfMeasure e m) := by
  rw [eLpNorm_restrict_flatHalf]
  gcongr
  calc eLpNorm F 2 (flatHalfMeasure e m) ≤ eLpNorm Φ 2 (flatHalfMeasure e m) :=
        eLpNorm_mono_ae hF (Filter.Eventually.of_forall hle)
    _ ≤ eLpNorm Φ p (flatHalfMeasure e m) * flatHalfMeasure e m Set.univ ^
          (1 / (2 : ℝ≥0∞).toReal - 1 / p.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp2 hΦ
    _ ≤ eLpNorm Φ p (flatHalfMeasure e m) * 1 := by
        gcongr
        refine ENNReal.rpow_le_one (flatHalfMeasure_univ_le_one e m) ?_
        have h2 : (2 : ℝ) ≤ p.toReal := by
          have := ENNReal.toReal_mono hpt.ne hp2
          simpa using this
        have : 1 / p.toReal ≤ 1 / (2 : ℝ) := one_div_le_one_div_of_le (by norm_num) h2
        simp only [ENNReal.toReal_ofNat]
        linarith only [this]
    _ = _ := mul_one _

/-- **Hessian from the series.** -/
theorem hc_hessian_of_series [NeZero d] (e : Fin d) (m : ℤ) {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hpt : p < ⊤)
    (x : ℕ → H10Function (flatHalfCube e m))
    (Hx : ∀ n, HasWeakHessianOn (flatHalfCube e m) (x n).toH1Function)
    (hHp : ∀ n, MemLp (flatHessMat (Hx n)) p (flatHalfMeasure e m)) {Bq : ℝ}
    (hHb : ∀ n, flatHalfNorm e m p (flatHessMat (Hx n)) ≤ Bq * (1 / 2) ^ n)
    (w : H10Function (flatHalfCube e m))
    (hgrad : Tendsto (fun n => eLpNorm (fun y => (flatPartialSum x n).toH1Function.grad y -
      w.toH1Function.grad y) 2 (flatHalfMeasure e m)) atTop (𝓝 0)) :
    ∃ H : HasWeakHessianOn (flatHalfCube e m) w.toH1Function,
      MemLp (flatHessMat H) p (flatHalfMeasure e m) ∧
        flatHalfNorm e m p (flatHessMat H) ≤ 2 * Bq := by
  have hBq : 0 ≤ Bq := by
    have := hHb 0
    have h0 : 0 ≤ flatHalfNorm e m p (flatHessMat (Hx 0)) := ENNReal.toReal_nonneg
    simpa using h0.trans this
  have hB : ∀ n, eLpNorm (flatHessMat (Hx n)) p (flatHalfMeasure e m) ≤
      ENNReal.ofReal (Bq * (1 / 2) ^ n) := fun n =>
    (ENNReal.le_ofReal_iff_toReal_le (hHp n).eLpNorm_lt_top.ne (by positivity)).2 (hHb n)
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp2
  obtain ⟨F₀, hF₀, hF₀n, hlim⟩ := flatW2p_exists_limit (μ := flatHalfMeasure e m) hp1
    (fun n => flatHessMat (Hx n)) hHp hBq hB
  have hF₀2 : MemLp F₀ 2 (flatHalfMeasure e m) := hF₀.mono_exponent hp2
  have hent : ∀ i j, MemLp (fun y => HilbertMat.toMat (F₀ y) i j) 2 (flatHalfMeasure e m) := by
    intro i j
    refine hF₀2.norm.mono ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((HilbertMat.entryL i j).continuous.comp_aestronglyMeasurable
        hF₀2.aestronglyMeasurable)
    · have := abs_hess_le_norm F₀ i j y
      simpa [Real.norm_eq_abs] using this
  have hentry_le : ∀ (M : HilbertMat d) (i j : Fin d), |HilbertMat.entryL i j M| ≤ ‖M‖ := by
    intro M i j
    have := abs_hess_le_norm (fun _ => M) i j 0
    simpa using this
  have hweak : ∀ i j, HasWeakPartialDerivOn (flatHalfCube e m) j
      (fun y => w.toH1Function.grad y i) (fun y => HilbertMat.toMat (F₀ y) i j) := by
    intro i j
    have hgm : ∀ n, AEStronglyMeasurable (fun y => (flatPartialSum x n).toH1Function.grad y -
        w.toH1Function.grad y) (flatHalfMeasure e m) := fun n =>
      ((hc_gradL2 e m (flatPartialSum x n)).sub (hc_gradL2 e m w)).aestronglyMeasurable
    refine HasWeakPartialDerivOn.of_tendsto_eLpNorm_two
      (u_n := fun n y => (flatPartialSum x n).toH1Function.grad y i)
      (g_n := fun n y => ∑ k ∈ Finset.range (n + 1), (Hx k).hess i j y)
      (w.toH1Function.gradMemL2 i) ((memLp_flatHalfMeasure_iff e m).1 (hent i j))
      (fun n => (flatPartialSum x n).toH1Function.gradMemL2 i)
      (fun n => memLp_finsetSum _ fun k _ => (Hx k).hess_memL2 i j)
      (fun n => flatPartialSum_weak x Hx i j n) ?_ ?_
    · have hc : Tendsto (fun n => ENNReal.ofReal ((cubeVolume (originCube d m)) ^
          (2 : ℝ≥0∞).toReal⁻¹) * eLpNorm (fun y => (flatPartialSum x n).toH1Function.grad y -
            w.toH1Function.grad y) 2 (flatHalfMeasure e m)) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul hgrad (Or.inr ENNReal.ofReal_ne_top)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
        (fun _ => bot_le) (fun n => ?_)
      refine hc_restrict_two_le e m (le_refl _) (by norm_num) ?_
        ((hc_gradL2 e m (flatPartialSum x n)).sub (hc_gradL2 e m w)).aestronglyMeasurable
        (fun y => ?_)
      · exact ((continuous_apply i).comp_aestronglyMeasurable
          ((hc_gradL2 e m (flatPartialSum x n)).sub (hc_gradL2 e m w)).aestronglyMeasurable)
      · have := norm_le_pi_norm ((flatPartialSum x n).toH1Function.grad y -
          w.toH1Function.grad y) i
        simpa using this
    · have hRm : ∀ n, AEStronglyMeasurable ((∑ k ∈ Finset.range (n + 1), flatHessMat (Hx k)) - F₀)
          (flatHalfMeasure e m) := fun n =>
        ((memLp_finsetSum' _ fun k _ => hHp k).sub hF₀).aestronglyMeasurable
      have hc : Tendsto (fun n => ENNReal.ofReal ((cubeVolume (originCube d m)) ^
          (2 : ℝ≥0∞).toReal⁻¹) * eLpNorm ((∑ k ∈ Finset.range (n + 1), flatHessMat (Hx k)) - F₀)
            p (flatHalfMeasure e m)) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofReal_ne_top)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
        (fun _ => bot_le) (fun n => ?_)
      have hform : ∀ y, (∑ k ∈ Finset.range (n + 1), (Hx k).hess i j y) -
          HilbertMat.toMat (F₀ y) i j =
          HilbertMat.entryL i j (((∑ k ∈ Finset.range (n + 1), flatHessMat (Hx k)) - F₀) y) := by
        intro y
        simp [Finset.sum_apply, flatHessMat]
      have hFm : AEStronglyMeasurable (fun y => (∑ k ∈ Finset.range (n + 1), (Hx k).hess i j y) -
          HilbertMat.toMat (F₀ y) i j) (flatHalfMeasure e m) := by
        have := (HilbertMat.entryL i j).continuous.comp_aestronglyMeasurable (hRm n)
        refine this.congr (Filter.Eventually.of_forall fun y => ?_)
        exact (hform y).symm
      refine hc_restrict_two_le e m hp2 hpt hFm (hRm n) (fun y => ?_)
      rw [hform y]
      exact hentry_le _ i j
  refine ⟨{ hess := fun i j y => HilbertMat.toMat (F₀ y) i j
            hess_memL2 := fun i j => by
              simpa [MemScalarL2, volumeMeasureOn] using (memLp_flatHalfMeasure_iff e m).1 (hent i j)
            weak_second := hweak }, ?_⟩
  have hfm : flatHessMat (HasWeakHessianOn.mk (fun i j y => HilbertMat.toMat (F₀ y) i j)
      (fun i j => by
        simpa [MemScalarL2, volumeMeasureOn] using (memLp_flatHalfMeasure_iff e m).1 (hent i j))
      hweak) = F₀ := by
    funext y
    simp [flatHessMat]
  rw [hfm]
  refine ⟨hF₀, ?_⟩
  unfold flatHalfNorm
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hF₀n).trans
    (by rw [ENNReal.toReal_ofReal (by positivity)])

end SuperdiffusionCLT.Section7
