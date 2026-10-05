/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.HalfCubeW2pF

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Flat `W^{2,p}` on the half cube: the scalar form and satisfiability

`-∇·(A∇w) = F` with `F ∈ L̲^p`, `p > 2`, on the half cube.  The scalar datum is replaced by
`∇·∇ψ` for the Laplace response `ψ` of `F` on the half cube, built by odd reflection.  The
witnesses exhibit the hypotheses with `A = 1`, `K = 0`, zero datum and `w = 0`.
-/

namespace SuperdiffusionCLT.Section7

open SuperdiffusionCLT.Sobolev

variable {d : ℕ}

theorem hc_exists_poisson [NeZero d] (e : Fin d) (m : ℤ) {F : Vec d → ℝ}
    (hF2 : MemLp F 2 (volume.restrict (flatHalfCube e m))) :
    ∃ y : H10Function (flatHalfCube e m), ∀ φ : H10Function (flatHalfCube e m),
      ∫ x in flatHalfCube e m, vecDot (y.toH1Function.grad x) (φ.toH1Function.grad x) =
        ∫ x in flatHalfCube e m, F x * φ.toH1Function.toFun x := by
  obtain ⟨y, hy⟩ := exists_h10_weak_solution (a := fun _ => (1 : Mat d)) (f := F)
    (g := fun _ => (0 : Vec d)) (isOpen_flatHalfCube e m) (isBoundedDomain_flatHalfCube e m)
    (flatHalfCube_nonempty e m)
    (Section5.isEllipticFieldOn_one (measurableSet_flatHalfCube e m)) hF2 (by simp [MemVectorL2, volumeMeasureOn])
  refine ⟨y, fun φ => ?_⟩
  have := hy φ
  simpa [matVecMul_one_left, vecDot_zero_left] using this

theorem eLpNorm_flatHalf_mono_exponent (e : Fin d) (m : ℤ) {F : Vec d → ℝ} {r p : ℝ≥0∞}
    (hr0 : 0 < r) (hrp : r ≤ p) (hpt : p ≠ ⊤) (hF : AEStronglyMeasurable F (flatHalfMeasure e m)) :
    eLpNorm F r (flatHalfMeasure e m) ≤ eLpNorm F p (flatHalfMeasure e m) := by
  calc eLpNorm F r (flatHalfMeasure e m) ≤ eLpNorm F p (flatHalfMeasure e m) *
        flatHalfMeasure e m Set.univ ^ (1 / r.toReal - 1 / p.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hrp hF
    _ ≤ eLpNorm F p (flatHalfMeasure e m) * 1 := by
        gcongr
        refine ENNReal.rpow_le_one (flatHalfMeasure_univ_le_one e m) ?_
        have h2 : r.toReal ≤ p.toReal := ENNReal.toReal_mono hpt hrp
        have h3 : 0 < r.toReal := ENNReal.toReal_pos hr0.ne' (ne_top_of_le_ne_top hpt hrp)
        have : 1 / p.toReal ≤ 1 / r.toReal := one_div_le_one_div_of_le h3 h2
        linarith only [this]
    _ = _ := mul_one _

/-- The Laplace response on the half cube of a scalar datum, by odd reflection: weak Hessian in
`L̲^p` and the Sobolev gradient bound. -/
theorem hc_base_scalar (hd : 2 ≤ d) (e : Fin d) {p : ℝ≥0∞} (hp2 : 2 < p) (hpt : p < ⊤) :
    ∃ Cs Ch : ℝ, 0 < Cs ∧ 0 < Ch ∧ ∀ (m : ℤ) (F : Vec d → ℝ), MemLp F p (flatHalfMeasure e m) →
      ∃ (ψ : H10Function (flatHalfCube e m))
        (Hψ : HasWeakHessianOn (flatHalfCube e m) ψ.toH1Function),
        (∀ φ : H10Function (flatHalfCube e m),
          ∫ x in flatHalfCube e m, vecDot (ψ.toH1Function.grad x) (φ.toH1Function.grad x) =
            ∫ x in flatHalfCube e m, F x * φ.toH1Function.toFun x) ∧
        MemLp ψ.toH1Function.grad p (flatHalfMeasure e m) ∧
        MemLp (flatHessMat Hψ) p (flatHalfMeasure e m) ∧
        flatHalfNorm e m p ψ.toH1Function.grad ≤
          Cs * cubeScaleFactor (originCube d m) * flatHalfNorm e m p F ∧
        flatHalfNorm e m p (flatHessMat Hψ) ≤ Ch * flatHalfNorm e m p F := by
  have : NeZero d := ⟨by omega⟩
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp2.le
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp1.le).ne'
  have hpt' : p ≠ ⊤ := hpt.ne
  have hP2 : 2 < p.toReal := by
    have := (ENNReal.toReal_lt_toReal (by norm_num) hpt.ne).2 hp2
    simpa using this
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = p.toReal := ⟨_, rfl⟩
  rw [← hPdef] at hP2
  obtain ⟨rr, hrrdef⟩ : ∃ rr : ℝ, rr = d * P / (d + P) := ⟨_, rfl⟩
  have hr1 : 1 < rr := by
    rw [hrrdef, lt_div_iff₀ (by positivity)]; nlinarith only [hd2, hP2]
  have hrd : rr < d := by
    rw [hrrdef, div_lt_iff₀ (by positivity)]; nlinarith only [hd2, hP2]
  have hrP : rr ≤ P := by
    rw [hrrdef, div_le_iff₀ (by positivity)]; nlinarith only [hd2, hP2]
  let r : FiniteLpExponent := mkExp rr hr1
  let pe : FiniteLpExponent := ⟨p, hp1, hpt⟩
  have hr : r.exponent.toReal < d := by
    show (mkExp rr hr1).exponent.toReal < d
    rw [mkExp_toReal]; exact hrd
  have hq : (pe.exponent.toReal)⁻¹ = r.exponent.toReal⁻¹ - (d : ℝ)⁻¹ := by
    show p.toReal⁻¹ = (mkExp rr hr1).exponent.toReal⁻¹ - (d : ℝ)⁻¹
    rw [mkExp_toReal, ← hPdef, hrrdef]
    have : (0 : ℝ) < d := by linarith only [hd2]
    have : (0 : ℝ) < P := by linarith only [hP2]
    field_simp
    ring
  obtain ⟨Cs, hCstop, hCs⟩ := exists_cubeScalarData_gradVecLp_sobolev_triadic hd r pe hr hq
  obtain ⟨Ch, hChtop, hCh⟩ :=
    CubeCalderonZygmund.exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le d pe
  refine ⟨2 * Cs.toReal + 1, 2 * Ch.toReal + 1, by positivity, by positivity, ?_⟩
  intro m F hFp
  have hℓ : 0 < cubeScaleFactor (originCube d m) := cubeScaleFactor_pos' _
  have hrle : r.exponent ≤ p := by
    show (mkExp rr hr1).exponent ≤ p
    rw [mkExp_exponent]
    calc ENNReal.ofReal rr ≤ ENNReal.ofReal P := ENNReal.ofReal_le_ofReal hrP
      _ = p := by rw [hPdef, ENNReal.ofReal_toReal hpt.ne]
  have hr0 : r.exponent ≠ 0 := (lt_trans one_pos r.one_lt).ne'
  have hrt : r.exponent ≠ ⊤ := r.lt_top.ne
  have hFr : MemLp F r.exponent (flatHalfMeasure e m) := hFp.mono_exponent hrle
  have hF2 : MemLp F 2 (flatHalfMeasure e m) := hFp.mono_exponent hp2.le
  have hF2v : MemLp F 2 (volume.restrict (flatHalfCube e m)) := (memLp_flatHalfMeasure_iff e m).1 hF2
  obtain ⟨y, hy⟩ := hc_exists_poisson e m hF2v
  have F3 := hc_extend_poisson e m hF2v hy
  have hFt : MemLp (hcExt (-1) e F) p (normalizedCubeMeasure (originCube d m)) :=
    memLp_hcExt_normalized e m (σ := -1) (by simp) hp0 hpt' hFp
  have hFt2 : MemLp (hcExt (-1) e F) 2 (normalizedCubeMeasure (originCube d m)) :=
    hFt.mono_exponent hp2.le
  have hFtr : MemLp (hcExt (-1) e F) r.exponent (normalizedCubeMeasure (originCube d m)) :=
    memLp_hcExt_normalized e m (σ := -1) (by simp) hr0 hrt hFr
  obtain ⟨hgm, hgb⟩ := hCs (originCube d m) _ hFt2 hFtr (hcOddH10 y) F3
  obtain ⟨Hψ, hHm, hHb⟩ := hCh m _ hFt2 hFt (hcOddH10 y) F3
  have hyg : eLpNorm y.toH1Function.grad p (flatHalfMeasure e m) =
      eLpNorm (hcOddH10 y).toH1Function.grad p (flatHalfMeasure e m) :=
    eLpNorm_flatHalf_congr e m (fun x hx => by
      funext i
      show y.toH1Function.grad x i = hcExtVec e y.toH1Function.grad x i
      simp only [hcExtVec, hcExt_of_pos hx.2]) p
  have hhess : flatHessMat (hcRestrictHessian e m y Hψ) = flatHessMat Hψ := rfl
  have hgm' : MemLp y.toH1Function.grad p (flatHalfMeasure e m) := by
    rw [memLp_iff, hyg]
    exact lt_of_le_of_lt (eLpNorm_flatHalf_le_cube e m _ p) hgm.eLpNorm_lt_top
  have hHm' : MemLp (flatHessMat (hcRestrictHessian e m y Hψ)) p (flatHalfMeasure e m) := by
    rw [memLp_iff, hhess]
    exact lt_of_le_of_lt (eLpNorm_flatHalf_le_cube e m _ p) hHm.eLpNorm_lt_top
  have hFnorm : ∀ q : ℝ≥0∞, 1 ≤ q → q ≠ ⊤ →
      eLpNorm (hcExt (-1) e F) q (normalizedCubeMeasure (originCube d m)) ≤
        2 * eLpNorm F q (flatHalfMeasure e m) := fun q hq hqt =>
    eLpNorm_hcExt_le e m (σ := -1) (by simp) hFp.aestronglyMeasurable hq hqt
  have hFrp : eLpNorm F r.exponent (flatHalfMeasure e m) ≤ eLpNorm F p (flatHalfMeasure e m) :=
    eLpNorm_flatHalf_mono_exponent e m (lt_trans one_pos r.one_lt) hrle hpt' hFp.aestronglyMeasurable
  have hfin : eLpNorm F p (flatHalfMeasure e m) ≠ ⊤ := hFp.eLpNorm_lt_top.ne
  refine ⟨y, hcRestrictHessian e m y Hψ, hy, hgm', hHm', ?_, ?_⟩
  · have h1 : eLpNorm y.toH1Function.grad p (flatHalfMeasure e m) ≤
        (Cs * ENNReal.ofReal (cubeScaleFactor (originCube d m)) * 2) *
          eLpNorm F p (flatHalfMeasure e m) := by
      rw [hyg]
      refine (eLpNorm_flatHalf_le_cube e m _ p).trans ?_
      have h2 : eLpNorm (hcOddH10 y).toH1Function.grad p (normalizedCubeMeasure (originCube d m)) ≤
          Cs * ENNReal.ofReal (cubeScaleFactor (originCube d m)) *
            eLpNorm (hcExt (-1) e F) r.exponent (normalizedCubeMeasure (originCube d m)) := hgb
      refine h2.trans ?_
      calc _ ≤ Cs * ENNReal.ofReal (cubeScaleFactor (originCube d m)) *
            (2 * eLpNorm F r.exponent (flatHalfMeasure e m)) := by
              gcongr
              exact hFnorm _ r.one_lt.le hrt
        _ ≤ Cs * ENNReal.ofReal (cubeScaleFactor (originCube d m)) *
            (2 * eLpNorm F p (flatHalfMeasure e m)) := by gcongr
        _ = _ := by ring
    have h3 := hc_toReal_le hfin h1
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top hCstop.ne ENNReal.ofReal_ne_top) (by simp))
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hℓ.le,
      ENNReal.toReal_ofNat] at h3
    have hn : 0 ≤ flatHalfNorm e m p F := ENNReal.toReal_nonneg
    have hC0 : 0 ≤ Cs.toReal := ENNReal.toReal_nonneg
    calc flatHalfNorm e m p y.toH1Function.grad ≤
          Cs.toReal * cubeScaleFactor (originCube d m) * 2 * flatHalfNorm e m p F := h3
      _ ≤ (2 * Cs.toReal + 1) * cubeScaleFactor (originCube d m) * flatHalfNorm e m p F := by
          have : 0 ≤ cubeScaleFactor (originCube d m) * flatHalfNorm e m p F := by positivity
          nlinarith only [this, hC0]
  · have h1 : eLpNorm (flatHessMat (hcRestrictHessian e m y Hψ)) p (flatHalfMeasure e m) ≤
        (Ch * 2) * eLpNorm F p (flatHalfMeasure e m) := by
      rw [hhess]
      refine (eLpNorm_flatHalf_le_cube e m _ p).trans (hHb.trans ?_)
      calc Ch * eLpNorm (hcExt (-1) e F) p (normalizedCubeMeasure (originCube d m))
          ≤ Ch * (2 * eLpNorm F p (flatHalfMeasure e m)) := by
            gcongr; exact hFnorm _ hp1.le hpt'
        _ = _ := by ring
    have h3 := hc_toReal_le hfin h1 (ENNReal.mul_ne_top hChtop.ne (by simp))
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h3
    have hn : 0 ≤ flatHalfNorm e m p F := ENNReal.toReal_nonneg
    have hC0 : 0 ≤ Ch.toReal := ENNReal.toReal_nonneg
    calc flatHalfNorm e m p (flatHessMat (hcRestrictHessian e m y Hψ)) ≤
          Ch.toReal * 2 * flatHalfNorm e m p F := h3
      _ ≤ (2 * Ch.toReal + 1) * flatHalfNorm e m p F := by nlinarith only [hn, hC0]

/-- **Flat `W^{2,p}` on the half cube, scalar form.** -/
theorem flatW2p_halfCube_scalar (hd : 2 ≤ d) (e : Fin d) {p : ℝ≥0∞} (hp2 : 2 < p)
    (hpt : p < ⊤) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ (m : ℤ) (A : CoeffField d) (K : ℝ),
        (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) →
        (∀ x ∈ flatHalfCube e m, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε) →
        (∀ x ∈ flatHalfCube e m, ∀ i j k,
          |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K) →
        K * cubeScaleFactor (originCube d m) ≤ ε →
        ∀ F : Vec d → ℝ, MemLp F p (flatHalfMeasure e m) →
          ∀ w : H10Function (flatHalfCube e m),
            IsH10WeakSolution A (flatHalfCube e m) F (fun _ => 0) w →
            ∃ H : HasWeakHessianOn (flatHalfCube e m) w.toH1Function,
              MemLp (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) p
                (flatHalfMeasure e m) ∧
              flatHalfNorm e m p (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≤
                C * flatHalfNorm e m p F := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, Ch, hCs, hCh, hbase⟩ := hc_base_scalar hd e hp2 hpt
  obtain ⟨ε, C₁, hε, hC₁, hdiv⟩ := flatW2p_halfCube_divergence hd e hp2.le hpt
  refine ⟨ε, C₁ * (Ch + Cs), hε, by positivity, ?_⟩
  intro m A K hA hAε hAK hKℓ F hFp w hw
  have hℓ : 0 < cubeScaleFactor (originCube d m) := cubeScaleFactor_pos' _
  obtain ⟨ψ, Hψ, hψ, hgm, hHm, hgb, hHb⟩ := hbase m F hFp
  have hGp : MemLp (fun x => -ψ.toH1Function.grad x) p (flatHalfMeasure e m) := hgm.neg
  have hweak := flatW2p_neg_jacobian Hψ
  have hjac : jacobianHilbertMat (fun i x k => -Hψ.hess i k x) =
      fun x => -(flatHessMat Hψ x) := by
    funext x; ext i j; simp [jacobianHilbertMat, flatHessMat]
  have hJp : MemLp (jacobianHilbertMat (fun i x k => -Hψ.hess i k x)) p (flatHalfMeasure e m) := by
    rw [hjac]; exact hHm.neg
  have hw' : IsZeroTraceDirichletRhsWeakSolution A (flatHalfCube e m) w
      (fun x => -(fun x => -ψ.toH1Function.grad x) x) := by
    intro φ
    have a := hw φ
    have b := hψ φ
    simp only [neg_neg]
    simp only [vecDot_zero_left, integral_zero, add_zero] at a
    rw [a, ← b]
  obtain ⟨H, hHm', hHb'⟩ := hdiv m A K hA hAε hAK hKℓ _ _ hGp hweak hJp w hw'
  refine ⟨H, hHm', ?_⟩
  have hn1 : flatHalfNorm e m p (jacobianHilbertMat (fun i x k => -Hψ.hess i k x)) =
      flatHalfNorm e m p (flatHessMat Hψ) := by
    rw [hjac]
    unfold flatHalfNorm
    rw [show (fun x => -(flatHessMat Hψ x)) = -(flatHessMat Hψ) from rfl, eLpNorm_neg]
  have hn2 : flatHalfNorm e m p (fun x => -ψ.toH1Function.grad x) =
      flatHalfNorm e m p ψ.toH1Function.grad := by
    unfold flatHalfNorm
    rw [show (fun x => -ψ.toH1Function.grad x) = -ψ.toH1Function.grad from rfl, eLpNorm_neg]
  have hnF : 0 ≤ flatHalfNorm e m p F := ENNReal.toReal_nonneg
  have hinv : (cubeScaleFactor (originCube d m))⁻¹ * (Cs * cubeScaleFactor (originCube d m) *
      flatHalfNorm e m p F) = Cs * flatHalfNorm e m p F := by
    field_simp
  rw [hn1, hn2] at hHb'
  have h4 : flatHalfNorm e m p (flatHessMat Hψ) +
      (cubeScaleFactor (originCube d m))⁻¹ * flatHalfNorm e m p ψ.toH1Function.grad ≤
      (Ch + Cs) * flatHalfNorm e m p F := by
    have h5 := mul_le_mul_of_nonneg_left hgb (inv_nonneg.2 hℓ.le)
    rw [hinv] at h5
    linarith only [hHb, h5]
  calc _ ≤ C₁ * _ := hHb'
    _ ≤ C₁ * ((Ch + Cs) * flatHalfNorm e m p F) := mul_le_mul_of_nonneg_left h4 hC₁.le
    _ = _ := by ring

end SuperdiffusionCLT.Section7
