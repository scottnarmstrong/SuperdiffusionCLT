/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.ScalarComparison

/-!
# The two Laplace problems: comparison of the solutions, and the scalar numerics

For `-s₁ Δu₁ = F = -s₂ Δu₂` in `W` with the same datum `g`, the difference `u₁ - u₂` is the
zero-datum solution of `-Δw = (s₁⁻¹ - s₂⁻¹) F`. Hence its `L^∞` norm and the `H^{-1}` seminorm of
its gradient are bounded by `C L² |s₁⁻¹ - s₂⁻¹| ‖F‖_{L^∞}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal NNReal

variable {d : ℕ}

/-- Cauchy-Schwarz for the pairing of two `L²` functions. -/
theorem s12_ofReal_abs_integral_le {μ : Measure (Vec d)} {h ψ : Vec d → ℝ} (hh : MemLp h 2 μ)
    (hψ : MemLp ψ 2 μ) :
    ENNReal.ofReal |∫ x, h x * ψ x ∂μ| ≤ eLpNorm h 2 μ * eLpNorm ψ 2 μ := by
  have hht : ENNReal.HolderTriple 2 2 1 :=
    ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  have hint : Integrable (fun x => h x * ψ x) μ := memLp_one_iff_integrable.mp (hh.fun_mul (r := 1) hψ)
  have h1 := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hh.aestronglyMeasurable
    hψ.aestronglyMeasurable
  have e1 : eLpNorm (h • ψ) 1 μ = ∫⁻ x, ‖h x * ψ x‖ₑ ∂μ :=
    eLpNorm_one_eq_lintegral_enorm (hint.aestronglyMeasurable)
  rw [e1] at h1
  have h2 : ENNReal.ofReal |∫ x, h x * ψ x ∂μ| ≤ ∫⁻ x, ‖h x * ψ x‖ₑ ∂μ := by
    calc ENNReal.ofReal |∫ x, h x * ψ x ∂μ| ≤ ENNReal.ofReal (∫ x, ‖h x * ψ x‖ ∂μ) := by
          refine ENNReal.ofReal_le_ofReal ?_
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => h x * ψ x)
      _ = ∫⁻ x, ‖h x * ψ x‖ₑ ∂μ := ofReal_integral_norm_eq_lintegral_enorm hint
  exact h2.trans h1

/-- The normalized dual seminorm of an `L²` function is bounded by `c L` times its normalized
`L²` norm, on a set inside a cube of side `L`. -/
theorem s12_wMinusOneBar_le [NeZero d] :
    ∃ c : ℝ, 0 < c ∧ ∀ {W : Set (Vec d)}, IsOpen W → volume W ≠ 0 → volume W ≠ ⊤ →
      ∀ (z : Vec d) {L : ℝ}, 0 < L → W ⊆ axisCube z L → ∀ (h : Vec d → ℝ),
        MemLp h 2 (volume.restrict W) →
          wMinusOneBar W 2 h ≤
            ENNReal.ofReal (c * L) * ((volume W ^ (1 / 2 : ℝ))⁻¹ * eLpNorm h 2 (volume.restrict W)) := by
  obtain ⟨c, hc, hP⟩ := p13_poincare (d := d)
  refine ⟨c, hc, ?_⟩
  intro W hWo hW0 hWt z L hL hWL h hh
  set a : ℝ≥0∞ := volume W ^ (1 / 2 : ℝ) with ha
  have ha0 : a ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hW0) hWt).ne'
  have hat : a ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hWt
  have haa : a * a = volume W := by
    rw [ha, ← ENNReal.rpow_add _ _ hW0 hWt]
    norm_num
  have hWinv : (volume W)⁻¹ = a⁻¹ * a⁻¹ := by
    rw [← haa, ENNReal.mul_inv (Or.inl ha0) (Or.inl hat)]
  have hainv : a⁻¹ * a = 1 := ENNReal.inv_mul_cancel ha0 hat
  unfold wMinusOneBar
  refine iSup_le fun ψ => iSup_le fun hψ => ?_
  -- the gradient of the test function
  have hψ2 : eLpNorm ψ.toH1Function.grad 2 (volume.restrict W) ≤ a := by
    have h1 := hψ
    unfold lpBar at h1
    have hconj : (2 : ℝ≥0∞).conjExponent = 2 := ENNReal.HolderConjugate.conjExponent_eq
    rw [hconj, eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.2 hWt)] at h1
    have e : ((volume W)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal = a⁻¹ := by
      rw [ha, ← ENNReal.inv_rpow, ENNReal.toReal_div]
      norm_num
    rw [e, smul_eq_mul, ENNReal.inv_mul_le_iff ha0 hat, mul_one] at h1
    exact h1
  have hPo := hP hWo z hL hWL ψ
  have hψm : MemLp ψ.toH1Function.toFun 2 (volume.restrict W) := ψ.toH1Function.memL2
  have hpair := s12_ofReal_abs_integral_le hh hψm
  have hnorm : ENNReal.ofReal |((volume W).toReal)⁻¹ * ∫ x in W, h x * ψ.toH1Function.toFun x| =
      (volume W)⁻¹ * ENNReal.ofReal |∫ x in W, h x * ψ.toH1Function.toFun x| := by
    rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), abs_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg),
      ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hW0 hWt), ENNReal.ofReal_toReal hWt]
  rw [hnorm, hWinv]
  calc a⁻¹ * a⁻¹ * ENNReal.ofReal |∫ x in W, h x * ψ.toH1Function.toFun x|
      ≤ a⁻¹ * a⁻¹ * (eLpNorm h 2 (volume.restrict W) *
          (ENNReal.ofReal (c * L) * a)) :=
        mul_le_mul' le_rfl (hpair.trans (mul_le_mul' le_rfl (hPo.trans (mul_le_mul' le_rfl hψ2))))
    _ = (a⁻¹ * a) * (ENNReal.ofReal (c * L) * (a⁻¹ * eLpNorm h 2 (volume.restrict W))) := by ring
    _ = ENNReal.ofReal (c * L) * (a⁻¹ * eLpNorm h 2 (volume.restrict W)) := by rw [hainv, one_mul]

/-- The `L²` norm is bounded by the `L^∞` norm times the root of the volume. -/
theorem s12_eLpNorm_two_le (W : Set (Vec d)) (f : Vec d → ℝ)
    (hM : eLpNorm f ⊤ (volume.restrict W) ≠ ⊤) :
    eLpNorm f 2 (volume.restrict W) ≤ eLpNorm f ⊤ (volume.restrict W) * volume W ^ (1 / 2 : ℝ) := by
  have hfm : AEStronglyMeasurable f (volume.restrict W) := aestronglyMeasurable_of_eLpNorm_ne_top hM
  have hfC : ∀ᵐ x ∂(volume.restrict W), ‖f x‖ₑ ≤ eLpNorm f ⊤ (volume.restrict W) := by
    rw [eLpNorm_exponent_top hfm]
    exact ae_le_eLpNormEssSup
  have h1 := eLpNorm_le_of_ae_enorm_bound (p := 2) hfm hfC
  rw [Measure.restrict_apply_univ, smul_eq_mul] at h1
  have e : (2 : ℝ≥0∞).toReal⁻¹ = 1 / 2 := by norm_num
  rwa [e] at h1

/-- `H^{-1}` seminorm of the gradient of a zero-datum Laplace solution. -/
theorem s12_hMinus_grad_bound [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ {W : Set (Vec d)}, IsOpen W → IsBoundedDomain W → W.Nonempty →
      ∀ (z : Vec d) {L : ℝ}, 0 < L → W ⊆ axisCube z L → ∀ (f : Vec d → ℝ) (w : H10Function W),
        IsWeakSolutionOn (fun _ => (1 : Mat d)) W w.toH1Function f (fun _ => 0) →
          s12_hMinusOneVec W w.toH1Function.grad ≤
            ENNReal.ofReal (C * L ^ 2) * eLpNorm f ⊤ (volume.restrict W) := by
  obtain ⟨c₁, hc₁, hE⟩ := s12_energy (d := d)
  obtain ⟨c₂, hc₂, hW⟩ := s12_wMinusOneBar_le (d := d)
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  refine ⟨d * (c₂ * c₁), by positivity, ?_⟩
  intro W hWo hWb hne z L hL hWL f w hw
  set M := eLpNorm f ⊤ (volume.restrict W) with hM
  by_cases hMt : M = ⊤
  · rw [hMt, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
    exact le_top
  have hWt : volume W ≠ ⊤ := by
    simpa using hWb.isFiniteMeasure_restrict_volume.measure_univ_lt_top.ne
  have hW0 : volume W ≠ 0 := (hWo.measure_pos volume hne).ne'
  set a : ℝ≥0∞ := volume W ^ (1 / 2 : ℝ) with ha
  have ha0 : a ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hW0) hWt).ne'
  have hat : a ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hWt
  have hainv : a⁻¹ * a = 1 := ENNReal.inv_mul_cancel ha0 hat
  obtain ⟨-, hgrad⟩ := hE hWo z hL hWL f w hw
  have hf2 := s12_eLpNorm_two_le W f hMt
  have hcomp : ∀ i : Fin d, wMinusOneBar W 2 (fun x => w.toH1Function.grad x i) ≤
      ENNReal.ofReal (c₂ * L) * ENNReal.ofReal (c₁ * L) * M := by
    intro i
    have hi : MemLp (fun x => w.toH1Function.grad x i) 2 (volume.restrict W) :=
      w.toH1Function.gradMemL2 i
    refine (hW hWo hW0 hWt z hL hWL _ hi).trans ?_
    have hle : eLpNorm (fun x => w.toH1Function.grad x i) 2 (volume.restrict W) ≤
        ENNReal.ofReal (c₁ * L) * (M * a) := by
      refine le_trans ?_ (hgrad.trans (mul_le_mul' le_rfl hf2))
      refine eLpNorm_mono hi.aestronglyMeasurable fun x => ?_
      have h0 : 0 ≤ eucNorm (w.toH1Function.grad x) := Real.sqrt_nonneg _
      rw [Real.norm_eq_abs, Real.norm_of_nonneg h0]
      exact abs_le_eucNorm _ i
    calc ENNReal.ofReal (c₂ * L) * (a⁻¹ * eLpNorm (fun x => w.toH1Function.grad x i) 2
          (volume.restrict W))
        ≤ ENNReal.ofReal (c₂ * L) * (a⁻¹ * (ENNReal.ofReal (c₁ * L) * (M * a))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hle)
      _ = (a⁻¹ * a) * (ENNReal.ofReal (c₂ * L) * ENNReal.ofReal (c₁ * L) * M) := by ring
      _ = ENNReal.ofReal (c₂ * L) * ENNReal.ofReal (c₁ * L) * M := by rw [hainv, one_mul]
  unfold s12_hMinusOneVec
  calc ∑ i : Fin d, wMinusOneBar W 2 (fun x => w.toH1Function.grad x i)
      ≤ ∑ _i : Fin d, ENNReal.ofReal (c₂ * L) * ENNReal.ofReal (c₁ * L) * M :=
        Finset.sum_le_sum fun i _ => hcomp i
    _ = ENNReal.ofReal (d * (c₂ * c₁) * L ^ 2) * M := by
        have e1 : ENNReal.ofReal (c₂ * L) * ENNReal.ofReal (c₁ * L) =
            ENNReal.ofReal ((c₂ * L) * (c₁ * L)) := (ENNReal.ofReal_mul (by positivity)).symm
        have e2 : ENNReal.ofReal (d * (c₂ * c₁) * L ^ 2) =
            (d : ℝ≥0∞) * ENNReal.ofReal ((c₂ * L) * (c₁ * L)) := by
          rw [← ENNReal.ofReal_natCast d, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
          congr 1
          ring
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, e2, e1]
        ring

theorem s12_vecDot_sub_left (a b c : Vec d) : vecDot (a - b) c = vecDot a c - vecDot b c := by
  simp [vecDot, sub_mul, Finset.sum_sub_distrib]

/-- The dual seminorm only sees the function up to a null set. -/
theorem s12_wMinusOneBar_congr_ae {W : Set (Vec d)} {h h' : Vec d → ℝ}
    (hh : ∀ᵐ x ∂(volume.restrict W), h x = h' x) (p : ℝ≥0∞) :
    wMinusOneBar W p h = wMinusOneBar W p h' := by
  unfold wMinusOneBar
  refine iSup_congr fun ψ => iSup_congr fun _ => ?_
  have : ∫ x in W, h x * ψ.toH1Function.toFun x = ∫ x in W, h' x * ψ.toH1Function.toFun x :=
    integral_congr_ae (hh.mono fun x hx => by simp only [hx])
  rw [this]

theorem s12_hMinusOneVec_congr_ae {W : Set (Vec d)} {F G : Vec d → Vec d}
    (hh : ∀ᵐ x ∂(volume.restrict W), F x = G x) :
    s12_hMinusOneVec W F = s12_hMinusOneVec W G := by
  unfold s12_hMinusOneVec
  refine Finset.sum_congr rfl fun i _ => ?_
  exact s12_wMinusOneBar_congr_ae (hh.mono fun x hx => by rw [hx]) 2

/-- **Comparison of the two Laplace problems.** If `-s₁ Δu₁ = F = -s₂ Δu₂` in `W ⊆ (z, z+L)^d`
with the same datum `g`, then `‖u₁ - u₂‖_{L^∞} + [∇u₁ - ∇u₂]_{H^{-1}}` is at most
`C L² |s₁⁻¹ - s₂⁻¹| ‖F‖_{L^∞}`, with `C` depending on `d` only. -/
theorem s12_laplace_comparison [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {W : Set (Vec d)}, IsOpen W → IsBoundedDomain W → W.Nonempty →
      ∀ (z : Vec d) {L : ℝ}, 0 < L → W ⊆ axisCube z L → ∀ (s₁ s₂ : ℝ), s₁ ≠ 0 → s₂ ≠ 0 →
        ∀ (F : Vec d → ℝ) (g u₁ u₂ : H1Function W),
          s12_IsDirichletSolution (fun _ => s₁ • (1 : Mat d)) W F g u₁ →
          s12_IsDirichletSolution (fun _ => s₂ • (1 : Mat d)) W F g u₂ →
            eLpNorm (fun x => u₁.toFun x - u₂.toFun x) ⊤ (volume.restrict W) +
                s12_hMinusOneVec W (fun x => u₁.grad x - u₂.grad x) ≤
              ENNReal.ofReal (C * L ^ 2 * |s₁⁻¹ - s₂⁻¹|) * eLpNorm F ⊤ (volume.restrict W) := by
  obtain ⟨C₁, hC₁, hS⟩ := s12_sup_bound (d := d) hd
  obtain ⟨C₂, hC₂, hH⟩ := s12_hMinus_grad_bound (d := d)
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro W hWo hWb hne z L hL hWL s₁ s₂ hs₁ hs₂ F g u₁ u₂ h₁ h₂
  obtain ⟨v₁, hv₁⟩ := h₁.2
  obtain ⟨v₂, hv₂⟩ := h₂.2
  set c : ℝ := s₁⁻¹ - s₂⁻¹ with hc
  set w : H10Function W := v₁ + (-1 : ℝ) • v₂ with hw
  have hwfun : ∀ x, w.toH1Function.toFun x = u₁.toFun x - u₂.toFun x := by
    intro x
    change v₁.toH1Function.toFun x + (-1 : ℝ) * v₂.toH1Function.toFun x = _
    rw [congrFun hv₁ x, congrFun hv₂ x]
    ring
  have hwgrad : w.toH1Function.grad =ᵐ[volume.restrict W] fun x => u₁.grad x - u₂.grad x := by
    filter_upwards [w0_h10_grad_ae hWo g u₁ v₁ hv₁, w0_h10_grad_ae hWo g u₂ v₂ hv₂] with x e1 e2
    change v₁.toH1Function.grad x + (-1 : ℝ) • v₂.toH1Function.grad x = _
    rw [e1, e2]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  -- the equation of the difference
  have hweak : IsWeakSolutionOn (fun _ => (1 : Mat d)) W w.toH1Function (fun x => c * F x)
      (fun _ => 0) := by
    intro φ
    have e1 := h₁.1 φ
    have e2 := h₂.1 φ
    simp only [s12_matVecMul_smul_left, p13_matVecMul_one, vecDot_smul_left, integral_const_mul,
      vecDot_zero_left, integral_zero, add_zero] at e1 e2 ⊢
    set J₁ := ∫ x in W, vecDot (u₁.grad x) (φ.toH1Function.grad x) with hJ₁
    set J₂ := ∫ x in W, vecDot (u₂.grad x) (φ.toH1Function.grad x) with hJ₂
    have hi₁ : IntegrableOn (fun x => vecDot (u₁.grad x) (φ.toH1Function.grad x)) W :=
      integrableOn_vecDot_of_memVectorL2 u₁.grad_memVectorL2 φ.toH1Function.grad_memVectorL2
    have hi₂ : IntegrableOn (fun x => vecDot (u₂.grad x) (φ.toH1Function.grad x)) W :=
      integrableOn_vecDot_of_memVectorL2 u₂.grad_memVectorL2 φ.toH1Function.grad_memVectorL2
    have hL : ∫ x in W, vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) = J₁ - J₂ := by
      rw [hJ₁, hJ₂, ← integral_sub hi₁ hi₂]
      refine integral_congr_ae (hwgrad.mono fun x hx => ?_)
      simp only [hx, s12_vecDot_sub_left]
    rw [hL]
    have k₁ : J₁ = s₁⁻¹ * ∫ x in W, F x * φ.toH1Function.toFun x := by
      field_simp
      linarith only [e1]
    have k₂ : J₂ = s₂⁻¹ * ∫ x in W, F x * φ.toH1Function.toFun x := by
      field_simp
      linarith only [e2]
    have hR : ∫ x in W, c * F x * φ.toH1Function.toFun x =
        c * ∫ x in W, F x * φ.toH1Function.toFun x := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hR, k₁, k₂, hc]
    ring
  set M := eLpNorm F ⊤ (volume.restrict W) with hMdef
  have hM : eLpNorm (fun x => c * F x) ⊤ (volume.restrict W) = ENNReal.ofReal |c| * M := by
    have : (fun x => c * F x) = c • F := by
      funext x
      simp
    rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
  have h1 := hS hWo hWb z hL hWL _ w hweak
  have h2 := hH hWo hWb hne z hL hWL _ w hweak
  rw [hM] at h1 h2
  have e1 : (fun x => u₁.toFun x - u₂.toFun x) = w.toH1Function.toFun := (funext hwfun).symm
  have e2 := s12_hMinusOneVec_congr_ae (W := W) hwgrad
  rw [e1, ← e2]
  have e3 : ENNReal.ofReal ((C₁ + C₂) * L ^ 2 * |c|) =
      ENNReal.ofReal (C₁ * L ^ 2) * ENNReal.ofReal |c| +
        ENNReal.ofReal (C₂ * L ^ 2) * ENNReal.ofReal |c| := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc _ ≤ ENNReal.ofReal (C₁ * L ^ 2) * (ENNReal.ofReal |c| * M) +
        ENNReal.ofReal (C₂ * L ^ 2) * (ENNReal.ofReal |c| * M) := add_le_add h1 h2
    _ = ENNReal.ofReal ((C₁ + C₂) * L ^ 2 * |c|) * M := by rw [e3]; ring

/-! ### Satisfiability: the zero solution -/

example : True := by
  obtain ⟨C, hC, hmain⟩ := s12_laplace_comparison (d := 2) le_rfl
  have hne : (axisCube (0 : Vec 2) 1).Nonempty :=
    ⟨fun _ => 1 / 2, fun j _ => by
      simp only [Set.mem_Ioo, Pi.zero_apply]
      constructor <;> norm_num⟩
  have hsol : s12_IsDirichletSolution (fun _ => (1 : ℝ) • (1 : Mat 2)) (axisCube (0 : Vec 2) 1)
      (fun _ => 0) witnessZeroH10.toH1Function witnessZeroH10.toH1Function := by
    refine ⟨?_, ?_⟩
    · have := witnessZeroH10_weak
      refine s12_transfer (fun x => ?_) (fun x => rfl) (fun x => rfl) this
      simp
    · have h0 : (fun x => witnessZeroH10.toH1Function.toFun x -
          witnessZeroH10.toH1Function.toFun x) = (0 : Vec 2 → ℝ) := by
        funext x
        simp
      rw [h0]
      exact memH10_zero
  have := hmain (isOpen_axisCube (0 : Vec 2) 1)
    (isOpenBoundedConvexDomain_axisCube (0 : Vec 2) 1).isBoundedDomain hne (0 : Vec 2) one_pos
    subset_rfl 1 1 one_ne_zero one_ne_zero (fun _ => 0) _ _ _ hsol hsol
  trivial

/-! ### Numerics of the replacement of `σ̄_K` by `S_ε` -/

/-- The scale `S_ε = (2 c⋆ |log ε|)^{1/2}` of the normalization. -/
noncomputable def s12_scaleS (cStar ε : ℝ) : ℝ := (2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2)

/-- The scale index `K = ⌈log₃ ε⁻¹⌉`. -/
noncomputable def s12_scaleK (ε : ℝ) : ℕ := ⌈Real.logb 3 ε⁻¹⌉₊

theorem s12_logb_pos {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) : 0 < Real.logb 3 ε⁻¹ := by
  apply Real.logb_pos (by norm_num)
  rw [lt_inv_comm₀ one_pos hε]
  simp only [inv_one]
  linarith only [hε2]

/-- `R ≤ 3^K < 3 R` and `1 ≤ K`, for `K = ⌈log₃ R⌉`, `R = ε⁻¹`. -/
theorem s12_scaleK_bounds {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ε⁻¹ ≤ (3 : ℝ) ^ s12_scaleK ε ∧ (3 : ℝ) ^ s12_scaleK ε < 3 * ε⁻¹ ∧ 1 ≤ s12_scaleK ε := by
  have hx := s12_logb_pos hε hε2
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  set x := Real.logb 3 ε⁻¹ with hxdef
  have h1 : x ≤ (s12_scaleK ε : ℝ) := Nat.le_ceil x
  have h2 : (s12_scaleK ε : ℝ) < x + 1 := Nat.ceil_lt_add_one hx.le
  refine ⟨?_, ?_, ?_⟩
  · have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) h1
    rwa [hxdef, Real.rpow_logb (by norm_num) (by norm_num) hR, Real.rpow_natCast] at this
  · have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3) h2
    rwa [Real.rpow_natCast, Real.rpow_add (by norm_num), hxdef,
      Real.rpow_logb (by norm_num) (by norm_num) hR, Real.rpow_one, mul_comm] at this
  · exact Nat.ceil_pos.2 hx

theorem s12_log_sq_le {k t : ℝ} (hk : 1 ≤ k) (ht : 0 < t) :
    Real.log k ^ 2 ≤ k ^ (2 * t) / t ^ 2 := by
  have h0 : 0 ≤ Real.log k := Real.log_nonneg hk
  have h1 : Real.log k ≤ k ^ t / t := Real.log_le_rpow_div (by linarith only [hk]) ht
  calc Real.log k ^ 2 ≤ (k ^ t / t) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = k ^ (2 * t) / t ^ 2 := by
      rw [div_pow, ← Real.rpow_natCast (k ^ t) 2, ← Real.rpow_mul (by linarith only [hk])]
      norm_num
      rw [mul_comm]

/-- The comparison of `S` and `T` from the position of `x = log₃ R` in `(K - 1, K]`. -/
theorem s12_sqrt_compare {A K x : ℝ} (hA : 0 < A) (hK : 1 ≤ K) (hx : 0 < x) (h1 : K - 1 < x)
    (h2 : x ≤ K) :
    Real.sqrt (A * x) ≤ Real.sqrt (A * K) ∧ 0 < Real.sqrt (A * K) ∧
      Real.sqrt (A * K) - Real.sqrt (A * x) ≤ A / Real.sqrt (A * K) := by
  have hKp : 0 < K := by linarith only [hK]
  have hT : 0 < Real.sqrt (A * K) := Real.sqrt_pos.2 (mul_pos hA hKp)
  have hST : Real.sqrt (A * x) ≤ Real.sqrt (A * K) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h2 hA.le)
  refine ⟨hST, hT, ?_⟩
  set S := Real.sqrt (A * x) with hS
  set T := Real.sqrt (A * K) with hTd
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S * S = A * x := Real.mul_self_sqrt (mul_pos hA hx).le
  have hT2 : T * T = A * K := Real.mul_self_sqrt (mul_pos hA hKp).le
  have hTS : S * S ≤ T * S := mul_le_mul_of_nonneg_right hST hS0
  rw [le_div_iff₀ hT]
  have : A * K - A * x ≤ A := by
    have := mul_le_mul_of_nonneg_left (show K - x ≤ 1 by linarith only [h1]) hA.le
    linarith only [this]
  linarith only [hS2, hT2, hTS, this]

theorem s12_scaleS_eq {cStar ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    s12_scaleS cStar ε = Real.sqrt (2 * cStar * Real.log 3 * Real.logb 3 ε⁻¹) := by
  unfold s12_scaleS
  rw [Real.sqrt_eq_rpow]
  congr 1
  have hlog : Real.log ε < 0 := Real.log_neg hε (by linarith only [hε2])
  rw [abs_of_neg hlog, Real.logb, ← Real.log_inv]
  have : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp

theorem s12_scaleK_x {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    Real.logb 3 ε⁻¹ ≤ (s12_scaleK ε : ℝ) ∧ (s12_scaleK ε : ℝ) < Real.logb 3 ε⁻¹ + 1 :=
  ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (s12_logb_pos hε hε2).le⟩

/-- The algebra behind the ratio `S / shom`. -/
theorem s12_ratio_core {S T A E sh : ℝ} (hT : 0 < T) (hST : S ≤ T)
    (hTS : T - S ≤ A / T) (hsh : |sh - T| ≤ E) (hE : E ≤ T / 2) :
    0 < sh ∧ S / sh ≤ 2 ∧ |S / sh - 1| ≤ 2 * E / T + 2 * (A / T) / T := by
  have h1 := abs_le.1 hsh
  have hsh2 : T / 2 ≤ sh := by linarith only [h1.1, hE]
  have hshp : 0 < sh := by linarith only [hsh2, hT]
  refine ⟨hshp, ?_, ?_⟩
  · rw [div_le_iff₀ hshp]
    linarith only [hsh2, hST]
  · have hnum : |S - sh| ≤ E + A / T := by
      have h2 : |S - sh| ≤ |S - T| + |T - sh| := abs_sub_le S T sh
      have h3 : |S - T| = T - S := by rw [abs_sub_comm, abs_of_nonneg (by linarith only [hST])]
      have h4 : |T - sh| = |sh - T| := abs_sub_comm _ _
      linarith only [h2, h3, h4, hsh, hTS]
    have e : S / sh - 1 = (S - sh) / sh := by field_simp
    rw [e, abs_div, abs_of_pos hshp, div_le_iff₀ hshp]
    have h5 : (2 * E / T + 2 * (A / T) / T) * sh ≥ (2 * E / T + 2 * (A / T) / T) * (T / 2) :=
      mul_le_mul_of_nonneg_left hsh2 (by
        have : 0 ≤ E := (abs_nonneg _).trans hsh
        have hA : 0 ≤ A / T := by
          have : 0 ≤ A / T := le_trans (by linarith only [hST]) hTS
          exact this
        positivity)
    have h6 : (2 * E / T + 2 * (A / T) / T) * (T / 2) = E + A / T := by
      field_simp
    linarith only [hnum, h5, h6]

theorem s12_rate_bound {k α b : ℝ} (hk : 1 ≤ k) (hα : α < 1 / 2) (hb : 0 ≤ b) :
    (Real.log k ^ 2 + b) / Real.sqrt k ≤
      (1 / ((1 / 2 - α) / 4) ^ 2 + b) * k ^ (-α) := by
  have hk0 : 0 < k := by linarith only [hk]
  set t : ℝ := (1 / 2 - α) / 4 with ht
  have ht0 : 0 < t := by rw [ht]; linarith only [hα]
  have hsq : Real.sqrt k = k ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow k
  have hpos : 0 < k ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hk0 _
  have h1 := s12_log_sq_le hk ht0
  have e1 : k ^ (2 * t) / t ^ 2 / k ^ (1 / 2 : ℝ) = (1 / t ^ 2) * k ^ (2 * t - 1 / 2) := by
    rw [Real.rpow_sub hk0]
    field_simp
  have e2 : k ^ (2 * t - 1 / 2) ≤ k ^ (-α) := by
    refine Real.rpow_le_rpow_of_exponent_le hk ?_
    rw [ht]
    linarith only [hα]
  have e3 : b / k ^ (1 / 2 : ℝ) ≤ b * k ^ (-α) := by
    have : k ^ (-α) ≥ 1 / k ^ (1 / 2 : ℝ) := by
      rw [one_div, ← Real.rpow_neg hk0.le]
      exact Real.rpow_le_rpow_of_exponent_le hk (by linarith only [hα])
    calc b / k ^ (1 / 2 : ℝ) = b * (1 / k ^ (1 / 2 : ℝ)) := by ring
      _ ≤ b * k ^ (-α) := mul_le_mul_of_nonneg_left this hb
  rw [hsq, add_div]
  have e4 : Real.log k ^ 2 / k ^ (1 / 2 : ℝ) ≤ (1 / t ^ 2) * k ^ (-α) := by
    calc Real.log k ^ 2 / k ^ (1 / 2 : ℝ) ≤ k ^ (2 * t) / t ^ 2 / k ^ (1 / 2 : ℝ) :=
          div_le_div_of_nonneg_right h1 hpos.le
      _ = (1 / t ^ 2) * k ^ (2 * t - 1 / 2) := e1
      _ ≤ (1 / t ^ 2) * k ^ (-α) := mul_le_mul_of_nonneg_left e2 (by positivity)
  linarith only [e3, e4]

/-- **The scalar replacement.** Let `σ̄_m` satisfy the sharp asymptotics
`|σ̄_m - (2 c⋆ log 3 · m)^{1/2}| ≤ C₀ c⋆⁻¹ (log² m + K_c)` for `m ≥ M`. For `α < 1/2` there are
`C` and `K₀` such that, for `ε ∈ (0, 1/2]` with `ε⁻¹ ≥ 3^{K₀}` and `K = ⌈log₃ ε⁻¹⌉`:
`shom_K > 0`, `S_ε / shom_K ≤ 2`, and `|S_ε / shom_K - 1| ≤ C K^{-α} ≤ C (log 3)^α |log ε|^{-α}`. -/
theorem s12_scalar_numerics {cStar C0 Kc : ℝ} (hc : 0 < cStar) (hC0 : 0 ≤ C0) {M : ℕ}
    {shom : ℕ → ℝ}
    (hsh : ∀ m : ℕ, M ≤ m → |shom m - (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
        C0 * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + Kc))
    {α : ℝ} (hα0 : 0 < α) (hα : α < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ K₀ : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → (3 : ℝ) ^ K₀ ≤ ε⁻¹ →
      0 < shom (s12_scaleK ε) ∧ s12_scaleS cStar ε / shom (s12_scaleK ε) ≤ 2 ∧
      |s12_scaleS cStar ε / shom (s12_scaleK ε) - 1| ≤ C * (s12_scaleK ε : ℝ) ^ (-α) ∧
      C * (s12_scaleK ε : ℝ) ^ (-α) ≤ C * Real.log 3 ^ α * |Real.log ε| ^ (-α) := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set A : ℝ := 2 * cStar * Real.log 3 with hA
  have hA0 : 0 < A := by positivity
  set κ : ℝ := Real.sqrt A with hκ
  have hκ0 : 0 < κ := Real.sqrt_pos.2 hA0
  set Θ : ℝ := 2 * C0 * cStar⁻¹ * (64 + |Kc|) / κ with hΘ
  have hΘ0 : 0 ≤ Θ := by positivity
  set C : ℝ := (2 * C0 * cStar⁻¹ / κ) * (1 / ((1 / 2 - α) / 4) ^ 2 + |Kc|) + 2 with hCdef
  have hC0' : 0 < C := by positivity
  refine ⟨C, hC0', max M ⌈Θ ^ 4⌉₊ + 1, ?_⟩
  intro ε hε hε2 hK0
  obtain ⟨hR1, hR2, hK1⟩ := s12_scaleK_bounds hε hε2
  obtain ⟨hx1, hx2⟩ := s12_scaleK_x hε hε2
  have hx0 := s12_logb_pos hε hε2
  set K := s12_scaleK ε with hK
  set k : ℝ := (K : ℝ) with hk
  have hk1 : 1 ≤ k := by rw [hk]; exact_mod_cast hK1
  have hk0 : 0 < k := by linarith only [hk1]
  have hK0K : max M ⌈Θ ^ 4⌉₊ + 1 ≤ K := by
    have := hK0.trans hR1
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 this
  have hMK : M ≤ K := by
    have := le_max_left M ⌈Θ ^ 4⌉₊
    omega
  have hΘK : Θ ^ 4 ≤ k := by
    have h1 := le_max_right M ⌈Θ ^ 4⌉₊
    have h2 : ⌈Θ ^ 4⌉₊ ≤ K := by omega
    calc Θ ^ 4 ≤ (⌈Θ ^ 4⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ k := by rw [hk]; exact_mod_cast h2
  -- the fourth root
  set q : ℝ := k ^ (1 / 4 : ℝ) with hq
  have hq1 : 1 ≤ q := Real.one_le_rpow hk1 (by norm_num)
  have hΘq : Θ ≤ q := by
    have h1 := Real.rpow_le_rpow (by positivity) hΘK (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have h2 : (Θ ^ 4) ^ (1 / 4 : ℝ) = Θ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hΘ0]
      norm_num
    rwa [h2] at h1
  have hq2 : q ^ 2 = Real.sqrt k := by
    rw [hq, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hk0.le]
    norm_num
  -- T = κ q²
  set T : ℝ := Real.sqrt (A * k) with hT
  have hTe : T = κ * q ^ 2 := by
    rw [hT, hκ, hq2, Real.sqrt_mul hA0.le]
  have hTanchor : (2 * cStar * Real.log 3 * k) ^ ((1 : ℝ) / 2) = T := by
    rw [hT, Real.sqrt_eq_rpow, hA]
  obtain ⟨hST, hTpos, hTS⟩ := s12_sqrt_compare hA0 hk1 hx0 (by linarith only [hx2]) hx1
  have hSeq : s12_scaleS cStar ε = Real.sqrt (A * Real.logb 3 ε⁻¹) := by
    rw [s12_scaleS_eq hε hε2, hA]
  rw [← hSeq] at hST hTS
  -- the anchor
  have hanchor := hsh K hMK
  rw [← hk, hTanchor, Real.rpow_two] at hanchor
  set E : ℝ := C0 * cStar⁻¹ * (Real.log k ^ 2 + Kc) with hE
  -- E is at most T / 2
  have hlog := s12_log_sq_le hk1 (by norm_num : (0 : ℝ) < 1 / 8)
  have hlog' : Real.log k ^ 2 ≤ 64 * q := by
    have : k ^ (2 * (1 / 8 : ℝ)) = q := by rw [hq]; norm_num
    rw [this] at hlog
    have e : q / (1 / 8 : ℝ) ^ 2 = 64 * q := by norm_num; ring
    linarith only [hlog, e]
  have hKc : Kc ≤ |Kc| * q := by
    calc Kc ≤ |Kc| := le_abs_self _
      _ = |Kc| * 1 := (mul_one _).symm
      _ ≤ |Kc| * q := mul_le_mul_of_nonneg_left hq1 (abs_nonneg _)
  have hEq : E ≤ C0 * cStar⁻¹ * ((64 + |Kc|) * q) := by
    rw [hE]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith only [hlog', hKc]
  have hET : E ≤ T / 2 := by
    refine hEq.trans ?_
    have h1 : C0 * cStar⁻¹ * ((64 + |Kc|) * q) = (Θ * κ / 2) * q := by
      rw [hΘ]
      field_simp
    rw [h1, hTe]
    have h2 : Θ * κ / 2 * q ≤ q * κ / 2 * q := by
      refine mul_le_mul_of_nonneg_right ?_ (by linarith only [hq1])
      have := mul_le_mul_of_nonneg_right hΘq hκ0.le
      linarith only [this]
    linarith only [h2]
  obtain ⟨hshp, hrat, hbound⟩ := s12_ratio_core hTpos hST hTS hanchor hET
  refine ⟨hshp, hrat, ?_, ?_⟩
  · refine hbound.trans ?_
    -- 2E/T + 2(A/T)/T ≤ C k^{-α}
    have hTsq : T = κ * Real.sqrt k := by rw [hTe, hq2]
    have h1 : 2 * (A / T) / T = 2 / k := by
      have : T * T = A * k := Real.mul_self_sqrt (mul_pos hA0 hk0).le
      calc 2 * (A / T) / T = 2 * A / (T * T) := by field_simp
        _ = 2 * A / (A * k) := by rw [this]
        _ = 2 / k := by field_simp
    have h2 : 2 / k ≤ 2 * k ^ (-α) := by
      have : k ^ (-α) ≥ 1 / k := by
        rw [one_div, ← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hk1 (by linarith only [hα])
      calc 2 / k = 2 * (1 / k) := by ring
        _ ≤ 2 * k ^ (-α) := mul_le_mul_of_nonneg_left this (by norm_num)
    have h3 : 2 * E / T ≤ (2 * C0 * cStar⁻¹ / κ) * ((1 / ((1 / 2 - α) / 4) ^ 2 + |Kc|) * k ^ (-α)) := by
      have hEq' : E ≤ C0 * cStar⁻¹ * (Real.log k ^ 2 + |Kc|) := by
        rw [hE]
        exact mul_le_mul_of_nonneg_left (by linarith only [le_abs_self Kc]) (by positivity)
      have hrb := s12_rate_bound hk1 hα (abs_nonneg Kc)
      have e : 2 * E / T = (2 / κ) * (E / Real.sqrt k) := by
        rw [hTsq]
        field_simp
      calc 2 * E / T = (2 / κ) * (E / Real.sqrt k) := e
        _ ≤ (2 / κ) * ((C0 * cStar⁻¹ * (Real.log k ^ 2 + |Kc|)) / Real.sqrt k) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_right hEq' (Real.sqrt_nonneg _)
        _ = (2 * C0 * cStar⁻¹ / κ) * ((Real.log k ^ 2 + |Kc|) / Real.sqrt k) := by ring
        _ ≤ (2 * C0 * cStar⁻¹ / κ) * ((1 / ((1 / 2 - α) / 4) ^ 2 + |Kc|) * k ^ (-α)) :=
          mul_le_mul_of_nonneg_left hrb (by positivity)
    rw [h1]
    have : C * k ^ (-α) = (2 * C0 * cStar⁻¹ / κ) *
        ((1 / ((1 / 2 - α) / 4) ^ 2 + |Kc|) * k ^ (-α)) + 2 * k ^ (-α) := by
      rw [hCdef]; ring
    linarith only [h2, h3, this]
  · rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC0'.le
    -- k ≥ x = |log ε| / log 3
    have hlog : Real.log ε < 0 := Real.log_neg hε (by linarith only [hε2])
    have hxe : Real.logb 3 ε⁻¹ = |Real.log ε| / Real.log 3 := by
      rw [Real.logb, Real.log_inv, abs_of_neg hlog]
    have hxk : |Real.log ε| / Real.log 3 ≤ k := by rw [← hxe]; exact hx1
    have hpos : 0 < |Real.log ε| / Real.log 3 := by rw [← hxe]; exact hx0
    calc k ^ (-α) ≤ (|Real.log ε| / Real.log 3) ^ (-α) :=
          Real.rpow_le_rpow_of_nonpos hpos hxk (by linarith only [hα0])
      _ = Real.log 3 ^ α * |Real.log ε| ^ (-α) := by
          rw [Real.div_rpow (abs_nonneg _) hl3.le, Real.rpow_neg hl3.le, Real.rpow_neg (abs_nonneg _)]
          field_simp

/-- Satisfiability: `shom_m = (2 c⋆ log 3 · m)^{1/2}` meets the sharp asymptotics exactly. -/
example : True := by
  have hsh : ∀ m : ℕ, 0 ≤ m → |(fun m : ℕ => (2 * (1 : ℝ) * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)) m -
      (2 * (1 : ℝ) * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
        0 * (1 : ℝ)⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + 0) := by
    intro m _
    simp
  have := s12_scalar_numerics (cStar := 1) (C0 := 0) (Kc := 0) one_pos le_rfl hsh
    (α := 1 / 4) (by norm_num) (by norm_num)
  trivial

/-! ### The right-hand sides (`e.Dir.new.superdiff.basic.rhs`) -/

end SuperdiffusionCLT.Section7
