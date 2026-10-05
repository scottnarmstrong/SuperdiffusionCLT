/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.LinftyReductionB
public import SuperdiffusionCLT.Section7.Analytic.CZ.Uniform

/-!
# Bookkeeping for the conclusion (display `e.Dir.new.Linfty.smooth.weak`)

The normalized `H^{-1}` norm is bounded by the normalized `L²` norm (with the scale factor of the
domain), subadditive, and so a perturbation of a vector field that is small in `L²` perturbs its
`H^{-1}` seminorm by at most that amount.  `li1_hMinusOneVec` is the sum over components of
`wMinusOneBar U 2`; to be replaced by the root carrier `hMinusOneVec`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem li1_conj_two : (2 : ℝ≥0∞).conjExponent = 2 := by
  have h : (2 : ℝ≥0∞) = 1 + 1 := one_add_one_eq_two.symm
  unfold ENNReal.conjExponent
  rw [show (2 : ℝ≥0∞) - 1 = 1 by
    rw [h]; exact ENNReal.add_sub_cancel_left ENNReal.one_ne_top]
  simp only [inv_one]
  exact h.symm

theorem li1_lpBar_two_eq {E : Type*} [NormedAddCommGroup E] (V : Set (Vec d)) (F : Vec d → E)
    (hF : AEStronglyMeasurable F (volume.restrict V))
    (h0 : volume V ≠ 0) (ht : volume V ≠ ⊤) :
    lpBar V 2 F = (volume V)⁻¹ ^ (1 / 2 : ℝ) * eLpNorm F 2 (volume.restrict V) := by
  have _ := h0
  have _ := ht
  unfold lpBar
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num) F]
  · simp [one_div]
  · exact hF

theorem li1_pairing_le (U : Set (Vec d)) (h u : Vec d → ℝ) (hh : MemLp h 2 (volume.restrict U))
    (hu : MemLp u 2 (volume.restrict U)) :
    ENNReal.ofReal |∫ x in U, h x * u x| ≤
      eLpNorm h 2 (volume.restrict U) * eLpNorm u 2 (volume.restrict U) := by
  have h1 : ENNReal.ofReal |∫ x in U, h x * u x| ≤ ∫⁻ x in U, ‖h x * u x‖ₑ := by
    rw [← Real.enorm_eq_ofReal_abs]
    exact enorm_integral_le_lintegral_enorm _
  have h2 : eLpNorm (fun x => h x * u x) 1 (volume.restrict U) ≤
      ((1 : ℝ≥0) : ℝ≥0∞) * eLpNorm h 2 (volume.restrict U) * eLpNorm u 2 (volume.restrict U) :=
    eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 2) (q := 2) (r := 1) (fun a b : ℝ => a * b) 1
      (by fun_prop) hh.aestronglyMeasurable hu.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by simp)
  rw [eLpNorm_one_eq_lintegral_enorm (f := fun x => h x * u x)
    (hh.aestronglyMeasurable.mul hu.aestronglyMeasurable)] at h2
  simpa using h1.trans h2

theorem li1_sqrt_inv_mul_self (m : ℝ≥0∞) (h0 : m ≠ 0) (ht : m ≠ ⊤) :
    (m⁻¹ ^ (1 / 2 : ℝ)) * (m⁻¹ ^ (1 / 2 : ℝ)) = ENNReal.ofReal m.toReal⁻¹ := by
  have hi0 : m⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ht
  have hit : m⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr h0
  rw [← ENNReal.rpow_add _ _ hi0 hit, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
    ENNReal.rpow_one, ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos h0 ht),
    ENNReal.ofReal_toReal ht]

theorem li1_grad_aesm {U : Set (Vec d)} (ψ : H10Function U) :
    AEStronglyMeasurable ψ.toH1Function.grad (volume.restrict U) := by
  refine AEMeasurable.aestronglyMeasurable (aemeasurable_pi_iff.mpr fun i => ?_)
  exact (ψ.toH1Function.gradMemL2 i).aestronglyMeasurable.aemeasurable

theorem li1_wMinusOneBar_two_le_lpBar [NeZero d] :
    ∃ c : ℝ, 0 < c ∧ ∀ {U : Set (Vec d)}, IsOpen U → ∀ (z : Vec d) {L : ℝ}, 0 < L →
      U ⊆ axisCube z L → volume U ≠ 0 →
      ∀ h : Vec d → ℝ, MemLp h 2 (volume.restrict U) →
        wMinusOneBar U 2 h ≤ ENNReal.ofReal (c * L) * lpBar U 2 h := by
  obtain ⟨c, hc, hP⟩ := p13_poincare (d := d)
  refine ⟨c, hc, fun {U} hU z {L} hL hsub h0 h hh => ?_⟩
  have ht : volume U ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
    rw [axisCube, Real.volume_pi_Ioo]
    exact ENNReal.prod_lt_top (fun i _ => ENNReal.ofReal_lt_top) |>.ne
  have hA : eLpNorm h 2 (volume.restrict U) ≠ ⊤ := hh.eLpNorm_ne_top
  rw [li1_lpBar_two_eq U h hh.aestronglyMeasurable h0 ht]
  unfold wMinusOneBar
  refine iSup₂_le fun ψ hψ => ?_
  rw [li1_conj_two, li1_lpBar_two_eq U _ (li1_grad_aesm ψ) h0 ht] at hψ
  set k : ℝ≥0∞ := (volume U)⁻¹ ^ (1 / 2 : ℝ) with hk
  have hkk := li1_sqrt_inv_mul_self (volume U) h0 ht
  have hpair := li1_pairing_le U h ψ.toH1Function.toFun hh ψ.toH1Function.memL2
  have hpo := hP hU z hL hsub ψ
  rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg),
    ← hkk]
  calc k * k * ENNReal.ofReal |∫ x in U, h x * ψ.toH1Function.toFun x|
      ≤ k * k * (eLpNorm h 2 (volume.restrict U) *
          (ENNReal.ofReal (c * L) * eLpNorm ψ.toH1Function.grad 2 (volume.restrict U))) := by
        gcongr
        exact hpair.trans (by gcongr)
    _ = (k * eLpNorm ψ.toH1Function.grad 2 (volume.restrict U)) * k *
          (ENNReal.ofReal (c * L) * eLpNorm h 2 (volume.restrict U)) := by ring
    _ ≤ 1 * k * (ENNReal.ofReal (c * L) * eLpNorm h 2 (volume.restrict U)) := by gcongr
    _ = ENNReal.ofReal (c * L) * (k * eLpNorm h 2 (volume.restrict U)) := by ring


/-- `wMinusOneBar` is subadditive on `L²` functions. -/
theorem li1_wMinusOneBar_add_le (V : Set (Vec d)) (h₁ h₂ : Vec d → ℝ)
    (m₁ : MemLp h₁ 2 (volume.restrict V)) (m₂ : MemLp h₂ 2 (volume.restrict V)) :
    wMinusOneBar V 2 (fun x => h₁ x + h₂ x) ≤ wMinusOneBar V 2 h₁ + wMinusOneBar V 2 h₂ := by
  unfold wMinusOneBar
  refine iSup₂_le fun ψ hψ => ?_
  have hi : ∀ h : Vec d → ℝ, MemLp h 2 (volume.restrict V) →
      Integrable (fun x => h x * ψ.toH1Function.toFun x) (volume.restrict V) := fun h hh =>
    hh.integrable_mul ψ.toH1Function.memL2
  have hsplit : (volume V).toReal⁻¹ * ∫ x in V, (h₁ x + h₂ x) * ψ.toH1Function.toFun x =
      (volume V).toReal⁻¹ * (∫ x in V, h₁ x * ψ.toH1Function.toFun x) +
        (volume V).toReal⁻¹ * (∫ x in V, h₂ x * ψ.toH1Function.toFun x) := by
    rw [← mul_add, ← integral_add (hi h₁ m₁) (hi h₂ m₂)]
    simp only [add_mul]
  rw [hsplit]
  refine (ENNReal.ofReal_le_ofReal (abs_add_le _ _)).trans ?_
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact add_le_add (le_iSup₂ (f := fun (ψ : H10Function V) (_ : lpBar V (2 : ℝ≥0∞).conjExponent
      ψ.toH1Function.grad ≤ 1) => ENNReal.ofReal |(volume V).toReal⁻¹ *
        ∫ x in V, h₁ x * ψ.toH1Function.toFun x|) ψ hψ)
    (le_iSup₂ (f := fun (ψ : H10Function V) (_ : lpBar V (2 : ℝ≥0∞).conjExponent
      ψ.toH1Function.grad ≤ 1) => ENNReal.ofReal |(volume V).toReal⁻¹ *
        ∫ x in V, h₂ x * ψ.toH1Function.toFun x|) ψ hψ)

/-- The `H^{-1}(U)` seminorm of a vector field (sum over components of `wMinusOneBar U 2`);
to be replaced by the root carrier. -/
noncomputable def li1_hMinusOneVec (U : Set (Vec d)) (F : Vec d → Vec d) : ℝ≥0∞ :=
  ∑ i : Fin d, wMinusOneBar U 2 (fun x => F x i)

/-- **Perturbation of the `H^{-1}` seminorm by an `L²`-small field** (T:12899): if `F` and `F'`
differ by `D` with components in `L²(U)`, then `[F]_{H^{-1}} ≤ [F']_{H^{-1}} + c L Σ ‖D_i‖_{L̲²}`
on a domain `U ⊆ axisCube z L`. -/
theorem li1_hMinusOneVec_perturb [NeZero d] :
    ∃ c : ℝ, 0 < c ∧ ∀ {U : Set (Vec d)}, IsOpen U → ∀ (z : Vec d) {L : ℝ}, 0 < L →
      U ⊆ axisCube z L → volume U ≠ 0 → ∀ (F F' : Vec d → Vec d),
      (∀ i, MemLp (fun x => F' x i) 2 (volume.restrict U)) →
      (∀ i, MemLp (fun x => F x i - F' x i) 2 (volume.restrict U)) →
        li1_hMinusOneVec U F ≤ li1_hMinusOneVec U F' +
          ENNReal.ofReal (c * L) * ∑ i : Fin d, lpBar U 2 (fun x => F x i - F' x i) := by
  obtain ⟨c, hc, h⟩ := li1_wMinusOneBar_two_le_lpBar (d := d)
  refine ⟨c, hc, fun {U} hU z {L} hL hsub h0 F F' m' md => ?_⟩
  unfold li1_hMinusOneVec
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hF : (fun x => F x i) = fun x => F' x i + (F x i - F' x i) := by
    funext x; ring
  rw [hF]
  exact (li1_wMinusOneBar_add_le U _ _ (m' i) (md i)).trans
    (add_le_add_right (h hU z hL hsub h0 _ (md i)) _)

/-- **Bookkeeping for the `L^∞` term** (T:12864, `e.Dir.new.Linfty.homog`): if the problem with the
smooth datum `g̃` has `|v - vhom| ≤ E` a.e. and the data `g, g̃` differ by at most `c` everywhere,
then `|u - uhom| ≤ E + 2c` a.e., for solutions with the original datum `g` of the same
right-hand side, for the oscillating field `a` and the homogenized field `ahom`. -/
theorem li1_linfty_bookkeeping [NeZero d] {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : IsBoundedDomain U) {lam Lam lamh Lamh : ℝ} {a ahom : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (hEllh : IsEllipticFieldOn lamh Lamh U ahom)
    {f : Vec d → ℝ} (g gt u v uhom vhom : H1Function U)
    (hu : IsWeakSolutionOn a U u f 0) (mu : MemH10 U (fun x => u.toFun x - g.toFun x))
    (hv : IsWeakSolutionOn a U v f 0) (mv : MemH10 U (fun x => v.toFun x - gt.toFun x))
    (hh : IsWeakSolutionOn ahom U uhom f 0) (mh : MemH10 U (fun x => uhom.toFun x - g.toFun x))
    (hvh : IsWeakSolutionOn ahom U vhom f 0)
    (mvh : MemH10 U (fun x => vhom.toFun x - gt.toFun x)) {c E : ℝ}
    (hc : ∀ x, |g.toFun x - gt.toFun x| ≤ c)
    (hE : ∀ᵐ x ∂(volume.restrict U), |v.toFun x - vhom.toFun x| ≤ E) :
    ∀ᵐ x ∂(volume.restrict U), |u.toFun x - uhom.toFun x| ≤ E + 2 * c := by
  have e1 := li1_linfty_comparison hU hUb hEll g gt u v hu mu hv mv hc
  have e2 := li1_linfty_comparison hU hUb hEllh g gt uhom vhom hh mh hvh mvh hc
  filter_upwards [e1, e2, hE] with x a1 a2 a3
  have : u.toFun x - uhom.toFun x = (u.toFun x - v.toFun x) + (v.toFun x - vhom.toFun x) +
      (vhom.toFun x - uhom.toFun x) := by ring
  rw [this]
  have b1 := abs_add_le ((u.toFun x - v.toFun x) + (v.toFun x - vhom.toFun x))
    (vhom.toFun x - uhom.toFun x)
  have b2 := abs_add_le (u.toFun x - v.toFun x) (v.toFun x - vhom.toFun x)
  rw [abs_sub_comm (vhom.toFun x)] at b1
  linarith only [b1, b2, a1, a2, a3]

/-- Witness for the perturbation lemma: the zero field on the cube `axisCube 0 1`. -/
example : ∃ c : ℝ, 0 < c ∧ li1_hMinusOneVec (axisCube (0 : Vec 2) 1) (fun _ => 0) ≤
    li1_hMinusOneVec (axisCube (0 : Vec 2) 1) (fun _ => 0) +
      ENNReal.ofReal (c * 1) * ∑ i : Fin 2, lpBar (axisCube (0 : Vec 2) 1) 2
        (fun x => (fun _ : Vec 2 => (0 : Vec 2)) x i - (fun _ : Vec 2 => (0 : Vec 2)) x i) := by
  obtain ⟨c, hc, h⟩ := li1_hMinusOneVec_perturb (d := 2)
  have hne : volume (axisCube (0 : Vec 2) 1) ≠ 0 := by
    rw [axisCube, Real.volume_pi_Ioo]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    simp
  exact ⟨c, hc, h (isOpen_axisCube (0 : Vec 2) 1) 0 one_pos subset_rfl hne (fun _ => 0)
    (fun _ => 0) (fun i => by simp) (fun i => by simp)⟩

/-- Witness for the `L^∞` bookkeeping: zero data and zero solutions on the unit ball. -/
example : ∀ᵐ x ∂(volume.restrict (Section6.euclidBall (d := 2) 1)),
    |(0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x -
      (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x| ≤ 0 + 2 * 0 := by
  have hz : IsWeakSolutionOn (fun _ => (1 : Mat 2)) (Section6.euclidBall (d := 2) 1)
      (0 : H1Function (Section6.euclidBall (d := 2) 1)) 0 0 := by
    intro φ
    have h0 : ∀ x, (0 : H1Function (Section6.euclidBall (d := 2) 1)).grad x = 0 := fun _ => rfl
    simp [vecDot, matVecMul, h0]
  have hm : MemH10 (Section6.euclidBall (d := 2) 1) (fun x =>
      (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x -
        (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x) := by
    have : (fun x => (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x -
        (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x) = 0 := by
      funext x; simp
    rw [this]
    exact memH10_zero
  exact li1_linfty_bookkeeping (Section6.isOpen_euclidBall (d := 2) 1)
    (isBoundedDomain_euclidBall one_pos) isEllipticFieldOn_one_euclidBall
    isEllipticFieldOn_one_euclidBall 0 0 0 0 0 0 hz hm hz hm hz hm hz hm (c := 0) (E := 0)
    (fun x => by simp) (Filter.Eventually.of_forall fun x => by simp)

end SuperdiffusionCLT.Section7
