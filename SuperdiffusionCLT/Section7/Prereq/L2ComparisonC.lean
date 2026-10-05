/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2ComparisonB

/-!
# The mollified function as an `H¹` function, and the comparison function `w`

Display `e.Dir.new.w.def`: for `H¹(ℝᵈ)` data `ũ`
(the extension of `u` by `g`) and `g̃` (the extension of `g`), a bounded open `W`, and a cutoff `ζ`
compactly supported in `W`,
`w = ζ (η_h ∗ ũ) + (1 - ζ) g̃` is an `H¹(W)` function, `w - g̃ = ζ (η_h ∗ ũ - g̃)` is in `H¹₀(W)`,
and `∇ w = ζ η_h ∗ ∇ũ + (1 - ζ) ∇g̃ + ∇ζ (η_h ∗ ũ - g̃)` (`l2a_wH1_grad`).
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal Convolution

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- A continuous function is in `L²` of a bounded measurable set. -/
theorem l2a_memL2_of_continuous {W : Set (Vec d)} (hWm : MeasurableSet W)
    (hW : Bornology.IsBounded W) {f : Vec d → ℝ} (hf : Continuous f) : MemL2On W f := by
  obtain ⟨B, hB⟩ := hW.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  have : IsFiniteMeasure (volume.restrict W) := ⟨by simpa using hW.measure_lt_top⟩
  refine MemLp.of_bound hf.aestronglyMeasurable B ?_
  rw [ae_restrict_iff' hWm]
  exact Filter.Eventually.of_forall fun x hx => hB x (subset_closure hx)

/-- An `L²(ℝᵈ)` function is locally integrable. -/
theorem l2a_locInt_of_memL2_univ {f : Vec d → ℝ} (hf : MemL2On (Set.univ : Set (Vec d)) f) :
    LocallyIntegrable f volume := by
  have : MemLp f 2 volume := by simpa [MemL2On, Measure.restrict_univ] using hf
  exact this.locallyIntegrable (by norm_num)

section Moll

variable {W : Set (Vec d)} {h : ℝ} {η : Vec d → ℝ}

/-- **The mollification of a whole-space `H¹` function is an `H¹(W)` function** on a bounded open
`W`, with gradient the mollified gradient. -/
noncomputable def l2a_mollH1 (hW : IsOpen W) (hWb : Bornology.IsBounded W) (hh : 0 < h)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0) (u : H1Function (Set.univ : Set (Vec d))) :
    H1Function W where
  toFun := l2a_moll d h η u.toFun
  grad := fun x i => l2a_moll d h η (fun y => u.grad y i) x
  memL2 := l2a_memL2_of_continuous hW.measurableSet hWb
    (l2a_moll_contDiff hh hη hη0 (l2a_locInt_of_memL2_univ u.memL2)).continuous
  gradMemL2 := fun i => l2a_memL2_of_continuous hW.measurableSet hWb
    (l2a_moll_contDiff hh hη hη0
      (l2a_locInt_of_memL2_univ (u.gradMemL2 i))).continuous
  hasWeakGradient := fun i => by
    have hcd := (l2a_moll_contDiff hh hη hη0 (l2a_locInt_of_memL2_univ u.memL2)).of_le
      (show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast le_top)
    have := HasWeakPartialDerivOn.of_contDiff (U := W) (i := i) hcd
    have e : (fun x => fderiv ℝ (l2a_moll d h η u.toFun) x (basisVec i)) =
        fun x => l2a_moll d h η (fun y => u.grad y i) x :=
      funext fun x => l2a_fderiv_moll hh hη hη0 (l2a_locInt_of_memL2_univ u.memL2)
        (u.hasWeakGradient i) x
    rwa [e] at this

@[simp] theorem l2a_mollH1_toFun (hW : IsOpen W) (hWb : Bornology.IsBounded W) (hh : 0 < h)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    (u : H1Function (Set.univ : Set (Vec d))) :
    (l2a_mollH1 hW hWb hh hη hη0 u).toFun = l2a_moll d h η u.toFun := rfl

@[simp] theorem l2a_mollH1_grad (hW : IsOpen W) (hWb : Bornology.IsBounded W) (hh : 0 < h)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    (u : H1Function (Set.univ : Set (Vec d))) :
    (l2a_mollH1 hW hWb hh hη hη0 u).grad =
      fun x i => l2a_moll d h η (fun y => u.grad y i) x := rfl

theorem l2a_lipschitz_one_sub {K : ℝ≥0} {ζ : Vec d → ℝ} (hζ : LipschitzWith K ζ) :
    LipschitzWith K (fun x => 1 - ζ x) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have := hζ.dist_le_mul x y
  rw [Real.dist_eq] at this ⊢
  have e : (1 - ζ x) - (1 - ζ y) = -(ζ x - ζ y) := by ring
  rw [e, abs_neg]
  exact this

theorem l2a_lipGradient_one_sub (ζ : Vec d → ℝ) (x : Vec d) :
    lipGradient (fun y => 1 - ζ y) x = -lipGradient ζ x := by
  funext i
  simp [lipGradient, fderiv_const_sub]

/-- **The comparison function** `w = ζ (η_h ∗ ũ) + (1 - ζ) g` as an `H¹(W)` function
(`e.Dir.new.w.def`). -/
noncomputable def l2a_wH1 (hW : IsOpen W) (hWb : Bornology.IsBounded W) (hh : 0 < h)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    (u : H1Function (Set.univ : Set (Vec d))) (g : H1Function W) {K : ℝ≥0} {ζ : Vec d → ℝ}
    (hζ : LipschitzWith K ζ) (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1) : H1Function W :=
  mulLip hW (l2a_mollH1 hW hWb hh hη hη0 u) (M := 1) hζ (fun x => by
      rw [abs_of_nonneg (hζ0 x)]; exact hζ1 x) +
    mulLip hW g (M := 1) (l2a_lipschitz_one_sub hζ) (fun x => by
      rw [abs_of_nonneg (by linarith only [hζ1 x])]; linarith only [hζ0 x])

theorem l2a_wH1_toFun (hW : IsOpen W) (hWb : Bornology.IsBounded W) (hh : 0 < h)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    (u : H1Function (Set.univ : Set (Vec d))) (g : H1Function W) {K : ℝ≥0} {ζ : Vec d → ℝ}
    (hζ : LipschitzWith K ζ) (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1) (x : Vec d) :
    (l2a_wH1 hW hWb hh hη hη0 u g hζ hζ0 hζ1).toFun x =
      ζ x * l2a_moll d h η u.toFun x + (1 - ζ x) * g.toFun x := rfl

/-- **The product rule** `∇w = ζ η_h ∗ ∇ũ + (1 - ζ) ∇g + (η_h ∗ ũ - g) ∇ζ`, valid everywhere
for the a.e. gradient `lipGradient ζ` of the cutoff (`e.Dir.new.convolution.identity`). -/
theorem l2a_wH1_grad (hW : IsOpen W) (hWb : Bornology.IsBounded W) (hh : 0 < h)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    (u : H1Function (Set.univ : Set (Vec d))) (g : H1Function W) {K : ℝ≥0} {ζ : Vec d → ℝ}
    (hζ : LipschitzWith K ζ) (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1) (x : Vec d) :
    (l2a_wH1 hW hWb hh hη hη0 u g hζ hζ0 hζ1).grad x =
      ζ x • (fun i => l2a_moll d h η (fun y => u.grad y i) x) + (1 - ζ x) • g.grad x +
        (l2a_moll d h η u.toFun x - g.toFun x) • lipGradient ζ x := by
  have e := l2a_lipGradient_one_sub ζ x
  funext i
  simp only [l2a_wH1, H1Function.add_grad, mulLip_grad, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, l2a_mollH1_toFun, l2a_mollH1_grad, mul_comm]
  rw [e]
  simp only [Pi.neg_apply]
  ring

/-- `w - g = ζ (η_h ∗ ũ - g)` is in `H¹₀(W)` when `ζ` is compactly supported in `W`. -/
noncomputable def l2a_wMinusG (hW : IsOpen W) (hWb : Bornology.IsBounded W) (hh : 0 < h)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    (u : H1Function (Set.univ : Set (Vec d))) (g : H1Function W) {K : ℝ≥0} {ζ : Vec d → ℝ}
    (hζ : LipschitzWith K ζ) (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1)
    (hc : HasCompactSupport ζ) (hs : tsupport ζ ⊆ W) : H10Function W :=
  mulLipH10 hW (l2a_mollH1 hW hWb hh hη hη0 u - g) (M := 1) hζ (fun x => by
      rw [abs_of_nonneg (hζ0 x)]; exact hζ1 x) hc hs

theorem l2a_wMinusG_toH1Function (hW : IsOpen W) (hWb : Bornology.IsBounded W) (hh : 0 < h)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    (u : H1Function (Set.univ : Set (Vec d))) (g : H1Function W) {K : ℝ≥0} {ζ : Vec d → ℝ}
    (hζ : LipschitzWith K ζ) (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1)
    (hc : HasCompactSupport ζ) (hs : tsupport ζ ⊆ W) :
    (l2a_wMinusG hW hWb hh hη hη0 u g hζ hζ0 hζ1 hc hs).toH1Function =
      l2a_wH1 hW hWb hh hη hη0 u g hζ hζ0 hζ1 - g := by
  apply H1Function.toFunGrad_injective
  have e := l2a_lipGradient_one_sub ζ
  refine Prod.ext ?_ ?_
  · funext x
    simp only [l2a_wMinusG, mulLipH10_toH1Function, mulLip_toFun, H1Function.sub_toFun,
      l2a_wH1_toFun, l2a_mollH1_toFun]
    ring
  · funext x i
    have := l2a_wH1_grad hW hWb hh hη hη0 u g hζ hζ0 hζ1 x
    simp only [l2a_wMinusG, mulLipH10_toH1Function, mulLip_grad, H1Function.sub_grad,
      H1Function.sub_toFun, l2a_mollH1_toFun, l2a_mollH1_grad, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    have hi := congrFun this i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    rw [hi]
    ring

end Moll


theorem l2a_vecDot_three (a b c : ℝ) (X Y Z V : Vec d) :
    vecDot (a • X + b • Y + c • Z) V = a * vecDot X V + b * vecDot Y V + c * vecDot Z V := by
  simp only [vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_ <;>
    exact Finset.sum_congr rfl fun i _ => by ring

theorem l2a_vecDot_two (a b : ℝ) (X Y V : Vec d) :
    vecDot X (a • V + b • Y) = a * vecDot X V + b * vecDot X Y := by
  simp only [vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  refine congrArg₂ _ ?_ ?_ <;> exact Finset.sum_congr rfl fun i _ => by ring

theorem l2a_lipGradient_abs_le {K : ℝ≥0} {ζ : Vec d → ℝ} (hζ : LipschitzWith K ζ) (x : Vec d)
    (i : Fin d) : |lipGradient ζ x i| ≤ K := by
  have h1 : ‖fderiv ℝ ζ x‖ ≤ K := norm_fderiv_le_of_lipschitz ℝ hζ
  have h2 : ‖basisVec (d := d) i‖ = 1 := by simp [basisVec, Pi.norm_single]
  have h3 : ‖fderiv ℝ ζ x (basisVec i)‖ ≤ K := by
    calc ‖fderiv ℝ ζ x (basisVec i)‖ ≤ ‖fderiv ℝ ζ x‖ * ‖basisVec (d := d) i‖ :=
          (fderiv ℝ ζ x).le_opNorm _
      _ ≤ K := by rw [h2, mul_one]; exact h1
  simpa [lipGradient] using h3

theorem l2a_lipGradient_eq_zero_off {ζ : Vec d → ℝ} {K : Set (Vec d)} (hK : IsClosed K)
    (hζK : ∀ x, x ∉ K → ζ x = 0) {x : Vec d} (hx : x ∉ K) : lipGradient ζ x = 0 := by
  funext i
  have : ζ =ᶠ[nhds x] fun _ => (0 : ℝ) :=
    (hK.isOpen_compl.eventually_mem hx).mono fun y hy => hζK y hy
  simp [lipGradient, this.fderiv_eq]

theorem l2a_integrableOn_of_memL2 {W : Set (Vec d)} (hW : Bornology.IsBounded W) {g : Vec d → ℝ}
    (hg : MemL2On W g) : IntegrableOn g W := by
  have : IsFiniteMeasure (volume.restrict W) := ⟨by simpa using hW.measure_lt_top⟩
  exact hg.integrable (by norm_num)

theorem l2a_integrableOn_mul_memL2 {W : Set (Vec d)} {a b : Vec d → ℝ}
    (ha : MemL2On W a) (hb : MemL2On W b) : IntegrableOn (fun x => a x * b x) W := by
  have := ha.integrable_mul hb
  exact this

theorem l2a_integrableOn_bdd {W : Set (Vec d)} {c g : Vec d → ℝ}
    (hc : AEStronglyMeasurable c volume) {C : ℝ} (hC : ∀ x, ‖c x‖ ≤ C)
    (hg : IntegrableOn g W) : IntegrableOn (fun x => c x * g x) W :=
  Integrable.bdd_mul hg (hc.mono_measure Measure.restrict_le_self)
    (Filter.Eventually.of_forall hC)

end SuperdiffusionCLT.Section7
