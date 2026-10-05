/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.RootChainAbsorptionB

/-!
The original law-dependent mixed bound remains open. These scalar estimates
identify a sufficient extra logarithmic contribution and show that it is not
bounded by a constant multiple of the threshold of the main statement. No
shell law is asserted at the scalar counterexample parameters.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

/-- A mixed logarithmic threshold controls the mixed error uniformly. -/
theorem rootChainAbsorptionC_scaled_mixed {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu cStar K L : ℝ,
      0 < nu → 0 < cStar → 0 ≤ K →
      C*(1+K)*(Real.log (3+nu⁻¹+cStar⁻¹)+Real.log (3+nu⁻¹+K)) ≤ cStar^3*L →
      (1+K)*Real.log (nu⁻¹*L) ≤ eps*(cStar^3*L) := by
  have hlim : Filter.Tendsto (fun y : ℝ => Real.log y / y)
      Filter.atTop (nhds 0) := by
    simpa only [inv_one, one_mul, pow_one] using
      (masterConstSpecD_log_pow_div_tendsto (nu := 1) (by norm_num) 1)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hlim.eventually_lt_const (by positivity : 0 < eps/2))
  let C := max 1 (max N (8/eps))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hCN : N ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCE : 8/eps ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC1, ?_⟩
  intro nu cStar K L hnu hc hK ht
  let a := Real.log (3+nu⁻¹+cStar⁻¹)
  let b := Real.log (3+nu⁻¹+K)
  let B := 1+K
  let x := cStar^3*L
  let y := x/B
  have hB : 0 < B := by dsimp only [B]; positivity
  have hi : 0 < nu⁻¹ := inv_pos.mpr hnu
  have hci : 0 < cStar⁻¹ := inv_pos.mpr hc
  have ha : 1 ≤ a := by
    apply le_trans (show (1 : ℝ) ≤ Real.log 3 from (by
      apply le_of_lt
      apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).mpr
      exact Real.exp_one_lt_d9.trans (by norm_num)))
    exact Real.log_le_log (by norm_num) (by linarith only [hi,hci])
  have hb : 0 ≤ b := Real.log_nonneg (by linarith only [hi,hK])
  have hab : 1 ≤ a+b := by linarith only [ha,hb]
  have hCy : C*(a+b) ≤ y := by
    apply (le_div_iff₀ hB).mpr
    change C*B*(a+b) ≤ x at ht
    nlinarith only [ht]
  have hCyle : C ≤ y := by
    have hh := mul_le_mul_of_nonneg_left hab hCp.le
    linarith only [hh,hCy]
  have hy : 0 < y := hCp.trans_le hCyle
  have hxy : x = B*y := by dsimp only [y]; field_simp
  have hx : 0 < x := by rw [hxy]; exact mul_pos hB hy
  have hL : 0 < L := (mul_pos_iff_of_pos_left (pow_pos hc 3)).mp hx
  have hlogsmall : Real.log y ≤ eps/2*y := by
    exact ((div_lt_iff₀ hy).mp (hN y (hCN.trans hCyle))).le
  have hbudget : 4*(a+b) ≤ eps/2*y := by
    have hEC : 8 ≤ C*eps := (div_le_iff₀ heps).mp hCE
    have hh := mul_le_mul_of_nonneg_right hEC (show 0 ≤ a+b by linarith only [hab])
    have hh' := mul_le_mul_of_nonneg_left hCy heps.le
    nlinarith only [hh,hh']
  have hlognu : Real.log nu⁻¹ ≤ a :=
    Real.log_le_log hi (by linarith only [hci])
  have hlogc : Real.log cStar⁻¹ ≤ a :=
    Real.log_le_log hci (by linarith only [hi])
  have hlogB : Real.log B ≤ b :=
    Real.log_le_log hB (by dsimp only [B]; linarith only [hi])
  have hlogid : Real.log (nu⁻¹*L) =
      Real.log nu⁻¹+3*Real.log cStar⁻¹+Real.log x := by
    dsimp only [x]
    rw [Real.log_mul (inv_ne_zero hnu.ne') hL.ne',
      Real.log_mul (pow_ne_zero _ hc.ne') hL.ne', Real.log_pow, Real.log_inv]
    norm_num only [Nat.cast_ofNat, Real.log_inv]
    ring
  have hlogx : Real.log x = Real.log B+Real.log y := by
    rw [hxy, Real.log_mul hB.ne' hy.ne']
  have hg : Real.log (nu⁻¹*L) ≤ eps*y := by
    linarith only [hlogid,hlogx,hlognu,hlogc,hlogB,hb,hbudget,hlogsmall]
  have hh := mul_le_mul_of_nonneg_left hg hB.le
  change B*Real.log (nu⁻¹*L) ≤ eps*x
  rw [hxy]
  nlinarith only [hh]

/-- Adding the mixed logarithm to the threshold suffices for the mixed-error bound.
This is a sufficient scalar estimate, not a modification of the main statement. -/
theorem rootChainAbsorptionC_augmented_threshold {CM A : ℝ}
    (hCM : 0 < CM) (hA : 0 < A) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu cStar K : ℝ,
      0 < nu → 0 < cStar → 0 ≤ K →
      ∀ L m : ℕ, m ≤ L →
      C*cStar ^ (-(3 : ℝ))*(eLvsNuTerm nu cStar K+
        (1+K)*Real.log (3+nu⁻¹+cStar⁻¹)) ≤ (m : ℝ) →
      8*CM*(1+K)*Real.log (nu⁻¹*(L : ℝ)) ≤ A*cStar^3*(L : ℝ) := by
  have hden : 0 < 8*CM := by positivity
  obtain ⟨C, hC, hscaled⟩ := rootChainAbsorptionC_scaled_mixed (div_pos hA hden)
  refine ⟨C, hC, ?_⟩
  intro nu cStar K hnu hc hK L m hm hthr
  let T := eLvsNuTerm nu cStar K+(1+K)*Real.log (3+nu⁻¹+cStar⁻¹)
  have hcancel : cStar ^ (-(3 : ℝ))*cStar^(3 : ℕ) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hc]
    norm_num
  have ht := mul_le_mul_of_nonneg_right hthr (pow_nonneg hc.le 3)
  have heq : C*cStar ^ (-(3 : ℝ))*T*cStar^3 =
      C*T*(cStar ^ (-(3 : ℝ))*cStar^3) := by ring
  change C*cStar ^ (-(3 : ℝ))*T*cStar^3 ≤ (m : ℝ)*cStar^3 at ht
  rw [heq, hcancel, mul_one] at ht
  have hterm : (1+K)*(Real.log (3+nu⁻¹+cStar⁻¹)+Real.log (3+nu⁻¹+K)) ≤ T := by
    have ht1 := eLvsNuTerm_term_one_nonneg hnu hc
    dsimp only [T, eLvsNuTerm]
    nlinarith only [ht1]
  have htarget : C*(1+K)*(Real.log (3+nu⁻¹+cStar⁻¹)+Real.log (3+nu⁻¹+K)) ≤
      cStar^3*(L : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hterm (zero_le_one.trans hC)
    have hm' := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hm : (m : ℝ) ≤ (L : ℝ))
      (pow_nonneg hc.le 3)
    nlinarith only [hh,ht,hm']
  have hh := mul_le_mul_of_nonneg_left
    (hscaled nu cStar K (L : ℝ) hnu hc hK htarget) hden.le
  calc
    _ ≤ (8*CM)*(A/(8*CM)*(cStar^3*(L : ℝ))) := by
      simpa only [mul_assoc] using hh
    _ = _ := by
      rw [← mul_assoc, mul_div_cancel₀ _ hden.ne']
      ring

/-- Including `cStar⁻¹` in the error-parameter logarithm is a sufficient scalar
threshold for the mixed error. No claim about the threshold of the main statement is made. -/
theorem rootChainAbsorptionC_joint_log_threshold {CM A : ℝ}
    (hCM : 0 < CM) (hA : 0 < A) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu cStar K : ℝ,
      0 < nu → 0 < cStar → 0 ≤ K →
      ∀ L m : ℕ, m ≤ L →
      C*cStar ^ (-(3 : ℝ))*(
        Real.log (3+nu⁻¹+cStar⁻¹)^3*Real.log (Real.log (3+nu⁻¹+cStar⁻¹))+
        (1+K)*Real.log (3+nu⁻¹+cStar⁻¹+K)) ≤ (m : ℝ) →
      8*CM*(1+K)*Real.log (nu⁻¹*(L : ℝ)) ≤ A*cStar^3*(L : ℝ) := by
  obtain ⟨C, hC, haug⟩ := rootChainAbsorptionC_augmented_threshold hCM hA
  refine ⟨2*C, by linarith only [hC], ?_⟩
  intro nu cStar K hnu hc hK L m hm hthr
  apply haug nu cStar K hnu hc hK L m hm
  have hi := inv_pos.mpr hnu
  have hci := inv_pos.mpr hc
  have ha : Real.log (3+nu⁻¹+cStar⁻¹) ≤ Real.log (3+nu⁻¹+cStar⁻¹+K) :=
    Real.log_le_log (by positivity) (by linarith only [hK])
  have hb : Real.log (3+nu⁻¹+K) ≤ Real.log (3+nu⁻¹+cStar⁻¹+K) :=
    Real.log_le_log (by positivity) (by linarith only [hci])
  have hB : 0 ≤ 1+K := by linarith only [hK]
  have hterm : eLvsNuTerm nu cStar K+(1+K)*Real.log (3+nu⁻¹+cStar⁻¹) ≤
      2*(Real.log (3+nu⁻¹+cStar⁻¹)^3*Real.log (Real.log (3+nu⁻¹+cStar⁻¹))+
        (1+K)*Real.log (3+nu⁻¹+cStar⁻¹+K)) := by
    have h1 := eLvsNuTerm_term_one_nonneg hnu hc
    have h2 := mul_le_mul_of_nonneg_left ha hB
    have h3 := mul_le_mul_of_nonneg_left hb hB
    dsimp only [eLvsNuTerm]
    linarith only [h1,h2,h3]
  have hh := mul_le_mul_of_nonneg_left hterm
    (mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hc.le (-(3 : ℝ))))
  calc
    _ ≤ C*cStar ^ (-(3 : ℝ))*(2*(
        Real.log (3+nu⁻¹+cStar⁻¹)^3*Real.log (Real.log (3+nu⁻¹+cStar⁻¹))+
        (1+K)*Real.log (3+nu⁻¹+cStar⁻¹+K))) := hh
    _ = 2*C*cStar ^ (-(3 : ℝ))*(
        Real.log (3+nu⁻¹+cStar⁻¹)^3*Real.log (Real.log (3+nu⁻¹+cStar⁻¹))+
        (1+K)*Real.log (3+nu⁻¹+cStar⁻¹+K)) := by ring
    _ ≤ _ := hthr

/-- The joint logarithm suffices for full absorption, including the log-square term.
The threshold here is explicitly stronger than that of the main statement. -/
theorem rootChainAbsorptionC_full_joint_log_threshold {CM Ks A : ℝ}
    (hCM : 0 < CM) (hKs : 0 < Ks) (hA : 0 < A) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu cStar K : ℝ,
      0 < nu → nu ≤ 1 → 0 < cStar → cStar ≤ 2 → 0 < K →
      ∀ L m : ℕ, m ≤ L →
      C*cStar ^ (-(3 : ℝ))*(
        Real.log (3+nu⁻¹+cStar⁻¹)^3*Real.log (Real.log (3+nu⁻¹+cStar⁻¹))+
        (1+K)*Real.log (3+nu⁻¹+cStar⁻¹+K)) ≤ (m : ℝ) →
      4*CM*(1+K+Ks*Real.log (nu⁻¹*(L : ℝ)))*Real.log (nu⁻¹*(L : ℝ)) ≤
        A*cStar^3*(L : ℝ) := by
  obtain ⟨C₀, hC₀, hreduce⟩ := rootChainAbsorptionB_mixed_reduction hCM hKs hA
  obtain ⟨C₁, _hC₁, hmixed⟩ := rootChainAbsorptionC_joint_log_threshold hCM hA
  refine ⟨max C₀ C₁, hC₀.trans (le_max_left _ _), ?_⟩
  intro nu cStar K hnu hnu1 hc hc2 hK L m hm ht
  let T := Real.log (3+nu⁻¹+cStar⁻¹)^3*Real.log (Real.log (3+nu⁻¹+cStar⁻¹))+
    (1+K)*Real.log (3+nu⁻¹+cStar⁻¹+K)
  have hlog : Real.log (3+nu⁻¹+K) ≤ Real.log (3+nu⁻¹+cStar⁻¹+K) :=
    Real.log_le_log (by positivity) (by have hi := inv_pos.mpr hc; linarith only [hi])
  have hT : eLvsNuTerm nu cStar K ≤ T := by
    have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 1+K)
    dsimp only [eLvsNuTerm,T]
    linarith only [hh]
  have hTpos : 0 ≤ T := (eLvsNuTerm_pos hnu hc hK.le).le.trans hT
  have hthr₀ : C₀*cStar ^ (-(3 : ℝ))*eLvsNuTerm nu cStar K ≤ (m : ℝ) := by
    apply le_trans _ ht
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hc.le _))
      hT (eLvsNuTerm_pos hnu hc hK.le).le
      (mul_nonneg (zero_le_one.trans (hC₀.trans (le_max_left _ _)))
        (Real.rpow_nonneg hc.le _))
  have hthr₁ : C₁*cStar ^ (-(3 : ℝ))*T ≤ (m : ℝ) := by
    apply le_trans _ ht
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hc.le _)) hTpos
  exact hreduce nu cStar K hnu hnu1 hc hc2 hK L m hm hthr₀
    (hmixed nu cStar K hnu hc hK.le L m hm hthr₁)

end SuperdiffusionCLT.Section3.Setup
