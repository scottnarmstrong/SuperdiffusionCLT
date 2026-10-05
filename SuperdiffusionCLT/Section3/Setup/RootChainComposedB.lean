/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.RootChainComposed
public import SuperdiffusionCLT.Section3.Terms.SstarAnnealedResidue
public import SuperdiffusionCLT.Section3.Setup.MasterConstSpecD
public import SuperdiffusionCLT.Section3.Terms.SstarWorkBracket

/-!
# Eight uniform root conditions and the obstruction to the ninth

The threshold of the paper (`l.localization`), with the
nondegeneracy logarithm correction, absorbs eight of the nine scalar
conditions of the root chain at one dimension-only constant.
The lower-order absorption condition is different:
its universal scalar formulation is false at every enlarged constant.

The counterexample takes `nu = 1`, `cStar = exp (-t²)`, `Knd = t⁸`, and
`m = L = ceil (2000 C exp (3t²) t⁹)`. The threshold holds, while multiplying
by `cStar³` leaves order `t⁹` on its right side and order `t¹⁰` in absorption.
This refutes the scalar reduction, not the stochastic conclusion.

The root-specialized theorems preserve the dimension restriction `2 ≤ d`.
No diffusivity conclusion is deduced from the inconsistent ninth condition.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

/-- Six scalar conditions follow uniformly from an enlarged threshold. -/
theorem rootChainComposedB_six_conditions (CM Cenv Ceta CT : ℝ) (hCM : 0 ≤ CM)
    (hCenv : 0 < Cenv) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (nu cStar K : ℝ),
      0 < nu → nu ≤ 1 → 0 < cStar → cStar ≤ 2 → 0 < K →
      ∀ L m : ℕ, m ≤ L →
      C * cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K ≤ (m : ℝ) →
      1 ≤ L ∧ 11 ≤ Real.log (nu⁻¹ * (L : ℝ)) ∧
      Real.log Cenv ≤ Real.log (nu⁻¹ * (L : ℝ)) ∧
      CM * (L : ℝ) ^ (-(500 : ℝ)) ≤ cStar / 8 ∧
      4*Ceta ≤ nu⁻¹ * (L : ℝ) ∧ CT ≤ nu⁻¹ * (L : ℝ) := by
  let D := SuperdiffusionCLT.Section3.Terms.sstarWorkDepthThrConst CM
  let C := max 100000000 (max (8 * max Cenv (max (4*Ceta) CT)) D)
  have hlarge : (100000000 : ℝ) ≤ C := le_max_left _ _
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num) hlarge
  have hD : D ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hscalar : 8 * max Cenv (max (4*Ceta) CT) ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨C, le_trans (by norm_num) hlarge, ?_⟩
  intro nu cStar K hnu hnu1 hc hc2 hK L m hm hthr
  have heighth := SuperdiffusionCLT.Section3.Terms.sstarAnnealedResidue_eighth_le_scale
    hCp.le hnu hnu1 hc hc2 hK hthr
  have hmX := SuperdiffusionCLT.Section3.Terms.sstarAnnealedResidue_scale_le_inv_mul_scale
    hnu hnu1 hm
  have hb : max Cenv (max (4*Ceta) CT) ≤ nu⁻¹ * (L : ℝ) := by
    have hh : max Cenv (max (4*Ceta) CT) ≤ (m : ℝ) := by
      linarith only [hscalar, heighth]
    exact hh.trans hmX
  refine ⟨SuperdiffusionCLT.Section3.Terms.sstarCloseB_one_le_L
    hnu hnu1 hc hc2 hK hlarge hthr hm,
    SuperdiffusionCLT.Section3.Terms.sstarCloseB_eleven_le_log
      hnu hnu1 hc hc2 hK hlarge hthr hm,
    Real.log_le_log hCenv ((le_max_left _ _).trans hb), ?_,
    ((le_max_left _ _).trans (le_max_right _ _)).trans hb,
    ((le_max_right _ _).trans (le_max_right _ _)).trans hb⟩
  apply SuperdiffusionCLT.Section3.Terms.sstarWorkDepthShape_of_thr hCM hc hc2 hCp
    (SuperdiffusionCLT.Section3.Terms.sstarCloseB_eLvsNuTerm_ge_one hnu hnu1 hc hK)
    _ hthr hm
  exact (SuperdiffusionCLT.Section3.Terms.sstarWorkDepthThrConst_pow_ge CM hCM).trans
    (Real.rpow_le_rpow
      (SuperdiffusionCLT.Section3.Terms.sstarWorkDepthThrConst_pos CM).le hD (by norm_num))

/-- Uniform cubic logarithm control after rescaling by the nondegeneracy parameter. -/
theorem rootChainComposedB_log_cube {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu cStar K : ℝ,
      0 < nu → nu ≤ 1 → 0 < cStar → 0 ≤ K →
      ∀ L m : ℕ, m ≤ L →
      C*cStar ^ (-(3 : ℝ))*eLvsNuTerm nu cStar K ≤ (m : ℝ) →
      Real.log (nu⁻¹*(L : ℝ))^3 ≤ eps*(cStar^3*(L : ℝ)) := by
  have hlim := masterConstSpecD_log_pow_div_tendsto (nu := 1) (by norm_num) 3
  have hlim' : Filter.Tendsto (fun x : ℝ => Real.log x ^ 3 / x)
      Filter.atTop (nhds 0) := by simpa only [inv_one, one_mul] using hlim
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hlim'.eventually_lt_const (by positivity : 0 < eps/8))
  let lam := Real.log (Real.log 4)
  have hlog4 : 1 < Real.log (4 : ℝ) :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by
      have h := Real.exp_one_lt_d9
      linarith only [h])
  have hlam : 0 < lam := Real.log_pos hlog4
  let C := max 1 (max (512/(eps*lam)) (max N 1 / lam))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hCeps : 512 ≤ C*(eps*lam) :=
    (div_le_iff₀ (mul_pos heps hlam)).mp ((le_max_left _ _).trans (le_max_right _ _))
  have hCN : max N 1 ≤ C*lam :=
    (div_le_iff₀ hlam).mp ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C, hC1, ?_⟩
  intro nu cStar K hnu hnu1 hc hK L m hm hthr
  let a := Real.log (3+nu⁻¹+cStar⁻¹)
  let x := cStar^3*(L : ℝ)
  have hi : 1 ≤ nu⁻¹ := (one_le_inv₀ hnu).mpr hnu1
  have hb : (4 : ℝ) ≤ 3+nu⁻¹+cStar⁻¹ := by
    have hc' := inv_pos.mpr hc
    linarith only [hi,hc']
  have ha4 : Real.log (4 : ℝ) ≤ a := Real.log_le_log (by norm_num) hb
  have ha1 : 1 ≤ a := hlog4.le.trans ha4
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hla : lam ≤ Real.log a := Real.log_le_log (lt_trans zero_lt_one hlog4) ha4
  have ha3 : 1 ≤ a^3 := one_le_pow₀ ha1
  have ht := (frozenThreshold_term_bounds hnu hc hK hC.le hthr hm).2
  have hax : C*lam*a^3 ≤ x := by
    have h := mul_le_mul_of_nonneg_right hla (mul_nonneg (pow_nonneg ha.le 3) hC.le)
    change a^3*Real.log a*C ≤ (L : ℝ)*cStar^3 at ht
    dsimp only [x]
    nlinarith only [h,ht]
  have hCx : C*lam ≤ x := by
    have h := mul_le_mul_of_nonneg_left ha3 (mul_nonneg hC.le hlam.le)
    linarith only [h,hax]
  have hx1 : 1 ≤ x := (le_max_right _ _).trans (hCN.trans hCx)
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hxN : N ≤ x := (le_max_left _ _).trans (hCN.trans hCx)
  have hsmall : Real.log x^3 ≤ eps/8*x := by
    have h := (div_lt_iff₀ hx).mp (hN x hxN)
    linarith only [h]
  have haSmall : 512*a^3 ≤ eps*x := by
    have h := mul_le_mul_of_nonneg_right hCeps (pow_nonneg ha.le 3)
    have hh := mul_le_mul_of_nonneg_left hax heps.le
    nlinarith only [h,hh]
  have hL : 1 ≤ L := (frozenThreshold_one_le_L hnu hc hK hC1 hthr hm).2
  have hLp : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hprod : 1 ≤ nu⁻¹*(L : ℝ) := by
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    simpa only [one_mul] using mul_le_mul hi hL1 (by norm_num) (inv_pos.mpr hnu).le
  have hg0 : 0 ≤ Real.log (nu⁻¹*(L : ℝ)) := Real.log_nonneg hprod
  have hni : Real.log nu⁻¹ ≤ a := Real.log_le_log (inv_pos.mpr hnu) (by
    have hci := inv_pos.mpr hc
    linarith only [hci])
  have hci : Real.log cStar⁻¹ ≤ a := Real.log_le_log (inv_pos.mpr hc) (by
    linarith only [hi])
  have hlogid : Real.log (nu⁻¹*(L : ℝ)) =
      Real.log nu⁻¹ + 3*Real.log cStar⁻¹ + Real.log x := by
    dsimp only [x]
    rw [Real.log_mul (inv_ne_zero hnu.ne') hLp.ne',
      Real.log_mul (pow_ne_zero _ hc.ne') hLp.ne', Real.log_pow, Real.log_inv]
    norm_num only [Nat.cast_ofNat, Real.log_inv]
    ring
  have hg : Real.log (nu⁻¹*(L : ℝ)) ≤ 4*a+Real.log x := by
    linarith only [hlogid,hni,hci]
  have hgp := pow_le_pow_left₀ hg0 hg 3
  have hadd := add_pow_le (show 0 ≤ 4*a by positivity) (Real.log_nonneg hx1) 3
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_succ, pow_zero, mul_one] at hadd
  have hcube : Real.log (nu⁻¹*(L : ℝ))^3 ≤ 256*a^3+4*Real.log x^3 := by
    nlinarith only [hgp,hadd]
  nlinarith only [hcube,haSmall,hsmall]

/-- Eight scalar conditions hold uniformly above one threshold of the printed shape. -/
theorem rootChainComposedB_eight_conditions (CM Cenv Ceta CT Ks CB c0 : ℝ)
    (hCM : 0 ≤ CM) (hCenv : 0 < Cenv) (hKs : 0 ≤ Ks) (hCB : 0 ≤ CB) (hc0 : 0 < c0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu cStar K : ℝ,
      0 < nu → nu ≤ 1 → 0 < cStar → cStar ≤ 2 → 0 < K →
      ∀ L m : ℕ, m ≤ L →
      C*cStar ^ (-(3 : ℝ))*eLvsNuTerm nu cStar K ≤ (m : ℝ) →
      1 ≤ L ∧ 11 ≤ Real.log (nu⁻¹*(L : ℝ)) ∧
      Real.log Cenv ≤ Real.log (nu⁻¹*(L : ℝ)) ∧
      20*(Ks*Real.log (nu⁻¹*(L : ℝ))^2+1)*
        (Cenv*Real.log (Cenv*(nu⁻¹*(L : ℝ)))) ≤ smallnessParameter c0 cStar*(L : ℝ) ∧
      CM*(L : ℝ) ^ (-(500 : ℝ)) ≤ cStar/8 ∧
      4*CB*Real.log (nu⁻¹*(L : ℝ))^2 ≤ (L : ℝ) ∧
      4*Ceta ≤ nu⁻¹*(L : ℝ) ∧ CT ≤ nu⁻¹*(L : ℝ) := by
  let H := 20*(Ks+1)*Cenv*(|Real.log Cenv|+1)
  have hH : 0 < H := by dsimp only [H]; positivity
  let eps := min (c0/(2*H)) (1/(32*(CB+1)))
  have heps : 0 < eps := lt_min (div_pos hc0 (by positivity)) (by positivity)
  have he1 : H*eps ≤ c0/2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2*H)).mp (min_le_left (c0/(2*H)) (1/(32*(CB+1))))
    change eps*(2*H) ≤ c0 at h
    linarith only [h]
  have he2 : 4*CB*eps ≤ 1/8 := by
    have h := (le_div_iff₀ (by positivity : 0 < 32*(CB+1))).mp
      (min_le_right (c0/(2*H)) (1/(32*(CB+1))))
    change eps*(32*(CB+1)) ≤ 1 at h
    nlinarith only [h,heps]
  obtain ⟨C6,hC6,hsix⟩ := rootChainComposedB_six_conditions CM Cenv Ceta CT hCM hCenv
  obtain ⟨Cg,hCg,hcube⟩ := rootChainComposedB_log_cube heps
  refine ⟨max C6 Cg,hC6.trans (le_max_left _ _),?_⟩
  intro nu cStar K hnu hnu1 hc hc2 hK L m hm hthr
  have hfactor : 0 ≤ cStar ^ (-(3 : ℝ))*eLvsNuTerm nu cStar K :=
    mul_nonneg (Real.rpow_nonneg hc.le _) (eLvsNuTerm_pos hnu hc hK.le).le
  have hthr6 : C6*cStar ^ (-(3 : ℝ))*eLvsNuTerm nu cStar K ≤ (m : ℝ) := by
    have h := mul_le_mul_of_nonneg_right (le_max_left C6 Cg) hfactor
    simpa only [mul_assoc] using h.trans (by simpa only [mul_assoc] using hthr)
  have hthrg : Cg*cStar ^ (-(3 : ℝ))*eLvsNuTerm nu cStar K ≤ (m : ℝ) := by
    have h := mul_le_mul_of_nonneg_right (le_max_right C6 Cg) hfactor
    simpa only [mul_assoc] using h.trans (by simpa only [mul_assoc] using hthr)
  obtain ⟨hL,hlog,henv,hdepth,hloc,hmaster⟩ := hsix nu cStar K hnu hnu1 hc hc2 hK L m hm hthr6
  have hgc := hcube nu cStar K hnu hnu1 hc hK.le L m hm hthrg
  let g := Real.log (nu⁻¹*(L : ℝ))
  have hg : 1 ≤ g := le_trans (by norm_num) hlog
  have hg0 : 0 ≤ g := le_trans zero_le_one hg
  have hg2 : 1 ≤ g^2 := one_le_pow₀ hg
  have hg23 : g^2 ≤ g^3 := pow_le_pow_right₀ hg (by omega)
  have hLp : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hsplit : Real.log (Cenv*(nu⁻¹*(L : ℝ))) = Real.log Cenv+g :=
    Real.log_mul hCenv.ne' (mul_ne_zero (inv_ne_zero hnu.ne') hLp.ne')
  have henvlog : Real.log (Cenv*(nu⁻¹*(L : ℝ))) ≤ (|Real.log Cenv|+1)*g := by
    have h := mul_le_mul_of_nonneg_left hg (abs_nonneg (Real.log Cenv))
    rw [hsplit]
    nlinarith only [h, le_abs_self (Real.log Cenv)]
  have hfirst : Ks*g^2+1 ≤ (Ks+1)*g^2 := by linarith only [hg2]
  have hsecond := mul_le_mul_of_nonneg_left henvlog hCenv.le
  have hcoeff : 0 ≤ 20*(Ks*g^2+1) := by positivity
  have hprod := mul_le_mul_of_nonneg_left hsecond hcoeff
  have hprod2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hfirst (by norm_num : (0 : ℝ) ≤ 20))
    (show 0 ≤ Cenv*((|Real.log Cenv|+1)*g) by positivity)
  have hwindow0 : 20*(Ks*g^2+1)*(Cenv*Real.log (Cenv*(nu⁻¹*(L : ℝ)))) ≤ H*g^3 := by
    dsimp only [H]
    nlinarith only [hprod,hprod2]
  have hcsq : cStar^3 ≤ 2*cStar^2 := by
    have h := mul_le_mul_of_nonneg_right hc2 (sq_nonneg cStar)
    nlinarith only [h]
  have hc3 : cStar^3 ≤ (8 : ℝ) := by
    have h := pow_le_pow_left₀ hc.le hc2 3
    norm_num at h
    exact h
  have hscale : 0 ≤ cStar^3*(L : ℝ) := by positivity
  have hwindow1 := mul_le_mul_of_nonneg_left hgc hH.le
  have hwindow2 := mul_le_mul_of_nonneg_right he1 hscale
  have hwindow3 := mul_le_mul_of_nonneg_right hcsq (show 0 ≤ c0/2*(L : ℝ) by positivity)
  have hbell0 := mul_le_mul_of_nonneg_left hg23 (show 0 ≤ 4*CB by positivity)
  have hbell1 := mul_le_mul_of_nonneg_left hgc (show 0 ≤ 4*CB by positivity)
  have hbell2 := mul_le_mul_of_nonneg_right he2 hscale
  have hbell3 := mul_le_mul_of_nonneg_right hc3 (show 0 ≤ (L : ℝ)/8 by positivity)
  refine ⟨hL,hlog,henv,?_,hdepth,?_,hloc,hmaster⟩
  · change _ ≤ c0*cStar^2*(L : ℝ)
    change g^3 ≤ eps*(cStar^3*(L : ℝ)) at hgc
    change H*g^3 ≤ H*(eps*(cStar^3*(L : ℝ))) at hwindow1
    nlinarith only [hwindow0,hwindow1,hwindow2,hwindow3]
  · change 4*CB*g^2 ≤ (L : ℝ)
    change 4*CB*g^3 ≤ 4*CB*(eps*(cStar^3*(L : ℝ))) at hbell1
    nlinarith only [hbell0,hbell1,hbell2,hbell3]

end SuperdiffusionCLT.Section3.Setup
