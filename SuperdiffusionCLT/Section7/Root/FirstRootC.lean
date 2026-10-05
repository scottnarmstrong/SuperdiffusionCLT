/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.FirstRootB
public import SuperdiffusionCLT.Section7.Prereq.DomainInvariance

/-!
# The deterministic chain of the first root, on one dilated domain

Given the black-box comparison on the dilated domain `W = ε⁻¹ • U`, the two comparison estimates
for the Laplace problems and the centring estimate, the three terms of the root estimate on `U`
are at most `(Ξ_f ‖f‖_{L^∞(U)} + Ξ_g ‖∇g‖_{L^∞(U)})`, with explicit real coefficients.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

/-- The bookkeeping of the four estimates in `ℝ≥0∞`. -/
theorem s5_combine {a1 a2 a3 b1 b2 p c q t12 t3 B1 B2 B3 : ℝ≥0∞} {θ γ τ : ℝ} (hθ : 0 ≤ θ)
    (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    (h12 : t12 ≤ (a1 + a2) + (b1 + b2))
    (h3 : t3 ≤ a3 + b2 + ENNReal.ofReal θ * c + ENNReal.ofReal τ * q)
    (hq : q ≤ a3 + (b2 + p) + ENNReal.ofReal θ * c)
    (hc : c ≤ ENNReal.ofReal γ * (a2 + b2 + p))
    (hB1 : a1 + a2 + a3 ≤ B1) (hB2 : b1 + b2 ≤ B2) (hB3 : p ≤ B3) :
    t12 + t3 ≤ B1 + 2 * B2 +
      ENNReal.ofReal ((1 + τ) * (θ * γ) + τ) * (B1 + B2 + B3) := by
  have ha2 : a2 ≤ B1 := (le_add_self.trans le_self_add).trans hB1
  have ha3 : a3 ≤ B1 := le_add_self.trans hB1
  have hb2 : b2 ≤ B2 := le_add_self.trans hB2
  set θ' := ENNReal.ofReal θ with hθ'
  set γ' := ENNReal.ofReal γ with hγ'
  set τ' := ENNReal.ofReal τ with hτ'
  set SS := B1 + B2 + B3 with hSS
  have hc' : c ≤ γ' * SS := hc.trans (mul_le_mul' le_rfl (add_le_add (add_le_add ha2 hb2) hB3))
  have hq' : q ≤ SS + θ' * c := by
    refine hq.trans (add_le_add ?_ le_rfl)
    calc a3 + (b2 + p) ≤ B1 + (B2 + B3) := add_le_add ha3 (add_le_add hb2 hB3)
      _ = SS := (add_assoc _ _ _).symm
  have e : ENNReal.ofReal ((1 + τ) * (θ * γ) + τ) = (1 + τ') * (θ' * γ') + τ' := by
    rw [ENNReal.ofReal_add (by positivity) hτ, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul hθ, ENNReal.ofReal_add zero_le_one hτ, ENNReal.ofReal_one]
  rw [e]
  calc t12 + t3 ≤ ((a1 + a2) + (b1 + b2)) + (a3 + b2 + θ' * c + τ' * q) := add_le_add h12 h3
    _ ≤ ((a1 + a2) + (b1 + b2)) + (a3 + b2 + θ' * c + τ' * (SS + θ' * c)) := by gcongr
    _ = (a1 + a2 + a3) + (b1 + b2) + b2 + (1 + τ') * (θ' * c) + τ' * SS := by ring
    _ ≤ B1 + B2 + B2 + (1 + τ') * (θ' * (γ' * SS)) + τ' * SS := by gcongr
    _ = B1 + 2 * B2 + ((1 + τ') * (θ' * γ') + τ') * SS := by ring

/-! ### Helpers for the chain -/

theorem s5_exists_entry_bound (M : Mat d) : ∃ B : ℝ, 0 ≤ B ∧ ∀ i j, |M i j| ≤ B := by
  refine ⟨∑ i, ∑ j, |M i j|, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _,
    fun i j => ?_⟩
  exact (Finset.single_le_sum (f := fun j => |M i j|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, |M i j|)
      (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i))

theorem s5_dilate_subset_axisCube {U : Set (Vec d)} {z : Vec d} {L ε : ℝ} (hε : 0 < ε)
    (h : U ⊆ axisCube z L) : ε⁻¹ • U ⊆ axisCube (ε⁻¹ • z) (ε⁻¹ * L) := by
  rintro x ⟨y, hy, rfl⟩
  have h1 := h hy
  rw [axisCube, Set.mem_pi] at h1 ⊢
  intro i _
  have h2 := h1 i (Set.mem_univ i)
  simp only [Set.mem_Ioo, Pi.smul_apply, smul_eq_mul] at h2 ⊢
  have hi : 0 < ε⁻¹ := inv_pos.2 hε
  constructor
  · exact mul_lt_mul_of_pos_left h2.1 hi
  · have := mul_lt_mul_of_pos_left h2.2 hi
    linarith only [this, mul_add ε⁻¹ (z i) L]

/-- A measurable field of the form `c (A - M)` with `A` bounded on `V`, times an `L²` gradient
field, is a legitimate flux. -/
theorem s5_pairInt_shift {V : Set (Vec d)} (hV : MeasurableSet V) {A : Vec d → Mat d}
    (hA : Measurable A) {Bw : ℝ} (hB : ∀ x ∈ V, ∀ i j, |A x i j| ≤ Bw) (M : Mat d) (c : ℝ)
    {F : Vec d → Vec d} (hF : GradMemL2On V F) :
    s12_PairInt V (fun x => matVecMul (c • (A x - M)) (F x)) := by
  obtain ⟨BM, -, hBM⟩ := s5_exists_entry_bound M
  refine s5_pairInt_matVecMul (B := |c| * (Bw + BM)) hV ?_ ?_ hF
  · refine measurable_matrix_of_entries fun i j => ?_
    have h1 : Measurable fun x => A x i j :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)
    simpa [Matrix.smul_apply, Matrix.sub_apply] using (h1.sub_const (M i j)).const_mul c
  · intro x hx i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact (abs_sub _ _).trans (add_le_add (hB x hx i j) (hBM i j))

/-! ### The real coefficients -/

/-- The coefficient of `‖f‖_{L^∞(U)}` in the chain. -/
noncomputable def s5_xiF (CL CH LU : ℝ) (dd Bc S sh ε Cb : ℝ) (K : ℕ) : ℝ :=
  let τ₀ := S * |sh⁻¹ - S⁻¹|
  let τ := |S⁻¹ - sh⁻¹| * sh
  let κ := (1 + τ) * (sh⁻¹ * (dd * Bc)) + τ
  let βf := Cb * (sh⁻¹ * (3 : ℝ) ^ (2 * K)) * (S * ε ^ 2)
  βf + 2 * (CL * LU ^ 2 * τ₀) + κ * (βf + CL * LU ^ 2 * τ₀ + CH * LU ^ 2)

/-- The coefficient of `‖∇g‖_{L^∞(U)}` in the chain. -/
noncomputable def s5_xiG (CH LU : ℝ) (dd Bc S sh ε Cb : ℝ) (K : ℕ) : ℝ :=
  let τ := |S⁻¹ - sh⁻¹| * sh
  let κ := (1 + τ) * (sh⁻¹ * (dd * Bc)) + τ
  let βg := Cb * Real.log K * (3 : ℝ) ^ K * ε
  βg + κ * (βg + CH * LU)

theorem s5_ofReal_mul_mul {x y : ℝ} {N : ℝ≥0∞} (hx : 0 ≤ x) :
    ENNReal.ofReal x * (ENNReal.ofReal y * N) = ENNReal.ofReal (x * y) * N := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul hx]

theorem s5_xi_alg (Nf Ng : ℝ≥0∞) {βf βg x2 x3 y3 κ : ℝ} (hβf : 0 ≤ βf) (hβg : 0 ≤ βg)
    (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3) (hy3 : 0 ≤ y3) (hκ : 0 ≤ κ) :
    (ENNReal.ofReal βf * Nf + ENNReal.ofReal βg * Ng) + 2 * (ENNReal.ofReal x2 * Nf) +
        ENNReal.ofReal κ * ((ENNReal.ofReal βf * Nf + ENNReal.ofReal βg * Ng) +
          ENNReal.ofReal x2 * Nf + (ENNReal.ofReal x3 * Nf + ENNReal.ofReal y3 * Ng)) =
      ENNReal.ofReal (βf + 2 * x2 + κ * (βf + x2 + x3)) * Nf +
        ENNReal.ofReal (βg + κ * (βg + y3)) * Ng := by
  have e1 : ENNReal.ofReal (βf + 2 * x2 + κ * (βf + x2 + x3)) =
      ENNReal.ofReal βf + 2 * ENNReal.ofReal x2 +
        ENNReal.ofReal κ * (ENNReal.ofReal βf + ENNReal.ofReal x2 + ENNReal.ofReal x3) := by
    have a1 : 0 ≤ βf + x2 := by positivity
    have a2 : 0 ≤ κ * (βf + x2 + x3) := by positivity
    have a3 : 0 ≤ 2 * x2 := by positivity
    rw [ENNReal.ofReal_add (by positivity) a2, ENNReal.ofReal_add hβf a3,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_mul hκ,
      ENNReal.ofReal_add a1 hx3, ENNReal.ofReal_add hβf hx2]
    simp
  have e2 : ENNReal.ofReal (βg + κ * (βg + y3)) =
      ENNReal.ofReal βg + ENNReal.ofReal κ * (ENNReal.ofReal βg + ENNReal.ofReal y3) := by
    rw [ENNReal.ofReal_add hβg (by positivity), ENNReal.ofReal_mul hκ,
      ENNReal.ofReal_add hβg hy3]
  rw [e1, e2]
  ring

/-- **The deterministic chain of the first root.** -/
theorem s5_chain [NeZero d] (hd : 2 ≤ d) :
    ∃ CL CH : ℝ, 0 < CL ∧ 0 < CH ∧
      ∀ {U : Set (Vec d)}, IsSmoothBoundedDomain U → ∀ (zU : Vec d) {LU : ℝ}, 0 < LU →
        U ⊆ axisCube zU LU →
        ∀ (nu : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) {ε : ℝ}, 0 < ε →
        ∀ {S sh : ℝ}, 0 < S → 0 < sh → ∀ (K : ℕ) (Cb Bw Bc : ℝ), 0 ≤ Cb → 0 ≤ Bc →
          (∀ x ∈ ε⁻¹ • U, ∀ i j,
            |SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega x i j| ≤ Bw) →
          ∀ (MK : Mat d),
          (∀ i j, |(Matrix.of fun i j => ⨍ w in ε⁻¹ • U,
              SuperdiffusionCLT.Section6.fullStreamRecentered omega w i j) i j - MK i j| ≤ Bc) →
          (∀ (f' : Vec d → ℝ) (g' u' uh' : H1Function (ε⁻¹ • U)),
              IsDirichletSolution (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                (ε⁻¹ • U) f' g' u' →
              IsDirichletSolution (fun _ => sh • (1 : Mat d)) (ε⁻¹ • U) f' g' uh' →
              eLpNorm (fun x => u'.toFun x - uh'.toFun x) ⊤ (volume.restrict (ε⁻¹ • U)) +
                  hMinusOneVec (ε⁻¹ • U) (fun x => u'.grad x - uh'.grad x) +
                  hMinusOneVec (ε⁻¹ • U) (fun x =>
                    matVecMul (sh⁻¹ • (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu
                      omega x - MK)) (u'.grad x) - uh'.grad x) ≤
                ENNReal.ofReal (Cb * (sh⁻¹ * (3 : ℝ) ^ (2 * K))) *
                    eLpNorm f' ⊤ (volume.restrict (ε⁻¹ • U)) +
                  ENNReal.ofReal (Cb * Real.log K * (3 : ℝ) ^ K) *
                    eLpNorm (fun x => eucNorm (g'.grad x)) ⊤ (volume.restrict (ε⁻¹ • U))) →
          ∀ (f : Vec d → ℝ) (g u uhom : H1Function U),
            IsDirichletSolution (fun x => S⁻¹ • epField nu omega ε x) U f g u →
            IsDirichletSolution (fun _ => (1 : Mat d)) U f g uhom →
            eLpNorm f ⊤ (volume.restrict U) ≠ ⊤ →
            eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict U) ≠ ⊤ →
              eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict U) +
                  hMinusOneVec U (fun x => u.grad x - uhom.grad x) +
                  hMinusOneVec U (fun x =>
                    matVecMul (S⁻¹ • epFieldCentered nu omega ε U x) (u.grad x) - uhom.grad x) ≤
                ENNReal.ofReal (s5_xiF CL CH LU d Bc S sh ε Cb K) *
                    eLpNorm f ⊤ (volume.restrict U) +
                  ENNReal.ofReal (s5_xiG CH LU d Bc S sh ε Cb K) *
                    eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict U) := by
  obtain ⟨CL, hCL, hLap⟩ := s12_laplace_comparison (d := d) hd
  obtain ⟨CH, hCH, hHg⟩ := s5_hMinus_dirichlet_grad (d := d)
  refine ⟨CL, CH, hCL, hCH, ?_⟩
  intro U hU zU LU hLU hUL nu omega ε hε S sh hS hsh K Cb Bw Bc hCb hBc hBw MK hMK hBB f g u uhom
    hu huh hNf hNg
  have hε0 : ε ≠ 0 := hε.ne'
  have hUo : IsOpen U := hU.1
  have hUd : IsBoundedDomain U := hU.2.2.1
  have hUne : U.Nonempty := hU.2.1.nonempty
  have hWsm : IsSmoothBoundedDomain (ε⁻¹ • U) := w0_isSmoothBoundedDomain_smul hU (inv_pos.2 hε)
  have hWo : IsOpen (ε⁻¹ • U) := hWsm.1
  have hWd : IsBoundedDomain (ε⁻¹ • U) := hWsm.2.2.1
  have hWne : (ε⁻¹ • U).Nonempty := hWsm.2.1.nonempty
  have hWcube := s5_dilate_subset_axisCube hε hUL
  have hLW : 0 < ε⁻¹ * LU := mul_pos (inv_pos.2 hε) hLU
  -- the rescaled problems
  have hu' := rc_isDirichletSolution_dilate_epField omega hS.ne' hε0 hu
  have huh' := rc_isDirichletSolution_dilate_const (S := S) hε0 huh
  set F : Vec d → ℝ := fun y => S * ε ^ 2 * f (ε • y) with hF
  have hNF : eLpNorm F ⊤ (volume.restrict (ε⁻¹ • U)) =
      ENNReal.ofReal (S * ε ^ 2) * eLpNorm f ⊤ (volume.restrict U) :=
    s12_rhs_f hε0 hS.le f
  have hNFt : eLpNorm F ⊤ (volume.restrict (ε⁻¹ • U)) ≠ ⊤ := by
    rw [hNF]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hNf
  have hWt : volume (ε⁻¹ • U) ≠ ⊤ := by
    simpa using hWd.isFiniteMeasure_restrict_volume.measure_univ_lt_top.ne
  have hF2 : MemLp F 2 (volume.restrict (ε⁻¹ • U)) := by
    refine lt_of_le_of_lt (s12_eLpNorm_two_le _ F hNFt) ?_
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hNFt)
      (lt_top_iff_ne_top.2 (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hWt))
  obtain ⟨⟨ub, hub⟩, -⟩ := rc_dirichlet_wellPosed_of_elliptic hWo hWd.isBounded
    (rc_isEllipticFieldOn_smul_one hsh hWo.measurableSet) hF2 (g.dilateArg hε0)
  have hBB' := hBB F (g.dilateArg hε0) (u.dilateArg hε0) ub hu' hub
  have hLap' := hLap hWo hWd hWne (ε⁻¹ • zU) hLW hWcube sh S hsh.ne' hS.ne' F (g.dilateArg hε0) ub
    (uhom.dilateArg hε0) (s5_isDirichletSolution_iff.1 hub) (s5_isDirichletSolution_iff.1 huh')
  have hHU := hHg hUo hUd hUne zU hLU hUL f g uhom (s5_isDirichletSolution_iff.1 huh)
  have hWm : MeasurableSet (ε⁻¹ • U) := hWo.measurableSet
  have hmeas := SuperdiffusionCLT.Section6.measurable_fullCoefficientRecentered (d := d) nu omega
  set MVm : Mat d := Matrix.of fun i j => ⨍ w in ε⁻¹ • U,
    SuperdiffusionCLT.Section6.fullStreamRecentered omega w i j with hMVm
  -- integrability of the fluxes
  have p₁ : s12_PairInt (ε⁻¹ • U) (fun y =>
      matVecMul (sh⁻¹ • (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega y - MK))
        ((u.dilateArg hε0).grad y) - ub.grad y) :=
    s5_pairInt_sub (s5_pairInt_shift hWm hmeas hBw MK sh⁻¹ (u.dilateArg hε0).gradMemL2)
      (s12_pairInt_grad ub)
  have p₂ : s12_PairInt (ε⁻¹ • U) (fun y => ub.grad y - (uhom.dilateArg hε0).grad y) := by
    simpa using s12_pairInt_grad (ub - uhom.dilateArg hε0)
  have p₃ : s12_PairInt (ε⁻¹ • U) (fun y => matVecMul (MVm - MK) ((u.dilateArg hε0).grad y)) :=
    s5_pairInt_matVecMul (A := fun _ => MVm - MK) (B := Bc) hWm measurable_const
      (fun x _ i j => by simpa [Matrix.sub_apply] using hMK i j) (u.dilateArg hε0).gradMemL2
  have p₄ : s12_PairInt (ε⁻¹ • U) (fun y => matVecMul
      (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega y - MVm)
        ((u.dilateArg hε0).grad y)) := by
    simpa only [one_smul] using
      s5_pairInt_shift hWm hmeas hBw MVm 1 (u.dilateArg hε0).gradMemL2
  have pA : s12_PairInt (ε⁻¹ • U) (fun y => (u.dilateArg hε0).grad y - ub.grad y) := by
    simpa using s12_pairInt_grad (u.dilateArg hε0 - ub)
  have hpeq : s12_hMinusOneVec (ε⁻¹ • U) (uhom.dilateArg hε0).grad =
      s12_hMinusOneVec U uhom.grad :=
    s12_hMinusOneVec_dilate_grad hε U uhom.grad (uhom.dilateArg hε0).grad fun y => by
      simp [H1Function.dilateArg_grad]
  have hsplit2 : s12_hMinusOneVec (ε⁻¹ • U) ub.grad ≤
      s12_hMinusOneVec (ε⁻¹ • U) (fun y => ub.grad y - (uhom.dilateArg hε0).grad y) +
        s12_hMinusOneVec U uhom.grad := by
    have e : (fun y => (ub.grad y - (uhom.dilateArg hε0).grad y) + (uhom.dilateArg hε0).grad y) =
        ub.grad := by
      funext y
      abel
    calc s12_hMinusOneVec (ε⁻¹ • U) ub.grad =
          s12_hMinusOneVec (ε⁻¹ • U)
            (fun y => (ub.grad y - (uhom.dilateArg hε0).grad y) + (uhom.dilateArg hε0).grad y) := by
          rw [e]
      _ ≤ _ := by
          rw [← hpeq]
          exact s12_hMinusOneVec_add_le _ p₂ (s12_pairInt_grad _)
  have hsplit1 : s12_hMinusOneVec (ε⁻¹ • U) (u.dilateArg hε0).grad ≤
      s12_hMinusOneVec (ε⁻¹ • U) (fun y => (u.dilateArg hε0).grad y - ub.grad y) +
        s12_hMinusOneVec (ε⁻¹ • U) (fun y => ub.grad y - (uhom.dilateArg hε0).grad y) +
        s12_hMinusOneVec U uhom.grad := by
    have e : (fun y => ((u.dilateArg hε0).grad y - ub.grad y) +
        (ub.grad y - (uhom.dilateArg hε0).grad y) + (uhom.dilateArg hε0).grad y) =
        (u.dilateArg hε0).grad := by
      funext y
      abel
    calc s12_hMinusOneVec (ε⁻¹ • U) (u.dilateArg hε0).grad =
          s12_hMinusOneVec (ε⁻¹ • U) (fun y => ((u.dilateArg hε0).grad y - ub.grad y) +
            (ub.grad y - (uhom.dilateArg hε0).grad y) + (uhom.dilateArg hε0).grad y) := by
          rw [e]
      _ ≤ _ := by
          rw [← hpeq]
          refine (s12_hMinusOneVec_add_le _ (s12_pairInt_add pA p₂) (s12_pairInt_grad _)).trans ?_
          exact add_le_add (s12_hMinusOneVec_add_le _ pA p₂) le_rfl
  have hc := (s5_hMinusOneVec_matVecMul_le (ε⁻¹ • U) (MVm - MK) (B := Bc)
    (fun i j => by simpa [Matrix.sub_apply] using hMK i j)
    (s12_pairInt_grad (u.dilateArg hε0))).trans
    (mul_le_mul' le_rfl hsplit1)
  have hq0 := s5_flux_centre_le (ε⁻¹ • U)
    (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) MVm MK sh
    (u.dilateArg hε0).grad ub.grad p₁ (s12_pairInt_grad ub) p₃
  have hq : s12_hMinusOneVec (ε⁻¹ • U) (fun y => matVecMul (sh⁻¹ •
        (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega y - MVm))
        ((u.dilateArg hε0).grad y)) ≤
      s12_hMinusOneVec (ε⁻¹ • U) (fun y => matVecMul (sh⁻¹ •
        (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega y - MK))
        ((u.dilateArg hε0).grad y) - ub.grad y) +
      (s12_hMinusOneVec (ε⁻¹ • U) (fun y => ub.grad y - (uhom.dilateArg hε0).grad y) +
        s12_hMinusOneVec U uhom.grad) +
      ENNReal.ofReal sh⁻¹ * s12_hMinusOneVec (ε⁻¹ • U) (fun y => matVecMul (MVm - MK)
        ((u.dilateArg hε0).grad y)) := by
    have := hq0.trans (add_le_add (add_le_add le_rfl hsplit2) le_rfl)
    rwa [abs_of_pos (inv_pos.2 hsh)] at this
  have h12 := s12_root_terms_one_two_le hε u uhom ub
  have h3 := s12_root_flux_le nu omega hε S sh MK u uhom ub p₁ p₂ p₃ p₄
  -- the swap of the scalar, expressed through the scaled flux
  set τ : ℝ := |S⁻¹ - sh⁻¹| * sh with hτ
  have hτ0 : 0 ≤ τ := by positivity
  have hqq : ENNReal.ofReal |S⁻¹ - sh⁻¹| * s12_hMinusOneVec (ε⁻¹ • U) (fun y => matVecMul
        (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega y - MVm)
        ((u.dilateArg hε0).grad y)) =
      ENNReal.ofReal τ * s12_hMinusOneVec (ε⁻¹ • U) (fun y => matVecMul (sh⁻¹ •
        (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega y - MVm))
        ((u.dilateArg hε0).grad y)) := by
    have e : (fun y => matVecMul (sh⁻¹ • (SuperdiffusionCLT.Section6.fullCoefficientRecentered
        nu omega y - MVm)) ((u.dilateArg hε0).grad y)) = fun y => sh⁻¹ •
          matVecMul (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega y - MVm)
            ((u.dilateArg hε0).grad y) := funext fun y => s12_matVecMul_smul_left _ _ _
    rw [e, s12_hMinusOneVec_smul, ← mul_assoc, ← ENNReal.ofReal_mul hτ0, hτ, abs_of_pos (inv_pos.2 hsh)]
    congr 2
    field_simp
  have h3' := h3
  rw [abs_neg, abs_of_pos (inv_pos.2 hsh), hqq] at h3'
  -- the right-hand sides
  have hg : eLpNorm (fun y => eucNorm ((g.dilateArg hε0).grad y)) ⊤
      (volume.restrict (ε⁻¹ • U)) =
      ENNReal.ofReal ε * eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict U) :=
    s12_rhs_g hε g
  have hS2 : 0 ≤ S * ε ^ 2 := by positivity
  have hB1 : ENNReal.ofReal (Cb * (sh⁻¹ * (3 : ℝ) ^ (2 * K))) *
        eLpNorm F ⊤ (volume.restrict (ε⁻¹ • U)) +
      ENNReal.ofReal (Cb * Real.log K * (3 : ℝ) ^ K) *
        eLpNorm (fun x => eucNorm ((g.dilateArg hε0).grad x)) ⊤ (volume.restrict (ε⁻¹ • U)) =
      ENNReal.ofReal (Cb * (sh⁻¹ * (3 : ℝ) ^ (2 * K)) * (S * ε ^ 2)) *
          eLpNorm f ⊤ (volume.restrict U) +
        ENNReal.ofReal (Cb * Real.log K * (3 : ℝ) ^ K * ε) *
          eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict U) := by
    rw [hNF, hg, s5_ofReal_mul_mul (by positivity), s5_ofReal_mul_mul (by positivity)]
  have hB1a := hBB'.trans_eq hB1
  have hB2 : ENNReal.ofReal (CL * (ε⁻¹ * LU) ^ 2 * |sh⁻¹ - S⁻¹|) *
        eLpNorm F ⊤ (volume.restrict (ε⁻¹ • U)) =
      ENNReal.ofReal (CL * LU ^ 2 * (S * |sh⁻¹ - S⁻¹|)) * eLpNorm f ⊤ (volume.restrict U) := by
    rw [hNF, s5_ofReal_mul_mul (by positivity)]
    congr 2
    field_simp
  have hB2a := hLap'.trans_eq hB2
  have hκ0 : 0 ≤ (1 + τ) * (sh⁻¹ * ((d : ℝ) * Bc)) + τ := by positivity
  have key := s5_combine (θ := sh⁻¹) (γ := (d : ℝ) * Bc) (τ := τ) (inv_pos.2 hsh).le
    (by positivity) hτ0 h12 h3' hq hc hB1a hB2a hHU
  refine key.trans ?_
  refine le_of_eq ?_
  have := s5_xi_alg (eLpNorm f ⊤ (volume.restrict U))
    (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict U))
    (βf := Cb * (sh⁻¹ * (3 : ℝ) ^ (2 * K)) * (S * ε ^ 2))
    (βg := Cb * Real.log K * (3 : ℝ) ^ K * ε) (x2 := CL * LU ^ 2 * (S * |sh⁻¹ - S⁻¹|))
    (x3 := CH * LU ^ 2) (y3 := CH * LU) (κ := (1 + τ) * (sh⁻¹ * ((d : ℝ) * Bc)) + τ)
    (by positivity) (mul_nonneg (mul_nonneg (mul_nonneg hCb (Real.log_natCast_nonneg K)) (by positivity)) hε.le) (by positivity) (by positivity) (by positivity) hκ0
  exact this.trans rfl

end SuperdiffusionCLT.Section7
