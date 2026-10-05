/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayChartL

@[expose] public section

open Homogenization MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

/-!
# The boundary excess decay in the original coordinates

A weak solution in `H¹₀(U)` near a boundary point with a `C^{1,1}` graph chart satisfies the
excess decay at the exponent `1 - d / p`, against the `L²` excess over any affine function, the
data in `L^p`, and the slope term `M₂ 3^m |∇ℓ₀|` of the second order chart error.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **Boundary excess decay in the original coordinates.** -/
theorem r3e_boundary_decay [NeZero d] (hd : 2 ≤ d) (M₁ : ℝ) {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ ε C c K : ℝ, 0 < ε ∧ 0 < C ∧ 0 < c ∧ 1 ≤ K ∧
      ∀ (U : Set (Vec d)) (e : Vec d) (ψ : Vec d → ℝ) (x₀ : Vec d) (r M₂ : ℝ) (m : ℤ),
        IsOpen U → vecNormSq e = 1 → ContDiff ℝ (⊤ : ℕ∞) ψ → (∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) →
        (∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) →
        vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e) →
        (∀ y ∈ Metric.ball x₀ r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))) →
        M₂ * (3 : ℝ) ^ m ≤ ε → K * (3 : ℝ) ^ m ≤ r →
        ∀ (φ : H10Function U) (f : Vec d → ℝ),
          IsWeakSolutionOn (fun _ => (1 : Mat d)) U φ.toH1Function f (fun _ => 0) →
          MemLp f (ENNReal.ofReal p) (volume.restrict (U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m))) →
          ∀ (a₀ : ℝ) (b₀ : Vec d) (ρ : ℝ), 0 < ρ → ρ ≤ c * (3 : ℝ) ^ m →
            ∃ (a : ℝ) (b : Vec d), ∀ᵐ y ∂(volume.restrict (U ∩ Metric.ball x₀ ρ)),
              |φ.toH1Function.toFun y - (a + vecDot b (y - x₀))| ≤
                C * ρ * (ρ / (3 : ℝ) ^ m) ^ (1 - (d : ℝ) / p) *
                  (((3 : ℝ) ^ m)⁻¹ * (eLpNorm (fun y => φ.toH1Function.toFun y -
                        (a₀ + vecDot b₀ (y - x₀))) 2
                      (p12_nmeas ((3 : ℝ) ^ m) (U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m)))).toReal +
                    M₂ * (3 : ℝ) ^ m * ‖b₀‖ +
                    (3 : ℝ) ^ m * (eLpNorm f (ENNReal.ofReal p)
                      (p12_nmeas ((3 : ℝ) ^ m) (U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m)))).toReal) := by
  classical
  obtain ⟨Kl, hKl1, HKl⟩ := p12_chart_lip d M₁
  obtain ⟨εf, Cf, hεf, hCf, HF⟩ := r3d_flat_decay hd (0 : Fin d) hp
  have hKl0 : 0 < Kl := by linarith only [hKl1]
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hp0 : 0 < p := hdR.trans hp
  have hd0 : (0 : ℝ) ≤ d := hdR.le
  have h1d : (0 : ℝ) ≤ 1 + d := add_nonneg zero_le_one hd0
  have h4Kl : 0 < 4 * Kl := by linarith only [hKl0]
  have h2Kl : 0 < 2 * Kl := by linarith only [hKl0]
  set α : ℝ := 1 - (d : ℝ) / p with hαd
  have hα0 : 0 < α := by
    have : (d : ℝ) / p < 1 := (div_lt_one hp0).2 hp
    linarith only [this]
  have hα1 : α ≤ 1 := by
    have : 0 ≤ (d : ℝ) / p := div_nonneg hd0 hp0.le
    linarith only [this]
  set cδ : ℝ := |flattenLipConst d M₁ 1| + |(2 * (d : ℝ) ^ 2 + 8 * d ^ 3 * M₁) * (2 * (1 + d) * Kl)|
    with hcδ
  have hcδ0 : 0 ≤ cδ := add_nonneg (abs_nonneg _) (abs_nonneg _)
  set q : ℝ := ((1 : ℝ) / 2) ^ α with hq
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα0
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  set CA : ℝ := 2 * (1 + d) * d ^ 2 * Kl ^ 2 * (2 * Kl) ^ d with hCA
  set Cs : ℝ := 6 * Cf / (1 - q) + (288 * 6 ^ d + 8 * Cf) with hCs
  set CB : ℝ := 1 + CA + cδ * d with hCB
  set cT : ℝ := 2 * (1 + d) * d ^ 3 with hcT
  set Ctot : ℝ := (Cf * (4 * Kl) * (4 * Kl) ^ α + cT * Cs) * CB + cT * d with hCtot
  have hCs0 : 0 ≤ Cs := by
    have : 0 < 1 - q := by linarith only [hq1]
    exact add_nonneg (div_nonneg (mul_nonneg (by norm_num) hCf.le) this.le)
      (add_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) d))
        (mul_nonneg (by norm_num) hCf.le))
  have hCA0 : 0 ≤ CA :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two h1d) (sq_nonneg _)) (sq_nonneg _))
      (pow_nonneg h2Kl.le d)
  have hcT0 : 0 < cT := mul_pos (mul_pos two_pos (add_pos_of_pos_of_nonneg one_pos hd0)) (pow_pos hdR 3)
  have hCtot : 0 < Ctot := by
    have : 0 < Cf * (4 * Kl) * (4 * Kl) ^ α :=
      mul_pos (mul_pos hCf h4Kl) (Real.rpow_pos_of_pos h4Kl _)
    have h1 : 0 < CB := add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg one_pos hCA0)
      (mul_nonneg hcδ0 hd0)
    have h2 : 0 ≤ cT * Cs := mul_nonneg hcT0.le hCs0
    have h3 : 0 < cT * d := mul_pos hcT0 hdR
    have : 0 < (Cf * (4 * Kl) * (4 * Kl) ^ α + cT * Cs) * CB :=
      mul_pos (add_pos_of_pos_of_nonneg this h2) h1
    rw [hCtot]; linarith only [this, h3]
  refine ⟨min 1 (εf / (cδ + 1)), Ctot, 1 / (72 * Kl), Kl, lt_min one_pos (div_pos hεf (add_pos_of_nonneg_of_pos hcδ0 one_pos)), hCtot,
    div_pos one_pos (mul_pos (by norm_num) hKl0), hKl1, ?_⟩
  intro U e ψ x₀ r M₂ m hU he hψ hb1 hb2 hx₀ hch hMε hKr φ f hw hf a₀ b₀ ρ hρ hρc
  have hR : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans (hb1 0)
  have hM₂ : 0 ≤ M₂ := flatten_nonneg_of_lipschitz hb2 (0 : Fin d)
  set R : ℝ := (3 : ℝ) ^ m with hRd
  have hRi : 0 ≤ R⁻¹ := inv_nonneg.2 hR.le
  have hRR : R⁻¹ * R = 1 := inv_mul_cancel₀ hR.ne'
  have hKK : Kl * Kl⁻¹ = 1 := mul_inv_cancel₀ hKl0.ne'
  have hR36 : 0 ≤ R / 36 := div_nonneg hR.le (by norm_num)
  set u : Vec d := -(basisVec (0 : Fin d)) with hu
  set τ : Vec d := r3c_z0 (0 : Fin d) m with hτ
  have hKlipI : ∀ y z : Vec d, ‖flattenInv e ψ x₀ u y - flattenInv e ψ x₀ u z‖ ≤ Kl * ‖y - z‖ :=
    fun y z => (HKl he hψ hb1 (r3e_u_unit 0) x₀ y z).2
  have hKlipF : ∀ y z : Vec d, ‖flattenMap e ψ x₀ u y - flattenMap e ψ x₀ u z‖ ≤ Kl * ‖y - z‖ :=
    fun y z => (HKl he hψ hb1 (r3e_u_unit 0) x₀ y z).1
  have hρR : ρ ≤ R / (72 * Kl) := by
    have : 1 / (72 * Kl) * R = R / (72 * Kl) := by ring
    rwa [this] at hρc
  have hρ36 : 2 * Kl * ρ ≤ R / 36 := by
    have h1 := mul_le_mul_of_nonneg_left hρR h2Kl.le
    have h2 : 2 * Kl * (R / (72 * Kl)) = R / 36 := by
      linear_combination (R / 36) * hKK
    linarith only [h1, h2]
  have hρR1 : ρ ≤ R := by
    have h1 : R / (72 * Kl) ≤ R := by
      rw [div_le_iff₀ (mul_pos (by norm_num) hKl0)]
      have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 72 * Kl by linarith only [hKl1]) hR.le
      linarith only [this]
    exact hρR.trans h1
  have hρr : ρ ≤ r := by
    have : R ≤ Kl * R := le_mul_of_one_le_left hR.le hKl1
    linarith only [hρR1, this, hKr]
  have hSm : MeasurableSet (U ∩ Metric.ball x₀ ρ) :=
    hU.measurableSet.inter Metric.isOpen_ball.measurableSet
  -- the transported problem
  obtain ⟨v, hvf, hvw, hvZ⟩ := r3e_transport hU he hψ hb1 hx₀ hch 0 hKl1 hKlipI m hKr φ hw
  have hvfun : v.toFun = fun x => φ.toH1Function.toFun (flattenInv e ψ x₀ u (x - τ)) :=
    funext hvf
  have himg : (fun x => flattenInv e ψ x₀ u (x - τ)) '' openCubeSet (originCube d m) ⊆
      U ∩ Metric.ball x₀ (Kl * R) := by
    rintro _ ⟨x, hx, rfl⟩
    exact r3e_pull_mem he hψ hx₀ hch 0 hKl1 hKlipI m hKr hx
  have hf₂ : MemLp (fun x => f (flattenInv e ψ x₀ u (x - τ))) (ENNReal.ofReal p)
      (normalizedCubeMeasure (originCube d m)) :=
    p12_memLp_pull he hψ u x₀ τ f _ m himg hf
  -- the coefficient
  have hLip : flattenLipConst d M₁ M₂ = M₂ * flattenLipConst d M₁ 1 := by
    unfold flattenLipConst; ring
  set δ : ℝ := M₂ * R * cδ with hδd
  have hδ0 : 0 ≤ δ := mul_nonneg (mul_nonneg hM₂ hR.le) hcδ0
  have hδε : δ ≤ εf := by
    have h1 : M₂ * R ≤ εf / (cδ + 1) := hMε.trans (min_le_right _ _)
    have h2 : M₂ * R * (cδ + 1) ≤ εf := by
      rwa [le_div_iff₀ (add_pos_of_nonneg_of_pos hcδ0 one_pos)] at h1
    have h3 : M₂ * R * cδ ≤ M₂ * R * (cδ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only) (mul_nonneg hM₂ hR.le)
    linarith only [h2, h3]
  have hAδ : ∀ x ∈ openCubeSet (originCube d m), ∀ i j,
      |(fun x => flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) (x - τ)) x i j - (1 : Mat d) i j| ≤ δ := by
    intro x hx i j
    have h1 := flattenCoeff_one_sub_le he hψ hb1 hb2 (u := u) x₀ (x - τ) i j
    have h2 : ‖x - τ‖ ≤ R := (r3e_Q_geom 0 hx).1.le
    have h3 : flattenLipConst d M₁ M₂ ≤ M₂ * cδ := by
      rw [hLip]
      refine mul_le_mul_of_nonneg_left ?_ hM₂
      rw [hcδ]
      linarith only [le_abs_self (flattenLipConst d M₁ 1), abs_nonneg
        ((2 * (d : ℝ) ^ 2 + 8 * d ^ 3 * M₁) * (2 * (1 + d) * Kl))]
    exact calc _ ≤ flattenLipConst d M₁ M₂ * ‖x - τ‖ := h1
      _ ≤ (M₂ * cδ) * R := mul_le_mul h3 h2 (norm_nonneg _) (mul_nonneg hM₂ hcδ0)
      _ = δ := by rw [hδd]; ring
  have hAK : ∀ x ∈ openCubeSet (originCube d m), ∀ i j k,
      |fderiv ℝ (fun y => (fun x => flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) (x - τ)) y i j) x
        (basisVec k)| ≤ M₂ * cδ := by
    intro x _ i j k
    have h1 := r3e_coeff_fderiv_le he hψ hb1 hb2 u x₀ τ hKlipI hKl0.le x k i j
    refine h1.trans ?_
    have h2 : (2 * (d : ℝ) ^ 2 + 8 * d ^ 3 * M₁) * (2 * M₂ * ((1 + d) * Kl)) =
        M₂ * ((2 * (d : ℝ) ^ 2 + 8 * d ^ 3 * M₁) * (2 * (1 + d) * Kl)) := by ring
    rw [h2]
    refine mul_le_mul_of_nonneg_left ?_ hM₂
    rw [hcδ]
    linarith only [abs_nonneg (flattenLipConst d M₁ 1), le_abs_self
      ((2 * (d : ℝ) ^ 2 + 8 * d ^ 3 * M₁) * (2 * (1 + d) * Kl))]
  have hKδ : M₂ * cδ * R ≤ δ := by rw [hδd]; exact le_of_eq (by ring)
  have HF' := fun (a₀' : ℝ) (b₀' : Vec d) (s : ℝ) (hs : 0 < s) (hsR : s ≤ R / 36) =>
    HF m (fun x => flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) (x - τ)) (M₂ * cδ) δ
      (fun i j => r3e_contDiff_coeff hψ u x₀ τ i j) hδ0 hδε hAδ hAK hKδ _ hf₂ v hvw hvZ a₀' b₀' s hs hsR
  -- the flat quantities
  set O : Mat d := r3e_O e ψ x₀ u with hOd
  set b₀' : Vec d := O *ᵥ b₀ with hb₀'
  set N₂ : ℝ := (eLpNorm (fun x => v.toFun x - (a₀ + vecDot b₀' (x - r3c_z0 (0 : Fin d) m))) 2
    (normalizedCubeMeasure (originCube d m))).toReal with hN₂
  set Np : ℝ := (eLpNorm (fun x => f (flattenInv e ψ x₀ u (x - τ))) (ENNReal.ofReal p)
    (normalizedCubeMeasure (originCube d m))).toReal with hNp
  set B : ℝ := R⁻¹ * N₂ + R * Np + δ * |b₀' 0| with hBd
  have hN₂0 : 0 ≤ N₂ := ENNReal.toReal_nonneg
  have hNp0 : 0 ≤ Np := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ B :=
    add_nonneg (add_nonneg (mul_nonneg hRi hN₂0) (mul_nonneg hR.le hNp0))
      (mul_nonneg hδ0 (abs_nonneg _))
  have H : ∀ s : ℝ, 0 < s → s ≤ R / 36 → ∃ (a : ℝ) (b : Vec d),
      ∀ᵐ x ∂(volume.restrict (r3e_F (0 : Fin d) m s)),
        |v.toFun x - (a + vecDot b (x - r3c_z0 (0 : Fin d) m))| ≤ Cf * s * (s / R) ^ α * B := by
    intro s hs hsR
    obtain ⟨a, b, hab⟩ := HF' a₀ b₀' s hs hsR
    exact ⟨a, b, hab⟩
  obtain ⟨a₁, b₁, h₁, Hc⟩ := r3e_chain (0 : Fin d) m hα0 hCf.le hB0 H
  -- the slope at the top scale
  have hv := r3e_memLp_flat (0 : Fin d) m v a₀ b₀'
  set E₁ : ℝ := Cf * (R / 36) * ((R / 36) / R) ^ α * B with hE₁
  have hE₁0 : 0 ≤ E₁ :=
    mul_nonneg (mul_nonneg (mul_nonneg hCf.le hR36)
      (Real.rpow_nonneg (div_nonneg hR36 hR.le) _)) hB0
  have hsl := r3e_slope_step (0 : Fin d) m hE₁0 h₁ hv
  have hN₂B : N₂ / R ≤ B := by
    have : N₂ / R = R⁻¹ * N₂ := by ring
    rw [this]
    have : 0 ≤ R * Np := mul_nonneg hR.le hNp0
    have : 0 ≤ δ * |b₀' 0| := mul_nonneg hδ0 (abs_nonneg _)
    linarith only [‹0 ≤ R * Np›, ‹0 ≤ δ * |b₀' 0|›]
  have hE₁le : E₁ ≤ Cf * (R / 36) * B := by
    have h1 : ((R / 36) / R) ^ α ≤ 1 :=
      Real.rpow_le_one (div_nonneg hR36 hR.le) (by rw [div_le_one hR]; linarith only [hR]) hα0.le
    have h2 : 0 ≤ Cf * (R / 36) := mul_nonneg hCf.le hR36
    exact calc E₁ = (Cf * (R / 36)) * ((R / 36) / R) ^ α * B := by rw [hE₁]
      _ ≤ (Cf * (R / 36)) * 1 * B :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) hB0
      _ = _ := by ring
  have hb₁ : ‖b₁ - b₀'‖ ≤ (288 * 6 ^ d + 8 * Cf) * B := by
    refine hsl.trans ?_
    rw [div_le_iff₀ hR]
    have h1 : 6 ^ d * N₂ ≤ 6 ^ d * (B * R) := by
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by norm_num) d)
      rwa [div_le_iff₀ hR] at hN₂B
    have h2 : E₁ ≤ Cf * (R / 36) * B := hE₁le
    linarith only [h1, h2]
  have hb₀'n : ‖b₀'‖ ≤ d * ‖b₀‖ := r3e_norm_O_le e ψ x₀ u b₀
  -- the bridge to the original norms
  have hbr := r3e_bridge_L2 hU he hψ hb2 hx₀ hch 0 hKl1 hKlipI m hKr φ a₀ b₀
  have hN₂o : N₂ ≤ (eLpNorm (fun y => φ.toH1Function.toFun y - (a₀ + vecDot b₀ (y - x₀))) 2
      (p12_nmeas R (U ∩ Metric.ball x₀ (Kl * R)))).toReal + CA * (M₂ * R ^ 2 * ‖b₀‖) := by
    have : N₂ = (eLpNorm (fun x => φ.toH1Function.toFun (flattenInv e ψ x₀ u (x - τ)) -
        (a₀ + vecDot b₀' (x - τ))) 2 (normalizedCubeMeasure (originCube d m))).toReal := by
      rw [hN₂, hvfun]
    rw [this]
    exact hbr
  have hNpo : Np ≤ (eLpNorm f (ENNReal.ofReal p)
      (p12_nmeas R (U ∩ Metric.ball x₀ (Kl * R)))).toReal := by
    have hfin : eLpNorm f (ENNReal.ofReal p) (p12_nmeas R (U ∩ Metric.ball x₀ (Kl * R))) ≠ ⊤ := by
      unfold p12_nmeas
      exact (hf.smul_measure ENNReal.ofReal_ne_top).eLpNorm_ne_top
    refine ENNReal.toReal_mono hfin ?_
    rw [p12_normalized_eq]
    exact p12_eLpNorm_pull_le he hψ u x₀ τ f _ R himg
  set No : ℝ := (eLpNorm (fun y => φ.toH1Function.toFun y - (a₀ + vecDot b₀ (y - x₀))) 2
    (p12_nmeas R (U ∩ Metric.ball x₀ (Kl * R)))).toReal with hNo
  set Npo : ℝ := (eLpNorm f (ENNReal.ofReal p)
    (p12_nmeas R (U ∩ Metric.ball x₀ (Kl * R)))).toReal with hNpo'
  have hNo0 : 0 ≤ No := ENNReal.toReal_nonneg
  have hNpo0 : 0 ≤ Npo := ENNReal.toReal_nonneg
  have hX0 : 0 ≤ M₂ * R * ‖b₀‖ := mul_nonneg (mul_nonneg hM₂ hR.le) (norm_nonneg _)
  have hP : 0 ≤ R⁻¹ * No := mul_nonneg hRi hNo0
  have hQ : 0 ≤ R * Npo := mul_nonneg hR.le hNpo0
  have hδb : δ * |b₀' 0| ≤ cδ * d * (M₂ * R * ‖b₀‖) := by
    have h1 : |b₀' 0| ≤ d * ‖b₀‖ := by
      have := norm_le_pi_norm b₀' 0
      rw [Real.norm_eq_abs] at this
      exact this.trans hb₀'n
    exact calc δ * |b₀' 0| ≤ δ * (d * ‖b₀‖) := mul_le_mul_of_nonneg_left h1 hδ0
      _ = cδ * d * (M₂ * R * ‖b₀‖) := by rw [hδd]; ring
  have hBB : B ≤ CB * (R⁻¹ * No + M₂ * R * ‖b₀‖ + R * Npo) := by
    have h1 : R⁻¹ * N₂ ≤ R⁻¹ * No + CA * (M₂ * R * ‖b₀‖) := by
      exact calc R⁻¹ * N₂ ≤ R⁻¹ * (No + CA * (M₂ * R ^ 2 * ‖b₀‖)) :=
            mul_le_mul_of_nonneg_left hN₂o hRi
        _ = R⁻¹ * No + CA * (M₂ * R * ‖b₀‖) := by
            linear_combination (CA * M₂ * ‖b₀‖ * R) * hRR
    have h2 : R * Np ≤ R * Npo := mul_le_mul_of_nonneg_left hNpo hR.le
    have hc0 : 0 ≤ CA + cδ * d := add_nonneg hCA0 (mul_nonneg hcδ0 hd0)
    have h3 : B ≤ R⁻¹ * No + R * Npo + (CA + cδ * d) * (M₂ * R * ‖b₀‖) := by
      rw [hBd]; linarith only [h1, h2, hδb]
    have h4 : (CA + cδ * d) * (M₂ * R * ‖b₀‖) ≤
        (CA + cδ * d) * (R⁻¹ * No + M₂ * R * ‖b₀‖ + R * Npo) :=
      mul_le_mul_of_nonneg_left (by linarith only [hP, hQ]) hc0
    have h5 : CB * (R⁻¹ * No + M₂ * R * ‖b₀‖ + R * Npo) =
        (R⁻¹ * No + M₂ * R * ‖b₀‖ + R * Npo) +
          (CA + cδ * d) * (R⁻¹ * No + M₂ * R * ‖b₀‖ + R * Npo) := by rw [hCB]; ring
    rw [h5]
    linarith only [h3, h4, hX0]
  have hMR : M₂ * R ≤ 1 := hMε.trans (min_le_left _ _)
  have hs : 0 < 2 * Kl * ρ := mul_pos h2Kl hρ
  obtain ⟨a, b, hab, hbb⟩ := Hc (2 * Kl * ρ) hs hρ36
  have hpb := r3e_pullback_ae hU he hψ hx₀ hch 0 hKl1 hKlipF m hρr φ.toH1Function.toFun a b
    (E := Cf * (2 * (2 * Kl * ρ)) * (2 * (2 * Kl * ρ) / R) ^ α * B)
    (hab.mono fun x hx => by rw [hvf x] at hx; exact hx)
  have h4 : 2 * (2 * Kl * ρ) = 4 * Kl * ρ := by ring
  rw [h4] at hpb
  have hnb : ‖b‖ ≤ Cs * B + d * ‖b₀‖ := by
    have h1 : ‖b‖ ≤ ‖b - b₁‖ + ‖b₁ - b₀'‖ + ‖b₀'‖ := by
      exact calc ‖b‖ = ‖(b - b₁) + (b₁ - b₀') + b₀'‖ := by congr 1; abel
        _ ≤ ‖(b - b₁) + (b₁ - b₀')‖ + ‖b₀'‖ := norm_add_le _ _
        _ ≤ _ := add_le_add_left (norm_add_le _ _) _
    have h2 : 6 * Cf * B / (1 - q) = 6 * Cf / (1 - q) * B := by ring
    have h3 : Cs * B = 6 * Cf / (1 - q) * B + (288 * 6 ^ d + 8 * Cf) * B := by rw [hCs]; ring
    have hbb' : ‖b - b₁‖ ≤ 6 * Cf * B / (1 - q) := hbb
    linarith only [h1, hbb', hb₁, hb₀'n, h2, h3]
  refine ⟨a, O *ᵥ b, ?_⟩
  filter_upwards [hpb, ae_restrict_mem hSm] with y hy hyS
  have hyb : ‖y - x₀‖ < ρ := by
    have := hyS.2
    rwa [Metric.mem_ball, dist_eq_norm] at this
  have hdot := r3e_dot_flatten he hψ u x₀ b y
  have hid : φ.toH1Function.toFun y - (a + vecDot (O *ᵥ b) (y - x₀)) =
      (φ.toH1Function.toFun y - (a + vecDot b (flattenMap e ψ x₀ u y))) -
        r3e_T e ψ x₀ y * vecDot (O *ᵥ b) e := by
    rw [hdot]; ring
  have hT := r3e_T_abs_le he hψ hM₂ hb2 x₀ y
  have hT2 : 2 * M₂ * (1 + d) * d * ‖y - x₀‖ ^ 2 ≤ 2 * M₂ * (1 + d) * d * ρ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hyb.le 2)
      (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hM₂) h1d) hd0)
  have hvd : |vecDot (O *ᵥ b) e| ≤ d * (d * ‖b‖) := by
    refine (r3e_vecDot_le (r3e_norm_le_one he)).trans ?_
    exact mul_le_mul_of_nonneg_left (r3e_norm_O_le e ψ x₀ u b) hd0
  have herr : |r3e_T e ψ x₀ y| * |vecDot (O *ᵥ b) e| ≤ cT * M₂ * ρ ^ 2 * ‖b‖ := by
    calc |r3e_T e ψ x₀ y| * |vecDot (O *ᵥ b) e| ≤ (2 * M₂ * (1 + d) * d * ρ ^ 2) * (d * (d * ‖b‖)) :=
          mul_le_mul (hT.trans hT2) hvd (abs_nonneg _)
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hM₂) h1d) hd0) (sq_nonneg ρ))
      _ = cT * M₂ * ρ ^ 2 * ‖b‖ := by rw [hcT]; ring
  have hfin := r3e_final_alg (R := R) (ρ := ρ) (M₂ := M₂) (B := B)
    (Bo := R⁻¹ * No + M₂ * R * ‖b₀‖ + R * Npo) (α := α) (C₀ := Cf) (Kl := Kl) (CB := CB)
    (Cs := Cs) (dd := d) (cT := cT) (nb := ‖b‖) (nb0 := ‖b₀‖) hR hρ hρR1 hKl0.le hα1 hM₂ hMR hB0
    hCf.le hCs0 hd0 hcT0.le (norm_nonneg _) hBB (by linarith only [hX0, hP, hQ]) hnb hy herr
  rw [hid]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  exact hfin

end SuperdiffusionCLT.Section7
