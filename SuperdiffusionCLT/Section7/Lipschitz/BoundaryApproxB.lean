/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryApprox
public import SuperdiffusionCLT.Section7.Lipschitz.CarriersS

/-!
# The harmonic approximation near the boundary: the Caccioppoli block in real form and the
arithmetic of the estimate
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- Monotonicity of the sup-norm block in the scale and the constant (`s` and `s'` within a factor
two, `2 C ≤ C'`). -/
theorem LipCaccBdryS.monoC {a : CoeffField d} {nu s s' C C' E : ℝ} {W : Set (Vec d)}
    {z : Vec d} {j : ℕ} (h : LipCaccBdryS a nu s C E W z j) (hs : 0 < s) (hs1 : s ≤ 2 * s')
    (hs2 : s' ≤ 2 * s) (hC : 0 ≤ C) (hCC : 2 * C ≤ C') : LipCaccBdryS a nu s' C' E W z j := by
  have hs' : 0 < s' := by linarith only [hs, hs1]
  refine LipCaccBdryS.mono ?_ ?_ ?_ h
  · calc C * s ≤ C * (2 * s') := mul_le_mul_of_nonneg_left hs1 hC
      _ = (2 * C) * s' := by ring
      _ ≤ C' * s' := mul_le_mul_of_nonneg_right hCC hs'.le
  · calc C * s⁻¹ ≤ C * (2 * s'⁻¹) := mul_le_mul_of_nonneg_left (lip_inv_le hs' hs2) hC
      _ = (2 * C) * s'⁻¹ := by ring
      _ ≤ C' * s'⁻¹ := mul_le_mul_of_nonneg_right hCC (inv_nonneg.2 hs'.le)
  · linarith only [hC, hCC]

/-- **The boundary Caccioppoli block in real numbers**: from bounds on the three norms of the
data to a bound of the gradient. -/
theorem lip_bdry_approx_cacc [NeZero d] {a : CoeffField d} {nu s C E : ℝ} {W : Set (Vec d)}
    {z : Vec d} {j : ℕ} (h : LipCaccBdryS a nu s C E W z j) (hnu : 0 < nu) (hs : 0 < s)
    (hC : 0 ≤ C) (hD0 : volume (shiftCube z ((j : ℤ) - 1) ∩ W) ≠ 0)
    (hD1 : volume (shiftCube z ((j : ℤ) - 1) ∩ W) ≠ ⊤)
    (hDsub : shiftCube z ((j : ℤ) - 1) ∩ W ⊆ shiftCube z (j : ℤ) ∩ W)
    (f γ : Vec d → ℝ) (u : H1Function (shiftCube z (j : ℤ) ∩ W)) (hγ : ContDiff ℝ 2 γ)
    (hsol : IsWeakSolutionOn a (shiftCube z (j : ℤ) ∩ W) u f (fun _ => 0))
    (hz : LocalizedZeroTraceFunctionOn (shiftCube z (j : ℤ) ∩ W) (shiftCube z (j : ℤ))
      (fun x => u.toFun x - γ x)) {Qb F B1 B2 : ℝ}
    (hQ : lpBar (shiftCube z (j : ℤ) ∩ W) 2 (fun x => u.toFun x - γ x) ≤ ENNReal.ofReal Qb)
    (hF : lpBar (shiftCube z (j : ℤ) ∩ W) 2 f ≤ ENNReal.ofReal F)
    (h1 : ∀ x ∈ shiftCube z (j : ℤ) ∩ W, ‖fderiv ℝ γ x‖ ≤ B1)
    (h2 : ∀ x ∈ shiftCube z (j : ℤ) ∩ W, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ B2)
    (hQ0 : 0 ≤ Qb) (hF0 : 0 ≤ F) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) :
    nu * lipGradL2 (shiftCube z ((j : ℤ) - 1) ∩ W) u.grad ^ 2 ≤
      C * s * (((3 : ℝ)⁻¹) ^ j) ^ 2 * Qb ^ 2 + C * s⁻¹ * ((3 : ℝ) ^ j) ^ 2 * F ^ 2 +
        C * s * B1 ^ 2 + C * ((j : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ j) ^ 2 * B2 ^ 2 := by
  have hc := h f γ B1 B2 u hγ hB1 hB2 h1 h2 hsol hz
  set X : ℝ := lipGradL2 (shiftCube z ((j : ℤ) - 1) ∩ W) u.grad with hXdef
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hmem : MemLp (fun x => eucNorm (u.grad x)) 2
      (volume.restrict (shiftCube z ((j : ℤ) - 1) ∩ W)) :=
    p13_memLp_euc ((u.grad_memVectorL2).mono_measure (Measure.restrict_mono hDsub le_rfl))
  have hX : lpBar (shiftCube z ((j : ℤ) - 1) ∩ W) 2 (fun x => eucNorm (u.grad x)) =
      ENNReal.ofReal X := (lip_int_harm_of_l2_ofReal_lipL2 hD0 hD1 hmem).symm
  have e1 : ENNReal.ofReal nu *
      lpBar (shiftCube z ((j : ℤ) - 1) ∩ W) 2 (fun x => eucNorm (u.grad x)) ^ 2 =
      ENNReal.ofReal (nu * X ^ 2) := by
    rw [hX, ← ENNReal.ofReal_pow hX0, ← ENNReal.ofReal_mul hnu.le]
  have hs' : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
  have hp1 : 0 ≤ C * s * (((3 : ℝ)⁻¹) ^ j) ^ 2 := by positivity
  have hp2 : 0 ≤ C * s⁻¹ * ((3 : ℝ) ^ j) ^ 2 := by positivity
  have hbound : ENNReal.ofReal (C * s * (((3 : ℝ)⁻¹) ^ j) ^ 2) *
          lpBar (shiftCube z (j : ℤ) ∩ W) 2 (fun x => u.toFun x - γ x) ^ 2 +
        ENNReal.ofReal (C * s⁻¹ * ((3 : ℝ) ^ j) ^ 2) *
          lpBar (shiftCube z (j : ℤ) ∩ W) 2 f ^ 2 +
        ENNReal.ofReal (C * s * B1 ^ 2) +
        ENNReal.ofReal (C * ((j : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ j) ^ 2 * B2 ^ 2) ≤
      ENNReal.ofReal (C * s * (((3 : ℝ)⁻¹) ^ j) ^ 2 * Qb ^ 2 + C * s⁻¹ * ((3 : ℝ) ^ j) ^ 2 * F ^ 2 +
        C * s * B1 ^ 2 + C * ((j : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ j) ^ 2 * B2 ^ 2) := by
    calc _ ≤ ENNReal.ofReal (C * s * (((3 : ℝ)⁻¹) ^ j) ^ 2) * ENNReal.ofReal Qb ^ 2 +
        ENNReal.ofReal (C * s⁻¹ * ((3 : ℝ) ^ j) ^ 2) * ENNReal.ofReal F ^ 2 +
        ENNReal.ofReal (C * s * B1 ^ 2) +
        ENNReal.ofReal (C * ((j : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ j) ^ 2 * B2 ^ 2) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_pow hQ0, ← ENNReal.ofReal_pow hF0,
          ← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_mul hp2,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have := e1.symm.le.trans (hc.trans hbound)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this


/-- The volume of the cube `z + □_{k+2}` against the volume of a set `V` that contains the
trace of a ball of radius `3^k / 3^ag / 2` on the domain. -/
theorem lip_bdry_approx_volume_ratio (d : ℕ) [NeZero d] (M₁ rU : ℝ) (hrU : 0 < rU) (ag : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (W V : Set (Vec d)) (rW M₂W DW : ℝ) (z : Vec d) (k : ℕ),
      IsUniformC11Domain W rW M₁ M₂W DW → rU * (3 : ℝ) ^ k ≤ rW → z ∈ W →
      Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2) ∩ W ⊆ V → V ⊆ shiftCube z (k : ℤ) →
      volume V ≠ 0 ∧
        (volume (shiftCube z ((k + 2 : ℕ) : ℤ))).toReal ≤ κ * (volume V).toReal := by
  obtain ⟨c, hc, -, hq⟩ := lip_inner_ball d M₁
  set m0 : ℝ := min (1 / (2 * (3 : ℝ) ^ ag)) rU with hm0
  have hm0pos : 0 < m0 := lt_min (by positivity) hrU
  refine ⟨(9 / (2 * c * m0)) ^ d, by positivity, ?_⟩
  intro W V rW M₂W DW z k hW hrW hz hBV hVk
  have ht : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  set ρ : ℝ := (3 : ℝ) ^ k * m0 with hρ
  have hρpos : 0 < ρ := by positivity
  have hρr : ρ ≤ rW := by
    have : m0 ≤ rU := min_le_right _ _
    calc ρ ≤ (3 : ℝ) ^ k * rU := mul_le_mul_of_nonneg_left this ht.le
      _ = rU * (3 : ℝ) ^ k := by ring
      _ ≤ rW := hrW
  have hρ3 : ρ ≤ (3 : ℝ) ^ k / 3 ^ ag / 2 := by
    have : m0 ≤ 1 / (2 * (3 : ℝ) ^ ag) := min_le_left _ _
    calc ρ ≤ (3 : ℝ) ^ k * (1 / (2 * (3 : ℝ) ^ ag)) := mul_le_mul_of_nonneg_left this ht.le
      _ = (3 : ℝ) ^ k / 3 ^ ag / 2 := by field_simp
  obtain ⟨q, hqs⟩ := hq W rW M₂W DW hW z hz ρ hρpos hρr
  have hqV : Metric.ball q (c * ρ) ⊆ V := fun y hy =>
    hBV ⟨Metric.ball_subset_ball hρ3 (hqs hy).1, (hqs hy).2⟩
  have hvolq : volume (Metric.ball q (c * ρ)) = ENNReal.ofReal ((2 * (c * ρ)) ^ d) := by
    rw [Real.volume_pi_ball q (by positivity), Fintype.card_fin]
  have hVt : volume V ≠ ⊤ := ne_top_of_le_ne_top (lip_bdry_approx_vol_cube_ne_top z k)
    (measure_mono hVk)
  have hlow : ENNReal.ofReal ((2 * (c * ρ)) ^ d) ≤ volume V := hvolq ▸ measure_mono hqV
  have hpos : (0 : ℝ) < (2 * (c * ρ)) ^ d := by positivity
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0] at hlow
    exact (ENNReal.ofReal_pos.2 hpos).ne' (le_antisymm hlow bot_le)
  · have h1 : (2 * (c * ρ)) ^ d ≤ (volume V).toReal := by
      have := ENNReal.toReal_mono hVt hlow
      rwa [ENNReal.toReal_ofReal hpos.le] at this
    rw [lip_bdry_approx_vol_cube, ENNReal.toReal_ofReal (by positivity)]
    calc ((3 : ℝ) ^ (k + 2)) ^ d = (9 / (2 * c * m0)) ^ d * (2 * (c * ρ)) ^ d := by
          rw [← mul_pow, hρ]
          congr 1
          field_simp
          ring
      _ ≤ (9 / (2 * c * m0)) ^ d * (volume V).toReal :=
          mul_le_mul_of_nonneg_left h1 (by positivity)

/-- From `ν X² ≤ s Z²` to the normalized slope `s^{-1/2} ν^{1/2} X ≤ Z`. -/
theorem lip_bdry_approx_sgrad_le {nu s X Z : ℝ} (hnu : 0 < nu) (hs : 0 < s) (hX : 0 ≤ X)
    (hZ : 0 ≤ Z) (h : nu * X ^ 2 ≤ s * Z ^ 2) : (Real.sqrt s)⁻¹ * Real.sqrt nu * X ≤ Z := by
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hq : 0 < Real.sqrt nu := Real.sqrt_pos.2 hnu
  have h1 : (Real.sqrt nu * X) ^ 2 ≤ (Real.sqrt s * Z) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hnu.le, Real.sq_sqrt hs.le]
    exact h
  have h2 : Real.sqrt nu * X ≤ Real.sqrt s * Z :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h1
  calc (Real.sqrt s)⁻¹ * Real.sqrt nu * X = (Real.sqrt s)⁻¹ * (Real.sqrt nu * X) := by ring
    _ ≤ (Real.sqrt s)⁻¹ * (Real.sqrt s * Z) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Z := by field_simp



/-- The arithmetic of the auxiliary function `w`: the right-hand side of its Caccioppoli
estimate. -/
theorem lip_bdry_approx_w_arith {Cin Cd s G1 G2 q kE : ℝ} (k : ℕ) (hCin : 1 ≤ Cin)
    (hCd : 1 ≤ Cd) (hs : 1 ≤ s) (hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2) (hq : 0 ≤ q) (hqk : q ≤ kE)
    (hk1 : kE ≤ 1) :
    Cin * s * (((3 : ℝ)⁻¹) ^ (k + 2)) ^ 2 * (2 * (Cd * (3 : ℝ) ^ k * G1)) ^ 2 +
        Cin * s⁻¹ * ((3 : ℝ) ^ (k + 2)) ^ 2 * (0 : ℝ) ^ 2 + Cin * s * (Cd * G1) ^ 2 +
        Cin * q ^ 2 * ((3 : ℝ) ^ (k + 2)) ^ 2 *
          (Cd * (((3 : ℝ) ^ k)⁻¹ * G1 + G2)) ^ 2 ≤
      s * (11 * Cin * Cd * (G1 + kE * (3 : ℝ) ^ k * G2)) ^ 2 := by
  have ht : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  set t : ℝ := (3 : ℝ) ^ k with htdef
  have e9 : (3 : ℝ) ^ (k + 2) = 9 * t := by rw [pow_add]; ring
  have e9i : ((3 : ℝ)⁻¹) ^ (k + 2) = (9 * t)⁻¹ := by rw [inv_pow, e9]
  rw [e9, e9i]
  set Y : ℝ := G1 + kE * t * G2 with hY
  have hkE0 : 0 ≤ kE := hq.trans hqk
  have hY0 : 0 ≤ Y := by positivity
  have hq1 : q ≤ 1 := hqk.trans hk1
  have hqY : q * (G1 + t * G2) ≤ Y := by
    have a1 : q * G1 ≤ G1 := mul_le_of_le_one_left hG1 hq1
    have a2 : q * (t * G2) ≤ kE * (t * G2) :=
      mul_le_mul_of_nonneg_right hqk (by positivity)
    calc q * (G1 + t * G2) = q * G1 + q * (t * G2) := by ring
      _ ≤ G1 + kE * (t * G2) := add_le_add a1 a2
      _ = Y := by rw [hY]; ring
  have hqY0 : 0 ≤ q * (G1 + t * G2) := by positivity
  have hG1Y : G1 ≤ Y := by rw [hY]; have : 0 ≤ kE * t * G2 := by positivity
                           linarith only [this]
  set Key : ℝ := Cin * Cd ^ 2 with hKey
  have hKey0 : 0 ≤ Key := by positivity
  have h1 : Cin * s * (9 * t)⁻¹ ^ 2 * (2 * (Cd * t * G1)) ^ 2 = (4 / 81) * (s * Key * G1 ^ 2) := by
    rw [hKey]; field_simp; ring
  have h4 : Cin * q ^ 2 * (9 * t) ^ 2 * (Cd * (t⁻¹ * G1 + G2)) ^ 2 =
      81 * (Key * (q * (G1 + t * G2)) ^ 2) := by
    rw [hKey]; field_simp; ring
  have h3 : Cin * s * (Cd * G1) ^ 2 = s * Key * G1 ^ 2 := by rw [hKey]; ring
  have hA : s * Key * G1 ^ 2 ≤ s * Key * Y ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hG1 hG1Y 2) (by positivity)
  have hB : Key * (q * (G1 + t * G2)) ^ 2 ≤ s * Key * Y ^ 2 := by
    have b1 : Key * (q * (G1 + t * G2)) ^ 2 ≤ Key * Y ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hqY0 hqY 2) hKey0
    have b2 : Key * Y ^ 2 ≤ s * (Key * Y ^ 2) := le_mul_of_one_le_left (by positivity) hs
    linarith only [b1, b2]
  have hP : 0 ≤ s * Key * Y ^ 2 := by positivity
  have hC : s * Key * Y ^ 2 ≤ Cin * (s * Key * Y ^ 2) := le_mul_of_one_le_left hP hCin
  have hfin : s * (11 * Cin * Cd * Y) ^ 2 = 121 * (Cin * (s * Key * Y ^ 2)) := by
    rw [hKey]; ring
  rw [h1, h4, h3, hfin]
  linarith only [hA, hB, hC, hP]


/-- The arithmetic of the Caccioppoli estimate of the solution at the scale `k + 1`. -/
theorem lip_bdry_approx_u_arith {Cin s Φ dP G1 G2 F q kE : ℝ} (k : ℕ) (hCin : 1 ≤ Cin)
    (hs : 1 ≤ s) (hΦ : 0 ≤ Φ) (hdP : 0 ≤ dP) (hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2) (hF : 0 ≤ F)
    (hq : 0 ≤ q) (hqk : q ≤ kE) :
    Cin * s * (((3 : ℝ)⁻¹) ^ (k + 1)) ^ 2 * ((3 : ℝ) ^ (k + 1) * (Φ + dP + G1)) ^ 2 +
        Cin * s⁻¹ * ((3 : ℝ) ^ (k + 1)) ^ 2 * F ^ 2 + Cin * s * G1 ^ 2 +
        Cin * q ^ 2 * ((3 : ℝ) ^ (k + 1)) ^ 2 * G2 ^ 2 ≤
      s * (Cin * (Φ + dP + 2 * G1 + 3 * (s⁻¹ * (3 : ℝ) ^ k * F) +
        3 * (kE * (3 : ℝ) ^ k * G2))) ^ 2 := by
  have ht : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  set t : ℝ := (3 : ℝ) ^ k with htdef
  have hs0 : 0 < s := by linarith only [hs]
  have e3 : (3 : ℝ) ^ (k + 1) = 3 * t := by rw [pow_succ]; ring
  have e3i : ((3 : ℝ)⁻¹) ^ (k + 1) = (3 * t)⁻¹ := by rw [inv_pow, e3]
  rw [e3, e3i]
  have hkE0 : 0 ≤ kE := hq.trans hqk
  set Λ : ℝ := Φ + dP + G1 with hΛ
  set c : ℝ := 3 * (s⁻¹ * t * F) with hc
  set e : ℝ := 3 * (kE * t * G2) with he
  have hΛ0 : 0 ≤ Λ := by positivity
  have hc0 : 0 ≤ c := by positivity
  have he0 : 0 ≤ e := by positivity
  have h1 : Cin * s * (3 * t)⁻¹ ^ 2 * (3 * t * Λ) ^ 2 = Cin * s * Λ ^ 2 := by
    field_simp
  have h2 : Cin * s⁻¹ * (3 * t) ^ 2 * F ^ 2 = Cin * s * c ^ 2 := by
    rw [hc]; field_simp
  have h4 : Cin * q ^ 2 * (3 * t) ^ 2 * G2 ^ 2 ≤ Cin * s * e ^ 2 := by
    have a1 : q * (3 * t * G2) ≤ kE * (3 * t * G2) :=
      mul_le_mul_of_nonneg_right hqk (by positivity)
    have a2 : (q * (3 * t * G2)) ^ 2 ≤ (kE * (3 * t * G2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) a1 2
    have a3 : (kE * (3 * t * G2)) ^ 2 ≤ s * (kE * (3 * t * G2)) ^ 2 :=
      le_mul_of_one_le_left (by positivity) hs
    have a4 : Cin * q ^ 2 * (3 * t) ^ 2 * G2 ^ 2 = Cin * (q * (3 * t * G2)) ^ 2 := by ring
    have a5 : Cin * s * e ^ 2 = Cin * (9 * (s * (kE * t * G2) ^ 2)) := by rw [he]; ring
    have a6 : (kE * (3 * t * G2)) ^ 2 = 9 * (kE * t * G2) ^ 2 := by ring
    rw [a4, a5]
    have := mul_le_mul_of_nonneg_left (a2.trans a3) (by positivity : 0 ≤ Cin)
    rw [a6] at this
    calc Cin * (q * (3 * t * G2)) ^ 2 ≤ Cin * (s * (9 * (kE * t * G2) ^ 2)) := this
      _ = _ := by ring
  have hsq : Λ ^ 2 + c ^ 2 + G1 ^ 2 + e ^ 2 ≤ (Λ + G1 + c + e) ^ 2 := by
    have := mul_nonneg hΛ0 hG1
    have := mul_nonneg hΛ0 hc0
    have := mul_nonneg hΛ0 he0
    have := mul_nonneg hG1 hc0
    have := mul_nonneg hG1 he0
    have := mul_nonneg hc0 he0
    linarith only [mul_nonneg hΛ0 hG1, mul_nonneg hΛ0 hc0, mul_nonneg hΛ0 he0,
      mul_nonneg hG1 hc0, mul_nonneg hG1 he0, mul_nonneg hc0 he0]
  have hsum : Φ + dP + 2 * G1 + c + e = Λ + G1 + c + e := by rw [hΛ]; ring
  have hCs : 0 ≤ Cin * s := by positivity
  have hmain : Cin * s * Λ ^ 2 + Cin * s * c ^ 2 + Cin * s * G1 ^ 2 + Cin * s * e ^ 2 ≤
      Cin * s * (Λ + G1 + c + e) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq hCs
    linarith only [this]
  have hP : 0 ≤ s * (Λ + G1 + c + e) ^ 2 := by positivity
  have hCin2 : s * (Λ + G1 + c + e) ^ 2 ≤ Cin * (s * (Λ + G1 + c + e) ^ 2) :=
    le_mul_of_one_le_left hP hCin
  have hfin : s * (Cin * (Φ + dP + 2 * G1 + c + e)) ^ 2 =
      Cin * (Cin * (s * (Λ + G1 + c + e) ^ 2)) := by rw [hsum]; ring
  have hfin2 : Cin * (s * (Λ + G1 + c + e) ^ 2) ≤ Cin * (Cin * (s * (Λ + G1 + c + e) ^ 2)) :=
    mul_le_mul_of_nonneg_left hCin2 (by positivity)
  rw [h1, h2]
  have : s * (Cin * (Φ + dP + 2 * G1 + c + e)) ^ 2 =
      Cin * (Cin * (s * (Λ + G1 + c + e) ^ 2)) := hfin
  have hcm : Cin * s * (Λ + G1 + c + e) ^ 2 = Cin * (s * (Λ + G1 + c + e) ^ 2) := by ring
  linarith only [h4, hmain, hfin2, this, hcm]


/-- The assembly of the estimate: `C` depends on `Cin`, `Cd`, `κs`, `d'` only. -/
theorem lip_bdry_approx_final_arith {Cin Cd κs d' δ Φ P G1 Gk Fs T1 Tk Sg Su Sw : ℝ}
    (hCin : 1 ≤ Cin) (hCd : 1 ≤ Cd) (hκ : 0 ≤ κs) (hd' : 0 ≤ d') (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hΦ : 0 ≤ Φ) (hP : 0 ≤ P) (hG1 : 0 ≤ G1) (hGk : 0 ≤ Gk) (hFs : 0 ≤ Fs)
    (hT1 : T1 ≤ Cd * G1) (hTk : Tk ≤ 2 * Cin * δ * Sg + Cin * Fs)
    (hSg : Sg ≤ κs * (Su + Sw))
    (hSu : Su ≤ Cin * (Φ + d' * P + 2 * G1 + 3 * Fs + 3 * Gk))
    (hSw : Sw ≤ 11 * Cin * Cd * (G1 + Gk)) :
    T1 + Tk ≤ (Cd + Cin + 2 * Cin ^ 2 * κs * (d' + 14 + 11 * Cd)) *
      (δ * (Φ + P) + G1 + Fs + Gk) := by
  set a0 : ℝ := 2 * Cin ^ 2 * κs with ha0
  have ha00 : 0 ≤ a0 := by positivity
  set M : ℝ := a0 * (d' + 14 + 11 * Cd) with hM
  have hCin0 : 0 ≤ Cin := by linarith only [hCin]
  have hCd0 : 0 ≤ Cd := by linarith only [hCd]
  have hK1 : 1 ≤ d' + 14 + 11 * Cd := by linarith only [hd', hCd]
  have hM1 : a0 ≤ M := by
    rw [hM]; exact le_mul_of_one_le_right ha00 hK1
  have hSg' : Sg ≤ κs * (Cin * (Φ + d' * P + 2 * G1 + 3 * Fs + 3 * Gk) +
      11 * Cin * Cd * (G1 + Gk)) :=
    hSg.trans (mul_le_mul_of_nonneg_left (add_le_add hSu hSw) hκ)
  have hTk' : Tk ≤ 2 * Cin * δ * (κs * (Cin * (Φ + d' * P + 2 * G1 + 3 * Fs + 3 * Gk) +
      11 * Cin * Cd * (G1 + Gk))) + Cin * Fs := by
    refine hTk.trans (add_le_add ?_ le_rfl)
    exact mul_le_mul_of_nonneg_left hSg' (by positivity)
  have hexp : 2 * Cin * δ * (κs * (Cin * (Φ + d' * P + 2 * G1 + 3 * Fs + 3 * Gk) +
      11 * Cin * Cd * (G1 + Gk))) = a0 * δ * (Φ + d' * P + (2 + 11 * Cd) * G1 + 3 * Fs +
      (3 + 11 * Cd) * Gk) := by rw [ha0]; ring
  have hMa : a0 * (2 + 11 * Cd) ≤ M := by
    rw [hM]; exact mul_le_mul_of_nonneg_left (by linarith only [hd', hCd]) ha00
  have hMb : a0 * (3 + 11 * Cd) ≤ M := by
    rw [hM]; exact mul_le_mul_of_nonneg_left (by linarith only [hd', hCd]) ha00
  have hMc : a0 * d' ≤ M := by
    rw [hM]; exact mul_le_mul_of_nonneg_left (by linarith only [hd', hCd]) ha00
  have hMd : a0 * 3 ≤ M := by
    rw [hM]; exact mul_le_mul_of_nonneg_left (by linarith only [hd', hCd]) ha00
  have n1 : 0 ≤ (M - a0) * (δ * Φ) := mul_nonneg (by linarith only [hM1]) (by positivity)
  have n2 : 0 ≤ (M - a0 * d') * (δ * P) := mul_nonneg (by linarith only [hMc]) (by positivity)
  have n3 : 0 ≤ (M - a0 * (2 + 11 * Cd) * δ) * G1 := by
    refine mul_nonneg ?_ hG1
    have : a0 * (2 + 11 * Cd) * δ ≤ a0 * (2 + 11 * Cd) * 1 :=
      mul_le_mul_of_nonneg_left hδ1 (by positivity)
    linarith only [this, hMa]
  have n4 : 0 ≤ (M - a0 * 3 * δ) * Fs := by
    refine mul_nonneg ?_ hFs
    have : a0 * 3 * δ ≤ a0 * 3 * 1 := mul_le_mul_of_nonneg_left hδ1 (by positivity)
    linarith only [this, hMd]
  have n5 : 0 ≤ (M - a0 * (3 + 11 * Cd) * δ) * Gk := by
    refine mul_nonneg ?_ hGk
    have : a0 * (3 + 11 * Cd) * δ ≤ a0 * (3 + 11 * Cd) * 1 :=
      mul_le_mul_of_nonneg_left hδ1 (by positivity)
    linarith only [this, hMb]
  have n6 : 0 ≤ Cd * G1 - T1 := by linarith only [hT1]
  have n7 : 0 ≤ Cin * Fs := by positivity
  have hfin := hTk'.trans_eq (by rw [hexp])
  have e2 : T1 + Tk ≤ Cd * G1 + (a0 * δ * (Φ + d' * P + (2 + 11 * Cd) * G1 + 3 * Fs +
      (3 + 11 * Cd) * Gk) + Cin * Fs) := by linarith only [hT1, hfin]
  have n8 : 0 ≤ Cd * G1 := by positivity
  have n9 : 0 ≤ (Cd + Cin) * Gk := by positivity
  have n10 : 0 ≤ Cin * G1 := by positivity
  have n11 : 0 ≤ Cd * Fs := by positivity
  have n12 : 0 ≤ Cd * (δ * (Φ + P)) := by positivity
  have n13 : 0 ≤ Cin * (δ * (Φ + P)) := by positivity
  have n14 : 0 ≤ Cin * Gk := by positivity
  have n15 : 0 ≤ Cd * Gk := by positivity
  linarith only [e2, n1, n2, n3, n4, n5, n8, n10, n11, n12, n13, n14, n15]



/-- The Laplace solution with the boundary values of `u - w` on `V`, and the right-hand side
that the equation sees on `V`. -/
theorem lip_bdry_approx_ub_data [NeZero d] {Ω V : Set (Vec d)} {lam Lam : ℝ} {a : CoeffField d}
    {s F : ℝ} (hΩ : IsOpen Ω) (hVo : IsOpen V) (hVΩ : V ⊆ Ω) (hVt : volume V ≠ ⊤)
    (hVb : IsBoundedDomain V) (hs : 0 < s) (hF0 : 0 ≤ F)
    (hell : IsEllipticFieldOn lam Lam Ω a) {f : Vec d → ℝ}
    (hF : ∀ᵐ x ∂volume.restrict Ω, |f x| ≤ F) {u w : H1Function Ω}
    (hu : IsWeakSolutionOn a Ω u f (fun _ => 0)) (hw : IsWeakSolutionOn a Ω w 0 0) :
    ∃ (fV : Vec d → ℝ) (ub : H1Function V), AEStronglyMeasurable fV (volume.restrict V) ∧
      (∀ᵐ x ∂volume.restrict V, |fV x| ≤ F) ∧
      IsWeakSolutionOn a V (u.restrict hVo hVΩ - w.restrict hVo hVΩ) fV (fun _ => 0) ∧
      IsWeakSolutionOn (fun _ => s • (1 : Mat d)) V ub fV (fun _ => 0) ∧
      IsWeakSolutionOn (fun _ => s • (1 : Mat d)) V ub f (fun _ => 0) ∧
      MemH10 V (fun x => ub.toFun x - (u.restrict hVo hVΩ - w.restrict hVo hVΩ).toFun x) := by
  obtain ⟨fV, hm, hb, hsol, hint⟩ := lip_bdry_approx_repl hΩ hVo hVΩ hell hu hF0 hF
  have hellV : IsEllipticFieldOn lam Lam V a := hell.mono hVo.measurableSet hVΩ
  have hsub := lip_bdry_approx_weak_sub hellV hsol (IsWeakSolutionOn.restrict' hw hVo hVΩ)
  obtain ⟨ub, hub, hubm⟩ := lip_bdry_approx_ub_exists hVo hVb hVt hs hb hm
    (u.restrict hVo hVΩ - w.restrict hVo hVΩ)
  refine ⟨fV, ub, hm, hb, hsub, hub, ?_, hubm⟩
  intro φ
  rw [hub φ, hint φ]

/-- The localized zero trace of `ub - gt` in a window on which the cut-off datum is `g - gt`. -/
theorem lip_bdry_approx_trace {Ω V B B' : Set (Vec d)} (hVo : IsOpen V) (hB' : IsOpen B')
    (hVΩ : V ⊆ Ω) (hBB : B' ⊆ B) (hagree : Ω ∩ B' = V ∩ B') {u w : H1Function Ω}
    {ub : H1Function V} {g ψ gt : Vec d → ℝ}
    (hz : LocalizedZeroTraceFunctionOn Ω B (fun x => u.toFun x - g x))
    (hw : MemH10 Ω (fun x => w.toFun x - ψ x))
    (hub : MemH10 V (fun x => ub.toFun x - (u.restrict hVo hVΩ - w.restrict hVo hVΩ).toFun x))
    (hψ : ∀ x ∈ B', ψ x = g x - gt x) :
    LocalizedZeroTraceFunctionOn V B' (fun x => ub.toFun x - gt x) := by
  intro η hη hηc hηT
  have A1 : LocalizedZeroTraceFunctionOn V B' (fun x => u.toFun x - g x) :=
    lip_localized_restrict hVo hB' hVΩ hBB hagree hz
  have A2 : LocalizedZeroTraceFunctionOn V B' (fun x => w.toFun x - ψ x) :=
    lip_localized_restrict hVo hB' hVΩ hBB hagree (lip_bdry_approx_loc_of_h10 hw)
  have m1 := A1 η hη hηc hηT
  have m2 := A2 η hη hηc hηT
  have m3 := lip_bdry_approx_h10_mul hub hη hηc
  have e : (fun y => η y * (ub.toFun y - gt y)) =
      fun y => (η y * (ub.toFun y - (u.restrict hVo hVΩ - w.restrict hVo hVΩ).toFun y) +
        η y * (u.toFun y - g y)) - η y * (w.toFun y - ψ y) := by
    funext y
    by_cases hy : η y = 0
    · simp [hy]
    · have h1 : ψ y = g y - gt y := hψ y (hηT (subset_tsupport _ hy))
      have h2 : (u.restrict hVo hVΩ - w.restrict hVo hVΩ).toFun y = u.toFun y - w.toFun y := by
        simp [H1Function.sub_toFun, H1Function.restrict]
      rw [h2, h1]
      ring
  rw [e]
  exact memH10_sub (memH10_add m3 m1) m2



theorem lip_bdry_approx_abs_vecDot_le (p y : Vec d) : |vecDot p y| ≤ (d : ℝ) * ‖p‖ * ‖y‖ := by
  unfold vecDot
  calc |∑ i, p i * y i| ≤ ∑ i, |p i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖p‖ * ‖y‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (by simpa using norm_le_pi_norm p i) (by simpa using norm_le_pi_norm y i)
          (abs_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * ‖p‖ * ‖y‖ := by simp; ring

theorem lip_bdry_approx_continuous_aff (p x₀ : Vec d) :
    Continuous (fun x : Vec d => vecDot p (x - x₀)) := by
  unfold vecDot
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.mul ((continuous_apply i).comp (continuous_id.sub continuous_const))

/-- Distance from the base point inside the cube `z + □_{k+1}`. -/
theorem lip_bdry_approx_dist_le {z x₀ x : Vec d} {k : ℕ} (hx₀ : ‖x₀ - z‖ ≤ (3 : ℝ) ^ k / 2)
    (hx : x ∈ shiftCube z ((k + 1 : ℕ) : ℤ)) : ‖x - x₀‖ ≤ 3 * (3 : ℝ) ^ k := by
  rw [lip_bdry_approx_shiftCube_eq_ball, Metric.mem_ball, dist_eq_norm] at hx
  have h1 : ‖x - x₀‖ ≤ ‖x - z‖ + ‖x₀ - z‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub x z x₀
    rw [norm_sub_rev z x₀] at this
    exact this
  have h2 : (3 : ℝ) ^ (k + 1) = 3 * (3 : ℝ) ^ k := by rw [pow_succ]; ring
  have : 0 < (3 : ℝ) ^ k := by positivity
  linarith only [h1, hx, hx₀, h2, this]


/-- **The slope of the gradient of `u`**: the boundary Caccioppoli block at the scale `k + 1`
for `u` against the datum `g`, with the pinned flatness `Φ_{k+1}(p)`. -/
theorem lip_bdry_approx_su [NeZero d] {a : CoeffField d} {nu s Cin E lam Lam : ℝ}
    {W : Set (Vec d)} {z x₀ : Vec d} {k : ℕ} (hnu : 0 < nu) (hs : 1 ≤ s) (hCin : 1 ≤ Cin)
    (hE : 0 ≤ E) (hk : 1 ≤ k) (hW : IsOpen W) (hx₀ : ‖x₀ - z‖ ≤ (3 : ℝ) ^ k / 2)
    (hell : IsEllipticFieldOn lam Lam (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) a)
    (hc1 : LipCaccBdryS a nu s Cin E W z (k + 1))
    (hD0 : volume (shiftCube z (k : ℤ) ∩ W) ≠ 0)
    (f g : Vec d → ℝ) (F G1 G2 : ℝ) (u : H1Function (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W))
    (hg : ContDiff ℝ 2 g) (hF0 : 0 ≤ F) (hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2)
    (hDg : ∀ x ∈ shiftCube z ((k + 2 : ℕ) : ℤ), ‖fderiv ℝ g x‖ ≤ G1)
    (hD2g : ∀ x ∈ shiftCube z ((k + 2 : ℕ) : ℤ), ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ G2)
    (hFae : ∀ᵐ x ∂volume.restrict (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W), |f x| ≤ F)
    (hsol : IsWeakSolutionOn a (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) u f (fun _ => 0))
    (hz : LocalizedZeroTraceFunctionOn (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W)
      (shiftCube z ((k + 2 : ℕ) : ℤ)) (fun x => u.toFun x - g x)) (p : Vec d) :
    (Real.sqrt s)⁻¹ * Real.sqrt nu * lipGradL2 (shiftCube z (k : ℤ) ∩ W) u.grad ≤
      Cin * (lipPin (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) (k + 1) x₀ (g x₀) u.toFun p +
        (d : ℝ) * ‖p‖ + 2 * G1 + 3 * (s⁻¹ * (3 : ℝ) ^ k * F) +
        3 * (((k : ℝ)) ^ (-E) * (3 : ℝ) ^ k * G2)) := by
  have hs0 : 0 < s := by linarith only [hs]
  have hCin0 : 0 ≤ Cin := by linarith only [hCin]
  have hQ01 : shiftCube z (k : ℤ) ⊆ shiftCube z ((k + 1 : ℕ) : ℤ) :=
    lip_bdry_approx_cube_mono z (by omega)
  have hQ12 : shiftCube z ((k + 1 : ℕ) : ℤ) ⊆ shiftCube z ((k + 2 : ℕ) : ℤ) :=
    lip_bdry_approx_cube_mono z (by omega)
  have hD01 : shiftCube z (k : ℤ) ∩ W ⊆ shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W :=
    Set.inter_subset_inter_left _ hQ01
  have hD12 : shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W ⊆ shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W :=
    Set.inter_subset_inter_left _ hQ12
  have hD1o : IsOpen (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) :=
    (lip_bdry_approx_isOpen_cube z _).inter hW
  have hD2o : IsOpen (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) :=
    (lip_bdry_approx_isOpen_cube z _).inter hW
  have hD0t : volume (shiftCube z (k : ℤ) ∩ W) ≠ ⊤ :=
    ne_top_of_le_ne_top (lip_bdry_approx_vol_cube_ne_top z k)
      (measure_mono Set.inter_subset_left)
  have hD1t : volume (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) ≠ ⊤ :=
    ne_top_of_le_ne_top (lip_bdry_approx_vol_cube_ne_top z (k + 1))
      (measure_mono Set.inter_subset_left)
  have hD1v : volume (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) ≠ 0 := fun h =>
    hD0 (le_antisymm (h ▸ measure_mono hD01) bot_le)
  have hQ2ball : shiftCube z ((k + 2 : ℕ) : ℤ) = Metric.ball z ((3 : ℝ) ^ (k + 2) / 2) :=
    lip_bdry_approx_shiftCube_eq_ball z (k + 2)
  have ht : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have h3 : (3 : ℝ) ^ (k + 1) = 3 * (3 : ℝ) ^ k := by rw [pow_succ]; ring
  have h9 : (3 : ℝ) ^ (k + 2) = 9 * (3 : ℝ) ^ k := by rw [pow_add]; ring
  have hx₀Q2 : x₀ ∈ shiftCube z ((k + 2 : ℕ) : ℤ) := by
    rw [hQ2ball, Metric.mem_ball, dist_eq_norm]
    linarith only [hx₀, h9, ht]
  have hconv : Convex ℝ (shiftCube z ((k + 2 : ℕ) : ℤ)) := by
    rw [hQ2ball]; exact convex_ball _ _
  set P : ℝ := ‖p‖ with hPdef
  have hP0 : 0 ≤ P := norm_nonneg _
  set Φ : ℝ := lipPin (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) (k + 1) x₀ (g x₀) u.toFun p with hΦdef
  have hΦ0 : 0 ≤ Φ := by
    rw [hΦdef]; unfold lipPin lipL2
    exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
  -- the pointwise bound of `u - g` against the affine function
  have hdist : ∀ x ∈ shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W, ‖x - x₀‖ ≤ 3 * (3 : ℝ) ^ k :=
    fun x hx => lip_bdry_approx_dist_le hx₀ hx.1
  set B : ℝ := 3 * (3 : ℝ) ^ k * ((d : ℝ) * P + G1) with hB
  have hB0 : 0 ≤ B := by positivity
  have hRb : ∀ x ∈ shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W,
      |g x₀ + vecDot p (x - x₀) - g x| ≤ B := by
    intro x hx
    have hxQ2 : x ∈ shiftCube z ((k + 2 : ℕ) : ℤ) := hQ12 hx.1
    have h1 := lip_bdry_approx_abs_vecDot_le p (x - x₀)
    have h2 : |g x₀ - g x| ≤ G1 * (3 * (3 : ℝ) ^ k) := by
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := g)
        (fun y _ => (hg.differentiable (by norm_num)).differentiableAt) hDg hconv hxQ2 hx₀Q2
      rw [Real.norm_eq_abs] at this
      calc |g x₀ - g x| ≤ G1 * ‖x₀ - x‖ := this
        _ = G1 * ‖x - x₀‖ := by rw [norm_sub_rev]
        _ ≤ G1 * (3 * (3 : ℝ) ^ k) := mul_le_mul_of_nonneg_left (hdist x hx) hG1
    have h4 : (d : ℝ) * P * ‖x - x₀‖ ≤ (d : ℝ) * P * (3 * (3 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left (hdist x hx) (by positivity)
    have h5 : g x₀ + vecDot p (x - x₀) - g x = vecDot p (x - x₀) + (g x₀ - g x) := by ring
    rw [h5]
    calc |vecDot p (x - x₀) + (g x₀ - g x)| ≤ |vecDot p (x - x₀)| + |g x₀ - g x| :=
          abs_add_le _ _
      _ ≤ _ := by rw [hB]; linarith only [h1, h2, h4]

  -- integrability
  have hmemu : MemLp u.toFun 2 (volume.restrict (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)) :=
    u.memL2.mono_measure (Measure.restrict_mono hD12 le_rfl)
  have hfin1 : IsFiniteMeasure (volume.restrict (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)) :=
    ⟨by simpa using hD1t.lt_top⟩
  have hcA : Continuous (fun x : Vec d => g x₀ + vecDot p (x - x₀)) :=
    continuous_const.add (lip_bdry_approx_continuous_aff p x₀)
  have hcR : Continuous (fun x : Vec d => g x₀ + vecDot p (x - x₀) - g x) :=
    hcA.sub hg.continuous
  have hRmem : MemLp (fun x : Vec d => g x₀ + vecDot p (x - x₀) - g x) 2
      (volume.restrict (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)) :=
    MemLp.of_bound hcR.aestronglyMeasurable B
      ((ae_restrict_iff' (hD1o.measurableSet)).2 (Filter.Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs]; exact hRb x hx))
  have hAmem : MemLp (fun x : Vec d => g x₀ + vecDot p (x - x₀)) 2
      (volume.restrict (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)) :=
    MemLp.of_bound hcA.aestronglyMeasurable (|g x₀| + (d : ℝ) * P * (3 * (3 : ℝ) ^ k))
      ((ae_restrict_iff' (hD1o.measurableSet)).2 (Filter.Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs]
        have h1 := lip_bdry_approx_abs_vecDot_le p (x - x₀)
        have h4 : (d : ℝ) * P * ‖x - x₀‖ ≤ (d : ℝ) * P * (3 * (3 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (hdist x hx) (by positivity)
        calc |g x₀ + vecDot p (x - x₀)| ≤ |g x₀| + |vecDot p (x - x₀)| := abs_add_le _ _
          _ ≤ _ := by linarith only [h1, h4]))
  have hU1mem : MemLp (fun x : Vec d => u.toFun x - g x₀ - vecDot p (x - x₀)) 2
      (volume.restrict (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)) := by
    have e : (fun x : Vec d => u.toFun x - g x₀ - vecDot p (x - x₀)) =
        fun x => u.toFun x - (g x₀ + vecDot p (x - x₀)) := funext fun x => by ring
    rw [e]
    exact hmemu.sub hAmem
  have hugmem : MemLp (fun x : Vec d => u.toFun x - g x) 2
      (volume.restrict (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)) := by
    have e : (fun x : Vec d => u.toFun x - g x) =
        fun x => (u.toFun x - g x₀ - vecDot p (x - x₀)) +
          (g x₀ + vecDot p (x - x₀) - g x) := funext fun x => by ring
    rw [e]
    exact hU1mem.add hRmem
  have hL2 : lipL2 (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) (fun x => u.toFun x - g x) ≤
      3 * (3 : ℝ) ^ k * (Φ + (d : ℝ) * P + G1) := by
    have e : (fun x : Vec d => u.toFun x - g x) =
        fun x => (u.toFun x - g x₀ - vecDot p (x - x₀)) +
          (g x₀ + vecDot p (x - x₀) - g x) := funext fun x => by ring
    rw [e]
    refine (lipL2_add_le hD1v hD1t hU1mem hRmem).trans ?_
    have hR := lipL2_le_of_ae_abs_le hB0 hD1v hD1t
      (f := fun x : Vec d => g x₀ + vecDot p (x - x₀) - g x)
      ((ae_restrict_iff' (hD1o.measurableSet)).2 (Filter.Eventually.of_forall hRb))
    have hΦe : lipL2 (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)
        (fun x : Vec d => u.toFun x - g x₀ - vecDot p (x - x₀)) = 3 * (3 : ℝ) ^ k * Φ := by
      rw [hΦdef]; unfold lipPin
      have : 3 * (3 : ℝ) ^ k * ((3 : ℝ)⁻¹) ^ (k + 1) = 1 := by
        rw [← h3, ← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
      rw [← mul_assoc, this, one_mul]
    rw [hΦe]
    have : 3 * (3 : ℝ) ^ k * (Φ + (d : ℝ) * P + G1) = 3 * (3 : ℝ) ^ k * Φ + B := by
      rw [hB]; ring
    rw [this]
    exact add_le_add le_rfl hR
  -- the Caccioppoli block at the scale `k + 1`
  have e1 : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by push_cast; ring
  obtain ⟨f1, hf1m, hf1b, hf1sol, -⟩ := lip_bdry_approx_repl hD2o hD1o hD12 hell hsol hF0 hFae
  set u1 : H1Function (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) := u.restrict hD1o hD12 with hu1
  have hagree : (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) ∩ shiftCube z ((k + 1 : ℕ) : ℤ) =
      (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) ∩ shiftCube z ((k + 1 : ℕ) : ℤ) := by
    ext x
    constructor
    · rintro ⟨⟨_, hw⟩, hq⟩
      exact ⟨⟨hq, hw⟩, hq⟩
    · rintro ⟨⟨hq, hw⟩, _⟩
      exact ⟨⟨hQ12 hq, hw⟩, hq⟩
  have hz1 : LocalizedZeroTraceFunctionOn (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)
      (shiftCube z ((k + 1 : ℕ) : ℤ)) (fun x => u1.toFun x - g x) :=
    lip_localized_restrict hD1o (lip_bdry_approx_isOpen_cube z _) hD12 hQ12 hagree hz
  have hQb : lpBar (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) 2 (fun x => u1.toFun x - g x) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (k + 1) * (Φ + (d : ℝ) * P + G1)) := by
    show lpBar (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) 2 (fun x => u.toFun x - g x) ≤ _
    rw [← ofReal_lipL2 hD1v hD1t hugmem]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [h3]
    exact hL2
  have hFb : lpBar (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) 2 f1 ≤ ENNReal.ofReal F :=
    lip_int_harm_of_l2_lpBar_le_of_ae_bound hD1v hD1t 2 hf1m hf1b
  have hQb0 : 0 ≤ (3 : ℝ) ^ (k + 1) * (Φ + (d : ℝ) * P + G1) := by positivity
  have cacc := lip_bdry_approx_cacc hc1 hnu hs0 hCin0 (by rw [e1]; exact hD0)
    (by rw [e1]; exact hD0t) (by rw [e1]; exact hD01) f1 g u1 hg hf1sol hz1 hQb hFb
    (fun x hx => hDg x (hQ12 hx.1)) (fun x hx => hD2g x (hQ12 hx.1))
    hQb0 hF0 hG1 hG2
  rw [e1] at cacc
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hqk : (((k + 1 : ℕ) : ℝ)) ^ (-E) ≤ (k : ℝ) ^ (-E) :=
    Real.rpow_le_rpow_of_nonpos hk0 (by push_cast; linarith only) (by linarith only [hE])
  have hq0 : 0 ≤ (((k + 1 : ℕ) : ℝ)) ^ (-E) := by positivity
  have harith := lip_bdry_approx_u_arith (Cin := Cin) (s := s) (Φ := Φ) (dP := (d : ℝ) * P)
    (G1 := G1) (G2 := G2) (F := F) (q := (((k + 1 : ℕ) : ℝ)) ^ (-E)) (kE := (k : ℝ) ^ (-E)) k
    hCin hs hΦ0 (by positivity) hG1 hG2 hF0 hq0 hqk
  have hX0 : 0 ≤ lipGradL2 (shiftCube z (k : ℤ) ∩ W) u1.grad := ENNReal.toReal_nonneg
  have hZ0 : 0 ≤ Cin * (Φ + (d : ℝ) * P + 2 * G1 + 3 * (s⁻¹ * (3 : ℝ) ^ k * F) +
        3 * (((k : ℝ)) ^ (-E) * (3 : ℝ) ^ k * G2)) := by positivity
  exact lip_bdry_approx_sgrad_le hnu hs0 hX0 hZ0 (cacc.trans harith)


end SuperdiffusionCLT.Section7
