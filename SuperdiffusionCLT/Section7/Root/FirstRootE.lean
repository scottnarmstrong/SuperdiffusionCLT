/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.FirstRootD
public import SuperdiffusionCLT.Section7.Prereq.CenteringF
public import SuperdiffusionCLT.Frozen.Section5.SigmaBarSharpBounds

/-!
# The first root

`s5_superdiffusivity` has the statement of `Frozen.Section7.superdiffusivity` from three explicit
hypotheses: the `L^∞` homogenization proposition `hLinf`, the sharp bounds for the
diffusivities `hSigma`, and the scale estimates `hV6` of Section 2.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

/-! ### The dilation parameter -/

theorem s5_scaleK_pack {ε T : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hT : 1 ≤ T) :
    T / ε ≤ (3 : ℝ) ^ s12_scaleK (ε / T) ∧ (3 : ℝ) ^ s12_scaleK (ε / T) < 3 * (T / ε) ∧
      1 ≤ s12_scaleK (ε / T) ∧ (3 : ℝ) ^ s12_scaleK (ε / T) * ε ≤ 3 * T ∧
      |Real.log ε| / Real.log 3 ≤ (s12_scaleK (ε / T) : ℝ) ∧
      (s12_scaleK (ε / T) : ℝ) - 1 < |Real.log (ε / T)| / Real.log 3 := by
  have hT0 : 0 < T := by linarith only [hT]
  have hε' : 0 < ε / T := div_pos hε hT0
  have hε'2 : ε / T ≤ 1 / 2 := (div_le_self hε.le hT).trans hε2
  obtain ⟨h1, h2, h3⟩ := s12_scaleK_bounds hε' hε'2
  obtain ⟨hx1, hx2⟩ := s12_scaleK_x hε' hε'2
  have hinv : (ε / T)⁻¹ = T / ε := inv_div ε T
  rw [hinv] at h1 h2 hx1 hx2
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl' : Real.log (ε / T) < 0 := Real.log_neg hε' (by linarith only [hε'2])
  have hxe : Real.logb 3 (T / ε) = |Real.log (ε / T)| / Real.log 3 := by
    rw [Real.logb, ← hinv, Real.log_inv, abs_of_neg hl']
  have hl : Real.log ε < 0 := Real.log_neg hε (by linarith only [hε2])
  have hBB := s5_abs_log_div hε hε2 hT
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
  · have := mul_lt_mul_of_pos_right h2 hε
    have e : 3 * (T / ε) * ε = 3 * T := by field_simp
    linarith only [this, e]
  · have : |Real.log ε| / Real.log 3 ≤ |Real.log (ε / T)| / Real.log 3 :=
      div_le_div_of_nonneg_right (by linarith only [hBB, hlT]) hl3.le
    rw [← hxe] at this
    exact this.trans hx1
  · rw [← hxe]
    linarith only [hx2]

theorem s5_ratio_pack {cStar ε T Cn α sh : ℝ} (hc : 0 < cStar) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hT : 1 ≤ T) (hα1 : α ≤ 1) (hn2 : 2 ≤ (s12_scaleK (ε / T) : ℝ)) (hsh : 0 < sh)
    (hr : s12_scaleS cStar (ε / T) / sh ≤ 2)
    (hb : |s12_scaleS cStar (ε / T) / sh - 1| ≤ Cn * (s12_scaleK (ε / T) : ℝ) ^ (-α))
    (hlow : Real.sqrt (2 * cStar * Real.log 3 * (s12_scaleK (ε / T) : ℝ)) / 2 ≤ sh) :
    s12_scaleS cStar ε / sh ≤ 2 ∧
      |s12_scaleS cStar ε / sh - 1| ≤ (Cn + 4 * Real.log T / Real.log 3) *
        (s12_scaleK (ε / T) : ℝ) ^ (-α) ∧
      (Real.sqrt (2 * cStar * Real.log 3) / 2) * (s12_scaleK (ε / T) : ℝ) ^ ((1 : ℝ) / 2) ≤ sh := by
  set n : ℝ := (s12_scaleK (ε / T) : ℝ) with hn
  have hT0 : 0 < T := by linarith only [hT]
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hn0 : 0 < n := by linarith only [hn2]
  obtain ⟨hS, hdiff⟩ := s5_scaleS_shift hc hε hε2 hT
  obtain ⟨-, -, -, -, -, hlogn⟩ := s5_scaleK_pack hε hε2 hT
  rw [← hn] at hlogn
  set B' := |Real.log (ε / T)| with hB'
  have hB'pos : 0 < B' := by
    have hl' : Real.log (ε / T) < 0 :=
      Real.log_neg (div_pos hε hT0) (by
        have : ε / T ≤ ε := div_le_self hε.le hT
        linarith only [this, hε2])
    exact abs_pos.2 hl'.ne
  have hB'ge : (n / 2) * Real.log 3 ≤ B' := by
    have h1 : n - 1 < B' / Real.log 3 := hlogn
    rw [lt_div_iff₀ hl3] at h1
    have : n / 2 * Real.log 3 ≤ (n - 1) * Real.log 3 :=
      mul_le_mul_of_nonneg_right (by linarith only [hn2]) hl3.le
    linarith only [h1, this]
  have hη : Real.log T / B' ≤ 2 * Real.log T / (n * Real.log 3) := by
    rw [div_le_div_iff₀ hB'pos (by positivity)]
    have := mul_le_mul_of_nonneg_left hB'ge hlT
    linarith only [this]
  have hη0 : 0 ≤ Real.log T / B' := div_nonneg hlT hB'pos.le
  obtain ⟨hr1, hr2⟩ := s5_ratio_shift hsh hS hdiff hη0 hr
  refine ⟨hr1, ?_, ?_⟩
  · have h1 : 2 * (Real.log T / B') ≤ (4 * Real.log T / Real.log 3) * n ^ (-α) := by
      have hn1 : n ^ (-(1 : ℝ)) ≤ n ^ (-α) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith only [hn2]) (by linarith only [hα1])
      rw [Real.rpow_neg_one] at hn1
      have e : 2 * (2 * Real.log T / (n * Real.log 3)) = (4 * Real.log T / Real.log 3) * n⁻¹ := by
        field_simp
        ring
      calc 2 * (Real.log T / B') ≤ 2 * (2 * Real.log T / (n * Real.log 3)) :=
            mul_le_mul_of_nonneg_left hη (by norm_num)
        _ = (4 * Real.log T / Real.log 3) * n⁻¹ := e
        _ ≤ (4 * Real.log T / Real.log 3) * n ^ (-α) :=
            mul_le_mul_of_nonneg_left hn1 (by positivity)
    have e2 : (Cn + 4 * Real.log T / Real.log 3) * n ^ (-α) =
        Cn * n ^ (-α) + (4 * Real.log T / Real.log 3) * n ^ (-α) := by ring
    rw [e2]
    linarith only [hr2, hb, h1]
  · have e : Real.sqrt (2 * cStar * Real.log 3 * n) =
        Real.sqrt (2 * cStar * Real.log 3) * n ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow n]
    rw [e] at hlow
    linarith only [hlow]

theorem s5_entry_le {V : Set (Vec d)} {f : Vec d → Mat d} {MK : Mat d} {B : ℝ}
    (h : Homogenization.Book.Ch02.matrixOperatorNorm (volumeAverageMat V f - MK) ≤ B) :
    ∀ i j, |(Matrix.of fun i j => ⨍ w in V, f w i j) i j - MK i j| ≤ B := by
  intro i j
  have h1 := Homogenization.Book.Ch02.abs_entry_le_matrixOperatorNorm (volumeAverageMat V f - MK) i j
  have e : (Matrix.of fun i j => ⨍ w in V, f w i j) i j - MK i j =
      (volumeAverageMat V f - MK) i j := by
    simp only [Matrix.of_apply, Matrix.sub_apply, volumeAverageMat, volumeAverage, setAverage_eq,
      Measure.real, smul_eq_mul]
  rw [e]
  exact h1.trans h

/-! ### The pointwise estimate at one scale -/

theorem s5_pointwise [NeZero d] (hd : 2 ≤ d) {α α0 ρ σ' : ℝ} (hα : 0 < α) (hαα0 : α < α0)
    (hα1 : α ≤ 1) (hρ : ρ = 1 - 2 * α0) (hσ' : σ' ≤ 1 / 2 - α) {U : Set (Vec d)}
    (hU : IsSmoothBoundedDomain U) (zU : Vec d) {LU : ℝ} (hLU : 0 < LU) (hUL : U ⊆ axisCube zU LU)
    {T : ℝ} (hT : 1 ≤ T) (C1 Cn Cf : ℝ) (hC1 : 0 ≤ C1) (hCn : 0 ≤ Cn) (hCf : 0 ≤ Cf)
    (cStar : ℝ) (hc : 0 < cStar) :
    ∃ Cx N1 : ℝ, 0 < Cx ∧
      ∀ (nu : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (sh : ℕ → ℝ) {ε : ℝ},
        0 < ε → ε ≤ 1 / 2 → N1 ≤ (s12_scaleK (ε / T) : ℝ) →
        0 < sh (s12_scaleK (ε / T)) →
        s12_scaleS cStar (ε / T) / sh (s12_scaleK (ε / T)) ≤ 2 →
        |s12_scaleS cStar (ε / T) / sh (s12_scaleK (ε / T)) - 1| ≤
          Cn * (s12_scaleK (ε / T) : ℝ) ^ (-α) →
        Real.sqrt (2 * cStar * Real.log 3 * (s12_scaleK (ε / T) : ℝ)) / 2 ≤
          sh (s12_scaleK (ε / T)) →
        ∀ (Bw Bc : ℝ) (MK : Mat d),
          (∀ x ∈ ε⁻¹ • U, ∀ i j,
            |SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega x i j| ≤ Bw) →
          (∀ i j, |(Matrix.of fun i j => ⨍ w in ε⁻¹ • U,
              SuperdiffusionCLT.Section6.fullStreamRecentered omega w i j) i j - MK i j| ≤ Bc) →
          Bc ≤ Cf * (s12_scaleK (ε / T) : ℝ) ^ σ' →
          (∀ (f' : Vec d → ℝ) (g' u' uh' : H1Function (ε⁻¹ • U)),
              IsDirichletSolution (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                (ε⁻¹ • U) f' g' u' →
              IsDirichletSolution (fun _ => sh (s12_scaleK (ε / T)) • (1 : Mat d)) (ε⁻¹ • U)
                f' g' uh' →
              eLpNorm (fun x => u'.toFun x - uh'.toFun x) ⊤ (volume.restrict (ε⁻¹ • U)) +
                  hMinusOneVec (ε⁻¹ • U) (fun x => u'.grad x - uh'.grad x) +
                  hMinusOneVec (ε⁻¹ • U) (fun x =>
                    matVecMul ((sh (s12_scaleK (ε / T)))⁻¹ •
                      (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega x - MK))
                      (u'.grad x) - uh'.grad x) ≤
                ENNReal.ofReal (C1 * deltaScale 1 ρ (s12_scaleK (ε / T) : ℝ) *
                    ((sh (s12_scaleK (ε / T)))⁻¹ * (3 : ℝ) ^ (2 * s12_scaleK (ε / T)))) *
                    eLpNorm f' ⊤ (volume.restrict (ε⁻¹ • U)) +
                  ENNReal.ofReal (C1 * deltaScale 1 ρ (s12_scaleK (ε / T) : ℝ) *
                    Real.log (s12_scaleK (ε / T) : ℝ) * (3 : ℝ) ^ s12_scaleK (ε / T)) *
                    eLpNorm (fun x => eucNorm (g'.grad x)) ⊤ (volume.restrict (ε⁻¹ • U))) →
          ∀ (f : Vec d → ℝ) (g u uhom : H1Function U),
            IsDirichletSolution (fun x => ((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹ •
              epField nu omega ε x) U f g u →
            IsDirichletSolution (fun _ => (1 : Mat d)) U f g uhom →
              eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict U) +
                  hMinusOneVec U (fun x => u.grad x - uhom.grad x) +
                  hMinusOneVec U (fun x =>
                    matVecMul (((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹ •
                      epFieldCentered nu omega ε U x) (u.grad x) - uhom.grad x) ≤
                ENNReal.ofReal (Cx * (s12_scaleK (ε / T) : ℝ) ^ (-α)) *
                  (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict U) +
                    eLpNorm f ⊤ (volume.restrict U)) := by
  obtain ⟨CL, CH, hCL, hCH, hchain⟩ := s5_chain (d := d) hd
  obtain ⟨Cx, N1, hCx, hxi⟩ := s5_xi_bound (α := α) (α0 := α0) hα hαα0 CL CH LU C1
    (Cn + 4 * Real.log T / Real.log 3) (Real.sqrt (2 * cStar * Real.log 3) / 2) Cf T (d : ℝ)
    hCL.le hCH.le hLU.le hC1 (by
      have : 0 ≤ Real.log T := Real.log_nonneg hT
      have : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
      positivity) (by positivity) hCf hT (Nat.cast_nonneg d) hσ'
  refine ⟨Cx, max N1 2, hCx, ?_⟩
  intro nu omega sh ε hε hε2 hN hshp hS2 hSb hlow Bw Bc MK hBw hMK hBcCf hBB f g u uhom hu huh
  set n : ℕ := s12_scaleK (ε / T) with hndef
  have hN1 : N1 ≤ (n : ℝ) := (le_max_left _ _).trans hN
  have hn2 : 2 ≤ (n : ℝ) := (le_max_right _ _).trans hN
  have hT0 : 0 < T := by linarith only [hT]
  obtain ⟨hR1, hR2, hn1, h3T, -, -⟩ := s5_scaleK_pack hε hε2 hT
  obtain ⟨hr1, hr2, hr3⟩ := s5_ratio_pack (cStar := cStar) (Cn := Cn) (α := α) hc hε hε2 hT hα1
    hn2 hshp hS2 hSb hlow
  have hlog : 0 < |Real.log ε| := abs_pos.2 (Real.log_neg hε (by linarith only [hε2])).ne
  have hSpos : 0 < (2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hρα : (1 - ρ) / 2 = α0 := by rw [hρ]; ring
  have hCb0 : 0 ≤ C1 * deltaScale 1 ρ (n : ℝ) := by
    have hn0 : 0 < (n : ℝ) := by linarith only [hn2]
    unfold deltaScale
    have := Real.log_nonneg (show (1 : ℝ) ≤ n by linarith only [hn2])
    have := Real.rpow_pos_of_pos hn0 (-((1 - ρ) / 2))
    positivity
  have hCbb : C1 * deltaScale 1 ρ (n : ℝ) ≤ C1 * (n : ℝ) ^ (-α0) * Real.log (n : ℝ) := by
    unfold deltaScale
    rw [hρα]
    refine le_of_eq ?_
    ring
  by_cases hNf : eLpNorm f ⊤ (volume.restrict U) = ⊤
  · have hpos : 0 < Cx * (n : ℝ) ^ (-α) :=
      mul_pos hCx (Real.rpow_pos_of_pos (by linarith only [hn2]) _)
    rw [hNf, add_top, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top
  by_cases hNg : eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict U) = ⊤
  · have hpos : 0 < Cx * (n : ℝ) ^ (-α) :=
      mul_pos hCx (Real.rpow_pos_of_pos (by linarith only [hn2]) _)
    rw [hNg, top_add, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top
  have hch := hchain hU zU hLU hUL nu omega hε hSpos hshp n (C1 * deltaScale 1 ρ (n : ℝ)) Bw Bc
    hCb0 (by
      have := hMK ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
      exact (abs_nonneg _).trans this) hBw MK hMK hBB f g u uhom hu huh hNf hNg
  refine hch.trans ?_
  have hxi' := hxi n ε _ (sh n) Bc _ hN1 hε h3T hSpos hshp hr1 hr2 hr3
    ((abs_nonneg _).trans (hMK ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩))
    hBcCf hCb0 hCbb
  calc _ ≤ ENNReal.ofReal (Cx * (n : ℝ) ^ (-α)) * eLpNorm f ⊤ (volume.restrict U) +
        ENNReal.ofReal (Cx * (n : ℝ) ^ (-α)) *
          eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict U) :=
        add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hxi'.1) le_rfl)
          (mul_le_mul' (ENNReal.ofReal_le_ofReal hxi'.2) le_rfl)
    _ = _ := by ring

end SuperdiffusionCLT.Section7
