/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Defs
public import Homogenization.Sobolev.CubeEmbedding.LimitFiniteP
public import Homogenization.Sobolev.MatchedPair.ScaledPoincare
public import Homogenization.Sobolev.W1p.FiniteMeasureDowngrade

/-!
# Cube Sobolev inequality at the exponent `sobStar d`

For `w ∈ H¹₀(axisCube z L)` and `d ≥ 2`,
`L^{-d/2^*} ‖w‖_{L^{2^*}} ≤ C L^{1-d/2} ‖∇w‖_{L²}`, with `C` depending only on `d`.
The case `d ≥ 3` uses `p = 2`, the case `d = 2` uses `p = 3/2` (so `q = 6`).
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem abs_le_eucNorm (v : Vec d) (i : Fin d) : |v i| ≤ eucNorm v := by
  unfold eucNorm
  apply Real.abs_le_sqrt
  unfold vecNormSq vecDot
  have : v i * v i ≤ ∑ j, v j * v j :=
    Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  linarith only [this, sq (v i)]

theorem eLpNorm_coord_le_eucNorm (z : Vec d) (L : ℝ) (u : H1Function (axisCube z L)) (i : Fin d) :
    eLpNorm (fun x => u.grad x i) 2 (volume.restrict (axisCube z L)) ≤
      eLpNorm (fun x => eucNorm (u.grad x)) 2 (volume.restrict (axisCube z L)) := by
  refine eLpNorm_mono (u.gradMemL2 i).aestronglyMeasurable ?_
  intro x
  have h0 : 0 ≤ eucNorm (u.grad x) := Real.sqrt_nonneg _
  rw [Real.norm_eq_abs, Real.norm_of_nonneg h0]
  exact abs_le_eucNorm _ _

theorem measure_univ_axisCube (z : Vec d) (L : ℝ) :
    (volume.restrict (axisCube z L)) Set.univ = ENNReal.ofReal L ^ d := by
  rw [Measure.restrict_apply_univ]
  simp only [axisCube, Real.volume_pi_Ioo, add_sub_cancel_left]
  simp

theorem measure_univ_axisCube_rpow (z : Vec d) {L : ℝ} (hL : 0 < L) (κ : ℝ) :
    (volume.restrict (axisCube z L)) Set.univ ^ κ = ENNReal.ofReal (L ^ ((d : ℝ) * κ)) := by
  rw [measure_univ_axisCube, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    ENNReal.ofReal_rpow_of_pos hL]

theorem cube_sobolev_aux (hd : 2 ≤ d) (p : FiniteLpExponent) (hp2 : p.exponent ≤ 2)
    (hpd : p.exponent.toReal < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : FiniteLpExponent,
      (q.exponent.toReal)⁻¹ = p.exponent.toReal⁻¹ - (d : ℝ)⁻¹ →
      ∀ (z : Vec d) (L : ℝ), 0 < L → ∀ u : H10Function (axisCube z L),
        eLpNorm u.toH1Function.toFun q.exponent (volume.restrict (axisCube z L)) ≤
          ENNReal.ofReal (C * L ^ ((d : ℝ) * (p.exponent.toReal⁻¹ - 2⁻¹))) *
            eLpNorm (fun x => eucNorm (u.toH1Function.grad x)) 2
              (volume.restrict (axisCube z L)) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C, hCpos, hC⟩ := Homogenization.cubeSobolevEmbedding_finiteLp (by omega : 0 < d) p hpd
  have hP0 := Homogenization.unitDirichletPoincareConst_nonneg d
  refine ⟨(C : ℝ) * d * (1 + Homogenization.unitDirichletPoincareConst d), by positivity, ?_⟩
  intro q hq z L hL u
  set P := Homogenization.unitDirichletPoincareConst d with hPdef
  set M := volume.restrict (axisCube z L) with hM
  set A := eLpNorm (fun x => eucNorm (u.toH1Function.grad x)) 2 M with hA
  set κ : ℝ := p.exponent.toReal⁻¹ - 2⁻¹ with hκ
  set K : ℝ≥0∞ := ENNReal.ofReal (L ^ ((d : ℝ) * κ)) with hK
  have hpne : p.exponent ≠ ⊤ := p.lt_top.ne
  have hH : ∀ f : Vec d → ℝ, AEStronglyMeasurable f M →
      eLpNorm f p.exponent M ≤ eLpNorm f 2 M * K := by
    intro f hf
    have h := Homogenization.eLpNorm_finiteMeasure_downgrade_le (U := axisCube z L) p hp2 f hf
    have hrw : (1 / p.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal) = κ := by
      simp [hκ]
    rw [hrw] at h
    have hm : (volume.restrict (axisCube z L)) Set.univ ^ κ = K := measure_univ_axisCube_rpow z hL κ
    rw [hm] at h
    exact h
  -- the downgraded function
  have h1 := hC q hq z L hL (u.toH1Function.toW1pOfExponentLETwo p hp2)
  change eLpNorm u.toH1Function.toFun q.exponent M ≤ _ at h1
  have hu2 : eLpNorm u.toH1Function.toFun 2 M ≠ ⊤ := u.toH1Function.memL2.eLpNorm_ne_top
  set S := ∑ i : Fin d, eLpNorm (fun x => u.toH1Function.grad x i) 2 M with hS
  have hSA : S ≤ (d : ℝ≥0∞) * A := by
    calc S ≤ ∑ _i : Fin d, A :=
          Finset.sum_le_sum fun i _ => eLpNorm_coord_le_eucNorm z L u.toH1Function i
      _ = d * A := by simp
  have hSfin : ∀ i : Fin d, eLpNorm (fun x => u.toH1Function.grad x i) 2 M ≠ ⊤ :=
    fun i => (u.toH1Function.gradMemL2 i).eLpNorm_ne_top
  have hSne : S ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ => hSfin i
  have hpo := Homogenization.scaled_dirichlet_poincare z hL u
  have hPo : eLpNorm u.toH1Function.toFun 2 M ≤ ENNReal.ofReal (P * L) * S := by
    have hsum : (∑ i, (eLpNorm (fun x => u.toH1Function.grad x i) 2 M).toReal) = S.toReal := by
      rw [hS, ENNReal.toReal_sum (fun i _ => hSfin i)]
    have hpo' : (eLpNorm u.toH1Function.toFun 2 M).toReal ≤ P * L * S.toReal := by
      rw [← hsum]; exact hpo
    calc eLpNorm u.toH1Function.toFun 2 M
        = ENNReal.ofReal ((eLpNorm u.toH1Function.toFun 2 M).toReal) :=
          (ENNReal.ofReal_toReal hu2).symm
      _ ≤ ENNReal.ofReal (P * L * S.toReal) := ENNReal.ofReal_le_ofReal hpo'
      _ = ENNReal.ofReal (P * L) * S := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hSne]
  have hcoordP : (∑ i : Fin d, eLpNorm (fun x => u.toH1Function.grad x i) p.exponent M) ≤ S * K := by
    calc _ ≤ ∑ i : Fin d, eLpNorm (fun x => u.toH1Function.grad x i) 2 M * K :=
          Finset.sum_le_sum fun i _ => hH _ (u.toH1Function.gradMemL2 i).aestronglyMeasurable
      _ = S * K := by rw [hS, Finset.sum_mul]
  have hup : eLpNorm u.toH1Function.toFun p.exponent M ≤ ENNReal.ofReal (P * L) * S * K :=
    (hH _ u.toH1Function.memL2.aestronglyMeasurable).trans (mul_le_mul_left hPo K)
  have h2 : eLpNorm u.toH1Function.toFun q.exponent M ≤
      (C : ℝ≥0∞) * ((∑ i : Fin d, eLpNorm (fun x => u.toH1Function.grad x i) p.exponent M) +
        ENNReal.ofReal L⁻¹ * eLpNorm u.toH1Function.toFun p.exponent M) := h1
  have he : ENNReal.ofReal L⁻¹ * ENNReal.ofReal (P * L) = ENNReal.ofReal P := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hkey : (C : ℝ≥0∞) * (S * K + ENNReal.ofReal L⁻¹ * (ENNReal.ofReal (P * L) * S * K)) =
      ENNReal.ofReal ((C : ℝ) * (1 + P)) * S * K := by
    rw [show ENNReal.ofReal L⁻¹ * (ENNReal.ofReal (P * L) * S * K) =
      (ENNReal.ofReal L⁻¹ * ENNReal.ofReal (P * L)) * S * K by ring, he,
      ENNReal.ofReal_mul (p := (C : ℝ)) (by positivity),
      ENNReal.ofReal_add (by norm_num) hP0, ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal]
    ring
  have hc : ENNReal.ofReal ((C : ℝ) * d * (1 + P) * L ^ ((d : ℝ) * κ)) =
      ENNReal.ofReal ((C : ℝ) * (1 + P)) * d * K := by
    rw [hK, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc eLpNorm u.toH1Function.toFun q.exponent M
      ≤ (C : ℝ≥0∞) * (S * K + ENNReal.ofReal L⁻¹ * (ENNReal.ofReal (P * L) * S * K)) :=
        h2.trans (mul_le_mul_right (add_le_add hcoordP (mul_le_mul_right hup _)) _)
    _ = ENNReal.ofReal ((C : ℝ) * (1 + P)) * S * K := hkey
    _ ≤ ENNReal.ofReal ((C : ℝ) * (1 + P)) * (d * A) * K := by gcongr
    _ = ENNReal.ofReal ((C : ℝ) * d * (1 + P) * L ^ ((d : ℝ) * κ)) * A := by rw [hc]; ring

theorem cube_sobolev_finish (hd : 2 ≤ d) (p q : FiniteLpExponent) (hp2 : p.exponent ≤ 2)
    (hpd : p.exponent.toReal < d) (hqexp : q.exponent = ENNReal.ofReal (sobStar d))
    (hq : (sobStar d)⁻¹ = p.exponent.toReal⁻¹ - (d : ℝ)⁻¹) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Vec d) (L : ℝ), 0 < L → ∀ u : H10Function (axisCube z L),
      ENNReal.ofReal (L ^ (-(d : ℝ) / sobStar d)) *
          eLpNorm u.toH1Function.toFun (ENNReal.ofReal (sobStar d))
            (volume.restrict (axisCube z L)) ≤
        ENNReal.ofReal (C * L ^ (1 - (d : ℝ) / 2)) *
          eLpNorm (fun x => eucNorm (u.toH1Function.grad x)) 2
            (volume.restrict (axisCube z L)) := by
  obtain ⟨C, hC0, hC⟩ := cube_sobolev_aux hd p hp2 hpd
  refine ⟨C, hC0, ?_⟩
  intro z L hL u
  have hs : 0 < sobStar d := lt_trans (by norm_num) (two_lt_sobStar hd)
  have hqr : q.exponent.toReal = sobStar d := by
    rw [hqexp, ENNReal.toReal_ofReal hs.le]
  have h := hC q (by rw [hqr]; exact hq) z L hL u
  rw [hqexp] at h
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [this]
  have hexp : -(d : ℝ) / sobStar d + (d : ℝ) * (p.exponent.toReal⁻¹ - 2⁻¹) = 1 - (d : ℝ) / 2 := by
    have : -(d : ℝ) / sobStar d = -(d : ℝ) * (sobStar d)⁻¹ := by rw [div_eq_mul_inv]
    rw [this, hq]
    field_simp
    ring
  calc ENNReal.ofReal (L ^ (-(d : ℝ) / sobStar d)) *
        eLpNorm u.toH1Function.toFun (ENNReal.ofReal (sobStar d)) (volume.restrict (axisCube z L))
      ≤ ENNReal.ofReal (L ^ (-(d : ℝ) / sobStar d)) *
          (ENNReal.ofReal (C * L ^ ((d : ℝ) * (p.exponent.toReal⁻¹ - 2⁻¹))) *
            eLpNorm (fun x => eucNorm (u.toH1Function.grad x)) 2
              (volume.restrict (axisCube z L))) := by gcongr
    _ = ENNReal.ofReal (C * L ^ (1 - (d : ℝ) / 2)) *
          eLpNorm (fun x => eucNorm (u.toH1Function.grad x)) 2
            (volume.restrict (axisCube z L)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [← hexp, Real.rpow_add hL]
        ring

/-- **Cube Sobolev inequality at `2^*`.** -/
theorem cube_sobolev_sobStar (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Vec d) (L : ℝ), 0 < L → ∀ u : H10Function (axisCube z L),
      ENNReal.ofReal (L ^ (-(d : ℝ) / sobStar d)) *
          eLpNorm u.toH1Function.toFun (ENNReal.ofReal (sobStar d))
            (volume.restrict (axisCube z L)) ≤
        ENNReal.ofReal (C * L ^ (1 - (d : ℝ) / 2)) *
          eLpNorm (fun x => eucNorm (u.toH1Function.grad x)) 2
            (volume.restrict (axisCube z L)) := by
  by_cases h2 : d = 2
  · subst h2
    let p : FiniteLpExponent := ⟨ENNReal.ofReal (3 / 2), by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num),
      ENNReal.ofReal_lt_top⟩
    let q : FiniteLpExponent := ⟨ENNReal.ofReal 6, by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num),
      ENNReal.ofReal_lt_top⟩
    have hpr : p.exponent.toReal = 3 / 2 := ENNReal.toReal_ofReal (by norm_num)
    refine cube_sobolev_finish hd p q ?_ ?_ ?_ ?_
    · show ENNReal.ofReal (3 / 2) ≤ 2
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    · rw [hpr]; norm_num
    · rw [sobStar_two]
    · rw [hpr, sobStar_two]; norm_num
  · have h3 : 3 ≤ d := by omega
    let p : FiniteLpExponent := ⟨2, by norm_num, by norm_num⟩
    let q : FiniteLpExponent := ⟨ENNReal.ofReal (sobStar d), by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith only [two_lt_sobStar hd])).2
        (by linarith only [two_lt_sobStar hd]),
      ENNReal.ofReal_lt_top⟩
    have hpr : p.exponent.toReal = 2 := by simp [p]
    refine cube_sobolev_finish hd p q le_rfl ?_ rfl ?_
    · rw [hpr]
      have : (3 : ℝ) ≤ d := by exact_mod_cast h3
      linarith only [this]
    · rw [hpr, inv_sobStar h3]
      norm_num

/-- Witness: the hypothesis `2 ≤ d` holds at `d = 2` and `d = 3`, and `H¹₀` of a cube is
nonempty, so the statement is not vacuous. -/
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Vec 2) (L : ℝ), 0 < L → ∀ u : H10Function (axisCube z L),
    ENNReal.ofReal (L ^ (-(2 : ℝ) / sobStar 2)) * eLpNorm u.toH1Function.toFun
        (ENNReal.ofReal (sobStar 2)) (volume.restrict (axisCube z L)) ≤
      ENNReal.ofReal (C * L ^ (1 - (2 : ℝ) / 2)) *
        eLpNorm (fun x => eucNorm (u.toH1Function.grad x)) 2 (volume.restrict (axisCube z L)) := by
  simpa using cube_sobolev_sobStar (d := 2) le_rfl

example (z : Vec 3) (L : ℝ) : Nonempty (H10Function (axisCube z L)) := ⟨0⟩

end SuperdiffusionCLT.Section7
