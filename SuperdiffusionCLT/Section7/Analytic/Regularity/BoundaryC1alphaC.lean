/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaB
public import SuperdiffusionCLT.Section7.Analytic.Regularity.HalfCubeW2pG

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Flat decay on the half cube for zero-trace solutions

For a zero-trace solution `w` of the perturbed equation `-∇·(A∇w) = F` on the half cube
`flatHalfCube e m` with `F ∈ L^p`, `p > d`, the half axis cubes `Q_s^+ = (-s/2, s/2)^{d-1} × (0, s)`
touching the flat face satisfy a first order Taylor bound with the Hölder gain `(s/3^m)^{1-d/p}`.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The base corner of the half axis cube of side `s` touching the flat face `x e = 0`. -/
noncomputable def r3c_faceBase (e : Fin d) (s : ℝ) : Vec d := fun i => if i = e then 0 else -(s / 2)

/-- The half axis cube `Q_s^+` of side `s` touching the flat face. -/
def r3c_faceCube (e : Fin d) (s : ℝ) : Set (Vec d) := axisCube (r3c_faceBase e s) s

theorem r3c_faceCube_subset (e : Fin d) (m : ℤ) {s : ℝ} (hsm : s ≤ (3 : ℝ) ^ m / 2) :
    r3c_faceCube e s ⊆ flatHalfCube e m := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [hc_mem_openCubeSet_originCube_iff]
    intro i
    have h := hx i (Set.mem_univ i)
    simp only [Set.mem_Ioo, r3c_faceBase] at h
    by_cases hi : i = e
    · subst hi
      simp only [ite_true, zero_add] at h
      constructor <;> linarith only [h.1, h.2, hsm]
    · simp only [hi, ite_false] at h
      constructor <;> linarith only [h.1, h.2, hsm]
  · have h := hx e (Set.mem_univ e)
    simp only [Set.mem_Ioo, r3c_faceBase, ite_true, zero_add] at h
    exact h.1

theorem r3c_volume_flatHalf (e : Fin d) (m : ℤ) :
    volume.restrict (flatHalfCube e m) =
      (ENNReal.ofReal (cubeVolume (originCube d m))⁻¹)⁻¹ • flatHalfMeasure e m := by
  have hV : (0 : ℝ) < cubeVolume (originCube d m) := cubeVolume_pos _
  have h1 : ENNReal.ofReal (cubeVolume (originCube d m))⁻¹ ≠ 0 := by simpa using hV
  rw [flatHalfMeasure_eq, smul_smul, ENNReal.inv_mul_cancel h1 ENNReal.ofReal_ne_top, one_smul]

/-- A function in `L^p` of the normalized half cube measure is in `L^p` of Lebesgue measure. -/
theorem r3c_memLp_flatHalf (e : Fin d) (m : ℤ) {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    {F : Vec d → E} (hF : MemLp F p (flatHalfMeasure e m)) :
    MemLp F p (volume.restrict (flatHalfCube e m)) := by
  have hV : (0 : ℝ) < cubeVolume (originCube d m) := cubeVolume_pos _
  have h1 : ENNReal.ofReal (cubeVolume (originCube d m))⁻¹ ≠ 0 := by simpa using hV
  refine MemLp.of_measure_le_smul (c := (ENNReal.ofReal (cubeVolume (originCube d m))⁻¹)⁻¹)
    (ENNReal.inv_ne_top.2 h1) ?_ hF
  rw [r3c_volume_flatHalf]

/-- Passing from the normalized half cube measure to Lebesgue measure. -/
theorem r3c_eLpNorm_flatHalf (e : Fin d) (m : ℤ) {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (F : Vec d → E) :
    (eLpNorm F p (volume.restrict (flatHalfCube e m))).toReal =
      ((3 : ℝ) ^ m) ^ ((d : ℝ) / p.toReal) * flatHalfNorm e m p F := by
  have hV : (0 : ℝ) < cubeVolume (originCube d m) := cubeVolume_pos _
  rw [r3c_volume_flatHalf, eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hpt, flatHalfNorm]
  rw [smul_eq_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (inv_nonneg.2 hV.le), inv_inv]
  have hp1 : (1 / p).toReal = 1 / p.toReal := by simp
  rw [hp1, cubeVolume, cubeScaleFactor_originCube, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- **F0b: flat decay for zero-trace solutions on the half cube.**  With `α = 1 - d/p`, on every half
axis cube `Q_s^+` touching the face (`s ≤ 3^m/2`) the solution `w ∈ H¹₀(flatHalfCube e m)` of
`-∇·(A∇w) = F` is, up to a continuous representative, affine up to an error
`C s (s/3^m)^α 3^m ‖F‖_{L̲^p}`. -/
theorem r3c_flat_decay (hd : 2 ≤ d) (e : Fin d) {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ (m : ℤ) (A : CoeffField d) (K : ℝ),
        (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) →
        (∀ x ∈ flatHalfCube e m, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε) →
        (∀ x ∈ flatHalfCube e m, ∀ i j k,
          |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K) →
        K * cubeScaleFactor (originCube d m) ≤ ε →
        ∀ F : Vec d → ℝ, MemLp F (ENNReal.ofReal p) (flatHalfMeasure e m) →
          ∀ w : H10Function (flatHalfCube e m),
            IsH10WeakSolution A (flatHalfCube e m) F (fun _ => 0) w →
            ∀ s : ℝ, 0 < s → s ≤ (3 : ℝ) ^ m / 2 →
              ∃ (ŵ : Vec d → ℝ) (c : Vec d), ContinuousOn ŵ (r3c_faceCube e s) ∧
                ŵ =ᵐ[volume.restrict (r3c_faceCube e s)] w.toH1Function.toFun ∧
                ∀ x ∈ r3c_faceCube e s, ∀ y ∈ r3c_faceCube e s,
                  |ŵ x - ŵ y - vecDot c (x - y)| ≤
                    C * s * (s / (3 : ℝ) ^ m) ^ (1 - (d : ℝ) / p) * (3 : ℝ) ^ m *
                      flatHalfNorm e m (ENNReal.ofReal p) F := by
  have : NeZero d := ⟨by omega⟩
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hp0 : 0 < p := by linarith only [hd1, hp]
  have hp2 : (2 : ℝ≥0∞) < ENNReal.ofReal p := by
    have : (2 : ℝ) < p := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith only [this, hp]
    calc (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
      _ < ENNReal.ofReal p := (ENNReal.ofReal_lt_ofReal_iff hp0).2 this
  obtain ⟨ε, C, hε, hC, H⟩ := flatW2p_halfCube_scalar hd e hp2 ENNReal.ofReal_lt_top
  set C₀ : ℝ := 4 * (d : ℝ) * (1 / (1 - (d : ℝ) / p)) with hC₀
  have hα : 0 < 1 - (d : ℝ) / p := by
    have : (d : ℝ) / p < 1 := (div_lt_one hp0).2 hp
    linarith only [this]
  have hC₀0 : 0 < C₀ := by
    have : 0 < 1 / (1 - (d : ℝ) / p) := one_div_pos.2 hα
    rw [hC₀]; positivity
  refine ⟨ε, C₀ * C₀ * C, hε, by positivity, ?_⟩
  intro m A K hA hAε hAK hKℓ F hF w hw s hs hsm
  obtain ⟨Hs, hHmem, hHb⟩ := H m A K hA hAε hAK hKℓ F hF w hw
  have hQ := r3c_faceCube_subset e m hsm
  set Q := r3c_faceCube e s with hQdef
  have h1 : MemLp (fun x => HilbertMat.ofMat (fun i j => Hs.hess i j x)) (ENNReal.ofReal p)
      (volume.restrict (flatHalfCube e m)) := by
    exact r3c_memLp_flatHalf e m hHmem
  have hHQ : MemLp (fun x => HilbertMat.ofMat (fun i j => Hs.hess i j x)) (ENNReal.ofReal p)
      (volume.restrict Q) := h1.mono_measure (Measure.restrict_mono hQ le_rfl)
  obtain ⟨ŵ, c, hc, hae, hbd⟩ := r3c_taylor_axisCube hs hQ hp Hs hHQ
  refine ⟨ŵ, c, hc, hae, fun x hx y hy => (hbd x hx y hy).trans ?_⟩
  set R : ℝ := (3 : ℝ) ^ m with hR
  have hRpos : 0 < R := zpow_pos (by norm_num) m
  set N := (eLpNorm (fun x => HilbertMat.ofMat (fun i j => Hs.hess i j x)) (ENNReal.ofReal p)
    (volume.restrict Q)).toReal with hN
  set Hn := flatHalfNorm e m (ENNReal.ofReal p) (fun x => HilbertMat.ofMat (fun i j => Hs.hess i j x))
    with hHn
  have hp0' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hN1 : N ≤ R ^ ((d : ℝ) / p) * (C * flatHalfNorm e m (ENNReal.ofReal p) F) := by
    have h2 : N ≤ (eLpNorm (fun x => HilbertMat.ofMat (fun i j => Hs.hess i j x))
        (ENNReal.ofReal p) (volume.restrict (flatHalfCube e m))).toReal :=
      ENNReal.toReal_mono h1.eLpNorm_ne_top
        (eLpNorm_mono_measure _ (Measure.restrict_mono hQ le_rfl))
    rw [r3c_eLpNorm_flatHalf e m hp0' ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left hHb (Real.rpow_nonneg hRpos.le _))
  have hkey : s ^ (1 + (1 - (d : ℝ) / p)) * R ^ ((d : ℝ) / p) = s * (s / R) ^ (1 - (d : ℝ) / p) * R := by
    have e1 : s ^ (1 + (1 - (d : ℝ) / p)) = s * s ^ (1 - (d : ℝ) / p) := by
      rw [Real.rpow_add hs, Real.rpow_one]
    have e2 : (s / R) ^ (1 - (d : ℝ) / p) * R ^ (1 - (d : ℝ) / p) = s ^ (1 - (d : ℝ) / p) := by
      rw [← Real.mul_rpow (div_nonneg hs.le hRpos.le) hRpos.le, div_mul_cancel₀ _ hRpos.ne']
    have e3 : R ^ (1 - (d : ℝ) / p) * R ^ ((d : ℝ) / p) = R := by
      rw [← Real.rpow_add hRpos]; simp
    rw [e1, ← e2]
    calc s * ((s / R) ^ (1 - (d : ℝ) / p) * R ^ (1 - (d : ℝ) / p)) * R ^ ((d : ℝ) / p)
        = s * (s / R) ^ (1 - (d : ℝ) / p) * (R ^ (1 - (d : ℝ) / p) * R ^ ((d : ℝ) / p)) := by ring
      _ = _ := by rw [e3]
  have hs0 : 0 ≤ s ^ (1 + (1 - (d : ℝ) / p)) := Real.rpow_nonneg hs.le _
  calc C₀ * C₀ * s ^ (1 + (1 - (d : ℝ) / p)) * N
      ≤ C₀ * C₀ * s ^ (1 + (1 - (d : ℝ) / p)) *
          (R ^ ((d : ℝ) / p) * (C * flatHalfNorm e m (ENNReal.ofReal p) F)) := by
        gcongr
    _ = C₀ * C₀ * C * (s ^ (1 + (1 - (d : ℝ) / p)) * R ^ ((d : ℝ) / p)) *
          flatHalfNorm e m (ENNReal.ofReal p) F := by ring
    _ = _ := by rw [hkey]; ring

end SuperdiffusionCLT.Section7
