/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.SubcubeAvg
public import SuperdiffusionCLT.Section5.Response.NeumannOscillationPoincare
public import SuperdiffusionCLT.Section2.Estimates.Stream.CenteredShellFluxBounds

/-!
# Normalized `L^k` norms of fields on the subcubes `z + cu_n`

* `eLpNorm_nat_pow`: `‖f‖_{L^k}^k = ∫ ‖f‖ᵏ` for a natural exponent.
* `subcubeAvg_pow_cubeLpENorm`: the subcube average of `‖f‖^k_{L̲^k(z+cu_n)}` is `‖f‖^k_{L̲^k(cu_Kc)}`
  (the partition identity), for fields measurable on the large open cube.
* The subcubes of `cu_Kc` at scale `n` are contained in it and have scale `n`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- `‖f‖_{L^k}^k = ∫ ‖f‖^k` for a natural exponent `k ≠ 0`. -/
theorem eLpNorm_nat_pow {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (k : ℕ) (hk : k ≠ 0) (f : α → E) (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f k μ) ^ k = ∫⁻ x, ‖f x‖ₑ ^ k ∂μ := by
  have hq : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk
  have hqt : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq hqt hf]
  have h8 : (k : ℝ≥0∞).toReal = (k : ℝ) := by simp
  rw [h8, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have : (1 / (k : ℝ)) * (k : ℝ) = 1 := by
    field_simp
  rw [this, ENNReal.rpow_one]
  exact lintegral_congr fun x => ENNReal.rpow_natCast _ _

/-- A subcube of `cu_Kc` at scale `n` lies in the open cube `cu_Kc`. -/
theorem openCubeSet_subset_of_mem_descendantsAtScale_originCube {Kc n : ℕ} (hn : n ≤ Kc)
    {Q : TriadicCube d} (hQ : Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)) :
    openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ)) := by
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  rw [descendantsAtScale_eq_descendantsAtDepth _ hk] at hQ
  exact openCubeSet_subset_of_mem_descendantsAtDepth hQ

/-- A subcube of `cu_Kc` at scale `n` has scale `n`. -/
theorem scale_eq_of_mem_descendantsAtScale_originCube {Kc n : ℕ} (hn : n ≤ Kc)
    {Q : TriadicCube d} (hQ : Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)) :
    Q.scale = n := by
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  have h := scale_eq_sub_of_mem_descendantsAtScale hk hQ
  have e : Int.toNat ((originCube d (Kc : ℤ)).scale - (n : ℤ)) = Kc - n := by
    show Int.toNat ((Kc : ℤ) - (n : ℤ)) = Kc - n
    omega
  rw [e] at h
  have : (originCube d (Kc : ℤ)).scale = (Kc : ℤ) := rfl
  rw [h, this]
  omega

theorem cubeScaleFactor_eq_of_mem_descendantsAtScale_originCube {Kc n : ℕ} (hn : n ≤ Kc)
    {Q : TriadicCube d} (hQ : Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)) :
    cubeScaleFactor Q = (3 : ℝ) ^ n := by
  simp [cubeScaleFactor, scale_eq_of_mem_descendantsAtScale_originCube hn hQ]

/-- **The partition identity for `L̲^k` norms**: the subcube average of `‖f‖^k_{L̲^k(Q)}` is
`‖f‖^k_{L̲^k(cu_Kc)}`. -/
theorem subcubeAvg_pow_cubeLpENorm {E : Type*} [NormedAddCommGroup E] {Kc n : ℕ} (hn : n ≤ Kc)
    (k : ℕ) (hk : k ≠ 0) (f : Vec d → E)
    (hf : AEStronglyMeasurable f (volume.restrict (openCubeSet (originCube d (Kc : ℤ))))) :
    subcubeAvg Kc n (fun Q => (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q k f) ^ k) =
      (SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) k f) ^ k := by
  have hmeas : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      AEStronglyMeasurable f (normalizedCubeMeasure Q) := fun Q hQ =>
    aestronglyMeasurable_normalized
      (hf.mono_measure (Measure.restrict_mono
        (openCubeSet_subset_of_mem_descendantsAtScale_originCube hn hQ) le_rfl))
  have hmeasK : AEStronglyMeasurable f (normalizedCubeMeasure (originCube d (Kc : ℤ))) :=
    aestronglyMeasurable_normalized hf
  calc subcubeAvg Kc n (fun Q => (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q k f) ^ k)
      = subcubeAvg Kc n (fun Q => ∫⁻ x, ‖f x‖ₑ ^ k ∂normalizedCubeMeasure Q) := by
        unfold subcubeAvg
        congr 1
        refine Finset.sum_congr rfl fun Q hQ => ?_
        exact eLpNorm_nat_pow k hk f (hmeas Q hQ)
    _ = ∫⁻ x, ‖f x‖ₑ ^ k ∂normalizedCubeMeasure (originCube d (Kc : ℤ)) :=
        subcubeAvg_lintegral_normalizedCubeMeasure hn (fun x => ‖f x‖ₑ ^ k)
    _ = _ := (eLpNorm_nat_pow k hk f hmeasK).symm

/-- The partition identity at the exponent `4`. -/
theorem subcubeAvg_pow_four_cubeLpENorm {E : Type*} [NormedAddCommGroup E] {Kc n : ℕ} (hn : n ≤ Kc)
    (f : Vec d → E)
    (hf : AEStronglyMeasurable f (volume.restrict (openCubeSet (originCube d (Kc : ℤ))))) :
    subcubeAvg Kc n (fun Q => (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 f) ^ 4) =
      (SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 4 f) ^ 4 :=
  subcubeAvg_pow_cubeLpENorm hn 4 (by norm_num) f hf

end

end SuperdiffusionCLT.Section5
