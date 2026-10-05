/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.LimitB

/-!
# The global corrected affine functions

For every `e₀` the truncated profiles of `V m e_m` (`e_m` the unique slope with the prescribed
slope on `□_n`) converge to an entire solution; the limits assemble into a linear map `Φ`.
-/

@[expose] public section

open scoped ENNReal Topology

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory Filter

variable {d : ℕ}

theorem eb6b_vec_expand (e0 : Vec d) : e0 = ∑ i, e0 i • (Pi.single i (1 : ℝ) : Vec d) := by
  have := (Pi.basisFun ℝ (Fin d)).sum_repr e0
  simpa using this.symm

/-- The truncated profile is linear in the starting vector. -/
theorem eb6b_F_linear {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)} {n : ℕ}
    {Em : ℕ → Vec d →ₗ[ℝ] Vec d}
    (hVm : ∀ (j : ℕ) (e : Vec d), MemLp (V (n + j) (Em j e)) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))))
    (e0 : Vec d) (j : ℕ) (x : Vec d) :
    eb6b_F V n (fun j => Em j e0) j x =
      ∑ i, e0 i * eb6b_F V n (fun j => Em j (Pi.single i (1 : ℝ))) j x := by
  have hp := e0b_isProb (d := d) n
  have hW : ∀ y, V (n + j) (Em j e0) y =
      ∑ i, e0 i * V (n + j) (Em j (Pi.single i (1 : ℝ))) y := by
    intro y
    conv_lhs => rw [eb6b_vec_expand e0]
    simp [map_sum, map_smul, Finset.sum_apply]
  have hint : ∫ y, V (n + j) (Em j e0) y ∂(normalizedCubeMeasure (originCube d (n : ℤ))) =
      ∑ i, e0 i * ∫ y, V (n + j) (Em j (Pi.single i (1 : ℝ))) y
        ∂(normalizedCubeMeasure (originCube d (n : ℤ))) := by
    simp_rw [hW]
    rw [integral_finsetSum _ (fun i _ => ((hVm j _).integrable one_le_two).const_mul _)]
    simp [integral_const_mul]
  unfold eb6b_F
  by_cases hx : x ∈ engCube d (n + j)
  · simp only [Set.indicator_of_mem hx]
    rw [hW x, hint]
    simp [mul_sub, Finset.sum_sub_distrib]
  · simp [Set.indicator_of_notMem hx]

/-- **E-B6b (the global corrected affines)**. Replaces the construction of `φ_e[n]` and
`e.sharp.Cone.limit.compare`. -/
theorem eng_limit (d : ℕ) [NeZero d] (Cin K Cc Cz : ℝ) (hCin : 1 ≤ Cin) (hK : 1 ≤ K)
    (hCc : 1 ≤ Cc) (hCz : 1 ≤ Cz) :
    ∃ (Cl c6 : ℝ), 1 ≤ Cl ∧ 0 < c6 ∧
      ∀ η κ : ℝ, 1 / 2 ≤ η → η < 1 → 0 < κ → κ ≤ 1 / 24 →
        ∀ (a : CoeffField d) (δ s : ℕ → ℝ) (mstar : ℕ)
          (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)),
          3 ≤ mstar →
          (∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j ≤ c6 * κ) →
          (∀ i j : ℕ, mstar ≤ i → i ≤ j → δ j ≤ δ i) →
          GrowthElliptic a →
          -- hell
          (∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a) →
          -- hVsol
          (∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
            ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g) →
          -- hHC (Caccioppoli, two scales down)
          (∀ k : ℕ, mstar ≤ k → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
            IsSolOn a (engCube d k) u g →
              cubeGradL2 (k - 2) g ≤ Cin * Real.sqrt (s k) * cubeFlat k u) →
          -- hflat K, at `k = j` only
          (∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
            engNorm (affSlope j (V j e) - e) ≤ K * δ j * engNorm e) →
          (∀ j : ℕ, mstar ≤ j → K * δ j ≤ 1 / 2) →
          -- hchain Cc κ
          (∀ m k : ℕ, mstar ≤ k → k ≤ m →
            (∀ e : Vec d, ∃ q : Vec d,
              affSlope k (V k q) = affSlope k (V m e) ∧
                cubeFlat k (fun x => V m e x - V k q x) ≤ Cc * δ k * engNorm q ∧
                engNorm q ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm e ∧
                engNorm e ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm q) ∧
              ∀ q : Vec d, ∃ e : Vec d, affSlope k (V m e) = affSlope k (V k q)) →
          -- hcons Cz (η - 5κ)
          (∀ n m : ℕ, mstar ≤ n → n ≤ m → ∀ e e' : Vec d,
            affSlope n (V (m + 1) e') = affSlope n (V m e) →
            engNorm (e' - e) ≤ Cz * δ m * engNorm e ∧
              ∀ k : ℕ, n ≤ k → k ≤ m →
                cubeFlat k (fun x => V (m + 1) e' x - V m e x) ≤
                  Cz * δ m * (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) *
                    engNorm e) →
          -- conclusion
          ∀ n : ℕ, mstar ≤ n →
            ∃ (Φ : Vec d →ₗ[ℝ] (Vec d → ℝ)) (GΦ : Vec d → Vec d → Vec d),
              (∀ e0 : Vec d, IsEntireSolution a (Φ e0) (GΦ e0)) ∧
                ∀ (e0 : Vec d) (m : ℕ) (e : Vec d), n ≤ m →
                  affSlope n (V m e) = affSlope n (V n e0) →
                  ∀ k : ℕ, n ≤ k → k ≤ m →
                    cubeFlat k (fun x => Φ e0 x - V m e x) ≤
                      Cl * δ m * (3 : ℝ) ^ (-((η - 6 * κ) * ((m : ℝ) - (k : ℝ)))) *
                        engNorm e := by
  have _ := hCin
  have _ := hK
  have _ := hCc
  refine ⟨max 1 (Cz * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹), 1 / Cz, le_max_left _ _,
    by positivity, ?_⟩
  intro η κ hη _ hκ hκ1 a δ s mstar V _ hδ hanti hGE hell hVsol hHC hflat hK hchain hcons n hn
  have hCz0 : 0 < Cz := by linarith only [hCz]
  have hδ' : ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ Cz * δ j ≤ κ := by
    intro j hj
    obtain ⟨h1, h2⟩ := hδ j hj
    refine ⟨h1, ?_⟩
    calc Cz * δ j ≤ Cz * (1 / Cz * κ) := mul_le_mul_of_nonneg_left h2 hCz0.le
      _ = κ := by field_simp
  have hlow : ∀ m n : ℕ, mstar ≤ n → n ≤ m → ∀ e : Vec d, ∃ q : Vec d,
      affSlope n (V n q) = affSlope n (V m e) ∧
        engNorm e ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (n : ℝ))) * engNorm q := by
    intro m n hn' hnm e
    obtain ⟨q, h1, -, -, h4⟩ := ((hchain m n hn' hnm).1 e)
    exact ⟨q, h1, h4⟩
  have hup : ∀ m n : ℕ, mstar ≤ n → n ≤ m → ∀ q : Vec d, ∃ e : Vec d,
      affSlope n (V m e) = affSlope n (V n q) := fun m n hn' hnm => (hchain m n hn' hnm).2
  obtain ⟨Em, hEm⟩ := eb6b_exists_Em hVsol hflat hK hlow hup hn
  have hε : ∀ (e0 : Vec d) (j : ℕ),
      affSlope n (V (n + j + 1) (Em (j + 1) e0)) = affSlope n (V (n + j) (Em j e0)) :=
    fun e0 j => (hEm (j + 1) e0).trans (hEm j e0).symm
  choose L Glim hlim hent hbound using fun e0 : Vec d =>
    eb6b_limit_one Cin Cz hη hκ hκ1 hCz hδ' hanti hGE hell hVsol hHC hcons hn
      (fun j => Em j e0) (hε e0)
  have hnj : ∀ j : ℕ, mstar ≤ n + j := fun j => hn.trans (Nat.le_add_right n j)
  have hVm : ∀ (j : ℕ) (e : Vec d), MemLp (V (n + j) (Em j e)) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) := fun j e =>
    (hVsol (n + j) (hnj j) (Em j e)).elim fun g hg => eb6b_sol_memLp hg (Nat.le_add_right n j)
  let Φ : Vec d →ₗ[ℝ] (Vec d → ℝ) :=
    (Pi.basisFun ℝ (Fin d)).constr ℝ (fun i => L (Pi.single i (1 : ℝ)))
  have hΦ : ∀ (e0 : Vec d) (x : Vec d), Φ e0 x = ∑ i, e0 i * L (Pi.single i (1 : ℝ)) x := by
    intro e0 x
    simp [Φ, Module.Basis.constr_apply_fintype, Finset.sum_apply]
  have hae : ∀ e0 : Vec d, Φ e0 =ᵐ[volume] L e0 := by
    intro e0
    have hall : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ i : Fin d,
        Tendsto (fun j => eb6b_F V n (fun j => Em j (Pi.single i (1 : ℝ))) j x) atTop
          (𝓝 (L (Pi.single i (1 : ℝ)) x)) := ae_all_iff.2 fun i => hlim _
    filter_upwards [hlim e0, hall] with x hx hxi
    have h1 : Tendsto (fun j => eb6b_F V n (fun j => Em j e0) j x) atTop
        (𝓝 (∑ i, e0 i * L (Pi.single i (1 : ℝ)) x)) := by
      simp_rw [eb6b_F_linear hVm e0]
      exact tendsto_finsetSum _ fun i _ => (hxi i).const_mul _
    rw [hΦ]
    exact tendsto_nhds_unique h1 hx
  refine ⟨Φ, Glim, fun e0 => eb6b_entire_congr (hent e0) (hae e0), ?_⟩
  intro e0 m e hnm hslope k hnk hkm
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have he : e = Em j e0 := eb6b_unique hVsol hflat hK hlow hn hnm (hslope.trans (hEm j e0).symm)
  subst he
  have h1 := hbound e0 j k hnk hkm
  have h2 : cubeFlat k (fun x => Φ e0 x - V (n + j) (Em j e0) x) =
      cubeFlat k (fun x => L e0 x - V (n + j) (Em j e0) x) := by
    refine cubeFlat_congr_ae ?_
    filter_upwards [(e0e_normalizedCube_ac (originCube d (k : ℤ))).ae_le (hae e0)] with x hx
    rw [hx]
  rw [h2]
  refine h1.trans ?_
  have hd := (hδ' (n + j) (hnj j)).1
  have hn0 := engNorm_nonneg (Em j e0)
  have hr : 0 < (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := inv_pos.2 (by linarith only [eb6b_geom_lt_one])
  have hle : Cz * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ ≤
      max 1 (Cz * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹) := le_max_right _ _
  have hp : (0 : ℝ) < (3 : ℝ) ^ (-((η - 6 * κ) * (((n + j : ℕ) : ℝ) - (k : ℝ)))) := by positivity
  gcongr

/-- Witness for the numerical hypotheses of `eng_limit`: `η = 3/4`, `κ = 1/24`, `c₆ = 1`,
`δ = 0`, `K = 1`, `m⋆ = 3`. -/
example : (1 / 2 : ℝ) ≤ 3 / 4 ∧ (3 / 4 : ℝ) < 1 ∧ (0 : ℝ) < 1 / 24 ∧ (1 / 24 : ℝ) ≤ 1 / 24 ∧
    (3 : ℕ) ≤ 3 ∧ (∀ j : ℕ, 3 ≤ j → (0 : ℝ) ≤ (fun _ : ℕ => (0 : ℝ)) j ∧
      (fun _ : ℕ => (0 : ℝ)) j ≤ 1 * (1 / 24)) ∧
    (∀ i j : ℕ, 3 ≤ i → i ≤ j → (fun _ : ℕ => (0 : ℝ)) j ≤ (fun _ : ℕ => (0 : ℝ)) i) ∧
    (∀ j : ℕ, 3 ≤ j → (1 : ℝ) * (fun _ : ℕ => (0 : ℝ)) j ≤ 1 / 2) := by
  refine ⟨by norm_num, by norm_num, by norm_num, le_rfl, le_rfl, fun j _ => ⟨le_rfl, by norm_num⟩,
    fun i j _ _ => le_rfl, fun j _ => by norm_num⟩

end SuperdiffusionCLT.Section6
