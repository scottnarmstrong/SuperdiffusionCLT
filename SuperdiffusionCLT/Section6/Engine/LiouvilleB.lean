/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Liouville
public import SuperdiffusionCLT.Section6.Engine.Chain

/-!
# The Liouville theorem for the corrected affine functions
-/

@[expose] public section

open scoped ENNReal Topology

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory Filter

variable {d : ℕ}

theorem eb7_le_zero_of_decay {x D ε : ℝ} {k : ℕ} (hε : 0 < ε)
    (h : ∀ᶠ m : ℕ in atTop, x ≤ D * (3 : ℝ) ^ (-(ε * ((m : ℝ) - (k : ℝ))))) : x ≤ 0 := by
  have h0 : Tendsto (fun m : ℕ => (m : ℝ) - (k : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ (-(k : ℝ)) tendsto_natCast_atTop_atTop |>.congr
      (fun m => by ring)
  have h1 : Tendsto (fun m : ℕ => -(ε * ((m : ℝ) - (k : ℝ)))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop hε h0)
  have h2 : Tendsto (fun m : ℕ => D * (3 : ℝ) ^ (-(ε * ((m : ℝ) - (k : ℝ))))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_atBot_of_base_gt_one 3 (by norm_num)).comp h1).const_mul D
  exact ge_of_tendsto h2 h

theorem eb7_T [NeZero d] {a : CoeffField d} {mstar : ℕ} {K : ℝ} {δ : ℕ → ℝ}
    {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)}
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hflat : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      engNorm (affSlope j (V j e) - e) ≤ K * δ j * engNorm e)
    (hK : ∀ j : ℕ, mstar ≤ j → K * δ j ≤ 1 / 2) :
    ∃ T : Vec d →ₗ[ℝ] Vec d, (∀ e, T e = affSlope mstar (V mstar e)) ∧ Function.Bijective T := by
  obtain ⟨T, hT⟩ := eb4_slope_linear (le_refl mstar) (V mstar) (hVsol mstar le_rfl)
  refine ⟨T, hT, (engNorm_bijective_of_close T fun e => ?_).1⟩
  rw [hT e]
  exact (hflat mstar le_rfl e).trans (mul_le_mul_of_nonneg_right (hK mstar le_rfl)
    (engNorm_nonneg e))

theorem eb7_chain_e [NeZero d] {mstar : ℕ} {Cc κ : ℝ} {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)}
    {δ : ℕ → ℝ} {T : Vec d →ₗ[ℝ] Vec d} (hTinj : Function.Injective T)
    (hT : ∀ e, T e = affSlope mstar (V mstar e))
    (hchain : ∀ m k : ℕ, mstar ≤ k → k ≤ m →
      (∀ e : Vec d, ∃ q : Vec d,
        affSlope k (V k q) = affSlope k (V m e) ∧
          cubeFlat k (fun x => V m e x - V k q x) ≤ Cc * δ k * engNorm q ∧
          engNorm q ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm e ∧
          engNorm e ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm q) ∧
        ∀ q : Vec d, ∃ e : Vec d, affSlope k (V m e) = affSlope k (V k q))
    (e0 : Vec d) {m : ℕ} (hm : mstar ≤ m) :
    ∃ e : Vec d, affSlope mstar (V m e) = affSlope mstar (V mstar e0) ∧
      engNorm e ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (mstar : ℝ))) * engNorm e0 := by
  obtain ⟨e, he⟩ := (hchain m mstar le_rfl hm).2 e0
  obtain ⟨q, hq1, -, -, hq4⟩ := (hchain m mstar le_rfl hm).1 e
  have hq : q = e0 := hTinj (by rw [hT q, hT e0, hq1, he])
  exact ⟨e, he, hq ▸ hq4⟩

theorem eb7_flat_V [NeZero d] {a : CoeffField d} {Cin : ℝ} {j : ℕ} {Vj : Vec d →ₗ[ℝ] (Vec d → ℝ)}
    {dj : ℝ} (hdj1 : dj ≤ 1) (hCin : 1 ≤ Cin)
    (hsol : ∀ e : Vec d, ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (Vj e) g)
    (hflat : ∀ e : Vec d, cubeFlat j (fun x => Vj e x - vecDot e x) ≤ Cin * dj * engNorm e)
    (e : Vec d) : cubeFlat j (Vj e) ≤ (1 + Cin) * engNorm e := by
  have hV : MemLp (Vj e) 2 (normalizedCubeMeasure (originCube d (j : ℤ))) :=
    (hsol e).elim fun g hg => hg.memLp.1
  have hl := e0c_memLp j (e0c_continuous_vecDot e)
  have hVl : MemLp (fun x => Vj e x - vecDot e x) 2
      (normalizedCubeMeasure (originCube d (j : ℤ))) := hV.sub hl
  have h1 := cubeFlat_add_le hl hVl
  have e1 : (fun x => vecDot e x + (Vj e x - vecDot e x)) = Vj e := by funext x; ring
  rw [e1, cubeFlat_vecDot] at h1
  have h3 : (1 : ℝ) ≤ 2 * Real.sqrt 3 := by
    have := Real.one_le_sqrt.2 (by norm_num : (1 : ℝ) ≤ 3)
    linarith only [this]
  have h4 : engNorm e / (2 * Real.sqrt 3) ≤ engNorm e := div_le_self (engNorm_nonneg e) h3
  have h5 := hflat e
  have h6 : Cin * dj * engNorm e ≤ Cin * engNorm e := by
    have := mul_le_mul_of_nonneg_left hdj1 (by linarith only [hCin] : 0 ≤ Cin)
    nlinarith only [this, engNorm_nonneg e]
  linarith only [h1, h4, h5, h6]

theorem eb7_phi_flat [NeZero d] {a : CoeffField d} {Cin Cl η κ : ℝ} {mstar : ℕ} {δ : ℕ → ℝ}
    {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)} {Φ : Vec d →ₗ[ℝ] (Vec d → ℝ)} {GΦ : Vec d → Vec d → Vec d}
    (hCin : 1 ≤ Cin) (hCl : 1 ≤ Cl)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hδ : ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j ≤ 1)
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hVflat : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      cubeFlat j (fun x => V j e x - vecDot e x) ≤ Cin * δ j * engNorm e)
    (hΦsol : ∀ e0 : Vec d, IsEntireSolution a (Φ e0) (GΦ e0))
    (hΦlim : ∀ (e0 : Vec d) (m : ℕ) (e : Vec d), mstar ≤ m →
      affSlope mstar (V m e) = affSlope mstar (V mstar e0) →
      ∀ k : ℕ, mstar ≤ k → k ≤ m →
        cubeFlat k (fun x => Φ e0 x - V m e x) ≤
          Cl * δ m * (3 : ℝ) ^ (-((η - 6 * κ) * ((m : ℝ) - (k : ℝ)))) * engNorm e)
    {e0 : Vec d} {m : ℕ} (hm : mstar ≤ m) {e : Vec d}
    (he : affSlope mstar (V m e) = affSlope mstar (V mstar e0)) :
    cubeFlat m (Φ e0) ≤ (Cl + (1 + Cin)) * engNorm e := by
  have hΦm := eb7_entire_memLp hell (hΦsol e0) m
  have hVm : MemLp (V m e) 2 (normalizedCubeMeasure (originCube d (m : ℤ))) :=
    ((hVsol m hm e).elim fun g hg => hg.memLp.1)
  have hsub : MemLp (fun x => Φ e0 x - V m e x) 2
      (normalizedCubeMeasure (originCube d (m : ℤ))) := hΦm.sub hVm
  have h1 := cubeFlat_add_le hsub hVm
  have e1 : (fun x => (Φ e0 x - V m e x) + V m e x) = Φ e0 := by funext x; ring
  rw [e1] at h1
  have h2 := hΦlim e0 m e hm he m hm le_rfl
  rw [sub_self, mul_zero, neg_zero, Real.rpow_zero, mul_one] at h2
  have h3 := eb7_flat_V (hδ m hm).2 hCin (hVsol m hm) (hVflat m hm) e
  have h4 : Cl * δ m * engNorm e ≤ Cl * engNorm e := by
    have := mul_le_mul_of_nonneg_left (hδ m hm).2 (by linarith only [hCl] : 0 ≤ Cl)
    nlinarith only [this, engNorm_nonneg e]
  nlinarith only [h1, h2, h3, h4]

theorem eb7_phi_slope [NeZero d] {a : CoeffField d} {Cl Cc η κ : ℝ} {mstar : ℕ} {δ : ℕ → ℝ}
    {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)} {Φ : Vec d →ₗ[ℝ] (Vec d → ℝ)} {GΦ : Vec d → Vec d → Vec d}
    (hCl : 1 ≤ Cl) (hε : 0 < η - 7 * κ)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hδ : ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j ≤ 1)
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hΦsol : ∀ e0 : Vec d, IsEntireSolution a (Φ e0) (GΦ e0))
    (hΦlim : ∀ (e0 : Vec d) (m : ℕ) (e : Vec d), mstar ≤ m →
      affSlope mstar (V m e) = affSlope mstar (V mstar e0) →
      ∀ k : ℕ, mstar ≤ k → k ≤ m →
        cubeFlat k (fun x => Φ e0 x - V m e x) ≤
          Cl * δ m * (3 : ℝ) ^ (-((η - 6 * κ) * ((m : ℝ) - (k : ℝ)))) * engNorm e)
    (hce : ∀ (e0 : Vec d) (m : ℕ), mstar ≤ m → ∃ e : Vec d,
      affSlope mstar (V m e) = affSlope mstar (V mstar e0) ∧
        engNorm e ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (mstar : ℝ))) * engNorm e0)
    (e0 : Vec d) : affSlope mstar (Φ e0) = affSlope mstar (V mstar e0) := by
  have hΦs := eb7_entire_memLp hell (hΦsol e0) mstar
  have hdecay : engNorm (affSlope mstar (Φ e0) - affSlope mstar (V mstar e0)) ≤ 0 := by
    refine eb7_le_zero_of_decay (D := 4 * Cl * Cc * engNorm e0) (ε := η - 7 * κ) (k := mstar) hε ?_
    filter_upwards [eventually_ge_atTop mstar] with m hm
    obtain ⟨e, he1, he2⟩ := hce e0 m hm
    have hVs : MemLp (V m e) 2 (normalizedCubeMeasure (originCube d (mstar : ℤ))) :=
      eb6b_sol_memLp (hVsol m hm e).choose_spec hm
    have hsub := eb6a_slope_sub hΦs hVs
    have hle := eb6a_slope_le (hΦs.sub hVs)
    have hfl := hΦlim e0 m e hm he1 mstar le_rfl hm
    have e1 : affSlope mstar (Φ e0) - affSlope mstar (V mstar e0) =
        affSlope mstar (fun x => Φ e0 x - V m e x) := by rw [hsub, he1]
    rw [e1]
    have hp : (3 : ℝ) ^ (-((η - 6 * κ) * ((m : ℝ) - (mstar : ℝ)))) *
        (3 : ℝ) ^ (κ * ((m : ℝ) - (mstar : ℝ))) =
        (3 : ℝ) ^ (-((η - 7 * κ) * ((m : ℝ) - (mstar : ℝ)))) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    have h3 : 0 ≤ (3 : ℝ) ^ (-((η - 6 * κ) * ((m : ℝ) - (mstar : ℝ)))) := by positivity
    have hd := hδ m hm
    have hn := engNorm_nonneg e0
    have hCl0 : 0 ≤ Cl := by linarith only [hCl]
    calc engNorm (affSlope mstar fun x => Φ e0 x - V m e x)
        ≤ 4 * cubeFlat mstar (fun x => Φ e0 x - V m e x) := hle
      _ ≤ 4 * (Cl * δ m * (3 : ℝ) ^ (-((η - 6 * κ) * ((m : ℝ) - (mstar : ℝ)))) * engNorm e) := by
          gcongr
      _ ≤ 4 * (Cl * 1 * (3 : ℝ) ^ (-((η - 6 * κ) * ((m : ℝ) - (mstar : ℝ)))) *
            (Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (mstar : ℝ))) * engNorm e0)) := by
          gcongr
          all_goals first | exact hd.1 | exact hd.2 | exact he2 | exact engNorm_nonneg _
      _ = 4 * Cl * Cc * engNorm e0 * (3 : ℝ) ^ (-((η - 7 * κ) * ((m : ℝ) - (mstar : ℝ)))) := by
          rw [← hp]
          ring
  have h0 := e0c_engNorm_eq_zero (le_antisymm hdecay (engNorm_nonneg _))
  exact sub_eq_zero.1 h0

theorem eb7_cubeSet_mono {k l : ℕ} (h : k ≤ l) :
    cubeSet (originCube d (k : ℤ)) ⊆ cubeSet (originCube d (l : ℤ)) := by
  intro x hx
  rw [mem_cubeSet_originCube_iff] at hx ⊢
  have h3 : (3 : ℝ) ^ (k : ℤ) ≤ (3 : ℝ) ^ (l : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by exact_mod_cast h)
  intro i
  obtain ⟨h1, h2⟩ := hx i
  constructor <;> nlinarith only [h1, h2, h3]

theorem eb7_ae_const [NeZero d] {k : ℕ} {w : Vec d → ℝ}
    (hw : MemLp w 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hz : cubeFlat k w = 0) :
    w =ᵐ[normalizedCubeMeasure (originCube d (k : ℤ))]
      fun _ => cubeAverage (originCube d (k : ℤ)) w := by
  have hw0 : MemLp (fun x => w x - cubeAverage (originCube d (k : ℤ)) w) 2
      (normalizedCubeMeasure (originCube d (k : ℤ))) := hw.sub (memLp_const _)
  have h1 : cubeL2 k (fun x => w x - cubeAverage (originCube d (k : ℤ)) w) = 0 := by
    unfold cubeFlat at hz
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd h (by positivity)
    · exact h
  unfold cubeL2 cubeLpNorm at h1
  have h2 : eLpNorm (fun x => w x - cubeAverage (originCube d (k : ℤ)) w) 2
      (normalizedCubeMeasure (originCube d (k : ℤ))) = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 h1 with h | h
    · exact h
    · exact absurd h hw0.eLpNorm_ne_top
  have h3 := (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).1 h2
  filter_upwards [h3] with x hx
  simpa [sub_eq_zero] using hx

theorem eb7_ae_normalized_mono {k l : ℕ} (hkl : k ≤ l) {P : Vec d → Prop}
    (h : ∀ᵐ x ∂(normalizedCubeMeasure (originCube d (l : ℤ))), P x) :
    ∀ᵐ x ∂(normalizedCubeMeasure (originCube d (k : ℤ))), P x := by
  rw [e0e_ae_normalized_iff] at h ⊢
  filter_upwards [h] with x hx hxk using hx (eb7_cubeSet_mono hkl hxk)

theorem eb7_const_of_flat_zero [NeZero d] {w : Vec d → ℝ} {s : ℕ}
    (hw : ∀ k : ℕ, MemLp w 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hz : ∀ k : ℕ, s ≤ k → cubeFlat k w = 0) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), w x = cubeAverage (originCube d (s : ℤ)) w := by
  have hk : ∀ k : ℕ, ∀ᵐ x ∂(normalizedCubeMeasure (originCube d ((s + k : ℕ) : ℤ))),
      w x = cubeAverage (originCube d (s : ℤ)) w := by
    intro k
    have hc := eb7_ae_const (hw (s + k)) (hz (s + k) (Nat.le_add_right s k))
    have hs := eb7_ae_normalized_mono (Nat.le_add_right s k) hc
    have hpr := e0b_isProb (d := d) s
    have hav : cubeAverage (originCube d (s : ℤ)) w =
        cubeAverage (originCube d ((s + k : ℕ) : ℤ)) w := by
      rw [cubeAverage_eq_integral_normalizedCubeMeasure]
      rw [integral_congr_ae hs]
      simp
    rw [hav]
    exact hc
  have hall : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ k : ℕ,
      x ∈ cubeSet (originCube d ((s + k : ℕ) : ℤ)) → w x = cubeAverage (originCube d (s : ℤ)) w := by
    rw [ae_all_iff]
    intro k
    exact (e0e_ae_normalized_iff _ _).1 (hk k)
  filter_upwards [hall] with x hx
  obtain ⟨k, hkx⟩ := e0e_exists_cube (d := d) x
  exact hx k (eb7_cubeSet_mono (by omega) hkx)

theorem eb7_iUnion_cube : (⋃ k : ℕ, engCube d k) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨k, hk⟩ := e0e_exists_cube (d := d) x
  refine Set.mem_iUnion.2 ⟨k + 1, ?_⟩
  rw [mem_cubeSet_originCube_iff] at hk
  show x ∈ openCubeSet (originCube d ((k + 1 : ℕ) : ℤ))
  rw [mem_openCubeSet_originCube_iff]
  intro i
  obtain ⟨h1, h2⟩ := hk i
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := by positivity
  have h4 : (3 : ℝ) ^ ((k + 1 : ℕ) : ℤ) = 3 * (3 : ℝ) ^ (k : ℤ) := by
    rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring, zpow_add₀ (by norm_num)]
    ring
  rw [h4]
  constructor <;> nlinarith only [h1, h2, h3]

theorem eb7_aesm [NeZero d] {a : CoeffField d}
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    {f : Vec d → ℝ} {g : Vec d → Vec d} (h : IsEntireSolution a f g) :
    AEStronglyMeasurable f (volume : Measure (Vec d)) := by
  have h1 : AEStronglyMeasurable f (volume.restrict (⋃ k : ℕ, engCube d k)) := by
    rw [aestronglyMeasurable_iUnion_iff]
    intro k
    obtain ⟨v, hv1, -⟩ := eb7_entire_cube hell h k
    exact v.toH1.memL2.aestronglyMeasurable.congr hv1
  rwa [eb7_iUnion_cube, Measure.restrict_univ] at h1


theorem eb7_pow_kappa {κ : ℝ} (hκ : 0 ≤ κ) (k s : ℕ) :
    (3 : ℝ) ^ (κ * ((k : ℝ) - (s : ℝ))) ≤ ((3 : ℝ) ^ κ) ^ k := by
  rw [eb7_rpow_pow_comm, eb7_rpow_nat_pow]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  nlinarith only [this, hκ]

theorem eb7_pow_gamma {κ γ : ℝ} (hκ : 0 ≤ κ) (hκγ : κ ≤ γ) (m s : ℕ) :
    (3 : ℝ) ^ (κ * ((m : ℝ) - (s : ℝ))) ≤ (3 : ℝ) ^ (γ * (m : ℝ)) := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith only [this, hκ, hκγ, hm]

theorem eb7_limsup_of_flat (d : ℕ) [NeZero d] {γ κ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hκγ : κ ≤ γ) {f : Vec d → ℝ} {s : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ k : ℕ, MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hfl : ∀ k : ℕ, s ≤ k → cubeFlat k f ≤ B * ((3 : ℝ) ^ κ) ^ k) :
    Filter.limsup (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + γ))) * ballL2 r f)
      Filter.atTop < ⊤ := by
  have ht : (1 : ℝ) ≤ (3 : ℝ) ^ κ := Real.one_le_rpow (by norm_num) hκ
  obtain ⟨C, hC, hbd⟩ := eb7_L2_growth hB ht hf hfl
  exact eb7_limsup_of_cube d hκ hκ1 hκγ hC hf hbd

/-- **E-B7 (Liouville)**, Step 7 (without the compactness argument). -/
theorem eng_liouville (d : ℕ) [NeZero d] (Cin K Cc Cz Cl : ℝ) (hCin : 1 ≤ Cin) (hK : 1 ≤ K)
    (hCc : 1 ≤ Cc) (hCz : 1 ≤ Cz) (hCl : 1 ≤ Cl) :
    ∃ c7 : ℝ, 0 < c7 ∧
      ∀ η κ γ : ℝ, 1 / 2 ≤ η → η < 1 → 0 < κ → κ ≤ 1 / 24 → 0 < γ → κ ≤ γ →
        γ + 5 * κ < η →
        ∀ (a : CoeffField d) (δ : ℕ → ℝ) (mstar : ℕ)
          (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ))
          (Φ : Vec d →ₗ[ℝ] (Vec d → ℝ)) (GΦ : Vec d → Vec d → Vec d),
          3 ≤ mstar →
          (∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j ≤ c7) →
          GrowthElliptic a →
          -- hell
          (∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a) →
          -- hVsol
          (∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
            ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g) →
          -- hVflat
          (∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
            cubeFlat j (fun x => V j e x - vecDot e x) ≤ Cin * δ j * engNorm e) →
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
          -- hzd Cz (η - 5κ)
          (∀ n m : ℕ, mstar ≤ n → n ≤ m →
            ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d m) w g) →
              affSlope n w = 0 →
              ∀ k : ℕ, n ≤ k → k ≤ m →
                cubeFlat k w ≤
                  Cz * (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) * cubeFlat m w) →
          -- hΦsol
          (∀ e0 : Vec d, IsEntireSolution a (Φ e0) (GΦ e0)) →
          -- hΦlim Cl (η - 6κ), anchored at `n = mstar`
          (∀ (e0 : Vec d) (m : ℕ) (e : Vec d), mstar ≤ m →
            affSlope mstar (V m e) = affSlope mstar (V mstar e0) →
            ∀ k : ℕ, mstar ≤ k → k ≤ m →
              cubeFlat k (fun x => Φ e0 x - V m e x) ≤
                Cl * δ m * (3 : ℝ) ^ (-((η - 6 * κ) * ((m : ℝ) - (k : ℝ)))) * engNorm e) →
          -- conclusion
          Module.finrank ℝ (Submodule.span ℝ (growthSpace a γ)) = 1 + d ∧
            (∀ (c : ℝ) (e0 : Vec d),
              ∃ hm : AEStronglyMeasurable (fun x => c + Φ e0 x) volume,
                AEEqFun.mk (fun x => c + Φ e0 x) hm ∈ growthSpace a γ) ∧
            ∀ φ ∈ growthSpace a γ, ∃ (c : ℝ) (e0 : Vec d),
              (φ : Vec d → ℝ) =ᵐ[volume] fun x => c + Φ e0 x := by
  have _ := hK
  refine ⟨1, one_pos, ?_⟩
  intro η κ γ hη hη1 hκ hκ1 hγ hκγ hγη a δ mstar V Φ GΦ hm3 hδ hGE hell hVsol hVflat hflat hKδ
    hchain hzd hΦsol hΦlim
  have _ := hη1
  have _ := hm3
  have hκ0 : 0 ≤ κ := hκ.le
  have hκ1' : κ ≤ 1 := by linarith only [hκ1]
  have hεη : 0 < η - 7 * κ := by linarith only [hη, hκ1]
  have hε5 : 0 < η - 5 * κ - γ := by linarith only [hγη]
  obtain ⟨T, hT, hTb⟩ := eb7_T hVsol hflat hKδ
  have hce : ∀ (e0 : Vec d) (m : ℕ), mstar ≤ m → ∃ e : Vec d,
      affSlope mstar (V m e) = affSlope mstar (V mstar e0) ∧
        engNorm e ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (mstar : ℝ))) * engNorm e0 :=
    fun e0 m hm => eb7_chain_e hTb.1 hT hchain e0 hm
  have hslope := eb7_phi_slope hCl hεη hell hδ hVsol hΦsol hΦlim hce
  have hmemΦ : ∀ (e0 : Vec d) (k : ℕ),
      MemLp (Φ e0) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
    fun e0 k => eb7_entire_memLp hell (hΦsol e0) k
  have hΦflat : ∀ (e0 : Vec d) (m : ℕ), mstar ≤ m →
      cubeFlat m (Φ e0) ≤ ((Cl + (1 + Cin)) * Cc * engNorm e0) * (3 : ℝ) ^ (κ * ((m : ℝ) - (mstar : ℝ))) := by
    intro e0 m hm
    obtain ⟨e, he1, he2⟩ := hce e0 m hm
    have h1 := eb7_phi_flat hCin hCl hell hδ hVsol hVflat hΦsol hΦlim hm he1
    have h2 := mul_le_mul_of_nonneg_left he2 (by linarith only [hCin, hCl] : 0 ≤ Cl + (1 + Cin))
    calc cubeFlat m (Φ e0) ≤ (Cl + (1 + Cin)) * engNorm e := h1
      _ ≤ _ := h2
      _ = _ := by ring
  have hmeas : ∀ (c : ℝ) (e0 : Vec d), AEStronglyMeasurable (fun x => c + Φ e0 x) volume :=
    fun c e0 => (eb7_aesm hell (hΦsol e0)).const_add c
  have hΦk : ∀ (c : ℝ) (e0 : Vec d) (k : ℕ), mstar ≤ k →
      cubeFlat k (fun x => c + Φ e0 x) ≤
        ((Cl + (1 + Cin)) * Cc * engNorm e0) * ((3 : ℝ) ^ κ) ^ k := by
    intro c e0 k hk
    have e1 : (fun x => c + Φ e0 x) = fun x => Φ e0 x + c := funext fun x => add_comm _ _
    rw [e1, cubeFlat_add_const (hmemΦ e0 k)]
    refine (hΦflat e0 k hk).trans ?_
    have hn := engNorm_nonneg e0
    have : 0 ≤ (Cl + (1 + Cin)) * Cc * engNorm e0 := by
      have := mul_nonneg (mul_nonneg (by linarith only [hCin, hCl] : 0 ≤ Cl + (1 + Cin))
        (by linarith only [hCc] : 0 ≤ Cc)) hn
      exact this
    exact mul_le_mul_of_nonneg_left (eb7_pow_kappa hκ0 k mstar) this
  -- second conclusion
  have hmem : ∀ (c : ℝ) (e0 : Vec d), ∃ hm : AEStronglyMeasurable (fun x => c + Φ e0 x) volume,
      AEEqFun.mk (fun x => c + Φ e0 x) hm ∈ growthSpace a γ := by
    intro c e0
    refine ⟨hmeas c e0, ?_, ?_⟩
    · refine ⟨GΦ e0, ?_⟩
      have hent : IsEntireSolution a (fun x => c + Φ e0 x) (GΦ e0) := by
        intro R hR
        have h1 := (hΦsol e0 R hR)
        rw [isBallSolution_iff_isSolOn] at h1 ⊢
        have h2 := IsSolOn.add_const (volume_euclidBall_ne_top hR) c h1
        have e1 : (fun x => c + Φ e0 x) = fun x => Φ e0 x + c := funext fun x => add_comm _ _
        rw [e1]
        exact h2
      exact eb6b_entire_congr hent (AEEqFun.coeFn_mk _ _)
    · have hf : ∀ k : ℕ, MemLp (fun x => c + Φ e0 x) 2
          (normalizedCubeMeasure (originCube d (k : ℤ))) :=
        fun k => (memLp_const c).add (hmemΦ e0 k)
      have hlim := eb7_limsup_of_flat d hκ0 hκ1' hκγ (s := mstar)
        (B := (Cl + (1 + Cin)) * Cc * engNorm e0)
        (by have := engNorm_nonneg e0; positivity) hf (hΦk c e0)
      have hb : ∀ r : ℝ, ballL2 r (⇑(AEEqFun.mk (fun x => c + Φ e0 x) (hmeas c e0))) =
          ballL2 r (fun x => c + Φ e0 x) := fun r => by
        unfold ballL2
        exact eLpNorm_congr_ae ((ballMeasure_absolutelyContinuous r).ae_eq (AEEqFun.coeFn_mk _ _))
      have heq : (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + γ))) *
          ballL2 r (⇑(AEEqFun.mk (fun x => c + Φ e0 x) (hmeas c e0)))) =
          fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + γ))) * ballL2 r (fun x => c + Φ e0 x) :=
        funext fun r => by rw [hb r]
      rw [heq]
      exact hlim
  -- third conclusion
  have hrep : ∀ φ ∈ growthSpace a γ, ∃ (c : ℝ) (e0 : Vec d),
      (φ : Vec d → ℝ) =ᵐ[volume] fun x => c + Φ e0 x := by
    rintro φ ⟨⟨gu, hgu⟩, hlimu⟩
    have hum : ∀ k : ℕ, MemLp (⇑φ) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
      fun k => eb7_entire_memLp hell hgu k
    obtain ⟨Bu, hBu0, m0, hm0⟩ := eb7_flat_of_limsup d hgu hell hlimu
    obtain ⟨e0, he0⟩ := hTb.2 (affSlope mstar (⇑φ))
    have hw : ∀ k : ℕ, MemLp (fun x => φ x - Φ e0 x) 2
        (normalizedCubeMeasure (originCube d (k : ℤ))) := fun k => (hum k).sub (hmemΦ e0 k)
    have hwsol' : ∀ m : ℕ, ∃ g : Vec d → Vec d,
        IsSolOn a (engCube d m) (fun x => φ x - Φ e0 x) g := fun m =>
      ⟨_, IsSolOn.sub (hell m) (eb7_entire_cube hell hgu m) (eb7_entire_cube hell (hΦsol e0) m)⟩
    have hslw : affSlope mstar (fun x => φ x - Φ e0 x) = 0 := by
      rw [eb6a_slope_sub (hum mstar) (hmemΦ e0 mstar), hslope e0, ← hT e0, he0, sub_self]
    have hflw : ∀ m : ℕ, max m0 mstar ≤ m → cubeFlat m (fun x => φ x - Φ e0 x) ≤
        (Bu + (Cl + (1 + Cin)) * Cc * engNorm e0) * (3 : ℝ) ^ (γ * (m : ℝ)) := by
      intro m hm
      have hm1 : m0 ≤ m := (le_max_left _ _).trans hm
      have hm2 : mstar ≤ m := (le_max_right _ _).trans hm
      have h1 := eb5a_flat_sub_le (hum m) (hmemΦ e0 m)
      have h2 := hm0 m hm1
      have h3 := hΦflat e0 m hm2
      have h4 := mul_le_mul_of_nonneg_left (eb7_pow_gamma hκ0 hκγ m mstar)
        (by have := engNorm_nonneg e0
            have : 0 ≤ (Cl + (1 + Cin)) * Cc * engNorm e0 :=
              mul_nonneg (mul_nonneg (by linarith only [hCin, hCl]) (by linarith only [hCc])) this
            exact this)
      nlinarith only [h1, h2, h3, h4]
    have hz : ∀ k : ℕ, mstar ≤ k → cubeFlat k (fun x => φ x - Φ e0 x) = 0 := by
      intro k hk
      refine le_antisymm ?_ (cubeFlat_nonneg _ _)
      refine eb7_le_zero_of_decay (D := Cz * (Bu + (Cl + (1 + Cin)) * Cc * engNorm e0) *
        (3 : ℝ) ^ (γ * (k : ℝ))) (ε := η - 5 * κ - γ) (k := k) hε5 ?_
      filter_upwards [eventually_ge_atTop (max (max m0 mstar) k)] with m hm
      have hm1 : max m0 mstar ≤ m := (le_max_left _ _).trans hm
      have hkm : k ≤ m := (le_max_right _ _).trans hm
      have h1 := hzd mstar m le_rfl ((le_max_right _ _).trans hm1) _ (hwsol' m) hslw k hk hkm
      have h2 := hflw m hm1
      have hB0 : 0 ≤ Bu + (Cl + (1 + Cin)) * Cc * engNorm e0 := by
        have := engNorm_nonneg e0
        have : 0 ≤ (Cl + (1 + Cin)) * Cc * engNorm e0 :=
          mul_nonneg (mul_nonneg (by linarith only [hCin, hCl]) (by linarith only [hCc])) this
        linarith only [hBu0, this]
      have hp : (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) * (3 : ℝ) ^ (γ * (m : ℝ)) =
          (3 : ℝ) ^ (γ * (k : ℝ)) * (3 : ℝ) ^ (-((η - 5 * κ - γ) * ((m : ℝ) - (k : ℝ)))) := by
        rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1
        ring
      have h3 : 0 ≤ (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) := by positivity
      calc cubeFlat k (fun x => φ x - Φ e0 x)
          ≤ Cz * (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) *
              cubeFlat m (fun x => φ x - Φ e0 x) := h1
        _ ≤ Cz * (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) *
              ((Bu + (Cl + (1 + Cin)) * Cc * engNorm e0) * (3 : ℝ) ^ (γ * (m : ℝ))) :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg (by linarith only [hCz]) h3)
        _ = Cz * (Bu + (Cl + (1 + Cin)) * Cc * engNorm e0) *
              ((3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) * (3 : ℝ) ^ (γ * (m : ℝ))) := by
            ring
        _ = Cz * (Bu + (Cl + (1 + Cin)) * Cc * engNorm e0) *
              ((3 : ℝ) ^ (γ * (k : ℝ)) *
                (3 : ℝ) ^ (-((η - 5 * κ - γ) * ((m : ℝ) - (k : ℝ))))) := by rw [hp]
        _ = Cz * (Bu + (Cl + (1 + Cin)) * Cc * engNorm e0) * (3 : ℝ) ^ (γ * (k : ℝ)) *
              (3 : ℝ) ^ (-((η - 5 * κ - γ) * ((m : ℝ) - (k : ℝ)))) := by ring
    have hconst := eb7_const_of_flat_zero hw hz
    refine ⟨cubeAverage (originCube d (mstar : ℤ)) (fun x => φ x - Φ e0 x), e0, ?_⟩
    filter_upwards [hconst] with x hx
    linarith only [hx]
  -- the linear map (c, e0) ↦ [c + Φ e0]
  let Lm : ℝ × Vec d →ₗ[ℝ] (Vec d →ₘ[volume] ℝ) :=
    { toFun := fun p => AEEqFun.mk (fun x => p.1 + Φ p.2 x) (hmeas p.1 p.2)
      map_add' := by
        intro p q
        rw [AEEqFun.mk_add_mk]
        congr 1
        funext x
        simp only [Prod.fst_add, Prod.snd_add, map_add, Pi.add_apply]
        ring
      map_smul' := by
        intro r p
        rw [RingHom.id_apply, AEEqFun.smul_mk]
        congr 1
        funext x
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Pi.smul_apply, smul_eq_mul]
        ring }
  have hLm : ∀ p : ℝ × Vec d, ⇑(Lm p) =ᵐ[volume] fun x => p.1 + Φ p.2 x :=
    fun p => AEEqFun.coeFn_mk _ _
  have hinj : Function.Injective Lm := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨c, e⟩ h0
    have h1 : (fun x => c + Φ e x) =ᵐ[volume] 0 := by
      have a1 := hLm (c, e)
      rw [h0] at a1
      exact a1.symm.trans AEEqFun.coeFn_zero
    have h1' : (fun x => c + Φ e x) =ᵐ[normalizedCubeMeasure (originCube d (mstar : ℤ))] 0 :=
      (e0e_normalizedCube_ac _).ae_eq h1
    have hsl : affSlope mstar (fun x => c + Φ e x) = 0 := by
      funext i
      have h2 := e0c_slope_apply mstar (fun x => c + Φ e x) i
      have h3 : ∫ x, (c + Φ e x) * x i ∂(normalizedCubeMeasure (originCube d (mstar : ℤ))) = 0 := by
        rw [integral_congr_ae (g := fun _ => (0 : ℝ))
          (by filter_upwards [h1'] with x hx; simp [hx])]
        simp
      rw [h3] at h2
      have hA : ((3 : ℝ) ^ mstar) ^ 2 / 12 ≠ 0 := by positivity
      exact (mul_eq_zero.1 h2).resolve_left hA
    have hs2 : affSlope mstar (fun x => c + Φ e x) = affSlope mstar (Φ e) + affSlope mstar (fun _ => c) := by
      have e1 : (fun x => c + Φ e x) = fun x => Φ e x + (fun _ : Vec d => c) x :=
        funext fun x => add_comm _ _
      rw [e1]
      exact affSlope_add (hmemΦ e mstar) (memLp_const c)
    have hcs : affSlope mstar (fun _ : Vec d => c) = 0 := by
      have := affSlope_affine mstar c (0 : Vec d)
      simpa [vecDot] using this
    have he : e = 0 := by
      refine hTb.1 ?_
      rw [hT e, ← hslope e, map_zero]
      rw [hs2, hcs, add_zero] at hsl
      exact hsl
    subst he
    have hc : c = 0 := by
      have h4 : ∀ᵐ x ∂(volume : Measure (Vec d)), c = 0 := by
        filter_upwards [h1] with x hx
        simpa using hx
      exact h4.exists.choose_spec
    rw [hc]
    rfl
  have hrange : LinearMap.range Lm = growthSubmodule a γ hGE := by
    ext φ
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨hm, hmem'⟩ := hmem p.1 p.2
      exact hmem'
    · intro hφ
      obtain ⟨c, e0, hce0⟩ := hrep φ hφ
      refine ⟨(c, e0), ?_⟩
      refine AEEqFun.ext ?_
      exact (hLm (c, e0)).trans hce0.symm
  have hspan : Submodule.span ℝ (growthSpace a γ) = growthSubmodule a γ hGE :=
    Submodule.span_eq (growthSubmodule a γ hGE)
  refine ⟨?_, hmem, hrep⟩
  rw [hspan, ← hrange, LinearMap.finrank_range_of_inj hinj]
  simp [Module.finrank_prod, add_comm]

/-- Numerical hypotheses of `eng_liouville` are satisfiable: `η = 3/4`, `κ = 1/48`, `γ = 1/24`,
`δ = 0`. -/
example : ∃ η κ γ : ℝ, (1 / 2 ≤ η ∧ η < 1 ∧ 0 < κ ∧ κ ≤ 1 / 24 ∧ 0 < γ ∧ κ ≤ γ ∧
    γ + 5 * κ < η) ∧ ∀ K : ℝ, 1 ≤ K → (0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1) ∧ K * 0 ≤ 1 / 2 :=
  ⟨3 / 4, 1 / 48, 1 / 24, ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩, fun K _ => ⟨⟨le_rfl, by norm_num⟩, by norm_num⟩⟩

end SuperdiffusionCLT.Section6
