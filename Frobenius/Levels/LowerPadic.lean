module

/-
Run r25, seat L1: the lower half of R-080 stage (d) over `ℤ_[p]`, by reduction to `ℤ`
(Lower.lean): a monic annihilator over `B` modulo `p ^ k` with coefficients in `ℤ_[p][[x]]` is
congruent modulo `p ^ k` to one with coefficients in `ℤ[[x]]` (`PadicInt.appr`).
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Lower

@[expose] public section

namespace FrobLevel

open MvPowerSeries

/-! ## 6. From `ℤ_[p]` to `ℤ` (coefficients modulo `p ^ k`) -/

section Padic

variable (p : ℕ) [hp : Fact p.Prime] {τ : Type*}

theorem exists_lift (a : MvPowerSeries τ ℤ_[p]) (k : ℕ) :
    ∃ a' : MvPowerSeries τ ℤ,
      (p : MvPowerSeries τ ℤ_[p]) ^ k ∣ a - MvPowerSeries.map (Int.castRingHom ℤ_[p]) a' := by
  refine ⟨(show MvPowerSeries τ ℤ from fun e => ((PadicInt.appr (coeff e a) k : ℕ) : ℤ)), ?_⟩
  rw [← map_natCast (C (σ := τ) (R := ℤ_[p])), ← map_pow]
  apply C_dvd_of_coeff
  intro e
  rw [map_sub, coeff_map]
  have h := PadicInt.appr_spec k (coeff e a)
  rw [Ideal.mem_span_singleton] at h
  have hc : coeff e (show MvPowerSeries τ ℤ from fun e => ((PadicInt.appr (coeff e a) k : ℕ) : ℤ))
      = ((PadicInt.appr (coeff e a) k : ℕ) : ℤ) := rfl
  rw [hc]
  simpa using h

theorem pullback_dvd {k : ℕ} {w : MvPowerSeries τ ℤ}
    (h : (p : MvPowerSeries τ ℤ_[p]) ^ k ∣ MvPowerSeries.map (Int.castRingHom ℤ_[p]) w) :
    (p : MvPowerSeries τ ℤ) ^ k ∣ w := by
  rw [← map_natCast (C (σ := τ) (R := ℤ)), ← map_pow]
  apply C_dvd_of_coeff
  intro e
  obtain ⟨q, hq⟩ := h
  have h1 := congrArg (coeff e) hq
  rw [coeff_map, ← map_natCast (C (σ := τ) (R := ℤ_[p])), ← map_pow, coeff_C_mul] at h1
  have h2 := congrArg (PadicInt.toZModPow (p := p) k) h1
  rw [map_mul, map_pow, map_natCast, eq_intCast, map_intCast] at h2
  have h3 : ((p : ZMod (p ^ k))) ^ k = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [h3, zero_mul] at h2
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2
  simpa using this

open Polynomial in
theorem dvd_eval_of_coeff {A : Type*} [CommRing A] {c : A} {F : A[X]} (h : ∀ i, c ∣ F.coeff i)
    (x : A) : c ∣ F.eval x := by
  rw [eval_eq_sum_range]
  exact Finset.dvd_sum fun i _ => Dvd.dvd.mul_right (h i) _

open Polynomial in
/-- A monic annihilator over `B` of `u ∈ ℤ_[p][[x]]` modulo `p ^ k` gives one over `ℤ`, of the same
degree, of every `u' ∈ ℤ[[x]]` with `u ≡ u' (mod p ^ k)`. -/
theorem monicAnn_int_of_padic {n k m : ℕ} {u : MvPowerSeries (Fin n) ℤ_[p]}
    {u' : MvPowerSeries (Fin n) ℤ}
    (huu : (p : MvPowerSeries (Fin n) ℤ_[p]) ^ k ∣ u - MvPowerSeries.map (Int.castRingHom ℤ_[p]) u')
    (hP : MonicAnn p (frob p) u k m) : MonicAnn p (frob p) u' k m := by
  classical
  obtain ⟨P, hmon, hdeg, hB, hPu⟩ := hP
  obtain ⟨φ, hφ⟩ : ∃ φ : MvPowerSeries (Fin n) ℤ →+* MvPowerSeries (Fin n) ℤ_[p],
      φ = MvPowerSeries.map (Int.castRingHom ℤ_[p]) := ⟨_, rfl⟩
  have hfφ : ∀ a, φ (frob p a) = frob p (φ a) := fun a => by
    simp [hφ, frob_apply, MvPowerSeries.map_expand]
  choose b hb using fun i => mem_BPoly_iff.1 hB i
  choose b' hb' using fun i => exists_lift p (τ := Fin n) (b i) k
  obtain ⟨L, hL⟩ : ∃ L : Polynomial (MvPowerSeries (Fin n) ℤ),
      L = ∑ i ∈ Finset.range m, Polynomial.C (frob p (b' i)) * Polynomial.X ^ i := ⟨_, rfl⟩
  have hLdeg : L.degree < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp [hL]
    rw [hL]
    refine (degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro i hi
    exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast Finset.mem_range.1 hi)
  have hP'm : (Polynomial.X ^ m + L).Monic := monic_X_pow_add hLdeg
  have hP'd : (Polynomial.X ^ m + L).natDegree = m := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have hP'B : Polynomial.X ^ m + L ∈ BPoly (frob p) := by
    have hσX := X_mem_BPoly (frob p : MvPowerSeries (Fin n) ℤ →+* MvPowerSeries (Fin n) ℤ)
    rw [hL]
    refine add_mem (pow_mem hσX m) (sum_mem fun i _ => ?_)
    exact mul_mem (C_mem_BPoly (frob p : MvPowerSeries (Fin n) ℤ →+* MvPowerSeries (Fin n) ℤ) (b' i))
      (pow_mem hσX i)
  refine ⟨Polynomial.X ^ m + L, hP'm, hP'd, hP'B, pullback_dvd p ?_⟩
  rw [← hφ]
  have hcoef : ∀ i, (Polynomial.X ^ m + L).coeff i
      = (if i = m then 1 else 0) + (if i < m then frob p (b' i) else 0) := by
    intro i
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, hL, Polynomial.finsetSum_coeff]
    congr 1
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range]
  have hdiff : ∀ i, (p : MvPowerSeries (Fin n) ℤ_[p]) ^ k ∣ ((Polynomial.X ^ m + L).map φ - P).coeff i := by
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_map, hcoef]
    rcases lt_trichotomy i m with hi | hi | hi
    · rw [if_neg hi.ne, if_pos hi, zero_add, hfφ, ← hb i, ← map_sub]
      obtain ⟨w, hw⟩ := hb' i
      rw [← hφ] at hw
      refine ⟨-frob p w, ?_⟩
      rw [show φ (b' i) - b i = -(b i - φ (b' i)) by ring, map_neg, hw, map_mul, map_pow,
        map_natCast]
      ring
    · subst hi
      rw [if_pos rfl, if_neg (lt_irrefl _), add_zero, map_one, ← hdeg, hmon.coeff_natDegree,
        sub_self]
      exact dvd_zero _
    · rw [if_neg hi.ne', if_neg (not_lt.2 hi.le), add_zero, map_zero, zero_sub,
        coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hi), neg_zero]
      exact dvd_zero _
  have h1 := dvd_eval_of_coeff hdiff u
  rw [eval_sub] at h1
  have h2 := (dvd_sub_left hPu).1 h1
  rw [← hφ] at huu
  have h3 : (p : MvPowerSeries (Fin n) ℤ_[p]) ^ k
      ∣ ((Polynomial.X ^ m + L).map φ).eval (φ u') - ((Polynomial.X ^ m + L).map φ).eval u :=
    (dvd_neg.2 huu).trans (by rw [neg_sub]; exact sub_dvd_eval_sub _ _ _)
  have h4 := (dvd_sub_left h2).1 h3
  rwa [eval_map, eval₂_hom] at h4

/-- Full rank passes to a lift modulo `p ^ k`, `k ≥ 1`. -/
theorem fullRank_int_of_padic {n k : ℕ} (hk : 1 ≤ k) {u : MvPowerSeries (Fin n) ℤ_[p]}
    {u' : MvPowerSeries (Fin n) ℤ}
    (huu : (p : MvPowerSeries (Fin n) ℤ_[p]) ^ k ∣ u - MvPowerSeries.map (Int.castRingHom ℤ_[p]) u')
    (hu : FullRank p u) : FullRank p u' := by
  intro h hlt hne
  obtain ⟨m, hm1, hm2⟩ := hu h hlt hne
  refine ⟨m, hm1, fun hd => hm2 ?_⟩
  obtain ⟨q, hq⟩ := huu
  have h1 := congrArg (coeff m) hq
  rw [map_sub, coeff_map, ← map_natCast (C (σ := Fin n) (R := ℤ_[p])), ← map_pow,
    coeff_C_mul] at h1
  have h2 : (p : ℤ_[p]) ∣ Int.castRingHom ℤ_[p] (coeff m u') := by
    obtain ⟨c, hc⟩ := hd
    exact ⟨c, by rw [hc]; simp⟩
  rw [show coeff m u = (p : ℤ_[p]) ^ k * coeff m q + Int.castRingHom ℤ_[p] (coeff m u') by
    rw [← h1]; ring]
  exact dvd_add (Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _) h2

/-- Lower bound over `ℤ_[p]`: if `u ∈ ℤ_[p][[x_1..x_n]]` has full rank and `k ≥ 1`, a monic
annihilator of `u` over `B` modulo `p ^ k` of degree `m < p ^ n` has `S(p ^ k) ≤ m`. -/
theorem kempner_le_of_monicAnn_padic {n k m : ℕ} (hk : 1 ≤ k) {u : MvPowerSeries (Fin n) ℤ_[p]}
    (hu : FullRank p u) (hm : m < p ^ n) (hP : MonicAnn p (frob p) u k m) : kempner p k ≤ m := by
  obtain ⟨u', hu'⟩ := exists_lift p u k
  exact kempner_le_of_monicAnn_int p (fullRank_int_of_padic p hk hu' hu) hm
    (monicAnn_int_of_padic p hu' hP)

/-- R-080 (C2) with `ρ = r = n`, in the ledger's setting `A = ℤ_[p][[x_1..x_n]]`: for a unit `f`
whose inverse has full rank, `L_f(p, k) + 1 = min (p ^ n) (S(p ^ k))` for every `k ≥ 1`. -/
theorem levelCount_eq_of_fullRank_padic {n : ℕ} {f u : MvPowerSeries (Fin n) ℤ_[p]}
    (hfu : f * u = 1) (hu : FullRank p u) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) f k + 1 = min (p ^ n) (kempner p k) := by
  refine le_antisymm (levelCount_le_min_padic p ⟨⟨f, u, hfu, by rw [mul_comm]; exact hfu⟩, rfl⟩ hk) ?_
  have hfu' : (p : MvPowerSeries (Fin n) ℤ_[p]) ^ k ∣ f * u - 1 := by
    rw [hfu, sub_self]; exact dvd_zero _
  have hpk := not_isUnit_pow_mvPowerSeries (τ := Fin n) p (padicInt_not_isUnit p) hk
  have hex := monicAnn_kempner (frob_isFrobLift p (padicInt_pow_sub p)) u k
  rw [levelCount_add_one hfu' hpk hex]
  have hmin := monicAnn_annDegree hex
  by_cases hlt : annDegree p (frob p) u k < p ^ n
  · exact (min_le_right _ _).trans (kempner_le_of_monicAnn_padic p hk hu hlt hmin)
  · exact (min_le_left _ _).trans (not_lt.1 hlt)

/-- R-080 (C) in the ledger's setting `A = ℤ_[p][[x_1..x_n]]`:
`L(ζ_n; p, k) + 1 = min (p ^ n) (S(p ^ k))` for every `n`, prime `p` and `k ≥ 1`. -/
theorem levelCount_zeta_padic (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) (zeta (R := ℤ_[p]) n) k + 1 = min (p ^ n) (kempner p k) :=
  levelCount_eq_of_fullRank_padic p (by rw [mul_comm]; exact zetaDen_mul_zeta n)
    (fullRank_zetaDen p (padicInt_not_isUnit p) n) hk

end Padic

end FrobLevel
