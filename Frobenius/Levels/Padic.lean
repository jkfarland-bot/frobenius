module

/-
Run r25, seat L5: R-083 over `ℤ_[p]` (the ledger's setting), from the `ℤ` case.

For `u ∈ ℤ_[p][[x]]` pick `K ≥ k` above every finite class depth of `u`, and the zero-preserving
lift `u' ∈ ℤ[[x]]` (`coeff u' = appr (coeff u) K`, and `0` where `coeff u = 0`). Then
* `u'` has exactly the depth spaces of `u` (`depthSpace_lift`, `fullSpace_lift`), so the same flag;
* monic annihilators modulo `p ^ k` of `u` and of `u'` have the same degrees (L1's
  `monicAnn_int_of_padic` and `monicAnn_padic_of_int` below);
* over `ℤ`, `u'` has the valuation tower and the top bound (ThmF.lean, TraceFlag.lean) and the
  Cayley-Hamilton cap, whether or not it is a unit.
`levelCount_eq_flagValue_padic`: **R-083 for every unit of `ℤ_[p][[x_1..x_n]]`**.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Lower
public import Frobenius.Levels.LowerPadic
public import Frobenius.Levels.Basis
public import Frobenius.Levels.Digit
public import Frobenius.Levels.PropP
public import Frobenius.Levels.Flag
public import Frobenius.Levels.Cap
public import Frobenius.Levels.ValTower
public import Frobenius.Levels.TraceCore
public import Frobenius.Levels.TraceFlag
public import Frobenius.Levels.Norm
public import Frobenius.Levels.ThmF

@[expose] public section

namespace FrobLevel

open MvPowerSeries

open scoped Classical

section Padic

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ}

theorem pow_dvd_series_iff {R : Type*} [CommRing R] (g : MvPowerSeries (Fin n) R) (j : ℕ) :
    (p : MvPowerSeries (Fin n) R) ^ j ∣ g ↔ ∀ q, (p : R) ^ j ∣ coeff q g := by
  constructor
  · rintro h q
    rw [natCast_pow_eq_C] at h
    obtain ⟨c, hc⟩ := h
    rw [hc, coeff_C_mul]; exact dvd_mul_right _ _
  · intro h
    rw [natCast_pow_eq_C]
    exact C_dvd_of_coeff h

/-- The zero-preserving lift modulo `p ^ K`. -/
noncomputable def lift0 (a : MvPowerSeries (Fin n) ℤ_[p]) (K : ℕ) : MvPowerSeries (Fin n) ℤ :=
  fun e => if coeff e a = 0 then 0 else ((PadicInt.appr (coeff e a) K : ℕ) : ℤ)

theorem coeff_lift0 (a : MvPowerSeries (Fin n) ℤ_[p]) (K : ℕ) (e : Fin n →₀ ℕ) :
    coeff e (lift0 p a K) = if coeff e a = 0 then 0 else ((PadicInt.appr (coeff e a) K : ℕ) : ℤ) :=
  rfl

theorem lift0_dvd (a : MvPowerSeries (Fin n) ℤ_[p]) (K : ℕ) (e : Fin n →₀ ℕ) :
    (p : ℤ_[p]) ^ K ∣ coeff e a - ((coeff e (lift0 p a K) : ℤ) : ℤ_[p]) := by
  rw [coeff_lift0]
  split_ifs with h
  · rw [h]; simp
  · have := PadicInt.appr_spec K (coeff e a)
    rw [Ideal.mem_span_singleton] at this
    simpa using this

theorem lift0_zero (a : MvPowerSeries (Fin n) ℤ_[p]) (K : ℕ) {e : Fin n →₀ ℕ}
    (h : coeff e a = 0) : coeff e (lift0 p a K) = 0 := by
  rw [coeff_lift0, if_pos h]

theorem lift0_series_dvd (a : MvPowerSeries (Fin n) ℤ_[p]) (K : ℕ) :
    (p : MvPowerSeries (Fin n) ℤ_[p]) ^ K
      ∣ a - MvPowerSeries.map (Int.castRingHom ℤ_[p]) (lift0 p a K) := by
  rw [pow_dvd_series_iff]
  intro q
  rw [map_sub, coeff_map, eq_intCast]
  exact lift0_dvd p a K q

/-- Scalar transfer: if `p ^ K ∣ c - z` and `j ≤ K`, then `p ^ j ∣ c ↔ p ^ j ∣ z`. -/
theorem dvd_iff_of_congr {c : ℤ_[p]} {z : ℤ} {K j : ℕ} (h : (p : ℤ_[p]) ^ K ∣ c - (z : ℤ_[p]))
    (hj : j ≤ K) : (p : ℤ_[p]) ^ j ∣ c ↔ (p : ℤ) ^ j ∣ z := by
  have h' : (p : ℤ_[p]) ^ j ∣ c - (z : ℤ_[p]) := (pow_dvd_pow _ hj).trans h
  constructor
  · intro hc
    have : (p : ℤ_[p]) ^ j ∣ (z : ℤ_[p]) := by
      have := dvd_sub hc h'
      rwa [sub_sub_cancel] at this
    have := (PadicInt.pow_p_dvd_int_iff j z).1 this
    exact_mod_cast this
  · intro hz
    have : (p : ℤ_[p]) ^ j ∣ (z : ℤ_[p]) := by
      obtain ⟨w, hw⟩ := hz
      exact ⟨(w : ℤ_[p]), by rw [hw]; push_cast; ring⟩
    have := dvd_add h' this
    rwa [sub_add_cancel] at this

theorem padic_exists_not_dvd {c : ℤ_[p]} (hc : c ≠ 0) : ∃ e, ¬ (p : ℤ_[p]) ^ e ∣ c := by
  refine ⟨c.valuation + 1, fun h => ?_⟩
  have := (PadicInt.mem_span_pow_iff_le_valuation c hc (c.valuation + 1)).1
    (Ideal.mem_span_singleton.2 h)
  omega

/-- A bound `K ≥ k` above every finite class depth of `u`. -/
theorem exists_K (u : MvPowerSeries (Fin n) ℤ_[p]) (k : ℕ) :
    ∃ K, k ≤ K ∧ ∀ κ ∈ digitExps p n, classPart p u κ ≠ 0 →
      ∃ q, ¬ (p : ℤ_[p]) ^ K ∣ coeff q (classPart p u κ) := by
  have hex : ∀ κ : Fin n →₀ ℕ, ∃ e, classPart p u κ ≠ 0 →
      ∃ q, ¬ (p : ℤ_[p]) ^ e ∣ coeff q (classPart p u κ) := by
    intro κ
    by_cases h : classPart p u κ = 0
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨q, hq⟩ : ∃ q, coeff q (classPart p u κ) ≠ 0 := by
        by_contra hc; push Not at hc
        exact h (MvPowerSeries.ext fun q => by rw [hc q, map_zero])
      obtain ⟨e, he⟩ := padic_exists_not_dvd p hq
      exact ⟨e, fun _ => ⟨q, he⟩⟩
  choose ee hee using hex
  refine ⟨k + ∑ κ ∈ digitExps p n, ee κ, by omega, fun κ hκ hne => ?_⟩
  obtain ⟨q, hq⟩ := hee κ hne
  refine ⟨q, fun h => hq ((pow_dvd_pow _ ?_).trans h)⟩
  have := Finset.single_le_sum (f := ee) (fun _ _ => Nat.zero_le _) hκ
  omega

section Lift

variable {u : MvPowerSeries (Fin n) ℤ_[p]} {K : ℕ}
  (hK : ∀ κ ∈ digitExps p n, classPart p u κ ≠ 0 →
    ∃ q, ¬ (p : ℤ_[p]) ^ K ∣ coeff q (classPart p u κ))
include hK

theorem classPart_lift_ne_iff {κ : Fin n →₀ ℕ} (hκ : κ ∈ digitExps p n) :
    classPart p (lift0 p u K) κ ≠ 0 ↔ classPart p u κ ≠ 0 := by
  constructor
  · intro h h0
    apply h
    ext q
    rw [coeff_classPart, map_zero]
    apply lift0_zero
    have := congrArg (coeff q) h0
    rwa [coeff_classPart, map_zero] at this
  · intro h h0
    obtain ⟨q, hq⟩ := hK κ hκ h
    have h1 := lift0_dvd p u K (p • q + κ)
    have h2 : coeff (p • q + κ) (lift0 p u K) = 0 := by
      have := congrArg (coeff q) h0
      rwa [coeff_classPart, map_zero] at this
    rw [h2, Int.cast_zero, sub_zero] at h1
    exact hq (by rw [coeff_classPart]; exact h1)

theorem classPart_lift_dvd_iff {κ : Fin n →₀ ℕ} (hκ : κ ∈ digitExps p n) (j : ℕ) :
    (p : MvPowerSeries (Fin n) ℤ) ^ j ∣ classPart p (lift0 p u K) κ
      ↔ (p : MvPowerSeries (Fin n) ℤ_[p]) ^ j ∣ classPart p u κ := by
  rw [pow_dvd_series_iff, pow_dvd_series_iff]
  by_cases hj : j ≤ K
  · refine forall_congr' fun q => ?_
    rw [coeff_classPart, coeff_classPart]
    exact (dvd_iff_of_congr p (lift0_dvd p u K (p • q + κ)) hj).symm
  · push Not at hj
    -- above `K`: divisibility means zero, on both sides
    have hzero_u : (∀ q, (p : ℤ_[p]) ^ j ∣ coeff q (classPart p u κ)) ↔ classPart p u κ = 0 := by
      constructor
      · intro h
        by_contra hne
        obtain ⟨q, hq⟩ := hK κ hκ hne
        exact hq ((pow_dvd_pow _ hj.le).trans (h q))
      · intro h q; rw [h, map_zero]; exact dvd_zero _
    have hzero_l : (∀ q, (p : ℤ) ^ j ∣ coeff q (classPart p (lift0 p u K) κ))
        ↔ classPart p (lift0 p u K) κ = 0 := by
      constructor
      · intro h
        by_contra hne
        have hne' := (classPart_lift_ne_iff p hK hκ).1 hne
        obtain ⟨q, hq⟩ := hK κ hκ hne'
        have h1 := (dvd_iff_of_congr p (lift0_dvd p u K (p • q + κ)) le_rfl).not.1
          (by rwa [coeff_classPart] at hq)
        exact h1 ((pow_dvd_pow _ hj.le).trans (by have := h q; rwa [coeff_classPart] at this))
      · intro h q; rw [h, map_zero]; exact dvd_zero _
    rw [hzero_u, hzero_l]
    exact not_iff_not.1 (classPart_lift_ne_iff p hK hκ)

theorem depthSpace_lift (d : ℕ) : depthSpace p (lift0 p u K) d = depthSpace p u d := by
  unfold depthSpace
  congr 2
  ext κ
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rwa [← classPart_lift_dvd_iff p hK h1]⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rwa [classPart_lift_dvd_iff p hK h1]⟩

theorem fullSpace_lift : fullSpace p (lift0 p u K) = fullSpace p u := by
  unfold fullSpace
  congr 2
  ext κ
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (classPart_lift_ne_iff p hK h1).1 h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (classPart_lift_ne_iff p hK h1).2 h3⟩

theorem flagValue_lift (k : ℕ) : flagValue p (lift0 p u K) k = flagValue p u k := by
  have hr : rankF p (lift0 p u K) = rankF p u := by unfold rankF; rw [fullSpace_lift p hK]
  have hd : depthFlag p (lift0 p u K) = depthFlag p u := by
    funext j; unfold depthFlag; rw [show depthSpace p (lift0 p u K) = depthSpace p u from
      funext (depthSpace_lift p hK)]
  have hj : flagJump p (lift0 p u K) = flagJump p u := by
    funext j; unfold flagJump; rw [hd]
  unfold flagValue; rw [hr, hj]

end Lift

open Polynomial in
/-- A monic annihilator over `ℤ` of `u'` gives one over `ℤ_[p]` of every `u ≡ u' (mod p ^ k)`. -/
theorem monicAnn_padic_of_int {k m : ℕ} {u : MvPowerSeries (Fin n) ℤ_[p]}
    {u' : MvPowerSeries (Fin n) ℤ}
    (huu : (p : MvPowerSeries (Fin n) ℤ_[p]) ^ k ∣ u - MvPowerSeries.map (Int.castRingHom ℤ_[p]) u')
    (hP : MonicAnn p (frob p) u' k m) : MonicAnn p (frob p) u k m := by
  obtain ⟨P, hmon, hdeg, hB, hPu⟩ := hP
  set ψ : MvPowerSeries (Fin n) ℤ →+* MvPowerSeries (Fin n) ℤ_[p] :=
    MvPowerSeries.map (Int.castRingHom ℤ_[p]) with hψ
  have hfψ : ∀ a, ψ (frob p a) = frob p (ψ a) := fun a => by
    simp [hψ, frob_apply, MvPowerSeries.map_expand]
  refine ⟨P.map ψ, hmon.map ψ, by rw [hmon.natDegree_map, hdeg], ?_, ?_⟩
  · rw [mem_BPoly_iff]
    intro i
    rw [Polynomial.coeff_map]
    obtain ⟨b, hb⟩ := mem_BPoly_iff.1 hB i
    exact ⟨ψ b, by rw [← hb, hfψ]⟩
  · have h1 : (p : MvPowerSeries (Fin n) ℤ_[p]) ^ k ∣ (P.map ψ).eval (ψ u') := by
      rw [eval_map, eval₂_hom]
      obtain ⟨w, hw⟩ := hPu
      exact ⟨ψ w, by rw [hw, map_mul, map_pow, map_natCast]⟩
    have h2 : (p : MvPowerSeries (Fin n) ℤ_[p]) ^ k ∣ (P.map ψ).eval u - (P.map ψ).eval (ψ u') :=
      huu.trans (sub_dvd_eval_sub _ _ _)
    have := dvd_add h2 h1
    rwa [sub_add_cancel] at this

/-- The digit-value minimum with the flag `γ` is the Legendre-type minimum. -/
theorem sInf_digit_eq_flag {N k : ℕ} (δ : ℕ → ℕ) :
    sInf {m | p ^ N ≤ m ∨ k ≤ digitVal p N (flagGamma p δ) m}
      = sInf {m | p ^ N ≤ m ∨ k ≤ padicValNat p m.factorial
          + ∑ j ∈ Finset.range N, δ j * (m / p ^ j)} := by
  congr 1
  ext m
  simp only [Set.mem_ofPred_eq]
  by_cases hm : m < p ^ N
  · rw [digitVal_flagGamma δ hm]
  · simp [not_lt.1 hm]

/-- For any `u' ∈ ℤ[[x]]` (unit or not): the least degree of a monic annihilator modulo `p ^ k`
is R-083's value for the flag of `u'`. -/
theorem annDegree_eq_flagValue_int (u' : MvPowerSeries (Fin n) ℤ) (k : ℕ) :
    annDegree p (frob p) u' k = flagValue p u' k := by
  obtain ⟨T, hT⟩ := thmF_valTower_int p u'
  obtain ⟨C, hCm, hCd, hCB, hCu⟩ := exists_monic_self p u'
  have hcap : MonicAnn p (frob p) u' k (p ^ rankF p u') :=
    ⟨C, hCm, hCd, hCB, by rw [hCu]; exact dvd_zero _⟩
  rw [annDegree_eq_digit_of_top hp.out.one_lt.le hT (topBound_flag_int p u') hcap,
    sInf_digit_eq_flag]
  rfl

/-- **R-083 for every unit of `ℤ_[p][[x_1..x_n]]`** (the ledger's setting): for `f u = 1`, every
prime `p` and every `k ≥ 1`,
`L_f(p, k) + 1 = min(p ^ r_f, min {m : v_p(m!) + ∑_{j<r_f} (d(j+1) - d(j)) ⌊m/p^j⌋ ≥ k})`. -/
theorem levelCount_eq_flagValue_padic {f u : MvPowerSeries (Fin n) ℤ_[p]} (hfu : f * u = 1)
    {k : ℕ} (hk : 1 ≤ k) : levelCount p (frob p) f k + 1 = flagValue p f k := by
  obtain ⟨K, hkK, hK⟩ := exists_K p u k
  set u' := lift0 p u K
  have huu : (p : MvPowerSeries (Fin n) ℤ_[p]) ^ k
      ∣ u - MvPowerSeries.map (Int.castRingHom ℤ_[p]) u' :=
    (pow_dvd_pow _ hkK).trans (lift0_series_dvd p u K)
  have hann : annDegree p (frob p) u k = annDegree p (frob p) u' k := by
    unfold annDegree
    congr 1
    ext m
    exact ⟨monicAnn_int_of_padic p huu, monicAnn_padic_of_int p huu⟩
  rw [levelCount_add_one (by rw [hfu, sub_self]; exact dvd_zero _)
      (not_isUnit_pow_mvPowerSeries p (padicInt_not_isUnit p) hk) (monicAnn_cap p hfu k),
    hann, annDegree_eq_flagValue_int, flagValue_lift p hK, flagValue_inv hfu]

end Padic

end FrobLevel
