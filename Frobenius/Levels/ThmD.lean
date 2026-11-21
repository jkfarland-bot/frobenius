module

/-
Run r25, seat L6: **Theorem D** (ledger R-080 (D), "pure depth"; note Corollary `cor:special` (c);
listed in R-083 as a special case) as a corollary of R-083 (L5's `levelCount_eq_flagValue_int`,
`_padic`), for every unit, over `ℤ` and `ℤ_[p]`, any number of variables.

Setting: `u = 1/f = σ(b) + p ^ J τ` (L3's form), `ρ(τ) = dim U_0(τ)` (the `F_p`-rank of the
classes of `τ` modulo `p`), `m_J(k) = min {m : J m + v_p(m!) ≥ k}`. Then

* `flag_thmD`: `U_d(u) = 0` for `d < J`, `U_{J+d}(u) = U_d(τ)`; hence `d(j) = J` for
  `1 ≤ j ≤ ρ(τ)` and `ρ(τ) ≤ r_f`;
* `flagValue_thmD_ge`, `levelCount_thmD_ge_int`, `_padic`: `L_f + 1 ≥ min(p ^ ρ(τ), m_J(k))`;
* `flagValue_thmD_eq`, `levelCount_thmD_eq_int`, `_padic`: equality when `ρ(τ) = r_f`.
* The note's form `1/f = s (1 + p ^ J τ)` with `s = σ(s₀)`, `s₀` a unit:
  `levelCount_thmD_note_ge_int`, `_padic`, `levelCount_thmD_note_eq_int`, `_padic`.

`J = 0` is allowed (the note assumes `J ≥ 1`; not needed).

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.Digit
public import Frobenius.Levels.Flag
public import Frobenius.Levels.Cap
public import Frobenius.Levels.TraceFlag
public import Frobenius.Levels.ThmF
public import Frobenius.Levels.Padic
public import Frobenius.Levels.Assemble
public import Frobenius.Levels.FlagCalc

@[expose] public section

namespace FrobLevel

open MvPowerSeries

section ThmD

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] {n : ℕ}

/-- `m_J(k)`: the least `m` with `J m + v_p(m!) ≥ k`. -/
noncomputable def depthMinS (J k : ℕ) : ℕ := sInf {m | k ≤ J * m + padicValNat p m.factorial}

/-- `ρ(τ) = dim U_0(τ)`. -/
noncomputable def rho (τ : MvPowerSeries (Fin n) R) : ℕ := Module.finrank (ZMod p) (depthSpace p τ 0)

variable {p}

/-- The depth spaces of `u = σ(b) + p ^ J τ`: in terms of finranks. -/
theorem finrank_depthSpace_thmD (ht : NoPTorsion p R) {u b τ : MvPowerSeries (Fin n) R} {J : ℕ}
    (hu : u = frob p b + (p : MvPowerSeries (Fin n) R) ^ J * τ) {j : ℕ} (hj1 : 1 ≤ j)
    (hjρ : j ≤ rho p τ) (d : ℕ) :
    j ≤ Module.finrank (ZMod p) (depthSpace p u d) ↔ J ≤ d := by
  constructor
  · intro h
    by_contra hd
    push Not at hd
    rw [depthSpace_shift_lt p hu hd, finrank_bot] at h
    omega
  · intro hd
    have h1 : depthSpace p u J ≤ depthSpace p u d := depthSpace_mono p u hd
    have h2 : depthSpace p u J = depthSpace p τ 0 := by
      have := depthSpace_shift p ht hu 0
      rwa [add_zero] at this
    have := Submodule.finrank_mono h1
    rw [h2] at this
    exact hjρ.trans this

/-- **The flag of `u = σ(b) + p ^ J τ`**: `d(j) = J` for `1 ≤ j ≤ ρ(τ)`. -/
theorem depthFlag_thmD (ht : NoPTorsion p R) {u b τ : MvPowerSeries (Fin n) R} {J : ℕ}
    (hu : u = frob p b + (p : MvPowerSeries (Fin n) R) ^ J * τ) {j : ℕ} (hj1 : 1 ≤ j)
    (hjρ : j ≤ rho p τ) : depthFlag p u j = J := by
  rw [depthFlag, if_neg (by omega)]
  exact sInf_eq_of_iff (finrank_depthSpace_thmD ht hu hj1 hjρ)

/-- `ρ(τ) ≤ r_u`. -/
theorem rho_le_rankF (ht : NoPTorsion p R) {u b τ : MvPowerSeries (Fin n) R} {J : ℕ}
    (hu : u = frob p b + (p : MvPowerSeries (Fin n) R) ^ J * τ) : rho p τ ≤ rankF p u := by
  have h2 : depthSpace p u J = depthSpace p τ 0 := by
    have := depthSpace_shift p ht hu 0
    rwa [add_zero] at this
  unfold rho rankF
  rw [← h2]
  exact Submodule.finrank_mono (depthSpace_le_fullSpace p u J)

/-- For `m < p ^ ρ(τ)` the flag sum of `u` is `J m`. -/
theorem flagSum_thmD (ht : NoPTorsion p R) {u b τ : MvPowerSeries (Fin n) R} {J : ℕ}
    (hu : u = frob p b + (p : MvPowerSeries (Fin n) R) ^ J * τ) {m : ℕ} (hm : m < p ^ rho p τ) :
    ∑ j ∈ Finset.range (rankF p u), flagJump p u j * (m / p ^ j) = J * m := by
  have hp1 := hp.out.one_lt
  have hρr := rho_le_rankF ht hu
  rcases Nat.eq_zero_or_pos (rho p τ) with h0 | hpos
  · rw [h0, pow_zero] at hm
    have : m = 0 := by omega
    subst this
    simp
  · rw [Finset.sum_eq_single 0]
    · rw [pow_zero, Nat.div_one]
      show (depthFlag p u (0 + 1) - depthFlag p u 0) * m = J * m
      rw [depthFlag_thmD ht hu (le_refl 1) hpos, depthFlag, if_pos rfl, Nat.sub_zero]
    · intro j _ hj0
      by_cases hjρ : j < rho p τ
      · show (depthFlag p u (j + 1) - depthFlag p u j) * (m / p ^ j) = 0
        rw [depthFlag_thmD ht hu (by omega) hjρ, depthFlag_thmD ht hu (by omega) hjρ.le,
          Nat.sub_self, zero_mul]
      · push Not at hjρ
        have : m / p ^ j = 0 := Nat.div_eq_of_lt
          (hm.trans_le (Nat.pow_le_pow_right (by omega) hjρ))
        rw [this, mul_zero]
    · intro h0
      exfalso
      exact h0 (Finset.mem_range.2 (by omega))

/-- **Theorem D, lower half, for the formula**: `min(p ^ ρ(τ), m_J(k)) ≤ flagValue u k`. -/
theorem flagValue_thmD_ge (ht : NoPTorsion p R) {u b τ : MvPowerSeries (Fin n) R} {J : ℕ}
    (hu : u = frob p b + (p : MvPowerSeries (Fin n) R) ^ J * τ) (k : ℕ) :
    min (p ^ rho p τ) (depthMinS p J k) ≤ flagValue p u k := by
  have hp1 := hp.out.one_lt
  set S := {m | p ^ rankF p u ≤ m ∨ k ≤ padicValNat p m.factorial
    + ∑ j ∈ Finset.range (rankF p u), flagJump p u j * (m / p ^ j)} with hS
  have hV : flagValue p u k = sInf S := rfl
  have hne : S.Nonempty := ⟨p ^ rankF p u, Or.inl le_rfl⟩
  have hmem := Nat.sInf_mem hne
  rw [hV]
  by_cases hlt : sInf S < p ^ rho p τ
  · have hlt' : sInf S < p ^ rankF p u :=
      hlt.trans_le (Nat.pow_le_pow_right (by omega) (rho_le_rankF ht hu))
    rcases hmem with h | h
    · omega
    · rw [flagSum_thmD ht hu hlt] at h
      have : depthMinS p J k ≤ sInf S := Nat.sInf_le (by
        show k ≤ J * sInf S + padicValNat p (sInf S).factorial
        omega)
      exact (min_le_right _ _).trans this
  · push Not at hlt
    exact (min_le_left _ _).trans hlt

/-- **Theorem D, equality for the formula** when `ρ(τ) = r_u`. -/
theorem flagValue_thmD_eq (ht : NoPTorsion p R) {u b τ : MvPowerSeries (Fin n) R} {J : ℕ}
    (hu : u = frob p b + (p : MvPowerSeries (Fin n) R) ^ J * τ) (hρ : rho p τ = rankF p u)
    (k : ℕ) : flagValue p u k = min (p ^ rho p τ) (depthMinS p J k) := by
  refine le_antisymm ?_ (flagValue_thmD_ge ht hu k)
  set S := {m | p ^ rankF p u ≤ m ∨ k ≤ padicValNat p m.factorial
    + ∑ j ∈ Finset.range (rankF p u), flagJump p u j * (m / p ^ j)} with hS
  have hV : flagValue p u k = sInf S := rfl
  rw [hV]
  rcases le_total (p ^ rho p τ) (depthMinS p J k) with hle | hle
  · rw [min_eq_left hle]
    exact Nat.sInf_le (Or.inl (by rw [hρ]))
  · rw [min_eq_right hle]
    by_cases hlt : depthMinS p J k < p ^ rho p τ
    · apply Nat.sInf_le
      right
      rw [flagSum_thmD ht hu hlt]
      have hne : {m | k ≤ J * m + padicValNat p m.factorial}.Nonempty :=
        ⟨kempner p k, by
          show k ≤ J * kempner p k + padicValNat p (kempner p k).factorial
          have := kempner_spec p k
          omega⟩
      have := Nat.sInf_mem hne
      show k ≤ padicValNat p (depthMinS p J k).factorial + J * depthMinS p J k
      have h' : k ≤ J * depthMinS p J k + padicValNat p (depthMinS p J k).factorial := this
      omega
    · push Not at hlt
      exact Nat.sInf_le (Or.inl (by rw [← hρ]; omega))

end ThmD

section ThmDLevel

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ}

/-- **Theorem D (lower bound), every unit of `ℤ[[x_1..x_n]]`**: if `1/f = σ(b) + p ^ J τ`, then
`min(p ^ ρ(τ), m_J(k)) ≤ L_f(p, k) + 1`. -/
theorem levelCount_thmD_ge_int {f u b τ : MvPowerSeries (Fin n) ℤ} (hfu : f * u = 1) {J : ℕ}
    (hu : u = frob p b + (p : MvPowerSeries (Fin n) ℤ) ^ J * τ) {k : ℕ} (hk : 1 ≤ k) :
    min (p ^ rho p τ) (depthMinS p J k) ≤ levelCount p (frob p) f k + 1 := by
  rw [levelCount_eq_flagValue_int p hfu hk, ← flagValue_inv hfu]
  exact flagValue_thmD_ge (int_noPTorsion p) hu k

/-- **Theorem D (equality), every unit of `ℤ[[x_1..x_n]]`** with `ρ(τ) = r_f`. -/
theorem levelCount_thmD_eq_int {f u b τ : MvPowerSeries (Fin n) ℤ} (hfu : f * u = 1) {J : ℕ}
    (hu : u = frob p b + (p : MvPowerSeries (Fin n) ℤ) ^ J * τ) (hρ : rho p τ = rankF p f)
    {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) f k + 1 = min (p ^ rho p τ) (depthMinS p J k) := by
  rw [levelCount_eq_flagValue_int p hfu hk, ← flagValue_inv hfu]
  exact flagValue_thmD_eq (int_noPTorsion p) hu (by rw [hρ, rankF_inv hfu]) k

theorem levelCount_thmD_ge_padic {f u b τ : MvPowerSeries (Fin n) ℤ_[p]} (hfu : f * u = 1)
    {J : ℕ} (hu : u = frob p b + (p : MvPowerSeries (Fin n) ℤ_[p]) ^ J * τ) {k : ℕ}
    (hk : 1 ≤ k) : min (p ^ rho p τ) (depthMinS p J k) ≤ levelCount p (frob p) f k + 1 := by
  rw [levelCount_eq_flagValue_padic p hfu hk, ← flagValue_inv hfu]
  exact flagValue_thmD_ge (padicInt_noPTorsion p) hu k

theorem levelCount_thmD_eq_padic {f u b τ : MvPowerSeries (Fin n) ℤ_[p]} (hfu : f * u = 1)
    {J : ℕ} (hu : u = frob p b + (p : MvPowerSeries (Fin n) ℤ_[p]) ^ J * τ)
    (hρ : rho p τ = rankF p f) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) f k + 1 = min (p ^ rho p τ) (depthMinS p J k) := by
  rw [levelCount_eq_flagValue_padic p hfu hk, ← flagValue_inv hfu]
  exact flagValue_thmD_eq (padicInt_noPTorsion p) hu (by rw [hρ, rankF_inv hfu]) k

/-- The note's form `1/f = s (1 + p ^ J τ)`, `s = σ(s₀)`, is L3's form with `τ' = s τ`, and
`ρ(s τ) = ρ(τ)`. -/
theorem note_form {R : Type*} [CommRing R] {s₀ τ : MvPowerSeries (Fin n) R} (hs : IsUnit s₀)
    (J : ℕ) :
    frob p s₀ * (1 + (p : MvPowerSeries (Fin n) R) ^ J * τ)
        = frob p s₀ + (p : MvPowerSeries (Fin n) R) ^ J * (frob p s₀ * τ) ∧
      rho p (frob p s₀ * τ) = rho p τ := by
  refine ⟨by ring, ?_⟩
  unfold rho
  rw [depthSpace_frob_mul p hs]

/-- **Theorem D in the note's form** (Corollary `cor:special` (c)), over `ℤ`: if
`1/f = σ(s₀) (1 + p ^ J τ)` with `s₀` a unit, then `L_f + 1 ≥ min(p ^ ρ(τ), m_J(k))`, with
equality when `ρ(τ) = r_f`. -/
theorem levelCount_thmD_note_int {f s₀ τ : MvPowerSeries (Fin n) ℤ} {J : ℕ}
    (hs : IsUnit s₀) (hfu : f * (frob p s₀ * (1 + (p : MvPowerSeries (Fin n) ℤ) ^ J * τ)) = 1)
    {k : ℕ} (hk : 1 ≤ k) :
    min (p ^ rho p τ) (depthMinS p J k) ≤ levelCount p (frob p) f k + 1 ∧
      (rho p τ = rankF p f →
        levelCount p (frob p) f k + 1 = min (p ^ rho p τ) (depthMinS p J k)) := by
  obtain ⟨h1, h2⟩ := note_form p hs (τ := τ) J
  rw [h1] at hfu
  refine ⟨?_, fun hρ => ?_⟩
  · rw [← h2]; exact levelCount_thmD_ge_int p hfu rfl hk
  · rw [← h2] at hρ ⊢; exact levelCount_thmD_eq_int p hfu rfl hρ hk

/-- The same over `ℤ_[p]`. -/
theorem levelCount_thmD_note_padic {f s₀ τ : MvPowerSeries (Fin n) ℤ_[p]} {J : ℕ}
    (hs : IsUnit s₀)
    (hfu : f * (frob p s₀ * (1 + (p : MvPowerSeries (Fin n) ℤ_[p]) ^ J * τ)) = 1)
    {k : ℕ} (hk : 1 ≤ k) :
    min (p ^ rho p τ) (depthMinS p J k) ≤ levelCount p (frob p) f k + 1 ∧
      (rho p τ = rankF p f →
        levelCount p (frob p) f k + 1 = min (p ^ rho p τ) (depthMinS p J k)) := by
  obtain ⟨h1, h2⟩ := note_form p hs (τ := τ) J
  rw [h1] at hfu
  refine ⟨?_, fun hρ => ?_⟩
  · rw [← h2]; exact levelCount_thmD_ge_padic p hfu rfl hk
  · rw [← h2] at hρ ⊢; exact levelCount_thmD_eq_padic p hfu rfl hρ hk

end ThmDLevel

end FrobLevel
