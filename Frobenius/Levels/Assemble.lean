module

/-
Run r25, seat L5: consequences of R-083 (ThmF.lean, Padic.lean).

* `levelCount_inv_int`, `levelCount_inv_padic`: `L_f = L_{1/f}` (R-083 consequence).
* `levelCount_thmM_int`, `levelCount_thmM_padic`: **general Theorem M** (ledger R-082 (2), note
  Corollary 6.4 (d)): for every unit `f` whose flag starts `d(1) = 0`, `d(2) = J`, `r_f ≥ 2`:
  `L_f + 1 = p ⌈k/(J+1)⌉` while `⌈k/(J+1)⌉ ≤ p - 1`; `L_f + 1 ≥ p ^ 2` beyond, with equality when
  `r_f = 2`. (`ρ(f) = 1` is `d(1) = 0 < d(2)`; the formula holds for any `J`.)
* `levelCount_large_int`, `_padic`: `L_f + 1 = p ^ r_f` as soon as `k > ∑_{b<r_f} (p-1) γ_b`.
* Dirichlet ring (L3's transfer): `levelCount_dir_smooth_int`, `_padic`: a unit `f` supported on
  `{q_1..q_n}`-smooth arguments has `L_f + 1 = flagValue p (res f) k` (R-084 for finitely many
  primes, every flag); `flagValue_res_le_int`, `_padic`: for every unit `f` and every finite set
  of primes, `flagValue p (res f) k ≤ L_f + 1` (the lower half of R-084).

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
public import Frobenius.Levels.ThmM
public import Frobenius.Levels.Flag
public import Frobenius.Levels.DirBase
public import Frobenius.Levels.DirMain
public import Frobenius.Levels.DirTransfer
public import Frobenius.Levels.Cap
public import Frobenius.Levels.ValTower
public import Frobenius.Levels.TraceCore
public import Frobenius.Levels.TraceFlag
public import Frobenius.Levels.Norm
public import Frobenius.Levels.ThmF
public import Frobenius.Levels.Padic

@[expose] public section

namespace FrobLevel

open MvPowerSeries

section Inv

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ}

theorem levelCount_inv_int {f u : MvPowerSeries (Fin n) ℤ} (hfu : f * u = 1) {k : ℕ}
    (hk : 1 ≤ k) : levelCount p (frob p) u k = levelCount p (frob p) f k := by
  have h1 := levelCount_eq_flagValue_int p hfu hk
  have h2 := levelCount_eq_flagValue_int p (show u * f = 1 by rw [mul_comm]; exact hfu) hk
  rw [flagValue_inv hfu] at h2
  omega

theorem levelCount_inv_padic {f u : MvPowerSeries (Fin n) ℤ_[p]} (hfu : f * u = 1) {k : ℕ}
    (hk : 1 ≤ k) : levelCount p (frob p) u k = levelCount p (frob p) f k := by
  have h1 := levelCount_eq_flagValue_padic p hfu hk
  have h2 := levelCount_eq_flagValue_padic p (show u * f = 1 by rw [mul_comm]; exact hfu) hk
  rw [flagValue_inv hfu] at h2
  omega

end Inv

section ThmMGeneral

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ} {R : Type*} [CommRing R]

theorem padicValNat_factorial_lt_sq {m : ℕ} (hm : m < p ^ 2) :
    padicValNat p m.factorial = m / p := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; simp
  · have hlog : Nat.log p m < 2 := Nat.log_lt_of_lt_pow hpos.ne' hm
    rw [padicValNat_factorial hlog]
    simp [Finset.sum_Ico_eq_sum_range]

/-- For `m < p ^ 2` and a flag with `d(1) = 0`, `d(2) = J`, `N ≥ 2`, the flag sum is `(J+1) ⌊m/p⌋`. -/
theorem flagSum_lt_sq (f : MvPowerSeries (Fin n) R) {J : ℕ} (h1 : depthFlag p f 1 = 0)
    (h2 : depthFlag p f 2 = J) {N : ℕ} (hN : 2 ≤ N) {m : ℕ} (hm : m < p ^ 2) :
    padicValNat p m.factorial + ∑ j ∈ Finset.range N, flagJump p f j * (m / p ^ j)
      = digit p 1 m * (J + 1) := by
  have hp1 := hp.out.one_lt
  have hmp : m / p < p := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [sq] at hm; exact hm
  have hd : digit p 1 m = m / p := by
    rw [digit, pow_one, Nat.mod_eq_of_lt hmp]
  obtain ⟨M, rfl⟩ : ∃ M, N = 2 + M := ⟨N - 2, by omega⟩
  rw [Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_one]
  have hd0 : depthFlag p f 0 = 0 := by simp [depthFlag]
  have hj0 : flagJump p f 0 = 0 := by
    show depthFlag p f 1 - depthFlag p f 0 = 0
    rw [h1, hd0]
  have hj1 : flagJump p f 1 = J := by
    show depthFlag p f 2 - depthFlag p f 1 = J
    rw [h2, h1, Nat.sub_zero]
  have hrest : ∑ x ∈ Finset.range M, flagJump p f (2 + x) * (m / p ^ (2 + x)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    have : m / p ^ (2 + x) = 0 := by
      rw [Nat.div_eq_zero_iff]; right
      exact hm.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
    rw [this, mul_zero]
  rw [hrest, hj0, hj1, padicValNat_factorial_lt_sq p hm, hd, pow_one]
  ring

/-- **Theorem M (arithmetic form)** for `flagValue`. -/
theorem flagValue_thmM (f : MvPowerSeries (Fin n) R) {J k : ℕ} (hk : 1 ≤ k)
    (h1 : depthFlag p f 1 = 0) (h2 : depthFlag p f 2 = J) (hr : 2 ≤ rankF p f) :
    ((k + J) / (J + 1) ≤ p - 1 → flagValue p f k = p * ((k + J) / (J + 1))) ∧
    (p - 1 < (k + J) / (J + 1) → p ^ 2 ≤ flagValue p f k) ∧
    (rankF p f = 2 → p - 1 < (k + J) / (J + 1) → flagValue p f k = p ^ 2) := by
  have hp2 := hp.out.two_le
  set N := rankF p f
  set SF := {m | p ^ N ≤ m ∨ k ≤ padicValNat p m.factorial
    + ∑ j ∈ Finset.range N, flagJump p f j * (m / p ^ j)} with hSF
  set SM := {m | p ^ 2 ≤ m ∨ k ≤ digit p 1 m * (J + 1)} with hSM
  have hV : flagValue p f k = sInf SF := rfl
  have hpN : p ^ 2 ≤ p ^ N := Nat.pow_le_pow_right (by omega) hr
  have key : ∀ m, m < p ^ 2 → (m ∈ SF ↔ m ∈ SM) := by
    intro m hm
    simp only [hSF, hSM, Set.mem_ofPred_eq]
    rw [flagSum_lt_sq p f h1 h2 hr hm]
    constructor
    · rintro (h | h); · omega
      · exact Or.inr h
    · rintro (h | h); · omega
      · exact Or.inr h
  have hSFne : SF.Nonempty := ⟨p ^ N, Or.inl le_rfl⟩
  have hSMne : SM.Nonempty := ⟨p ^ 2, Or.inl le_rfl⟩
  have hM := sInf_thmM (p := p) hp2 (J := J) hk
  refine ⟨fun hc => ?_, fun hc => ?_, fun hr2 hc => ?_⟩
  · rw [if_pos hc] at hM
    have hlt : p * ((k + J) / (J + 1)) < p ^ 2 := by
      rw [sq]; exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    rw [hV]
    apply le_antisymm
    · apply Nat.sInf_le
      have : p * ((k + J) / (J + 1)) ∈ SM := by rw [← hM]; exact Nat.sInf_mem hSMne
      exact (key _ hlt).2 this
    · by_contra hcon
      push Not at hcon
      have hmem : sInf SF ∈ SM := (key _ (hcon.trans hlt)).1 (Nat.sInf_mem hSFne)
      have := Nat.sInf_le hmem
      rw [hM] at this
      omega
  · rw [if_neg (by omega)] at hM
    rw [hV]
    by_contra hcon
    push Not at hcon
    have hmem : sInf SF ∈ SM := (key _ hcon).1 (Nat.sInf_mem hSFne)
    have := Nat.sInf_le hmem
    rw [hM] at this
    omega
  · rw [if_neg (by omega)] at hM
    have hle : flagValue p f k ≤ p ^ 2 := by
      rw [hV]; exact Nat.sInf_le (Or.inl (by rw [hr2]))
    have hge : p ^ 2 ≤ flagValue p f k := by
      rw [hV]
      by_contra hcon
      push Not at hcon
      have hmem : sInf SF ∈ SM := (key _ hcon).1 (Nat.sInf_mem hSFne)
      have := Nat.sInf_le hmem
      rw [hM] at this
      omega
    omega

/-- **Theorem M for every unit of `ℤ_[p][[x_1..x_n]]`** with flag `(0, J, ...)`, `r_f ≥ 2`. -/
theorem levelCount_thmM_padic {f u : MvPowerSeries (Fin n) ℤ_[p]} (hfu : f * u = 1) {J k : ℕ}
    (hk : 1 ≤ k) (h1 : depthFlag p f 1 = 0) (h2 : depthFlag p f 2 = J) (hr : 2 ≤ rankF p f) :
    ((k + J) / (J + 1) ≤ p - 1 → levelCount p (frob p) f k + 1 = p * ((k + J) / (J + 1))) ∧
    (p - 1 < (k + J) / (J + 1) → p ^ 2 ≤ levelCount p (frob p) f k + 1) ∧
    (rankF p f = 2 → p - 1 < (k + J) / (J + 1) → levelCount p (frob p) f k + 1 = p ^ 2) := by
  rw [levelCount_eq_flagValue_padic p hfu hk]
  exact flagValue_thmM p f hk h1 h2 hr

theorem levelCount_thmM_int {f u : MvPowerSeries (Fin n) ℤ} (hfu : f * u = 1) {J k : ℕ}
    (hk : 1 ≤ k) (h1 : depthFlag p f 1 = 0) (h2 : depthFlag p f 2 = J) (hr : 2 ≤ rankF p f) :
    ((k + J) / (J + 1) ≤ p - 1 → levelCount p (frob p) f k + 1 = p * ((k + J) / (J + 1))) ∧
    (p - 1 < (k + J) / (J + 1) → p ^ 2 ≤ levelCount p (frob p) f k + 1) ∧
    (rankF p f = 2 → p - 1 < (k + J) / (J + 1) → levelCount p (frob p) f k + 1 = p ^ 2) := by
  rw [levelCount_eq_flagValue_int p hfu hk]
  exact flagValue_thmM p f hk h1 h2 hr

end ThmMGeneral

section Large

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ} {R : Type*} [CommRing R]

/-- For `k > ∑_{b<r} (p - 1) γ_b` the formula is the cap `p ^ r`. -/
theorem flagValue_large (f : MvPowerSeries (Fin n) R) {k : ℕ}
    (hk : topVal p (rankF p f) (flagGamma p (flagJump p f)) < k) :
    flagValue p f k = p ^ rankF p f := by
  set N := rankF p f
  set S := {m | p ^ N ≤ m ∨ k ≤ padicValNat p m.factorial
      + ∑ j ∈ Finset.range N, flagJump p f j * (m / p ^ j)} with hS
  have hV : flagValue p f k = sInf S := rfl
  apply le_antisymm
  · exact Nat.sInf_le (Or.inl le_rfl)
  · by_contra hcon
    push Not at hcon
    rw [hV] at hcon
    have hmem := Nat.sInf_mem (s := S) ⟨p ^ N, Or.inl le_rfl⟩
    generalize sInf S = m at hmem hcon
    simp only [hS, Set.mem_ofPred_eq] at hmem
    rcases hmem with h | h
    · omega
    · rw [← digitVal_flagGamma _ hcon] at h
      have hle : digitVal p N (flagGamma p (flagJump p f)) m
          ≤ topVal p N (flagGamma p (flagJump p f)) := by
        rw [topVal, digitVal]
        refine Finset.sum_le_sum fun b _ => Nat.mul_le_mul_right _ ?_
        have := digit_lt (p := p) hp.out.pos b m
        omega
      omega

theorem levelCount_large_padic {f u : MvPowerSeries (Fin n) ℤ_[p]} (hfu : f * u = 1) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : topVal p (rankF p f) (flagGamma p (flagJump p f)) < k) :
    levelCount p (frob p) f k + 1 = p ^ rankF p f := by
  rw [levelCount_eq_flagValue_padic p hfu hk1, flagValue_large p f hk]

theorem levelCount_large_int {f u : MvPowerSeries (Fin n) ℤ} (hfu : f * u = 1) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : topVal p (rankF p f) (flagGamma p (flagJump p f)) < k) :
    levelCount p (frob p) f k + 1 = p ^ rankF p f := by
  rw [levelCount_eq_flagValue_int p hfu hk1, flagValue_large p f hk]

end Large

namespace Dir

section DirFlag

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ} {q : Fin n → ℕ}
variable (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)

/-- **R-084 for units supported on finitely many primes, every flag, over `ℤ`.** -/
theorem levelCount_dir_smooth_int {f : ArithmeticFunction ℤ} (hf : IsUnit f)
    (hsupp : ∀ N, f N ≠ 0 → ∃ e, smoothNum q e = N) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) f k + 1 = flagValue p (res hq hinj f) k := by
  rw [levelCount_eq_res_of_smooth p hq hinj (int_pow_sub p) hf hsupp hk]
  obtain ⟨v, hv⟩ := hf.map (res hq hinj)
  exact levelCount_eq_flagValue_int p (u := ↑v⁻¹) (by rw [← hv]; exact v.mul_inv) hk

/-- The same over `ℤ_[p]`. -/
theorem levelCount_dir_smooth_padic {f : ArithmeticFunction ℤ_[p]} (hf : IsUnit f)
    (hsupp : ∀ N, f N ≠ 0 → ∃ e, smoothNum q e = N) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) f k + 1 = flagValue p (res hq hinj f) k := by
  rw [levelCount_eq_res_of_smooth p hq hinj (padicInt_pow_sub p) hf hsupp hk]
  obtain ⟨v, hv⟩ := hf.map (res hq hinj)
  exact levelCount_eq_flagValue_padic p (u := ↑v⁻¹) (by rw [← hv]; exact v.mul_inv) hk

/-- **Lower half of R-084 for every unit of the Dirichlet ring over `ℤ`**: for every finite set of
primes `q_1..q_n`, R-083's value for the restriction is at most `L_f + 1`. -/
theorem flagValue_res_le_int {f : ArithmeticFunction ℤ} (hf : IsUnit f) {k : ℕ} (hk : 1 ≤ k) :
    flagValue p (res hq hinj f) k ≤ levelCount p (Ep p) f k + 1 := by
  have hle := levelCount_map_le (res hq hinj) (σ := Ep p) (σ' := frob p)
    (fun a => res_Ep hq hinj p a) (hasLevel_kempner p (int_pow_sub p) f hf hk)
  obtain ⟨v, hv⟩ := hf.map (res hq hinj)
  have heq := levelCount_eq_flagValue_int p (f := res hq hinj f) (u := ↑v⁻¹)
    (by rw [← hv]; exact v.mul_inv) hk
  omega

/-- The same over `ℤ_[p]`. -/
theorem flagValue_res_le_padic {f : ArithmeticFunction ℤ_[p]} (hf : IsUnit f) {k : ℕ}
    (hk : 1 ≤ k) : flagValue p (res hq hinj f) k ≤ levelCount p (Ep p) f k + 1 := by
  have hle := levelCount_map_le (res hq hinj) (σ := Ep p) (σ' := frob p)
    (fun a => res_Ep hq hinj p a) (hasLevel_kempner p (padicInt_pow_sub p) f hf hk)
  obtain ⟨v, hv⟩ := hf.map (res hq hinj)
  have heq := levelCount_eq_flagValue_padic p (f := res hq hinj f) (u := ↑v⁻¹)
    (by rw [← hv]; exact v.mul_inv) hk
  omega

end DirFlag

end Dir

end FrobLevel
