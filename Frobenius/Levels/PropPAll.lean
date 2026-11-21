module

/-
Run r25, seat L6: **Proposition P** (ledger R-082 (3), note Corollary `cor:special` (e)) for
EVERY `a, b`, as a corollary of R-083 (L5's `levelCount_eq_flagValue_int`, `_padic`).

For `u = 1 + p ^ a x + p ^ b y` (L2's `uP p a b`) over `ℤ` or `ℤ_[p]`:
* `flag_uP`: `U_d` has rank `[a ≤ d] + [b ≤ d]`, so the flag is `(min a b, max a b)`, `r = 2`;
* `flagGamma_uP`: `γ = (min a b, (p - 1) min a b + max a b + 1)`;
* `levelCount_propP_all_int`, `_padic`: for `f = 1/u`, `k ≥ 1`,
  `L_f + 1 = min(p ^ 2, min {m : e_0(m) γ_0 + e_1(m) γ_1 ≥ k})` with that `γ`;
* `levelCount_propP_le_*` (`a ≤ b`, the ledger's `γ = (a, (p-1)a + b + 1)`; re-derives L2's
  `levelCount_propP` for `a < b`), `levelCount_propP_eq_*` (`a = b`, `γ = (a, p a + 1)`: this is
  exactly L2's open statement `open_propP_equal`);
* `propP_ledger_needs_le`: for `a > b` the ledger's `γ = (a, (p-1)a + b + 1)` is wrong:
  `p = 2`, `u = 1 + 4x + 2y`, `k = 2`: `L_f + 1 = 2`, the ledger's form gives `1`.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.Digit
public import Frobenius.Levels.PropP
public import Frobenius.Levels.Flag
public import Frobenius.Levels.Cap
public import Frobenius.Levels.Padic
public import Frobenius.Levels.Assemble
public import Frobenius.Levels.FlagCalc
public import Frobenius.Levels.PolyFlag

@[expose] public section

namespace FrobLevel

open MvPowerSeries

section PropPAll

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R]

/-- The exponents `0, x, y`. -/
noncomputable def exP : Fin 3 → (Fin 2 →₀ ℕ) := ![0, Finsupp.single 0 1, Finsupp.single 1 1]

theorem exP_zero : exP 0 = 0 := rfl
theorem exP_one : exP 1 = Finsupp.single 0 1 := rfl
theorem exP_two : exP 2 = Finsupp.single 1 1 := rfl

theorem fin3_cases (t : Fin 3) : t = 0 ∨ t = 1 ∨ t = 2 := by fin_cases t <;> simp

theorem exP_mem (t : Fin 3) : exP t ∈ digitExps p 2 := by
  fin_cases t
  · rw [mem_digitExps]; intro i; simp [exP, hp.out.pos]
  · exact single_mem_digitExps p 0
  · exact single_mem_digitExps p 1

theorem exP_inj : Function.Injective exP := by
  intro s t h
  fin_cases s <;> fin_cases t <;> simp_all [exP, Finsupp.single_eq_single_iff, eq_comm]

theorem uP_eq_powPoly (a b : ℕ) : uP p (R := R) a b = powPoly p exP ![0, a, b] := by
  rw [powPoly, Fin.sum_univ_three, uP]
  simp only [exP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, pow_zero, Matrix.tail_cons]
  rw [monomial_zero_eq_C_apply, map_one, natCast_pow_eq_C, natCast_pow_eq_C, X_def, X_def,
    ← monomial_zero_eq_C_apply, ← monomial_zero_eq_C_apply, monomial_mul_monomial,
    monomial_mul_monomial, zero_add, zero_add, mul_one, mul_one, add_assoc]

variable [IsDomain R]

theorem finrank_depthSpace_uP (hp0 : (p : R) ≠ 0) (hpu : ¬ IsUnit (p : R)) (a b d : ℕ) :
    Module.finrank (ZMod p) (depthSpace p (uP p (R := R) a b) d)
      = (if a ≤ d then 1 else 0) + (if b ≤ d then 1 else 0) := by
  rw [uP_eq_powPoly, depthSpace_powPoly hp0 hpu (exP_mem p) exP_inj]
  rw [finrank_span_eq_card (Tf := Finset.univ.filter (fun i : Fin 2 => ![a, b] i ≤ d))]
  · rw [Finset.card_filter, Fin.sum_univ_two]
    by_cases ha : a ≤ d <;> by_cases hb : b ≤ d <;> simp [ha, hb]
  · rintro _ ⟨t, ⟨hne, hle⟩, rfl⟩
    rcases fin3_cases t with rfl | rfl | rfl
    · exact absurd rfl hne
    · beta_reduce; rw [exP_one, classVec_single]
      exact Submodule.subset_span ⟨0, by simpa using hle, rfl⟩
    · beta_reduce; rw [exP_two, classVec_single]
      exact Submodule.subset_span ⟨1, by simpa using hle, rfl⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    fin_cases i
    · refine Submodule.subset_span ⟨1, ⟨by simp [exP], by simpa using hi⟩, ?_⟩
      show classVec p (exP 1) = Pi.single 0 1
      rw [exP_one, classVec_single]
    · refine Submodule.subset_span ⟨2, ⟨by simp [exP], by simpa using hi⟩, ?_⟩
      show classVec p (exP 2) = Pi.single 1 1
      rw [exP_two, classVec_single]

theorem rankF_uP (hp0 : (p : R) ≠ 0) (a b : ℕ) : rankF p (uP p (R := R) a b) = 2 := by
  rw [rankF, uP_eq_powPoly, fullSpace_powPoly hp0 (exP_mem p) exP_inj]
  rw [finrank_span_eq_card (Tf := Finset.univ)]
  · rfl
  · rintro _ ⟨t, hne, rfl⟩
    rcases fin3_cases t with rfl | rfl | rfl
    · exact absurd rfl hne
    · beta_reduce; rw [exP_one, classVec_single]
      exact Submodule.subset_span ⟨0, by simp, rfl⟩
    · beta_reduce; rw [exP_two, classVec_single]
      exact Submodule.subset_span ⟨1, by simp, rfl⟩
  · intro i _
    fin_cases i
    · refine Submodule.subset_span ⟨1, by simp [exP], ?_⟩
      show classVec p (exP 1) = Pi.single 0 1
      rw [exP_one, classVec_single]
    · refine Submodule.subset_span ⟨2, by simp [exP], ?_⟩
      show classVec p (exP 2) = Pi.single 1 1
      rw [exP_two, classVec_single]

/-- **The depth flag of `1 + p ^ a x + p ^ b y`** is `(min a b, max a b)`, `r = 2`. -/
theorem flag_uP (hp0 : (p : R) ≠ 0) (hpu : ¬ IsUnit (p : R)) (a b : ℕ) :
    rankF p (uP p (R := R) a b) = 2 ∧ depthFlag p (uP p (R := R) a b) 1 = min a b ∧
      depthFlag p (uP p (R := R) a b) 2 = max a b := by
  refine ⟨rankF_uP p hp0 a b, ?_, ?_⟩
  · rw [depthFlag, if_neg one_ne_zero]
    refine sInf_eq_of_iff fun d => ?_
    rw [finrank_depthSpace_uP p hp0 hpu]
    split_ifs <;> omega
  · rw [depthFlag, if_neg two_ne_zero]
    refine sInf_eq_of_iff fun d => ?_
    rw [finrank_depthSpace_uP p hp0 hpu]
    split_ifs <;> omega

/-- **`γ = (min a b, (p - 1) min a b + max a b + 1)`** (R-083's recursion on the flag). -/
theorem flagGamma_uP (hp0 : (p : R) ≠ 0) (hpu : ¬ IsUnit (p : R)) (a b : ℕ) :
    flagGamma p (flagJump p (uP p (R := R) a b)) 0 = min a b ∧
      flagGamma p (flagJump p (uP p (R := R) a b)) 1 = (p - 1) * min a b + max a b + 1 := by
  obtain ⟨_, h1, h2⟩ := flag_uP p hp0 hpu a b
  have h0 : depthFlag p (uP p (R := R) a b) 0 = 0 := by simp [depthFlag]
  have hj0 : flagJump p (uP p (R := R) a b) 0 = min a b := by
    show depthFlag p _ (0 + 1) - depthFlag p _ 0 = _
    rw [h1, h0, Nat.sub_zero]
  have hj1 : flagJump p (uP p (R := R) a b) 1 = max a b - min a b := by
    show depthFlag p _ (1 + 1) - depthFlag p _ 1 = _
    rw [h2, h1]
  refine ⟨by rw [flagGamma_zero, hj0], ?_⟩
  rw [flagGamma_succ, flagGamma_zero, hj0, hj1]
  have hp1 := hp.out.one_lt
  have hmul : (p - 1) * min a b + min a b = p * min a b := by
    rw [Nat.sub_one_mul]
    have := Nat.le_mul_of_pos_left (min a b) (show 0 < p by omega)
    omega
  have hle : min a b ≤ max a b := min_le_max
  omega

/-- R-083's value for `uP p a b` in digit form, every `a, b`. -/
theorem flagValue_uP (hp0 : (p : R) ≠ 0) (hpu : ¬ IsUnit (p : R)) (a b k : ℕ) :
    flagValue p (uP p (R := R) a b) k = sInf {m | p ^ 2 ≤ m ∨
      k ≤ digit p 0 m * min a b + digit p 1 m * ((p - 1) * min a b + max a b + 1)} := by
  obtain ⟨hr, _, _⟩ := flag_uP p hp0 hpu a b
  obtain ⟨g0, g1⟩ := flagGamma_uP p hp0 hpu a b
  unfold flagValue
  rw [hr, ← sInf_digit_eq_flag p (flagJump p (uP p (R := R) a b))]
  congr 1
  ext m
  simp only [Set.mem_ofPred_eq, digitVal, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    g0, g1]

end PropPAll

section PropPLevel

variable (p : ℕ) [hp : Fact p.Prime]

theorem int_natCast_ne_zero : ((p : ℕ) : ℤ) ≠ 0 := by
  exact_mod_cast hp.out.ne_zero

theorem padicInt_natCast_ne_zero : ((p : ℕ) : ℤ_[p]) ≠ 0 := by
  exact_mod_cast hp.out.ne_zero

/-- **Proposition P for every `a, b`, over `ℤ`.** -/
theorem levelCount_propP_all_int {a b : ℕ} {f : MvPowerSeries (Fin 2) ℤ}
    (hfu : f * uP p a b = 1) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) f k + 1 = sInf {m | p ^ 2 ≤ m ∨
      k ≤ digit p 0 m * min a b + digit p 1 m * ((p - 1) * min a b + max a b + 1)} := by
  rw [levelCount_eq_flagValue_int p hfu hk, ← flagValue_inv hfu,
    flagValue_uP p (int_natCast_ne_zero p) (int_not_isUnit p)]

/-- **Proposition P for every `a, b`, over `ℤ_[p]`** (the ledger's setting). -/
theorem levelCount_propP_all_padic {a b : ℕ} {f : MvPowerSeries (Fin 2) ℤ_[p]}
    (hfu : f * uP p a b = 1) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) f k + 1 = sInf {m | p ^ 2 ≤ m ∨
      k ≤ digit p 0 m * min a b + digit p 1 m * ((p - 1) * min a b + max a b + 1)} := by
  rw [levelCount_eq_flagValue_padic p hfu hk, ← flagValue_inv hfu,
    flagValue_uP p (padicInt_natCast_ne_zero p) (padicInt_not_isUnit p)]

/-- `a ≤ b`: the ledger's `γ = (a, (p - 1) a + b + 1)` (re-derives L2's `levelCount_propP`). -/
theorem levelCount_propP_le_padic {a b : ℕ} (hab : a ≤ b) {f : MvPowerSeries (Fin 2) ℤ_[p]}
    (hfu : f * uP p a b = 1) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) f k + 1
      = sInf {m | p ^ 2 ≤ m ∨ k ≤ digit p 0 m * a + digit p 1 m * ((p - 1) * a + b + 1)} := by
  rw [levelCount_propP_all_padic p hfu hk, min_eq_left hab, max_eq_right hab]

theorem levelCount_propP_le_int {a b : ℕ} (hab : a ≤ b) {f : MvPowerSeries (Fin 2) ℤ}
    (hfu : f * uP p a b = 1) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) f k + 1
      = sInf {m | p ^ 2 ≤ m ∨ k ≤ digit p 0 m * a + digit p 1 m * ((p - 1) * a + b + 1)} := by
  rw [levelCount_propP_all_int p hfu hk, min_eq_left hab, max_eq_right hab]

/-- **Proposition P with `a = b`** (`γ = (a, p a + 1)`): exactly the statement of L2's
`open_propP_equal`, now proved. -/
theorem levelCount_propP_eq_padic {a : ℕ} {f : MvPowerSeries (Fin 2) ℤ_[p]}
    (hfu : f * uP p a a = 1) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) f k + 1
      = sInf {m | p ^ 2 ≤ m ∨ k ≤ digit p 0 m * a + digit p 1 m * (p * a + 1)} := by
  rw [levelCount_propP_le_padic p le_rfl hfu hk]
  have : (p - 1) * a + a + 1 = p * a + 1 := by
    have hp1 := hp.out.one_lt
    rw [Nat.sub_one_mul]
    have := Nat.le_mul_of_pos_left a (show 0 < p by omega)
    omega
  rw [this]

theorem levelCount_propP_eq_int {a : ℕ} {f : MvPowerSeries (Fin 2) ℤ}
    (hfu : f * uP p a a = 1) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) f k + 1
      = sInf {m | p ^ 2 ≤ m ∨ k ≤ digit p 0 m * a + digit p 1 m * (p * a + 1)} := by
  rw [levelCount_propP_le_int p le_rfl hfu hk]
  have : (p - 1) * a + a + 1 = p * a + 1 := by
    have hp1 := hp.out.one_lt
    rw [Nat.sub_one_mul]
    have := Nat.le_mul_of_pos_left a (show 0 < p by omega)
    omega
  rw [this]

end PropPLevel

section Counter

theorem sInf_eq_of_mem {S : Set ℕ} {c : ℕ} (h1 : c ∈ S) (h2 : ∀ m < c, m ∉ S) : sInf S = c := by
  refine le_antisymm (Nat.sInf_le h1) ?_
  by_contra h
  push Not at h
  exact h2 _ h (Nat.sInf_mem ⟨c, h1⟩)

/-- **The ledger's Proposition P needs `a ≤ b`.** For `p = 2`, `u = 1 + 4x + 2y`
(`a = 2 > b = 1`) and `k = 2`: `L_f + 1 = 2`, while the ledger's `γ = (a, (p-1)a + b + 1) = (2, 4)`
would give `1`. -/
theorem propP_ledger_needs_le {f : MvPowerSeries (Fin 2) ℤ_[2]} (hfu : f * uP 2 2 1 = 1) :
    levelCount 2 (frob 2) f 2 + 1 = 2 ∧
      sInf {m | 2 ^ 2 ≤ m ∨ 2 ≤ digit 2 0 m * 2 + digit 2 1 m * ((2 - 1) * 2 + 1 + 1)} = 1 := by
  refine ⟨?_, ?_⟩
  · rw [levelCount_propP_all_padic 2 hfu (k := 2) (by norm_num)]
    refine sInf_eq_of_mem ?_ ?_
    · right; decide
    · intro m hm
      interval_cases m <;> decide
  · refine sInf_eq_of_mem ?_ ?_
    · right; decide
    · intro m hm
      interval_cases m; decide

end Counter

end FrobLevel
