module

/-
Run r25, seat L7: corollaries of R-084 (DirFlag.lean) and the reduction to finitely many
variables over any coefficient ring with `R / p^k R` finite.

* `Dir.levelCount_finRank_int`, `_padic`: when `r_f = r` is finite,
  `L_f + 1 = min(p^r, min{m : v_p(m!) + ∑_{j<r} (d(j+1)-d(j)) ⌊m/p^j⌋ ≥ k})` (R-083's shape).
* `Dir.levelCount_infRank_int`, `_padic`: when `r_f` is infinite, the same without the cap:
  `L_f + 1 = min{m : v_p(m!) + ∑_{j ≤ m} (d(j+1)-d(j)) ⌊m/p^j⌋ ≥ k}`.
* `Dir.levelCount_rank_zero_int`, `_padic`: `r_f = 0` gives `L_f = 0`.
* `Dir.levelCount_inv_dir_int`, `_padic`: `L_f = L_(1/f)`.
* `Dir.levelCount_eq_max_res_general`: over ANY commutative ring `R` with `R / p^k R` finite
  (for instance `ℤ[χ]` or its completions), for every `f` with a level identity,
  `L_f = max_q L_(res_q f)`, the max over finite families of primes, attained. This reduces the
  Dirichlet-ring clauses of R-084 (`Z[χ]`) and R-085 (T1, T2) to finitely many variables.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Flag
public import Frobenius.Levels.DirBase
public import Frobenius.Levels.DirTransfer
public import Frobenius.Levels.Cap
public import Frobenius.Levels.ThmF
public import Frobenius.Levels.Padic
public import Frobenius.Levels.Assemble
public import Frobenius.Levels.Compact
public import Frobenius.Levels.Sup
public import Frobenius.Levels.DirFlag
public import Frobenius.Levels.DirMain

@[expose] public section

namespace FrobLevel

namespace Dir

open MvPowerSeries

section Shapes

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R]

/-- The Dirichlet value in R-083's shape when `r_f = r` is finite. -/
theorem dirFlagValue_finRank (f : ArithmeticFunction R) (k : ℕ) {r : ℕ}
    (hr : dRank p f Set.univ = r) :
    dirFlagValue p f k = sInf {m | p ^ r ≤ m ∨ k ≤ padicValNat p m.factorial +
      ∑ j ∈ Finset.range r,
        (dFlag p f Set.univ (j + 1) - dFlag p f Set.univ j) * (m / p ^ j)} := by
  unfold dirFlagValue dFlagValue
  congr 1
  ext m
  simp only [Set.mem_setOf_eq, hr, Nat.cast_inj, exists_eq_left']
  rw [sum_range_eq_filter _ r m]
  intro j hj
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hj (Nat.lt_pow_self hp.out.one_lt).le), mul_zero]

/-- The Dirichlet value without the cap when `r_f` is infinite. -/
theorem dirFlagValue_infRank (f : ArithmeticFunction R) (k : ℕ)
    (hr : Cardinal.aleph0 ≤ dRank p f Set.univ) :
    dirFlagValue p f k = sInf {m | k ≤ padicValNat p m.factorial +
      ∑ j ∈ Finset.range (m + 1),
        (dFlag p f Set.univ (j + 1) - dFlag p f Set.univ j) * (m / p ^ j)} := by
  unfold dirFlagValue dFlagValue
  congr 1
  ext m
  simp only [Set.mem_setOf_eq]
  have hno : ¬ ∃ r : ℕ, dRank p f Set.univ = r ∧ p ^ r ≤ m := by
    rintro ⟨r, hr', _⟩
    rw [hr'] at hr
    exact absurd hr (not_le.2 (Cardinal.natCast_lt_aleph0))
  have hfilt : (Finset.range (m + 1)).filter
      (fun j : ℕ => ((j : ℕ) : Cardinal) < dRank p f Set.univ) = Finset.range (m + 1) :=
    Finset.filter_true_of_mem fun j _ => lt_of_lt_of_le Cardinal.natCast_lt_aleph0 hr
  rw [hfilt]
  exact ⟨fun h => h.resolve_left hno, Or.inr⟩

theorem dirFlagValue_rank_zero (f : ArithmeticFunction R) {k : ℕ} (hk : 1 ≤ k)
    (hr : dRank p f Set.univ = 0) : dirFlagValue p f k = 1 := by
  rw [dirFlagValue_finRank p f k (r := 0) (by rw [hr, Nat.cast_zero])]
  apply le_antisymm
  · exact Nat.sInf_le (show (1 : ℕ) ∈ _ from Or.inl (by simp))
  · rw [Nat.one_le_iff_ne_zero]
    intro h
    rcases Nat.sInf_eq_zero.1 h with h0 | h0
    · rcases h0 with h0 | h0
      · simp at h0
      · simp at h0; omega
    · exact (Set.eq_empty_iff_forall_notMem.1 h0) 1 (Or.inl (by simp))

end Shapes

section Cor

variable (p : ℕ) [hp : Fact p.Prime]

/-- **R-084 over `ℤ`, hypothesis as in the note: `f(1)` a unit (`f(1) = ±1`).** -/
theorem levelCount_eq_dirFlagValue_int' {f : ArithmeticFunction ℤ} (h1 : IsUnit (f 1)) {k : ℕ}
    (hk : 1 ≤ k) : levelCount p (Ep p) f k + 1 = dirFlagValue p f k :=
  levelCount_eq_dirFlagValue_int p (ArithmeticFunction.isUnit_iff_isUnit_apply_one.2 h1) hk

/-- **R-084 over `ℤ_[p]`, hypothesis as in the note: `f(1)` a unit.** -/
theorem levelCount_eq_dirFlagValue_padic' {f : ArithmeticFunction ℤ_[p]} (h1 : IsUnit (f 1))
    {k : ℕ} (hk : 1 ≤ k) : levelCount p (Ep p) f k + 1 = dirFlagValue p f k :=
  levelCount_eq_dirFlagValue_padic p (ArithmeticFunction.isUnit_iff_isUnit_apply_one.2 h1) hk

/-- **R-084, finite rank, over `ℤ`.** -/
theorem levelCount_finRank_int {f : ArithmeticFunction ℤ} (hf : IsUnit f) {k : ℕ} (hk : 1 ≤ k)
    {r : ℕ} (hr : dRank p f Set.univ = r) :
    levelCount p (Ep p) f k + 1 = sInf {m | p ^ r ≤ m ∨ k ≤ padicValNat p m.factorial +
      ∑ j ∈ Finset.range r,
        (dFlag p f Set.univ (j + 1) - dFlag p f Set.univ j) * (m / p ^ j)} := by
  rw [levelCount_eq_dirFlagValue_int p hf hk, dirFlagValue_finRank p f k hr]

/-- **R-084, finite rank, over `ℤ_[p]`.** -/
theorem levelCount_finRank_padic {f : ArithmeticFunction ℤ_[p]} (hf : IsUnit f) {k : ℕ}
    (hk : 1 ≤ k) {r : ℕ} (hr : dRank p f Set.univ = r) :
    levelCount p (Ep p) f k + 1 = sInf {m | p ^ r ≤ m ∨ k ≤ padicValNat p m.factorial +
      ∑ j ∈ Finset.range r,
        (dFlag p f Set.univ (j + 1) - dFlag p f Set.univ j) * (m / p ^ j)} := by
  rw [levelCount_eq_dirFlagValue_padic p hf hk, dirFlagValue_finRank p f k hr]

/-- **R-084, infinite rank, over `ℤ`**: the formula without the cap. -/
theorem levelCount_infRank_int {f : ArithmeticFunction ℤ} (hf : IsUnit f) {k : ℕ} (hk : 1 ≤ k)
    (hr : Cardinal.aleph0 ≤ dRank p f Set.univ) :
    levelCount p (Ep p) f k + 1 = sInf {m | k ≤ padicValNat p m.factorial +
      ∑ j ∈ Finset.range (m + 1),
        (dFlag p f Set.univ (j + 1) - dFlag p f Set.univ j) * (m / p ^ j)} := by
  rw [levelCount_eq_dirFlagValue_int p hf hk, dirFlagValue_infRank p f k hr]

/-- **R-084, infinite rank, over `ℤ_[p]`.** -/
theorem levelCount_infRank_padic {f : ArithmeticFunction ℤ_[p]} (hf : IsUnit f) {k : ℕ}
    (hk : 1 ≤ k) (hr : Cardinal.aleph0 ≤ dRank p f Set.univ) :
    levelCount p (Ep p) f k + 1 = sInf {m | k ≤ padicValNat p m.factorial +
      ∑ j ∈ Finset.range (m + 1),
        (dFlag p f Set.univ (j + 1) - dFlag p f Set.univ j) * (m / p ^ j)} := by
  rw [levelCount_eq_dirFlagValue_padic p hf hk, dirFlagValue_infRank p f k hr]

theorem levelCount_rank_zero_int {f : ArithmeticFunction ℤ} (hf : IsUnit f) {k : ℕ} (hk : 1 ≤ k)
    (hr : dRank p f Set.univ = 0) : levelCount p (Ep p) f k = 0 := by
  have := levelCount_eq_dirFlagValue_int p hf hk
  rw [dirFlagValue_rank_zero p f hk hr] at this
  omega

theorem levelCount_rank_zero_padic {f : ArithmeticFunction ℤ_[p]} (hf : IsUnit f) {k : ℕ}
    (hk : 1 ≤ k) (hr : dRank p f Set.univ = 0) : levelCount p (Ep p) f k = 0 := by
  have := levelCount_eq_dirFlagValue_padic p hf hk
  rw [dirFlagValue_rank_zero p f hk hr] at this
  omega

/-- `L_f = L_(1/f)` in the Dirichlet ring over `ℤ`. -/
theorem levelCount_inv_dir_int {f u : ArithmeticFunction ℤ} (hfu : f * u = 1) {k : ℕ}
    (hk : 1 ≤ k) : levelCount p (Ep p) u k = levelCount p (Ep p) f k := by
  have hf : IsUnit f := ⟨⟨f, u, hfu, by rw [mul_comm]; exact hfu⟩, rfl⟩
  have hu : IsUnit u := ⟨⟨u, f, by rw [mul_comm]; exact hfu, hfu⟩, rfl⟩
  have hres : ∀ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      flagValue p (res hq hinj u) k = flagValue p (res hq hinj f) k := fun n q hq hinj =>
    flagValue_inv (p := p) (by rw [← map_mul, hfu, map_one]) k
  have h1 := levelCount_le_of_flagValue_res_int p hu hk ∅ (by simp) (M := levelCount p (Ep p) f k + 1)
    fun n q hq hinj _ => (hres n q hq hinj).le.trans (flagValue_res_le_int p hq hinj hf hk)
  have h2 := levelCount_le_of_flagValue_res_int p hf hk ∅ (by simp) (M := levelCount p (Ep p) u k + 1)
    fun n q hq hinj _ => (hres n q hq hinj).ge.trans (flagValue_res_le_int p hq hinj hu hk)
  omega

/-- `L_f = L_(1/f)` in the Dirichlet ring over `ℤ_[p]`. -/
theorem levelCount_inv_dir_padic {f u : ArithmeticFunction ℤ_[p]} (hfu : f * u = 1) {k : ℕ}
    (hk : 1 ≤ k) : levelCount p (Ep p) u k = levelCount p (Ep p) f k := by
  have hf : IsUnit f := ⟨⟨f, u, hfu, by rw [mul_comm]; exact hfu⟩, rfl⟩
  have hu : IsUnit u := ⟨⟨u, f, by rw [mul_comm]; exact hfu, hfu⟩, rfl⟩
  have hres : ∀ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      flagValue p (res hq hinj u) k = flagValue p (res hq hinj f) k := fun n q hq hinj =>
    flagValue_inv (p := p) (by rw [← map_mul, hfu, map_one]) k
  have h1 := levelCount_le_of_flagValue_res_padic p hu hk ∅ (by simp)
    (M := levelCount p (Ep p) f k + 1)
    fun n q hq hinj _ => (hres n q hq hinj).le.trans (flagValue_res_le_padic p hq hinj hf hk)
  have h2 := levelCount_le_of_flagValue_res_padic p hf hk ∅ (by simp)
    (M := levelCount p (Ep p) u k + 1)
    fun n q hq hinj _ => (hres n q hq hinj).ge.trans (flagValue_res_le_padic p hq hinj hu hk)
  omega

/-- Instance: for `f = μ` the Dirichlet flag value is the Kempner value `S(p^k)` (from the main
theorem and L3's `levelCount_moebius_int`; note Corollary `cor:named` (a)). -/
theorem dirFlagValue_moebius_int {k : ℕ} (hk : 1 ≤ k) :
    dirFlagValue p (ArithmeticFunction.moebius : ArithmeticFunction ℤ) k = kempner p k := by
  have h : (ArithmeticFunction.moebius : ArithmeticFunction ℤ) * ArithmeticFunction.zeta = 1 :=
    ArithmeticFunction.moebius_mul_coe_zeta
  have hu : IsUnit (ArithmeticFunction.moebius : ArithmeticFunction ℤ) :=
    ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩
  rw [← levelCount_eq_dirFlagValue_int p hu hk, levelCount_moebius_int p hk]

end Cor

section General

/-- The lower half for any coefficient ring. -/
theorem levelCount_res_le_general {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] {k : ℕ}
    {f : ArithmeticFunction R} {L0 : ℕ} (hex : HasLevel p (Ep p) f k L0) {n : ℕ}
    {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q) :
    levelCount p (frob p) (res hq hinj f) k ≤ levelCount p (Ep p) f k := by
  have := levelCount_map_le (res hq hinj) (σ := Ep p) (σ' := frob p)
    (fun a => res_Ep hq hinj p a) hex
  exact this

/-- **Reduction to finitely many variables over any coefficient ring with `R / p^k R` finite.**
For every `f` with some level identity in the Dirichlet ring (with `E_p`), `L_f(p, k)` is the
largest level count of a restriction `res_q f` to finitely many primes (in `R[[x_1..x_n]]` with
the standard lift), and the largest is attained. -/
theorem levelCount_eq_max_res_general {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]
    {k : ℕ} [Finite (R ⧸ Ideal.span {(p : R) ^ k})] {f : ArithmeticFunction R} {L0 : ℕ}
    (hex : HasLevel p (Ep p) f k L0) :
    (∀ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      levelCount p (frob p) (res hq hinj f) k ≤ levelCount p (Ep p) f k) ∧
    ∃ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      levelCount p (Ep p) f k = levelCount p (frob p) (res hq hinj f) k := by
  have hlow : ∀ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      levelCount p (frob p) (res hq hinj f) k ≤ levelCount p (Ep p) f k :=
    fun n q hq hinj => levelCount_res_le_general p hex hq hinj
  refine ⟨hlow, ?_⟩
  let V : Set ℕ := {v | ∃ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q), v = levelCount p (frob p) (res hq hinj f) k}
  have hbdd : BddAbove V := ⟨levelCount p (Ep p) f k, by
    rintro v ⟨n, q, hq, hinj, rfl⟩; exact hlow n q hq hinj⟩
  have hne : V.Nonempty := ⟨_, 0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, rfl⟩
  obtain ⟨n, q, hq, hinj, hM⟩ := Nat.sSup_mem hne hbdd
  refine ⟨n, q, hq, hinj, le_antisymm ?_ (hlow n q hq hinj)⟩
  rw [← hM]
  apply levelCount_le
  apply hasLevel_of_res p (Ideal.Quotient.mk (Ideal.span {(p : R) ^ k})) Ideal.Quotient.mk_surjective
    (fun a ha => Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 ha))
    (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)) f
  intro N
  have hT : ∀ t ∈ (∅ : Finset ℕ), t.Prime := by simp
  refine ⟨_, enum (coverSet N ∅), coverSet_prime hT, enum_injective _,
    coverSet_smooth N ∅ hT, ?_⟩
  have h0 := HasLevel.map (res (coverSet_prime hT) (enum_injective (coverSet N ∅)))
    (σ := Ep p) (σ' := frob p) (fun a => res_Ep _ _ p a) hex
  have h1 := hasLevel_levelCount h0
  exact h1.mono (le_csSup hbdd ⟨_, _, _, _, rfl⟩)

end General

end Dir

end FrobLevel
