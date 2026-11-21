module

/-
Run r25, seat L3: exact level counts in the Dirichlet ring (ledger R-084, the all-zero flag case,
with the prime count of the note's Remark "a lower bound without multiplicativity").

For `R = ℤ` or `R = ℤ_[p]`, `f` a unit of the Dirichlet ring (`f(1)` a unit), `p` prime, `k ≥ 1`:

* `levelCount_add_one_le_kempner`: `L_f(p, k) + 1 ≤ S(p ^ k)` (any `R` with `p ∣ a ^ p - a`);
* `min_le_levelCount_int`, `_padic`: if `q_0, ..., q_(n-1)` are distinct primes with
  `p ∤ f(q_i)`, then `min(p ^ n, S(p ^ k)) ≤ L_f(p, k) + 1` (no multiplicativity);
* `levelCount_eq_kempner_int`, `_padic`: equality `L_f + 1 = S(p ^ k)` once `S(p ^ k) ≤ p ^ n`;
* `..._of_infinite`: equality for every `k ≥ 1` when infinitely many primes have `p ∤ f(q)`;
* named cases: `μ`, `ζ`, Liouville `λ`, `μ²` for every `p`; `d_2 = ζ * ζ` and `μ * μ` for odd `p`.

Lower-bound route: restrict to `{q_i}`-smooth arguments (DirBase.lean, `res`, a ring hom commuting
with the lifts), then seat L1's power-series theorem `levelCount_eq_of_fullRank_int` / `_padic`.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Lower
public import Frobenius.Levels.LowerPadic
public import Frobenius.Levels.DirBase

@[expose] public section

namespace FrobLevel

namespace Dir

open MvPowerSeries

section Primes

variable {R : Type*} [CommRing R]

instance instNontrivialArith [Nontrivial R] : Nontrivial (ArithmeticFunction R) :=
  ⟨⟨0, 1, fun h => by
    have := congrArg (fun f : ArithmeticFunction R => f 1) h
    simp at this⟩⟩

/-- `(f * g)(q) = f(1) g(q) + f(q) g(1)` at a prime `q`. -/
theorem mul_apply_prime (f g : ArithmeticFunction R) {q : ℕ} (hq : q.Prime) :
    (f * g) q = f 1 * g q + f q * g 1 := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b),
    hq.divisors, Finset.sum_pair hq.one_lt.ne, Nat.div_one, Nat.div_self hq.pos]

/-- At a prime `q`, the inverse `u` of `f` has `u(q) ≡ 0 (mod p)` only if `f(q) ≡ 0 (mod p)`. -/
theorem not_dvd_inv_apply_prime {p : ℕ} {f u : ArithmeticFunction R} (hfu : f * u = 1) {q : ℕ}
    (hq : q.Prime) (hf : ¬ (p : R) ∣ f q) : ¬ (p : R) ∣ u q := by
  have h1 : f 1 * u q + f q * u 1 = 0 := by
    rw [← mul_apply_prime f u hq, hfu, ArithmeticFunction.one_apply_ne hq.one_lt.ne']
  have h2 : f 1 * u 1 = 1 := by
    rw [← ArithmeticFunction.mul_apply_one, hfu, ArithmeticFunction.one_one]
  have e : f q = -(f 1 * f 1) * u q := by linear_combination (f 1) * h1 - (f q) * h2
  intro hd
  exact hf (e ▸ Dvd.dvd.mul_left hd _)

/-- The restriction of `u` has full rank (`ρ = n`) as soon as `p ∤ u(q_i)` for every `i`. -/
theorem fullRank_res {p n : ℕ} {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q) (u : ArithmeticFunction R)
    (hu : ∀ i, ¬ (p : R) ∣ u (q i)) : FullRank p (res hq hinj u) := by
  intro h hlt hne
  obtain ⟨i, hi⟩ := hne
  refine ⟨Finsupp.single i 1, ?_, ?_⟩
  · rw [Finset.sum_eq_single i]
    · rw [Finsupp.single_eq_same, mul_one]
      exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hi) (hlt i)
    · intro j _ hj; rw [Finsupp.single_apply, if_neg (Ne.symm hj), mul_zero]
    · intro h'; exact absurd (Finset.mem_univ i) h'
  · rw [coeff_res, smoothNum_single]; exact hu i

/-- `n` distinct elements of an infinite set of naturals. -/
theorem exists_injective_of_infinite {S : Set ℕ} (hS : S.Infinite) (n : ℕ) :
    ∃ q : Fin n → ℕ, Function.Injective q ∧ ∀ i, q i ∈ S :=
  ⟨fun i => (Set.Infinite.natEmbedding S hS i.val : ℕ),
    fun _i _j h => Fin.ext ((Set.Infinite.natEmbedding S hS).injective (Subtype.ext h)),
    fun i => (Set.Infinite.natEmbedding S hS i.val).2⟩

end Primes

section Main

variable (p : ℕ) [hp : Fact p.Prime]

theorem kempner_le_mul (k : ℕ) : kempner p k ≤ p * k :=
  kempner_le p (by rw [padicValNat_factorial_div p, Nat.mul_div_cancel_left _ hp.out.pos]; omega)

theorem kempner_le_pow_mul (k : ℕ) : kempner p k ≤ p ^ (p * k) :=
  (kempner_le_mul p k).trans (Nat.lt_pow_self hp.out.one_lt).le

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- The `δ`-tower identity at level `S(p ^ k) - 1` exists in the Dirichlet ring. -/
theorem hasLevel_kempner (hR : ∀ a : R, (p : R) ∣ a ^ p - a) (f : ArithmeticFunction R)
    (hf : IsUnit f) {k : ℕ} (hk : 1 ≤ k) : HasLevel p (Ep p) f k (kempner p k - 1) := by
  have hfu : f * ↑hf.unit⁻¹ = 1 := hf.mul_val_inv
  have hm := monicAnn_kempner (ep_isFrobLift p hR) (↑hf.unit⁻¹ : ArithmeticFunction R) k
  have e : kempner p k - 1 + 1 = kempner p k := Nat.sub_add_cancel (kempner_pos p hk)
  apply MonicAnn.hasLevel (by rw [hfu, sub_self]; exact dvd_zero _)
  rwa [e]

/-- **Upper bound** (note Theorem A1 in the level form): `L_f(p, k) + 1 ≤ S(p ^ k)`. -/
theorem levelCount_add_one_le_kempner (hR : ∀ a : R, (p : R) ∣ a ^ p - a)
    (f : ArithmeticFunction R) (hf : IsUnit f) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) f k + 1 ≤ kempner p k := by
  have h1 := levelCount_le (hasLevel_kempner p hR f hf hk)
  have h2 := kempner_pos p hk
  omega

/-- **Lower bound over `ℤ`**: `n` distinct primes `q_i` with `p ∤ f(q_i)` force
`L_f(p, k) + 1 ≥ min(p ^ n, S(p ^ k))`. No multiplicativity is assumed. -/
theorem min_le_levelCount_int (f : ArithmeticFunction ℤ) (hf : IsUnit f) {n : ℕ}
    {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)
    (hfq : ∀ i, ¬ (p : ℤ) ∣ f (q i)) {k : ℕ} (hk : 1 ≤ k) :
    min (p ^ n) (kempner p k) ≤ levelCount p (Ep p) f k + 1 := by
  have hfu : f * ↑hf.unit⁻¹ = 1 := hf.mul_val_inv
  have hle := levelCount_map_le (res hq hinj) (σ := Ep p) (σ' := frob p)
    (fun a => res_Ep hq hinj p a) (hasLevel_kempner p (int_pow_sub p) f hf hk)
  have heq := levelCount_eq_of_fullRank_int p (f := res hq hinj f)
    (u := res hq hinj (↑hf.unit⁻¹ : ArithmeticFunction ℤ))
    (by rw [← map_mul, hfu, map_one])
    (fullRank_res hq hinj _ (fun i => not_dvd_inv_apply_prime hfu (hq i) (hfq i))) hk
  omega

/-- **Lower bound over `ℤ_[p]`**, same statement. -/
theorem min_le_levelCount_padic (f : ArithmeticFunction ℤ_[p]) (hf : IsUnit f) {n : ℕ}
    {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)
    (hfq : ∀ i, ¬ (p : ℤ_[p]) ∣ f (q i)) {k : ℕ} (hk : 1 ≤ k) :
    min (p ^ n) (kempner p k) ≤ levelCount p (Ep p) f k + 1 := by
  have hfu : f * ↑hf.unit⁻¹ = 1 := hf.mul_val_inv
  have hle := levelCount_map_le (res hq hinj) (σ := Ep p) (σ' := frob p)
    (fun a => res_Ep hq hinj p a) (hasLevel_kempner p (padicInt_pow_sub p) f hf hk)
  have heq := levelCount_eq_of_fullRank_padic p (f := res hq hinj f)
    (u := res hq hinj (↑hf.unit⁻¹ : ArithmeticFunction ℤ_[p]))
    (by rw [← map_mul, hfu, map_one])
    (fullRank_res hq hinj _ (fun i => not_dvd_inv_apply_prime hfu (hq i) (hfq i))) hk
  omega

/-- **Exact count over `ℤ`**: with `S(p ^ k) ≤ p ^ n`, `L_f(p, k) = S(p ^ k) - 1`. -/
theorem levelCount_eq_kempner_int (f : ArithmeticFunction ℤ) (hf : IsUnit f) {n : ℕ}
    {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)
    (hfq : ∀ i, ¬ (p : ℤ) ∣ f (q i)) {k : ℕ} (hk : 1 ≤ k) (hn : kempner p k ≤ p ^ n) :
    levelCount p (Ep p) f k + 1 = kempner p k := by
  have h1 := min_le_levelCount_int p f hf hq hinj hfq hk
  have h2 := levelCount_add_one_le_kempner p (int_pow_sub p) f hf hk
  rw [min_eq_right hn] at h1
  omega

/-- **Exact count over `ℤ_[p]`**. -/
theorem levelCount_eq_kempner_padic (f : ArithmeticFunction ℤ_[p]) (hf : IsUnit f) {n : ℕ}
    {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)
    (hfq : ∀ i, ¬ (p : ℤ_[p]) ∣ f (q i)) {k : ℕ} (hk : 1 ≤ k) (hn : kempner p k ≤ p ^ n) :
    levelCount p (Ep p) f k + 1 = kempner p k := by
  have h1 := min_le_levelCount_padic p f hf hq hinj hfq hk
  have h2 := levelCount_add_one_le_kempner p (padicInt_pow_sub p) f hf hk
  rw [min_eq_right hn] at h1
  omega

/-- **Exact count, every `k`, over `ℤ`**: infinitely many primes `q` with `p ∤ f(q)`. -/
theorem levelCount_eq_kempner_int_of_infinite (f : ArithmeticFunction ℤ) (hf : IsUnit f)
    (hinf : {q : ℕ | q.Prime ∧ ¬ (p : ℤ) ∣ f q}.Infinite) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) f k + 1 = kempner p k := by
  obtain ⟨q, hinj, hqS⟩ := exists_injective_of_infinite hinf (p * k)
  exact levelCount_eq_kempner_int p f hf (fun i => (hqS i).1) hinj (fun i => (hqS i).2) hk
    (kempner_le_pow_mul p k)

/-- **Exact count, every `k`, over `ℤ_[p]`**. -/
theorem levelCount_eq_kempner_padic_of_infinite (f : ArithmeticFunction ℤ_[p]) (hf : IsUnit f)
    (hinf : {q : ℕ | q.Prime ∧ ¬ (p : ℤ_[p]) ∣ f q}.Infinite) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) f k + 1 = kempner p k := by
  obtain ⟨q, hinj, hqS⟩ := exists_injective_of_infinite hinf (p * k)
  exact levelCount_eq_kempner_padic p f hf (fun i => (hqS i).1) hinj (fun i => (hqS i).2) hk
    (kempner_le_pow_mul p k)

/-- Divisibility by `p` of an integer is the same in `ℤ_[p]`. -/
theorem padic_natCast_dvd_intCast_iff (c : ℤ) : (p : ℤ_[p]) ∣ (c : ℤ_[p]) ↔ (p : ℤ) ∣ c := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
    RingHom.mem_ker, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Integer functions with `f(1) = 1` and `p ∤ f(q)` at every prime: exact count over `ℤ`. -/
theorem levelCount_eq_kempner_int_of_primes (f : ArithmeticFunction ℤ) (h1 : f 1 = 1)
    (hfq : ∀ q : ℕ, q.Prime → ¬ (p : ℤ) ∣ f q) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) f k + 1 = kempner p k := by
  refine levelCount_eq_kempner_int_of_infinite p f ?_
    (Nat.infinite_setOfPred_prime.mono fun q hq => ⟨hq, hfq q hq⟩) hk
  rw [ArithmeticFunction.isUnit_iff_isUnit_apply_one, h1]; exact isUnit_one

/-- The same functions, with values read in `ℤ_[p]`: exact count over `ℤ_[p]`. -/
theorem levelCount_eq_kempner_padic_of_primes (f : ArithmeticFunction ℤ) (h1 : f 1 = 1)
    (hfq : ∀ q : ℕ, q.Prime → ¬ (p : ℤ) ∣ f q) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) (f : ArithmeticFunction ℤ_[p]) k + 1 = kempner p k := by
  refine levelCount_eq_kempner_padic_of_infinite p _ ?_
    (Nat.infinite_setOfPred_prime.mono fun q hq => ⟨hq, ?_⟩) hk
  · rw [ArithmeticFunction.isUnit_iff_isUnit_apply_one, ArithmeticFunction.intCoe_apply, h1,
      Int.cast_one]
    exact isUnit_one
  · rw [ArithmeticFunction.intCoe_apply, padic_natCast_dvd_intCast_iff]; exact hfq q hq

end Main

/-! ## Named cases (note Corollary `cor:named` (a), and (b) for odd `p`) -/

section Named

variable (p : ℕ) [hp : Fact p.Prime]

theorem not_dvd_of_natAbs_one {c : ℤ} (hc : c.natAbs = 1) : ¬ (p : ℤ) ∣ c := by
  rw [Int.natCast_dvd, hc, Nat.dvd_one]; exact hp.out.ne_one

theorem not_dvd_of_natAbs_two (hp2 : p ≠ 2) {c : ℤ} (hc : c.natAbs = 2) : ¬ (p : ℤ) ∣ c := by
  rw [Int.natCast_dvd, hc]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h)

theorem moebius_apply_one' : ArithmeticFunction.moebius 1 = 1 := by simp

/-- The integer `ζ` (constant `1`). -/
abbrev zetaZ : ArithmeticFunction ℤ := (ArithmeticFunction.zeta : ArithmeticFunction ℤ)

theorem zetaZ_apply {n : ℕ} (hn : n ≠ 0) : zetaZ n = 1 := by
  rw [zetaZ, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hn, Nat.cast_one]

/-- `L_μ(p, k) = S(p ^ k) - 1` over `ℤ`, every prime `p`, every `k ≥ 1`. -/
theorem levelCount_moebius_int {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) ArithmeticFunction.moebius k + 1 = kempner p k :=
  levelCount_eq_kempner_int_of_primes p _ (by simp) (fun q hq => not_dvd_of_natAbs_one p
    (by rw [ArithmeticFunction.moebius_apply_prime hq]; rfl)) hk

theorem levelCount_moebius_padic {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) (ArithmeticFunction.moebius : ArithmeticFunction ℤ_[p]) k + 1 =
      kempner p k :=
  levelCount_eq_kempner_padic_of_primes p _ (by simp) (fun q hq => not_dvd_of_natAbs_one p
    (by rw [ArithmeticFunction.moebius_apply_prime hq]; rfl)) hk

/-- `L_ζ(p, k) = S(p ^ k) - 1` (ledger R-053, now in the Dirichlet ring by restriction). -/
theorem levelCount_zetaZ_int {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) zetaZ k + 1 = kempner p k :=
  levelCount_eq_kempner_int_of_primes p _ (zetaZ_apply one_ne_zero)
    (fun q hq => not_dvd_of_natAbs_one p (by rw [zetaZ_apply hq.ne_zero]; rfl)) hk

theorem levelCount_zetaZ_padic {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) (zetaZ : ArithmeticFunction ℤ_[p]) k + 1 = kempner p k :=
  levelCount_eq_kempner_padic_of_primes p _ (zetaZ_apply one_ne_zero)
    (fun q hq => not_dvd_of_natAbs_one p (by rw [zetaZ_apply hq.ne_zero]; rfl)) hk

/-- Liouville `λ`: `L_λ(p, k) = S(p ^ k) - 1`. -/
theorem levelCount_liouville_int {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) ArithmeticFunction.liouville k + 1 = kempner p k :=
  levelCount_eq_kempner_int_of_primes p _ ArithmeticFunction.liouville_apply_one
    (fun q hq => not_dvd_of_natAbs_one p (by
      rw [ArithmeticFunction.liouville_apply hq.ne_zero,
        ArithmeticFunction.cardFactors_apply_prime hq]; rfl)) hk

theorem levelCount_liouville_padic {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) (ArithmeticFunction.liouville : ArithmeticFunction ℤ_[p]) k + 1 =
      kempner p k :=
  levelCount_eq_kempner_padic_of_primes p _ ArithmeticFunction.liouville_apply_one
    (fun q hq => not_dvd_of_natAbs_one p (by
      rw [ArithmeticFunction.liouville_apply hq.ne_zero,
        ArithmeticFunction.cardFactors_apply_prime hq]; rfl)) hk

/-- `μ² = |μ|` (pointwise square). -/
abbrev moebiusSq : ArithmeticFunction ℤ :=
  ArithmeticFunction.pmul ArithmeticFunction.moebius ArithmeticFunction.moebius

theorem levelCount_moebiusSq_int {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) moebiusSq k + 1 = kempner p k :=
  levelCount_eq_kempner_int_of_primes p _ (by simp [moebiusSq, ArithmeticFunction.pmul_apply])
    (fun q hq => not_dvd_of_natAbs_one p (by
      rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.moebius_apply_prime hq]; rfl)) hk

theorem levelCount_moebiusSq_padic {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) (moebiusSq : ArithmeticFunction ℤ_[p]) k + 1 = kempner p k :=
  levelCount_eq_kempner_padic_of_primes p _ (by simp [moebiusSq, ArithmeticFunction.pmul_apply])
    (fun q hq => not_dvd_of_natAbs_one p (by
      rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.moebius_apply_prime hq]; rfl)) hk

/-- The divisor function `d_2 = ζ * ζ`: `L(p, k) = S(p ^ k) - 1` for odd `p`. -/
theorem levelCount_d2_int (hp2 : p ≠ 2) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) (zetaZ * zetaZ) k + 1 = kempner p k :=
  levelCount_eq_kempner_int_of_primes p _
    (by rw [ArithmeticFunction.mul_apply_one, zetaZ_apply one_ne_zero, mul_one])
    (fun q hq => not_dvd_of_natAbs_two p hp2 (by
      rw [mul_apply_prime _ _ hq, zetaZ_apply one_ne_zero, zetaZ_apply hq.ne_zero]; rfl)) hk

theorem levelCount_d2_padic (hp2 : p ≠ 2) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) ((zetaZ * zetaZ : ArithmeticFunction ℤ) : ArithmeticFunction ℤ_[p]) k + 1 =
      kempner p k :=
  levelCount_eq_kempner_padic_of_primes p _
    (by rw [ArithmeticFunction.mul_apply_one, zetaZ_apply one_ne_zero, mul_one])
    (fun q hq => not_dvd_of_natAbs_two p hp2 (by
      rw [mul_apply_prime _ _ hq, zetaZ_apply one_ne_zero, zetaZ_apply hq.ne_zero]; rfl)) hk

/-- `d_2⁻¹ = μ * μ`: `L(p, k) = S(p ^ k) - 1` for odd `p`. -/
theorem levelCount_moebius_mul_moebius_int (hp2 : p ≠ 2) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) (ArithmeticFunction.moebius * ArithmeticFunction.moebius) k + 1 =
      kempner p k :=
  levelCount_eq_kempner_int_of_primes p _ (by rw [ArithmeticFunction.mul_apply_one]; simp)
    (fun q hq => not_dvd_of_natAbs_two p hp2 (by
      rw [mul_apply_prime _ _ hq, ArithmeticFunction.moebius_apply_prime hq]; simp)) hk

theorem levelCount_moebius_mul_moebius_padic (hp2 : p ≠ 2) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) (((ArithmeticFunction.moebius * ArithmeticFunction.moebius :
      ArithmeticFunction ℤ)) : ArithmeticFunction ℤ_[p]) k + 1 = kempner p k :=
  levelCount_eq_kempner_padic_of_primes p _ (by rw [ArithmeticFunction.mul_apply_one]; simp)
    (fun q hq => not_dvd_of_natAbs_two p hp2 (by
      rw [mul_apply_prime _ _ hq, ArithmeticFunction.moebius_apply_prime hq]; simp)) hk

end Named

end Dir

end FrobLevel
