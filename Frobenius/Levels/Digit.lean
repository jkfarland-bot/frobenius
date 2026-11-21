module

/-
Run r25, seat L2: Theorem A' of ledger R-082 (adapted towers give the digit formula), in abstract
form, and the arithmetic step 3 of R-083 (the flag recursion for gamma turns the digit value into
v_p(m!) + sum_j (d(j+1) - d(j)) floor(m / p^j)).

Setting (as in L1's Basis.lean): `A` a commutative ring without `p`-torsion, `σ` a ring
endomorphism, `B = σ(A)` with `B ∩ p A = p B` (`PSat`), `p` not a unit.

An adapted tower of length `N` for `u` (note Theorem 6.3, step 1): monic `T_b ∈ B[X]` of degree
`p ^ b` (`b < N`) with `T_b(u) = p ^ (γ b) * w b`, and the `p ^ N` products
`w ^ e = ∏_b (w b) ^ (e b)`, `e ∈ [0, p) ^ N`, independent over `B` modulo `p` (this is what
"the residues of the `w b` are p-independent" means; `PIndep` of Basis.lean on the products).

Theorem A' (`monicAnn_iff_digit`, `annDegree_eq_digit`, `levelCount_eq_digit`): for `m < p ^ N`
a monic annihilator of degree `m` modulo `p ^ k` exists iff `k ≤ ∑_b e_b(m) γ_b`, so
`L_f + 1 = min(p ^ N, min {m : ∑_b e_b(m) γ_b ≥ k})` when a degree `p ^ N` annihilator exists
(for `N = r_f = n` this is Cayley-Hamilton, L1's `monicAnn_of_span`).

Lean v4.33.1 with Mathlib; no sorry, no axioms beyond propext, Classical.choice, Quot.sound.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Basis

@[expose] public section

namespace FrobLevel

open Polynomial

/-! ## Base `p` digits -/

/-- The base `p` digit of `m` at position `b`. -/
def digit (p b m : ℕ) : ℕ := m / p ^ b % p

theorem sum_digit_mul_pow (p m : ℕ) :
    ∀ N, ∑ b ∈ Finset.range N, digit p b m * p ^ b = m % p ^ N
  | 0 => by simp [Nat.mod_one]
  | N + 1 => by
    rw [Finset.sum_range_succ, sum_digit_mul_pow p m N, Nat.mod_pow_succ, digit]; ring

theorem sum_digit_mul_pow_of_lt {p m N : ℕ} (hm : m < p ^ N) :
    ∑ b ∈ Finset.range N, digit p b m * p ^ b = m := by
  rw [sum_digit_mul_pow, Nat.mod_eq_of_lt hm]

theorem digit_lt {p : ℕ} (hp : 0 < p) (b m : ℕ) : digit p b m < p := Nat.mod_lt _ hp

/-- The digit value `c(m) = ∑_{b < N} e_b(m) γ_b`. -/
def digitVal (p N : ℕ) (γ : ℕ → ℕ) (m : ℕ) : ℕ := ∑ b ∈ Finset.range N, digit p b m * γ b

section Tower

variable {A : Type*} [CommRing A] {p : ℕ} {σ : A →+* A}

/-- `T_{e(m)} = ∏_b T_b ^ (e_b(m))`. -/
noncomputable def towerPoly (p N : ℕ) (T : ℕ → A[X]) (m : ℕ) : A[X] :=
  ∏ b ∈ Finset.range N, T b ^ digit p b m

/-- `w ^ e(m) = ∏_b w_b ^ (e_b(m))`. -/
def towerVal (p N : ℕ) (w : ℕ → A) (m : ℕ) : A :=
  ∏ b ∈ Finset.range N, w b ^ digit p b m

/-- An adapted tower of length `N` for `u` (note Theorem 6.3, step 1; ledger R-082 (3)). -/
def AdaptedTower (p : ℕ) (σ : A →+* A) (N : ℕ) (T : ℕ → A[X]) (γ : ℕ → ℕ) (w : ℕ → A) (u : A) :
    Prop :=
  (∀ b < N, (T b).Monic ∧ (T b).natDegree = p ^ b ∧ T b ∈ BPoly σ ∧
    (T b).eval u = (p : A) ^ (γ b) * w b) ∧
  PIndep p σ (Finset.range (p ^ N)) (towerVal p N w)

theorem towerPoly_monic {N : ℕ} {T : ℕ → A[X]} (hT : ∀ b < N, (T b).Monic) (m : ℕ) :
    (towerPoly p N T m).Monic :=
  monic_prod_of_monic _ _ fun b hb => (hT b (Finset.mem_range.1 hb)).pow _

theorem towerPoly_natDegree {N : ℕ} {T : ℕ → A[X]}
    (hT : ∀ b < N, (T b).Monic ∧ (T b).natDegree = p ^ b) {m : ℕ} (hm : m < p ^ N) :
    (towerPoly p N T m).natDegree = m := by
  rw [towerPoly, natDegree_prod_of_monic _ _ fun b hb =>
    (hT b (Finset.mem_range.1 hb)).1.pow _]
  conv_rhs => rw [← sum_digit_mul_pow_of_lt hm]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [(hT b (Finset.mem_range.1 hb)).1.natDegree_pow, (hT b (Finset.mem_range.1 hb)).2]

theorem towerPoly_mem {N : ℕ} {T : ℕ → A[X]} (hT : ∀ b < N, T b ∈ BPoly σ) (m : ℕ) :
    towerPoly p N T m ∈ BPoly σ :=
  Subring.prod_mem _ fun b hb => pow_mem (hT b (Finset.mem_range.1 hb)) _

theorem towerPoly_eval {N : ℕ} {T : ℕ → A[X]} {γ : ℕ → ℕ} {w : ℕ → A} {u : A}
    (hT : ∀ b < N, (T b).eval u = (p : A) ^ (γ b) * w b) (m : ℕ) :
    (towerPoly p N T m).eval u = (p : A) ^ (digitVal p N γ m) * towerVal p N w m := by
  rw [towerPoly, eval_prod, towerVal, digitVal, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [eval_pow, hT b (Finset.mem_range.1 hb), mul_pow, ← pow_mul, mul_comm (γ b)]

/-- The full monic basis used with Basis.lean: `T_{e(j)}` below `p ^ N`, `X ^ j` above. -/
noncomputable def fullBasis (p N : ℕ) (T : ℕ → A[X]) (j : ℕ) : A[X] :=
  if j < p ^ N then towerPoly p N T j else X ^ j

theorem fullBasis_spec [Nontrivial A] {N : ℕ} {T : ℕ → A[X]}
    (hT : ∀ b < N, (T b).Monic ∧ (T b).natDegree = p ^ b ∧ T b ∈ BPoly σ) (j : ℕ) :
    (fullBasis p N T j).Monic ∧ (fullBasis p N T j).natDegree = j ∧
      fullBasis p N T j ∈ BPoly σ := by
  unfold fullBasis
  split_ifs with hj
  · exact ⟨towerPoly_monic (fun b hb => (hT b hb).1) j,
      towerPoly_natDegree (fun b hb => ⟨(hT b hb).1, (hT b hb).2.1⟩) hj,
      towerPoly_mem (fun b hb => (hT b hb).2.2) j⟩
  · exact ⟨monic_X_pow j, natDegree_X_pow j, pow_mem (X_mem_BPoly σ) j⟩

/-! ## Theorem A' -/

/-- **Theorem A'** (ledger R-082 (3), degree form): with an adapted tower of length `N`, for
`m < p ^ N` a monic annihilator of `u` of degree `m` in `B[X]` modulo `p ^ k` exists if and only
if `k ≤ ∑_b e_b(m) γ_b`. -/
theorem monicAnn_iff_digit [Nontrivial A] (ht : NoPTorsion p A) (hs : PSat p σ)
    (hpu : ¬ IsUnit (p : A)) {N : ℕ} {T : ℕ → A[X]} {γ : ℕ → ℕ} {w : ℕ → A} {u : A}
    (htow : AdaptedTower p σ N T γ w u) {m k : ℕ} (hm : m < p ^ N) :
    MonicAnn p σ u k m ↔ k ≤ digitVal p N γ m := by
  obtain ⟨hT, hind⟩ := htow
  constructor
  · intro hP
    refine le_of_monicAnn ht hs hpu (fullBasis p N T)
      (fullBasis_spec (fun b hb => ⟨(hT b hb).1, (hT b hb).2.1, (hT b hb).2.2.1⟩))
      (W := towerVal p N w) (c := digitVal p N γ) (fun j hj => ?_) hind hm hP
    rw [fullBasis, if_pos hj]
    exact towerPoly_eval (fun b hb => (hT b hb).2.2.2) j
  · intro hk
    refine ⟨towerPoly p N T m, towerPoly_monic (fun b hb => (hT b hb).1) m,
      towerPoly_natDegree (fun b hb => ⟨(hT b hb).1, (hT b hb).2.1⟩) hm,
      towerPoly_mem (fun b hb => (hT b hb).2.2.1) m, ?_⟩
    rw [towerPoly_eval (fun b hb => (hT b hb).2.2.2) m]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ hk) _

/-- **Theorem A'** (ledger R-082 (3)): the least degree of a monic annihilator is
`min(p ^ N, min {m : ∑_b e_b(m) γ_b ≥ k})`, written as one `sInf`, provided some monic
annihilator of degree `p ^ N` exists (the cap; Cayley-Hamilton when `N = r_f`). -/
theorem annDegree_eq_digit [Nontrivial A] (ht : NoPTorsion p A) (hs : PSat p σ)
    (hpu : ¬ IsUnit (p : A)) {N : ℕ} {T : ℕ → A[X]} {γ : ℕ → ℕ} {w : ℕ → A} {u : A}
    (htow : AdaptedTower p σ N T γ w u) {k : ℕ} (hcap : MonicAnn p σ u k (p ^ N)) :
    annDegree p σ u k = sInf {m | p ^ N ≤ m ∨ k ≤ digitVal p N γ m} := by
  set S := {m | p ^ N ≤ m ∨ k ≤ digitVal p N γ m}
  have hne : (p ^ N) ∈ S := Or.inl le_rfl
  apply le_antisymm
  · have hmem : sInf S ∈ S := Nat.sInf_mem ⟨_, hne⟩
    rcases hmem with h | h
    · exact (annDegree_le hcap).trans h
    · by_cases hlt : sInf S < p ^ N
      · exact annDegree_le ((monicAnn_iff_digit ht hs hpu htow hlt).2 h)
      · exact (annDegree_le hcap).trans (not_lt.1 hlt)
  · apply Nat.sInf_le
    by_cases hlt : annDegree p σ u k < p ^ N
    · exact Or.inr ((monicAnn_iff_digit ht hs hpu htow hlt).1 (monicAnn_annDegree hcap))
    · exact Or.inl (not_lt.1 hlt)

/-- **Theorem A'** for the level count (ledger R-082 (3)): for `u` an inverse of `f` modulo
`p ^ k`, `L_f(p, k) + 1 = min(p ^ N, min {m : ∑_b e_b(m) γ_b ≥ k})`. -/
theorem levelCount_eq_digit [Nontrivial A] (ht : NoPTorsion p A) (hs : PSat p σ)
    (hpu : ¬ IsUnit (p : A)) {N : ℕ} {T : ℕ → A[X]} {γ : ℕ → ℕ} {w : ℕ → A} {f u : A}
    (htow : AdaptedTower p σ N T γ w u) {k : ℕ} (hfu : (p : A) ^ k ∣ f * u - 1)
    (hpk : ¬ IsUnit ((p : A) ^ k)) (hcap : MonicAnn p σ u k (p ^ N)) :
    levelCount p σ f k + 1 = sInf {m | p ^ N ≤ m ∨ k ≤ digitVal p N γ m} := by
  rw [levelCount_add_one hfu hpk hcap, annDegree_eq_digit ht hs hpu htow hcap]

/-- A consequence of Theorem A': along an adapted tower the digit value is nondecreasing below
`p ^ N` (it contains the cold reader's INV, `γ_{b+1} ≥ (p - 1)(γ_0 + ... + γ_b)`). -/
theorem digitVal_mono [Nontrivial A] (ht : NoPTorsion p A) (hs : PSat p σ)
    (hpu : ¬ IsUnit (p : A)) {N : ℕ} {T : ℕ → A[X]} {γ : ℕ → ℕ} {w : ℕ → A} {u : A}
    (htow : AdaptedTower p σ N T γ w u) {m m' : ℕ} (hmm : m ≤ m') (hm' : m' < p ^ N) :
    digitVal p N γ m ≤ digitVal p N γ m' := by
  have h1 := (monicAnn_iff_digit ht hs hpu htow (lt_of_le_of_lt hmm hm')).2 le_rfl
  exact (monicAnn_iff_digit ht hs hpu htow hm').1 (h1.mono hmm)

end Tower

/-! ## R-083 step 3: the flag recursion and the Legendre-type formula -/

/-- `γ_b` from the depth flag, with `δ j = d(j+1) - d(j)`:
`γ_b = ∑_{j ≤ b} p ^ (b - j) (δ_j + [j ≥ 1])`. -/
def flagGamma (p : ℕ) (δ : ℕ → ℕ) (b : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (b + 1), p ^ (b - j) * (δ j + if j = 0 then 0 else 1)

theorem flagGamma_zero (p : ℕ) (δ : ℕ → ℕ) : flagGamma p δ 0 = δ 0 := by
  simp [flagGamma]

/-- The recursion of R-083: `γ_{b+1} = p γ_b + 1 + d(b+2) - d(b+1)`. -/
theorem flagGamma_succ (p : ℕ) (δ : ℕ → ℕ) (b : ℕ) :
    flagGamma p δ (b + 1) = p * flagGamma p δ b + 1 + δ (b + 1) := by
  rw [flagGamma, Finset.sum_range_succ, flagGamma, Finset.mul_sum, Nat.sub_self, pow_zero,
    one_mul, if_neg (Nat.succ_ne_zero b)]
  have : ∑ j ∈ Finset.range (b + 1), p ^ (b + 1 - j) * (δ j + if j = 0 then 0 else 1)
      = ∑ j ∈ Finset.range (b + 1), p * (p ^ (b - j) * (δ j + if j = 0 then 0 else 1)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [show b + 1 - j = (b - j) + 1 by omega, pow_succ]; ring
  rw [this]; ring

/-- `∑_{j ≤ b < N} e_b(m) p ^ (b - j) = ⌊m / p ^ j⌋` for `m < p ^ N`. -/
theorem sum_Ico_digit {p m N j : ℕ} (hp : 0 < p) (hm : m < p ^ N) (hj : j ≤ N) :
    ∑ b ∈ Finset.Ico j N, digit p b m * p ^ (b - j) = m / p ^ j := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hlt : m / p ^ j < p ^ (N - j) := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hp j), ← pow_add, Nat.sub_add_cancel hj]; exact hm
  rw [← sum_digit_mul_pow_of_lt hlt]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.add_sub_cancel_left, digit, digit, Nat.div_div_eq_div_mul, ← pow_add]

/-- **R-083, step 3** (arithmetic): with `γ` from the flag recursion, for `m < p ^ N`,
`∑_b e_b(m) γ_b = v_p(m!) + ∑_{j < N} (d(j+1) - d(j)) ⌊m / p ^ j⌋`. -/
theorem digitVal_flagGamma {p : ℕ} [hp : Fact p.Prime] (δ : ℕ → ℕ) {N m : ℕ}
    (hm : m < p ^ N) :
    digitVal p N (flagGamma p δ) m
      = padicValNat p m.factorial + ∑ j ∈ Finset.range N, δ j * (m / p ^ j) := by
  have hp0 := hp.out.pos
  set x : ℕ → ℕ := fun j => δ j + if j = 0 then 0 else 1 with hx
  have h1 : digitVal p N (flagGamma p δ) m
      = ∑ j ∈ Finset.range N, x j * (m / p ^ j) := by
    rw [digitVal]
    simp only [flagGamma, Finset.mul_sum]
    rw [Finset.sum_comm' (t' := Finset.range N) (s' := fun j => Finset.Ico j N)
      (fun b j => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← sum_Ico_digit hp0 hm (Finset.mem_range.1 hj).le, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hx]; ring
  rw [h1]
  simp only [hx, add_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  -- the `[j ≥ 1]` part is Legendre's formula
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : m = 0 := by simpa using hm
    subst this; simp
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN, if_pos rfl, zero_mul, zero_add]
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0; simp
    · rw [padicValNat_factorial (Nat.log_lt_of_lt_pow hm0.ne' hm)]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [if_neg (by have := (Finset.mem_Ico.1 hj).1; omega), one_mul]

section Flag

variable {A : Type*} [CommRing A] {p : ℕ} {σ : A →+* A}

/-- **R-083, conditional form**: if `u = 1/f` has an adapted tower of length `N` whose `γ` follows
the flag recursion (`γ_0 = d(1)`, `γ_{b+1} = p γ_b + 1 + d(b+2) - d(b+1)`, `δ j = d(j+1) - d(j)`),
and a degree `p ^ N` annihilator exists, then
`L_f + 1 = min(p ^ N, min {m : v_p(m!) + ∑_{j<N} (d(j+1) - d(j)) ⌊m / p ^ j⌋ ≥ k})`.
The existence of such a tower for every unit (Theorem F of R-083) is NOT proved here. -/
theorem levelCount_eq_flag [Fact p.Prime] [Nontrivial A] (ht : NoPTorsion p A) (hs : PSat p σ)
    (hpu : ¬ IsUnit (p : A)) {N : ℕ} {T : ℕ → A[X]} {δ : ℕ → ℕ} {w : ℕ → A} {f u : A}
    (htow : AdaptedTower p σ N T (flagGamma p δ) w u) {k : ℕ} (hfu : (p : A) ^ k ∣ f * u - 1)
    (hpk : ¬ IsUnit ((p : A) ^ k)) (hcap : MonicAnn p σ u k (p ^ N)) :
    levelCount p σ f k + 1 = sInf {m | p ^ N ≤ m ∨
      k ≤ padicValNat p m.factorial + ∑ j ∈ Finset.range N, δ j * (m / p ^ j)} := by
  rw [levelCount_eq_digit ht hs hpu htow hfu hpk hcap]
  congr 1
  ext m
  simp only [Set.mem_ofPred_eq]
  by_cases hm : m < p ^ N
  · rw [digitVal_flagGamma δ hm]
  · simp [not_lt.1 hm]

end Flag

end FrobLevel
