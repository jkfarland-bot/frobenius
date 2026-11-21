module

/-
Run r25, seat L1: R-080 stage (b), the tower basis lemma (ledger R-080 (A), note Theorem 6.3 step 1),
in abstract form.

Setting: `A` a commutative ring without `p`-torsion, `σ` any ring endomorphism, `B = σ(A)` with
`B ∩ p A = p B` (`PSat`). Given monic `T_j ∈ B[X]` of degree `j` (`j < M`) with
`T_j(u) = p ^ (c j) * W j`, and the values `W j` independent over `B` modulo `p`
(`∑ q_j W_j ∈ p A` with `q_j ∈ B` forces every `q_j ∈ p A`), then:
* `tower_val`: `p ^ k ∣ ∑ q_j p ^ (c j) W_j` iff `p ^ k ∣ q_j p ^ (c j)` for every `j`;
* `exists_expansion`: every `P ∈ B[X]` of degree `≤ d < M` is `∑_{j ≤ d} q_j T_j` with `q_j ∈ B`
  and `q_d` the coefficient of `X ^ d` in `P`;
* `le_of_monicAnn`: a monic `P ∈ B[X]` of degree `m < M` with `p ^ k ∣ P(u)` has `k ≤ c m`.
With `c m = v_p(m!)` (the δ-tower; `M = p ^ N`) this is the ledger's statement
"`v_p(m!) ≥ k`". The Frobenius lift property is not needed here; it enters only through the
construction of the tower and the independence of its values (stage (c)).
-/
public import Mathlib
public import Frobenius.Levels.Found

@[expose] public section

namespace FrobLevel

open Polynomial

variable {A : Type*} [CommRing A] {p : ℕ} {σ : A →+* A}

/-- `B ∩ p A = p B`. -/
def PSat (p : ℕ) (σ : A →+* A) : Prop :=
  ∀ b ∈ frobImage σ, (p : A) ∣ b → ∃ b' ∈ frobImage σ, b = p * b'

theorem cancel_pow (ht : NoPTorsion p A) {a : ℕ} {x y : A}
    (h : (p : A) ^ a * x = (p : A) ^ a * y) : x = y := by
  induction a with
  | zero => simpa using h
  | succ a ih =>
    apply ih
    have : (p : A) * ((p : A) ^ a * x - (p : A) ^ a * y) = 0 := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, ← pow_succ', h, sub_self]
    exact sub_eq_zero.1 (ht _ this)

theorem dvd_of_pow_mul_dvd (ht : NoPTorsion p A) {a b : ℕ} {x : A}
    (h : (p : A) ^ (a + b) ∣ (p : A) ^ a * x) : (p : A) ^ b ∣ x := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, cancel_pow ht (by rw [hy, pow_add, mul_assoc])⟩

/-- `B ∩ p ^ i A = p ^ i B`. -/
theorem PSat.pow (ht : NoPTorsion p A) (hs : PSat p σ) (i : ℕ) :
    ∀ b ∈ frobImage σ, (p : A) ^ i ∣ b → ∃ b' ∈ frobImage σ, b = p ^ i * b' := by
  induction i with
  | zero => intro b hb _; exact ⟨b, hb, by simp⟩
  | succ i ih =>
    intro b hb hdiv
    obtain ⟨b1, hb1, rfl⟩ := hs b hb (dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero i)) hdiv)
    have : (p : A) ^ i ∣ b1 := dvd_of_pow_mul_dvd (a := 1) ht (by rw [pow_one, add_comm]; exact hdiv)
    obtain ⟨b2, hb2, rfl⟩ := ih b1 hb1 this
    exact ⟨b2, hb2, by ring⟩

/-- Independence of the values over `B` modulo `p`. -/
def PIndep (p : ℕ) (σ : A →+* A) (s : Finset ℕ) (W : ℕ → A) : Prop :=
  ∀ q : ℕ → A, (∀ j ∈ s, q j ∈ frobImage σ) → (p : A) ∣ ∑ j ∈ s, q j * W j →
    ∀ j ∈ s, (p : A) ∣ q j

/-- The tower basis lemma, valuation form (induction on the valuation, as in the ledger). -/
theorem tower_val (ht : NoPTorsion p A) (hs : PSat p σ) {s : Finset ℕ} {W : ℕ → A} (c : ℕ → ℕ)
    (hind : PIndep p σ s W) (k : ℕ) :
    ∀ q : ℕ → A, (∀ j ∈ s, q j ∈ frobImage σ) →
      (p : A) ^ k ∣ ∑ j ∈ s, q j * p ^ (c j) * W j → ∀ j ∈ s, (p : A) ^ k ∣ q j * p ^ (c j) := by
  induction k with
  | zero => intros; simp
  | succ k ih =>
    intro q hq hdiv
    have hk := ih q hq (dvd_trans (pow_dvd_pow _ (Nat.le_succ k)) hdiv)
    -- write `q_j p ^ c_j = p ^ k r_j + p ^ (k + 1) t_j` with `r_j ∈ B`
    have hsplit : ∀ j ∈ s, ∃ r ∈ frobImage σ, ∃ t : A,
        q j * p ^ (c j) = p ^ k * r + p ^ (k + 1) * t := by
      intro j hj
      by_cases hc : c j ≤ k
      · have h1 : (p : A) ^ (c j + (k - c j)) ∣ (p : A) ^ (c j) * q j := by
          rw [Nat.add_sub_cancel' hc, mul_comm]; exact hk j hj
        obtain ⟨r, hr, hqr⟩ := hs.pow ht (k - c j) (q j) (hq j hj) (dvd_of_pow_mul_dvd ht h1)
        refine ⟨r, hr, 0, ?_⟩
        rw [hqr, mul_zero, add_zero, mul_comm, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hc]
      · refine ⟨0, zero_mem _, q j * p ^ (c j - (k + 1)), ?_⟩
        rw [mul_zero, zero_add, mul_left_comm, ← pow_add, Nat.add_sub_cancel' (by omega)]
    choose! r hr t ht' using hsplit
    have hsum : ∑ j ∈ s, q j * p ^ (c j) * W j
        = p ^ k * ∑ j ∈ s, r j * W j + p ^ (k + 1) * ∑ j ∈ s, t j * W j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [ht' j hj]; ring
    rw [hsum] at hdiv
    have h2 : (p : A) ^ (k + 1) ∣ p ^ k * ∑ j ∈ s, r j * W j :=
      (dvd_add_left (dvd_mul_right _ _)).1 hdiv
    have h3 : (p : A) ∣ ∑ j ∈ s, r j * W j := by
      simpa using dvd_of_pow_mul_dvd (a := k) (b := 1) ht h2
    intro j hj
    obtain ⟨y, hy⟩ := hind r hr h3 j hj
    rw [ht' j hj, hy, pow_succ]
    exact dvd_add ⟨y, by ring⟩ (dvd_mul_right _ _)

/-- The converse direction (trivial): termwise divisibility gives divisibility of the sum. -/
theorem tower_val_iff (ht : NoPTorsion p A) (hs : PSat p σ) {s : Finset ℕ} {W : ℕ → A}
    (c : ℕ → ℕ) (hind : PIndep p σ s W) (k : ℕ) (q : ℕ → A) (hq : ∀ j ∈ s, q j ∈ frobImage σ) :
    (p : A) ^ k ∣ ∑ j ∈ s, q j * p ^ (c j) * W j ↔ ∀ j ∈ s, (p : A) ^ k ∣ q j * p ^ (c j) :=
  ⟨tower_val ht hs c hind k q hq,
    fun h => Finset.dvd_sum fun j hj => Dvd.dvd.mul_right (h j hj) _⟩

/-- Expansion in a monic basis of `B[X]` with exact degrees. -/
theorem exists_expansion (T : ℕ → A[X]) (hT : ∀ j, (T j).Monic ∧ (T j).natDegree = j ∧
    T j ∈ BPoly σ) (d : ℕ) :
    ∀ P ∈ BPoly σ, P.natDegree ≤ d → ∃ q : ℕ → A, (∀ j, q j ∈ frobImage σ) ∧
      q d = P.coeff d ∧ P = ∑ j ∈ Finset.range (d + 1), C (q j) * T j := by
  induction d with
  | zero =>
    intro P hP hd
    refine ⟨fun j => if j = 0 then P.coeff 0 else 0, fun j => ?_, by simp, ?_⟩
    · dsimp only
      split_ifs
      · exact (mem_BPoly_iff.1 hP) 0
      · exact zero_mem _
    · have h0 : T 0 = 1 := Polynomial.eq_one_of_monic_natDegree_zero (hT 0).1 (hT 0).2.1
      rw [Finset.sum_range_one]
      show P = C (if (0 : ℕ) = 0 then P.coeff 0 else 0) * T 0
      rw [if_pos rfl, h0, mul_one]
      exact eq_C_of_natDegree_le_zero hd
  | succ d ih =>
    intro P hP hd
    set P' := P - C (P.coeff (d + 1)) * T (d + 1) with hP'
    have hP'B : P' ∈ BPoly σ := by
      refine sub_mem hP (mul_mem ?_ (hT _).2.2)
      obtain ⟨a, ha⟩ := (mem_BPoly_iff.1 hP) (d + 1)
      rw [← ha]; exact C_mem_BPoly σ a
    have hP'd : P'.natDegree ≤ d := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      have hN' : d + 1 ≤ N := by exact_mod_cast hN
      rw [hP', coeff_sub, coeff_C_mul]
      have hc : (T (d + 1)).coeff (d + 1) = 1 := by
        have := (hT (d + 1)).1.coeff_natDegree; rwa [(hT (d + 1)).2.1] at this
      rcases Nat.eq_or_lt_of_le hN' with h | h
      · rw [← h, hc, mul_one, sub_self]
      · have h1 : P.coeff N = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
        have h2 : (T (d + 1)).coeff N = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [(hT (d + 1)).2.1]; exact h)
        rw [h1, h2, mul_zero, sub_zero]
    obtain ⟨q, hq, -, hsum⟩ := ih P' hP'B hP'd
    refine ⟨fun j => if j = d + 1 then P.coeff (d + 1) else q j, fun j => ?_, by simp, ?_⟩
    · dsimp only
      split_ifs
      · exact (mem_BPoly_iff.1 hP) _
      · exact hq j
    · rw [Finset.sum_range_succ]
      show P = _ + C (if d + 1 = d + 1 then P.coeff (d + 1) else q (d + 1)) * T (d + 1)
      rw [if_pos rfl]
      have : ∑ j ∈ Finset.range (d + 1), C (if j = d + 1 then P.coeff (d + 1) else q j) * T j
          = ∑ j ∈ Finset.range (d + 1), C (q j) * T j :=
        Finset.sum_congr rfl fun j hj => by
          rw [if_neg (by have := Finset.mem_range.1 hj; omega)]
      rw [this, ← hsum, hP', sub_add_cancel]

/-- The tower basis lemma, degree form (ledger R-080 (A), last clause): if `T_j(u) = p ^ (c j) W_j`
for `j < M` and the `W_j` (`j < M`) are independent over `B` modulo `p`, then a monic `P ∈ B[X]` of
degree `m < M` with `p ^ k ∣ P(u)` has `k ≤ c m`. -/
theorem le_of_monicAnn (ht : NoPTorsion p A) (hs : PSat p σ) (hpu : ¬ IsUnit (p : A))
    {M : ℕ} (T : ℕ → A[X]) (hT : ∀ j, (T j).Monic ∧ (T j).natDegree = j ∧ T j ∈ BPoly σ)
    {u : A} {W : ℕ → A} {c : ℕ → ℕ} (hTu : ∀ j < M, (T j).eval u = p ^ (c j) * W j)
    (hind : PIndep p σ (Finset.range M) W) {m k : ℕ} (hm : m < M)
    (hP : MonicAnn p σ u k m) : k ≤ c m := by
  obtain ⟨P, hmon, hdeg, hB, hPu⟩ := hP
  obtain ⟨q, hq, hqm, hsum⟩ := exists_expansion T hT m P hB hdeg.le
  have hqm1 : q m = 1 := by rw [hqm, ← hdeg]; exact hmon.coeff_natDegree
  -- extend `q` by `0` beyond `m`, so that the sum runs over `range M`
  set q' : ℕ → A := fun j => if j < m + 1 then q j else 0 with hq'
  have hq'B : ∀ j ∈ Finset.range M, q' j ∈ frobImage σ := fun j _ => by
    simp only [hq']; split_ifs
    · exact hq j
    · exact zero_mem _
  have hev : P.eval u = ∑ j ∈ Finset.range M, q' j * p ^ (c j) * W j := by
    rw [hsum, eval_finsetSum]
    have hsub : Finset.range (m + 1) ⊆ Finset.range M := Finset.range_subset_range.2 hm
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.1 hj
      rw [eval_mul, eval_C, hTu j (by omega), hq']
      simp only [if_pos hj']; ring
    · intro j _ hj
      simp only [hq']
      rw [if_neg (fun h => hj (Finset.mem_range.2 h)), zero_mul, zero_mul]
  rw [hev] at hPu
  have h := tower_val ht hs c hind k q' hq'B hPu m (Finset.mem_range.2 hm)
  simp only [hq', if_pos (Nat.lt_succ_self m), hqm1, one_mul] at h
  by_contra hlt
  push Not at hlt
  obtain ⟨y, hy⟩ := h
  have : (p : A) ^ (c m) * 1 = (p : A) ^ (c m) * ((p : A) ^ (k - c m) * y) := by
    rw [mul_one, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]; exact hy
  have h1 := cancel_pow ht this
  exact hpu (isUnit_of_dvd_one ⟨(p : A) ^ (k - c m - 1) * y, by
    rw [h1, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]⟩)

/-- With `c m = v_p(m!)`: a monic annihilator of degree `m < M` modulo `p ^ k` forces
`m ≥ S(p ^ k)`; so `L + 1 ≥ min(M, S(p ^ k))` once a tower with these values exists. -/
theorem kempner_le_of_monicAnn [Fact p.Prime] (ht : NoPTorsion p A) (hs : PSat p σ)
    (hpu : ¬ IsUnit (p : A)) {M : ℕ} (T : ℕ → A[X])
    (hT : ∀ j, (T j).Monic ∧ (T j).natDegree = j ∧ T j ∈ BPoly σ) {u : A} {W : ℕ → A}
    (hTu : ∀ j < M, (T j).eval u = p ^ (padicValNat p j.factorial) * W j)
    (hind : PIndep p σ (Finset.range M) W) {m k : ℕ} (hm : m < M)
    (hP : MonicAnn p σ u k m) : kempner p k ≤ m :=
  kempner_le p (le_of_monicAnn ht hs hpu T hT hTu hind hm hP)

end FrobLevel
