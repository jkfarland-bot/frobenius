module

/-
Run r25, seat L4: ledger R-086 Theorem G1 and R-087 Lemma D1, abstract form.

Setting: a commutative ring `A`, a prime `p`, a ring endomorphism `σ` of `A` (a Frobenius lift
where needed), `B = σ(A)`. Results:

* `hasLevel_of_poly`: a polynomial `Q ∈ B[X]` of degree `≤ L` with `f Q(f) ≡ 1 (mod p ^ k)` is a
  level `L` identity.
* `hasLevel_geom` (G1 upper bound, the truncated geometric series): if `f ≡ s (mod p ^ J)` with
  `s ∈ B` invertible modulo `p ^ k` inside `B`, then `L_f + 1 ≤ ⌈k / J⌉`.
* `not_hasLevel_of_decomp` (G1 lower bound): if `f = s (1 + p ^ J τ)` with `s ∈ B` and
  `1, τ, ..., τ ^ (p - 1)` independent over `B` modulo `p`, then no level `L` identity has
  `L + 1 < p` and `J (L + 1) < k`.
* `pIndep_of_deriv`: that independence holds whenever some derivation of a domain `K ⊇ A / p`
  is nonzero on `τ mod p` (no other property of `σ` than the lift congruence).
* `pSat_of_domain`: `B ∩ p A = p B` when `A / p` embeds in a domain.
* `pow_mem_iff_delta_mem` (Lemma D1): `m ^ p ∈ B ↔ δ(m) ∈ B`, and `deriv_frob_eq_zero`: every
  derivation kills the image of `B` modulo `p` (the core of Theorem N).
* `levelCount_G1_pos`, `levelCount_G1_zero`: the G1 formula `L_f + 1 = min(p, ⌈k / J⌉)` (and `p`
  for `J = 0`) from these hypotheses together with an identity of level `p - 1`.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.PropT

@[expose] public section

namespace FrobLevel

open Polynomial

/-- `⌈k / J⌉` for natural numbers. -/
def cdiv (k J : ℕ) : ℕ := (k + J - 1) / J

theorem cdiv_le_iff {k J m : ℕ} (hJ : 0 < J) : cdiv k J ≤ m ↔ k ≤ J * m := by
  unfold cdiv
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hJ, Nat.succ_mul, mul_comm m J]
  generalize J * m = t
  omega

theorem le_mul_cdiv {k J : ℕ} (hJ : 0 < J) : k ≤ J * cdiv k J := (cdiv_le_iff hJ).1 le_rfl

theorem one_le_cdiv {k J : ℕ} (hJ : 0 < J) (hk : 1 ≤ k) : 1 ≤ cdiv k J := by
  by_contra h
  have h0 : cdiv k J ≤ 0 := by omega
  rw [cdiv_le_iff hJ] at h0
  omega

section Abstract

variable {A : Type*} [CommRing A]

/-- A polynomial `Q ∈ B[X]` of degree `≤ L` with `p ^ k ∣ 1 - f Q(f)` gives a level `L` identity. -/
theorem hasLevel_of_poly {p : ℕ} {σ : A →+* A} {f : A} {k L : ℕ} {Q : A[X]} (hQ : Q ∈ BPoly σ)
    (hdeg : Q.natDegree ≤ L) (h : (p : A) ^ k ∣ 1 - f * Q.eval f) : HasLevel p σ f k L := by
  have hQ' : ∀ i, ∃ x, σ x = Q.coeff i := fun i => RingHom.mem_range.1 ((mem_BPoly_iff.1 hQ) i)
  choose g hg using hQ'
  refine ⟨g, ?_⟩
  have : Q.eval f = ∑ z ∈ Finset.range (L + 1), f ^ z * σ (g z) := by
    rw [eval_eq_sum_range' (n := L + 1) (by omega)]
    exact Finset.sum_congr rfl fun z _ => by rw [hg z, mul_comm]
  rwa [← this]

/-- **G1, upper bound** (truncated geometric series; every lift, every ring). If `f ≡ s` modulo
`p ^ J` with `s ∈ B`, and `s' ∈ B` inverts `s` modulo `p ^ k`, then for every `N ≥ 1` with
`k ≤ N J` there is an identity of level `N - 1`. -/
theorem hasLevel_geom {p : ℕ} {σ : A →+* A} {f s s' : A} {k J N : ℕ}
    (hs' : s' ∈ frobImage σ) (hss' : (p : A) ^ k ∣ s' * s - 1)
    (hfs : (p : A) ^ J ∣ f - s) (hN : 1 ≤ N) (hkN : k ≤ N * J) :
    HasLevel p σ f k (N - 1) := by
  set Q : A[X] := C s' * ∑ n ∈ Finset.range N, (1 - C s' * X) ^ n with hQ
  have hC : C s' ∈ BPoly σ := by obtain ⟨a, rfl⟩ := hs'; exact C_mem_BPoly σ a
  refine hasLevel_of_poly (Q := Q) ?_ ?_ ?_
  · exact mul_mem hC (sum_mem fun n _ =>
      pow_mem (sub_mem (one_mem _) (mul_mem hC (X_mem_BPoly σ))) n)
  · refine (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun n hn => ?_)
    have h1 : (1 - C s' * X : A[X]).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))
    have hn' := Finset.mem_range.1 hn
    exact natDegree_pow_le.trans ((Nat.mul_le_mul_left n h1).trans (by omega))
  · have hev : 1 - f * Q.eval f = (1 - s' * f) ^ N := by
      have hg := geom_sum_mul (1 - s' * f) N
      simp only [hQ, eval_mul, eval_C, eval_finsetSum, eval_pow, eval_sub, eval_one, eval_X]
      linear_combination hg
    rw [hev]
    have ht : (p : A) ^ (min J k) ∣ 1 - s' * f := by
      have e : 1 - s' * f = -(s' * s - 1) - s' * (f - s) := by ring
      rw [e]
      exact dvd_sub (dvd_neg.2 ((pow_dvd_pow _ (min_le_right _ _)).trans hss'))
        (Dvd.dvd.mul_left ((pow_dvd_pow _ (min_le_left _ _)).trans hfs) _)
    have hk : k ≤ N * min J k := by
      rcases le_total J k with h | h
      · rw [min_eq_left h]; exact hkN
      · rw [min_eq_right h]; exact Nat.le_mul_of_pos_left k hN
    exact (pow_dvd_pow _ hk).trans (by rw [pow_mul']; exact pow_dvd_pow_of_dvd ht N)

/-- **G1, lower bound** (abstract). Let `A` have no `p`-torsion, `B ∩ p A = p B`, `p` not a unit,
`f = s (1 + p ^ J τ)` with `s ∈ B`, and `1, τ, ..., τ ^ (p - 1)` independent over `B` modulo `p`.
Then a level `L` identity modulo `p ^ k` forces `p ≤ L + 1` or `k ≤ J (L + 1)`. -/
theorem le_of_hasLevel_decomp {p : ℕ} {σ : A →+* A} (ht : NoPTorsion p A) (hs : PSat p σ)
    (hp : ¬ IsUnit (p : A)) {f s τ : A} {J k L : ℕ} (hsB : s ∈ frobImage σ)
    (hf : f = s * (1 + (p : A) ^ J * τ))
    (hind : PIndep p σ (Finset.range p) (fun j => τ ^ j)) (h : HasLevel p σ f k L) :
    p ≤ L + 1 ∨ k ≤ J * (L + 1) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hLp, hJk⟩ := hcon
  obtain ⟨g, hg⟩ := h
  set R : A[X] := 1 - X * ∑ z ∈ Finset.range (L + 1), C (σ (g z)) * X ^ z with hR
  have hRB : R ∈ BPoly σ := sub_mem (one_mem _) (mul_mem (X_mem_BPoly σ)
    (sum_mem fun z _ => mul_mem (C_mem_BPoly σ _) (pow_mem (X_mem_BPoly σ) _)))
  have hRdeg : R.natDegree ≤ L + 1 := by
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    refine natDegree_mul_le.trans ?_
    have : (∑ z ∈ Finset.range (L + 1), C (σ (g z)) * X ^ z).natDegree ≤ L :=
      natDegree_sum_le_of_forall_le _ _ fun z hz =>
        (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le z |>.trans
          (by have := Finset.mem_range.1 hz; omega))
    have h2 := natDegree_X_le (R := A)
    omega
  have hReval : ∀ y, R.eval y = 1 - y * ∑ z ∈ Finset.range (L + 1), y ^ z * σ (g z) := by
    intro y
    simp only [hR, eval_sub, eval_one, eval_mul, eval_X, eval_finsetSum, eval_C, eval_pow]
    congr 2
    exact Finset.sum_congr rfl fun z _ => mul_comm _ _
  set Y : A[X] := C s * (1 + X) with hY
  set S : A[X] := R.comp Y with hS
  have hYB : Y ∈ BPoly σ := by
    obtain ⟨a, rfl⟩ := hsB
    exact mul_mem (C_mem_BPoly σ a) (add_mem (one_mem _) (X_mem_BPoly σ))
  have hSB : S ∈ BPoly σ := comp_mem_BPoly hRB hYB
  have hYdeg : Y.natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le))
  have hSdeg : S.natDegree ≤ L + 1 :=
    natDegree_comp_le.trans ((Nat.mul_le_mul hRdeg hYdeg).trans (by omega))
  have hSeval : ∀ y, S.eval y = R.eval (s * (1 + y)) := fun y => by
    simp [hS, hY, eval_comp]
  -- `S(p ^ J τ) = R(f)`, expanded in powers of `τ`
  have hexp : S.eval ((p : A) ^ J * τ)
      = ∑ j ∈ Finset.range p, S.coeff j * (p : A) ^ (J * j) * τ ^ j := by
    rw [eval_eq_sum_range' (n := p) (by omega)]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_pow, ← pow_mul]; ring
  have hdiv : (p : A) ^ k ∣ ∑ j ∈ Finset.range p, S.coeff j * (p : A) ^ (J * j) * τ ^ j := by
    rw [← hexp, hSeval, ← hf, hReval]; exact hg
  have hcoef := tower_val ht hs (fun j => J * j) hind k (fun j => S.coeff j)
    (fun j _ => (mem_BPoly_iff.1 hSB) j) hdiv
  -- every coefficient of `S` is divisible by `p`
  have hall : ∀ j ∈ Finset.range p, (p : A) ∣ S.coeff j := by
    intro j hj
    by_cases hjL : j ≤ L + 1
    · have hJj : J * j + 1 ≤ k := by
        have := Nat.mul_le_mul_left J hjL; omega
      have h1 : (p : A) ^ (J * j + 1) ∣ (p : A) ^ (J * j) * S.coeff j := by
        rw [mul_comm ((p : A) ^ (J * j))]; exact (pow_dvd_pow _ hJj).trans (hcoef j hj)
      simpa using dvd_of_pow_mul_dvd (a := J * j) (b := 1) ht h1
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact dvd_zero _
  -- evaluate at `-1`: `S(-1) = R(0) = 1`
  have hm1 : S.eval (-1) = 1 := by rw [hSeval]; simp [hReval]
  have : (p : A) ∣ S.eval (-1) := by
    rw [eval_eq_sum_range' (n := p) (by omega)]
    exact Finset.dvd_sum fun j hj => Dvd.dvd.mul_right (hall j hj) _
  rw [hm1] at this
  exact hp (isUnit_of_dvd_one this)

/-! ### Independence from a derivation -/

/-- In a domain, a relation `∑_{j < n} c_j t ^ j = 0` with `n ≤ p`, constants `c_j` (killed by
`D`), `D t ≠ 0` and `1, ..., p - 1` nonzero is trivial. -/
theorem eq_zero_of_deriv {K : Type*} [CommRing K] [NoZeroDivisors K] {R : Type*} [CommRing R]
    [Algebra R K] (D : Derivation R K K) {p : ℕ} (hchar : ∀ d : ℕ, 0 < d → d < p → (d : K) ≠ 0)
    {t : K} (ht : D t ≠ 0) :
    ∀ n : ℕ, n ≤ p → ∀ c : ℕ → K, (∀ j < n, D (c j) = 0) →
      ∑ j ∈ Finset.range n, c j * t ^ j = 0 → ∀ j < n, c j = 0 := by
  intro n
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro hn c hc hsum
    -- differentiate
    have hD : D (∑ j ∈ Finset.range (n + 1), c j * t ^ j)
        = (∑ i ∈ Finset.range n, ((i + 1 : ℕ) * c (i + 1)) * t ^ i) * D t := by
      rw [map_sum, Finset.sum_range_succ', Finset.sum_mul]
      have h0 : D (c 0 * t ^ 0) = 0 := by
        rw [pow_zero, mul_one]; exact hc 0 (by omega)
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      rw [Derivation.leibniz, Derivation.leibniz_pow, hc (i + 1) (by omega), smul_zero, add_zero,
        smul_eq_mul, smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
      push_cast; ring
    rw [hsum, map_zero] at hD
    have hsum' : ∑ i ∈ Finset.range n, ((i + 1 : ℕ) * c (i + 1)) * t ^ i = 0 := by
      rcases mul_eq_zero.1 hD.symm with h | h
      · exact h
      · exact absurd h ht
    have hc' : ∀ i < n, D ((i + 1 : ℕ) * c (i + 1)) = 0 := by
      intro i hi
      rw [Derivation.leibniz, hc (i + 1) (by omega), smul_zero, zero_add, smul_eq_mul]
      have : D ((i + 1 : ℕ) : K) = 0 := by
        rw [← map_natCast (algebraMap R K)]; exact D.map_algebraMap _
      rw [this, mul_zero]
    have hz := ih (by omega) (fun i => ((i + 1 : ℕ) : K) * c (i + 1)) hc' hsum'
    have hpos : ∀ j, 1 ≤ j → j < n + 1 → c j = 0 := by
      intro j hj1 hj
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have := hz i (by omega)
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (hchar (i + 1) (by omega) (by omega))
      · exact h
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [Finset.sum_range_succ'] at hsum
      have : ∑ i ∈ Finset.range n, c (i + 1) * t ^ (i + 1) = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [hpos (i + 1) (by omega) (by have := Finset.mem_range.1 hi; omega), zero_mul]
      rw [this, zero_add, pow_zero, mul_one] at hsum
      exact hsum
    · exact hpos j hj0 hj

/-- Under a Frobenius lift, `π (σ a) = π a ^ p` for any ring map `π` killing `p`. -/
theorem map_frob {p : ℕ} {σ : A →+* A} (h : IsFrobLift p σ) {K : Type*} [CommRing K]
    (π : A →+* K) (hπp : π (p : A) = 0) (a : A) : π (σ a) = π a ^ p := by
  obtain ⟨c, hc⟩ := h a
  have := congrArg π hc
  rw [map_sub, map_mul, hπp, zero_mul, sub_eq_zero, map_pow] at this
  exact this

/-- **Core of R-087 Theorem N.** Every derivation of `K` kills the image of `B` modulo `p`. -/
theorem deriv_frob_eq_zero {p : ℕ} {σ : A →+* A} (h : IsFrobLift p σ) {K : Type*} [CommRing K]
    {R : Type*} [CommRing R] [Algebra R K] (D : Derivation R K K) (π : A →+* K)
    (hπp : π (p : A) = 0) (a : A) : D (π (σ a)) = 0 := by
  rw [map_frob h π hπp, Derivation.leibniz_pow, nsmul_eq_mul, ← map_natCast π, hπp, zero_mul]

/-- `1, τ, ..., τ ^ (p - 1)` are independent over `B` modulo `p` as soon as some derivation of a
domain `K` receiving `A / p` is nonzero on `τ mod p`. -/
theorem pIndep_of_deriv {p : ℕ} {σ : A →+* A} (h : IsFrobLift p σ) {K : Type*} [CommRing K]
    [NoZeroDivisors K] {R : Type*} [CommRing R] [Algebra R K] (π : A →+* K)
    (hπ : ∀ a, π a = 0 ↔ (p : A) ∣ a) (hchar : ∀ d : ℕ, 0 < d → d < p → (d : K) ≠ 0)
    (D : Derivation R K K) {τ : A} (hτ : D (π τ) ≠ 0) :
    PIndep p σ (Finset.range p) (fun j => τ ^ j) := by
  intro q hq hdiv j hj
  have hπp : π (p : A) = 0 := (hπ _).2 dvd_rfl
  have h0 : ∑ i ∈ Finset.range p, π (q i) * π τ ^ i = 0 := by
    have := (hπ _).2 hdiv
    simpa [map_sum, map_mul, map_pow] using this
  have hc : ∀ i < p, D (π (q i)) = 0 := by
    intro i hi
    obtain ⟨a, ha⟩ := hq i (Finset.mem_range.2 hi)
    rw [← ha]; exact deriv_frob_eq_zero h D π hπp a
  exact (hπ _).1 (eq_zero_of_deriv D hchar hτ p le_rfl (fun i => π (q i)) hc h0 j
    (Finset.mem_range.1 hj))

/-- `B ∩ p A = p B` when `π : A → K` has kernel `p A` and `K` is a domain. -/
theorem pSat_of_domain {p : ℕ} {σ : A →+* A} (h : IsFrobLift p σ) {K : Type*} [CommRing K]
    [NoZeroDivisors K] (π : A →+* K) (hπ : ∀ a, π a = 0 ↔ (p : A) ∣ a) : PSat p σ := by
  rintro b ⟨a, rfl⟩ hb
  have hπp : π (p : A) = 0 := (hπ _).2 dvd_rfl
  have h1 : π a ^ p = 0 := by rw [← map_frob h π hπp, (hπ _).2 hb]
  obtain ⟨a', rfl⟩ := (hπ a).1 (eq_zero_of_pow_eq_zero h1)
  exact ⟨σ a', ⟨a', rfl⟩, by rw [map_mul, map_natCast]⟩

/-- **R-087 Lemma D1.** For `A` without `p`-torsion and `B ∩ p A = p B`:
`m ^ p ∈ B ↔ δ(m) ∈ B`. -/
theorem pow_mem_iff_delta_mem {p : ℕ} {σ : A →+* A} (ht : NoPTorsion p A) (hs : PSat p σ)
    (h : IsFrobLift p σ) (m : A) : m ^ p ∈ frobImage σ ↔ delta h m ∈ frobImage σ := by
  have hpd := p_mul_delta h m
  have hσ : σ m ∈ frobImage σ := ⟨m, rfl⟩
  constructor
  · intro hm
    have hmem : (p : A) * delta h m ∈ frobImage σ := by rw [hpd]; exact sub_mem hσ hm
    obtain ⟨b, hb, hbe⟩ := hs _ hmem (dvd_mul_right _ _)
    have : delta h m = b := cancel_pow (a := 1) ht (by simpa using hbe)
    rw [this]; exact hb
  · intro hd
    have : m ^ p = σ m - (p : A) * delta h m := by rw [hpd]; ring
    rw [this]
    exact sub_mem hσ (mul_mem (natCast_mem _ p) hd)

/-! ### The G1 formula from the abstract hypotheses -/

/-- **G1, abstract, `J ≥ 1`.** Hypotheses: no `p`-torsion, `B ∩ p A = p B`, `p` not a unit;
`f = s (1 + p ^ J τ)` with `s ∈ B`, `s' ∈ B` inverting `s` modulo `p ^ k`, `τ` independent; and
some identity of level `p - 1` (in one variable it comes from the rank bound). Then
`L_f(p, k) + 1 = min(p, ⌈k / J⌉)`. -/
theorem levelCount_G1_pos {p : ℕ} [hp : Fact p.Prime] {σ : A →+* A} (ht : NoPTorsion p A)
    (hs : PSat p σ) (hpu : ¬ IsUnit (p : A)) {f s s' τ : A} {J k : ℕ} (hJ : 1 ≤ J) (hk : 1 ≤ k)
    (hsB : s ∈ frobImage σ) (hs'B : s' ∈ frobImage σ) (hss' : (p : A) ^ k ∣ s' * s - 1)
    (hf : f = s * (1 + (p : A) ^ J * τ))
    (hind : PIndep p σ (Finset.range p) (fun j => τ ^ j))
    (hrank : HasLevel p σ f k (p - 1)) :
    levelCount p σ f k + 1 = min p (cdiv k J) := by
  have hp1 := hp.out.one_lt
  have hc1 := one_le_cdiv (by omega : 0 < J) hk
  have hgeo : HasLevel p σ f k (cdiv k J - 1) :=
    hasLevel_geom hs'B hss' (by rw [hf]; exact ⟨s * τ, by ring⟩) hc1
      (by rw [mul_comm]; exact le_mul_cdiv (by omega))
  have hup : levelCount p σ f k + 1 ≤ min p (cdiv k J) := by
    rcases le_total p (cdiv k J) with h | h
    · rw [min_eq_left h]; have := levelCount_le hrank; omega
    · rw [min_eq_right h]; have := levelCount_le hgeo; omega
  have hlow := le_of_hasLevel_decomp ht hs hpu hsB hf hind (hasLevel_levelCount hrank)
  have hlow' : min p (cdiv k J) ≤ levelCount p σ f k + 1 := by
    rcases hlow with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans ((cdiv_le_iff (by omega)).2 h)
  omega

/-- **G1, abstract, `J = 0`.** With `f = s (1 + τ)`, `s ∈ B`, `τ` independent and an identity of
level `p - 1`: `L_f(p, k) + 1 = p` for every `k ≥ 1`. -/
theorem levelCount_G1_zero {p : ℕ} [hp : Fact p.Prime] {σ : A →+* A} (ht : NoPTorsion p A)
    (hs : PSat p σ) (hpu : ¬ IsUnit (p : A)) {f s τ : A} {k : ℕ} (hk : 1 ≤ k)
    (hsB : s ∈ frobImage σ) (hf : f = s * (1 + τ))
    (hind : PIndep p σ (Finset.range p) (fun j => τ ^ j))
    (hrank : HasLevel p σ f k (p - 1)) :
    levelCount p σ f k + 1 = p := by
  have hp1 := hp.out.one_lt
  have hlow := le_of_hasLevel_decomp (J := 0) ht hs hpu hsB (by rw [hf]; simp) hind
    (hasLevel_levelCount hrank)
  have := levelCount_le hrank
  rcases hlow with h | h
  · omega
  · simp at h; omega

end Abstract

end FrobLevel
