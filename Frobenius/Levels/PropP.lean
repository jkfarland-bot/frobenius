module

/-
Run r25, seat L2: Proposition P of ledger R-082 and the refutation of C3, in Lean.

Setting: `A = R[[x, y]]` (`MvPowerSeries (Fin 2) R`, `x = X 0`, `y = X 1`), `σ = frob p`
(`x_i ↦ x_i ^ p`), `R` any commutative ring without `p`-torsion in which `p` is not a unit
(`ℤ_[p]`, the ledger's ring, and `ℤ`).

* `psat_frob`: `B ∩ p A = p B` for `B = σ(A)`.
* `pIndep_of_monomial`: values congruent modulo `p` to monomials in pairwise distinct classes
  modulo `p` are independent over `B` modulo `p`.
* Proposition P (`propP_adapted`): for `u = 1 + p ^ a x + p ^ b y` with `a < b`, the tower
  `T_0 = X - 1`, `T_1 = (X - 1) ^ p - p ^ (p a) x ^ p - p ^ (p b) y ^ p` is adapted, with
  `γ = (a, (p - 1) a + b + 1)`, `w_0 ≡ x`, `w_1 ≡ x ^ (p - 1) y (mod p)`.
* `levelCount_propP`: hence (Theorem A', Digit.lean) for every `k ≥ 1`
  `L_f(p, k) + 1 = min(p ^ 2, min {m : e_0(m) a + e_1(m) ((p - 1) a + b + 1) ≥ k})`, `f = 1/u`.
* The refutation of C3 (ledger R-082 (1)): `ce_two` (`p = 2`, `u = 1 + 2x + 4y`, `k = 4`:
  `L + 1 = 2`), `ce_three` (`p = 3`, `u = 1 + 3x + 9y`, `k = 5`: `L + 1 = 3`), and the ledger's
  displayed relations `ce_two_relation`, `ce_three_relation`.

The tower differs from the ledger's displayed relation by the constant `p ^ (p b) y ^ p ∈ B`; this
makes `w_1` a monomial modulo `p` also in the tie case `p = 2`, `b = a + 1`.

Lean v4.33.1 with Mathlib; no sorry, no axioms beyond propext, Classical.choice, Quot.sound.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.Digit

@[expose] public section

namespace FrobLevel

open MvPowerSeries

section General

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] {n : ℕ}

/-- `B ∩ p A = p B` for `A = R[[x_1..x_n]]` and `B = σ(A)`. -/
theorem psat_frob : PSat p (frob p : MvPowerSeries (Fin n) R →+* MvPowerSeries (Fin n) R) := by
  rintro b ⟨a, rfl⟩ hdiv
  have h1 : ∀ d, (p : R) ∣ coeff d a := fun d => by
    have := coeff_of_natCast_dvd p hdiv (p • d)
    rwa [coeff_frob_smul] at this
  obtain ⟨a', ha'⟩ := natCast_dvd_of_coeff p h1
  exact ⟨frob p a', ⟨a', rfl⟩, by rw [ha', map_mul, map_natCast]⟩

/-- Values congruent modulo `p` to monomials `x ^ (c j)` whose exponents are pairwise distinct
modulo `p` are independent over `B` modulo `p`. -/
theorem pIndep_of_monomial {s : Finset ℕ} {W : ℕ → MvPowerSeries (Fin n) R}
    (c : ℕ → (Fin n →₀ ℕ))
    (hW : ∀ j ∈ s, (p : MvPowerSeries (Fin n) R) ∣ W j - monomial (c j) 1)
    (hc : ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → ∃ i, c j i % p ≠ c j' i % p) :
    PIndep p (frob p) s W := by
  classical
  intro q hq hdiv j0 hj0
  have hdiv' : (p : MvPowerSeries (Fin n) R) ∣ ∑ j ∈ s, q j * monomial (c j) 1 := by
    have h2 : (p : MvPowerSeries (Fin n) R) ∣ ∑ j ∈ s, q j * (W j - monomial (c j) 1) :=
      Finset.dvd_sum fun j hj => (hW j hj).mul_left _
    have h3 := dvd_sub hdiv h2
    have : ∑ j ∈ s, q j * W j - ∑ j ∈ s, q j * (W j - monomial (c j) 1)
        = ∑ j ∈ s, q j * monomial (c j) 1 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rwa [this] at h3
  obtain ⟨b0, hb0⟩ := hq j0 hj0
  have hcoef : ∀ d, (p : R) ∣ coeff d b0 := by
    intro d
    have h := coeff_of_natCast_dvd p hdiv' (p • d + c j0)
    rw [map_sum, Finset.sum_eq_single_of_mem j0 hj0] at h
    · rwa [← hb0, coeff_mul_monomial, if_pos le_add_self, add_tsub_cancel_right,
        coeff_frob_smul, mul_one] at h
    · intro j hj hne
      obtain ⟨b, hb⟩ := hq j hj
      rw [← hb, coeff_mul_monomial]
      split_ifs with hle
      · obtain ⟨i, hi⟩ := hc j0 hj0 j hj (Ne.symm hne)
        rw [coeff_frob_of_not_dvd p _ (i := i), zero_mul]
        intro hdvd
        apply hi
        have hle' : c j i ≤ (p • d + c j0) i := hle i
        rw [Finsupp.tsub_apply] at hdvd
        have := (Nat.modEq_iff_dvd' hle').2 hdvd
        unfold Nat.ModEq at this
        rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Nat.add_mod,
          Nat.mul_mod_right, zero_add, Nat.mod_mod] at this
        exact this.symm
      · rfl
  obtain ⟨a', ha'⟩ := natCast_dvd_of_coeff p hcoef
  rw [← hb0, ha', map_mul, map_natCast]
  exact dvd_mul_right _ _

end General

section PropP

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R]

/-- `u = 1 + p ^ a x + p ^ b y`. -/
noncomputable def uP (a b : ℕ) : MvPowerSeries (Fin 2) R :=
  1 + (p : MvPowerSeries (Fin 2) R) ^ a * X 0 + (p : MvPowerSeries (Fin 2) R) ^ b * X 1

/-- `T_0 = X - 1`. -/
noncomputable def T0P : Polynomial (MvPowerSeries (Fin 2) R) := Polynomial.X - 1

/-- `T_1 = (X - 1) ^ p - (p ^ (p a) x ^ p + p ^ (p b) y ^ p)`. -/
noncomputable def T1P (a b : ℕ) : Polynomial (MvPowerSeries (Fin 2) R) :=
  (Polynomial.X - 1) ^ p - Polynomial.C ((p : MvPowerSeries (Fin 2) R) ^ (p * a) * X 0 ^ p
    + (p : MvPowerSeries (Fin 2) R) ^ (p * b) * X 1 ^ p)

noncomputable def towerP (a b : ℕ) : ℕ → Polynomial (MvPowerSeries (Fin 2) R) :=
  fun j => if j = 0 then T0P (R := R) else T1P p a b

theorem towerP_zero (a b : ℕ) : towerP p (R := R) a b 0 = T0P := by simp [towerP]

theorem towerP_one (a b : ℕ) : towerP p (R := R) a b 1 = T1P p a b := by simp [towerP]

def gammaP (a b : ℕ) : ℕ → ℕ := fun j => if j = 0 then a else (p - 1) * a + b + 1

/-- `w_0 = x + p ^ (b - a) y`. -/
noncomputable def w0P (a b : ℕ) : MvPowerSeries (Fin 2) R :=
  X 0 + (p : MvPowerSeries (Fin 2) R) ^ (b - a) * X 1

/-- `w_1 = ∑_{1 ≤ i < p} p ^ ((b - a)(i - 1)) (C(p, i) / p) x ^ (p - i) y ^ i`. -/
noncomputable def w1P (a b : ℕ) : MvPowerSeries (Fin 2) R :=
  ∑ i ∈ Finset.range (p - 1), (((p ^ ((b - a) * i) * (p.choose (1 + i) / p) : ℕ)) :
    MvPowerSeries (Fin 2) R) * X 1 ^ (1 + i) * X 0 ^ (p - (1 + i))

noncomputable def wP (a b : ℕ) : ℕ → MvPowerSeries (Fin 2) R :=
  fun j => if j = 0 then w0P p (R := R) a b else w1P p a b

theorem eval_T0P {a b : ℕ} (hab : a ≤ b) :
    (T0P (R := R)).eval (uP p a b) = (p : MvPowerSeries (Fin 2) R) ^ a * w0P p a b := by
  simp only [T0P, uP, w0P, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
  rw [show b = a + (b - a) by omega, pow_add, Nat.add_sub_cancel_left]; ring

/-- The binomial computation behind Proposition P. -/
theorem eval_T1P {a b : ℕ} (hab : a < b) :
    (T1P p a b).eval (uP p (R := R) a b)
      = (p : MvPowerSeries (Fin 2) R) ^ ((p - 1) * a + b + 1) * w1P p a b := by
  have hp2 := hp.out.two_le
  set P : MvPowerSeries (Fin 2) R := (p : MvPowerSeries (Fin 2) R) with hP
  set s : MvPowerSeries (Fin 2) R := P ^ b * X 1 with hs
  set t : MvPowerSeries (Fin 2) R := P ^ a * X 0 with ht
  have h1 : (T1P p a b).eval (uP p (R := R) a b)
      = (s + t) ^ p - (P ^ (p * a) * X 0 ^ p + P ^ (p * b) * X 1 ^ p) := by
    simp only [T1P, uP, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_C, hs, ht, hP]
    ring
  have htp : t ^ p = P ^ (p * a) * X 0 ^ p := by rw [ht, mul_pow, ← pow_mul, mul_comm a p]
  have hsp : s ^ p = P ^ (p * b) * X 1 ^ p := by rw [hs, mul_pow, ← pow_mul, mul_comm b p]
  rw [h1, add_pow, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p + 1),
    Finset.sum_Ico_succ_top (by omega : 1 ≤ p), Finset.sum_Ico_eq_sum_range]
  simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.sub_self, Nat.choose_self,
    Nat.cast_one, mul_one, one_mul]
  rw [htp, hsp, w1P, Finset.mul_sum]
  have hterm : ∀ i ∈ Finset.range (p - 1),
      s ^ (1 + i) * t ^ (p - (1 + i)) * ((p.choose (1 + i) : ℕ) : MvPowerSeries (Fin 2) R)
        = P ^ ((p - 1) * a + b + 1) * ((((p ^ ((b - a) * i) * (p.choose (1 + i) / p) : ℕ)) :
          MvPowerSeries (Fin 2) R) * X 1 ^ (1 + i) * X 0 ^ (p - (1 + i))) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hc : p ∣ p.choose (1 + i) := hp.out.dvd_choose_self (by omega) (by omega)
    set K := p.choose (1 + i) / p with hK
    have hch : p.choose (1 + i) = p * K := (Nat.mul_div_cancel' hc).symm
    rw [hch]
    push_cast
    rw [hs, ht, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    have hE : b * (1 + i) + a * (p - (1 + i)) + 1 = (p - 1) * a + b + 1 + (b - a) * i := by
      obtain ⟨q, hq⟩ : ∃ q, p = 1 + i + q := ⟨p - (1 + i), by omega⟩
      obtain ⟨e, he⟩ : ∃ e, b = a + e := ⟨b - a, by omega⟩
      rw [hq, he, show 1 + i + q - (1 + i) = q by omega, show 1 + i + q - 1 = i + q by omega,
        show a + e - a = e by omega]
      ring
    have key : P ^ (b * (1 + i)) * P ^ (a * (p - (1 + i))) * P
        = P ^ ((p - 1) * a + b + 1) * P ^ ((b - a) * i) := by
      rw [← pow_add, ← pow_succ, ← pow_add, hE]
    linear_combination ((K : MvPowerSeries (Fin 2) R) * X 1 ^ (1 + i) * X 0 ^ (p - (1 + i))) * key
  rw [Finset.sum_congr rfl hterm]
  ring

theorem dvd_w0P_sub {a b : ℕ} (hab : a < b) :
    (p : MvPowerSeries (Fin 2) R) ∣ w0P p a b - X 0 := by
  rw [w0P, add_sub_cancel_left]
  exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _

theorem dvd_w1P_sub {a b : ℕ} (hab : a < b) :
    (p : MvPowerSeries (Fin 2) R) ∣ w1P p a b - X 0 ^ (p - 1) * X 1 := by
  have hp2 := hp.out.two_le
  have h0 : (0 : ℕ) ∈ Finset.range (p - 1) := Finset.mem_range.2 (by omega)
  rw [w1P, ← Finset.add_sum_erase _ _ h0]
  have hf0 : (((p ^ ((b - a) * 0) * (p.choose (1 + 0) / p) : ℕ)) : MvPowerSeries (Fin 2) R)
      * X 1 ^ (1 + 0) * X 0 ^ (p - (1 + 0)) = X 0 ^ (p - 1) * X 1 := by
    rw [mul_zero, pow_zero, one_mul, add_zero, Nat.choose_one_right,
      Nat.div_self hp.out.pos, Nat.cast_one, one_mul, pow_one, mul_comm]
  rw [hf0, add_sub_cancel_left]
  refine Finset.dvd_sum fun i hi => ?_
  have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
  have : p ∣ p ^ ((b - a) * i) * (p.choose (1 + i) / p) :=
    Dvd.dvd.mul_right (dvd_pow_self _ (Nat.mul_ne_zero (by omega) hi0)) _
  exact_mod_cast Nat.cast_dvd_cast this

/-- The exponent of the residue of `w ^ e(j)`: `x ^ (e_0 + (p - 1) e_1) y ^ (e_1)`. -/
noncomputable def clsP (j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (digit p 0 j + (p - 1) * digit p 1 j) + Finsupp.single 1 (digit p 1 j)

theorem clsP_zero (j : ℕ) : clsP p j 0 = digit p 0 j + (p - 1) * digit p 1 j := by
  simp [clsP]

theorem clsP_one (j : ℕ) : clsP p j 1 = digit p 1 j := by
  simp [clsP]

theorem monomial_clsP (j : ℕ) :
    (monomial (clsP p j) (1 : R) : MvPowerSeries (Fin 2) R)
      = X 0 ^ (digit p 0 j + (p - 1) * digit p 1 j) * X 1 ^ (digit p 1 j) := by
  rw [clsP, ← one_mul (1 : R), ← monomial_mul_monomial, ← X_pow_eq, ← X_pow_eq]

theorem towerVal_wP (a b j : ℕ) :
    towerVal p 2 (wP p (R := R) a b) j = w0P p a b ^ digit p 0 j * w1P p a b ^ digit p 1 j := by
  simp [towerVal, Finset.prod_range_succ, wP]

theorem dvd_towerVal_sub {a b : ℕ} (hab : a < b) (j : ℕ) :
    (p : MvPowerSeries (Fin 2) R) ∣ towerVal p 2 (wP p a b) j - monomial (clsP p j) 1 := by
  set I : Ideal (MvPowerSeries (Fin 2) R) := Ideal.span {(p : MvPowerSeries (Fin 2) R)}
  have hiff : ∀ x y : MvPowerSeries (Fin 2) R,
      (p : MvPowerSeries (Fin 2) R) ∣ x - y ↔ Ideal.Quotient.mk I x = Ideal.Quotient.mk I y :=
    fun x y => by rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have h0 := (hiff _ _).1 (dvd_w0P_sub p (R := R) hab)
  have h1 := (hiff _ _).1 (dvd_w1P_sub p (R := R) hab)
  rw [hiff, towerVal_wP, monomial_clsP, map_mul, map_pow, map_pow, h0, h1, ← map_pow,
    ← map_pow, ← map_mul]
  congr 1
  ring

theorem clsP_distinct (j j' : ℕ) (hj : j < p ^ 2) (hj' : j' < p ^ 2) (hne : j ≠ j') :
    ∃ i, clsP p j i % p ≠ clsP p j' i % p := by
  have hp0 := hp.out.pos
  by_contra hall
  push Not at hall
  have e1 : digit p 1 j = digit p 1 j' := by
    have := hall 1
    rwa [clsP_one, clsP_one, Nat.mod_eq_of_lt (digit_lt hp0 1 j),
      Nat.mod_eq_of_lt (digit_lt hp0 1 j')] at this
  have e0 : digit p 0 j = digit p 0 j' := by
    have h := hall 0
    rw [clsP_zero, clsP_zero, e1] at h
    have h' : digit p 0 j ≡ digit p 0 j' [MOD p] := Nat.ModEq.add_right_cancel' _ h
    unfold Nat.ModEq at h'
    rwa [Nat.mod_eq_of_lt (digit_lt hp0 0 j), Nat.mod_eq_of_lt (digit_lt hp0 0 j')] at h'
  apply hne
  rw [← sum_digit_mul_pow_of_lt hj, ← sum_digit_mul_pow_of_lt hj']
  simp [Finset.sum_range_succ, e0, e1]

/-- **Proposition P** (ledger R-082 (3)): for `u = 1 + p ^ a x + p ^ b y` with `a < b` the tower
`(T_0, T_1)` is adapted with `γ = (a, (p - 1) a + b + 1)`. -/
theorem propP_adapted [Nontrivial R] {a b : ℕ} (hab : a < b) :
    AdaptedTower p (frob p) 2 (towerP p (R := R) a b) (gammaP p a b) (wP p a b) (uP p a b) := by
  have hp2 := hp.out.two_le
  refine ⟨fun j hj => ?_, ?_⟩
  · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · have hm : (T0P (R := R)).Monic := by
        rw [T0P, ← map_one Polynomial.C]; exact Polynomial.monic_X_sub_C 1
      rw [towerP_zero]
      refine ⟨hm, ?_, ?_, ?_⟩
      · rw [pow_zero, T0P, ← map_one Polynomial.C, Polynomial.natDegree_X_sub_C]
      · exact sub_mem (X_mem_BPoly _) (one_mem _)
      · simp only [gammaP, wP, if_pos rfl]
        exact eval_T0P p hab.le
    · have hX1 : (Polynomial.X - 1 : Polynomial (MvPowerSeries (Fin 2) R)).Monic := by
        rw [← map_one Polynomial.C]; exact Polynomial.monic_X_sub_C 1
      have hdeg1 : (Polynomial.X - 1 : Polynomial (MvPowerSeries (Fin 2) R)).natDegree = 1 := by
        rw [← map_one Polynomial.C, Polynomial.natDegree_X_sub_C]
      have hpow : ((Polynomial.X - 1 : Polynomial (MvPowerSeries (Fin 2) R)) ^ p).natDegree = p := by
        rw [hX1.natDegree_pow, hdeg1, mul_one]
      have hm : (T1P p (R := R) a b).Monic := by
        refine (hX1.pow p).sub_of_left ?_
        refine lt_of_le_of_lt Polynomial.degree_C_le ?_
        rw [Polynomial.degree_eq_natDegree (hX1.pow p).ne_zero, hpow]
        exact_mod_cast hp.out.pos
      rw [towerP_one]
      refine ⟨hm, ?_, ?_, ?_⟩
      · rw [pow_one, T1P, Polynomial.natDegree_sub_C, hpow]
      · rw [T1P]
        refine sub_mem (pow_mem (sub_mem (X_mem_BPoly _) (one_mem _)) _) ?_
        have : (p : MvPowerSeries (Fin 2) R) ^ (p * a) * X 0 ^ p
            + (p : MvPowerSeries (Fin 2) R) ^ (p * b) * X 1 ^ p
            = frob p ((p : MvPowerSeries (Fin 2) R) ^ (p * a) * X 0
              + (p : MvPowerSeries (Fin 2) R) ^ (p * b) * X 1) := by
          simp [map_add, map_mul, map_pow, map_natCast, frob_X]
        rw [this]; exact C_mem_BPoly _ _
      · simp only [gammaP, wP, one_ne_zero, if_false]
        exact eval_T1P p hab
  · exact pIndep_of_monomial p (clsP p) (fun j _ => dvd_towerVal_sub p hab j)
      (fun j hj j' hj' hne => clsP_distinct p j j' (by simpa using hj) (by simpa using hj') hne)

theorem digitVal_gammaP (a b m : ℕ) :
    digitVal p 2 (gammaP p a b) m = digit p 0 m * a + digit p 1 m * ((p - 1) * a + b + 1) := by
  simp [digitVal, Finset.sum_range_succ, gammaP]

/-- **Proposition P with Theorem A'**: for `u = 1 + p ^ a x + p ^ b y`, `a < b`, `f = 1/u` and
every `k ≥ 1`, `L_f(p, k) + 1 = min(p ^ 2, min {m : e_0(m) a + e_1(m) ((p - 1) a + b + 1) ≥ k})`. -/
theorem levelCount_propP [Nontrivial R] (htor : NoPTorsion p R) (hpu : ¬ IsUnit (p : R))
    {a b : ℕ} (hab : a < b) {f : MvPowerSeries (Fin 2) R} (hfu : f * uP p a b = 1) {k : ℕ}
    (hk : 1 ≤ k) :
    levelCount p (frob p) f k + 1
      = sInf {m | p ^ 2 ≤ m ∨ k ≤ digit p 0 m * a + digit p 1 m * ((p - 1) * a + b + 1)} := by
  have hpuA : ¬ IsUnit (p : MvPowerSeries (Fin 2) R) := by
    have := not_isUnit_pow_mvPowerSeries p (τ := Fin 2) hpu (le_refl 1)
    rwa [pow_one] at this
  have hcap : MonicAnn p (frob p) (uP p (R := R) a b) k (p ^ 2) := by
    have hs : ∀ a : MvPowerSeries (Fin 2) R, ∃ c : (Fin 2 →₀ ℕ) → MvPowerSeries (Fin 2) R,
        a = ∑ e ∈ digitExps p 2, frob p (c e) * (monomial e 1 : MvPowerSeries (Fin 2) R) :=
      fun a => span_digit p a
    have := monicAnn_of_span (p := p) (digitExps p 2)
      (fun e => (monomial e 1 : MvPowerSeries (Fin 2) R)) hs (uP p a b) k
    rwa [card_digitExps] at this
  rw [levelCount_eq_digit (noPTorsion_mvPowerSeries p htor) (psat_frob p) hpuA
    (propP_adapted p hab) (by rw [hfu, sub_self]; exact dvd_zero _)
    (not_isUnit_pow_mvPowerSeries p hpu hk) hcap]
  simp only [digitVal_gammaP]

/-- The ledger's setting `ℤ_[p][[x, y]]`. -/
theorem levelCount_propP_padic {a b : ℕ} (hab : a < b) {f : MvPowerSeries (Fin 2) ℤ_[p]}
    (hfu : f * uP p a b = 1) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) f k + 1
      = sInf {m | p ^ 2 ≤ m ∨ k ≤ digit p 0 m * a + digit p 1 m * ((p - 1) * a + b + 1)} :=
  levelCount_propP p (padicInt_noPTorsion p) (padicInt_not_isUnit p) hab hfu hk

end PropP

/-! ## The refutation of C3 (ledger R-082 (1)) -/

section Counter

/-- The ledger's displayed relation at `p = 2`: `P(X) = (X - 1) ^ 2 - 4 x ^ 2` is monic of
degree `2`, lies in `B[X]`, and `P(1 + 2x + 4y) = 16 (x y + y ^ 2)`. -/
theorem ce_two_relation {R : Type*} [CommRing R] [Nontrivial R] :
    let P : Polynomial (MvPowerSeries (Fin 2) R) :=
      (Polynomial.X - 1) ^ 2 - Polynomial.C (4 * MvPowerSeries.X 0 ^ 2)
    P.Monic ∧ P.natDegree = 2 ∧ P ∈ BPoly (frob 2) ∧
      P.eval (1 + 2 * MvPowerSeries.X 0 + 4 * MvPowerSeries.X 1)
        = 16 * (MvPowerSeries.X 0 * MvPowerSeries.X 1 + MvPowerSeries.X 1 ^ 2) := by
  intro P
  have hX1 : (Polynomial.X - 1 : Polynomial (MvPowerSeries (Fin 2) R)).Monic := by
    rw [← map_one Polynomial.C]; exact Polynomial.monic_X_sub_C 1
  have hdeg : ((Polynomial.X - 1 : Polynomial (MvPowerSeries (Fin 2) R)) ^ 2).natDegree = 2 := by
    rw [hX1.natDegree_pow, ← map_one Polynomial.C, Polynomial.natDegree_X_sub_C]
  refine ⟨(hX1.pow 2).sub_of_left ?_, by rw [Polynomial.natDegree_sub_C, hdeg], ?_, ?_⟩
  · refine lt_of_le_of_lt Polynomial.degree_C_le ?_
    rw [Polynomial.degree_eq_natDegree (hX1.pow 2).ne_zero, hdeg]; exact_mod_cast (by norm_num : 0 < 2)
  · refine sub_mem (pow_mem (sub_mem (X_mem_BPoly _) (one_mem _)) _) ?_
    have : (4 * MvPowerSeries.X 0 ^ 2 : MvPowerSeries (Fin 2) R)
        = frob 2 (4 * MvPowerSeries.X 0) := by rw [map_mul, map_ofNat, frob_X]
    rw [this]; exact C_mem_BPoly _ _
  · simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_C]; ring

/-- The ledger's displayed relation at `p = 3`: `(X - 1) ^ 3 - 27 x ^ 3` at `1 + 3x + 9y` is
`3 ^ 5 (x ^ 2 y + 3 x y ^ 2 + 3 y ^ 3)`. -/
theorem ce_three_relation {R : Type*} [CommRing R] [Nontrivial R] :
    let P : Polynomial (MvPowerSeries (Fin 2) R) :=
      (Polynomial.X - 1) ^ 3 - Polynomial.C (27 * MvPowerSeries.X 0 ^ 3)
    P.Monic ∧ P.natDegree = 3 ∧ P ∈ BPoly (frob 3) ∧
      P.eval (1 + 3 * MvPowerSeries.X 0 + 9 * MvPowerSeries.X 1)
        = 3 ^ 5 * (MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1
          + 3 * MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ 2 + 3 * MvPowerSeries.X 1 ^ 3) := by
  intro P
  have hX1 : (Polynomial.X - 1 : Polynomial (MvPowerSeries (Fin 2) R)).Monic := by
    rw [← map_one Polynomial.C]; exact Polynomial.monic_X_sub_C 1
  have hdeg : ((Polynomial.X - 1 : Polynomial (MvPowerSeries (Fin 2) R)) ^ 3).natDegree = 3 := by
    rw [hX1.natDegree_pow, ← map_one Polynomial.C, Polynomial.natDegree_X_sub_C]
  refine ⟨(hX1.pow 3).sub_of_left ?_, by rw [Polynomial.natDegree_sub_C, hdeg], ?_, ?_⟩
  · refine lt_of_le_of_lt Polynomial.degree_C_le ?_
    rw [Polynomial.degree_eq_natDegree (hX1.pow 3).ne_zero, hdeg]; exact_mod_cast (by norm_num : 0 < 3)
  · refine sub_mem (pow_mem (sub_mem (X_mem_BPoly _) (one_mem _)) _) ?_
    have : (27 * MvPowerSeries.X 0 ^ 3 : MvPowerSeries (Fin 2) R)
        = frob 3 (27 * MvPowerSeries.X 0) := by rw [map_mul, map_ofNat, frob_X]
    rw [this]; exact C_mem_BPoly _ _
  · simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_C]; ring

theorem uP_two : uP 2 1 2 = (1 + 2 * X 0 + 4 * X 1 : MvPowerSeries (Fin 2) ℤ_[2]) := by
  simp only [uP]; norm_num

theorem uP_three : uP 3 1 2 = (1 + 3 * X 0 + 9 * X 1 : MvPowerSeries (Fin 2) ℤ_[3]) := by
  simp only [uP]; norm_num

/-- **C3 is false, `p = 2`** (ledger R-082 (1)): for `f = 1/(1 + 2x + 4y)` in `ℤ_[2][[x, y]]`,
`L_f(2, 4) + 1 = 2`; the depth-relation (A5) bound is `3` (ledger; A5 is not formalized). -/
theorem ce_two {f : MvPowerSeries (Fin 2) ℤ_[2]} (hf : f * (1 + 2 * X 0 + 4 * X 1) = 1) :
    levelCount 2 (frob 2) f 4 + 1 = 2 := by
  rw [levelCount_propP_padic 2 (by norm_num : 1 < 2) (by rw [uP_two]; exact hf) (by norm_num)]
  apply le_antisymm
  · exact Nat.sInf_le (Or.inr (by norm_num [digit]))
  · refine le_csInf ⟨4, Or.inl (by norm_num)⟩ fun m hm => ?_
    by_contra h
    push Not at h
    interval_cases m <;> norm_num [digit] at hm

/-- **C3 is false, `p = 3`** (ledger R-082 (1)): for `f = 1/(1 + 3x + 9y)` in `ℤ_[3][[x, y]]`,
`L_f(3, 5) + 1 = 3`; the A5 bound is `4` (ledger). -/
theorem ce_three {f : MvPowerSeries (Fin 2) ℤ_[3]} (hf : f * (1 + 3 * X 0 + 9 * X 1) = 1) :
    levelCount 3 (frob 3) f 5 + 1 = 3 := by
  rw [levelCount_propP_padic 3 (by norm_num : 1 < 2) (by rw [uP_three]; exact hf) (by norm_num)]
  apply le_antisymm
  · exact Nat.sInf_le (Or.inr (by norm_num [digit]))
  · refine le_csInf ⟨9, Or.inl (by norm_num)⟩ fun m hm => ?_
    by_contra h
    push Not at h
    interval_cases m <;> norm_num [digit] at hm

/-- The full count for `f = 1/(1 + 2x + 4y)`, `p = 2`, every `k ≥ 1`:
`L + 1 = 1, 2, 2, 2, 3, 4, 4, ...` (`k = 1, 2, 3, 4, 5, 6, ...`). -/
theorem ce_two_all {f : MvPowerSeries (Fin 2) ℤ_[2]} (hf : f * (1 + 2 * X 0 + 4 * X 1) = 1)
    {k : ℕ} (hk : 1 ≤ k) :
    levelCount 2 (frob 2) f k + 1
      = if k ≤ 1 then 1 else if k ≤ 4 then 2 else if k = 5 then 3 else 4 := by
  rw [levelCount_propP_padic 2 (by norm_num : 1 < 2) (by rw [uP_two]; exact hf) hk]
  have key : ∀ m0, m0 ∈ {m | 2 ^ 2 ≤ m ∨ k ≤ digit 2 0 m * 1 + digit 2 1 m * ((2 - 1) * 1 + 2 + 1)}
      → (∀ m < m0, m ∉ {m | 2 ^ 2 ≤ m ∨ k ≤ digit 2 0 m * 1 + digit 2 1 m * ((2 - 1) * 1 + 2 + 1)})
      → sInf {m | 2 ^ 2 ≤ m ∨ k ≤ digit 2 0 m * 1 + digit 2 1 m * ((2 - 1) * 1 + 2 + 1)} = m0 :=
    fun m0 h1 h2 => le_antisymm (Nat.sInf_le h1)
      (le_csInf ⟨m0, h1⟩ fun m hm => by by_contra h; push Not at h; exact h2 m h hm)
  split_ifs with h1 h2 h3
  · exact key 1 (Or.inr (by norm_num [digit]; omega)) fun m hm => by
      interval_cases m; norm_num [digit]; omega
  · exact key 2 (Or.inr (by norm_num [digit]; omega)) fun m hm => by
      interval_cases m <;> norm_num [digit] <;> omega
  · exact key 3 (Or.inr (by norm_num [digit]; omega)) fun m hm => by
      interval_cases m <;> norm_num [digit] <;> omega
  · exact key 4 (Or.inl (by norm_num)) fun m hm => by
      interval_cases m <;> norm_num [digit] <;> omega

end Counter

end FrobLevel
