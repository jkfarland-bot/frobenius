module

/-
Run r25, seat L8: **R-087 Lemma D1 (linear test) for EVERY Frobenius lift** of
`A = ℤ_[p][[x_1..x_n]]`, including lifts with `h_i(0) ≠ 0` (σ need not fix the origin), and its
consequence **"B monomial ⟹ Λ idempotent"** (note Proposition `monotests` (a), second sentence).

Setting: `σ : A →+* A` is ANY ring endomorphism with `p ∣ σ a - a ^ p` (no continuity, no
`ℤ_[p]`-linearity assumed), and `h_i` is any element with `σ(x_i) = x_i ^ p + p h_i` (it exists
by the Frobenius congruence; `h_i(0)` is arbitrary).

* `sigma_C_sub`: every ring endomorphism moves constants only by `p ^ 2 A`:
  `σ(C c) - C c ∈ p ^ 2 A` (from `c ≡ N (mod p ^ 2)`, `N ∈ ℕ`).
* `coeff_single_sigma`: `[σ m]_{x_j} ≡ p ∑_i m_i (h_i)_j (mod p ^ 2)`.
* `d1_linear_test_gen`: if `m ^ p ∈ B` then `∑_i m_i (h_i)_j ≡ m(0) ^ (p - 1) m_j (mod p)`
  (this is `Λ(l) = c̄ ^ (p - 1) l`). L6's `d1_linear_test` is the case `σ = frobForm h`, `h_i(0) = 0`.
* `lambda_idempotent`: if `m_1, ..., m_n` have `m_i ^ p ∈ B` and the matrix of linear parts of
  `m̄_i` is invertible over `𝔽_p` (the `t_i` of note Definition `monomial` are coordinates), then
  the matrix `Λ_{ij} = (h̄_i)_{x_j}` satisfies `Λ * Λ = Λ`.
* `liftPY_not_monomial`: for `σ = (x ^ p + p y, y ^ p)` no such `m_1, m_2` exist: the image is not
  monomial in any coordinates (note, consequences of Proposition `monotests`).
* `oneVar_not_monomial`: one variable, `σ(x) = x ^ p + p h` with `(h)_x ≢ 0, 1 (mod p)`: no `m`
  with `m ^ p ∈ B` has a linear part that is a unit mod `p`; e.g. `x ^ 3 + 6x` (`threeSixX_not_monomial`).

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.PropT
public import Frobenius.Levels.G1
public import Frobenius.Levels.G1Series
public import Frobenius.Levels.ThmR
public import Frobenius.Levels.Lifts
public import Frobenius.Levels.D1Linear

@[expose] public section

-- Port (Mathlib v4.35.0-rc2): restore the v4.33 instance path for `AddCommGroup (ZMod p)`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace FrobLevel

open MvPowerSeries

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

/-! ### Elements whose constant and linear coefficients are divisible by `q` -/

/-- `q` divides the constant and every linear coefficient of `f`. -/
def SmallC (q : ℤ_[p]) (f : MvPowerSeries (Fin n) ℤ_[p]) : Prop :=
  q ∣ constantCoeff f ∧ ∀ j, q ∣ coeff (Finsupp.single j 1) f

theorem SmallC.mul {q₁ q₂ : ℤ_[p]} {a b : MvPowerSeries (Fin n) ℤ_[p]} (ha : SmallC q₁ a)
    (hb : SmallC q₂ b) : SmallC (q₁ * q₂) (a * b) := by
  refine ⟨by rw [map_mul]; exact mul_dvd_mul ha.1 hb.1, fun j => ?_⟩
  rw [coeff_single_mul, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply]
  exact dvd_add (mul_dvd_mul ha.1 (hb.2 j)) (mul_dvd_mul (ha.2 j) hb.1)

theorem SmallC.mul_right {q : ℤ_[p]} {a : MvPowerSeries (Fin n) ℤ_[p]} (ha : SmallC q a)
    (b : MvPowerSeries (Fin n) ℤ_[p]) : SmallC q (a * b) := by
  refine ⟨by rw [map_mul]; exact dvd_mul_of_dvd_left ha.1 _, fun j => ?_⟩
  rw [coeff_single_mul, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply]
  exact dvd_add (dvd_mul_of_dvd_left ha.1 _) (dvd_mul_of_dvd_left (ha.2 j) _)

theorem SmallC.add {q : ℤ_[p]} {a b : MvPowerSeries (Fin n) ℤ_[p]} (ha : SmallC q a)
    (hb : SmallC q b) : SmallC q (a + b) :=
  ⟨by rw [map_add]; exact dvd_add ha.1 hb.1, fun j => by rw [map_add]; exact dvd_add (ha.2 j) (hb.2 j)⟩

theorem SmallC.zero (q : ℤ_[p]) : SmallC q (0 : MvPowerSeries (Fin n) ℤ_[p]) :=
  ⟨by simp, fun j => by simp⟩

theorem SmallC.sum {q : ℤ_[p]} {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries (Fin n) ℤ_[p])
    (hf : ∀ i ∈ s, SmallC q (f i)) : SmallC q (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SmallC.zero q
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem SmallC.natCast_pow_mul (K : ℕ) (w : MvPowerSeries (Fin n) ℤ_[p]) :
    SmallC ((p : ℤ_[p]) ^ K) (((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ K * w) := by
  have hC : ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ K = C ((p : ℤ_[p]) ^ K) := by
    rw [map_pow, map_natCast]
  rw [hC]
  refine ⟨by rw [map_mul, constantCoeff_C]; exact dvd_mul_right _ _, fun j => ?_⟩
  rw [coeff_C_mul]; exact dvd_mul_right _ _

/-! ### Decomposition of series with zero constant term -/

theorem exists_eq_sum_X_mul (f : MvPowerSeries (Fin n) ℤ_[p]) (hf : constantCoeff f = 0) :
    ∃ g : Fin n → MvPowerSeries (Fin n) ℤ_[p], f = ∑ i, X i * g i ∧
      ∀ i, constantCoeff (g i) = coeff (Finsupp.single i 1) f := by
  classical
  let g : Fin n → MvPowerSeries (Fin n) ℤ_[p] := fun i d =>
    if (∀ j, j < i → d j = 0) then coeff (d + Finsupp.single i 1) f else 0
  refine ⟨g, ?_, fun i => ?_⟩
  · ext e
    rw [map_sum]
    have hterm : ∀ i, coeff e (X i * g i)
        = if (1 ≤ e i ∧ ∀ j, j < i → e j = 0) then coeff e f else 0 := by
      intro i
      rw [X_def, coeff_monomial_mul, one_mul]
      by_cases hi : 1 ≤ e i
      · have hle : Finsupp.single i 1 ≤ e := by
          intro k
          by_cases hk : k = i
          · subst hk; simpa using hi
          · simp [Finsupp.single_apply, Ne.symm hk]
        rw [if_pos hle]
        have hsub : ∀ j, j < i → (e - Finsupp.single i 1 : Fin n →₀ ℕ) j = e j := by
          intro j hj
          rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (ne_of_lt hj).symm, Nat.sub_zero]
        have hadd : e - Finsupp.single i 1 + Finsupp.single i 1 = e := tsub_add_cancel_of_le hle
        show (if (∀ j, j < i → (e - Finsupp.single i 1 : Fin n →₀ ℕ) j = 0) then
            coeff (e - Finsupp.single i 1 + Finsupp.single i 1) f else 0) = _
        rw [hadd]
        by_cases hc : ∀ j, j < i → e j = 0
        · rw [if_pos (fun j hj => by rw [hsub j hj]; exact hc j hj), if_pos ⟨hi, hc⟩]
        · rw [if_neg (fun h' => hc fun j hj => by rw [← hsub j hj]; exact h' j hj),
            if_neg (fun h' => hc h'.2)]
      · have hnle : ¬ Finsupp.single i 1 ≤ e := by
          intro h'; have := h' i; simp at this; omega
        rw [if_neg hnle, if_neg (fun h' => hi h'.1)]
    simp only [hterm]
    by_cases he : e = 0
    · subst he
      simp only [Finsupp.coe_zero, Pi.zero_apply, nonpos_iff_eq_zero, one_ne_zero, false_and,
        if_false, Finset.sum_const_zero]
      rw [coeff_zero_eq_constantCoeff_apply, hf]
    · have hS : (Finset.univ.filter fun i => e i ≠ 0).Nonempty := by
        by_contra hS
        rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hS
        exact he (Finsupp.ext fun i => by simpa using hS (Finset.mem_univ i))
      set i0 := (Finset.univ.filter fun i => e i ≠ 0).min' hS with hi0
      have hi0mem : e i0 ≠ 0 := (Finset.mem_filter.1 (Finset.min'_mem _ hS)).2
      have hcond : ∀ i, (1 ≤ e i ∧ ∀ j, j < i → e j = 0) ↔ i = i0 := by
        intro i
        constructor
        · rintro ⟨h1, h2⟩
          have hmem : i ∈ Finset.univ.filter fun i => e i ≠ 0 :=
            Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩
          have hle : i0 ≤ i := Finset.min'_le _ _ hmem
          rcases lt_or_eq_of_le hle with hlt | heq
          · exact absurd (h2 i0 hlt) hi0mem
          · exact heq.symm
        · rintro rfl
          refine ⟨by omega, fun j hj => ?_⟩
          by_contra hne
          have hmem : j ∈ Finset.univ.filter fun i => e i ≠ 0 :=
            Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩
          exact absurd (Finset.min'_le _ _ hmem) (not_le.2 hj)
      simp only [hcond]
      rw [Finset.sum_ite_eq' Finset.univ i0, if_pos (Finset.mem_univ _)]
  · rw [← coeff_zero_eq_constantCoeff_apply]
    show (if (∀ j, j < i → (0 : Fin n →₀ ℕ) j = 0) then coeff (0 + Finsupp.single i 1) f else 0) = _
    simp

/-! ### Linear coefficients of `σ(m)` modulo `p ^ 2`, every lift -/

section AnyLift

variable {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}

/-- Every ring endomorphism of `ℤ_[p][[x]]` moves constants only by `p ^ 2 A`. -/
theorem sigma_C_sub (c : ℤ_[p]) : ∃ w : MvPowerSeries (Fin n) ℤ_[p],
    σ (C c) - C c = ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ 2 * w := by
  have h := PadicInt.appr_spec 2 c
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨e₀, he⟩ := h
  obtain ⟨N, e, hNe⟩ : ∃ N : ℕ, ∃ e : ℤ_[p], c = (N : ℤ_[p]) + (p : ℤ_[p]) ^ 2 * e :=
    ⟨c.appr 2, e₀, by rw [← he]; ring⟩
  have hc : C c = ((N : ℕ) : MvPowerSeries (Fin n) ℤ_[p])
      + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ 2 * C e := by
    rw [hNe]
    simp [map_add, map_mul, map_pow, map_natCast]
  refine ⟨σ (C e) - C e, ?_⟩
  rw [hc, map_add, map_mul, map_pow, map_natCast, map_natCast]
  ring

theorem smallC_sigma_X (hσ : IsFrobLift p σ) (i : Fin n) : SmallC (p : ℤ_[p]) (σ (X i)) := by
  obtain ⟨w, hw⟩ := hσ (X i)
  have : σ (X i) = X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ 1 * w := by
    rw [pow_one, ← hw]; ring
  have h2 := SmallC.natCast_pow_mul (p := p) 1 w
  simp only [pow_one] at h2
  rw [this, pow_one]
  refine ⟨?_, fun j => ?_⟩
  · rw [map_add, map_pow, constantCoeff_X, zero_pow hp.out.ne_zero, zero_add]; exact h2.1
  · rw [map_add, coeff_single_X_pow, zero_add]; exact h2.2 j

theorem smallC_sigma_of_const_zero (hσ : IsFrobLift p σ) {g : MvPowerSeries (Fin n) ℤ_[p]}
    (hg : constantCoeff g = 0) : SmallC (p : ℤ_[p]) (σ g) := by
  obtain ⟨g', hg', -⟩ := exists_eq_sum_X_mul g hg
  rw [hg', map_sum]
  exact SmallC.sum _ _ fun i _ => by rw [map_mul]; exact (smallC_sigma_X hσ i).mul_right _

theorem smallC_sigma_rest2 (hσ : IsFrobLift p σ) (m : MvPowerSeries (Fin n) ℤ_[p]) :
    SmallC ((p : ℤ_[p]) * (p : ℤ_[p])) (σ (rest2 m)) := by
  have ho := order_two_le_rest m
  have h0 : constantCoeff (rest2 m) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    apply coeff_of_lt_order
    exact lt_of_lt_of_le (by simp) ho
  have h1 : ∀ i, coeff (Finsupp.single i 1) (rest2 m) = 0 := by
    intro i
    apply coeff_of_lt_order
    rw [Finsupp.degree_single]
    exact lt_of_lt_of_le (by norm_num) ho
  obtain ⟨g, hg, hg0⟩ := exists_eq_sum_X_mul (rest2 m) h0
  rw [hg, map_sum]
  refine SmallC.sum _ _ fun i _ => ?_
  rw [map_mul]
  exact (smallC_sigma_X hσ i).mul (smallC_sigma_of_const_zero hσ (by rw [hg0 i, h1 i]))

/-- **Linear coefficients of `σ(m)`**, every lift: `[σ m]_{x_j} ≡ p ∑_i m_i (h_i)_j (mod p ^ 2)`
whenever `σ(x_i) = x_i ^ p + p h_i`. -/
theorem coeff_single_sigma (hσ : IsFrobLift p σ) (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (hh : ∀ i, σ (X i) = X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * h i)
    (m : MvPowerSeries (Fin n) ℤ_[p]) (j : Fin n) :
    (p : ℤ_[p]) * (p : ℤ_[p]) ∣ coeff (Finsupp.single j 1) (σ m)
      - p * ∑ i, coeff (Finsupp.single i 1) m * coeff (Finsupp.single j 1) (h i) := by
  set P := ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) with hP
  have hpp : (p : ℤ_[p]) * (p : ℤ_[p]) = (p : ℤ_[p]) ^ 2 := by ring
  obtain ⟨w0, hw0⟩ := sigma_C_sub (σ := σ) (coeff 0 m)
  have hwi : ∀ i, ∃ w, σ (C (coeff (Finsupp.single i 1) m)) - C (coeff (Finsupp.single i 1) m)
      = P ^ 2 * w := fun i => sigma_C_sub _
  choose w hw using hwi
  -- `σ m = main + D` with `D` small modulo `p ^ 2`
  have hsplit : σ m = (C (coeff 0 m) + ∑ i, C (coeff (Finsupp.single i 1) m) * (X i ^ p + P * h i))
      + (P ^ 2 * w0 + ∑ i, P ^ 2 * w i * σ (X i) + σ (rest2 m)) := by
    conv_lhs => rw [eq_rest m]
    rw [map_add, map_add, map_sum]
    have e0 : σ (C (coeff 0 m)) = C (coeff 0 m) + P ^ 2 * w0 := by rw [← hw0]; ring
    have ei : ∀ i, σ (C (coeff (Finsupp.single i 1) m) * X i)
        = C (coeff (Finsupp.single i 1) m) * (X i ^ p + P * h i) + P ^ 2 * w i * σ (X i) := by
      intro i
      rw [map_mul, ← hh i]
      have := hw i
      rw [sub_eq_iff_eq_add] at this
      rw [this]; ring
    rw [e0, Finset.sum_congr rfl fun i _ => ei i, Finset.sum_add_distrib]
    ring
  have hD : SmallC ((p : ℤ_[p]) * (p : ℤ_[p])) (P ^ 2 * w0 + ∑ i, P ^ 2 * w i * σ (X i) + σ (rest2 m)) := by
    refine ((?_ : SmallC _ _).add (SmallC.sum _ _ fun i _ => ?_)).add (smallC_sigma_rest2 hσ m)
    · rw [hpp]; exact SmallC.natCast_pow_mul 2 w0
    · rw [hpp, mul_assoc]; exact SmallC.natCast_pow_mul 2 _
  have hmain : coeff (Finsupp.single j 1)
      (C (coeff 0 m) + ∑ i, C (coeff (Finsupp.single i 1) m) * (X i ^ p + P * h i))
      = p * ∑ i, coeff (Finsupp.single i 1) m * coeff (Finsupp.single j 1) (h i) := by
    rw [map_add, coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero), zero_add, map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_C_mul, map_add, coeff_single_X_pow, zero_add, hP,
      ← map_natCast (C (σ := Fin n) (R := ℤ_[p])), coeff_C_mul]
    ring
  rw [hsplit, map_add, hmain, add_sub_cancel_left]
  exact hD.2 j

/-- **R-087 Lemma D1, linear test, every lift** (note Proposition `monotests` (a)): if
`σ(x_i) = x_i ^ p + p h_i` (any `h_i`, `h_i(0)` arbitrary) and `m ^ p ∈ B`, then for every `j`,
`∑_i m_i (h_i)_j ≡ m(0) ^ (p - 1) m_j (mod p)`. -/
theorem d1_linear_test_gen (hσ : IsFrobLift p σ) (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (hh : ∀ i, σ (X i) = X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * h i)
    {m : MvPowerSeries (Fin n) ℤ_[p]} (hm : m ^ p ∈ frobImage σ) (j : Fin n) :
    (p : ℤ_[p]) ∣ ∑ i, coeff (Finsupp.single i 1) m * coeff (Finsupp.single j 1) (h i)
      - constantCoeff m ^ (p - 1) * coeff (Finsupp.single j 1) m := by
  obtain ⟨b, hb⟩ := (pow_mem_iff_delta_mem_series hσ m).1 hm
  have hσb : (p : ℤ_[p]) ∣ coeff (Finsupp.single j 1) (σ b) := by
    obtain ⟨w, hw⟩ := hσ b
    have : σ b = b ^ p + (p : MvPowerSeries (Fin n) ℤ_[p]) * w := by rw [← hw]; ring
    rw [this, map_add, coeff_single_pow, ← map_natCast (C (σ := Fin n) (R := ℤ_[p])),
      coeff_C_mul]
    exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) (dvd_mul_right _ _)
  rw [hb] at hσb
  obtain ⟨y, hy⟩ := hσb
  -- `p [δ m]_j = [σ m]_j - [m ^ p]_j`
  have hpd := p_mul_delta hσ m
  have hj := congrArg (coeff (Finsupp.single j 1)) hpd
  rw [← map_natCast (C (σ := Fin n) (R := ℤ_[p])), coeff_C_mul, map_sub, coeff_single_pow,
    coeff_zero_eq_constantCoeff_apply, hy] at hj
  obtain ⟨z, hz⟩ := coeff_single_sigma hσ h hh m j
  set S := ∑ i, coeff (Finsupp.single i 1) m * coeff (Finsupp.single j 1) (h i)
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  refine ⟨y - z, ?_⟩
  apply mul_left_cancel₀ hp0
  have : coeff (Finsupp.single j 1) (σ m) = (p : ℤ_[p]) * S + p * p * z := by
    rw [← hz]; ring
  rw [this] at hj
  linear_combination (-1 : ℤ_[p]) * hj

end AnyLift

/-! ### `B` monomial ⟹ `Λ` idempotent -/

section Idem

/-- The matrix of `Λ` over `𝔽_p`: `Λ(∑_i a_i x_i) = ∑_i a_i [h̄_i]_1`, i.e. row vectors times
`Λmat h` with `(Λmat h)_{ij} = (h̄_i)_{x_j}`. -/
noncomputable def Λmat (h : Fin n → MvPowerSeries (Fin n) ℤ_[p]) : Matrix (Fin n) (Fin n) (ZMod p) :=
  fun i j => PadicInt.toZMod (coeff (Finsupp.single j 1) (h i))

/-- The matrix of linear parts of `m̄_1, ..., m̄_n`. -/
noncomputable def linMat (m : Fin n → MvPowerSeries (Fin n) ℤ_[p]) :
    Matrix (Fin n) (Fin n) (ZMod p) :=
  fun i j => PadicInt.toZMod (coeff (Finsupp.single j 1) (m i))

theorem zmod_pow_sub_one_idem (x : ZMod p) : x ^ (p - 1) * x ^ (p - 1) = x ^ (p - 1) := by
  by_cases hx : x = 0
  · subst hx
    rw [zero_pow (by have := hp.out.two_le; omega), mul_zero]
  · rw [ZMod.pow_card_sub_one_eq_one hx, mul_one]

/-- `M Λ = D M` with `D = diag(c̄_i ^ (p - 1))`, from the linear test. -/
theorem linMat_mul_Λmat {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}
    (hσ : IsFrobLift p σ) (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (hh : ∀ i, σ (X i) = X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * h i)
    (m : Fin n → MvPowerSeries (Fin n) ℤ_[p]) (hm : ∀ i, m i ^ p ∈ frobImage σ) :
    linMat m * Λmat h
      = Matrix.diagonal (fun i => PadicInt.toZMod (constantCoeff (m i)) ^ (p - 1)) * linMat m := by
  ext i j
  rw [Matrix.mul_apply, Matrix.diagonal_mul]
  have := d1_linear_test_gen hσ h hh (hm i) j
  rw [← toZMod_eq_zero_iff, map_sub, map_sum, sub_eq_zero] at this
  simp only [map_mul, map_pow] at this
  show ∑ x, PadicInt.toZMod (coeff (Finsupp.single x 1) (m i))
      * PadicInt.toZMod (coeff (Finsupp.single j 1) (h x))
    = PadicInt.toZMod (constantCoeff (m i)) ^ (p - 1)
      * PadicInt.toZMod (coeff (Finsupp.single j 1) (m i))
  exact this

/-- **"`B` monomial ⟹ `Λ` idempotent"** (note Proposition `monotests` (a), second sentence).
If `m_1, ..., m_n` satisfy `m_i ^ p ∈ B` and their linear parts mod `p` form a basis (the `t_i`
of Definition `monomial` are coordinates), then `Λ ∘ Λ = Λ`. -/
theorem lambda_idempotent {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}
    (hσ : IsFrobLift p σ) (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (hh : ∀ i, σ (X i) = X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * h i)
    (m : Fin n → MvPowerSeries (Fin n) ℤ_[p]) (hm : ∀ i, m i ^ p ∈ frobImage σ)
    (hM : IsUnit (linMat m)) : Λmat h * Λmat h = Λmat h := by
  have hML := linMat_mul_Λmat hσ h hh m hm
  set D := Matrix.diagonal (fun i => PadicInt.toZMod (constantCoeff (m i)) ^ (p - 1))
  have hDD : D * D = D := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i; exact zmod_pow_sub_one_idem _
  apply hM.mul_left_cancel
  rw [← mul_assoc, hML, mul_assoc, hML, ← mul_assoc, hDD]

/-- No `m_1, ..., m_n` with `m_i ^ p ∈ B` and invertible linear parts exist when `Λ` is not
idempotent (contrapositive form, intrinsic to `B`). -/
theorem not_monomial_of_not_idem
    {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}
    (hσ : IsFrobLift p σ) (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (hh : ∀ i, σ (X i) = X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * h i)
    (hn : Λmat h * Λmat h ≠ Λmat h) :
    ¬ ∃ m : Fin n → MvPowerSeries (Fin n) ℤ_[p], (∀ i, m i ^ p ∈ frobImage σ) ∧ IsUnit (linMat m) :=
  fun ⟨m, hm, hM⟩ => hn (lambda_idempotent hσ h hh m hm hM)

end Idem

/-! ### Named verdicts -/

section Named

theorem liftPY_X0 : liftPY (p := p) (X 0) = X 0 ^ p + ((p : ℕ) : MvPowerSeries (Fin 2) ℤ_[p]) * X 1 := by
  unfold liftPY; rw [frobForm_X]; simp

theorem liftPY_X1 : liftPY (p := p) (X 1) = X 1 ^ p + ((p : ℕ) : MvPowerSeries (Fin 2) ℤ_[p]) * 0 := by
  unfold liftPY; rw [frobForm_X]; simp

/-- **`x ^ p + p y`, `y ^ p` has no monomial image** (R-087; note, consequences of Proposition
`monotests`): no `m_1, m_2` with `m_i ^ p ∈ B` have linearly independent linear parts mod `p`.
Here `Λ(x) = y`, `Λ(y) = 0`, so `Λ ^ 2 = 0 ≠ Λ`. -/
theorem liftPY_not_monomial :
    ¬ ∃ m : Fin 2 → MvPowerSeries (Fin 2) ℤ_[p],
      (∀ i, m i ^ p ∈ frobImage (liftPY (p := p))) ∧ IsUnit (linMat m) := by
  let h : Fin 2 → MvPowerSeries (Fin 2) ℤ_[p] := ![X 1, 0]
  refine not_monomial_of_not_idem liftPY_isFrobLift h (fun i => ?_) ?_
  · fin_cases i
    · simpa [h] using liftPY_X0
    · simpa [h] using liftPY_X1
  · intro hc
    have := congrFun (congrFun hc 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Λmat, h] at this
    simp [coeff_X] at this
    exact absurd ((Finsupp.single_left_inj one_ne_zero).1 this) (by decide)

/-- **One variable**: if `σ(x) = x ^ p + p h` with `(h)_x ≢ 0, 1 (mod p)`, then no `m` with
`m ^ p ∈ B` has a linear coefficient that is a unit mod `p`; so `B` is not monomial. -/
theorem oneVar_not_monomial
    {σ : MvPowerSeries (Fin 1) ℤ_[p] →+* MvPowerSeries (Fin 1) ℤ_[p]} (hσ : IsFrobLift p σ)
    (h : MvPowerSeries (Fin 1) ℤ_[p])
    (hh : σ (X 0) = X 0 ^ p + ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p]) * h)
    (hu0 : PadicInt.toZMod (coeff (Finsupp.single 0 1) h) ≠ 0)
    (hu1 : PadicInt.toZMod (coeff (Finsupp.single 0 1) h) ≠ 1) :
    ¬ ∃ m : MvPowerSeries (Fin 1) ℤ_[p], m ^ p ∈ frobImage σ ∧
      PadicInt.toZMod (coeff (Finsupp.single 0 1) m) ≠ 0 := by
  rintro ⟨m, hm, hm1⟩
  have hidem := lambda_idempotent hσ (fun _ => h) (fun i => by fin_cases i; exact hh)
    (fun _ => m) (fun _ => hm) (by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique]
      exact isUnit_iff_ne_zero.2 hm1)
  have := congrFun (congrFun hidem 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Λmat] at this
  set u := PadicInt.toZMod (coeff (Finsupp.single 0 1) h)
  have : u * (u - 1) = 0 := by rw [mul_sub, this, mul_one, sub_self]
  rcases mul_eq_zero.1 this with h0 | h1
  · exact hu0 h0
  · exact hu1 (sub_eq_zero.1 h1)

instance fact_prime_three : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- `x ↦ x ^ 3 + 6 x` over `ℤ_[3][[x]]` (the note's example: no monomial image). -/
noncomputable def threeSixX : MvPowerSeries (Fin 1) ℤ_[3] →+* MvPowerSeries (Fin 1) ℤ_[3] :=
  frobForm (p := 3) (fun _ => (2 : MvPowerSeries (Fin 1) ℤ_[3]) * X 0)
    (fun _ => by rw [map_mul, constantCoeff_X, mul_zero])

theorem threeSixX_not_monomial :
    ¬ ∃ m : MvPowerSeries (Fin 1) ℤ_[3], m ^ 3 ∈ frobImage threeSixX ∧
      PadicInt.toZMod (coeff (Finsupp.single 0 1) m) ≠ 0 := by
  have hc : PadicInt.toZMod (coeff (Finsupp.single (0 : Fin 1) 1)
      ((2 : MvPowerSeries (Fin 1) ℤ_[3]) * X 0)) = 2 := by
    rw [show (2 : MvPowerSeries (Fin 1) ℤ_[3]) = C 2 from (map_ofNat C 2).symm, coeff_C_mul, coeff_X, if_pos rfl,
      mul_one, map_ofNat]
  refine oneVar_not_monomial (frobForm_isFrobLift _ _) ((2 : MvPowerSeries (Fin 1) ℤ_[3]) * X 0)
    (by unfold threeSixX; rw [frobForm_X]) ?_ ?_
  · rw [hc]; decide
  · rw [hc]; decide

end Named

end FrobLevel
