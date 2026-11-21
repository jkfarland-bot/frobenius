module

/-
Run r25, seat L6: **R-087 Lemma D1, the linear test** (note Proposition `prop:monotests` (a)),
for every lift `σ(x_i) = x_i ^ p + p h_i` (`h_i(0) = 0`) of `ℤ_[p][[x_1..x_n]]` (seat L4's
`frobForm`).

`d1_linear_test`: if `m ^ p ∈ B = σ(A)`, `c = m(0)`, `m_i` the coefficient of `x_i` in `m` and
`(h_i)_j` the coefficient of `x_j` in `h_i`, then for every `j`
    `∑_i m_i (h_i)_j ≡ c ^ (p - 1) m_j  (mod p)`.
This is `Λ(l) = c̄ ^ (p - 1) l` for the linear part `l = ∑_i m̄_i x_i` of `m̄ - c̄`, with
`Λ(∑_i a_i x_i) = ∑_i a_i [h̄_i]_1`, written in coordinates. (The note's `m = c + t` with `t` in
the maximal ideal is any `m`, with `c = m(0)`.) L4 proved the first step, `m ^ p ∈ B ↔ δ(m) ∈ B`
(`pow_mem_iff_delta_mem_series`), which is used here.

Helper results: `coeff_single_mul`, `coeff_single_pow` (linear coefficients of products and
powers), `order_two_le_rest` (`m` minus its constant and linear terms has order `≥ 2`),
`coeff_single_frobForm` (`[σ(m)]_{x_j} = p ∑_i m_i (h_i)_j`).

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

@[expose] public section

namespace FrobLevel

open MvPowerSeries

section LinearCoeff

variable {R : Type*} [CommRing R] {n : ℕ}

theorem coeff_single_mul (A B : MvPowerSeries (Fin n) R) (j : Fin n) :
    coeff (Finsupp.single j 1) (A * B)
      = coeff 0 A * coeff (Finsupp.single j 1) B + coeff (Finsupp.single j 1) A * coeff 0 B := by
  rw [coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  rw [show (1 : ℕ) = 0 + 1 from rfl, Finset.Nat.antidiagonal_succ]
  simp [add_comm]

theorem coeff_single_pow (g : MvPowerSeries (Fin n) R) (j : Fin n) (k : ℕ) :
    coeff (Finsupp.single j 1) (g ^ k)
      = (k : R) * coeff 0 g ^ (k - 1) * coeff (Finsupp.single j 1) g := by
  induction k with
  | zero =>
    rw [pow_zero, coeff_one, if_neg (Finsupp.single_ne_zero.2 one_ne_zero)]
    simp
  | succ k ih =>
    rw [pow_succ, coeff_single_mul, ih, coeff_zero_eq_constantCoeff_apply, map_pow,
      ← coeff_zero_eq_constantCoeff_apply]
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      ring

theorem degree_lt_two {d : Fin n →₀ ℕ} (hd : d.degree < 2) :
    d = 0 ∨ ∃ i, d = Finsupp.single i 1 := by
  by_cases h0 : d = 0
  · exact Or.inl h0
  · right
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h; push Not at h; exact h0 (Finsupp.ext h)
    rw [Finsupp.degree_eq_sum] at hd
    have hle : d i ≤ ∑ k, d k := Finset.single_le_sum (fun k _ => Nat.zero_le _)
      (Finset.mem_univ i)
    have hi1 : d i = 1 := by omega
    refine ⟨i, Finsupp.ext fun k => ?_⟩
    by_cases hk : k = i
    · subst hk; simp [hi1]
    · rw [Finsupp.single_apply, if_neg (Ne.symm hk)]
      have h2 : d i + d k ≤ ∑ l, d l := by
        rw [← Finset.sum_pair (f := fun l => d l) (Ne.symm hk)]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      omega

/-- `m` minus its constant and linear terms. -/
noncomputable def rest2 (m : MvPowerSeries (Fin n) R) : MvPowerSeries (Fin n) R :=
  m - C (coeff 0 m) - ∑ i, C (coeff (Finsupp.single i 1) m) * X i

theorem order_two_le_rest (m : MvPowerSeries (Fin n) R) : (2 : ℕ∞) ≤ (rest2 m).order := by
  classical
  apply le_order
  intro d hd
  have hd' : d.degree < 2 := by exact_mod_cast hd
  rcases degree_lt_two hd' with rfl | ⟨j, rfl⟩
  · simp [rest2, coeff_C, coeff_X]
  · rw [rest2, map_sub, map_sub, coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero),
      map_sum, Finset.sum_eq_single j]
    · rw [coeff_C_mul, coeff_X, if_pos rfl]; ring
    · intro i _ hij
      rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
      intro h
      exact hij ((Finsupp.single_left_inj one_ne_zero).1 h).symm
    · intro h; exact absurd (Finset.mem_univ j) h

theorem eq_rest (m : MvPowerSeries (Fin n) R) :
    m = C (coeff 0 m) + ∑ i, C (coeff (Finsupp.single i 1) m) * X i + rest2 m := by
  rw [rest2]; ring

end LinearCoeff

section D1

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

theorem coeff_single_X_pow (i j : Fin n) :
    coeff (Finsupp.single j 1) ((X i : MvPowerSeries (Fin n) ℤ_[p]) ^ p) = 0 := by
  rw [X_pow_eq, coeff_monomial, if_neg]
  intro h
  have := congrArg (· i) h
  have hp2 := hp.out.two_le
  by_cases hji : j = i
  · subst hji; simp at this; omega
  · simp [Finsupp.single_apply, Ne.symm hji] at this; omega

/-- The linear coefficients of `σ(m)` for `σ(x_i) = x_i ^ p + p h_i`. -/
theorem coeff_single_frobForm (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (h0 : ∀ i, constantCoeff (h i) = 0) (m : MvPowerSeries (Fin n) ℤ_[p]) (j : Fin n) :
    coeff (Finsupp.single j 1) (frobForm h h0 m)
      = (p : ℤ_[p]) * ∑ i, coeff (Finsupp.single i 1) m * coeff (Finsupp.single j 1) (h i) := by
  have hrest : coeff (Finsupp.single j 1) (frobForm h h0 (rest2 m)) = 0 := by
    apply coeff_of_lt_order
    have ha := hasSubst_frobForm h h0
    have hle := le_order_subst ha (rest2 m)
    have h1 : (1 : ℕ∞) ≤ ⨅ i, (X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * h i).order := by
      refine le_iInf fun i => ?_
      rw [one_le_order_iff_constCoeff_eq_zero, map_add, map_pow, constantCoeff_X,
        zero_pow hp.out.ne_zero, map_mul, h0, mul_zero, add_zero]
    have h2 : (2 : ℕ∞) ≤ (subst (fun i => X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * h i)
        (rest2 m)).order := by
      refine le_trans ?_ hle
      calc (2 : ℕ∞) = 1 * 2 := by simp
        _ ≤ _ := mul_le_mul' h1 (order_two_le_rest m)
    rw [Finsupp.degree_single]
    unfold frobForm
    rw [substLift_apply]
    exact lt_of_lt_of_le (by norm_num) h2
  conv_lhs => rw [eq_rest m]
  simp only [map_add, map_sum, hrest, add_zero]
  have hC : ∀ c : ℤ_[p], frobForm h h0 (C c) = C c := by
    intro c
    unfold frobForm
    rw [substLift_apply, subst_C]
  rw [hC, coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero), zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hC, frobForm_X, coeff_C_mul, map_add, coeff_single_X_pow, zero_add,
    ← map_natCast (C (σ := Fin n) (R := ℤ_[p])), coeff_C_mul]
  ring

/-- **R-087 Lemma D1, linear test** (note Proposition `monotests` (a)), every lift
`x_i ↦ x_i ^ p + p h_i`: if `m ^ p ∈ B`, then `∑_i m_i (h_i)_j ≡ m(0) ^ (p - 1) m_j (mod p)` for
every `j`. -/
theorem d1_linear_test (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (h0 : ∀ i, constantCoeff (h i) = 0) {m : MvPowerSeries (Fin n) ℤ_[p]}
    (hm : m ^ p ∈ frobImage (frobForm h h0)) (j : Fin n) :
    (p : ℤ_[p]) ∣ ∑ i, coeff (Finsupp.single i 1) m * coeff (Finsupp.single j 1) (h i)
      - constantCoeff m ^ (p - 1) * coeff (Finsupp.single j 1) m := by
  set σ := frobForm h h0 with hσdef
  have hσ : IsFrobLift p σ := frobForm_isFrobLift h h0
  obtain ⟨b, hb⟩ := (pow_mem_iff_delta_mem_series hσ m).1 hm
  -- `p ∣ [σ b]_j`
  have hσb : (p : ℤ_[p]) ∣ coeff (Finsupp.single j 1) (σ b) := by
    obtain ⟨w, hw⟩ := hσ b
    have : σ b = b ^ p + (p : MvPowerSeries (Fin n) ℤ_[p]) * w := by rw [← hw]; ring
    rw [this, map_add, coeff_single_pow, ← map_natCast (C (σ := Fin n) (R := ℤ_[p])),
      coeff_C_mul]
    exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) (dvd_mul_right _ _)
  -- `p [δ m]_j = [σ m]_j - [m ^ p]_j`
  have hpd := p_mul_delta hσ m
  have hj := congrArg (coeff (Finsupp.single j 1)) hpd
  have hsm : coeff (Finsupp.single j 1) (σ m)
      = (p : ℤ_[p]) * ∑ i, coeff (Finsupp.single i 1) m * coeff (Finsupp.single j 1) (h i) :=
    coeff_single_frobForm h h0 m j
  rw [← map_natCast (C (σ := Fin n) (R := ℤ_[p])), coeff_C_mul, map_sub, hsm,
    coeff_single_pow, coeff_zero_eq_constantCoeff_apply] at hj
  rw [hb] at hσb
  obtain ⟨y, hy⟩ := hσb
  refine ⟨y, ?_⟩
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply mul_left_cancel₀ hp0
  rw [mul_sub]
  have : (p : ℤ_[p]) * (p * y)
      = (p : ℤ_[p]) * ∑ i, coeff (Finsupp.single i 1) m * coeff (Finsupp.single j 1) (h i)
        - (p : ℤ_[p]) * constantCoeff m ^ (p - 1) * coeff (Finsupp.single j 1) m := by
    rw [← hy, hj]
  rw [mul_assoc] at this
  rw [← this]

end D1

end FrobLevel
