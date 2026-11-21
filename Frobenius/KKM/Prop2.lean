module

public import Frobenius.KKM.UpperBound

/-!
# The entry of Krattenthaler and Müller's Proposition 2 for the modulus `p ^ (p+1)`

Numbers refer to J. S. Farland, *A proof of a conjecture of Kauers, Krattenthaler and
Müller, and exact level counts for Frobenius lifts* (2026), the larger paper.

Remark 5.4(v). Proposition 2 of C. Krattenthaler and
T. W. Müller (Aequationes Math. 99 (2025)) lists, for the modulus `p ^ (p+1)`, the polynomial

  `P = (t ^ p - t + z) ^ p - p ^ (p-1) (t ^ 2 - t + z)`.

It does not vanish modulo `p ^ (p+1)` at `t = Φ_p(z)`:

* `coeff_two_evalPhi_km25`: for every prime `p ≥ 3` the coefficient of `z ^ 2` in `P(z, Φ_p)` is
  `-p ^ (p-1)`; hence `not_vanishesMod_km25` (`p` odd).
* `coeff_evalPhi_km25p`: with `t ^ p` in place of `t ^ 2`, for every prime `p`, the coefficient of
  `z ^ (2p-1)` is `-p ^ p`; hence `not_vanishesMod_km25p`. For `p = 2` the two polynomials agree
  (`km25_two`), so `coeff_three_evalPhi_km25_two` and `not_vanishesMod_km25_two` cover `P` at `p = 2`.
* `km25fix`, the corrected polynomial `(t ^ p - t + z) ^ p - p ^ (p-1) A_1(z ^ p, t - z)`:
  `km25fix_eq_tower_two` (it is the tower polynomial `A_2` for odd `p`), `evalPhi_km25fix_two`
  (for `p = 2` its value at `Φ` is that of `A_2` plus `8 σ(δ(Φ))`), and `vanishesMod_km25fix`
  (it vanishes modulo `p ^ (p+1)` for every prime `p`).
* `tower_two_two`: for `p = 2`, `A_2 = t^4 - 2t^3 + (2z+3)t^2 - (6z+2)t + 5z^2 + 2z`, and
  `tower_two_two_sub_kkm8`: it agrees modulo `8`, coefficient by coefficient, with the quartic of
  Kauers, Krattenthaler and Müller (2012), Proposition 2, for the modulus `8`.

The key expansion is `X_1 := Φ ^ p - Φ + z = p z ^ (2p-1) + z ^ (2p) r` (`evalPhi_tower_one_eq`).
-/

@[expose] public section

namespace Frobenius.KKM

open PowerSeries

/-! ## The polynomials -/

/-- Krattenthaler and Müller's entry for the modulus `p ^ (p+1)`:
`(t ^ p - t + z) ^ p - p ^ (p-1) (t ^ 2 - t + z)`. -/
noncomputable def km25 (p : ℕ) : Polynomial (Polynomial ℤ) :=
  (Polynomial.X ^ p - Polynomial.X + Polynomial.C Polynomial.X) ^ p -
    Polynomial.C (Polynomial.C ((p : ℤ) ^ (p - 1))) *
      (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C Polynomial.X)

/-- The same with `t ^ p` in place of `t ^ 2`: `(t ^ p - t + z) ^ p - p ^ (p-1) (t ^ p - t + z)`. -/
noncomputable def km25p (p : ℕ) : Polynomial (Polynomial ℤ) :=
  (Polynomial.X ^ p - Polynomial.X + Polynomial.C Polynomial.X) ^ p -
    Polynomial.C (Polynomial.C ((p : ℤ) ^ (p - 1))) *
      (Polynomial.X ^ p - Polynomial.X + Polynomial.C Polynomial.X)

/-- The corrected polynomial `(t ^ p - t + z) ^ p - p ^ (p-1) A_1(z ^ p, t - z)`, with
`A_1(z ^ p, t - z) = (t - z) ^ p - (t - z) + z ^ p`. -/
noncomputable def km25fix (p : ℕ) : Polynomial (Polynomial ℤ) :=
  (Polynomial.X ^ p - Polynomial.X + Polynomial.C Polynomial.X) ^ p -
    Polynomial.C (Polynomial.C ((p : ℤ) ^ (p - 1))) *
      ((Polynomial.X - Polynomial.C Polynomial.X) ^ p - (Polynomial.X - Polynomial.C Polynomial.X) +
        Polynomial.C (Polynomial.X ^ p))

theorem km25_two : km25 2 = km25p 2 := rfl

/-! ## Evaluation at `Φ` -/

theorem evalPhi_X (p : ℕ) : evalPhi p Polynomial.X = Phi p := by
  simp [evalPhi]

theorem evalPhi_C_X (p : ℕ) : evalPhi p (Polynomial.C Polynomial.X) = PowerSeries.X := by
  simp [evalPhi, Polynomial.coe_X]

theorem evalPhi_CC (p : ℕ) (c : ℤ) :
    evalPhi p (Polynomial.C (Polynomial.C c)) = PowerSeries.C c := by
  rw [evalPhi, Polynomial.eval₂_C, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]

/-- `evalPhi` as a ring hom. -/
noncomputable def evalPhiHom (p : ℕ) : Polynomial (Polynomial ℤ) →+* PowerSeries ℤ :=
  Polynomial.eval₂RingHom Polynomial.coeToPowerSeries.ringHom (Phi p)

theorem evalPhiHom_apply (p : ℕ) (A : Polynomial (Polynomial ℤ)) :
    evalPhiHom p A = evalPhi p A := rfl

/-! ## The expansion of `Φ` and of `Φ ^ p - Φ + z` -/

theorem one_add_pow_eq (y : PowerSeries ℤ) (n : ℕ) :
    ∃ h : PowerSeries ℤ, (1 + y) ^ n = 1 + (n : PowerSeries ℤ) * y + y ^ 2 * h := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨h, hh⟩ := ih
    refine ⟨(n : PowerSeries ℤ) + h + y * h, ?_⟩
    rw [pow_succ, hh]
    push_cast
    ring

/-- `Φ_p = z + z ^ p + z ^ (p ^ 2) w`. -/
theorem Phi_eq (p : ℕ) [hp : Fact p.Prime] :
    ∃ w : PowerSeries ℤ, Phi p = X + X ^ p + X ^ (p ^ 2) * w := by
  have hdvd : (X : PowerSeries ℤ) ^ (p ^ 2) ∣ Phi p - X - X ^ p := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    have hp1 : p ≠ 1 := hp.out.ne_one
    have key : m ∈ Set.range (fun k : ℕ => p ^ k) ↔ m = 1 ∨ m = p := by
      constructor
      · rintro ⟨k, rfl⟩
        have hk : k < 2 := (Nat.pow_lt_pow_iff_right hp.out.one_lt).1 hm
        interval_cases k <;> simp
      · rintro (h | h)
        · exact ⟨0, by simp [h]⟩
        · exact ⟨1, by simp [h]⟩
    rw [map_sub, map_sub, coeff_Phi, coeff_X, coeff_X_pow]
    by_cases h1 : m = 1
    · rw [Set.indicator_of_mem (key.2 (Or.inl h1)), Pi.one_apply, ite_eq_left h1, ite_eq_right]
      · simp
      · rw [h1]; exact Ne.symm hp1
    · by_cases h2 : m = p
      · rw [Set.indicator_of_mem (key.2 (Or.inr h2)), Pi.one_apply, ite_eq_right h1, ite_eq_left h2]
        simp
      · rw [Set.indicator_of_notMem (fun h => (key.1 h).elim h1 h2), ite_eq_right h1, ite_eq_right h2]
        simp
  obtain ⟨w, hw⟩ := hdvd
  exact ⟨w, by rw [← hw]; ring⟩

/-- `Φ_p ^ p - Φ_p + z = p z ^ (2p-1) + z ^ (2p) r`, written with `p = n + 2`. -/
theorem evalPhi_tower_one_eq_aux (n : ℕ) [hp : Fact (n + 2).Prime] :
    ∃ r : PowerSeries ℤ, Phi (n + 2) ^ (n + 2) - Phi (n + 2) + X =
      ((n + 2 : ℕ) : PowerSeries ℤ) * X ^ (2 * n + 3) + X ^ (2 * n + 4) * r := by
  obtain ⟨w, hw⟩ := Phi_eq (n + 2)
  set u : PowerSeries ℤ := X + X ^ (n + 2) with hu
  -- `Φ = u + z ^ (2n+4) w'`
  have hΦ : Phi (n + 2) = u + X ^ (2 * n + 4) * (X ^ (n * n + 2 * n) * w) := by
    rw [hw, hu]
    ring
  -- `Φ ^ (n+2) = u ^ (n+2) + z ^ (2n+4) s`
  obtain ⟨s, hs⟩ : (X : PowerSeries ℤ) ^ (2 * n + 4) ∣ Phi (n + 2) ^ (n + 2) - u ^ (n + 2) := by
    refine dvd_trans ?_ (sub_dvd_pow_sub_pow _ _ _)
    exact ⟨X ^ (n * n + 2 * n) * w, by rw [hΦ]; ring⟩
  -- `(1 + z ^ (n+1)) ^ (n+2) = 1 + (n+2) z ^ (n+1) + z ^ (2n+2) h`
  obtain ⟨h, hh⟩ := one_add_pow_eq (X ^ (n + 1)) (n + 2)
  have hu' : u ^ (n + 2) = X ^ (n + 2) * (1 + X ^ (n + 1)) ^ (n + 2) := by
    rw [hu, ← mul_pow]
    ring
  refine ⟨X ^ n * h + s - X ^ (n * n + 2 * n) * w, ?_⟩
  have e1 : Phi (n + 2) ^ (n + 2) = u ^ (n + 2) + X ^ (2 * n + 4) * s := by
    rw [← hs]; ring
  rw [e1, hu', hh, hΦ, hu]
  push_cast
  ring

theorem exists_add_two (p : ℕ) [hp : Fact p.Prime] : ∃ n, p = n + 2 :=
  ⟨p - 2, by have := hp.out.two_le; omega⟩

theorem evalPhi_A1 (p m : ℕ) :
    evalPhi p (Polynomial.X ^ m - Polynomial.X + Polynomial.C Polynomial.X) =
      Phi p ^ m - Phi p + X := by
  rw [← evalPhiHom_apply, map_add, map_sub, map_pow, evalPhiHom_apply, evalPhiHom_apply,
    evalPhi_X, evalPhi_C_X]

/-- **`X_1 = A_1(z, Φ) = Φ ^ p - Φ + z = p z ^ (2p-1) + z ^ (2p) r`.** -/
theorem evalPhi_tower_one_eq (p : ℕ) [hp : Fact p.Prime] :
    ∃ r : PowerSeries ℤ, Phi p ^ p - Phi p + X =
      (p : PowerSeries ℤ) * X ^ (2 * p - 1) + X ^ (2 * p) * r := by
  obtain ⟨n, rfl⟩ := exists_add_two p
  obtain ⟨r, hr⟩ := evalPhi_tower_one_eq_aux n
  refine ⟨r, ?_⟩
  rw [hr, show 2 * (n + 2) - 1 = 2 * n + 3 by omega, show 2 * (n + 2) = 2 * n + 4 by ring]

theorem X_pow_eq_mul {a b c : ℕ} (h : a = b + c) :
    (X : PowerSeries ℤ) ^ a = X ^ b * X ^ c := by
  rw [h, pow_add]

/-! ## The coefficients -/

theorem coeff_X_pow_mul_of_lt {N m : ℕ} (h : m < N) (g : PowerSeries ℤ) :
    coeff m ((X : PowerSeries ℤ) ^ N * g) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with h'
  · omega
  · rfl

/-- **Remark 5.4(v), `t ^ p` form.** For every prime `p`, the coefficient of `z ^ (2p-1)` in
`((t ^ p - t + z) ^ p - p ^ (p-1) (t ^ p - t + z))(z, Φ_p)` is `-p ^ p`. -/
theorem coeff_evalPhi_km25p (p : ℕ) [hp : Fact p.Prime] :
    coeff (2 * p - 1) (evalPhi p (km25p p)) = -(p : ℤ) ^ p := by
  obtain ⟨r, hr⟩ := evalPhi_tower_one_eq p
  have hp2 := hp.out.two_le
  set Y := Phi p ^ p - Phi p + X with hY
  have hev : evalPhi p (km25p p) = Y ^ p - PowerSeries.C ((p : ℤ) ^ (p - 1)) * Y := by
    rw [km25p, ← evalPhiHom_apply, map_sub, map_pow, map_mul, evalPhiHom_apply,
      evalPhiHom_apply, evalPhi_CC, evalPhi_A1]
  -- `Y ^ p` is divisible by `z ^ (2p)`
  obtain ⟨S, hS⟩ : (X : PowerSeries ℤ) ^ (2 * p) ∣ Y ^ p := by
    have h1 : (X : PowerSeries ℤ) ^ (2 * p - 1) ∣ Y :=
      ⟨(p : PowerSeries ℤ) + X * r, by
        rw [hr, X_pow_eq_mul (show 2 * p = (2 * p - 1) + 1 by omega), pow_one]; ring⟩
    have h2 : (X : PowerSeries ℤ) ^ ((2 * p - 1) * p) ∣ Y ^ p := by
      rw [pow_mul]; exact pow_dvd_pow_of_dvd h1 p
    refine dvd_trans (pow_dvd_pow _ ?_) h2
    nlinarith [Nat.sub_add_cancel (show 1 ≤ 2 * p by omega)]
  have e : evalPhi p (km25p p) =
      PowerSeries.C (-(p : ℤ) ^ p) * X ^ (2 * p - 1) +
        X ^ (2 * p) * (S - PowerSeries.C ((p : ℤ) ^ (p - 1)) * r) := by
    rw [hev, hS, hr]
    have hc : PowerSeries.C ((p : ℤ) ^ (p - 1)) * (p : PowerSeries ℤ) =
        PowerSeries.C ((p : ℤ) ^ p) := by
      rw [← map_natCast (PowerSeries.C (R := ℤ)), ← map_mul, ← pow_succ,
        Nat.sub_add_cancel hp.out.one_lt.le]
    rw [map_neg]
    linear_combination (-(X : PowerSeries ℤ) ^ (2 * p - 1)) * hc
  rw [e, map_add, PowerSeries.coeff_C_mul_X_pow, ite_eq_left rfl,
    coeff_X_pow_mul_of_lt (by omega), add_zero]

/-- **Remark 5.4(v), odd `p`.** For every prime `p ≠ 2`, the coefficient of `z ^ 2` in
`((t ^ p - t + z) ^ p - p ^ (p-1) (t ^ 2 - t + z))(z, Φ_p)` is `-p ^ (p-1)`. -/
theorem coeff_two_evalPhi_km25 (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    coeff 2 (evalPhi p (km25 p)) = -(p : ℤ) ^ (p - 1) := by
  obtain ⟨r, hr⟩ := evalPhi_tower_one_eq p
  obtain ⟨w, hw⟩ := Phi_eq p
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  set Y := Phi p ^ p - Phi p + X with hY
  have hev : evalPhi p (km25 p) = Y ^ p - PowerSeries.C ((p : ℤ) ^ (p - 1)) *
      (Phi p ^ 2 - Phi p + X) := by
    rw [km25, ← evalPhiHom_apply, map_sub, map_pow, map_mul]
    simp only [evalPhiHom_apply, evalPhi_CC, evalPhi_A1]
    rfl
  -- `Y ^ p` is divisible by `z ^ 3`
  obtain ⟨S, hS⟩ : (X : PowerSeries ℤ) ^ 3 ∣ Y ^ p := by
    have h1 : (X : PowerSeries ℤ) ^ 3 ∣ Y :=
      ⟨(p : PowerSeries ℤ) * X ^ (2 * p - 4) + X ^ (2 * p - 3) * r, by
        rw [hr, X_pow_eq_mul (show 2 * p - 1 = 3 + (2 * p - 4) by omega),
          X_pow_eq_mul (show 2 * p = 3 + (2 * p - 3) by omega)]
        ring⟩
    exact dvd_trans h1 (dvd_pow_self Y (by omega))
  -- `Φ = z + z ^ 3 v`
  obtain ⟨v, hv⟩ : ∃ v : PowerSeries ℤ, Phi p = X + X ^ 3 * v :=
    ⟨X ^ (p - 3) + X ^ (p ^ 2 - 3) * w, by
      rw [hw, mul_add, ← mul_assoc, ← pow_add, ← pow_add, show 3 + (p - 3) = p by omega,
        show 3 + (p ^ 2 - 3) = p ^ 2 by nlinarith [Nat.sub_add_cancel (show 3 ≤ p ^ 2 by nlinarith)]]
      ring⟩
  have e : evalPhi p (km25 p) =
      PowerSeries.C (-(p : ℤ) ^ (p - 1)) * X ^ 2 +
        X ^ 3 * (S - PowerSeries.C ((p : ℤ) ^ (p - 1)) * (2 * X * v + X ^ 3 * v ^ 2 - v)) := by
    rw [hev, hS, hv, map_neg]
    ring
  rw [e, map_add, PowerSeries.coeff_C_mul_X_pow, ite_eq_left rfl,
    coeff_X_pow_mul_of_lt (by omega), add_zero]

/-- For `p = 2` the coefficient of `z ^ 3` in `((t^2 - t + z)^2 - 2 (t^2 - t + z))(z, Φ_2)` is
`-4 = -2 ^ 2`. -/
theorem coeff_three_evalPhi_km25_two :
    coeff 3 (evalPhi 2 (km25 2)) = -4 := by
  have := coeff_evalPhi_km25p 2
  rw [km25_two]
  norm_num at this ⊢
  exact this

theorem not_pow_succ_succ_dvd (p : ℕ) [hp : Fact p.Prime] {j : ℕ} (hj : j ≤ p) :
    ¬ (p : ℤ) ^ (p + 1) ∣ -(p : ℤ) ^ j := by
  rw [dvd_neg]
  intro h
  have h' : p ^ (p + 1) ∣ p ^ j := by exact_mod_cast h
  have := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 h'
  omega

/-- **Remark 5.4(v).** For every odd prime `p`, Krattenthaler and Müller's polynomial
`(t ^ p - t + z) ^ p - p ^ (p-1) (t ^ 2 - t + z)` does not vanish modulo `p ^ (p+1)` at `Φ_p`. -/
theorem not_vanishesMod_km25 (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ¬ VanishesMod p (p + 1) (km25 p) := by
  intro h
  have := h 2
  rw [coeff_two_evalPhi_km25 p hp2] at this
  exact not_pow_succ_succ_dvd p (Nat.sub_le p 1) this

/-- **Remark 5.4(v), `t ^ p` form.** For every prime `p`,
`(t ^ p - t + z) ^ p - p ^ (p-1) (t ^ p - t + z)` does not vanish modulo `p ^ (p+1)` at `Φ_p`. -/
theorem not_vanishesMod_km25p (p : ℕ) [hp : Fact p.Prime] :
    ¬ VanishesMod p (p + 1) (km25p p) := by
  intro h
  have := h (2 * p - 1)
  rw [coeff_evalPhi_km25p p] at this
  exact not_pow_succ_succ_dvd p le_rfl this

/-- **Remark 5.4(v), `p = 2`.** `(t^2 - t + z)^2 - 2 (t^2 - t + z)` does not vanish modulo
`2 ^ 3 = 8` at `Φ_2`. -/
theorem not_vanishesMod_km25_two :
    ¬ VanishesMod 2 (2 + 1) (km25 2) := by
  rw [km25_two]
  exact not_vanishesMod_km25p 2

/-! ## The corrected polynomial -/

/-- `A_1(z ^ p, t - z) = (t - z) ^ p - (t - z) + z ^ p`. -/
theorem shift_tower_one (p : ℕ) [hp : Fact p.Prime] :
    shift p (tower p 1) = (Polynomial.X - Polynomial.C Polynomial.X) ^ p -
      (Polynomial.X - Polynomial.C Polynomial.X) + Polynomial.C (Polynomial.X ^ p) := by
  rw [tower_one, shift]
  simp [Polynomial.map_pow, Polynomial.expand_X, Polynomial.sub_comp, Polynomial.add_comp]

/-- `km25fix p = A_1 ^ p - p ^ (p-1) A_1(z ^ p, t - z)`. -/
theorem km25fix_eq (p : ℕ) [hp : Fact p.Prime] :
    km25fix p = tower p 1 ^ p -
      Polynomial.C (Polynomial.C ((p : ℤ) ^ (p - 1))) * shift p (tower p 1) := by
  rw [shift_tower_one, tower_one, km25fix]

theorem tower_two_eq (p : ℕ) [hp : Fact p.Prime] :
    tower p 2 = tower p 1 ^ p -
      Polynomial.C (Polynomial.C ((-(p : ℤ)) ^ (p - 1))) * shift p (tower p 1) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, tower]
  simp [c]

/-- **Remark 5.4(v), corrected polynomial, odd `p`.** For every odd prime `p`,
`(t ^ p - t + z) ^ p - p ^ (p-1) A_1(z ^ p, t - z)` is the tower polynomial `A_2`. -/
theorem km25fix_eq_tower_two (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    km25fix p = tower p 2 := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have heven : Even (p - 1) := by
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m, by omega⟩
  rw [km25fix_eq, tower_two_eq, heven.neg_pow]

/-- **Remark 5.4(v), corrected polynomial, `p = 2`.** The value at `Φ_2` of
`(t^2 - t + z)^2 - 2 A_1(z^2, t - z)` is that of `A_2` plus `8 σ(δ(Φ_2))`. -/
theorem evalPhi_km25fix_two :
    evalPhi 2 (km25fix 2) = evalPhi 2 (tower 2 2) + 8 * sigma 2 (delta 2 (Phi 2)) := by
  have hs : evalPhi 2 (shift 2 (tower 2 1)) = -2 * sigma 2 (delta 2 (Phi 2)) := by
    rw [evalPhi_shift, evalPhi_tower, map_mul, map_intCast]
    simp [c]
  have e : km25fix 2 = tower 2 2 -
      Polynomial.C (Polynomial.C (4 : ℤ)) * shift 2 (tower 2 1) := by
    rw [km25fix_eq, tower_two_eq]
    simp only [map_neg, map_ofNat, Nat.cast_ofNat, show 2 - 1 = 1 from rfl, pow_one]
    ring
  rw [e, ← evalPhiHom_apply, map_sub, map_mul, evalPhiHom_apply, evalPhiHom_apply,
    evalPhiHom_apply, evalPhi_CC, hs]
  have h4 : (PowerSeries.C (4 : ℤ) : PowerSeries ℤ) = 4 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, map_natCast]; norm_num
  rw [h4]
  ring

/-- **Remark 5.4(v), corrected polynomial.** For every prime `p`,
`(t ^ p - t + z) ^ p - p ^ (p-1) A_1(z ^ p, t - z)` vanishes modulo `p ^ (p+1)` at `Φ_p`. -/
theorem vanishesMod_km25fix (p : ℕ) [hp : Fact p.Prime] : VanishesMod p (p + 1) (km25fix p) := by
  have he : e p 2 = p + 1 := by simp [e]
  by_cases hp2 : p = 2
  · subst hp2
    intro n
    rw [evalPhi_km25fix_two, map_add]
    refine dvd_add (by rw [← he]; exact vanishesMod_tower 2 2 n) ?_
    rw [show (8 : PowerSeries ℤ) = PowerSeries.C ((2 : ℤ) ^ (2 + 1)) by
      rw [map_pow]; norm_num, PowerSeries.coeff_C_mul]
    push_cast
    exact dvd_mul_right _ _
  · rw [km25fix_eq_tower_two p hp2, ← he]
    exact vanishesMod_tower p 2

/-- **Remark 5.4(v), `A_2` for `p = 2`.**
`A_2 = t^4 - 2 t^3 + (2z + 3) t^2 - (6z + 2) t + 5z^2 + 2z`. -/
theorem tower_two_two :
    tower 2 2 = Polynomial.X ^ 4 - 2 * Polynomial.X ^ 3 +
      Polynomial.C (2 * Polynomial.X + 3) * Polynomial.X ^ 2 -
        Polynomial.C (6 * Polynomial.X + 2) * Polynomial.X +
          Polynomial.C (5 * Polynomial.X ^ 2 + 2 * Polynomial.X) := by
  rw [tower_two]
  simp only [map_add, map_mul, map_pow, map_ofNat, map_neg, map_natCast]
  norm_num
  ring_nf

/-- The quartic listed by Kauers, Krattenthaler and Müller (2012), Proposition 2, for the modulus
`8` (`p = 2`): `t^4 + 6t^3 + (2z + 3)t^2 + (2z + 6)t + 5z^2 + 2z`. (Checked against the arXiv
source arXiv:1107.2015v2, Proposition 2 and the relation after it, and the journal text.) -/
noncomputable def kkm8 : Polynomial (Polynomial ℤ) :=
  Polynomial.X ^ 4 + 6 * Polynomial.X ^ 3 + Polynomial.C (2 * Polynomial.X + 3) * Polynomial.X ^ 2 +
    Polynomial.C (2 * Polynomial.X + 6) * Polynomial.X +
      Polynomial.C (5 * Polynomial.X ^ 2 + 2 * Polynomial.X)

/-- **Remark 5.4(v), last sentence.** For `p = 2`, `A_2 - Q = -8 (t ^ 3 + (z + 1) t)` with `Q`
the quartic `kkm8`, so `A_2` and `Q` agree modulo `8` coefficient by coefficient. -/
theorem tower_two_two_sub_kkm8 :
    tower 2 2 - kkm8 = Polynomial.C (Polynomial.C (-8)) *
      (Polynomial.X ^ 3 + Polynomial.C (Polynomial.X + 1) * Polynomial.X) := by
  rw [tower_two_two, kkm8]
  simp only [map_add, map_mul, map_neg, map_ofNat, map_one]
  ring

/-- The quartic `kkm8` vanishes modulo `8` at `Φ_2`, as the tower polynomial `A_2` does. -/
theorem vanishesMod_kkm8 : VanishesMod 2 3 kkm8 := by
  intro n
  have h : kkm8 = tower 2 2 - Polynomial.C (Polynomial.C (-8)) *
      (Polynomial.X ^ 3 + Polynomial.C (Polynomial.X + 1) * Polynomial.X) := by
    rw [← tower_two_two_sub_kkm8]; ring
  have he : e 2 2 = 3 := by simp [e]
  rw [h, ← evalPhiHom_apply, map_sub, map_mul, evalPhiHom_apply, evalPhiHom_apply,
    evalPhi_CC, map_sub, PowerSeries.coeff_C_mul]
  refine dvd_sub (by rw [← he]; exact vanishesMod_tower 2 2 n) (dvd_mul_of_dvd_left ?_ _)
  norm_num

end Frobenius.KKM
