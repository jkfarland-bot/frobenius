module

/-
Run r25, seat L8: **`A = ℤ_[p][[x_1..x_n]]` is free over `B = σ(A)` with basis the digit monomials
`x ^ e`, `0 ≤ e_i < p`, for EVERY Frobenius lift `σ`** (R-086, note Section 6 "other lifts":
"A is free over B with basis x^c"), with no continuity assumed.

* `classPart_frob_mul_monomial`: the class part at a digit `κ` of `frob(b) x ^ e` is `b` if
  `κ = e` and `0` otherwise (the standard decomposition is unique).
* `digit_indep_every_lift`: `∑_e σ(c_e) x ^ e = 0` forces every `c_e = 0` (induction on the
  power of `p` dividing the `c_e`, then `p`-adic separation).
* `free_every_lift`: existence (Span.lean) and uniqueness of `a = ∑_e σ(c_e) x ^ e`.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.PropT
public import Frobenius.Levels.G1
public import Frobenius.Levels.G1Series
public import Frobenius.Levels.Lifts
public import Frobenius.Levels.Span

@[expose] public section

namespace FrobLevel

open MvPowerSeries

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

theorem digit_eq_of_mod {a b d c : ℕ} (ha : a < p) (hb : b < p) (h : p * c + b = p * d + a) :
    a = b := by
  have h1 := congrArg (· % p) h
  simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
  exact h1.symm

theorem classPart_frob_mul_monomial {R : Type*} [CommRing R] {κ e : Fin n →₀ ℕ}
    (hκ : κ ∈ digitExps p n) (he : e ∈ digitExps p n) (b : MvPowerSeries (Fin n) R) :
    classPart p (frob p b * monomial e 1) κ = if κ = e then b else 0 := by
  ext d
  rw [coeff_classPart, coeff_mul_monomial, mul_one]
  split_ifs with hle hke hke
  · subst hke
    rw [add_tsub_cancel_right, coeff_frob_smul]
  · rw [map_zero]
    obtain ⟨i, hi⟩ : ∃ i, κ i ≠ e i := by
      by_contra h; push Not at h; exact hke (Finsupp.ext h)
    apply coeff_frob_of_not_dvd p b (i := i)
    rintro ⟨c, hc⟩
    have hle_i := hle i
    simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hc hle_i
    have h2 : p * c + e i = p * d i + κ i := by omega
    exact hi (digit_eq_of_mod ((mem_digitExps p n).1 hκ i) ((mem_digitExps p n).1 he i) h2)
  · subst hke
    exact absurd (le_add_self) hle
  · rw [map_zero]

theorem coeff_classPart_sum {R : Type*} [CommRing R] {κ : Fin n →₀ ℕ} (hκ : κ ∈ digitExps p n)
    (c : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) R) (d : Fin n →₀ ℕ) :
    coeff (p • d + κ) (∑ e ∈ digitExps p n, frob p (c e) * monomial e 1) = coeff d (c κ) := by
  classical
  rw [map_sum]
  have : ∀ e ∈ digitExps p n, coeff (p • d + κ) (frob p (c e) * monomial e 1)
      = if κ = e then coeff d (c κ) else 0 := by
    intro e he
    have := congrArg (coeff d) (classPart_frob_mul_monomial (p := p) hκ he (c e))
    rw [coeff_classPart] at this
    rw [this]
    split_ifs with h
    · subst h; rfl
    · rw [map_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq (digitExps p n) κ, if_pos hκ]

section AnyLift

variable {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}

theorem digit_indep_pow (hσ : IsFrobLift p σ) (K : ℕ) :
    ∀ c : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p],
      ∑ e ∈ digitExps p n, σ (c e) * monomial e 1 = 0 →
        ∀ e ∈ digitExps p n, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ K ∣ c e := by
  set P := ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) with hP
  induction K with
  | zero => intro c _ e _; simp
  | succ K ih =>
    intro c hc e he
    have hf := frob_isFrobLift (τ := Fin n) p (padicInt_pow_sub p)
    -- `p ∣ ∑ frob(c_e) x ^ e`
    have hdiv : P ∣ ∑ e ∈ digitExps p n, frob p (c e) * monomial e 1 := by
      have : ∑ e ∈ digitExps p n, frob p (c e) * monomial e 1
          = ∑ e ∈ digitExps p n, (frob p (c e) - σ (c e)) * monomial e 1 := by
        simp only [sub_mul, Finset.sum_sub_distrib, hc, sub_zero]
      rw [this]
      refine Finset.dvd_sum fun e _ => dvd_mul_of_dvd_left ?_ _
      have : frob p (c e) - σ (c e) = (frob p (c e) - c e ^ p) - (σ (c e) - c e ^ p) := by ring
      rw [this]; exact dvd_sub (hf (c e)) (hσ (c e))
    -- so `p ∣ c_κ` for every digit `κ`
    have hpc : ∀ κ ∈ digitExps p n, P ∣ c κ := by
      intro κ hκ
      have h1 := (series_dvd_iff 1 _).1 (by simpa using hdiv)
      have h2 : ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ 1 ∣ c κ :=
        (series_dvd_iff 1 (c κ)).2 fun d => by
          have := h1 (p • d + κ)
          rwa [coeff_classPart_sum hκ] at this
      simpa [hP] using h2
    choose! c' hc' using hpc
    have hrel : ∑ e ∈ digitExps p n, σ (c' e) * monomial e 1 = 0 := by
      apply noPTorsion_series (p := p) (n := n)
      rw [Finset.mul_sum, ← hc]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [hc' e he, map_mul, hP, map_natCast]; ring
    obtain ⟨q, hq⟩ := ih c' hrel e he
    refine ⟨q, ?_⟩
    rw [hc' e he, hq, pow_succ]; ring

/-- **Independence of the digit monomials over `B`, every lift.** -/
theorem digit_indep_every_lift (hσ : IsFrobLift p σ)
    (c : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p])
    (hc : ∑ e ∈ digitExps p n, σ (c e) * monomial e 1 = 0) : ∀ e ∈ digitExps p n, c e = 0 :=
  fun e he => series_sep _ fun K => digit_indep_pow hσ K c hc e he

/-- **Freeness (R-086), every lift**: every `a` is `∑_{e digit} σ(c_e) x ^ e` for unique
`c_e` (uniqueness on the digit exponents). -/
theorem free_every_lift (hσ : IsFrobLift p σ) (a : MvPowerSeries (Fin n) ℤ_[p]) :
    (∃ c : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p],
      a = ∑ e ∈ digitExps p n, σ (c e) * monomial e 1) ∧
    ∀ c c' : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p],
      a = ∑ e ∈ digitExps p n, σ (c e) * monomial e 1 →
      a = ∑ e ∈ digitExps p n, σ (c' e) * monomial e 1 → ∀ e ∈ digitExps p n, c e = c' e := by
  refine ⟨span_every_lift hσ a, fun c c' h1 h2 e he => ?_⟩
  have := digit_indep_every_lift hσ (fun e => c e - c' e) (by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib, ← h1, ← h2, sub_self]) e he
  exact sub_eq_zero.1 this

end AnyLift

end FrobLevel
