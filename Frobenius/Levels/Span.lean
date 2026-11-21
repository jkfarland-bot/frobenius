module

/-
Run r25, seat L8: **the digit monomials span `ℤ_[p][[x_1..x_n]]` over the image of EVERY
Frobenius lift** (R-086, "A is free over B with basis x^c", spanning half), with no continuity,
no `ℤ_[p]`-linearity and no form `x_i ↦ x_i ^ p + p h_i` assumed: `σ` is any ring endomorphism with
`p ∣ σ a - a ^ p` for all `a`.

Proof: modulo `p` the standard decomposition `a = ∑_e frob(c_e) x^e` works for `σ` as well,
since `frob(c) ≡ c ^ p ≡ σ(c)`; iterate on the error and pass to the `p`-adic limit
coefficientwise (`ℤ_[p]` is `p`-adically complete and separated). `σ` commutes with the limit
because `σ(p ^ K y) = p ^ K σ(y)`.

Consequences:
* `levelCount_le_min_every_lift`: `L_f + 1 ≤ min(p ^ n, S(p ^ k))` for every lift, every `n`.
* `levelCount_G1_every_lift`: **G1 (R-086) in one variable for every lift**, unconditionally:
  `L_f + 1 = p` if `J_B(f) = 0`, and `min(p, ⌈k / J_B(f)⌉)` if `J_B(f) ≥ 1`. This closes L4's open
  statement `open_span_frobForm_one` (in a stronger form: every lift, not only `x ↦ x ^ p + p h`).

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

@[expose] public section

namespace FrobLevel

open MvPowerSeries

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

/-! ### `p`-adic limits and separation in `ℤ_[p]` -/

theorem padic_dvd_iff_mem (K : ℕ) (x : ℤ_[p]) :
    (p : ℤ_[p]) ^ K ∣ x ↔ x ∈ (IsLocalRing.maximalIdeal ℤ_[p] ^ K • ⊤ : Submodule ℤ_[p] ℤ_[p]) := by
  rw [← Ideal.one_eq_top, smul_eq_mul, mul_one, PadicInt.maximalIdeal_eq_span_p,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem padic_sep (y : ℤ_[p]) (h : ∀ K, (p : ℤ_[p]) ^ K ∣ y) : y = 0 := by
  apply IsHausdorff.haus (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]) y
  intro K
  rw [SModEq.sub_mem, sub_zero, ← padic_dvd_iff_mem]
  exact h K

theorem padic_tele (x : ℕ → ℤ_[p]) (hx : ∀ K, (p : ℤ_[p]) ^ K ∣ x (K + 1) - x K) {m k : ℕ}
    (hmk : m ≤ k) : (p : ℤ_[p]) ^ m ∣ x k - x m := by
  induction k, hmk using Nat.le_induction with
  | base => simp
  | succ k hmk ih =>
    have : x (k + 1) - x m = (x (k + 1) - x k) + (x k - x m) := by ring
    rw [this]
    exact dvd_add ((pow_dvd_pow _ hmk).trans (hx k)) ih

theorem padic_lim (x : ℕ → ℤ_[p]) (hx : ∀ K, (p : ℤ_[p]) ^ K ∣ x (K + 1) - x K) :
    ∃ L : ℤ_[p], ∀ K, (p : ℤ_[p]) ^ K ∣ L - x K := by
  obtain ⟨L, hL⟩ := IsPrecomplete.prec
    (inferInstance : IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p]) (f := x)
    (fun {m k} hmk => by
      rw [SModEq.sub_mem, ← padic_dvd_iff_mem, ← dvd_neg, neg_sub]
      exact padic_tele x hx hmk)
  refine ⟨L, fun K => ?_⟩
  have := hL K
  rw [SModEq.sub_mem, ← padic_dvd_iff_mem, ← dvd_neg, neg_sub] at this
  exact this

/-! ### The same in `ℤ_[p][[x]]`, coefficientwise -/

theorem natCast_pow_eq_C_span (K : ℕ) :
    ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ K = C ((p : ℤ_[p]) ^ K) := by
  rw [map_pow, map_natCast]

theorem series_dvd_iff (K : ℕ) (y : MvPowerSeries (Fin n) ℤ_[p]) :
    ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ K ∣ y ↔ ∀ d, (p : ℤ_[p]) ^ K ∣ coeff d y := by
  rw [natCast_pow_eq_C_span]
  constructor
  · rintro ⟨q, rfl⟩ d
    rw [coeff_C_mul]; exact dvd_mul_right _ _
  · intro h
    choose q hq using h
    let a : MvPowerSeries (Fin n) ℤ_[p] := fun d => q d
    refine ⟨a, ?_⟩
    ext d
    rw [coeff_C_mul, hq d]
    rfl

theorem series_sep (y : MvPowerSeries (Fin n) ℤ_[p])
    (h : ∀ K, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ K ∣ y) : y = 0 := by
  ext d
  rw [map_zero]
  exact padic_sep _ fun K => (series_dvd_iff K y).1 (h K) d

theorem series_lim (s : ℕ → MvPowerSeries (Fin n) ℤ_[p])
    (hs : ∀ K, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ K ∣ s (K + 1) - s K) :
    ∃ L : MvPowerSeries (Fin n) ℤ_[p],
      ∀ K, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ K ∣ L - s K := by
  have h1 : ∀ d, ∃ L : ℤ_[p], ∀ K, (p : ℤ_[p]) ^ K ∣ L - coeff d (s K) := fun d =>
    padic_lim (fun K => coeff d (s K)) fun K => by
      rw [← map_sub]; exact (series_dvd_iff K _).1 (hs K) d
  choose L hL using h1
  let a : MvPowerSeries (Fin n) ℤ_[p] := fun d => L d
  refine ⟨a, fun K => (series_dvd_iff K _).2 fun d => ?_⟩
  rw [map_sub]
  exact hL d K

/-! ### Spanning for every lift -/

section Span

variable {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}

/-- One step: `a = ∑_e σ(c_e) x^e + p a'`. -/
theorem span_step (hσ : IsFrobLift p σ) (a : MvPowerSeries (Fin n) ℤ_[p]) :
    ∃ c : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p], ∃ a' : MvPowerSeries (Fin n) ℤ_[p],
      a = ∑ e ∈ digitExps p n, σ (c e) * monomial e 1
        + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * a' := by
  obtain ⟨c, hc⟩ := span_digit p a
  have hf := frob_isFrobLift (τ := Fin n) p (padicInt_pow_sub p)
  have hw : ∀ e, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ∣ frob p (c e) - σ (c e) := by
    intro e
    have h1 := hf (c e)
    have h2 := hσ (c e)
    have : frob p (c e) - σ (c e) = (frob p (c e) - c e ^ p) - (σ (c e) - c e ^ p) := by ring
    rw [this]; exact dvd_sub h1 h2
  choose w hw using hw
  refine ⟨c, ∑ e ∈ digitExps p n, w e * monomial e 1, ?_⟩
  conv_lhs => rw [hc]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have : frob p (c e) = σ (c e) + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * w e := by
    rw [← hw e]; ring
  rw [this]; ring

/-- **Spanning for every Frobenius lift**: every `a ∈ ℤ_[p][[x_1..x_n]]` is
`∑_{e digit} σ(c_e) x^e`. -/
theorem span_every_lift (hσ : IsFrobLift p σ) (a : MvPowerSeries (Fin n) ℤ_[p]) :
    ∃ c : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p],
      a = ∑ e ∈ digitExps p n, σ (c e) * monomial e 1 := by
  classical
  set P : MvPowerSeries (Fin n) ℤ_[p] := ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) with hP
  choose cs rs hcs using span_step hσ
  -- remainders `r K` and digit coefficients `cs (r K)`
  let r : ℕ → MvPowerSeries (Fin n) ℤ_[p] := fun K => Nat.rec a (fun _ x => rs x) K
  have hr0 : r 0 = a := rfl
  have hrs : ∀ K, r (K + 1) = rs (r K) := fun K => rfl
  let S : ℕ → (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p] :=
    fun K e => ∑ k ∈ Finset.range K, P ^ k * cs (r k) e
  have hinv : ∀ K, a = ∑ e ∈ digitExps p n, σ (S K e) * monomial e 1 + P ^ K * r K := by
    intro K
    induction K with
    | zero => simp [S, hr0]
    | succ K ih =>
      rw [ih]
      have hσP : ∀ y, σ (P ^ K * y) = P ^ K * σ y := fun y => by
        rw [map_mul, map_pow, hP, map_natCast]
      have hS : ∀ e, σ (S (K + 1) e) = σ (S K e) + P ^ K * σ (cs (r K) e) := fun e => by
        simp only [S, Finset.sum_range_succ, map_add, hσP]
      have hstep := hcs (r K)
      rw [← hrs] at hstep
      simp only [hS, add_mul, Finset.sum_add_distrib]
      conv_lhs => rw [hstep]
      rw [mul_add, Finset.mul_sum, pow_succ]
      have h2 : ∀ x ∈ digitExps p n, P ^ K * σ (cs (r K) x) * monomial x 1
          = P ^ K * (σ (cs (r K) x) * monomial x 1) := fun x _ => by ring
      rw [Finset.sum_congr rfl h2]
      ring
  have hlim : ∀ e, ∃ L : MvPowerSeries (Fin n) ℤ_[p], ∀ K, P ^ K ∣ L - S K e := fun e =>
    series_lim (fun K => S K e) fun K => by
      simp only [S, Finset.sum_range_succ, add_sub_cancel_left]
      exact dvd_mul_right _ _
  choose b hb using hlim
  refine ⟨b, ?_⟩
  rw [← sub_eq_zero]
  apply series_sep
  intro K
  rw [hinv K]
  have : ∑ e ∈ digitExps p n, σ (S K e) * monomial e 1 + P ^ K * r K
      - ∑ e ∈ digitExps p n, σ (b e) * monomial e 1
      = P ^ K * r K - ∑ e ∈ digitExps p n, σ (b e - S K e) * monomial e 1 := by
    rw [sub_eq_iff_eq_add]
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [this]
  refine dvd_sub (dvd_mul_right _ _) (Finset.dvd_sum fun e _ => ?_)
  obtain ⟨q, hq⟩ := hb e K
  rw [hq, map_mul, map_pow, map_natCast, mul_assoc]
  exact dvd_mul_right _ _

/-- **Rank bound for every lift**: `L_f + 1 ≤ min(p ^ n, S(p ^ k))` (`u f ≡ 1 mod p ^ k`). -/
theorem levelCount_le_min_every_lift (hσ : IsFrobLift p σ) {f u : MvPowerSeries (Fin n) ℤ_[p]}
    {k : ℕ} (hk : 1 ≤ k)
    (hfu : ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ k ∣ f * u - 1) :
    levelCount p σ f k + 1 ≤ min (p ^ n) (kempner p k) := by
  have := levelCount_le_min_of_span hσ (digitExps p n) (fun e => monomial e 1)
    (span_every_lift hσ) hk hfu
  rwa [card_digitExps] at this

end Span

/-- **G1 (R-086), one variable, every Frobenius lift, unconditional**: for a unit `f` with
`J_B(f) = J` and `k ≥ 1`, `L_f + 1 = p` if `J = 0` and `min(p, ⌈k / J⌉)` if `J ≥ 1`. -/
theorem levelCount_G1_every_lift
    {σ : MvPowerSeries (Fin 1) ℤ_[p] →+* MvPowerSeries (Fin 1) ℤ_[p]} (h : IsFrobLift p σ)
    {f : MvPowerSeries (Fin 1) ℤ_[p]} (hf : IsUnit f) {J k : ℕ} (hk : 1 ≤ k)
    (hJb : ∃ b, ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p]) ^ J ∣ f - σ b)
    (hJ1 : ¬ ∃ b, ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p]) ^ (J + 1) ∣ f - σ b) :
    levelCount p σ f k + 1 = if J = 0 then p else min p (cdiv k J) :=
  levelCount_G1_of_span h (span_every_lift h) hf hk hJb hJ1

/-- L4's open statement `open_span_frobForm_one`, now a theorem (the special case
`σ = x ↦ x ^ p + p h`, one variable, of `span_every_lift`). -/
theorem span_frobForm_one (h : Fin 1 → MvPowerSeries (Fin 1) ℤ_[p])
    (h0 : ∀ i, constantCoeff (h i) = 0) (a : MvPowerSeries (Fin 1) ℤ_[p]) :
    ∃ c : (Fin 1 →₀ ℕ) → MvPowerSeries (Fin 1) ℤ_[p],
      a = ∑ e ∈ digitExps p 1, frobForm h h0 (c e) * monomial e 1 :=
  span_every_lift (frobForm_isFrobLift h h0) a

end FrobLevel
