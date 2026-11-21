module

/-
Run r25, seat L8: **the chain rule for substitution in multivariate power series**
(not in Mathlib at this version).

* `pderiv_aeval_chain`: for `P : MvPolynomial (Fin n) R` and `a : Fin n → MvPowerSeries (Fin m) R`,
  `∂_j (P(a)) = ∑_i (∂_i P)(a) · ∂_j a_i`.
* `pderiv_subst_chain`: for `f : MvPowerSeries (Fin n) R` and `a_i` with zero constant term,
  `∂_j (f(a)) = ∑_i (∂_i f)(a) · ∂_j a_i`. Proof: split `f` into its truncation below total degree
  `N = |e| + 2` (a polynomial, where the polynomial rule applies) and a remainder of order `≥ N`,
  whose contribution to the coefficient at `e` vanishes on both sides.
* `pderiv_frobForm`: the chain rule for L4's lifts `x_i ↦ x_i ^ p + p h_i` (`h_i(0) = 0`).

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

section Chain

variable {R : Type*} [CommRing R] {n m : ℕ}

theorem pderiv_aeval_chain (a : Fin n → MvPowerSeries (Fin m) R) (P : MvPolynomial (Fin n) R)
    (j : Fin m) :
    pderiv (R := R) j (MvPolynomial.aeval a P)
      = ∑ i, MvPolynomial.aeval a (MvPolynomial.pderiv i P) * pderiv (R := R) j (a i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.aeval_C]
    simp only [MvPolynomial.pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
    rw [show (algebraMap R (MvPowerSeries (Fin m) R)) r = C r from rfl, pderiv_C]
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P k hP =>
    rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hP]
    simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, map_add, map_mul,
      MvPolynomial.aeval_X, add_mul, Finset.sum_add_distrib]
    have : ∑ i, MvPolynomial.aeval a P
        * MvPolynomial.aeval a (Pi.single (M := fun _ => MvPolynomial (Fin n) R) i 1 k)
        * pderiv (R := R) j (a i) = MvPolynomial.aeval a P * pderiv (R := R) j (a k) := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro i _ hik
        rw [Pi.single_eq_of_ne' hik]; simp
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [this, Finset.mul_sum, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

theorem order_ge_of_coeff {f : MvPowerSeries (Fin n) R} {N : ℕ}
    (h : ∀ d : Fin n →₀ ℕ, d.degree < N → coeff d f = 0) : (N : ℕ∞) ≤ f.order :=
  le_order fun d hd => h d (by exact_mod_cast hd)

theorem coeff_eq_zero_of_order_ge {f : MvPowerSeries (Fin n) R} {N : ℕ} (hf : (N : ℕ∞) ≤ f.order)
    {d : Fin n →₀ ℕ} (hd : d.degree < N) : coeff d f = 0 :=
  coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) hf)

theorem one_le_iInf_order {a : Fin n → MvPowerSeries (Fin m) R}
    (ha0 : ∀ i, constantCoeff (a i) = 0) : (1 : ℕ∞) ≤ ⨅ i, (a i).order :=
  le_iInf fun i => (one_le_order_iff_constCoeff_eq_zero).2 (ha0 i)

theorem order_subst_ge {a : Fin n → MvPowerSeries (Fin m) R}
    (ha0 : ∀ i, constantCoeff (a i) = 0) (g : MvPowerSeries (Fin n) R) :
    g.order ≤ (subst a g).order := by
  have ha := hasSubst_of_constantCoeff_zero ha0
  refine le_trans ?_ (le_order_subst ha g)
  calc g.order = 1 * g.order := (one_mul _).symm
    _ ≤ _ := mul_le_mul' (one_le_iInf_order ha0) le_rfl

/-- **Chain rule for substitution** (zero constant terms). -/
theorem pderiv_subst_chain (a : Fin n → MvPowerSeries (Fin m) R)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries (Fin n) R) (j : Fin m) :
    pderiv (R := R) j (subst a f) = ∑ i, subst a (pderiv (R := R) i f) * pderiv (R := R) j (a i) := by
  classical
  have ha := hasSubst_of_constantCoeff_zero ha0
  ext e
  set N := e.degree + 2 with hN
  set P : MvPolynomial (Fin n) R := truncTotal N f
  set g : MvPowerSeries (Fin n) R := f - (P : MvPowerSeries (Fin n) R) with hg
  have hfg : f = (P : MvPowerSeries (Fin n) R) + g := by rw [hg]; ring
  have hgo : (N : ℕ∞) ≤ g.order := order_ge_of_coeff fun d hd => by
    rw [hg, map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]
  -- contributions of `g`
  have hL : coeff e (pderiv (R := R) j (subst a g)) = 0 := by
    rw [coeff_pderiv]
    have := coeff_eq_zero_of_order_ge (le_trans hgo (order_subst_ge ha0 g))
      (d := e + Finsupp.single j 1) (by
        rw [map_add, Finsupp.degree_single]; omega)
    rw [this, zero_mul]
  have hR : ∀ i, coeff e (subst a (pderiv (R := R) i g) * pderiv (R := R) j (a i)) = 0 := by
    intro i
    have h1 : ((N - 1 : ℕ) : ℕ∞) ≤ (pderiv (R := R) i g).order := order_ge_of_coeff fun d hd => by
      rw [coeff_pderiv]
      have := coeff_eq_zero_of_order_ge hgo (d := d + Finsupp.single i 1) (by
        rw [map_add, Finsupp.degree_single]; omega)
      rw [this, zero_mul]
    have h2 := le_trans h1 (order_subst_ge ha0 (pderiv (R := R) i g))
    have h3 : ((N - 1 : ℕ) : ℕ∞) ≤ (subst a (pderiv (R := R) i g) * pderiv (R := R) j (a i)).order :=
      le_trans (le_trans h2 le_self_add) le_order_mul
    exact coeff_eq_zero_of_order_ge h3 (by omega)
  -- the polynomial part
  have hP : pderiv (R := R) j (subst a (P : MvPowerSeries (Fin n) R))
      = ∑ i, subst a (pderiv (R := R) i (P : MvPowerSeries (Fin n) R)) * pderiv (R := R) j (a i) := by
    rw [subst_coe, pderiv_aeval_chain]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pderiv_coe, subst_coe]
  rw [hfg, subst_add ha, map_add, map_add, hP, hL, add_zero]
  simp only [map_add, subst_add ha, add_mul, Finset.sum_add_distrib, map_sum, hR,
    Finset.sum_const_zero, add_zero]

end Chain

section Frob

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

/-- The chain rule for `x_i ↦ x_i ^ p + p h_i` (`h_i(0) = 0`). -/
theorem pderiv_frobForm (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (h0 : ∀ i, constantCoeff (h i) = 0) (f : MvPowerSeries (Fin n) ℤ_[p]) (j : Fin n) :
    pderiv (R := ℤ_[p]) j (frobForm h h0 f)
      = ∑ i, frobForm h h0 (pderiv (R := ℤ_[p]) i f) * pderiv (R := ℤ_[p]) j (frobForm h h0 (X i)) := by
  have ha0 : ∀ i, constantCoeff (X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * h i) = 0 := by
    intro i
    rw [map_add, map_pow, constantCoeff_X, zero_pow hp.out.ne_zero, map_mul, h0, mul_zero, add_zero]
  simp only [frobForm_X]
  unfold frobForm
  simp only [substLift_apply]
  exact pderiv_subst_chain _ ha0 f j

end Frob

end FrobLevel
