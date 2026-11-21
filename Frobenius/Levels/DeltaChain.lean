module

/-
Run r25, seat L8: **the chain rule for `δ`** (note, proof of Theorem `Rsigma`:
`d δ(b)‾ = F_σ(d b̄) - b̄ ^ (p-1) d b̄`; Borger and Buium's eq. (5.5) in this setting), in
coordinates, for every `b` and every lift `σ(x_i) = x_i ^ p + p h_i` satisfying the chain rule
(in particular every `x_i ↦ x_i ^ p + p h_i` with `h_i(0) = 0`):

  `∂_j (δ(b) mod p) = (∂_j b̄) ^ p x_j ^ (p-1) + ∑_i (∂_i b̄) ^ p ∂_j h̄_i - b̄ ^ (p-1) ∂_j b̄`.

Theorem N (`thmN_poly`) is the case `b ^ p ∈ B`, where the left side vanishes.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Lifts
public import Frobenius.Levels.Chain
public import Frobenius.Levels.ThmN

@[expose] public section

namespace FrobLevel

open MvPowerSeries

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

theorem delta_chain_rule {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}
    (hσ : IsFrobLift p σ) (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (hh : ∀ i, σ (X i) = X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * h i)
    (hchain : ∀ (f : MvPowerSeries (Fin n) ℤ_[p]) (j : Fin n),
      pderiv (R := ℤ_[p]) j (σ f) = ∑ i, σ (pderiv (R := ℤ_[p]) i f) * pderiv (R := ℤ_[p]) j (σ (X i)))
    (m : MvPowerSeries (Fin n) ℤ_[p]) (j : Fin n) :
    pderiv (R := ZMod p) j (redp p (delta hσ m))
      = pderiv (R := ZMod p) j (redp p m) ^ p * (X j : MvPowerSeries (Fin n) (ZMod p)) ^ (p - 1)
        + ∑ i, pderiv (R := ZMod p) i (redp p m) ^ p * pderiv (R := ZMod p) j (redp p (h i))
        - redp p m ^ (p - 1) * pderiv (R := ZMod p) j (redp p m) := by
  classical
  set P := ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) with hP
  set D := pderiv (R := ℤ_[p]) j
  have hDP : ∀ y, D (P * y) = P * D y := fun y => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hP, Derivation.map_natCast, mul_zero,
      add_zero]
  have hDX : ∀ i, D (σ (X i)) = P * (X i ^ (p - 1) * D (X i) + D (h i)) := fun i => by
    rw [hh i, map_add, hDP, pderiv_pow, hP]; ring
  set T := ∑ i, σ (pderiv (R := ℤ_[p]) i m) * (X i ^ (p - 1) * D (X i) + D (h i)) with hT
  have hDσ : D (σ m) = P * T := by
    rw [hchain m j, hT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hDX i]; ring
  have hδ : D (delta hσ m) = T - m ^ (p - 1) * D m := by
    have hpd := congrArg D (p_mul_delta hσ m)
    rw [hDP, map_sub, hDσ, pderiv_pow] at hpd
    apply sub_eq_zero.1
    apply noPTorsion_series (p := p) (n := n)
    rw [mul_sub, hpd]
    simp only [hP]
    ring
  have hDr : ∀ y, redp p (D y) = pderiv (R := ZMod p) j (redp p y) := fun y => redp_pderiv j y
  rw [← hDr, hδ, map_sub, hT, map_sum]
  simp only [map_mul, map_add, map_pow, redp_frob_eq_pow hσ, redp_pderiv, hDr, redp_X]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 2
  rw [Finset.sum_eq_single j]
  · rw [pderiv_X_self]; ring
  · intro i _ hij
    rw [pderiv_X_of_ne hij]
    ring
  · intro h'; exact absurd (Finset.mem_univ j) h'

/-- The chain rule for `δ` for `x_i ↦ x_i ^ p + p h_i`, `h_i(0) = 0`. -/
theorem delta_chain_rule_frobForm (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (h0 : ∀ i, constantCoeff (h i) = 0) (m : MvPowerSeries (Fin n) ℤ_[p]) (j : Fin n) :
    pderiv (R := ZMod p) j (redp p (delta (frobForm_isFrobLift h h0) m))
      = pderiv (R := ZMod p) j (redp p m) ^ p * (X j : MvPowerSeries (Fin n) (ZMod p)) ^ (p - 1)
        + ∑ i, pderiv (R := ZMod p) i (redp p m) ^ p * pderiv (R := ZMod p) j (redp p (h i))
        - redp p m ^ (p - 1) * pderiv (R := ZMod p) j (redp p m) :=
  delta_chain_rule (frobForm_isFrobLift h h0) h (frobForm_X h h0) (pderiv_frobForm h h0) m j

end FrobLevel
