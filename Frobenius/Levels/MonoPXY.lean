module

/-
Run r25, seat L10: note Prop `monotests`, last sentence (R-087): for `p ≥ 3` the lift
`σ(x) = x ^ p + p x y`, `σ(y) = y ^ p` of `ℤ_[p][[x, y]]` has `Λ = 0` (so the linear test (a)
is passed trivially: `Λ` is idempotent) and no monomial image, by test (b).

* `liftPXY_Lambda_zero`: `Λ = 0`.
* `pxy_key`: if `m ^ p ∈ B`, then `a ^ p (x ^ (p-1) + y) = m̄ ^ (p-1) a` with `a = ∂_x m̄`
  (L8's Theorem N, `thmN_poly_frobForm`, x-coordinate).
* `pxy_dx_eq_zero`: then `a = 0` (total order: `(p-1) ord a + 1 = (p-1) ord m̄`, impossible
  for `p - 1 ≥ 2`).
* `liftPXY_not_monomial`: no `m_1, m_2` with `m_i ^ p ∈ B` and invertible linear parts mod `p`
  (the note's Definition `monomial`, in L8's form).

Lean v4.33.1 with Mathlib; no sorry, no axioms beyond propext, Classical.choice, Quot.sound.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.G1Series
public import Frobenius.Levels.Lifts
public import Frobenius.Levels.D1Gen
public import Frobenius.Levels.ThmN

@[expose] public section

namespace L10

open MvPowerSeries FrobLevel

variable {p : ℕ} [hp : Fact p.Prime]

/-- `h = (x y, 0)`. -/
noncomputable def hPXY : Fin 2 → MvPowerSeries (Fin 2) ℤ_[p] := ![X 0 * X 1, 0]

theorem hPXY_const : ∀ i, constantCoeff (hPXY (p := p) i) = 0 := by
  intro i; fin_cases i <;> simp [hPXY]

/-- `σ(x) = x ^ p + p x y`, `σ(y) = y ^ p`. -/
noncomputable def liftPXY : MvPowerSeries (Fin 2) ℤ_[p] →+* MvPowerSeries (Fin 2) ℤ_[p] :=
  frobForm hPXY hPXY_const

theorem liftPXY_isFrobLift : IsFrobLift p (liftPXY (p := p)) := frobForm_isFrobLift _ _

theorem liftPXY_X0 : liftPXY (p := p) (X 0)
    = X 0 ^ p + ((p : ℕ) : MvPowerSeries (Fin 2) ℤ_[p]) * (X 0 * X 1) := by
  rw [liftPXY, frobForm_X]; simp [hPXY]

theorem liftPXY_X1 : liftPXY (p := p) (X 1) = X 1 ^ p := by
  rw [liftPXY, frobForm_X]; simp [hPXY]

/-- `Λ = 0` for this lift. -/
theorem liftPXY_Lambda_zero : Λmat (hPXY (p := p)) = 0 := by
  ext i j
  fin_cases i
  · simp only [Λmat, hPXY, Matrix.zero_apply]
    show PadicInt.toZMod (coeff (Finsupp.single j 1) (X 0 * X 1 : MvPowerSeries (Fin 2) ℤ_[p])) = 0
    rw [X, X, monomial_mul_monomial, coeff_monomial, if_neg]
    · simp
    · intro h
      have h0 := congrArg (fun d => d 0) h
      have h1 := congrArg (fun d => d 1) h
      fin_cases j <;> simp_all
  · simp [Λmat, hPXY]

theorem pxy_key {m : MvPowerSeries (Fin 2) ℤ_[p]} (hm : m ^ p ∈ frobImage (liftPXY (p := p))) :
    pderiv (R := ZMod p) 0 (redp p m) ^ p * ((X 0 : MvPowerSeries (Fin 2) (ZMod p)) ^ (p - 1) + X 1)
      = redp p m ^ (p - 1) * pderiv (R := ZMod p) 0 (redp p m) := by
  have h := thmN_poly_frobForm (p := p) hPXY hPXY_const hm 0
  rw [← h, Fin.sum_univ_two]
  have h0 : redp p (hPXY (p := p) 0) = X 0 * X 1 := by simp [hPXY, redp]
  have h1 : redp p (hPXY (p := p) 1) = 0 := by simp [hPXY]
  rw [h0, h1, map_zero, mul_zero, add_zero, Derivation.leibniz, pderiv_X_self,
    pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide), smul_zero, zero_add, smul_eq_mul, mul_one]
  ring

theorem order_pow_fin2 (f : MvPowerSeries (Fin 2) (ZMod p)) (k : ℕ) :
    (f ^ k).order = k • f.order := by
  induction k with
  | zero => simp [order, weightedOrder_one]
  | succ k ih => rw [pow_succ, order_mul, ih, succ_nsmul]

theorem order_X_fin2 (i : Fin 2) : (X i : MvPowerSeries (Fin 2) (ZMod p)).order = 1 := by
  rw [X, order_monomial_of_ne_zero one_ne_zero]
  simp

theorem order_q (hp3 : 3 ≤ p) :
    ((X 0 : MvPowerSeries (Fin 2) (ZMod p)) ^ (p - 1) + X 1).order = 1 := by
  have h1 : ((X 0 : MvPowerSeries (Fin 2) (ZMod p)) ^ (p - 1)).order = ((p - 1 : ℕ) : ℕ∞) := by
    rw [order_pow_fin2, order_X_fin2, nsmul_eq_mul, mul_one]
  rw [order_add_of_order_ne, h1, order_X_fin2]
  · have : (1 : ℕ∞) ≤ ((p - 1 : ℕ) : ℕ∞) := by exact_mod_cast (by omega : 1 ≤ p - 1)
    exact inf_eq_right.2 this
  · rw [h1, order_X_fin2]
    intro h
    have : p - 1 = 1 := by exact_mod_cast h
    omega

/-- **If `m ^ p ∈ B` then `∂_x m̄ = 0`** (`p ≥ 3`). -/
theorem pxy_dx_eq_zero (hp3 : 3 ≤ p) {m : MvPowerSeries (Fin 2) ℤ_[p]}
    (hm : m ^ p ∈ frobImage (liftPXY (p := p))) : pderiv (R := ZMod p) 0 (redp p m) = 0 := by
  by_contra ha
  set a := pderiv (R := ZMod p) 0 (redp p m) with ha_def
  set M := redp p m with hM_def
  set q : MvPowerSeries (Fin 2) (ZMod p) := (X 0) ^ (p - 1) + X 1 with hq_def
  have key : a ^ p * q = M ^ (p - 1) * a := pxy_key hm
  have hp1 : p = (p - 1) + 1 := by omega
  have h2 : a ^ (p - 1) * q = M ^ (p - 1) := by
    apply mul_left_cancel₀ ha
    calc a * (a ^ (p - 1) * q) = a ^ p * q := by
          rw [← mul_assoc, ← pow_succ']; congr 2; omega
      _ = M ^ (p - 1) * a := key
      _ = a * M ^ (p - 1) := mul_comm _ _
  have hq : q.order = 1 := order_q hp3
  have hq0 : q ≠ 0 := by
    intro h; rw [h, order_zero] at hq; exact ENat.top_ne_one hq
  have hM0 : M ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega)] at h2
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact ha (pow_eq_zero_iff (by omega) |>.1 h3)
    · exact hq0 h3
  have ho := congrArg MvPowerSeries.order h2
  rw [order_mul, order_pow_fin2, order_pow_fin2, hq] at ho
  have hafin := (ne_zero_iff_order_finite).1 ha
  have hMfin := (ne_zero_iff_order_finite).1 hM0
  rw [← hafin, ← hMfin, nsmul_eq_mul, nsmul_eq_mul] at ho
  have ho' : (p - 1) * a.order.toNat + 1 = (p - 1) * M.order.toNat := by exact_mod_cast ho
  have hdvd : (p - 1) ∣ 1 := by
    have : (p - 1) ∣ (p - 1) * a.order.toNat + 1 := ho' ▸ dvd_mul_right _ _
    exact (Nat.dvd_add_right (dvd_mul_right _ _)).1 this
  have := Nat.le_of_dvd one_pos hdvd
  omega

/-- If `m ^ p ∈ B` then the `x`-coefficient of `m` is `0` modulo `p`. -/
theorem pxy_linX_zero (hp3 : 3 ≤ p) {m : MvPowerSeries (Fin 2) ℤ_[p]}
    (hm : m ^ p ∈ frobImage (liftPXY (p := p))) :
    PadicInt.toZMod (coeff (Finsupp.single 0 1) m) = 0 := by
  have h := congrArg (coeff 0) (pxy_dx_eq_zero hp3 hm)
  rw [coeff_pderiv, zero_add] at h
  simpa [redp, coeff_map] using h

/-- **`x ^ p + p x y`, `y ^ p` (`p ≥ 3`) has no monomial image** (note Prop `monotests`,
last sentence), although `Λ = 0` is idempotent (`liftPXY_Lambda_zero`). -/
theorem liftPXY_not_monomial (hp3 : 3 ≤ p) :
    ¬ ∃ m : Fin 2 → MvPowerSeries (Fin 2) ℤ_[p],
      (∀ i, m i ^ p ∈ frobImage (liftPXY (p := p))) ∧ IsUnit (linMat m) := by
  rintro ⟨m, hm, hu⟩
  have hcol : ∀ i, linMat m i 0 = 0 := fun i => pxy_linX_zero hp3 (hm i)
  have hdet : (linMat m).det = 0 := Matrix.det_eq_zero_of_column_eq_zero 0 hcol
  rw [Matrix.isUnit_iff_isUnit_det, hdet] at hu
  exact not_isUnit_zero hu

/-- Instance: `p = 3` (the hypothesis `3 ≤ p` is met). -/
theorem liftPXY_not_monomial_three :
    ¬ ∃ m : Fin 2 → MvPowerSeries (Fin 2) ℤ_[3],
      (∀ i, m i ^ 3 ∈ frobImage (liftPXY (p := 3))) ∧ IsUnit (linMat m) :=
  liftPXY_not_monomial (p := 3) le_rfl

end L10
