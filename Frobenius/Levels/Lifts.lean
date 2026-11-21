module

/-
Run r25, seat L4: substitution lifts `x_i ↦ x_i ^ p + p h_i` of `ℤ_[p][[x_1..x_n]]`, R-087
Lemma D1 and the core of Theorem N in the series setting, and the named examples of R-086 and
R-087 that the proved theorems reach.

* `substLift a ha`: the continuous `ℤ_[p]`-algebra map with `x_i ↦ a_i` (Mathlib's `substAlgHom`);
  `substLift_isFrobLift`: it is a Frobenius lift whenever `a_i ≡ x_i ^ p (mod p)`;
  `hasSubst_frobForm`, `redp_frobForm`: the form `a_i = x_i ^ p + p h_i` with `h_i(0) = 0`.
* `not_exists_dvd_of_pderiv`: a certificate for `J_B(f) = J` (every lift): if
  `f = σ b₀ + p ^ J e` and some partial derivative of `e mod p` is nonzero, then
  `f ∉ B + p ^ (J + 1) A`.
* `pow_mem_iff_delta_mem_series` (Lemma D1) and `pderiv_redp_delta_eq_zero` (Theorem N core):
  `m ^ p ∈ B ↔ δ(m) ∈ B`, and then every partial derivative of `δ(m) mod p` vanishes.
* Named lifts: `σ(x) = x ^ p + p x` in one variable with `f = 1 + x ^ p`: `L_f + 1 = k` for
  `1 ≤ k ≤ p` and `≥ p` beyond, while `L_f = 0` under the standard lift (`levelCount_std_one_add`);
  `σ = (x ^ p + p y, y ^ p)`: `L + 1 ≥ p` for `f = 1 + x`, and `L + 1 = k` for
  `f = 1 + p x + p ^ 2 y`, `1 ≤ k ≤ p`.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.PropT
public import Frobenius.Levels.G1
public import Frobenius.Levels.G1Series
public import Frobenius.Levels.ThmR

@[expose] public section

-- Port (Mathlib v4.35.0-rc2): restore the v4.33 instance path for `AddCommGroup (ZMod p)`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace FrobLevel

open MvPowerSeries

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

/-- The substitution `x_i ↦ a_i` as a ring endomorphism of `ℤ_[p][[x_1..x_n]]`. -/
noncomputable def substLift (a : Fin n → MvPowerSeries (Fin n) ℤ_[p]) (ha : HasSubst a) :
    MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p] :=
  (substAlgHom ha : MvPowerSeries (Fin n) ℤ_[p] →ₐ[ℤ_[p]] MvPowerSeries (Fin n) ℤ_[p])

theorem substLift_apply (a : Fin n → MvPowerSeries (Fin n) ℤ_[p]) (ha : HasSubst a)
    (g : MvPowerSeries (Fin n) ℤ_[p]) : substLift a ha g = subst a g := by
  rw [substLift, RingHom.coe_coe, coe_substAlgHom]

theorem substLift_X (a : Fin n → MvPowerSeries (Fin n) ℤ_[p]) (ha : HasSubst a) (i : Fin n) :
    substLift a ha (X i) = a i := by
  rw [substLift, RingHom.coe_coe]; exact substAlgHom_X ha i

/-- A substitution `x_i ↦ a_i` with `a_i ≡ x_i ^ p (mod p)` is a Frobenius lift. -/
theorem substLift_isFrobLift (a : Fin n → MvPowerSeries (Fin n) ℤ_[p]) (ha : HasSubst a)
    (hred : ∀ i, redp p (a i) = X i ^ p) : IsFrobLift p (substLift a ha) := by
  intro g
  refine (redp_eq_zero_iff p _).1 ?_
  rw [map_sub, sub_eq_zero, substLift_apply, map_pow]
  have h1 : redp p (subst a g) = subst (fun i => X i ^ p) (redp p g) := by
    have := map_subst ha (h := PadicInt.toZMod) g
    rw [redp, this]
    congr 1
    funext i
    exact hred i
  rw [h1]
  have h2 : subst (fun i => (X i : MvPowerSeries (Fin n) (ZMod p)) ^ p) (redp p g)
      = expand p hp.out.ne_zero (redp p g) := by
    rw [expand, coe_substAlgHom]
  rw [h2, ← map_frobenius_expand (p := p) (hp := hp.out.ne_zero), ZMod.frobenius_zmod, map_id,
    RingHom.id_apply]

/-- The form `a_i = x_i ^ p + p h_i` with `h_i(0) = 0` is a substitution. -/
theorem hasSubst_frobForm (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (h0 : ∀ i, constantCoeff (h i) = 0) :
    HasSubst (fun i => X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * h i) := by
  refine hasSubst_of_constantCoeff_zero fun i => ?_
  rw [map_add, map_pow, constantCoeff_X, zero_pow hp.out.ne_zero, map_mul, h0, mul_zero, add_zero]

theorem redp_frobForm (h : Fin n → MvPowerSeries (Fin n) ℤ_[p]) (i : Fin n) :
    redp p (X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * h i) = X i ^ p := by
  rw [map_add, map_mul, redp_p, zero_mul, add_zero, map_pow, redp, map_X]

/-- The lift `x_i ↦ x_i ^ p + p h_i` (with `h_i(0) = 0`). -/
noncomputable def frobForm (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (h0 : ∀ i, constantCoeff (h i) = 0) :
    MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p] :=
  substLift _ (hasSubst_frobForm h h0)

theorem frobForm_isFrobLift (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (h0 : ∀ i, constantCoeff (h i) = 0) : IsFrobLift p (frobForm h h0) :=
  substLift_isFrobLift _ _ (redp_frobForm h)

theorem frobForm_X (h : Fin n → MvPowerSeries (Fin n) ℤ_[p]) (h0 : ∀ i, constantCoeff (h i) = 0)
    (i : Fin n) :
    frobForm h h0 (X i) = X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * h i :=
  substLift_X _ _ i

section AnyLift

variable {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}

/-- **Certificate for `J_B(f) = J`** (every lift): `f = σ b₀ + p ^ J e` with `d ē ≠ 0`
gives `f ∉ B + p ^ (J + 1) A`. -/
theorem not_exists_dvd_of_pderiv (hσ : IsFrobLift p σ) {f b₀ e : MvPowerSeries (Fin n) ℤ_[p]}
    {J : ℕ} (hf : f = σ b₀ + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ J * e) {i : Fin n}
    (hi : pderiv (R := ZMod p) i (redp p e) ≠ 0) :
    ¬ ∃ b, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ (J + 1) ∣ f - σ b := by
  rintro ⟨b, hb⟩
  have ht := noPTorsion_series (p := p) (n := n)
  have hs : PSat p σ := pSat_of_domain hσ (redp p) (redp_eq_zero_iff p)
  have h1 : ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ J ∣ σ (b₀ - b) := by
    have : σ (b₀ - b) = (f - σ b) - ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ J * e := by
      rw [map_sub, hf]; ring
    rw [this]
    exact dvd_sub ((pow_dvd_pow _ (Nat.le_succ J)).trans hb) (dvd_mul_right _ _)
  obtain ⟨c, ⟨c', rfl⟩, hc⟩ := hs.pow ht J _ ⟨b₀ - b, rfl⟩ h1
  have h2 : f - σ b = ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ J * (e + σ c') := by
    have : f - σ b = σ (b₀ - b) + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ J * e := by
      rw [map_sub, hf]; ring
    rw [this, hc]; ring
  rw [h2, pow_succ] at hb
  have h3 : ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ∣ e + σ c' := by
    simpa using dvd_of_pow_mul_dvd (a := J) (b := 1) ht (by simpa [pow_succ] using hb)
  apply hi
  have : redp p e = - redp p (σ c') := by
    rw [eq_neg_iff_add_eq_zero, ← map_add]; exact (redp_eq_zero_iff p _).2 h3
  rw [this, map_neg, deriv_frob_eq_zero hσ _ (redp p) redp_p, neg_zero]

/-- **R-087 Lemma D1** on `ℤ_[p][[x_1..x_n]]`, every lift: `m ^ p ∈ B ↔ δ(m) ∈ B`. -/
theorem pow_mem_iff_delta_mem_series (hσ : IsFrobLift p σ) (m : MvPowerSeries (Fin n) ℤ_[p]) :
    m ^ p ∈ frobImage σ ↔ delta hσ m ∈ frobImage σ :=
  pow_mem_iff_delta_mem noPTorsion_series (pSat_of_domain hσ (redp p) (redp_eq_zero_iff p)) hσ m

/-- **Core of R-087 Theorem N**: if `m ^ p ∈ B` then `d (δ(m) mod p) = 0`, i.e. every partial
derivative of `δ(m) mod p` vanishes (`δ(m) mod p` is a `p`-th power). -/
theorem pderiv_redp_delta_eq_zero (hσ : IsFrobLift p σ) {m : MvPowerSeries (Fin n) ℤ_[p]}
    (hm : m ^ p ∈ frobImage σ) (i : Fin n) : pderiv (R := ZMod p) i (redp p (delta hσ m)) = 0 := by
  obtain ⟨c, hc⟩ := (pow_mem_iff_delta_mem_series hσ m).1 hm
  rw [← hc]; exact deriv_frob_eq_zero hσ _ (redp p) redp_p c

end AnyLift

/-! ### Named lifts -/

section Named

/-- `σ(x) = x ^ p + p x` on `ℤ_[p][[x]]` (one variable, `Fin 1`). -/
noncomputable def liftPX : MvPowerSeries (Fin 1) ℤ_[p] →+* MvPowerSeries (Fin 1) ℤ_[p] :=
  frobForm (fun _ => X 0) (fun _ => constantCoeff_X 0)

theorem liftPX_isFrobLift : IsFrobLift p (liftPX (p := p)) := frobForm_isFrobLift _ _

theorem liftPX_X : liftPX (p := p) (X 0) = X 0 ^ p + ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p]) * X 0 :=
  frobForm_X _ _ 0

theorem redp_X (i : Fin n) : redp p (X i : MvPowerSeries (Fin n) ℤ_[p]) = X i := by
  rw [redp, map_X]

/-- Under `x ↦ x ^ p + p x`, `f = 1 + x ^ p` has `J_B(f) = 1`; so `L_f(p, k) + 1 = k` for
`1 ≤ k ≤ p` (R-086 example: the value depends on the lift through `J_B`). -/
theorem levelCount_liftPX_one_add {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ p) :
    levelCount p (liftPX (p := p)) (1 + X 0 ^ p) k + 1 = k := by
  have hσ := liftPX_isFrobLift (p := p)
  have hdec : (1 + X 0 ^ p : MvPowerSeries (Fin 1) ℤ_[p])
      = liftPX (1 + X 0) + ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p]) ^ 1 * (- X 0) := by
    rw [map_add, map_one, liftPX_X]; ring
  have hunit : IsUnit (1 + X 0 ^ p : MvPowerSeries (Fin 1) ℤ_[p]) := by
    rw [isUnit_iff_constantCoeff]; simp [zero_pow hp.out.ne_zero]
  have hc : cdiv k 1 = k := by simp [cdiv]
  conv_rhs => rw [← hc]
  refine levelCount_G1_of_cdiv_le hσ hunit le_rfl hk ⟨1 + X 0, ?_⟩
    (not_exists_dvd_of_pderiv hσ hdec (i := 0) ?_) (by rw [hc]; exact hkp)
  · rw [hdec]; exact ⟨- X 0, by ring⟩
  · rw [map_neg, map_neg, redp_X, pderiv_X_self]; exact neg_ne_zero.2 one_ne_zero

/-- Beyond `k = p`: `L_f(p, k) + 1 ≥ p` for the same `f`. -/
theorem levelCount_liftPX_one_add_ge {k : ℕ} (hk : p < k) :
    p ≤ levelCount p (liftPX (p := p)) (1 + X 0 ^ p) k + 1 := by
  have hσ := liftPX_isFrobLift (p := p)
  have hdec : (1 + X 0 ^ p : MvPowerSeries (Fin 1) ℤ_[p])
      = liftPX (1 + X 0) + ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p]) ^ 1 * (- X 0) := by
    rw [map_add, map_one, liftPX_X]; ring
  have hunit : IsUnit (1 + X 0 ^ p : MvPowerSeries (Fin 1) ℤ_[p]) := by
    rw [isUnit_iff_constantCoeff]; simp [zero_pow hp.out.ne_zero]
  refine G1_ge_p hσ hunit (by omega) ⟨1 + X 0, ?_⟩
    (not_exists_dvd_of_pderiv hσ hdec (i := 0) ?_) (Or.inr (by omega))
  · rw [hdec]; exact ⟨- X 0, by ring⟩
  · rw [map_neg, map_neg, redp_X, pderiv_X_self]; exact neg_ne_zero.2 one_ne_zero

/-- Under the standard lift the same `f = 1 + x ^ p` lies in `B`: `L_f = 0`. -/
theorem levelCount_std_one_add {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) (1 + X 0 ^ p : MvPowerSeries (Fin 1) ℤ_[p]) k = 0 := by
  have hunit : IsUnit (1 + X 0 ^ p : MvPowerSeries (Fin 1) ℤ_[p]) := by
    rw [isUnit_iff_constantCoeff]; simp [zero_pow hp.out.ne_zero]
  refine levelCount_eq_zero_of_mem (frob_isFrobLift p (padicInt_pow_sub p)) hunit hk
    ⟨1 + X 0, ?_⟩
  rw [map_add, map_one, frob_apply, expand_X, sub_self]; exact dvd_zero _

/-- `σ = (x ^ p + p y, y ^ p)` on `ℤ_[p][[x, y]]`. -/
noncomputable def liftPY : MvPowerSeries (Fin 2) ℤ_[p] →+* MvPowerSeries (Fin 2) ℤ_[p] :=
  frobForm ![X 1, 0] (fun i => by fin_cases i <;> simp)

theorem liftPY_isFrobLift : IsFrobLift p (liftPY (p := p)) := frobForm_isFrobLift _ _

/-- Under `(x ^ p + p y, y ^ p)`, `f = 1 + x` has `L_f(p, k) + 1 ≥ p` for every `k ≥ 1`
(`d f̄ ≠ 0`; the note's value is `min(p ^ 2, S(p ^ k))`, whose lower half beyond `p` is open
here). -/
theorem levelCount_liftPY_one_add_x_ge {k : ℕ} (hk : 1 ≤ k) :
    p ≤ levelCount p (liftPY (p := p)) (1 + X 0 : MvPowerSeries (Fin 2) ℤ_[p]) k + 1 := by
  have hunit : IsUnit (1 + X 0 : MvPowerSeries (Fin 2) ℤ_[p]) := by
    rw [isUnit_iff_constantCoeff]; simp
  refine levelCount_ge_p_of_pderiv liftPY_isFrobLift hunit hk (i := 0) ?_
  rw [map_add, map_one, redp_X, map_add, pderiv_X_self, Derivation.map_one_eq_zero, zero_add]
  exact one_ne_zero

/-- Under `(x ^ p + p y, y ^ p)`, `f = 1 + p x + p ^ 2 y` (flag `(1, 1)`) has
`L_f(p, k) + 1 = k` for `1 ≤ k ≤ p`, as the note's formula `min(p ^ 2, min{m : v_p(m!) + m ≥ k})`
predicts. -/
theorem levelCount_liftPY_flag11 {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ p) :
    levelCount p (liftPY (p := p))
      (1 + (p : MvPowerSeries (Fin 2) ℤ_[p]) * X 0 + (p : MvPowerSeries (Fin 2) ℤ_[p]) ^ 2 * X 1)
      k + 1 = k := by
  have hσ := liftPY_isFrobLift (p := p)
  set f : MvPowerSeries (Fin 2) ℤ_[p] :=
    1 + (p : MvPowerSeries (Fin 2) ℤ_[p]) * X 0 + (p : MvPowerSeries (Fin 2) ℤ_[p]) ^ 2 * X 1
  have hdec : f = liftPY 1 + ((p : ℕ) : MvPowerSeries (Fin 2) ℤ_[p]) ^ 1 *
      (X 0 + (p : MvPowerSeries (Fin 2) ℤ_[p]) * X 1) := by
    rw [map_one]; ring
  have hunit : IsUnit f := by
    rw [isUnit_iff_constantCoeff]; simp [f]
  have hc : cdiv k 1 = k := by simp [cdiv]
  conv_rhs => rw [← hc]
  refine levelCount_G1_of_cdiv_le hσ hunit le_rfl hk ⟨1, ?_⟩
    (not_exists_dvd_of_pderiv hσ hdec (i := 0) ?_) (by rw [hc]; exact hkp)
  · rw [hdec, map_one]; exact ⟨X 0 + (p : MvPowerSeries (Fin 2) ℤ_[p]) * X 1, by ring⟩
  · rw [map_add, map_mul, redp_p, zero_mul, add_zero, redp_X, pderiv_X_self]
    exact one_ne_zero

end Named

end FrobLevel
