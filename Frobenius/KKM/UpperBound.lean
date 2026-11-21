module

public import Frobenius.KKM.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Monic

/-!
# The delta tower for `Φ_p` (upper bound)

Let `σ` be the Frobenius lift `σ(f)(z) = f(z ^ p)` of `ℤ⟦z⟧` and `δ(f) = (σ(f) - f ^ p) / p`.
The functional equation `Φ(z ^ p) = Φ(z) - z` says `σ(Φ) = Φ - z`, so for `A ∈ ℤ[z][t]`

  `A(z ^ p, Φ - z) = σ(A(z, Φ))`.

Define `A_0 = t`, `c_0 = 1`, `A_{a+1} = A_a ^ p - c_a ^ (p-1) A_a(z ^ p, t - z)`,
`c_{a+1} = -p c_a ^ p`. Then `A_a` is monic of `t`-degree `p ^ a` with coefficients in `ℤ[z]`, and

  `A_a(z, Φ) = c_a δ^a(Φ)` exactly, with `v_p(c_a) = (p ^ a - 1) / (p - 1)`.

For `d = ∑ d_a p ^ a` in base `p`, the product `∏ A_a ^ d_a` is monic of degree `d` and
`B_d(z, Φ)` is divisible by `p ^ v_p(d!)` (Legendre). This is condition (2.4) of Krattenthaler and
Müller (2025), Remark 5(2), for every `a`, and gives the upper bound in their Conjecture 4.
-/

@[expose] public section

namespace Frobenius.KKM

open PowerSeries

/-! ## The Frobenius lift and `δ` -/

section Lift

variable (p : ℕ) [hp : Fact p.Prime]

theorem prime_ne_zero : p ≠ 0 := hp.out.ne_zero

/-- The Frobenius lift `σ(f)(z) = f(z ^ p)` of `ℤ⟦z⟧`. -/
noncomputable def sigma : PowerSeries ℤ →ₐ[ℤ] PowerSeries ℤ :=
  PowerSeries.expand p (prime_ne_zero p)

theorem coeff_sigma (f : PowerSeries ℤ) (n : ℕ) :
    coeff n (sigma p f) = if p ∣ n then coeff (n / p) f else 0 := by
  rw [sigma, PowerSeries.coeff_expand]

/-- The Frobenius congruence `σ(f) ≡ f ^ p (mod p)` in `ℤ⟦z⟧`. -/
theorem dvd_coeff_sigma_sub_pow (f : PowerSeries ℤ) (n : ℕ) :
    (p : ℤ) ∣ coeff n (sigma p f - f ^ p) := by
  set φ := Int.castRingHom (ZMod p)
  have key : PowerSeries.map φ (sigma p f - f ^ p) = 0 := by
    have h := PowerSeries.map_frobenius_expand (R := ZMod p) p (prime_ne_zero p)
      (f := PowerSeries.map φ f)
    rw [ZMod.frobenius_zmod, PowerSeries.map_id] at h
    rw [map_sub, map_pow, sigma, PowerSeries.map_expand, sub_eq_zero]
    exact h
  have h2 := congrArg (coeff n) key
  rw [PowerSeries.coeff_map, map_zero] at h2
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h2

/-- `δ(f) = (σ(f) - f ^ p) / p`, computed coefficientwise. -/
noncomputable def delta (f : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => coeff n (sigma p f - f ^ p) / p

theorem natCast_mul_delta (f : PowerSeries ℤ) :
    (p : PowerSeries ℤ) * delta p f = sigma p f - f ^ p := by
  ext n
  rw [← map_natCast (PowerSeries.C (R := ℤ)), PowerSeries.coeff_C_mul, delta, coeff_mk]
  exact Int.mul_ediv_cancel' (dvd_coeff_sigma_sub_pow p f n)

theorem mul_mem_range_pow_iff (m : ℕ) :
    p * m ∈ Set.range (fun k : ℕ => p ^ k) ↔ m ∈ Set.range (fun k : ℕ => p ^ k) := by
  constructor
  · rintro ⟨k, hk⟩
    simp only at hk
    cases k with
    | zero => exact absurd (Nat.eq_one_of_mul_eq_one_right (by rw [← hk, pow_zero])) hp.out.ne_one
    | succ k =>
      refine ⟨k, Nat.eq_of_mul_eq_mul_left hp.out.pos ?_⟩
      simp only
      rw [← pow_succ', hk]
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, by simp [pow_succ']⟩

omit hp in
theorem mem_range_pow_iff_of_not_dvd {n : ℕ} (h : ¬ p ∣ n) :
    n ∈ Set.range (fun k : ℕ => p ^ k) ↔ n = 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    cases k with
    | zero => simp
    | succ k => exact absurd (dvd_pow_self p (Nat.succ_ne_zero k)) h
  · rintro rfl
    exact ⟨0, pow_zero p⟩

/-- The functional equation `Φ(z ^ p) = Φ(z) - z`. -/
theorem sigma_Phi : sigma p (Phi p) = Phi p - X := by
  classical
  ext n
  simp only [coeff_sigma, map_sub, coeff_Phi, coeff_X, Set.indicator_apply, Pi.one_apply]
  by_cases hdiv : p ∣ n
  · obtain ⟨m, rfl⟩ := hdiv
    have hn1 : p * m ≠ 1 := fun h => hp.out.ne_one (Nat.eq_one_of_mul_eq_one_right h)
    simp only [dvd_mul_right, Nat.mul_div_cancel_left m hp.out.pos, mul_mem_range_pow_iff, hn1,
      ↓reduceIte, sub_zero]
  · simp only [hdiv, mem_range_pow_iff_of_not_dvd p hdiv, ↓reduceIte]
    split_ifs <;> simp

/-- `σ` on polynomial coefficients is `Polynomial.expand`. -/
theorem sigma_coe (q : Polynomial ℤ) :
    sigma p (q : PowerSeries ℤ) = ((Polynomial.expand ℤ p q : Polynomial ℤ) : PowerSeries ℤ) := by
  ext n
  simp only [coeff_sigma, Polynomial.coeff_coe, Polynomial.coeff_expand hp.out.pos]

theorem sigma_comp_coe :
    (sigma p).toRingHom.comp Polynomial.coeToPowerSeries.ringHom =
      Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.expand ℤ p).toRingHom := by
  refine RingHom.ext fun q => ?_
  exact sigma_coe p q

/-- `A(z, t) ↦ A(z ^ p, t - z)`. -/
noncomputable def shift (A : Polynomial (Polynomial ℤ)) : Polynomial (Polynomial ℤ) :=
  (A.map (Polynomial.expand ℤ p).toRingHom).comp (Polynomial.X - Polynomial.C Polynomial.X)

/-- The key identity `A(z ^ p, Φ - z) = σ(A(z, Φ))`. -/
theorem evalPhi_shift (A : Polynomial (Polynomial ℤ)) :
    evalPhi p (shift p A) = sigma p (evalPhi p A) := by
  have h1 : Polynomial.eval₂ Polynomial.coeToPowerSeries.ringHom (Phi p)
      (Polynomial.X - Polynomial.C Polynomial.X) = Phi p - X := by
    simp [Polynomial.eval₂_sub, Polynomial.coe_X]
  have h2 := Polynomial.hom_eval₂ A Polynomial.coeToPowerSeries.ringHom (sigma p).toRingHom (Phi p)
  rw [sigma_comp_coe] at h2
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
  rw [evalPhi, evalPhi, shift, Polynomial.eval₂_comp, Polynomial.eval₂_map, h1, h2, sigma_Phi]
  rfl

end Lift

/-! ## The tower -/

/-- `c_0 = 1`, `c_{a+1} = -p c_a ^ p`. -/
def c (p : ℕ) : ℕ → ℤ
  | 0 => 1
  | a + 1 => -(p : ℤ) * c p a ^ p

/-- `e_0 = 0`, `e_{a+1} = p e_a + 1`, so that `e_a = (p ^ a - 1) / (p - 1) = v_p(c_a)`. -/
def e (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | a + 1 => p * e p a + 1

/-- The tower `A_0 = t`, `A_{a+1} = A_a ^ p - c_a ^ (p-1) A_a(z ^ p, t - z)`. -/
noncomputable def tower (p : ℕ) [Fact p.Prime] : ℕ → Polynomial (Polynomial ℤ)
  | 0 => Polynomial.X
  | a + 1 => tower p a ^ p - Polynomial.C (Polynomial.C (c p a ^ (p - 1))) * shift p (tower p a)

section Tower

variable (p : ℕ) [hp : Fact p.Prime]

omit hp in
theorem pow_e_dvd_c (a : ℕ) : (p : ℤ) ^ e p a ∣ c p a := by
  induction a with
  | zero => simp [e, c]
  | succ a ih =>
    rw [e, c, show (p : ℤ) ^ (p * e p a + 1) = (p : ℤ) * ((p : ℤ) ^ e p a) ^ p by ring]
    exact mul_dvd_mul (dvd_neg.mpr dvd_rfl) (pow_dvd_pow_of_dvd ih p)

theorem sub_one_mul_e_add_one (a : ℕ) : (p - 1) * e p a + 1 = p ^ a := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  induction a with
  | zero => simp [e]
  | succ a ih =>
    rw [e, pow_succ, ← ih]
    zify [hp1]
    ring

omit hp in
/-- `c_a = ± p ^ e_a`. (Proof contributed by the verifier seat V.) -/
theorem c_eq_sign_mul (a : ℕ) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ c p a = s * (p : ℤ) ^ e p a := by
  induction a with
  | zero => exact ⟨1, Or.inl rfl, by simp [c, e]⟩
  | succ a ih =>
    obtain ⟨s, hs, hc⟩ := ih
    refine ⟨-(s ^ p), ?_, ?_⟩
    · rcases hs with rfl | rfl
      · simp
      · rcases neg_one_pow_eq_or ℤ p with h | h <;> simp [h]
    · rw [c, e, hc, mul_pow, pow_succ, pow_mul]
      ring

/-- `v_p(c_a) = e_a = (p ^ a - 1) / (p - 1)`. (Proof contributed by the verifier seat V.) -/
theorem padicValInt_c (a : ℕ) : padicValInt p (c p a) = e p a := by
  obtain ⟨s, hs, hc⟩ := c_eq_sign_mul p a
  rw [hc]
  rcases hs with rfl | rfl
  · rw [one_mul, show ((p : ℤ) ^ e p a) = ((p ^ e p a : ℕ) : ℤ) by push_cast; rfl,
      padicValInt.of_nat, padicValNat.prime_pow]
  · rw [neg_one_mul, show padicValInt p (-((p : ℤ) ^ e p a)) = padicValInt p ((p : ℤ) ^ e p a) by
      simp [padicValInt], show ((p : ℤ) ^ e p a) = ((p ^ e p a : ℕ) : ℤ) by push_cast; rfl,
      padicValInt.of_nat, padicValNat.prime_pow]

/-- **Tower identity**: `A_a(z, Φ) = c_a δ^a(Φ)`. -/
theorem evalPhi_tower (a : ℕ) :
    evalPhi p (tower p a) = (c p a : PowerSeries ℤ) * (delta p)^[a] (Phi p) := by
  induction a with
  | zero => simp [tower, c, evalPhi]
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    set y := (delta p)^[a] (Phi p)
    have hev : evalPhi p (tower p (a + 1)) = evalPhi p (tower p a) ^ p -
        ((c p a ^ (p - 1) : ℤ) : PowerSeries ℤ) * evalPhi p (shift p (tower p a)) := by
      simp only [tower, evalPhi, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_C, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
      rw [eq_intCast]
    have hd := natCast_mul_delta p y
    have hpow : ((c p a : PowerSeries ℤ)) ^ (p - 1) * (c p a : PowerSeries ℤ) =
        (c p a : PowerSeries ℤ) ^ p := by
      rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le]
    rw [hev, evalPhi_shift, ih, map_mul, map_intCast, c]
    push_cast
    linear_combination ((c p a : PowerSeries ℤ) ^ p) * hd - sigma p y * hpow

theorem tower_monic_natDegree (a : ℕ) :
    (tower p a).Monic ∧ (tower p a).natDegree = p ^ a := by
  induction a with
  | zero => exact ⟨Polynomial.monic_X, by simp [tower]⟩
  | succ a ih =>
    obtain ⟨hm, hdeg⟩ := ih
    have hpow : (tower p a ^ p).Monic := hm.pow p
    have hdegp : (tower p a ^ p).natDegree = p ^ (a + 1) := by
      rw [hm.natDegree_pow, hdeg, pow_succ, mul_comm]
    have hshift : (shift p (tower p a)).natDegree ≤ p ^ a := by
      calc (shift p (tower p a)).natDegree
          ≤ ((tower p a).map (Polynomial.expand ℤ p).toRingHom).natDegree *
              (Polynomial.X - Polynomial.C (Polynomial.X : Polynomial ℤ)).natDegree :=
            Polynomial.natDegree_comp_le
        _ ≤ (tower p a).natDegree * 1 := by
            rw [Polynomial.natDegree_X_sub_C]
            exact Nat.mul_le_mul_right 1 (Polynomial.natDegree_map_le)
        _ = p ^ a := by rw [hdeg, mul_one]
    have hlt : (Polynomial.C (Polynomial.C (c p a ^ (p - 1))) * shift p (tower p a)).natDegree <
        (tower p a ^ p).natDegree := by
      rw [hdegp]
      calc _ ≤ (shift p (tower p a)).natDegree := Polynomial.natDegree_C_mul_le _ _
        _ ≤ p ^ a := hshift
        _ < p ^ (a + 1) := Nat.pow_lt_pow_right hp.out.one_lt (Nat.lt_succ_self a)
    refine ⟨hpow.sub_of_left (Polynomial.degree_lt_degree hlt), ?_⟩
    rw [tower, Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hdegp]

/-- `A_a(z, Φ) ≡ 0 (mod p ^ ((p ^ a - 1) / (p - 1)))`: condition (2.4) of Krattenthaler and Müller. -/
theorem vanishesMod_tower (a : ℕ) : VanishesMod p (e p a) (tower p a) := by
  intro n
  rw [evalPhi_tower, ← map_intCast (PowerSeries.C (R := ℤ)), PowerSeries.coeff_C_mul]
  exact dvd_mul_of_dvd_left (pow_e_dvd_c p a) _

/-- `A_1 = t ^ p - t + z`. (Proof contributed by the verifier seat V.) -/
theorem tower_one : tower p 1 = Polynomial.X ^ p - Polynomial.X + Polynomial.C Polynomial.X := by
  simp [tower, c, shift]
  ring

/-- `A_2 = (t ^ p - t + z) ^ p - (-p) ^ (p - 1) ((t - z) ^ p - t + z + z ^ p)`. (Proof contributed
by the verifier seat V.) -/
theorem tower_two : tower p 2 =
    (Polynomial.X ^ p - Polynomial.X + Polynomial.C Polynomial.X) ^ p -
      Polynomial.C (Polynomial.C ((-(p : ℤ)) ^ (p - 1))) *
        ((Polynomial.X - Polynomial.C Polynomial.X) ^ p - Polynomial.X +
          Polynomial.C Polynomial.X + Polynomial.C (Polynomial.X ^ p)) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, tower, tower_one]
  simp [c, shift, Polynomial.map_pow, Polynomial.expand_X]
  left
  ring

/-! ## Digit products -/

/-- `∏_j A_{i+j} ^ (L[j])`. -/
noncomputable def digitProd : List ℕ → ℕ → Polynomial (Polynomial ℤ)
  | [], _ => 1
  | x :: L, i => tower p i ^ x * digitProd L (i + 1)

/-- `∑_j L[j] e_{i+j}`. -/
def wsum : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: L, i => x * e p i + wsum L (i + 1)

theorem digitProd_monic_natDegree (L : List ℕ) (i : ℕ) :
    (digitProd p L i).Monic ∧ (digitProd p L i).natDegree = p ^ i * Nat.ofDigits p L := by
  induction L generalizing i with
  | nil => simp [digitProd]
  | cons x L ih =>
    obtain ⟨hm, hd⟩ := ih (i + 1)
    obtain ⟨tm, td⟩ := tower_monic_natDegree p i
    refine ⟨(tm.pow x).mul hm, ?_⟩
    rw [digitProd, (tm.pow x).natDegree_mul hm, (tm).natDegree_pow, td, hd, Nat.ofDigits_cons,
      pow_succ]
    ring

theorem evalPhi_digitProd (L : List ℕ) (i : ℕ) :
    ∃ g : PowerSeries ℤ, evalPhi p (digitProd p L i) = (p : PowerSeries ℤ) ^ wsum p L i * g := by
  induction L generalizing i with
  | nil => exact ⟨1, by simp [digitProd, wsum, evalPhi]⟩
  | cons x L ih =>
    obtain ⟨g, hg⟩ := ih (i + 1)
    obtain ⟨u, hu⟩ := pow_e_dvd_c p i
    refine ⟨((u : PowerSeries ℤ) * (delta p)^[i] (Phi p)) ^ x * g, ?_⟩
    have hev : evalPhi p (digitProd p (x :: L) i) =
        evalPhi p (tower p i) ^ x * evalPhi p (digitProd p L (i + 1)) := by
      simp only [digitProd, evalPhi, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
    rw [hev, hg, evalPhi_tower, hu, wsum]
    push_cast
    ring

theorem wsum_spec (L : List ℕ) (i : ℕ) :
    (p - 1) * wsum p L i + L.sum = p ^ i * Nat.ofDigits p L := by
  induction L generalizing i with
  | nil => simp [wsum]
  | cons x L ih =>
    have h1 := sub_one_mul_e_add_one p i
    have h2 := ih (i + 1)
    rw [wsum, List.sum_cons, Nat.ofDigits_cons]
    calc (p - 1) * (x * e p i + wsum p L (i + 1)) + (x + L.sum)
        = x * ((p - 1) * e p i + 1) + ((p - 1) * wsum p L (i + 1) + L.sum) := by ring
      _ = x * p ^ i + p ^ i * p * Nat.ofDigits p L := by rw [h1, h2, pow_succ]
      _ = p ^ i * (x + p * Nat.ofDigits p L) := by ring

/-- The weight of the base-`p` digits of `d` is `v_p(d!)` (Legendre). -/
theorem wsum_digits (d : ℕ) : wsum p (Nat.digits p d) 0 = padicValNat p d.factorial := by
  have h1 := wsum_spec p (Nat.digits p d) 0
  rw [pow_zero, one_mul, Nat.ofDigits_digits] at h1
  have h2 := sub_one_mul_padicValNat_factorial (p := p) d
  have h3 := Nat.digit_sum_le p d
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  apply Nat.eq_of_mul_eq_mul_left hp1
  omega

/-- **Upper bound.** For every `d` there is a monic `B ∈ ℤ[z][t]` of `t`-degree `d` with
`B(z, Φ) ≡ 0 (mod p ^ v_p(d!))`. -/
theorem exists_monic_vanishesMod_factorial (d : ℕ) :
    ∃ B : Polynomial (Polynomial ℤ), B.Monic ∧ B.natDegree = d ∧
      VanishesMod p (padicValNat p d.factorial) B := by
  refine ⟨digitProd p (Nat.digits p d) 0, (digitProd_monic_natDegree p _ 0).1, ?_, ?_⟩
  · rw [(digitProd_monic_natDegree p _ 0).2, pow_zero, one_mul, Nat.ofDigits_digits]
  · intro n
    obtain ⟨g, hg⟩ := evalPhi_digitProd p (Nat.digits p d) 0
    rw [hg, wsum_digits, ← map_natCast (PowerSeries.C (R := ℤ)), ← map_pow,
      PowerSeries.coeff_C_mul]
    exact dvd_mul_right _ _

theorem exists_monic_vanishesMod_of_dvd (γ d : ℕ) (h : p ^ γ ∣ d.factorial) :
    ∃ B : Polynomial (Polynomial ℤ), B.Monic ∧ B.natDegree = d ∧ VanishesMod p γ B := by
  obtain ⟨B, hm, hd, hv⟩ := exists_monic_vanishesMod_factorial p d
  have hle : γ ≤ padicValNat p d.factorial :=
    (padicValNat_dvd_iff_le (Nat.factorial_ne_zero d)).mp h
  exact ⟨B, hm, hd, fun n => (pow_dvd_pow (p : ℤ) hle).trans (hv n)⟩

end Tower

end Frobenius.KKM
