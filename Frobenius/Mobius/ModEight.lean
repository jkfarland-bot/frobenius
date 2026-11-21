module

public import Frobenius.Mobius.Levels

/-!
# The Mertens function modulo 8 through the squarefree count (displayed form)

Numbers refer to J. S. Farland, *A proof of a conjecture of Kauers, Krattenthaler and
Müller, and exact level counts for Frobenius lifts* (2026), the larger paper.

Theorem 8.1 (Section 8). With
`G = (d_2 - E_2 ζ) / 2` (`G8`, exact division) and `a = G * E_4(μ)` (`a8`),

  `μ ≡ 2 ζ * E_2(μ) - d_3 * E_2(μ * μ - 4 a)  (mod 8)`            (`mod_eight_display`)

and, for every `x`, with `Q(x) = ∑_{m² ≤ x} μ(m) ⌊x / m²⌋` (`sqfQ`) and
`D_3(t) = ∑_{n ≤ t} d_3(n)` (`D3`),

  `M(x) ≡ 2 Q(x) - ∑_{m² ≤ x} (μ * μ)(m) D_3(x / m²) + 4 ∑_{m² ≤ x} a(m) D_3(x / m²)  (mod 8)`
                                                                    (`mertens_mod_eight`).

Here `d_2 = ζ ^ 2`, `d_3 = ζ ^ 3` and `E_j = frobPush j`. The existing `mod_eight_identity`
(`μ ≡ ζ * E_2(2 ζ h) + ζ ^ 3 * E_2(-h)` with `h = μ ^ 2 + 4 D μ ^ 4`, `D = δ(ζ) = -G`) is the third
identity of the remark after Theorem 8.1; `mod_eight_identity_cong_display` shows that its
right side and the displayed one agree modulo 8, and the displayed form is derived from it.
The summed form is stated for natural `x`; for real `x ≥ 1` both sides depend only on `⌊x⌋`.
`mod_eight_correction_needed`: without the term `4 a` the pointwise identity fails (at `n = 4`).
`sqfQ_eq_card`: `Q(x)` is the number of squarefree `n ≤ x`.
-/

@[expose] public section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace FrobCong

section ModEightDisplay

local notation "AF" => ArithmeticFunction ℤ

/-- `E_a ∘ E_b = E_(b a)`. -/
theorem frobPush_frobPush {R : Type*} [CommRing R] {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (f : ArithmeticFunction R) : frobPush a (frobPush b f) = frobPush (b * a) f := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  by_cases h : ∃ j, j ^ (b * a) = n
  · obtain ⟨j, rfl⟩ := h
    have hj : j ≠ 0 := by rintro rfl; exact hn (zero_pow (mul_ne_zero hb ha))
    rw [pow_mul, frobPush_apply_pow ha _ (pow_ne_zero _ hj), frobPush_apply_pow hb _ hj,
      ← pow_mul, frobPush_apply_pow (mul_ne_zero hb ha) _ hj]
  · rw [frobPush_apply_of_not f h]
    by_cases h' : ∃ i, i ^ a = n
    · obtain ⟨i, rfl⟩ := h'
      have hi : i ≠ 0 := by rintro rfl; exact hn (zero_pow ha)
      rw [frobPush_apply_pow ha _ hi]
      refine frobPush_apply_of_not f ?_
      rintro ⟨j, hj⟩
      exact h ⟨j, by rw [pow_mul, hj]⟩
    · exact frobPush_apply_of_not _ h'

/-- `G = (d_2 - E_2 ζ) / 2`, exact division by `zeta_pow_cong` (`d_2 = ζ ^ 2`). -/
def G8 : AF :=
  ⟨fun n => ((ζ : AF) ^ 2 - frobPush 2 (ζ : AF)) n / 2, by simp⟩

theorem G8_eq_neg_dZ : G8 = -dZ := by
  ext n
  rw [ArithmeticFunction.neg_apply, dZ_apply]
  show ((ζ : AF) ^ 2 - frobPush 2 (ζ : AF)) n / 2 = _
  rw [sub_apply', sub_apply']
  have h := zeta_pow_cong 2 n
  push_cast at h
  obtain ⟨c, hc⟩ := h
  rw [hc, show (frobPush 2 (ζ : AF)) n - ((ζ : AF) ^ 2) n = -(2 * c) by linarith]
  rw [Int.mul_ediv_cancel_left _ two_ne_zero, neg_mul_eq_mul_neg,
    Int.mul_ediv_cancel_left _ two_ne_zero, neg_neg]

theorem two_mul_G8 : (2 : AF) * G8 = (ζ : AF) ^ 2 - frobPush 2 (ζ : AF) := by
  rw [G8_eq_neg_dZ, mul_neg, two_mul_dZ, neg_sub]

/-- `a = G * E_4(μ)`. -/
def a8 : AF := G8 * frobPush 4 (μ : AF)

theorem natCast_dvd_iff_cong (m : ℕ) (A B : AF) : (m : AF) ∣ A - B ↔ Cong m A B :=
  (cong_iff_dvd m A B).symm

/-- `μ ^ 4 ≡ E_4(μ) (mod 2)`: the Frobenius congruence twice. -/
theorem moebius_pow_four_cong : (2 : AF) ∣ (μ : AF) ^ 4 - frobPush 4 (μ : AF) := by
  have h1 : ((2 : ℕ) : AF) ∣ ((μ : AF) ^ 2) ^ 2 - frobPush 2 ((μ : AF) ^ 2) :=
    (cong_iff_dvd 2 _ _).1 (cong_pow_frobPush 2 _)
  have h2 : ((2 : ℕ) : AF) ∣ (μ : AF) ^ 2 - frobPush 2 (μ : AF) :=
    (cong_iff_dvd 2 _ _).1 (cong_pow_frobPush 2 _)
  push_cast at h1 h2
  obtain ⟨W2, hW2⟩ := h2
  have h3 : frobPush 2 ((μ : AF) ^ 2) - frobPush 4 (μ : AF) =
      2 * frobHom two_ne_zero W2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, ← frobPush_frobPush two_ne_zero two_ne_zero]
    have : frobPush 2 ((μ : AF) ^ 2) - frobPush 2 (frobPush 2 (μ : AF)) =
        frobHom two_ne_zero ((μ : AF) ^ 2 - frobPush 2 (μ : AF)) := by
      rw [map_sub]; rfl
    rw [this, hW2, map_mul, map_ofNat]
  rw [show (μ : AF) ^ 4 - frobPush 4 (μ : AF) =
      (((μ : AF) ^ 2) ^ 2 - frobPush 2 ((μ : AF) ^ 2)) +
        (frobPush 2 ((μ : AF) ^ 2) - frobPush 4 (μ : AF)) by ring, h3]
  exact dvd_add h1 (dvd_mul_right _ _)

/-- The right side of the existing `mod_eight_identity` and the right side of Theorem 8.1
agree modulo 8. -/
theorem mod_eight_identity_cong_display :
    Cong 8 ((ζ : AF) * frobPush 2 (2 * (ζ : AF) * hE) + (ζ : AF) ^ 3 * frobPush 2 (-hE))
      (2 * (ζ : AF) * frobPush 2 (μ : AF) - (ζ : AF) ^ 3 * frobPush 2 ((μ : AF) ^ 2 - 4 * a8)) := by
  rw [← natCast_dvd_iff_cong]
  obtain ⟨W, hW⟩ := moebius_pow_four_cong
  set E2 := frobHom (R := ℤ) two_ne_zero with hE2
  have hΦ : ∀ f : AF, frobPush 2 f = E2 f := fun f => rfl
  have R1 : (ζ : AF) * μ = 1 := coe_zeta_mul_moebius
  have R2 : E2 (ζ : AF) * E2 (μ : AF) = 1 := by rw [← map_mul, R1, map_one]
  have hW' : E2 ((μ : AF) ^ 4) - E2 (frobPush 4 (μ : AF)) = 2 * E2 W := by
    rw [← map_sub, hW, map_mul, map_ofNat]
  rw [hΦ, hΦ, hΦ, hΦ, hE, a8, G8_eq_neg_dZ]
  simp only [map_mul, map_add, map_sub, map_neg, map_pow, map_ofNat]
  simp only [map_pow] at hW'
  refine ⟨(ζ : AF) * E2 (ζ : AF) * E2 dZ * E2 (μ : AF) ^ 4 - (ζ : AF) ^ 3 * E2 dZ * E2 W, ?_⟩
  push_cast
  linear_combination (2 * (ζ : AF) * E2 (μ : AF)) * R2 + (-4 * (ζ : AF) ^ 3 * E2 dZ) * hW'

/-- **Theorem 8.1, pointwise form.** Modulo 8,
`μ ≡ 2 ζ * E_2(μ) - d_3 * E_2(μ * μ - 4 a)`, with `d_3 = ζ ^ 3`, `G = (d_2 - E_2 ζ) / 2` and
`a = G * E_4(μ)`. -/
theorem mod_eight_display :
    Cong 8 (μ : AF)
      (2 * (ζ : AF) * frobPush 2 (μ : AF) - (ζ : AF) ^ 3 * frobPush 2 ((μ : AF) ^ 2 - 4 * a8)) := by
  have h1 := (cong_iff_dvd 8 _ _).1 mod_eight_identity
  have h2 := (cong_iff_dvd 8 _ _).1 mod_eight_identity_cong_display
  rw [cong_iff_dvd]
  have := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at this

/-- `Q(x) = ∑_{m² ≤ x} μ(m) ⌊x / m²⌋`. -/
def sqfQ (x : ℕ) : ℤ :=
  ∑ m ∈ (Ioc 0 x).filter (fun m => m ^ 2 ≤ x), (μ : AF) m * ((x / m ^ 2 : ℕ) : ℤ)

/-- `D_3(t) = ∑_{n ≤ t} d_3(n)`, `d_3 = ζ ^ 3`. -/
def D3 (t : ℕ) : ℤ := ∑ n ∈ Ioc 0 t, ((ζ : AF) ^ 3) n

theorem sum_zeta_Ioc (t : ℕ) : ∑ n ∈ Ioc 0 t, (ζ : AF) n = (t : ℤ) := by
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ)), Finset.sum_const, Nat.card_Ioc]
  · simp
  · intro n hn
    rw [natCoe_apply, zeta_apply_ne (mem_Ioc.1 hn).1.ne']
    simp

theorem two_mul_apply (F : AF) (n : ℕ) : ((2 : AF) * F) n = 2 * F n := by
  rw [show (2 : AF) = ((2 : ℕ) : AF) by norm_cast, natCast_mul_apply]
  norm_num

theorem four_mul_apply (F : AF) (n : ℕ) : ((4 : AF) * F) n = 4 * F n := by
  rw [show (4 : AF) = ((4 : ℕ) : AF) by norm_cast, natCast_mul_apply]
  norm_num

/-- **Theorem 8.1, summed form.** For every natural `x`,
`M(x) ≡ 2 Q(x) - ∑_{m² ≤ x} (μ * μ)(m) D_3(x / m²) + 4 ∑_{m² ≤ x} a(m) D_3(x / m²) (mod 8)`. -/
theorem mertens_mod_eight (x : ℕ) :
    (8 : ℤ) ∣ (∑ n ∈ Ioc 0 x, (μ : AF) n) -
      (2 * sqfQ x -
        ∑ m ∈ (Ioc 0 x).filter (fun m => m ^ 2 ≤ x), ((μ : AF) ^ 2) m * D3 (x / m ^ 2) +
        4 * ∑ m ∈ (Ioc 0 x).filter (fun m => m ^ 2 ≤ x), a8 m * D3 (x / m ^ 2)) := by
  have h := mod_eight_display
  have hsum : ∑ n ∈ Ioc 0 x,
      ((2 * (ζ : AF) * frobPush 2 (μ : AF) - (ζ : AF) ^ 3 * frobPush 2 ((μ : AF) ^ 2 - 4 * a8) :
        AF)) n =
      2 * sqfQ x -
        ∑ m ∈ (Ioc 0 x).filter (fun m => m ^ 2 ≤ x), ((μ : AF) ^ 2) m * D3 (x / m ^ 2) +
        4 * ∑ m ∈ (Ioc 0 x).filter (fun m => m ^ 2 ≤ x), a8 m * D3 (x / m ^ 2) := by
    simp only [sub_apply', mul_assoc, two_mul_apply, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    rw [sum_mul_frobPush two_ne_zero, sum_mul_frobPush two_ne_zero, sqfQ]
    simp only [sum_zeta_Ioc, D3, sub_apply', four_mul_apply, sub_mul, Finset.sum_sub_distrib,
      mul_assoc, ← Finset.mul_sum]
    ring
  rw [← hsum, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun n _ => h n

/-! ## `Q(x)` is the squarefree count -/

theorem dvd_of_sq_dvd_sq_mul_squarefree {a b d : ℕ} (ha : Squarefree a) (hb : b ≠ 0)
    (h : d ^ 2 ∣ b ^ 2 * a) : d ∣ b := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have hn0 : b ^ 2 * a ≠ 0 := mul_ne_zero (pow_ne_zero _ hb) ha0
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, zero_dvd_iff] at h
    exact hn0 h
  refine (Nat.factorization_le_iff_dvd hd0 hb).1 fun q => ?_
  have h1 := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd0) hn0).2 h q
  rw [Nat.factorization_pow, Nat.factorization_mul (pow_ne_zero _ hb) ha0,
    Nat.factorization_pow] at h1
  simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul] at h1
  have h2 := ha.natFactorization_le_one q
  omega

/-- `(ζ * E_2 μ)(n) = 1` if `n` is squarefree and `0` otherwise (`n ≥ 1`). -/
theorem zeta_mul_E2_moebius_apply {n : ℕ} (hn : n ≠ 0) :
    ((ζ : AF) * frobPush 2 (μ : AF)) n = if Squarefree n then 1 else 0 := by
  obtain ⟨a, b, ha0, hb0, rfl, ha⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hn)
  rw [coe_zeta_mul_apply]
  have hsub : (b.divisors).image (· ^ 2) ⊆ (b ^ 2 * a).divisors := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hc
    exact Nat.mem_divisors.2 ⟨dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (Nat.dvd_of_mem_divisors hd) 2) _, hn⟩
  rw [← Finset.sum_subset hsub, Finset.sum_image]
  · have : ∑ x ∈ b.divisors, frobPush 2 (μ : AF) (x ^ 2) = ∑ x ∈ b.divisors, (μ : AF) x := by
      refine Finset.sum_congr rfl fun d hd => frobPush_apply_pow two_ne_zero _ ?_
      exact Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    rw [this, ← coe_mul_zeta_apply, moebius_mul_coe_zeta]
    by_cases hb1 : b = 1
    · subst hb1
      simp [ha]
    · rw [one_apply_ne hb1, ite_eq_right]
      intro hsq
      apply hb1
      have := hsq b ⟨a, by ring⟩
      exact Nat.isUnit_iff.1 this
  · intro x _ y _ hxy
    exact Nat.pow_left_injective two_ne_zero hxy
  · intro c hc hci
    refine frobPush_apply_of_not _ ?_
    rintro ⟨d, rfl⟩
    apply hci
    refine mem_image.2 ⟨d, Nat.mem_divisors.2 ⟨?_, hb0.ne'⟩, rfl⟩
    exact dvd_of_sq_dvd_sq_mul_squarefree ha hb0.ne' (Nat.dvd_of_mem_divisors hc)

/-- `Q(x)`, defined as `∑_{m² ≤ x} μ(m) ⌊x / m²⌋`, is the number of squarefree `n` with
`1 ≤ n ≤ x` (the description of `Q` in Section 8 of the paper). -/
theorem sqfQ_eq_card (x : ℕ) : sqfQ x = ((Ioc 0 x).filter Squarefree).card := by
  have h := sum_mul_frobPush two_ne_zero (ζ : AF) (μ : AF) x
  simp only [sum_zeta_Ioc] at h
  rw [sqfQ, ← h, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [zeta_mul_E2_moebius_apply (mem_Ioc.1 hn).1.ne']
  split_ifs <;> simp

/-- **Theorem 8.1, summed form, with `Q(x)` the squarefree count.** For every natural `x`,
`M(x) ≡ 2 #{n ≤ x squarefree} - ∑_{m² ≤ x} (μ * μ)(m) D_3(x / m²) + 4 ∑_{m² ≤ x} a(m) D_3(x / m²)`
modulo `8`. -/
theorem mertens_mod_eight_card (x : ℕ) :
    (8 : ℤ) ∣ (∑ n ∈ Ioc 0 x, (μ : AF) n) -
      (2 * ((Ioc 0 x).filter Squarefree).card -
        ∑ m ∈ (Ioc 0 x).filter (fun m => m ^ 2 ≤ x), ((μ : AF) ^ 2) m * D3 (x / m ^ 2) +
        4 * ∑ m ∈ (Ioc 0 x).filter (fun m => m ^ 2 ≤ x), a8 m * D3 (x / m ^ 2)) := by
  rw [← sqfQ_eq_card]
  exact mertens_mod_eight x

/-! ## The correction `4 a` cannot be dropped -/

theorem zetaZ_pow_apply_one (z : ℕ) : ((ζ : AF) ^ z) 1 = 1 :=
  (isMultiplicative_zeta.natCast.pow : IsMultiplicative ((ζ : AF) ^ z)).map_one

theorem frobPush_apply_one {R : Type*} [CommRing R] {q : ℕ} (hq : q ≠ 0) (f : ArithmeticFunction R) :
    frobPush q f 1 = f 1 := by
  have := frobPush_apply_pow hq f one_ne_zero
  rwa [one_pow] at this

theorem G8_apply_one : G8 1 = 0 := by
  show ((ζ : AF) ^ 2 - frobPush 2 (ζ : AF)) 1 / 2 = 0
  rw [sub_apply', zetaZ_pow_apply_one, frobPush_apply_one two_ne_zero]
  simp

theorem frobPush_two_apply_two {R : Type*} [CommRing R] (f : ArithmeticFunction R) :
    frobPush 2 f 2 = 0 := by
  refine frobPush_apply_of_not f ?_
  rintro ⟨j, hj⟩
  have h1 : j ≤ 1 := by nlinarith
  interval_cases j <;> simp at hj

theorem G8_apply_two : G8 2 = 1 := by
  show ((ζ : AF) ^ 2 - frobPush 2 (ζ : AF)) 2 / 2 = 1
  rw [sub_apply', zeta_pow_apply_prime 2 Nat.prime_two, frobPush_two_apply_two]
  norm_num

theorem a8_apply_one : a8 1 = 0 := by
  rw [a8, mul_apply, show Nat.divisorsAntidiagonal 1 = {(1, 1)} by decide, sum_singleton,
    G8_apply_one, zero_mul]

theorem a8_apply_two : a8 2 = 1 := by
  rw [a8, mul_apply, show Nat.divisorsAntidiagonal 2 = {(1, 2), (2, 1)} by decide,
    sum_pair (by decide), G8_apply_one, G8_apply_two, frobPush_apply_one (by norm_num),
    moebius_apply_one]
  simp

theorem zeta_cube_mul_E2_a8_apply_four : ((ζ : AF) ^ 3 * frobPush 2 a8) 4 = 1 := by
  rw [mul_apply, show Nat.divisorsAntidiagonal 4 = {(1, 4), (2, 2), (4, 1)} by decide]
  rw [sum_insert (by decide), sum_pair (by decide)]
  simp only
  rw [frobPush_two_apply_two, frobPush_apply_one two_ne_zero, a8_apply_one,
    show (4 : ℕ) = 2 ^ 2 from rfl, frobPush_apply_pow two_ne_zero _ two_ne_zero, a8_apply_two,
    zetaZ_pow_apply_one]
  ring

/-- **The correction `4 a` cannot be dropped** (remark after Theorem 8.1):
`μ ≢ 2 ζ * E_2(μ) - d_3 * E_2(μ * μ) (mod 8)`; at `n = 4` the two sides differ by `4` modulo `8`,
because `(d_3 * E_2(a))(4) = a(2) = G(2) = 1`. -/
theorem mod_eight_correction_needed :
    ¬ Cong 8 (μ : AF)
      (2 * (ζ : AF) * frobPush 2 (μ : AF) - (ζ : AF) ^ 3 * frobPush 2 ((μ : AF) ^ 2)) := by
  intro h
  have h1 := mod_eight_display 4
  have h2 := h 4
  have e : (2 * (ζ : AF) * frobPush 2 (μ : AF) - (ζ : AF) ^ 3 * frobPush 2 ((μ : AF) ^ 2)) -
      (2 * (ζ : AF) * frobPush 2 (μ : AF) - (ζ : AF) ^ 3 * frobPush 2 ((μ : AF) ^ 2 - 4 * a8)) =
      -(4 * ((ζ : AF) ^ 3 * frobPush 2 a8)) := by
    have hΦ : ∀ f : AF, frobPush 2 f = frobHom two_ne_zero f := fun f => rfl
    rw [hΦ, hΦ, hΦ, hΦ]
    simp only [map_sub, map_mul, map_ofNat]
    ring
  have := dvd_sub h1 h2
  rw [sub_sub_sub_cancel_left, ← sub_apply', e, ArithmeticFunction.neg_apply, four_mul_apply,
    zeta_cube_mul_E2_a8_apply_four] at this
  norm_num at this

end ModEightDisplay

end FrobCong
