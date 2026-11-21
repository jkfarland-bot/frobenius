module

public import Mathlib

@[expose] public section

/-!
# Frobenius congruence for arithmetic functions (r4i, Q3, seat PR-O)

In the commutative ring `ArithmeticFunction R` (Dirichlet convolution), with `R` a commutative
ring of prime characteristic `p`, the `p`-th power map satisfies
`(f ^ p) n = sum over d | n with d ^ p = n of (f d) ^ p`.
Over `ZMod p` this reads `f ^ p = frobPush p f`, so `zeta ^ p = zeta_p` and `mu ^ p = mu_p`,
and `mu = zeta ^ (p - 1) * mu_p`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace FrobCong

section General

variable {R : Type*} [CommRing R]

/-- The point function with value `c` at `d` (and `0` everywhere if `d = 0`). -/
def pt (d : ℕ) (c : R) : ArithmeticFunction R :=
  ⟨fun m => if m = d ∧ d ≠ 0 then c else 0, by
    rw [if_neg]; rintro ⟨h1, h2⟩; exact h2 h1.symm⟩

theorem pt_apply (d : ℕ) (c : R) (m : ℕ) :
    pt d c m = if m = d ∧ d ≠ 0 then c else 0 := rfl

theorem pt_mul (a b : ℕ) (c e : R) : pt a c * pt b e = pt (a * b) (c * e) := by
  ext m
  rw [mul_apply]
  by_cases h : m = a * b ∧ a * b ≠ 0
  · obtain ⟨rfl, hab⟩ := h
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    rw [Finset.sum_eq_single (a, b)]
    · simp [pt_apply, ha, hb, hab]
    · intro x _ hne
      rw [pt_apply, pt_apply]
      split_ifs with h1 h2 <;> first | exact absurd (Prod.ext h1.1 h2.1) hne | simp
    · intro hx
      exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hab⟩) hx
  · rw [pt_apply, if_neg h]
    apply Finset.sum_eq_zero
    intro x hx
    rw [pt_apply, pt_apply]
    split_ifs with h1 h2 <;>
      first
      | exact absurd ⟨by rw [← h1.1, ← h2.1, (Nat.mem_divisorsAntidiagonal.mp hx).1],
          mul_ne_zero h1.2 h2.2⟩ h
      | simp

theorem pt_one : pt 1 (1 : R) = 1 := by
  ext m
  rw [pt_apply, one_apply]
  simp

theorem pt_pow (d : ℕ) (c : R) (k : ℕ) : pt d c ^ k = pt (d ^ k) (c ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, pow_zero, pt_one]
  | succ k ih => rw [pow_succ, ih, pt_mul, pow_succ, pow_succ]

/-- Evaluation at `m` as an additive monoid hom. -/
def evalHom (m : ℕ) : ArithmeticFunction R →+ R where
  toFun f := f m
  map_zero' := by simp
  map_add' f g := by simp

theorem sum_apply' {ι : Type*} (s : Finset ι) (g : ι → ArithmeticFunction R) (m : ℕ) :
    (∑ i ∈ s, g i) m = ∑ i ∈ s, g i m :=
  map_sum (evalHom m) g s

/-- `(f ^ k) m` for `m | n` depends only on the values of `f` on the divisors of `n`. -/
theorem pow_apply_congr {f g : ArithmeticFunction R} {n : ℕ}
    (h : ∀ m ∈ n.divisors, f m = g m) (k : ℕ) :
    ∀ m ∈ n.divisors, (f ^ k) m = (g ^ k) m := by
  induction k with
  | zero => intro m _; simp
  | succ k ih =>
    intro m hm
    rw [pow_succ, pow_succ, mul_apply, mul_apply]
    apply Finset.sum_congr rfl
    intro x hx
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have hn := Nat.ne_zero_of_mem_divisors hm
    have hmn := Nat.dvd_of_mem_divisors hm
    rw [ih x.1 ?_, h x.2 ?_]
    · exact Nat.mem_divisors.mpr ⟨(Dvd.intro_left _ hx'.1).trans hmn, hn⟩
    · exact Nat.mem_divisors.mpr ⟨(Dvd.intro _ hx'.1).trans hmn, hn⟩

variable (p : ℕ) [hp : Fact p.Prime] [CharP R p]

omit hp in
theorem charP_arith : CharP (ArithmeticFunction R) p :=
  charP_of_injective_algebraMap (R := R) (A := ArithmeticFunction R) (fun x y hxy => by
    have := congrArg (fun f : ArithmeticFunction R => f 1) hxy
    simpa using this) p

/-- **Frobenius congruence**, general form: in characteristic `p`,
`(f ^ p) n = sum_{d | n, d ^ p = n} (f d) ^ p`. -/
theorem frob_apply (f : ArithmeticFunction R) (n : ℕ) :
    (f ^ p) n = ∑ d ∈ n.divisors, if d ^ p = n then f d ^ p else 0 := by
  have := charP_arith (R := R) p
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  set g : ArithmeticFunction R := ∑ d ∈ n.divisors, pt d (f d) with hg
  have hfg : ∀ m ∈ n.divisors, f m = g m := by
    intro m hm
    rw [hg, sum_apply']
    simp only [pt_apply]
    rw [Finset.sum_eq_single m]
    · simp [(Nat.pos_of_mem_divisors hm).ne']
    · intro b _ hb
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact hb h1.symm
    · intro hm'
      exact absurd hm hm'
  rw [pow_apply_congr hfg p n (Nat.mem_divisors_self n hn), hg, sum_pow_char p, sum_apply']
  apply Finset.sum_congr rfl
  intro d hd
  rw [pt_pow, pt_apply]
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hdp : d ^ p ≠ 0 := pow_ne_zero _ hd0
  by_cases h : d ^ p = n
  · rw [if_pos ⟨h.symm, hdp⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1.symm), if_neg h]

end General

section ZModP

variable {R : Type*} [CommRing R]

/-- Frobenius pushforward: `frobPush p f (j ^ p) = f j`, and `0` off the `p`-th powers. -/
def frobPush (p : ℕ) (f : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => ∑ d ∈ n.divisors, if d ^ p = n then f d else 0, by simp⟩

theorem frobPush_apply (p : ℕ) (f : ArithmeticFunction R) (n : ℕ) :
    frobPush p f n = ∑ d ∈ n.divisors, if d ^ p = n then f d else 0 := rfl

theorem frobPush_apply_pow {p : ℕ} (hp0 : p ≠ 0) (f : ArithmeticFunction R) {j : ℕ}
    (hj : j ≠ 0) : frobPush p f (j ^ p) = f j := by
  rw [frobPush_apply, Finset.sum_eq_single j]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Nat.pow_left_injective hp0 h)
  · intro hj'
    exact absurd (Nat.mem_divisors.mpr ⟨dvd_pow_self j hp0, pow_ne_zero _ hj⟩) hj'

theorem frobPush_apply_of_not {p : ℕ} (f : ArithmeticFunction R) {n : ℕ}
    (h : ¬ ∃ j, j ^ p = n) : frobPush p f n = 0 := by
  rw [frobPush_apply]
  apply Finset.sum_eq_zero
  intro d _
  rw [if_neg]
  exact fun hd => h ⟨d, hd⟩

variable (p : ℕ) [hp : Fact p.Prime]

/-- Over `ZMod p`, the Frobenius congruence: `f ^ p = frobPush p f`. -/
theorem pow_eq_frobPush (f : ArithmeticFunction (ZMod p)) : f ^ p = frobPush p f := by
  ext n
  rw [frob_apply p f n, frobPush_apply]
  simp only [ZMod.pow_card]

/-- The indicator of the nonzero perfect `p`-th powers, as `frobPush p zeta`. -/
abbrev zetaP : ArithmeticFunction (ZMod p) := frobPush p (ζ : ArithmeticFunction (ZMod p))

/-- The `p`-th power Mobius function: `muP (j ^ p) = mu j`, else `0`. -/
abbrev muP : ArithmeticFunction (ZMod p) := frobPush p (μ : ArithmeticFunction (ZMod p))

theorem zetaP_apply_pow {j : ℕ} (hj : j ≠ 0) : zetaP p (j ^ p) = 1 := by
  rw [zetaP, frobPush_apply_pow hp.out.ne_zero _ hj, natCoe_apply, zeta_apply_ne hj, Nat.cast_one]

theorem zetaP_apply_of_not {n : ℕ} (h : ¬ ∃ j, j ^ p = n) : zetaP p n = 0 :=
  frobPush_apply_of_not _ h

theorem muP_apply_pow (j : ℕ) (hj : j ≠ 0) : muP p (j ^ p) = (μ j : ZMod p) := by
  rw [muP, frobPush_apply_pow hp.out.ne_zero _ hj, intCoe_apply]

theorem muP_apply_of_not {n : ℕ} (h : ¬ ∃ j, j ^ p = n) : muP p n = 0 :=
  frobPush_apply_of_not _ h

/-- **Main theorem 1**: `zeta ^ p = zeta_p` in `ArithmeticFunction (ZMod p)`. -/
theorem zeta_pow_eq : (ζ : ArithmeticFunction (ZMod p)) ^ p = zetaP p :=
  pow_eq_frobPush p _

/-- Pointwise form of main theorem 1. -/
theorem zeta_pow_apply (n : ℕ) :
    ((ζ : ArithmeticFunction (ZMod p)) ^ p) n = if n ≠ 0 ∧ ∃ j, j ^ p = n then 1 else 0 := by
  classical
  rw [zeta_pow_eq]
  split_ifs with h
  · obtain ⟨hn, j, rfl⟩ := h
    have hj : j ≠ 0 := by rintro rfl; exact hn (zero_pow hp.out.ne_zero)
    exact zetaP_apply_pow p hj
  · by_cases hn : n = 0
    · subst hn; rw [zetaP, frobPush_apply]; simp
    · exact zetaP_apply_of_not p (fun hex => h ⟨hn, hex⟩)

theorem moebius_pow_eq : (μ : ArithmeticFunction (ZMod p)) ^ p = muP p :=
  pow_eq_frobPush p _

/-- **Main theorem 2**: `mu = zeta ^ (p - 1) * mu_p` in `ArithmeticFunction (ZMod p)`.
(Here `zeta ^ (p - 1)` is the Dirichlet power, the `(p-1)`-fold divisor function.) -/
theorem moebius_eq_zeta_pow_mul_muP :
    (μ : ArithmeticFunction (ZMod p)) = (ζ : ArithmeticFunction (ZMod p)) ^ (p - 1) * muP p := by
  rw [← moebius_pow_eq]
  have h1 : (ζ : ArithmeticFunction (ZMod p)) * μ = 1 := coe_zeta_mul_coe_moebius
  calc (μ : ArithmeticFunction (ZMod p))
      = ((ζ : ArithmeticFunction (ZMod p)) * μ) ^ (p - 1) * μ := by rw [h1, one_pow, one_mul]
    _ = (ζ : ArithmeticFunction (ZMod p)) ^ (p - 1) * (μ : ArithmeticFunction (ZMod p)) ^ p := by
        rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel hp.out.one_le]

/-- Equivalent form: `zeta ^ (p - 1) * mu_p * zeta = 1`. -/
theorem zeta_pow_mul_muP_mul_zeta :
    (ζ : ArithmeticFunction (ZMod p)) ^ (p - 1) * muP p * ζ = 1 := by
  rw [← moebius_eq_zeta_pow_mul_muP, coe_moebius_mul_coe_zeta]

end ZModP

section Summed

variable (p : ℕ) [hp : Fact p.Prime]

/-- Reindexing a sum against `mu_p` over the `p`-th powers. -/
theorem sum_muP_mul (F : ℕ → ZMod p) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, muP p n * F n =
      ∑ j ∈ (Ioc 0 N).filter (fun j => j ^ p ≤ N), (μ j : ZMod p) * F (j ^ p) := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  symm
  calc ∑ j ∈ (Ioc 0 N).filter (fun j => j ^ p ≤ N), (μ j : ZMod p) * F (j ^ p)
      = ∑ j ∈ (Ioc 0 N).filter (fun j => j ^ p ≤ N), muP p (j ^ p) * F (j ^ p) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj0 : j ≠ 0 := (mem_Ioc.mp (mem_filter.mp hj).1).1.ne'
        rw [muP_apply_pow p j hj0]
    _ = ∑ n ∈ ((Ioc 0 N).filter (fun j => j ^ p ≤ N)).image (· ^ p), muP p n * F n :=
        (Finset.sum_image (f := fun n => muP p n * F n) (fun a _ b _ h => Nat.pow_left_injective hp0 h)).symm
    _ = ∑ n ∈ Ioc 0 N, muP p n * F n := by
        apply Finset.sum_subset
        · intro n hn
          obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
          have hj' := mem_filter.mp hj
          exact mem_Ioc.mpr ⟨pow_pos (mem_Ioc.mp hj'.1).1 _, hj'.2⟩
        · intro n hn hni
          rw [muP_apply_of_not p, zero_mul]
          rintro ⟨j, rfl⟩
          apply hni
          have hn' := mem_Ioc.mp hn
          have hj0 : j ≠ 0 := by
            rintro rfl
            rw [zero_pow hp0] at hn'
            exact absurd hn'.1 (lt_irrefl 0)
          refine mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hj0, ?_⟩, hn'.2⟩, rfl⟩
          exact (Nat.le_self_pow hp0 j).trans hn'.2

/-- **Main theorem 3** (summed Mobius congruence): for every `N`,
`M(N) = sum_{j >= 1, j ^ p <= N} mu(j) * D_{p-1}(N / j ^ p)` modulo `p`, where
`D_{p-1}(x) = sum_{m <= x} d_{p-1}(m)` and `d_{p-1} = zeta ^ (p - 1)` (Dirichlet power). -/
theorem mertens_mod (N : ℕ) :
    ((∑ n ∈ Ioc 0 N, μ n : ℤ) : ZMod p) =
      ∑ j ∈ (Ioc 0 N).filter (fun j => j ^ p ≤ N),
        (μ j : ZMod p) * ∑ m ∈ Ioc 0 (N / j ^ p), ((ζ : ArithmeticFunction (ZMod p)) ^ (p - 1)) m := by
  have e : (μ : ArithmeticFunction (ZMod p)) = muP p * (ζ : ArithmeticFunction (ZMod p)) ^ (p - 1) := by
    rw [mul_comm]; exact moebius_eq_zeta_pow_mul_muP p
  rw [Int.cast_sum]
  calc ∑ n ∈ Ioc 0 N, ((μ n : ℤ) : ZMod p)
      = ∑ n ∈ Ioc 0 N, (muP p * (ζ : ArithmeticFunction (ZMod p)) ^ (p - 1)) n := by
        apply Finset.sum_congr rfl
        intro n _
        rw [← e, intCoe_apply]
    _ = ∑ n ∈ Ioc 0 N, muP p n *
          ∑ m ∈ Ioc 0 (N / n), ((ζ : ArithmeticFunction (ZMod p)) ^ (p - 1)) m :=
        sum_Ioc_mul_eq_sum_sum _ _ N
    _ = _ := sum_muP_mul p
          (fun n => ∑ m ∈ Ioc 0 (N / n), ((ζ : ArithmeticFunction (ZMod p)) ^ (p - 1)) m) N

end Summed

end FrobCong

/-! # r4j additions (seat PR-O2): congruences over `ℤ`, the lifting lemma, Dwork and Newton lifts -/

namespace FrobCong

section Push

variable {R : Type*} [CommRing R] {p : ℕ}

theorem frobPush_apply_zero (f : ArithmeticFunction R) : frobPush p f 0 = 0 := by
  rw [frobPush_apply]; simp

/-- `E_p` is multiplicative for Dirichlet convolution (because `n ↦ n ^ p` is injective). -/
theorem frobPush_mul (hp0 : p ≠ 0) (f g : ArithmeticFunction R) :
    frobPush p (f * g) = frobPush p f * frobPush p g := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [frobPush_apply_zero, ArithmeticFunction.map_zero]
  -- a nonzero term of the right side sits at a pair of `p`-th powers
  have key : ∀ y ∈ n.divisorsAntidiagonal, frobPush p f y.1 * frobPush p g y.2 ≠ 0 →
      ∃ a b, a ^ p = y.1 ∧ b ^ p = y.2 := by
    intro y _ hne
    have ha : ∃ x, x ^ p = y.1 := by
      by_contra h; exact hne (by rw [frobPush_apply_of_not f h, zero_mul])
    have hb : ∃ x, x ^ p = y.2 := by
      by_contra h; exact hne (by rw [frobPush_apply_of_not g h, mul_zero])
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    exact ⟨a, b, ha, hb⟩
  rw [mul_apply]
  by_cases hex : ∃ m, m ^ p = n
  · obtain ⟨m, rfl⟩ := hex
    have hm : m ≠ 0 := by rintro rfl; exact hn (zero_pow hp0)
    rw [frobPush_apply_pow hp0 _ hm, mul_apply]
    calc ∑ x ∈ m.divisorsAntidiagonal, f x.1 * g x.2
        = ∑ x ∈ m.divisorsAntidiagonal, frobPush p f (x.1 ^ p) * frobPush p g (x.2 ^ p) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hx' := Nat.mem_divisorsAntidiagonal.mp hx
          rw [frobPush_apply_pow hp0 _ (left_ne_zero_of_mul (hx'.1 ▸ hm)),
            frobPush_apply_pow hp0 _ (right_ne_zero_of_mul (hx'.1 ▸ hm))]
      _ = ∑ y ∈ m.divisorsAntidiagonal.image (fun x : ℕ × ℕ => (x.1 ^ p, x.2 ^ p)),
            frobPush p f y.1 * frobPush p g y.2 := by
          rw [Finset.sum_image]
          intro x _ y _ h
          have h' := Prod.ext_iff.mp h
          exact Prod.ext (Nat.pow_left_injective hp0 h'.1) (Nat.pow_left_injective hp0 h'.2)
      _ = _ := by
          apply Finset.sum_subset
          · intro y hy
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
            have hx' := Nat.mem_divisorsAntidiagonal.mp hx
            exact Nat.mem_divisorsAntidiagonal.mpr ⟨by rw [← mul_pow, hx'.1], pow_ne_zero _ hm⟩
          · intro y hy hni
            by_contra hne
            obtain ⟨a, b, ha, hb⟩ := key y hy hne
            have hy1 := (Nat.mem_divisorsAntidiagonal.mp hy).1
            apply hni
            refine Finset.mem_image.mpr ⟨(a, b), Nat.mem_divisorsAntidiagonal.mpr
              ⟨Nat.pow_left_injective hp0 (by simp only; rw [mul_pow, ha, hb, hy1]), hm⟩, ?_⟩
            exact Prod.ext ha hb
  · rw [frobPush_apply_of_not _ hex]
    symm
    apply Finset.sum_eq_zero
    intro y hy
    by_contra hne
    obtain ⟨a, b, ha, hb⟩ := key y hy hne
    exact hex ⟨a * b, by rw [mul_pow, ha, hb, (Nat.mem_divisorsAntidiagonal.mp hy).1]⟩

theorem frobPush_one (hp0 : p ≠ 0) : frobPush p (1 : ArithmeticFunction R) = 1 := by
  ext n
  by_cases hex : ∃ m, m ^ p = n
  · obtain ⟨m, rfl⟩ := hex
    rcases eq_or_ne m 0 with rfl | hm
    · rw [zero_pow hp0, frobPush_apply_zero]; rfl
    rw [frobPush_apply_pow hp0 _ hm, one_apply, one_apply]
    by_cases h1 : m = 1
    · subst h1; simp
    · rw [if_neg h1, if_neg]
      intro h
      rcases (pow_eq_one_iff).mp h with h' | h'
      · exact h1 h'
      · exact hp0 h'
  · rw [frobPush_apply_of_not _ hex, one_apply, if_neg]
    rintro rfl; exact hex ⟨1, one_pow p⟩

theorem frobPush_pow (hp0 : p ≠ 0) (f : ArithmeticFunction R) (k : ℕ) :
    frobPush p (f ^ k) = frobPush p f ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, frobPush_one hp0]
  | succ k ih => rw [pow_succ, pow_succ, frobPush_mul hp0, ih]

end Push

end FrobCong

namespace FrobCong

section IntCong

/-- Coefficientwise congruence modulo `m` of integer arithmetic functions:
`Cong m A B` means `(m : ℤ) ∣ A n - B n` for every `n`. -/
def Cong (m : ℕ) (A B : ArithmeticFunction ℤ) : Prop := ∀ n, (m : ℤ) ∣ A n - B n

theorem sub_apply' (A B : ArithmeticFunction ℤ) (n : ℕ) : (A - B) n = A n - B n := by
  rfl

theorem natCast_mul_apply (m : ℕ) (D : ArithmeticFunction ℤ) (n : ℕ) :
    ((m : ArithmeticFunction ℤ) * D) n = m * D n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [mul_apply, Finset.sum_eq_single (1, n)]
  · show (if (1 : ℕ) = 1 then (m : ℤ) else 0) * D n = _
    rw [if_pos rfl]
  · intro x hx hne
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have h1 : x.1 ≠ 1 := by
      intro h
      apply hne
      refine Prod.ext h ?_
      show x.2 = n
      rw [← hx'.1, h, one_mul]
    show (if x.1 = 1 then (m : ℤ) else 0) * D x.2 = 0
    rw [if_neg h1, zero_mul]
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul n, hn⟩) h

/-- Congruence as divisibility in the ring `ArithmeticFunction ℤ`. -/
theorem cong_iff_dvd (m : ℕ) (A B : ArithmeticFunction ℤ) :
    Cong m A B ↔ (m : ArithmeticFunction ℤ) ∣ A - B := by
  constructor
  · intro h
    let D : ArithmeticFunction ℤ := ⟨fun n => (A n - B n) / m, by simp⟩
    refine ⟨D, ?_⟩
    ext n
    rw [sub_apply', natCast_mul_apply]
    exact (Int.mul_ediv_cancel' (h n)).symm
  · rintro ⟨D, hD⟩ n
    have := congrArg (fun F : ArithmeticFunction ℤ => F n) hD
    simp only [sub_apply', natCast_mul_apply] at this
    rw [this]
    exact dvd_mul_right _ _

/-- Reduction of coefficients modulo `m`, as a ring hom for Dirichlet convolution. -/
def toZMod (m : ℕ) : ArithmeticFunction ℤ →+* ArithmeticFunction (ZMod m) where
  toFun f := (f : ArithmeticFunction (ZMod m))
  map_one' := intCoe_one
  map_mul' _ _ := intCoe_mul
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

theorem toZMod_apply (m : ℕ) (f : ArithmeticFunction ℤ) (n : ℕ) :
    toZMod m f n = (f n : ZMod m) := rfl

/-- Congruence as equality after reducing modulo `m`. -/
theorem cong_iff_map (m : ℕ) (A B : ArithmeticFunction ℤ) :
    Cong m A B ↔ toZMod m A = toZMod m B := by
  constructor
  · intro h
    ext n
    rw [toZMod_apply, toZMod_apply]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (dvd_sub_comm.mp (h n))
  · intro h n
    have := congrArg (fun F => F n) h
    simp only [toZMod_apply] at this
    exact dvd_sub_comm.mp ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp this)

theorem toZMod_frobPush (m p : ℕ) (f : ArithmeticFunction ℤ) :
    toZMod m (frobPush p f) = frobPush p (toZMod m f) := by
  ext n
  rw [toZMod_apply, frobPush_apply, frobPush_apply, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp [toZMod_apply]

/-- **Lifting lemma**, ring form: `p ^ j ∣ a - b` with `j ≥ 1` gives `p ^ (j + 1) ∣ a ^ p - b ^ p`. -/
theorem lift_dvd {S : Type*} [CommRing S] {p j : ℕ} {a b : S} (hj : 1 ≤ j)
    (h : (p : S) ^ j ∣ a - b) : (p : S) ^ (j + 1) ∣ a ^ p - b ^ p := by
  rw [← geom_sum₂_mul, pow_succ']
  refine mul_dvd_mul ?_ h
  have h1 : (p : S) ∣ a - b := (dvd_pow_self (p : S) (by omega)).trans h
  let f : S →+* S ⧸ Ideal.span {(p : S)} := Ideal.Quotient.mk (Ideal.span {(p : S)})
  have hf : ∀ r : S, (p : S) ∣ r ↔ f r = 0 := fun r ↦ by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [hf, map_sub, sub_eq_zero] at h1
  rw [hf, RingHom.map_geom_sum₂, h1, geom_sum₂_self, mul_eq_zero_of_left]
  rw [← map_natCast f, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- **Target 2, the lifting lemma**: `A ≡ B (mod p ^ j)` coefficientwise, `j ≥ 1`, gives
`A ^ p ≡ B ^ p (mod p ^ (j + 1))` (Dirichlet powers). -/
theorem lift_cong {p j : ℕ} (hj : 1 ≤ j) {A B : ArithmeticFunction ℤ}
    (h : Cong (p ^ j) A B) : Cong (p ^ (j + 1)) (A ^ p) (B ^ p) := by
  rw [cong_iff_dvd, Nat.cast_pow] at h ⊢
  exact lift_dvd hj h

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Target 1 (T1(iv))**: over `ℤ`, `f ^ p ≡ E_p f (mod p)` coefficientwise, `E_p = frobPush p`. -/
theorem cong_pow_frobPush (f : ArithmeticFunction ℤ) : Cong p (f ^ p) (frobPush p f) := by
  rw [cong_iff_map, map_pow, toZMod_frobPush, pow_eq_frobPush]

/-- Target 1 for `zeta`: `zeta ^ p ≡ E_p zeta (mod p)` over `ℤ`. -/
theorem zeta_pow_cong : Cong p ((ζ : ArithmeticFunction ℤ) ^ p) (frobPush p (ζ : ArithmeticFunction ℤ)) :=
  cong_pow_frobPush p _

/-- **Target 3 (T2a, Dwork lift)**: `f ^ (p ^ k) ≡ E_p (f ^ (p ^ (k - 1))) (mod p ^ k)`, `k ≥ 1`. -/
theorem dwork_cong (f : ArithmeticFunction ℤ) {k : ℕ} (hk : 1 ≤ k) :
    Cong (p ^ k) (f ^ p ^ k) (frobPush p (f ^ p ^ (k - 1))) := by
  induction k, hk using Nat.le_induction with
  | base => simpa using cong_pow_frobPush p f
  | succ k hk ih =>
    have hp0 := hp.out.ne_zero
    have e1 : f ^ p ^ (k + 1) = (f ^ p ^ k) ^ p := by rw [pow_succ, pow_mul]
    have e2 : frobPush p (f ^ p ^ (k + 1 - 1)) = (frobPush p (f ^ p ^ (k - 1))) ^ p := by
      rw [← frobPush_pow hp0, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hk, Nat.add_sub_cancel]
    rw [e1, e2]
    exact lift_cong hk ih

/-- T2a for `zeta`: `zeta ^ (p ^ k) ≡ E_p (zeta ^ (p ^ (k - 1))) (mod p ^ k)`. -/
theorem zeta_dwork_cong {k : ℕ} (hk : 1 ≤ k) :
    Cong (p ^ k) ((ζ : ArithmeticFunction ℤ) ^ p ^ k)
      (frobPush p ((ζ : ArithmeticFunction ℤ) ^ p ^ (k - 1))) :=
  dwork_cong p _ hk

/-- T2a consequence: `mu ≡ d_{p^k - 1} * E_p (mu ^ (p ^ (k - 1))) (mod p ^ k)`. -/
theorem moebius_dwork_cong {k : ℕ} (hk : 1 ≤ k) :
    Cong (p ^ k) (μ : ArithmeticFunction ℤ)
      ((ζ : ArithmeticFunction ℤ) ^ (p ^ k - 1) * frobPush p ((μ : ArithmeticFunction ℤ) ^ p ^ (k - 1))) := by
  have hN : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.out.pos
  have hm : (μ : ArithmeticFunction ℤ) = (ζ : ArithmeticFunction ℤ) ^ (p ^ k - 1) * μ ^ p ^ k := by
    have h1 : (ζ : ArithmeticFunction ℤ) * μ = 1 := coe_zeta_mul_moebius
    calc (μ : ArithmeticFunction ℤ)
        = ((ζ : ArithmeticFunction ℤ) * μ) ^ (p ^ k - 1) * μ := by rw [h1, one_pow, one_mul]
      _ = _ := by rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel hN]
  have h := (cong_iff_dvd _ _ _).mp (dwork_cong p (μ : ArithmeticFunction ℤ) hk)
  rw [cong_iff_dvd]
  nth_rewrite 1 [hm]
  rw [← mul_sub]
  exact Dvd.dvd.mul_left h _

end IntCong

end FrobCong

namespace FrobCong

section Newton

/-- The ring identity behind the Newton lift: with `z * m = 1` and `e = 1 - z ^ (q + 1) * ν`,
`m - z ^ q * ν * sum_{i < k} e ^ i = z ^ q * m ^ (q + 1) * e ^ k`. -/
theorem newton_identity {S : Type*} [CommRing S] (z m ν : S) (q k : ℕ) (hzm : z * m = 1) :
    m - z ^ q * ν * ∑ i ∈ Finset.range k, (1 - z ^ (q + 1) * ν) ^ i =
      z ^ q * m ^ (q + 1) * (1 - z ^ (q + 1) * ν) ^ k := by
  have hg := mul_neg_geom_sum (1 - z ^ (q + 1) * ν) k
  have h1 : (z * m) ^ (q + 1) = 1 := by rw [hzm, one_pow]
  have h0 : (z * m) ^ q = 1 := by rw [hzm, one_pow]
  linear_combination (-(z ^ q * m ^ (q + 1))) * hg +
    z ^ q * ν * (∑ i ∈ Finset.range k, (1 - z ^ (q + 1) * ν) ^ i) * h1 - m * h0

variable (p : ℕ) [hp : Fact p.Prime]

/-- The Newton error term `e = 1 - zeta ^ p * mu_p` over `ℤ` (`mu_p = E_p mu`). -/
def nerr : ArithmeticFunction ℤ :=
  1 - (ζ : ArithmeticFunction ℤ) ^ p * frobPush p (μ : ArithmeticFunction ℤ)

/-- `e ≡ 0 (mod p)`, from Target 1 and `E_p zeta * E_p mu = 1`. -/
theorem nerr_cong : Cong p (nerr p) 0 := by
  have hp0 := hp.out.ne_zero
  have hzm : (ζ : ArithmeticFunction ℤ) * μ = 1 := coe_zeta_mul_moebius
  have hE : frobPush p (ζ : ArithmeticFunction ℤ) * frobPush p (μ : ArithmeticFunction ℤ) = 1 := by
    rw [← frobPush_mul hp0, hzm, frobPush_one hp0]
  obtain ⟨D, hD⟩ := (cong_iff_dvd p _ _).mp (zeta_pow_cong p)
  rw [cong_iff_dvd, sub_zero]
  exact ⟨-(D * frobPush p (μ : ArithmeticFunction ℤ)), by
    show 1 - (ζ : ArithmeticFunction ℤ) ^ p * frobPush p (μ : ArithmeticFunction ℤ) = _
    linear_combination (-(frobPush p (μ : ArithmeticFunction ℤ))) * hD - hE⟩

/-- **Target 4 (T2b, Newton lift), geometric form**: for every `k`,
`mu ≡ zeta ^ (p - 1) * mu_p * sum_{i < k} e ^ i (mod p ^ k)`, `e = 1 - zeta ^ p * mu_p`. -/
theorem newton_cong (k : ℕ) :
    Cong (p ^ k) (μ : ArithmeticFunction ℤ)
      ((ζ : ArithmeticFunction ℤ) ^ (p - 1) * frobPush p (μ : ArithmeticFunction ℤ) *
        ∑ i ∈ Finset.range k, nerr p ^ i) := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_le).symm⟩
  have hz1 : (ζ : ArithmeticFunction ℤ) ^ (p - 1) = (ζ : ArithmeticFunction ℤ) ^ q := by
    rw [hq, Nat.add_sub_cancel]
  have hn : nerr p = 1 - (ζ : ArithmeticFunction ℤ) ^ (q + 1) * frobPush p (μ : ArithmeticFunction ℤ) := by
    show 1 - (ζ : ArithmeticFunction ℤ) ^ p * _ = _
    rw [hq]
  have he := (cong_iff_dvd _ _ _).mp (nerr_cong p)
  rw [sub_zero] at he
  rw [cong_iff_dvd, Nat.cast_pow, hz1, hn,
    newton_identity _ _ _ q k (coe_zeta_mul_moebius : (ζ : ArithmeticFunction ℤ) * μ = 1)]
  rw [hn] at he
  exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd he k) _

/-- T2b at `k = 2`: `mu ≡ zeta ^ (p - 1) * mu_p * (1 + e) (mod p ^ 2)`. -/
theorem newton_cong_two :
    Cong (p ^ 2) (μ : ArithmeticFunction ℤ)
      ((ζ : ArithmeticFunction ℤ) ^ (p - 1) * frobPush p (μ : ArithmeticFunction ℤ) * (1 + nerr p)) := by
  have h := newton_cong p 2
  rwa [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one] at h

end Newton

end FrobCong

open FrobCong in
#print axioms frobPush_mul
open FrobCong in
#print axioms cong_iff_dvd
open FrobCong in
#print axioms cong_iff_map
open FrobCong in
#print axioms cong_pow_frobPush
open FrobCong in
#print axioms zeta_pow_cong
open FrobCong in
#print axioms lift_cong
open FrobCong in
#print axioms dwork_cong
open FrobCong in
#print axioms zeta_dwork_cong
open FrobCong in
#print axioms moebius_dwork_cong
open FrobCong in
#print axioms newton_cong
open FrobCong in
#print axioms newton_cong_two

namespace FrobCong

section NewtonBinomial

/-- `sum_{i < k} (1 - w) ^ i = sum_{j < k} (-1) ^ j * C(k, j + 1) * w ^ j` in any commutative ring. -/
theorem geom_binom {S : Type*} [CommRing S] (w : S) (k : ℕ) :
    ∑ i ∈ Finset.range k, (1 - w) ^ i =
      ∑ j ∈ Finset.range k, (-1 : S) ^ j * (k.choose (j + 1) : S) * w ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hb : (1 - w) ^ k = ∑ j ∈ Finset.range (k + 1), (-1 : S) ^ j * (k.choose j : S) * w ^ j := by
      rw [sub_eq_add_neg, add_comm, add_pow]
      apply Finset.sum_congr rfl
      intro j _
      rw [one_pow, mul_one, neg_pow]
      ring
    have hc : ∀ j, (((k + 1).choose (j + 1) : ℕ) : S) = (k.choose j : S) + (k.choose (j + 1) : S) :=
      fun j => by rw [Nat.choose_succ_succ', Nat.cast_add]
    have hz : ∑ j ∈ Finset.range (k + 1), (-1 : S) ^ j * (k.choose (j + 1) : S) * w ^ j =
        ∑ j ∈ Finset.range k, (-1 : S) ^ j * (k.choose (j + 1) : S) * w ^ j := by
      rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    rw [hb]
    simp only [hc, mul_add, add_mul, Finset.sum_add_distrib, hz]
    ring

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Target 4 (T2b, Newton lift), binomial form, as in the paper**: for every `k`,
`mu ≡ sum_{j < k} (-1) ^ j C(k, j + 1) d_{(j+1)p - 1} * E_p (mu ^ (j + 1)) (mod p ^ k)`,
where `d_z = zeta ^ z` (Dirichlet power) and `E_p = frobPush p`. -/
theorem newton_cong_binom (k : ℕ) :
    Cong (p ^ k) (μ : ArithmeticFunction ℤ)
      (∑ j ∈ Finset.range k, (-1 : ArithmeticFunction ℤ) ^ j * (k.choose (j + 1) : ArithmeticFunction ℤ) *
        ((ζ : ArithmeticFunction ℤ) ^ ((j + 1) * p - 1) * frobPush p ((μ : ArithmeticFunction ℤ) ^ (j + 1)))) := by
  have hp0 := hp.out.ne_zero
  have h := newton_cong p k
  have hn : nerr p = 1 - (ζ : ArithmeticFunction ℤ) ^ p * frobPush p (μ : ArithmeticFunction ℤ) := rfl
  rw [hn, geom_binom, Finset.mul_sum] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_le).symm⟩
  have hexp : (j + 1) * (q + 1) - 1 = q + (q + 1) * j := by
    have : (j + 1) * (q + 1) = q + (q + 1) * j + 1 := by ring
    omega
  rw [hexp, frobPush_pow hp0, Nat.add_sub_cancel, pow_add, pow_mul]
  ring

end NewtonBinomial

end FrobCong

open FrobCong in
#print axioms geom_binom
open FrobCong in
#print axioms newton_cong_binom

/-! # r4k additions (seat PR-O3): summed Newton lift, the moment lemma, the p = 2 level bound -/

namespace FrobCong

section SummedNewton

variable {R : Type*} [CommRing R]

/-- Reindexing a sum against `E_p g` over the `p`-th powers (general ring, `p ≠ 0`). -/
theorem sum_frobPush_mul {p : ℕ} (hp0 : p ≠ 0) (g : ArithmeticFunction R) (F : ℕ → R) (x : ℕ) :
    ∑ n ∈ Ioc 0 x, frobPush p g n * F n =
      ∑ j ∈ (Ioc 0 x).filter (fun j => j ^ p ≤ x), g j * F (j ^ p) := by
  symm
  calc ∑ j ∈ (Ioc 0 x).filter (fun j => j ^ p ≤ x), g j * F (j ^ p)
      = ∑ j ∈ (Ioc 0 x).filter (fun j => j ^ p ≤ x), frobPush p g (j ^ p) * F (j ^ p) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj0 : j ≠ 0 := (mem_Ioc.mp (mem_filter.mp hj).1).1.ne'
        rw [frobPush_apply_pow hp0 g hj0]
    _ = ∑ n ∈ ((Ioc 0 x).filter (fun j => j ^ p ≤ x)).image (· ^ p), frobPush p g n * F n :=
        (Finset.sum_image (f := fun n => frobPush p g n * F n)
          (fun a _ b _ h => Nat.pow_left_injective hp0 h)).symm
    _ = ∑ n ∈ Ioc 0 x, frobPush p g n * F n := by
        apply Finset.sum_subset
        · intro n hn
          obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
          have hj' := mem_filter.mp hj
          exact mem_Ioc.mpr ⟨pow_pos (mem_Ioc.mp hj'.1).1 _, hj'.2⟩
        · intro n hn hni
          rw [frobPush_apply_of_not g, zero_mul]
          rintro ⟨j, rfl⟩
          apply hni
          have hn' := mem_Ioc.mp hn
          have hj0 : j ≠ 0 := by
            rintro rfl
            rw [zero_pow hp0] at hn'
            exact absurd hn'.1 (lt_irrefl 0)
          refine mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hj0, ?_⟩, hn'.2⟩, rfl⟩
          exact (Nat.le_self_pow hp0 j).trans hn'.2

/-- **Summation lemma**: `sum_{n <= x} (f * E_p g)(n) = sum_{m >= 1, m^p <= x} g(m) F(x / m^p)`,
`F` the summatory function of `f`. -/
theorem sum_mul_frobPush {p : ℕ} (hp0 : p ≠ 0) (f g : ArithmeticFunction R) (x : ℕ) :
    ∑ n ∈ Ioc 0 x, (f * frobPush p g) n =
      ∑ m ∈ (Ioc 0 x).filter (fun m => m ^ p ≤ x), g m * ∑ n ∈ Ioc 0 (x / m ^ p), f n := by
  rw [mul_comm, sum_Ioc_mul_eq_sum_sum]
  exact sum_frobPush_mul hp0 g (fun n => ∑ m ∈ Ioc 0 (x / n), f m) x

theorem coef_apply (j c : ℕ) (Y : ArithmeticFunction ℤ) (n : ℕ) :
    ((-1 : ArithmeticFunction ℤ) ^ j * (c : ArithmeticFunction ℤ) * Y) n = (-1 : ℤ) ^ j * c * Y n := by
  rw [mul_assoc, mul_assoc]
  rcases Nat.even_or_odd j with h | h
  · rw [h.neg_one_pow, h.neg_one_pow, one_mul, one_mul, natCast_mul_apply]
  · rw [h.neg_one_pow, h.neg_one_pow, neg_one_mul, neg_one_mul, ArithmeticFunction.neg_apply, natCast_mul_apply]

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Target (a), summed Newton lift**: for every `x`,
`M(x) == sum_{j<k} (-1)^j C(k, j+1) sum_{m^p <= x} mu^{*(j+1)}(m) D_{(j+1)p-1}(x / m^p) (mod p^k)`. -/
theorem mertens_cong_binom (k x : ℕ) :
    (p : ℤ) ^ k ∣ (∑ n ∈ Ioc 0 x, (μ n : ℤ)) -
      ∑ j ∈ Finset.range k, (-1 : ℤ) ^ j * (k.choose (j + 1) : ℤ) *
        ∑ m ∈ (Ioc 0 x).filter (fun m => m ^ p ≤ x),
          ((μ : ArithmeticFunction ℤ) ^ (j + 1)) m *
            ∑ n ∈ Ioc 0 (x / m ^ p), ((ζ : ArithmeticFunction ℤ) ^ ((j + 1) * p - 1)) n := by
  have hp0 := hp.out.ne_zero
  have h := newton_cong_binom p k
  have key : ∑ n ∈ Ioc 0 x, (∑ j ∈ Finset.range k, (-1 : ArithmeticFunction ℤ) ^ j *
      (k.choose (j + 1) : ArithmeticFunction ℤ) *
        ((ζ : ArithmeticFunction ℤ) ^ ((j + 1) * p - 1) * frobPush p ((μ : ArithmeticFunction ℤ) ^ (j + 1)))) n =
      ∑ j ∈ Finset.range k, (-1 : ℤ) ^ j * (k.choose (j + 1) : ℤ) *
        ∑ m ∈ (Ioc 0 x).filter (fun m => m ^ p ≤ x),
          ((μ : ArithmeticFunction ℤ) ^ (j + 1)) m *
            ∑ n ∈ Ioc 0 (x / m ^ p), ((ζ : ArithmeticFunction ℤ) ^ ((j + 1) * p - 1)) n := by
    simp only [sum_apply', coef_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, sum_mul_frobPush hp0]
  rw [← key, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro n _
  have := h n
  push_cast at this
  exact this

end SummedNewton

end FrobCong

open FrobCong in
#print axioms sum_mul_frobPush
open FrobCong in
#print axioms mertens_cong_binom

namespace FrobCong

open scoped Nat

section Moment

/-- `u_t = -p (t + 1)`. -/
def momU (p t : ℕ) : ℤ := -((p : ℤ) * ((t : ℤ) + 1))

/-- `D(m, n) = sum_t c_t (1 + u_t)^m u_t^n - [n = 0]`, the functional at `(1 + X)^m X^n`. -/
def momD (p K0 : ℕ) (c : ℕ → ℤ) (m n : ℕ) : ℤ :=
  (∑ t ∈ Finset.range K0, c t * ((1 + momU p t) ^ m * momU p t ^ n)) - (0 : ℤ) ^ n

theorem momD_rel (p K0 : ℕ) (c : ℕ → ℤ) (m n : ℕ) :
    momD p K0 c m n = momD p K0 c (m + 1) n - momD p K0 c m (n + 1) := by
  unfold momD
  have e : ∀ t, c t * ((1 + momU p t) ^ m * momU p t ^ n) =
      c t * ((1 + momU p t) ^ (m + 1) * momU p t ^ n) - c t * ((1 + momU p t) ^ m * momU p t ^ (n + 1)) :=
    fun t => by ring
  rw [Finset.sum_congr rfl (fun t _ => e t), Finset.sum_sub_distrib, pow_succ (0 : ℤ) n, mul_zero]
  ring

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Target (b), the moment lemma (core of Th1)**: if `sum_{t=1}^{K0} c_t (1 - p t)^r == 1 (mod p^k)`
for every `r >= k`, then `k <= K0 + v_p(K0!)`.  (Here `c t` is the coefficient of index `t + 1`.) -/
theorem moment_bound (k K0 : ℕ) (c : ℕ → ℤ)
    (h : ∀ r, k ≤ r → (p : ℤ) ^ k ∣ (∑ t ∈ Finset.range K0, c t * (1 - (p : ℤ) * ((t : ℤ) + 1)) ^ r) - 1) :
    k ≤ K0 + padicValNat p (K0 !) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Nat.zero_le _
  -- columns m >= k
  have hm : ∀ n m, k ≤ m → (p : ℤ) ^ k ∣ momD p K0 c m n := by
    intro n
    induction n with
    | zero =>
      intro m hkm
      have e : ∀ t : ℕ, (1 : ℤ) + momU p t = 1 - (p : ℤ) * ((t : ℤ) + 1) := fun t => by
        unfold momU; ring
      simp only [momD, e, pow_zero, mul_one]
      exact h m hkm
    | succ n ih =>
      intro m hkm
      have r := momD_rel p K0 c m n
      rw [show momD p K0 c m (n + 1) = momD p K0 c (m + 1) n - momD p K0 c m n by linarith]
      exact dvd_sub (ih (m + 1) (by omega)) (ih m hkm)
  -- rows n >= k
  have hn : ∀ m n, k ≤ n → (p : ℤ) ^ k ∣ momD p K0 c m n := by
    intro m n hkn
    unfold momD
    rw [zero_pow (by omega), sub_zero]
    apply Finset.dvd_sum
    intro t _
    have hu : (p : ℤ) ∣ momU p t := by
      unfold momU; exact (dvd_neg).mpr (dvd_mul_right _ _)
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
      ((pow_dvd_pow (p : ℤ) hkn).trans (pow_dvd_pow_of_dvd hu n)) _) _
  -- all entries, by induction on 2k - m - n
  have hall : ∀ d m n, 2 * k ≤ m + n + d → (p : ℤ) ^ k ∣ momD p K0 c m n := by
    intro d
    induction d with
    | zero =>
      intro m n hmn
      rcases le_or_gt k m with h1 | h1
      · exact hm n m h1
      · exact hn m n (by omega)
    | succ d ih =>
      intro m n hmn
      rcases le_or_gt k m with h1 | h1
      · exact hm n m h1
      rcases le_or_gt k n with h2 | h2
      · exact hn m n h2
      rw [momD_rel p K0 c m n]
      exact dvd_sub (ih (m + 1) n (by omega)) (ih m (n + 1) (by omega))
  -- the polynomial H = prod_{s < K0} (X + p (s + 1))
  set P : Polynomial ℤ := ∏ s ∈ Finset.range K0, (Polynomial.X + Polynomial.C ((p : ℤ) * ((s : ℤ) + 1)))
    with hP
  have hev : ∀ y : ℤ, P.eval y = ∏ s ∈ Finset.range K0, (y + (p : ℤ) * ((s : ℤ) + 1)) := by
    intro y
    rw [hP, Polynomial.eval_prod]
    simp
  have key : (∑ t ∈ Finset.range K0, c t * P.eval (momU p t)) - P.eval 0 =
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * momD p K0 c 0 i := by
    simp only [Polynomial.eval_eq_sum_range, momD, pow_zero, one_mul, mul_sub, Finset.sum_sub_distrib,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hzero : ∀ t ∈ Finset.range K0, P.eval (momU p t) = 0 := by
    intro t ht
    rw [hev]
    apply Finset.prod_eq_zero ht
    unfold momU
    ring
  have hP0 : P.eval 0 = ((p ^ K0 * K0 ! : ℕ) : ℤ) := by
    rw [hev, ← Finset.prod_range_add_one_eq_factorial]
    simp only [zero_add]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    push_cast
    ring
  have hdvd : (p : ℤ) ^ k ∣ (∑ t ∈ Finset.range K0, c t * P.eval (momU p t)) - P.eval 0 := by
    rw [key]
    exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hall (2 * k) 0 i (by omega)) _)
  rw [Finset.sum_eq_zero (fun t ht => by rw [hzero t ht, mul_zero]), zero_sub, dvd_neg, hP0] at hdvd
  have hnat : p ^ k ∣ p ^ K0 * K0 ! := by exact_mod_cast hdvd
  have hne : p ^ K0 * K0 ! ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (Nat.factorial_ne_zero _)
  have hv := (padicValNat_dvd_iff_le hne).mp hnat
  rwa [padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) (Nat.factorial_ne_zero _),
    padicValNat.prime_pow] at hv

end Moment

end FrobCong

open FrobCong in
#print axioms moment_bound

namespace FrobCong

open scoped Nat

section LevelTwo

/-- `zeta^z` at a prime `q` is `z`. -/
theorem zeta_pow_apply_prime (z : ℕ) {q : ℕ} (hq : q.Prime) :
    ((ζ : ArithmeticFunction ℤ) ^ z) q = z := by
  induction z with
  | zero => rw [pow_zero, one_apply_ne hq.ne_one]; simp
  | succ z ih =>
    rw [pow_succ', coe_zeta_mul_apply, hq.divisors, Finset.sum_pair hq.ne_one.symm, ih,
      (isMultiplicative_zeta.natCast.pow (k := z) : IsMultiplicative ((ζ : ArithmeticFunction ℤ) ^ z)).map_one]
    push_cast
    ring

/-- A product of distinct primes is squarefree. -/
theorem squarefree_prod_primes (t : Finset ℕ) (ht : ∀ q ∈ t, q.Prime) : Squarefree (∏ q ∈ t, q) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Nat.squarefree_mul_iff]
    refine ⟨?_, Irreducible.squarefree (ht a (mem_insert_self a s)),
      ih (fun q hq => ht q (mem_insert_of_mem hq))⟩
    apply Nat.Coprime.prod_right
    intro q hq
    exact (Nat.coprime_primes (ht a (mem_insert_self a s)) (ht q (mem_insert_of_mem hq))).mpr
      (fun h => ha (h ▸ hq))

/-- At squarefree `n`, `(zeta^z * E_2 g)(n) = zeta^z(n) g(1)`. -/
theorem zeta_pow_mul_frobPush_two_sqfree (z : ℕ) (g : ArithmeticFunction ℤ) {n : ℕ}
    (hn : Squarefree n) (hn0 : n ≠ 0) :
    ((ζ : ArithmeticFunction ℤ) ^ z * frobPush 2 g) n = ((ζ : ArithmeticFunction ℤ) ^ z) n * g 1 := by
  rw [mul_apply, Finset.sum_eq_single (n, 1)]
  · have := frobPush_apply_pow (p := 2) two_ne_zero g one_ne_zero
    rw [one_pow] at this
    rw [this]
  · intro x hx hne
    rw [frobPush_apply_of_not g, mul_zero]
    rintro ⟨j, hj⟩
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have hj1 : IsUnit j := hn j ⟨x.1, by rw [← hx'.1, ← hj]; ring⟩
    rw [Nat.isUnit_iff] at hj1
    apply hne
    have h2 : x.2 = 1 := by rw [← hj, hj1, one_pow]
    have h1 : x.1 = n := by rw [← hx'.1, h2, mul_one]
    exact Prod.ext h1 h2
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one n, hn0⟩) h

/-- Even `z` drop modulo `2^r`; odd `z = 2t + 1` remain. -/
theorem odd_split (a : ℕ → ℤ) (r N : ℕ) :
    (2 : ℤ) ^ r ∣ (∑ z ∈ Finset.range N, a z * (z : ℤ) ^ r) -
      ∑ t ∈ Finset.range (N / 2), a (2 * t + 1) * ((2 * t + 1 : ℕ) : ℤ) ^ r := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.even_or_odd N with ⟨m, hm⟩ | ⟨m, hm⟩
    · have e : (N + 1) / 2 = N / 2 := by omega
      rw [e]
      have h2 : (2 : ℤ) ∣ (N : ℤ) := ⟨m, by rw [hm]; push_cast; ring⟩
      have := dvd_add ih (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd h2 r) (a N))
      rw [show ∀ x y w : ℤ, x + y - w = (x - w) + y from fun x y w => by ring]
      exact this
    · have e : (N + 1) / 2 = N / 2 + 1 := by omega
      have e2 : 2 * (N / 2) + 1 = N := by omega
      rw [e, Finset.sum_range_succ, e2]
      convert ih using 1
      ring

/-- **Target (c), p = 2**: if `mu == sum_{z <= L} zeta^z * E_2(g_z) (mod 2^k)` coefficientwise, then the
moment condition of `moment_bound` holds for `c_t = g_{2t+1}(1)`, so `k <= K0 + v_2(K0!)`, `K0 = (L+1)/2`. -/
theorem level_bound_two (k L : ℕ) (g : ℕ → ArithmeticFunction ℤ)
    (h : Cong (2 ^ k) (μ : ArithmeticFunction ℤ)
      (∑ z ∈ Finset.range (L + 1), (ζ : ArithmeticFunction ℤ) ^ z * frobPush 2 (g z))) :
    k ≤ (L + 1) / 2 + padicValNat 2 (((L + 1) / 2) !) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply moment_bound 2 k ((L + 1) / 2) (fun t => g (2 * t + 1) 1)
  intro r hr
  simp only [Nat.cast_ofNat]
  obtain ⟨T, hT, hTc⟩ := (Set.infinite_of_not_bddAbove Nat.not_bddAbove_setOfPred_prime).exists_subset_card_eq r
  have hTp : ∀ q ∈ T, q.Prime := fun q hq => hT hq
  have hsq : Squarefree (∏ q ∈ T, q) := squarefree_prod_primes T hTp
  have hn0 : (∏ q ∈ T, q) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun q hq => (hTp q hq).ne_zero)
  have hmu : (μ : ArithmeticFunction ℤ) (∏ q ∈ T, q) = (-1) ^ r := by
    rw [IsMultiplicative.map_prod_of_prime isMultiplicative_moebius T hTp,
      Finset.prod_congr rfl (fun q hq => moebius_apply_prime (hTp q hq)), Finset.prod_const, hTc]
  have hz : ∀ z : ℕ, ((ζ : ArithmeticFunction ℤ) ^ z) (∏ q ∈ T, q) = (z : ℤ) ^ r := by
    intro z
    rw [IsMultiplicative.map_prod_of_prime (isMultiplicative_zeta.natCast.pow (k := z)) T hTp,
      Finset.prod_congr rfl (fun q hq => zeta_pow_apply_prime z (hTp q hq)), Finset.prod_const, hTc]
  have hS : (∑ z ∈ Finset.range (L + 1), (ζ : ArithmeticFunction ℤ) ^ z * frobPush 2 (g z)) (∏ q ∈ T, q) =
      ∑ z ∈ Finset.range (L + 1), g z 1 * (z : ℤ) ^ r := by
    rw [sum_apply']
    apply Finset.sum_congr rfl
    intro z _
    rw [zeta_pow_mul_frobPush_two_sqfree z (g z) hsq hn0, hz, mul_comm]
  have h1 := h (∏ q ∈ T, q)
  rw [hmu, hS] at h1
  push_cast at h1
  have h2 := dvd_add h1 ((pow_dvd_pow (2 : ℤ) hr).trans (odd_split (fun z => g z 1) r (L + 1)))
  beta_reduce at h2
  have hT' : ∑ t ∈ Finset.range ((L + 1) / 2), g (2 * t + 1) 1 * ((2 * t + 1 : ℕ) : ℤ) ^ r =
      (-1) ^ r * ∑ t ∈ Finset.range ((L + 1) / 2), g (2 * t + 1) 1 * (1 - 2 * ((t : ℤ) + 1)) ^ r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    have : ((2 * t + 1 : ℕ) : ℤ) ^ r = (-1) ^ r * (1 - 2 * ((t : ℤ) + 1)) ^ r := by
      rw [← mul_pow]; push_cast; ring
    rw [this]
    ring
  rw [hT'] at h2
  obtain ⟨q, hq⟩ := h2
  have u2 : ((-1 : ℤ) ^ r) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  refine ⟨-((-1) ^ r * q), ?_⟩
  linear_combination (-((-1 : ℤ) ^ r)) * hq +
    (1 - ∑ t ∈ Finset.range ((L + 1) / 2), g (2 * t + 1) 1 * (1 - 2 * ((t : ℤ) + 1)) ^ r) * u2

/-- The level form: if every `K' < K` has `K' + v_2(K'!) < k` (so `K <= K(2,k)`), then `2 K <= L + 1`. -/
theorem level_bound_two_K (k L K : ℕ) (g : ℕ → ArithmeticFunction ℤ)
    (h : Cong (2 ^ k) (μ : ArithmeticFunction ℤ)
      (∑ z ∈ Finset.range (L + 1), (ζ : ArithmeticFunction ℤ) ^ z * frobPush 2 (g z)))
    (hK : ∀ K' < K, K' + padicValNat 2 (K' !) < k) : 2 * K ≤ L + 1 := by
  have h1 := level_bound_two k L g h
  by_contra hc
  have h2 := hK ((L + 1) / 2) (by omega)
  omega

end LevelTwo

end FrobCong

open FrobCong in
#print axioms level_bound_two
open FrobCong in
#print axioms level_bound_two_K

/-! ## r4l PR-O4: the odd-p lower bound (Th1 for every prime p) -/

namespace FrobCong

open scoped Nat

section LevelOdd

/-- At squarefree `n`, `(zeta^z * E_p g)(n) = zeta^z(n) g(1)`, for any `p >= 2`. -/
theorem zeta_pow_mul_frobPush_sqfree {p : ℕ} (hp2 : 2 ≤ p) (z : ℕ) (g : ArithmeticFunction ℤ) {n : ℕ}
    (hn : Squarefree n) (hn0 : n ≠ 0) :
    ((ζ : ArithmeticFunction ℤ) ^ z * frobPush p g) n = ((ζ : ArithmeticFunction ℤ) ^ z) n * g 1 := by
  rw [mul_apply, Finset.sum_eq_single (n, 1)]
  · have := frobPush_apply_pow (p := p) (by omega) g one_ne_zero
    rw [one_pow] at this
    rw [this]
  · intro x hx hne
    rw [frobPush_apply_of_not g, mul_zero]
    rintro ⟨j, hj⟩
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have e : j ^ p = j * j * j ^ (p - 2) := by
      rw [← sq, ← pow_add]; congr 1; omega
    have hj1 : IsUnit j := hn j ⟨x.1 * j ^ (p - 2), by rw [← hx'.1, ← hj, e]; ring⟩
    rw [Nat.isUnit_iff] at hj1
    apply hne
    have h2 : x.2 = 1 := by rw [← hj, hj1, one_pow]
    have h1 : x.1 = n := by rw [← hx'.1, h2, mul_one]
    exact Prod.ext h1 h2
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one n, hn0⟩) h

/-- Th1, step 1: the identity gives `sum_{z<=L} c_z z^r == (-1)^r (mod p^k)` for every `r >= 0`,
with `c_z = g_z(1)` (evaluate at a product of `r` distinct primes). -/
theorem level_moments {p : ℕ} (hp2 : 2 ≤ p) (k L : ℕ) (g : ℕ → ArithmeticFunction ℤ)
    (h : Cong (p ^ k) (μ : ArithmeticFunction ℤ)
      (∑ z ∈ Finset.range (L + 1), (ζ : ArithmeticFunction ℤ) ^ z * frobPush p (g z))) (r : ℕ) :
    (p : ℤ) ^ k ∣ (∑ z ∈ Finset.range (L + 1), g z 1 * (z : ℤ) ^ r) - (-1) ^ r := by
  obtain ⟨T, hT, hTc⟩ := (Set.infinite_of_not_bddAbove Nat.not_bddAbove_setOfPred_prime).exists_subset_card_eq r
  have hTp : ∀ q ∈ T, q.Prime := fun q hq => hT hq
  have hsq : Squarefree (∏ q ∈ T, q) := squarefree_prod_primes T hTp
  have hn0 : (∏ q ∈ T, q) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun q hq => (hTp q hq).ne_zero)
  have hmu : (μ : ArithmeticFunction ℤ) (∏ q ∈ T, q) = (-1) ^ r := by
    rw [IsMultiplicative.map_prod_of_prime isMultiplicative_moebius T hTp,
      Finset.prod_congr rfl (fun q hq => moebius_apply_prime (hTp q hq)), Finset.prod_const, hTc]
  have hz : ∀ z : ℕ, ((ζ : ArithmeticFunction ℤ) ^ z) (∏ q ∈ T, q) = (z : ℤ) ^ r := by
    intro z
    rw [IsMultiplicative.map_prod_of_prime (isMultiplicative_zeta.natCast.pow (k := z)) T hTp,
      Finset.prod_congr rfl (fun q hq => zeta_pow_apply_prime z (hTp q hq)), Finset.prod_const, hTc]
  have hS : (∑ z ∈ Finset.range (L + 1), (ζ : ArithmeticFunction ℤ) ^ z * frobPush p (g z)) (∏ q ∈ T, q) =
      ∑ z ∈ Finset.range (L + 1), g z 1 * (z : ℤ) ^ r := by
    rw [sum_apply']
    apply Finset.sum_congr rfl
    intro z _
    rw [zeta_pow_mul_frobPush_sqfree hp2 z (g z) hsq hn0, hz, mul_comm]
  have h1 := h (∏ q ∈ T, q)
  rw [hmu, hS] at h1
  push_cast at h1
  have h2 := dvd_neg.mpr h1
  rwa [neg_sub] at h2

/-- Th1, step 2 (the filter, replacing Teichmuller lifts): if `sum_z a_z z^r == (-1)^r (mod m)` for
all `r`, then `sum_z a_z z^r (z + 1)^N == 0 (mod m)` for all `r` and `N >= 1` (binomial expansion and
`(-1 + 1)^N = 0`). -/
theorem moment_filter (m : ℤ) (a : ℕ → ℤ) (M N : ℕ) (hN : 1 ≤ N)
    (h : ∀ r, m ∣ (∑ z ∈ Finset.range M, a z * (z : ℤ) ^ r) - (-1) ^ r) (r : ℕ) :
    m ∣ ∑ z ∈ Finset.range M, a z * (z : ℤ) ^ r * ((z : ℤ) + 1) ^ N := by
  have e0 : ∑ j ∈ Finset.range (N + 1), (N.choose j : ℤ) * (-1) ^ (r + j) =
      (-1) ^ r * ((-1) + 1) ^ N := by
    rw [add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [one_pow, pow_add]
    ring
  rw [neg_add_cancel, zero_pow (by omega), mul_zero] at e0
  have e : ∑ z ∈ Finset.range M, a z * (z : ℤ) ^ r * ((z : ℤ) + 1) ^ N =
      ∑ j ∈ Finset.range (N + 1),
        (N.choose j : ℤ) * ((∑ z ∈ Finset.range M, a z * (z : ℤ) ^ (r + j)) - (-1) ^ (r + j)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, e0, sub_zero]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [one_pow, pow_add]
    ring
  rw [e]
  exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_right (h (r + j)) _)

end LevelOdd

end FrobCong

namespace FrobCong

open scoped Nat

section LevelOdd2

variable (p : ℕ) [hp : Fact p.Prime]

/-- Th1, step 3 (isolating the class `z == -1 (mod p)`): with `N = phi(p^k) k`,
`z^r (1 - (z+1)^N) == z^r [p | z + 1] (mod p^k)` (Euler for `p` not dividing `z + 1`), and the
`z < M` with `p | z + 1` are `z = p t + (p - 1)`, `t < M / p`. -/
theorem class_split (k : ℕ) (a : ℕ → ℤ) (r M : ℕ) :
    (p : ℤ) ^ k ∣ (∑ z ∈ Finset.range M, a z * (z : ℤ) ^ r * (1 - ((z : ℤ) + 1) ^ (φ (p ^ k) * k))) -
      ∑ t ∈ Finset.range (M / p), a (p * t + (p - 1)) * ((p * t + (p - 1) : ℕ) : ℤ) ^ r := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Nat.succ_div]
    by_cases hd : p ∣ M + 1
    · rw [if_pos hd, Finset.sum_range_succ]
      have eM : p * (M / p) + (p - 1) = M := by
        obtain ⟨q, hq⟩ := hd
        rcases q with _ | q
        · simp at hq
        · have hp1 := hp.out.one_lt
          have hM : M = p * q + (p - 1) := by
            rw [Nat.mul_succ] at hq
            generalize p * q = Q at hq ⊢
            omega
          rw [hM, Nat.mul_add_div hp.out.pos, Nat.div_eq_of_lt (by omega), add_zero]
      rw [eM]
      have hdz : (p : ℤ) ^ k ∣ ((M : ℤ) + 1) ^ (φ (p ^ k) * k) := by
        have h1 : (p : ℤ) ∣ (M : ℤ) + 1 := by exact_mod_cast hd
        exact (pow_dvd_pow (p : ℤ)
          (Nat.le_mul_of_pos_left k (Nat.totient_pos.mpr (pow_pos hp.out.pos k)))).trans
          (pow_dvd_pow_of_dvd h1 _)
      have := dvd_sub ih (dvd_mul_of_dvd_right hdz (a M * (M : ℤ) ^ r))
      convert this using 1 <;> first | rfl | ring
    · rw [if_neg hd, add_zero]
      have hcop : Nat.Coprime (M + 1) (p ^ k) :=
        Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hd).symm
      have h2 := (Nat.ModEq.pow_totient hcop).pow k
      rw [one_pow, ← pow_mul] at h2
      have h3 := Nat.modEq_iff_dvd.mp h2
      push_cast at h3
      have := dvd_add ih (dvd_mul_of_dvd_right h3 (a M * (M : ℤ) ^ r))
      convert this using 1 <;> first | rfl | ring

/-- **Th1 for every prime `p`**: if `mu == sum_{z <= L} zeta^z * E_p(g_z) (mod p^k)` coefficientwise
(`g_z` integer valued), then `k <= K0 + v_p(K0!)` with `K0 = (L + 1) / p`. -/
theorem level_bound (k L : ℕ) (g : ℕ → ArithmeticFunction ℤ)
    (h : Cong (p ^ k) (μ : ArithmeticFunction ℤ)
      (∑ z ∈ Finset.range (L + 1), (ζ : ArithmeticFunction ℤ) ^ z * frobPush p (g z))) :
    k ≤ (L + 1) / p + padicValNat p (((L + 1) / p) !) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Nat.zero_le _
  apply moment_bound p k ((L + 1) / p) (fun t => g (p * t + (p - 1)) 1)
  intro r _
  have hmom := level_moments hp.out.two_le k L g h
  have hN : 1 ≤ φ (p ^ k) * k := Nat.mul_pos (Nat.totient_pos.mpr (pow_pos hp.out.pos k)) hk
  have hf := moment_filter ((p : ℤ) ^ k) (fun z => g z 1) (L + 1) (φ (p ^ k) * k) hN hmom r
  have hs := class_split p k (fun z => g z 1) r (L + 1)
  beta_reduce at hf hs
  have e : ∑ z ∈ Finset.range (L + 1), g z 1 * (z : ℤ) ^ r * (1 - ((z : ℤ) + 1) ^ (φ (p ^ k) * k)) =
      (∑ z ∈ Finset.range (L + 1), g z 1 * (z : ℤ) ^ r) -
        ∑ z ∈ Finset.range (L + 1), g z 1 * (z : ℤ) ^ r * ((z : ℤ) + 1) ^ (φ (p ^ k) * k) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    ring
  have key := dvd_sub (dvd_sub (hmom r) hf) hs
  rw [e] at key
  set T' := ∑ t ∈ Finset.range ((L + 1) / p), g (p * t + (p - 1)) 1 * (1 - (p : ℤ) * ((t : ℤ) + 1)) ^ r
    with hT'
  have hT : ∑ t ∈ Finset.range ((L + 1) / p), g (p * t + (p - 1)) 1 * ((p * t + (p - 1) : ℕ) : ℤ) ^ r =
      (-1) ^ r * T' := by
    rw [hT', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    have : ((p * t + (p - 1) : ℕ) : ℤ) = -(1 - (p : ℤ) * ((t : ℤ) + 1)) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hp.out.one_le]
      push_cast
      ring
    rw [this, neg_pow]
    ring
  rw [hT] at key
  obtain ⟨q, hq⟩ := key
  have u2 : ((-1 : ℤ) ^ r) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  refine ⟨(-1) ^ r * q, ?_⟩
  linear_combination ((-1 : ℤ) ^ r) * hq + (1 - T') * u2

/-- The level form: if every `K' < K` has `K' + v_p(K'!) < k` (so `K <= K(p,k)`), then `p K <= L + 1`. -/
theorem level_bound_K (k L K : ℕ) (g : ℕ → ArithmeticFunction ℤ)
    (h : Cong (p ^ k) (μ : ArithmeticFunction ℤ)
      (∑ z ∈ Finset.range (L + 1), (ζ : ArithmeticFunction ℤ) ^ z * frobPush p (g z)))
    (hK : ∀ K' < K, K' + padicValNat p (K' !) < k) : p * K ≤ L + 1 := by
  have h1 := level_bound p k L g h
  by_contra hc
  have hlt : (L + 1) / p < K := by
    by_contra h2
    push Not at h2
    have := Nat.mul_le_mul_left p h2
    have := Nat.mul_div_le (L + 1) p
    omega
  have h2 := hK ((L + 1) / p) hlt
  omega

end LevelOdd2

end FrobCong

open FrobCong in
#print axioms level_moments
open FrobCong in
#print axioms moment_filter
open FrobCong in
#print axioms class_split
open FrobCong in
#print axioms level_bound
open FrobCong in
#print axioms level_bound_K

/-! ## r4l PR-O4 stretch: the mod 8 construction (Th2 / Th5, p = 2, k = 3, K = 2, levels 1 and 3) -/

namespace FrobCong

open scoped Nat

section FrobHom

variable {R : Type*} [CommRing R]

theorem frobPush_add (p : ℕ) (f g : ArithmeticFunction R) :
    frobPush p (f + g) = frobPush p f + frobPush p g := by
  ext n
  simp only [frobPush_apply, ArithmeticFunction.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp

theorem frobPush_zero (p : ℕ) : frobPush p (0 : ArithmeticFunction R) = 0 := by
  ext n
  simp [frobPush_apply]

/-- `E_p` as a ring endomorphism of `ArithmeticFunction R`. -/
def frobHom {p : ℕ} (hp0 : p ≠ 0) : ArithmeticFunction R →+* ArithmeticFunction R where
  toFun := frobPush p
  map_one' := frobPush_one hp0
  map_mul' := frobPush_mul hp0
  map_zero' := frobPush_zero p
  map_add' := frobPush_add p

end FrobHom

section ModEight

/-- `D` with `2 D = E_2 zeta - zeta^2` (exact division by `zeta_pow_cong`); `D = delta(zeta)`. -/
def dZ : ArithmeticFunction ℤ :=
  ⟨fun n => (frobPush 2 (ζ : ArithmeticFunction ℤ) - (ζ : ArithmeticFunction ℤ) ^ 2) n / 2, by simp⟩

theorem dZ_apply (n : ℕ) :
    dZ n = (frobPush 2 (ζ : ArithmeticFunction ℤ) - (ζ : ArithmeticFunction ℤ) ^ 2) n / 2 := rfl

theorem two_mul_dZ :
    (2 : ArithmeticFunction ℤ) * dZ = frobPush 2 (ζ : ArithmeticFunction ℤ) - (ζ : ArithmeticFunction ℤ) ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext n
  rw [show (2 : ArithmeticFunction ℤ) = ((2 : ℕ) : ArithmeticFunction ℤ) by norm_cast, natCast_mul_apply,
    dZ_apply]
  have h := zeta_pow_cong 2 n
  have h' : (2 : ℤ) ∣ (frobPush 2 (ζ : ArithmeticFunction ℤ) - (ζ : ArithmeticFunction ℤ) ^ 2) n := by
    rw [sub_apply']
    push_cast at h
    have h2 := dvd_neg.mpr h
    rwa [neg_sub] at h2
  push_cast
  exact Int.mul_ediv_cancel' h'

/-- `h = mu^2 + 4 D mu^4`. -/
def hE : ArithmeticFunction ℤ := μ ^ 2 + 4 * dZ * μ ^ 4

/-- **Th2 for p = 2, k = 3 (explicit)**: `mu == zeta * E_2(2 zeta h) + zeta^3 * E_2(-h) (mod 8)`,
`h = mu^2 + 4 D mu^4`, `2 D = E_2 zeta - zeta^2`. Only the levels `z = 1, 3` occur, so `L(2,3) <= 3`. -/
theorem mod_eight_identity :
    Cong 8 (μ : ArithmeticFunction ℤ)
      ((ζ : ArithmeticFunction ℤ) * frobPush 2 (2 * (ζ : ArithmeticFunction ℤ) * hE) +
        (ζ : ArithmeticFunction ℤ) ^ 3 * frobPush 2 (-hE)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΦ : ∀ f : ArithmeticFunction ℤ, frobPush 2 f = frobHom two_ne_zero f := fun f => rfl
  have R1 : (ζ : ArithmeticFunction ℤ) * μ = 1 := coe_zeta_mul_moebius
  have R2 : frobHom two_ne_zero (ζ : ArithmeticFunction ℤ) * frobHom two_ne_zero μ = 1 := by
    rw [← map_mul, R1, map_one]
  have R3 : 2 * dZ = frobHom two_ne_zero (ζ : ArithmeticFunction ℤ) - (ζ : ArithmeticFunction ℤ) ^ 2 :=
    two_mul_dZ
  set Z : ArithmeticFunction ℤ := (ζ : ArithmeticFunction ℤ) with hZ
  set y := frobHom two_ne_zero Z with hy
  set m' := frobHom two_ne_zero (μ : ArithmeticFunction ℤ) with hm'
  set Dp := frobHom two_ne_zero dZ with hDp
  have e : Z * frobPush 2 (2 * Z * hE) + Z ^ 3 * frobPush 2 (-hE) =
      Z * (2 * y * (m' ^ 2 + 4 * Dp * m' ^ 4)) - Z ^ 3 * (m' ^ 2 + 4 * Dp * m' ^ 4) := by
    rw [hΦ, hΦ, hE]
    simp only [map_mul, map_add, map_neg, map_pow, map_ofNat]
    ring
  have key : μ - (Z * (2 * y * (m' ^ 2 + 4 * Dp * m' ^ 4)) - Z ^ 3 * (m' ^ 2 + 4 * Dp * m' ^ 4)) =
      4 * ((dZ ^ 2 - Dp) * (μ * m' ^ 2)) + 8 * (2 * (μ * Dp * dZ ^ 2 * m' ^ 4)) := by
    linear_combination ((m' ^ 2 + 4 * Dp * m' ^ 4) * (2 * y * Z - Z ^ 3)) * R1 +
      (-μ * (m' * y + 1) * (1 + 4 * Dp * m' ^ 2)) * R2 +
      (-(m' ^ 2 + 4 * Dp * m' ^ 4) * μ * (2 * dZ + y - Z ^ 2)) * R3
  have hEv : ∀ n, (2 : ℤ) ∣ (dZ ^ 2 - Dp) n := fun n => by
    have h := cong_pow_frobPush 2 dZ n
    push_cast at h
    rw [sub_apply']
    exact h
  have hconv : ∀ (Y : ArithmeticFunction ℤ) (n : ℕ), (2 : ℤ) ∣ ((dZ ^ 2 - Dp) * Y) n := fun Y n => by
    rw [mul_apply]
    exact Finset.dvd_sum (fun x _ => dvd_mul_of_dvd_left (hEv x.1) _)
  have hnum4 : ∀ (F : ArithmeticFunction ℤ) (n : ℕ), ((4 : ArithmeticFunction ℤ) * F) n = 4 * F n :=
    fun F n => by
      (rw [show (4 : ArithmeticFunction ℤ) = ((4 : ℕ) : ArithmeticFunction ℤ) by norm_cast,
        natCast_mul_apply]) <;> norm_num
  have hnum8 : ∀ (F : ArithmeticFunction ℤ) (n : ℕ), ((8 : ArithmeticFunction ℤ) * F) n = 8 * F n :=
    fun F n => by
      (rw [show (8 : ArithmeticFunction ℤ) = ((8 : ℕ) : ArithmeticFunction ℤ) by norm_cast,
        natCast_mul_apply]) <;> norm_num
  intro n
  rw [e]
  have hk := congrArg (fun F : ArithmeticFunction ℤ => F n) key
  rw [sub_apply', ArithmeticFunction.add_apply, hnum4, hnum8] at hk
  rw [hk]
  obtain ⟨c, hc⟩ := hconv (μ * m' ^ 2) n
  rw [hc]
  push_cast
  exact dvd_add ⟨c, by ring⟩ (dvd_mul_right _ _)

/-- The level form: `g_1 = 2 zeta h`, `g_3 = -h`, all other `g_z = 0`, `L = 3`. -/
def gE (z : ℕ) : ArithmeticFunction ℤ :=
  if z = 1 then 2 * (ζ : ArithmeticFunction ℤ) * hE else if z = 3 then -hE else 0

theorem mod_eight_levels :
    Cong (2 ^ 3) (μ : ArithmeticFunction ℤ)
      (∑ z ∈ Finset.range (3 + 1), (ζ : ArithmeticFunction ℤ) ^ z * frobPush 2 (gE z)) := by
  have hs : ∑ z ∈ Finset.range (3 + 1), (ζ : ArithmeticFunction ℤ) ^ z * frobPush 2 (gE z) =
      (ζ : ArithmeticFunction ℤ) * frobPush 2 (2 * (ζ : ArithmeticFunction ℤ) * hE) +
        (ζ : ArithmeticFunction ℤ) ^ 3 * frobPush 2 (-hE) := by
    simp [Finset.sum_range_succ, gE, frobPush_zero]
  rw [hs]
  exact mod_eight_identity

/-- Sharpness: no identity mod 8 uses only levels `z <= 2`; with `mod_eight_levels`, `L(2,3) = 3`. -/
theorem mod_eight_sharp (L : ℕ) (g : ℕ → ArithmeticFunction ℤ)
    (h : Cong (2 ^ 3) (μ : ArithmeticFunction ℤ)
      (∑ z ∈ Finset.range (L + 1), (ζ : ArithmeticFunction ℤ) ^ z * frobPush 2 (g z))) : 3 ≤ L := by
  have := level_bound_two_K 3 L 2 g h (fun K' hK' => by interval_cases K' <;> simp)
  omega

end ModEight

end FrobCong

open FrobCong in
#print axioms two_mul_dZ
open FrobCong in
#print axioms mod_eight_identity
open FrobCong in
#print axioms mod_eight_levels
open FrobCong in
#print axioms mod_eight_sharp

/-! ## r4m PR-O5: the delta tower, R-053's upper bound for every prime `p` and every `k`

Polynomials in `Y` (standing for `zeta ^ p`) over `ArithmeticFunction ℤ`, evaluated with coefficients pushed by
`E_p`: `T_0 = 1 - mu Y`, `T_{b+1} = T_b ^ p - c_b ^ p w_b`, `c_0 = p`, `c_{b+1} = -p c_b ^ p`,
`w_0 = E_p(mu) delta(zeta)`, `w_{b+1} = delta(w_b)`, `p delta(w) = E_p w - w ^ p` (exact). Then
`T_b(zeta) = c_b w_b`, `p ^ (1 + p + ... + p ^ b) ∣ c_b`, and the product of `T_b ^ (e_b)` over the base `p`
digits `e_b` of `K` has degree `≤ K` in `Y`, constant term `≡ 1 (mod p)` and value divisible by
`p ^ (K + v_p(K!))` (Legendre). -/

namespace FrobCong

open scoped Nat Polynomial

section Tower

local notation "AF" => ArithmeticFunction ℤ

variable (p : ℕ) [hp : Fact p.Prime]

/-- `E_p` over `ℤ` as a ring hom. -/
abbrev EZ : AF →+* AF := frobHom (R := ℤ) hp.out.ne_zero

theorem EZ_apply (f : AF) : EZ p f = frobPush p f := rfl

/-- The exact divided difference `delta w = (E_p w - w ^ p) / p`. -/
def delta (w : AF) : AF :=
  ⟨fun n => (frobPush p w - w ^ p) n / p, by simp⟩

theorem delta_apply (w : AF) (n : ℕ) : delta p w n = (frobPush p w - w ^ p) n / p := rfl

theorem p_mul_delta (w : AF) : (p : AF) * delta p w = frobPush p w - w ^ p := by
  ext n
  rw [natCast_mul_apply, delta_apply]
  have h' : (p : ℤ) ∣ (frobPush p w - w ^ p) n := by
    rw [sub_apply']
    exact dvd_sub_comm.mp (cong_pow_frobPush p w n)
  exact Int.mul_ediv_cancel' h'

/-- `c_0 = p`, `c_{b+1} = -p c_b ^ p`. -/
def tc : ℕ → ℤ
  | 0 => p
  | b + 1 => -(p : ℤ) * tc b ^ p

/-- `w_0 = E_p(mu) delta(zeta)`, `w_{b+1} = delta(w_b)`. -/
def tw : ℕ → AF
  | 0 => frobPush p (μ : AF) * delta p (ζ : AF)
  | b + 1 => delta p (tw b)

/-- The tower polynomials in `Y`: `T_0 = 1 - mu Y`, `T_{b+1} = T_b ^ p - c_b ^ p w_b`. -/
noncomputable def tT : ℕ → AF[X]
  | 0 => 1 - Polynomial.C (μ : AF) * Polynomial.X
  | b + 1 => tT b ^ p - Polynomial.C (((tc p b : ℤ) : AF) ^ p * tw p b)

/-- Value at `Y = zeta ^ p` with coefficients pushed by `E_p`. -/
noncomputable def tval (P : AF[X]) : AF := P.eval₂ (EZ p) ((ζ : AF) ^ p)

theorem tval_mul (P P' : AF[X]) : tval p (P * P') = tval p P * tval p P' := by
  simp only [tval, Polynomial.eval₂_mul]

theorem tval_pow (P : AF[X]) (n : ℕ) : tval p (P ^ n) = tval p P ^ n := by
  simp only [tval, Polynomial.eval₂_pow]

/-- **The exact tower identity**: `T_b(zeta) = c_b w_b` in `ArithmeticFunction ℤ`. -/
theorem tval_tT (b : ℕ) : tval p (tT p b) = ((tc p b : ℤ) : AF) * tw p b := by
  induction b with
  | zero =>
    have h1 : frobPush p (μ : AF) * frobPush p (ζ : AF) = 1 := by
      rw [← EZ_apply, ← EZ_apply, ← _root_.map_mul, moebius_mul_coe_zeta, _root_.map_one]
    have h2 := p_mul_delta p (ζ : AF)
    simp only [tval, tT, tc, tw, Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X, EZ_apply, Int.cast_natCast]
    linear_combination -h1 - frobPush p (μ : AF) * h2
  | succ b ih =>
    have h2 := p_mul_delta p (tw p b)
    have e : tval p (tT p (b + 1)) =
        tval p (tT p b) ^ p - EZ p (((tc p b : ℤ) : AF) ^ p * tw p b) := by
      simp only [tval, tT, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_C]
    rw [e, ih, _root_.map_mul, _root_.map_pow, _root_.map_intCast, EZ_apply]
    simp only [tc, tw]
    push_cast
    linear_combination ((tc p b : ℤ) : AF) ^ p * h2

/-- `s_0 = 1`, `s_{b+1} = 1 + p s_b`, so `s_b = 1 + p + ... + p ^ b`. -/
def ts : ℕ → ℕ
  | 0 => 1
  | b + 1 => 1 + p * ts b

theorem ts_mul (b : ℕ) : ((p : ℤ) - 1) * (ts p b : ℤ) = (p : ℤ) ^ (b + 1) - 1 := by
  induction b with
  | zero => simp [ts]
  | succ b ih =>
    simp only [ts]
    push_cast
    linear_combination (p : ℤ) * ih

theorem tc_dvd (b : ℕ) : (p : ℤ) ^ ts p b ∣ tc p b := by
  induction b with
  | zero => simp [ts, tc]
  | succ b ih =>
    simp only [ts, tc]
    rw [pow_add, pow_one, pow_mul', neg_mul, dvd_neg]
    exact mul_dvd_mul_left _ (pow_dvd_pow_of_dvd ih p)

theorem tc_dvd_p (b : ℕ) : (p : AF) ∣ ((tc p b : ℤ) : AF) := by
  have h : (p : ℤ) ∣ tc p b := by
    cases b with
    | zero => simp [tc]
    | succ b =>
      simp only [tc]
      exact Dvd.dvd.mul_right (dvd_neg.mpr (dvd_refl _)) _
  have := map_dvd (Int.castRingHom AF) h
  simpa using this

/-- `p ^ (1 + p + ... + p ^ b)` divides `T_b(zeta)`. -/
theorem tval_tT_dvd (b : ℕ) : (p : AF) ^ ts p b ∣ tval p (tT p b) := by
  rw [tval_tT]
  refine Dvd.dvd.mul_right ?_ _
  have := map_dvd (Int.castRingHom AF) (tc_dvd p b)
  simpa using this

theorem tT_natDegree (b : ℕ) : (tT p b).natDegree ≤ p ^ b := by
  induction b with
  | zero =>
    simp only [tT, pow_zero]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  | succ b ih =>
    simp only [tT]
    refine (Polynomial.natDegree_sub_le _ _).trans
      (max_le ?_ (by rw [Polynomial.natDegree_C]; exact Nat.zero_le _))
    refine Polynomial.natDegree_pow_le.trans ?_
    rw [pow_succ']
    exact Nat.mul_le_mul_left p ih

/-- The constant term of `T_b` is `≡ 1 (mod p)`. -/
theorem tT_eval_zero (b : ℕ) : (p : AF) ∣ (tT p b).eval 0 - 1 := by
  induction b with
  | zero => simp [tT]
  | succ b ih =>
    simp only [tT, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C]
    have h1 : (p : AF) ∣ (tT p b).eval 0 ^ p - 1 := by
      have := sub_dvd_pow_sub_pow ((tT p b).eval 0) 1 p
      rw [one_pow] at this
      exact ih.trans this
    have h2 : (p : AF) ∣ ((tc p b : ℤ) : AF) ^ p * tw p b :=
      ((tc_dvd_p p b).trans (dvd_pow_self _ hp.out.ne_zero)).mul_right _
    have e : (tT p b).eval 0 ^ p - ((tc p b : ℤ) : AF) ^ p * tw p b - 1 =
        ((tT p b).eval 0 ^ p - 1) - ((tc p b : ℤ) : AF) ^ p * tw p b := by ring
    rw [e]
    exact dvd_sub h1 h2

/-- `QL b [e_0, e_1, ...] = T_b ^ e_0 * T_{b+1} ^ e_1 * ...` (digits, least significant first). -/
noncomputable def QL : ℕ → List ℕ → AF[X]
  | _, [] => 1
  | b, e :: t => tT p b ^ e * QL (b + 1) t

/-- `VL b [e_0, e_1, ...] = e_0 s_b + e_1 s_{b+1} + ...`. -/
def VL : ℕ → List ℕ → ℕ
  | _, [] => 0
  | b, e :: t => e * ts p b + VL (b + 1) t

theorem QL_natDegree (L : List ℕ) (b : ℕ) : (QL p b L).natDegree ≤ p ^ b * Nat.ofDigits p L := by
  induction L generalizing b with
  | nil => simp [QL]
  | cons e t ih =>
    simp only [QL, Nat.ofDigits_cons, Nat.cast_id]
    refine Polynomial.natDegree_mul_le.trans ?_
    have h1 : (tT p b ^ e).natDegree ≤ e * p ^ b :=
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left e (tT_natDegree p b))
    have h2 := ih (b + 1)
    calc _ ≤ e * p ^ b + p ^ (b + 1) * Nat.ofDigits p t := add_le_add h1 h2
      _ = p ^ b * (e + p * Nat.ofDigits p t) := by ring

theorem QL_dvd (L : List ℕ) (b : ℕ) : (p : AF) ^ VL p b L ∣ tval p (QL p b L) := by
  induction L generalizing b with
  | nil => simp [VL]
  | cons e t ih =>
    simp only [QL, VL]
    rw [tval_mul, tval_pow, pow_add]
    refine mul_dvd_mul ?_ (ih (b + 1))
    rw [show e * ts p b = ts p b * e from mul_comm _ _, pow_mul]
    exact pow_dvd_pow_of_dvd (tval_tT_dvd p b) e

theorem QL_eval_zero (L : List ℕ) (b : ℕ) : (p : AF) ∣ (QL p b L).eval 0 - 1 := by
  induction L generalizing b with
  | nil => simp [QL]
  | cons e t ih =>
    simp only [QL, Polynomial.eval_mul, Polynomial.eval_pow]
    have h1 : (p : AF) ∣ (tT p b).eval 0 ^ e - 1 := by
      have := sub_dvd_pow_sub_pow ((tT p b).eval 0) 1 e
      rw [one_pow] at this
      exact (tT_eval_zero p b).trans this
    have e' : (tT p b).eval 0 ^ e * (QL p (b + 1) t).eval 0 - 1 =
        ((tT p b).eval 0 ^ e - 1) * (QL p (b + 1) t).eval 0 + ((QL p (b + 1) t).eval 0 - 1) := by ring
    rw [e']
    exact dvd_add (h1.mul_right _) (ih (b + 1))

theorem VL_mul (L : List ℕ) (b : ℕ) :
    ((p : ℤ) - 1) * (VL p b L : ℤ) =
      (p : ℤ) ^ (b + 1) * ((Nat.ofDigits p L : ℕ) : ℤ) - ((L.sum : ℕ) : ℤ) := by
  induction L generalizing b with
  | nil => simp [VL, Nat.ofDigits_nil]
  | cons e t ih =>
    have h1 := ts_mul p b
    have h2 := ih (b + 1)
    simp only [VL, Nat.ofDigits_cons, Nat.cast_id, List.sum_cons, Nat.cast_add, Nat.cast_mul]
    linear_combination (e : ℤ) * h1 + h2

/-- **Valuation = Legendre**: `VL 0 (digits p K) = K + v_p(K!)`. -/
theorem VL_digits (K : ℕ) : VL p 0 (Nat.digits p K) = K + padicValNat p K ! := by
  have h1 := VL_mul p (Nat.digits p K) 0
  simp only [zero_add, pow_one, Nat.ofDigits_digits] at h1
  have h2 := sub_one_mul_padicValNat_factorial (p := p) K
  have h3 := Nat.digit_sum_le p K
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have h2' : ((p : ℤ) - 1) * (padicValNat p K ! : ℤ) = (K : ℤ) - (((Nat.digits p K).sum : ℕ) : ℤ) := by
    rw [← Nat.cast_one, ← Nat.cast_sub hp1, ← Nat.cast_mul, h2, Nat.cast_sub h3]
  have hp0 : (p : ℤ) - 1 ≠ 0 := by have := hp.out.two_le; omega
  have h4 : ((p : ℤ) - 1) * (VL p 0 (Nat.digits p K) : ℤ) =
      ((p : ℤ) - 1) * ((K + padicValNat p K ! : ℕ) : ℤ) := by
    rw [Nat.cast_add]
    linear_combination h1 - h2'
  exact_mod_cast mul_left_cancel₀ hp0 h4

end Tower

end FrobCong

namespace FrobCong

open scoped Nat Polynomial

section TowerMain

local notation "AF" => ArithmeticFunction ℤ

variable (p : ℕ) [hp : Fact p.Prime]

theorem moebius_mul_zeta_pow (i : ℕ) :
    (μ : AF) * ((ζ : AF) ^ p) ^ (i + 1) = (ζ : AF) ^ (p * (i + 1) - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, p * (i + 1) = m + 1 :=
    ⟨p * (i + 1) - 1, (Nat.sub_add_cancel (Nat.mul_pos hp.out.pos (Nat.succ_pos i))).symm⟩
  rw [← pow_mul, hm, Nat.add_sub_cancel, pow_succ, mul_comm, mul_assoc, coe_zeta_mul_moebius, mul_one]

/-- **R-053 upper bound (the delta tower, every prime `p`, every `k`)**: if `k ≤ K + v_p(K!)`, there are
integer arithmetic functions `h_1, ..., h_K` (here `h (i - 1)`) with
`mu ≡ sum_{i=1}^{K} zeta ^ (p i - 1) * E_p(h_i) (mod p ^ k)` coefficientwise. -/
theorem tower_upper (k K : ℕ) (hK : k ≤ K + padicValNat p K !) :
    ∃ h : ℕ → AF, Cong (p ^ k) (μ : AF)
      (∑ i ∈ Finset.range K, (ζ : AF) ^ (p * (i + 1) - 1) * frobPush p (h i)) := by
  have hdeg := QL_natDegree p (Nat.digits p K) 0
  have hdvd := QL_dvd p (Nat.digits p K) 0
  have hc0 := QL_eval_zero p (Nat.digits p K) 0
  simp only [pow_zero, one_mul, Nat.ofDigits_digits] at hdeg
  rw [VL_digits] at hdvd
  replace hdvd := (pow_dvd_pow (p : AF) hK).trans hdvd
  generalize QL p 0 (Nat.digits p K) = Q at hdeg hdvd hc0
  rw [← Polynomial.coeff_zero_eq_eval_zero] at hc0
  obtain ⟨t, ht⟩ := hc0
  set v : AF := ∑ j ∈ Finset.range k, ((p : AF) * (-t)) ^ j with hv
  have hinv : v * Q.coeff 0 = 1 - (p : AF) ^ k * (-t) ^ k := by
    have hq : Q.coeff 0 = 1 - (p : AF) * (-t) := by linear_combination ht
    rw [hq, mul_comm v, hv, mul_neg_geom_sum, mul_pow]
  have hsum : tval p Q = ∑ i ∈ Finset.range (K + 1), EZ p (Q.coeff i) * ((ζ : AF) ^ p) ^ i :=
    Polynomial.eval₂_eq_sum_range' _ (by omega) _
  have e1 : EZ p v * tval p Q = ∑ i ∈ Finset.range K, EZ p (v * Q.coeff (i + 1)) * ((ζ : AF) ^ p) ^ (i + 1)
      + EZ p (v * Q.coeff 0) := by
    rw [hsum, Finset.mul_sum, Finset.sum_range_succ']
    simp only [_root_.map_mul, pow_zero, mul_one, mul_assoc]
  have e2 : EZ p (v * Q.coeff 0) = 1 - (p : AF) ^ k * EZ p ((-t) ^ k) := by
    rw [hinv, _root_.map_sub, _root_.map_one, _root_.map_mul, _root_.map_pow,
      _root_.map_natCast]
  have e3 : ∀ i ∈ Finset.range K, (μ : AF) * (EZ p (v * Q.coeff (i + 1)) * ((ζ : AF) ^ p) ^ (i + 1)) =
      (ζ : AF) ^ (p * (i + 1) - 1) * EZ p (v * Q.coeff (i + 1)) := by
    intro i _
    rw [← moebius_mul_zeta_pow p i]
    ring
  have key : (μ : AF) - ∑ i ∈ Finset.range K, (ζ : AF) ^ (p * (i + 1) - 1) * frobPush p (-(v * Q.coeff (i + 1)))
      = (μ : AF) * (EZ p v * tval p Q + (p : AF) ^ k * EZ p ((-t) ^ k)) := by
    show (μ : AF) - ∑ i ∈ Finset.range K, (ζ : AF) ^ (p * (i + 1) - 1) * EZ p (-(v * Q.coeff (i + 1))) = _
    rw [e1, e2, mul_add, mul_add, Finset.mul_sum, Finset.sum_congr rfl e3]
    simp only [_root_.map_neg, mul_neg, Finset.sum_neg_distrib]
    ring
  refine ⟨fun i => -(v * Q.coeff (i + 1)), ?_⟩
  rw [cong_iff_dvd, Nat.cast_pow, key]
  obtain ⟨D, hD⟩ := hdvd
  exact ⟨(μ : AF) * (EZ p v * D + EZ p ((-t) ^ k)), by rw [hD]; ring⟩

theorem exists_K (k : ℕ) : ∃ K, k ≤ K + padicValNat p K ! := ⟨k, Nat.le_add_right _ _⟩

/-- **R-053 upper bound at the least level count** `K(p,k)` (the least `K` with `K + v_p(K!) ≥ k`):
`mu ≡ sum_{i=1}^{K(p,k)} zeta ^ (p i - 1) * E_p(h_i) (mod p ^ k)`. With `level_bound_K`, `L(p,k) + 1 = p K(p,k)`. -/
theorem tower_upper_min (k : ℕ) :
    ∃ h : ℕ → AF, Cong (p ^ k) (μ : AF)
      (∑ i ∈ Finset.range (Nat.find (exists_K p k)), (ζ : AF) ^ (p * (i + 1) - 1) * frobPush p (h i)) :=
  tower_upper p k _ (Nat.find_spec (exists_K p k))


/-- Level form: `g z = h ((z + 1) / p - 1)` when `p ∣ z + 1`, else `0` (only levels `z = p i - 1`). -/
def gL (h : ℕ → AF) (z : ℕ) : AF := if (z + 1) % p = 0 then h ((z + 1) / p - 1) else 0

theorem levels_reindex (h : ℕ → AF) (K : ℕ) :
    ∑ z ∈ Finset.range (p * K), (ζ : AF) ^ z * frobPush p (gL p h z) =
      ∑ i ∈ Finset.range K, (ζ : AF) ^ (p * (i + 1) - 1) * frobPush p (h i) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hp1 := hp.out.one_lt
    rw [show Finset.range (p * (K + 1)) = Finset.range (p * K + p) by rw [mul_add, mul_one],
      Finset.sum_range_add, Finset.sum_range_succ, ← ih]
    congr 1
    rw [Finset.sum_eq_single (p - 1)]
    · have e1 : p * K + (p - 1) = p * (K + 1) - 1 := by rw [mul_add, mul_one]; omega
      have e2 : p * K + (p - 1) + 1 = p * (K + 1) := by rw [mul_add, mul_one]; omega
      rw [gL, e2, Nat.mul_mod_right, if_pos rfl, Nat.mul_div_cancel_left _ hp.out.pos, Nat.add_sub_cancel,
        e1]
    · intro j hj hne
      have hj' := Finset.mem_range.mp hj
      have e3 : (p * K + j + 1) % p ≠ 0 := by
        rw [show p * K + j + 1 = (j + 1) + p * K by ring, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (by omega)]
        omega
      rw [gL, if_neg e3, frobPush_zero, mul_zero]
    · intro hn
      exact absurd (Finset.mem_range.mpr (by omega)) hn

/-- **R-053 upper bound, level form**: `mu ≡ sum_{z < p K} zeta ^ z * E_p(g_z) (mod p ^ k)` with `g_z = 0`
unless `p ∣ z + 1`, whenever `k ≤ K + v_p(K!)`. -/
theorem tower_levels (k K : ℕ) (hK : k ≤ K + padicValNat p K !) :
    ∃ g : ℕ → AF, (∀ z, (z + 1) % p ≠ 0 → g z = 0) ∧
      Cong (p ^ k) (μ : AF) (∑ z ∈ Finset.range (p * K), (ζ : AF) ^ z * frobPush p (g z)) := by
  obtain ⟨h, hh⟩ := tower_upper p k K hK
  exact ⟨gL p h, fun z hz => by rw [gL, if_neg hz], by rw [levels_reindex]; exact hh⟩

/-- **R-053 exactly** (with r4l's `level_bound_K`): for `k ≥ 1` and `K = K(p,k)` the least `K` with
`K + v_p(K!) ≥ k`, levels `z ≤ p K - 1` suffice, and every identity with levels `z ≤ L` has `L + 1 ≥ p K`.
So the least `L` is `L(p,k) = p K(p,k) - 1`. -/
theorem levels_sharp (k : ℕ) (hk : 1 ≤ k) :
    (∃ g : ℕ → AF, Cong (p ^ k) (μ : AF)
      (∑ z ∈ Finset.range (p * Nat.find (exists_K p k) - 1 + 1), (ζ : AF) ^ z * frobPush p (g z))) ∧
    ∀ (L : ℕ) (g : ℕ → AF), Cong (p ^ k) (μ : AF)
      (∑ z ∈ Finset.range (L + 1), (ζ : AF) ^ z * frobPush p (g z)) →
        p * Nat.find (exists_K p k) ≤ L + 1 := by
  have hK0 : 1 ≤ Nat.find (exists_K p k) := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    have := Nat.find_spec (exists_K p k)
    rw [h0] at this
    simp at this
    omega
  refine ⟨?_, fun L g hg => level_bound_K p k L _ g hg (fun K' hK' => ?_)⟩
  · obtain ⟨g, -, hg⟩ := tower_levels p k _ (Nat.find_spec (exists_K p k))
    refine ⟨g, ?_⟩
    rwa [Nat.sub_add_cancel (Nat.mul_pos hp.out.pos hK0)]
  · have := Nat.find_min (exists_K p k) hK'
    omega

end TowerMain

end FrobCong

open FrobCong in
#print axioms tval_tT
open FrobCong in
#print axioms VL_digits
open FrobCong in
#print axioms tower_upper
open FrobCong in
#print axioms tower_upper_min
open FrobCong in
#print axioms tower_levels
open FrobCong in
#print axioms levels_sharp

/-! ## Kempner identification (r5n, brief P6, seat PR-O6)

The Kempner value `S(p ^ k)` is the least `N` with `p ^ k ∣ N!`. By Legendre,
`v_p((p K)!) = K + v_p(K!)`, and `v_p(N!) = v_p((p (N / p))!)` (constant on blocks of length `p`),
so the least such `N` is a multiple of `p`, namely `p K(p,k)` (note, Section 4, eq. (4.2)).
Hence the exact level count of R-053 is `L(p,k) = S(p ^ k) - 1`. -/

namespace FrobCong

open scoped Nat

section Kempner

local notation "AF" => ArithmeticFunction ℤ

variable (p : ℕ) [hp : Fact p.Prime]

theorem exists_kempner (k : ℕ) : ∃ N, p ^ k ∣ N ! :=
  ⟨p ^ k, Nat.dvd_factorial (pow_pos hp.out.pos k) le_rfl⟩

/-- The Kempner value `S(p ^ k)`: the least `N` with `p ^ k ∣ N!`. -/
noncomputable def kempner (k : ℕ) : ℕ := Nat.find (exists_kempner p k)

theorem pow_dvd_factorial_iff (k N : ℕ) : p ^ k ∣ N ! ↔ k ≤ padicValNat p N ! :=
  padicValNat_dvd_iff_le (Nat.factorial_ne_zero N)

/-- Legendre at multiples of `p`: `v_p((p K)!) = K + v_p(K!)`. -/
theorem padicValNat_factorial_p_mul (K : ℕ) :
    padicValNat p (p * K) ! = K + padicValNat p K ! := by
  rw [padicValNat_factorial_mul, add_comm]

/-- `v_p(N!)` is constant on each block `[p K, p K + p - 1]`. -/
theorem padicValNat_factorial_floor (N : ℕ) :
    padicValNat p N ! = padicValNat p (p * (N / p)) ! :=
  (padicValNat_mul_div_factorial N).symm

/-- `p ^ k ∣ (p K)!` exactly when `k ≤ K + v_p(K!)`. -/
theorem pow_dvd_factorial_p_mul_iff (k K : ℕ) :
    p ^ k ∣ (p * K) ! ↔ k ≤ K + padicValNat p K ! := by
  rw [pow_dvd_factorial_iff, padicValNat_factorial_p_mul]

/-- **Kempner identification** (note, Section 4, eq. (4.2)): `p K(p,k) = S(p ^ k)`, the least `N`
with `p ^ k ∣ N!`. Holds for every `k` (both sides are `0` at `k = 0`). -/
theorem kempner_eq (k : ℕ) : p * Nat.find (exists_K p k) = kempner p k := by
  apply le_antisymm
  · -- `S = S(p^k)` has `k ≤ v_p(S!) = v_p((p (S / p))!) = S / p + v_p((S / p)!)`, so `K ≤ S / p`.
    have hS := Nat.find_spec (exists_kempner p k)
    rw [pow_dvd_factorial_iff, padicValNat_factorial_floor, padicValNat_factorial_p_mul] at hS
    have hK : Nat.find (exists_K p k) ≤ kempner p k / p := Nat.find_min' _ hS
    calc p * Nat.find (exists_K p k) ≤ p * (kempner p k / p) := Nat.mul_le_mul_left p hK
      _ ≤ kempner p k := Nat.mul_div_le _ _
  · -- `p K` itself is a witness: `p ^ k ∣ (p K)!`.
    exact Nat.find_min' _ ((pow_dvd_factorial_p_mul_iff p k _).mpr (Nat.find_spec (exists_K p k)))

/-- `S(p ^ k)` is the threshold: `p ^ k ∣ N!` exactly when `S(p ^ k) ≤ N`. -/
theorem pow_dvd_factorial_iff_kempner_le (k N : ℕ) : p ^ k ∣ N ! ↔ kempner p k ≤ N := by
  constructor
  · exact fun h => Nat.find_min' _ h
  · intro h
    exact (Nat.find_spec (exists_kempner p k)).trans (Nat.factorial_dvd_factorial h)

/-- For `k ≥ 1`, `S(p ^ k) ≥ p` (so `S(p ^ k) - 1 + 1 = S(p ^ k)`). -/
theorem p_le_kempner (k : ℕ) (hk : 1 ≤ k) : p ≤ kempner p k := by
  have hK0 : 1 ≤ Nat.find (exists_K p k) := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    have := Nat.find_spec (exists_K p k)
    rw [h0] at this
    simp at this
    omega
  rw [← kempner_eq]
  exact Nat.le_mul_of_pos_right p hK0

/-- **R-053 exactly, Kempner form**: for `k ≥ 1`, levels `z ≤ S(p ^ k) - 1` suffice, and every identity
`mu ≡ sum_{z ≤ L} zeta ^ z * E_p(g_z) (mod p ^ k)` has `L + 1 ≥ S(p ^ k)`.
So the least `L` is `L(p,k) = S(p ^ k) - 1`. -/
theorem levels_sharp_kempner (k : ℕ) (hk : 1 ≤ k) :
    (∃ g : ℕ → AF, Cong (p ^ k) (μ : AF)
      (∑ z ∈ Finset.range (kempner p k - 1 + 1), (ζ : AF) ^ z * frobPush p (g z))) ∧
    ∀ (L : ℕ) (g : ℕ → AF), Cong (p ^ k) (μ : AF)
      (∑ z ∈ Finset.range (L + 1), (ζ : AF) ^ z * frobPush p (g z)) →
        kempner p k ≤ L + 1 := by
  rw [← kempner_eq]
  exact levels_sharp p k hk

/-- The same, with the top level written as `S(p ^ k)` levels `z < S(p ^ k)` (no truncated subtraction). -/
theorem levels_kempner_range (k : ℕ) :
    ∃ g : ℕ → AF, Cong (p ^ k) (μ : AF)
      (∑ z ∈ Finset.range (kempner p k), (ζ : AF) ^ z * frobPush p (g z)) := by
  obtain ⟨g, -, hg⟩ := tower_levels p k _ (Nat.find_spec (exists_K p k))
  exact ⟨g, by rwa [← kempner_eq]⟩

end Kempner

end FrobCong

open FrobCong in
#print axioms kempner_eq
open FrobCong in
#print axioms pow_dvd_factorial_iff_kempner_le
open FrobCong in
#print axioms p_le_kempner
open FrobCong in
#print axioms levels_sharp_kempner
open FrobCong in
#print axioms levels_kempner_range
