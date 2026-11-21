module

/-
Run r25, seat L3: the Dirichlet ring with the Frobenius push `E_p`, and the transfer to power
series in finitely many variables (one per prime), ledger R-084.

Contents.
1. `frobPush p` (`E_p`, copied from FrobLib/Frob3.lean, namespace FrobCong, 31 Oct, with its
   proofs) as a ring endomorphism `Ep p` of `ArithmeticFunction R`; the coefficient map `mapHom`.
2. `ep_isFrobLift`: `E_p` is a Frobenius lift of `ArithmeticFunction R` for every commutative ring
   `R` with `p ∣ a ^ p - a` (so `R = ℤ`, `ℤ_[p]`). The characteristic `p` congruence
   `frob_apply` is FrobLib's, copied.
3. Smooth numbers: for distinct primes `q_0, ..., q_(n-1)`, `smoothNum q e = ∏ q_i ^ e_i`.
4. `res q`: restriction to `{q_i}`-smooth arguments, a ring hom
   `ArithmeticFunction R →+* MvPowerSeries (Fin n) R` (Cashwell-Everett), with
   `res (E_p g) = frob p (res g)` (`res_Ep`).
5. Transfer: a ring hom commuting with the lifts carries level identities (`HasLevel.map`), so
   the level count can only drop (`levelCount_map_le`).

Lean v4.33.1 with Mathlib; imports seat L1's oleans (Found, Upper). No sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper

@[expose] public section

namespace FrobLevel

namespace Dir

open Finset

section Push

variable {R : Type*} [CommRing R]

/-- `E_p`: `frobPush p f (j ^ p) = f j`, and `0` off the `p`-th powers (FrobLib's definition). -/
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

theorem frobPush_apply_zero {p : ℕ} (f : ArithmeticFunction R) : frobPush p f 0 = 0 := by
  rw [frobPush_apply]; simp

theorem frobPush_mul {p : ℕ} (hp0 : p ≠ 0) (f g : ArithmeticFunction R) :
    frobPush p (f * g) = frobPush p f * frobPush p g := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [frobPush_apply_zero, ArithmeticFunction.map_zero]
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
  rw [ArithmeticFunction.mul_apply]
  by_cases hex : ∃ m, m ^ p = n
  · obtain ⟨m, rfl⟩ := hex
    have hm : m ≠ 0 := by rintro rfl; exact hn (zero_pow hp0)
    rw [frobPush_apply_pow hp0 _ hm, ArithmeticFunction.mul_apply]
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

theorem frobPush_one {p : ℕ} (hp0 : p ≠ 0) : frobPush p (1 : ArithmeticFunction R) = 1 := by
  ext n
  by_cases hex : ∃ m, m ^ p = n
  · obtain ⟨m, rfl⟩ := hex
    rcases eq_or_ne m 0 with rfl | hm
    · rw [zero_pow hp0, frobPush_apply_zero]; rfl
    rw [frobPush_apply_pow hp0 _ hm, ArithmeticFunction.one_apply, ArithmeticFunction.one_apply]
    by_cases h1 : m = 1
    · subst h1; simp
    · rw [if_neg h1, if_neg]
      intro h
      rcases (pow_eq_one_iff).mp h with h' | h'
      · exact h1 h'
      · exact hp0 h'
  · rw [frobPush_apply_of_not _ hex, ArithmeticFunction.one_apply, if_neg]
    rintro rfl; exact hex ⟨1, one_pow p⟩

theorem frobPush_add {p : ℕ} (f g : ArithmeticFunction R) :
    frobPush p (f + g) = frobPush p f + frobPush p g := by
  ext n
  rw [ArithmeticFunction.add_apply, frobPush_apply, frobPush_apply, frobPush_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp

/-- `E_p` as a ring endomorphism of the Dirichlet ring. -/
def Ep (p : ℕ) [hp : Fact p.Prime] : ArithmeticFunction R →+* ArithmeticFunction R where
  toFun := frobPush p
  map_one' := frobPush_one hp.out.ne_zero
  map_mul' := frobPush_mul hp.out.ne_zero
  map_zero' := by ext n; simp [frobPush_apply]
  map_add' := frobPush_add

theorem Ep_apply (p : ℕ) [Fact p.Prime] (f : ArithmeticFunction R) : Ep p f = frobPush p f := rfl

/-- Reduction of values along a ring hom, as a ring hom of Dirichlet rings. -/
def mapHom {S : Type*} [CommRing S] (φ : R →+* S) : ArithmeticFunction R →+* ArithmeticFunction S where
  toFun f := ⟨fun n => φ (f n), by simp⟩
  map_one' := by
    ext n
    show φ ((1 : ArithmeticFunction R) n) = (1 : ArithmeticFunction S) n
    rw [ArithmeticFunction.one_apply, ArithmeticFunction.one_apply]
    split_ifs <;> simp
  map_mul' f g := by
    ext n
    show φ ((f * g) n) = ∑ x ∈ n.divisorsAntidiagonal, φ (f x.1) * φ (g x.2)
    rw [ArithmeticFunction.mul_apply, map_sum]
    simp only [map_mul]
  map_zero' := by ext n; show φ ((0 : ArithmeticFunction R) n) = 0; simp
  map_add' f g := by
    ext n
    show φ ((f + g) n) = φ (f n) + φ (g n)
    rw [ArithmeticFunction.add_apply, map_add]

theorem mapHom_apply {S : Type*} [CommRing S] (φ : R →+* S) (f : ArithmeticFunction R) (n : ℕ) :
    mapHom φ f n = φ (f n) := rfl

theorem mapHom_frobPush {S : Type*} [CommRing S] (φ : R →+* S) (p : ℕ) (f : ArithmeticFunction R) :
    mapHom φ (frobPush p f) = frobPush p (mapHom φ f) := by
  ext n
  rw [mapHom_apply, frobPush_apply, frobPush_apply, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp [mapHom_apply]

/-- The constant `m` acts on values: `(m * D) n = m * D n`. -/
theorem natCast_mul_apply (m : ℕ) (D : ArithmeticFunction R) (n : ℕ) :
    ((m : ArithmeticFunction R) * D) n = (m : R) * D n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply, Finset.sum_eq_single (1, n)]
  · show (if (1 : ℕ) = 1 then (m : R) else 0) * D n = _
    rw [if_pos rfl]
  · intro x hx hne
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have h1 : x.1 ≠ 1 := by
      intro h
      apply hne
      refine Prod.ext h ?_
      show x.2 = n
      rw [← hx'.1, h, one_mul]
    show (if x.1 = 1 then (m : R) else 0) * D x.2 = 0
    rw [if_neg h1, zero_mul]
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul n, hn⟩) h

theorem sub_apply' (A B : ArithmeticFunction R) (n : ℕ) : (A - B) n = A n - B n := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, ← sub_eq_add_neg]

theorem natCast_apply_one (m : ℕ) : (m : ArithmeticFunction R) 1 = (m : R) := by
  have := natCast_mul_apply m (1 : ArithmeticFunction R) 1
  rwa [mul_one, ArithmeticFunction.one_one, mul_one] at this

theorem pow_apply_one (f : ArithmeticFunction R) (k : ℕ) : (f ^ k) 1 = f 1 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ArithmeticFunction.mul_apply_one, ih, pow_succ]

/-- Coefficientwise divisibility by `m` is divisibility by `m` in the Dirichlet ring. -/
theorem natCast_dvd_of_apply {m : ℕ} {D : ArithmeticFunction R} (h : ∀ n, (m : R) ∣ D n) :
    (m : ArithmeticFunction R) ∣ D := by
  choose c hc using h
  let c' : ArithmeticFunction R := ⟨fun n => if n = 0 then 0 else c n, by simp⟩
  refine ⟨c', ?_⟩
  ext n
  rw [natCast_mul_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · show D n = (m : R) * (if n = 0 then 0 else c n)
    rw [if_neg hn, ← hc n]

end Push

/-! ## 2. The Frobenius congruence (FrobLib's `frob_apply`, copied) and `IsFrobLift` -/

section Congruence

variable {R : Type*} [CommRing R]

/-- The point function with value `c` at `d`. -/
def pt (d : ℕ) (c : R) : ArithmeticFunction R :=
  ⟨fun m => if m = d ∧ d ≠ 0 then c else 0, by
    rw [if_neg]; rintro ⟨h1, h2⟩; exact h2 h1.symm⟩

theorem pt_apply (d : ℕ) (c : R) (m : ℕ) :
    pt d c m = if m = d ∧ d ≠ 0 then c else 0 := rfl

theorem pt_mul (a b : ℕ) (c e : R) : pt a c * pt b e = pt (a * b) (c * e) := by
  ext m
  rw [ArithmeticFunction.mul_apply]
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
  rw [pt_apply, ArithmeticFunction.one_apply]
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

theorem pow_apply_congr {f g : ArithmeticFunction R} {n : ℕ}
    (h : ∀ m ∈ n.divisors, f m = g m) (k : ℕ) :
    ∀ m ∈ n.divisors, (f ^ k) m = (g ^ k) m := by
  induction k with
  | zero => intro m _; simp
  | succ k ih =>
    intro m hm
    rw [pow_succ, pow_succ, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    apply Finset.sum_congr rfl
    intro x hx
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have hn := Nat.ne_zero_of_mem_divisors hm
    have hmn := Nat.dvd_of_mem_divisors hm
    rw [ih x.1 ?_, h x.2 ?_]
    · exact Nat.mem_divisors.mpr ⟨(Dvd.intro_left _ hx'.1).trans hmn, hn⟩
    · exact Nat.mem_divisors.mpr ⟨(Dvd.intro _ hx'.1).trans hmn, hn⟩

theorem charP_arith (p : ℕ) [CharP R p] : CharP (ArithmeticFunction R) p :=
  charP_of_injective_algebraMap (R := R) (A := ArithmeticFunction R) (fun x y hxy => by
    have := congrArg (fun f : ArithmeticFunction R => f 1) hxy
    simpa using this) p

/-- Frobenius congruence (FrobLib): in characteristic `p`,
`(f ^ p) n = ∑_{d ∣ n, d ^ p = n} (f d) ^ p`. -/
theorem frob_apply' (p : ℕ) [Fact p.Prime] [CharP R p] (f : ArithmeticFunction R) (n : ℕ) :
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

/-- **`E_p` is a Frobenius lift of the Dirichlet ring** over every commutative ring `R` with
`p ∣ a ^ p - a` for all `a` (for example `ℤ` and `ℤ_[p]`): `E_p f ≡ f ^ p` modulo `p`. -/
theorem ep_isFrobLift (p : ℕ) [hp : Fact p.Prime] (hR : ∀ a : R, (p : R) ∣ a ^ p - a) :
    IsFrobLift p (Ep p : ArithmeticFunction R →+* ArithmeticFunction R) := by
  intro f
  by_cases hu : IsUnit (p : R)
  · have : IsUnit (p : ArithmeticFunction R) := by
      rw [ArithmeticFunction.isUnit_iff_isUnit_apply_one, natCast_apply_one]; exact hu
    exact this.dvd
  apply natCast_dvd_of_apply
  intro n
  have := CharP.quotient R p (mem_nonunits_iff.mpr hu)
  set π := Ideal.Quotient.mk (Ideal.span ({(p : R)} : Set R)) with hπ
  have key : ∀ r : R, (p : R) ∣ r ↔ π r = 0 := fun r => by
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hfrob : ∀ a : R, π a ^ p = π a := fun a => by
    have := (key _).1 (hR a); rwa [map_sub, sub_eq_zero, map_pow] at this
  rw [key, sub_apply', map_sub, sub_eq_zero]
  have h1 : π ((Ep p f) n) = frobPush p (mapHom π f) n := by
    rw [← mapHom_frobPush]; rfl
  have h2 : π ((f ^ p) n) = ((mapHom π f) ^ p) n := by
    rw [← map_pow]; rfl
  rw [h1, h2, frob_apply' p, frobPush_apply]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs
  · rw [mapHom_apply, hfrob]
  · rfl

end Congruence

/-! ## 3. Smooth numbers for finitely many distinct primes -/

section Smooth

variable {n : ℕ} (q : Fin n → ℕ)

/-- `∏ q_i ^ e_i`. -/
def smoothNum (e : Fin n →₀ ℕ) : ℕ := ∏ i, q i ^ e i

/-- The exponent vector `(v_(q_i)(N))_i`. -/
noncomputable def expOf (N : ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => N.factorization (q i))

theorem expOf_apply (N : ℕ) (i : Fin n) : expOf q N i = N.factorization (q i) := rfl

variable {q} (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)
include hq

theorem smoothNum_ne_zero (e : Fin n →₀ ℕ) : smoothNum q e ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hq i).ne_zero

omit hq in
theorem smoothNum_add (e₁ e₂ : Fin n →₀ ℕ) :
    smoothNum q (e₁ + e₂) = smoothNum q e₁ * smoothNum q e₂ := by
  simp only [smoothNum, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]

omit hq in
theorem smoothNum_zero : smoothNum q 0 = 1 := by simp [smoothNum]

omit hq in
theorem smoothNum_smul (p : ℕ) (e : Fin n →₀ ℕ) : smoothNum q (p • e) = smoothNum q e ^ p := by
  simp only [smoothNum, Finsupp.smul_apply, smul_eq_mul, ← Finset.prod_pow, ← pow_mul, mul_comm]

omit hq in
theorem smoothNum_single (i : Fin n) : smoothNum q (Finsupp.single i 1) = q i := by
  rw [smoothNum, Finset.prod_eq_single i]
  · simp
  · intro j _ hj; rw [Finsupp.single_apply, if_neg (Ne.symm hj), pow_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem factorization_smoothNum (e : Fin n →₀ ℕ) (r : ℕ) :
    (smoothNum q e).factorization r = ∑ i, if q i = r then e i else 0 := by
  rw [smoothNum, Nat.factorization_prod (fun i _ => pow_ne_zero _ (hq i).ne_zero),
    Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hq i).factorization_pow, Finsupp.single_apply]

include hinj in
theorem factorization_smoothNum_q (e : Fin n →₀ ℕ) (j : Fin n) :
    (smoothNum q e).factorization (q j) = e j := by
  rw [factorization_smoothNum hq, Finset.sum_eq_single j]
  · rw [if_pos rfl]
  · intro i _ hij; rw [if_neg (fun h => hij (hinj h))]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem factorization_smoothNum_of_notMem (e : Fin n →₀ ℕ) {r : ℕ} (hr : ∀ i, q i ≠ r) :
    (smoothNum q e).factorization r = 0 := by
  rw [factorization_smoothNum hq]
  exact Finset.sum_eq_zero fun i _ => if_neg (hr i)

include hinj in
theorem expOf_smoothNum (e : Fin n →₀ ℕ) : expOf q (smoothNum q e) = e := by
  ext j; rw [expOf_apply, factorization_smoothNum_q hq hinj]

include hinj in
theorem smoothNum_injective : Function.Injective (smoothNum q) := fun e₁ e₂ h => by
  rw [← expOf_smoothNum hq hinj e₁, h, expOf_smoothNum hq hinj]

include hinj in
/-- Every divisor of a smooth number is the smooth number of its exponent vector. -/
theorem smoothNum_expOf_of_dvd {a : ℕ} {e : Fin n →₀ ℕ} (ha : a ∣ smoothNum q e) :
    smoothNum q (expOf q a) = a := by
  have hN := smoothNum_ne_zero hq e
  have ha0 : a ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd ha)
  apply Nat.eq_of_factorization_eq (smoothNum_ne_zero hq _) ha0
  intro r
  by_cases hr : ∃ j, q j = r
  · obtain ⟨j, rfl⟩ := hr
    rw [factorization_smoothNum_q hq hinj, expOf_apply]
  · push Not at hr
    rw [factorization_smoothNum_of_notMem hq _ hr]
    have hle := (Nat.factorization_le_iff_dvd ha0 hN).2 ha r
    rw [factorization_smoothNum_of_notMem hq _ hr] at hle
    omega

omit hq in
omit hq in
theorem expOf_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    expOf q (a * b) = expOf q a + expOf q b := by
  ext j
  rw [Finsupp.add_apply, expOf_apply, expOf_apply, expOf_apply, Nat.factorization_mul ha hb,
    Finsupp.add_apply]

end Smooth

/-! ## 4. Restriction to smooth arguments: the Dirichlet ring maps to power series -/

section Restriction

variable {R : Type*} [CommRing R] {n : ℕ} {q : Fin n → ℕ}

open MvPowerSeries

/-- The underlying power series of the restriction of `g` to `{q_i}`-smooth arguments. -/
def resFun (q : Fin n → ℕ) (g : ArithmeticFunction R) : MvPowerSeries (Fin n) R :=
  fun e => g (smoothNum q e)

theorem coeff_resFun (q : Fin n → ℕ) (g : ArithmeticFunction R) (e : Fin n →₀ ℕ) :
    coeff e (resFun q g) = g (smoothNum q e) := rfl

variable (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)
include hq hinj

theorem resFun_mul (f g : ArithmeticFunction R) :
    resFun q (f * g) = resFun q f * resFun q g := by
  classical
  ext e
  rw [coeff_resFun, ArithmeticFunction.mul_apply, coeff_mul]
  symm
  refine Finset.sum_nbij' (fun x => (smoothNum q x.1, smoothNum q x.2))
    (fun y => (expOf q y.1, expOf q y.2)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    refine Nat.mem_divisorsAntidiagonal.mpr ?_
    exact ⟨by rw [← smoothNum_add, hx'], smoothNum_ne_zero hq e⟩
  · intro y hy
    have hy := Nat.mem_divisorsAntidiagonal.mp hy
    refine Finset.HasAntidiagonal.mem_antidiagonal.mpr ?_
    have h1 : y.1 ≠ 0 := left_ne_zero_of_mul (hy.1 ▸ hy.2)
    have h2 : y.2 ≠ 0 := right_ne_zero_of_mul (hy.1 ▸ hy.2)
    rw [← expOf_mul h1 h2, hy.1, expOf_smoothNum hq hinj]
  · intro x _
    simp only [expOf_smoothNum hq hinj]
  · intro y hy
    have hy := Nat.mem_divisorsAntidiagonal.mp hy
    have hd1 : y.1 ∣ smoothNum q e := ⟨y.2, hy.1.symm⟩
    have hd2 : y.2 ∣ smoothNum q e := ⟨y.1, by rw [mul_comm]; exact hy.1.symm⟩
    simp only [smoothNum_expOf_of_dvd hq hinj hd1, smoothNum_expOf_of_dvd hq hinj hd2]
  · intro x _
    rfl

/-- **Restriction** to `{q_i}`-smooth arguments, a ring hom from the Dirichlet ring to
`R[[x_0, ..., x_(n-1)]]` (`x_i` stands for the prime `q_i`). -/
def res : ArithmeticFunction R →+* MvPowerSeries (Fin n) R where
  toFun := resFun q
  map_one' := by
    classical
    ext e
    rw [coeff_resFun, coeff_one, ArithmeticFunction.one_apply]
    have : smoothNum q e = 1 ↔ e = 0 := by
      rw [← smoothNum_zero (q := q)]; exact (smoothNum_injective hq hinj).eq_iff
    by_cases h : e = 0
    · rw [if_pos (this.2 h), if_pos h]
    · rw [if_neg (fun h' => h (this.1 h')), if_neg h]
  map_mul' := resFun_mul hq hinj
  map_zero' := by ext e; rw [coeff_resFun]; simp
  map_add' f g := by ext e; rw [map_add, coeff_resFun, coeff_resFun, coeff_resFun]; rfl

theorem coeff_res (g : ArithmeticFunction R) (e : Fin n →₀ ℕ) :
    coeff e (res hq hinj g) = g (smoothNum q e) := rfl

/-- **The restriction commutes with the lifts**: `res (E_p g) = frob p (res g)`. -/
theorem res_Ep (p : ℕ) [hp : Fact p.Prime] (g : ArithmeticFunction R) :
    res hq hinj (Ep p g) = frob p (res hq hinj g) := by
  ext e
  rw [coeff_res, Ep_apply]
  by_cases hdiv : ∀ i, p ∣ e i
  · set e' : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => e i / p) with he'
    have hee : p • e' = e := by
      ext i
      rw [Finsupp.smul_apply, smul_eq_mul, he', Finsupp.equivFunOnFinite_symm_apply_apply,
        Nat.mul_div_cancel' (hdiv i)]
    rw [← hee, coeff_frob_smul, smoothNum_smul, frobPush_apply_pow hp.out.ne_zero _
      (smoothNum_ne_zero hq e'), coeff_res]
  · push Not at hdiv
    obtain ⟨i, hi⟩ := hdiv
    rw [coeff_frob_of_not_dvd p _ hi, frobPush_apply_of_not]
    rintro ⟨j, hj⟩
    apply hi
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact smoothNum_ne_zero hq e (by rw [← hj, zero_pow hp.out.ne_zero])
    have := congrArg (fun N => N.factorization (q i)) hj
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      factorization_smoothNum_q hq hinj] at this
    exact ⟨_, this.symm⟩

end Restriction

/-! ## 5. Transfer of level identities along ring homs commuting with the lifts -/

section Transfer

variable {A A' : Type*} [CommRing A] [CommRing A']

/-- A ring hom `φ` with `φ ∘ σ = σ' ∘ φ` carries a level-`L` identity of `f` to one of `φ f`. -/
theorem HasLevel.map (φ : A →+* A') {σ : A →+* A} {σ' : A' →+* A'}
    (hφ : ∀ a, φ (σ a) = σ' (φ a)) {p : ℕ} {f : A} {k L : ℕ} (h : HasLevel p σ f k L) :
    HasLevel p σ' (φ f) k L := by
  obtain ⟨g, hg⟩ := h
  refine ⟨fun z => φ (g z), ?_⟩
  have := map_dvd φ hg
  simpa only [map_sub, map_mul, map_sum, map_pow, map_natCast, map_one, hφ] using this

/-- **Transfer lemma.** If `f` has some level identity, the level count of `φ f` is at most that
of `f`. -/
theorem levelCount_map_le (φ : A →+* A') {σ : A →+* A} {σ' : A' →+* A'}
    (hφ : ∀ a, φ (σ a) = σ' (φ a)) {p : ℕ} {f : A} {k L : ℕ} (hex : HasLevel p σ f k L) :
    levelCount p σ' (φ f) k ≤ levelCount p σ f k :=
  levelCount_le (HasLevel.map φ hφ (hasLevel_levelCount hex))

end Transfer

end Dir

end FrobLevel
