module

/-
Run r25, seat L1: R-080 stage (c) and the lower half of stage (d), by a trace argument over
`ℤ[ζ_p]` (this replaces the p-independence / Moore determinant route; see INDEX.md).

Core (`core_bound`): `O` a domain with a primitive `p`-th root of unity `ζ`, `π = ζ - 1` prime,
`π ^ (p - 1)` associated to `p`. Let `G = (Fin n → Fin p)` act on `O[[x_1..x_n]]` by the twists
`tw g : x_i ↦ ζ ^ (g i) x_i`; they fix `B = σ(O[[x]])` coefficientwise. If `u` satisfies
`(hu)`: for every `h ≠ 0` some monomial `x ^ m` of `u` has `π ∤ u_m` and `p ∤ ∑ h_i m_i`,
then every monic `P ∈ B[X]` of degree `p ^ n - 1` with `p ^ k ∣ P(u)` has `(p - 1)(k + n) < p ^ n`.
Proof: Lagrange at the `p ^ n` points `tw g u` (cleared of denominators), `P(tw g u) = tw g P(u)`,
`tw g u - tw (g + h) u = π · tw g (E_h)` with `E_h ≢ 0 (mod π)`, the trace `∑_g tw g` is divisible
by `p ^ n`, and comparison of powers of `π` modulo the prime `π`.

Consequences: with the δ-tower of degree `p ^ n - 1 - m` and Legendre (`legendre_split`), a monic
annihilator of `u = ∏ (1 - x_i)` of degree `m < p ^ n` modulo `p ^ k` forces `S(p ^ k) ≤ m`
(`kempner_le_of_monicAnn_int`, `..._padic`), and so
`L(ζ_n; p, k) + 1 = min (p ^ n) (S(p ^ k))` over `ℤ` and over `ℤ_[p]` (`levelCount_zeta_int`,
`levelCount_zeta_padic`): ledger R-080 (C), R-060 closed, for every `n`, `p`, `k ≥ 1`.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper

@[expose] public section

namespace FrobLevel

open MvPowerSeries

/-! ## 1. Twists -/

section Twist

variable {O : Type*} [CommRing O] {n p : ℕ}

/-- The twist `x_i ↦ ζ ^ (g i) x_i` of `O[[x_1..x_n]]`. -/
noncomputable def tw (ζ : O) (g : Fin n → Fin p) :
    MvPowerSeries (Fin n) O →+* MvPowerSeries (Fin n) O :=
  rescale fun i => ζ ^ (g i : ℕ)

theorem coeff_tw (ζ : O) (g : Fin n → Fin p) (f : MvPowerSeries (Fin n) O) (m : Fin n →₀ ℕ) :
    coeff m (tw ζ g f) = ζ ^ (∑ i, (g i : ℕ) * m i) * coeff m f := by
  rw [tw, coeff_rescale, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    ← Finset.prod_pow_eq_pow_sum]
  congr 1
  exact Finset.prod_congr rfl fun i _ => (pow_mul ζ _ _).symm

theorem pow_mod_of_pow_eq_one {ζ : O} (hζ : ζ ^ p = 1) (a : ℕ) : ζ ^ (a % p) = ζ ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a p, pow_add, pow_mul, hζ, one_pow, mul_one]

theorem tw_tw {ζ : O} (hζ : ζ ^ p = 1) (g h : Fin n → Fin p) (f : MvPowerSeries (Fin n) O) :
    tw ζ g (tw ζ h f) = tw ζ (g + h) f := by
  have e : ((fun i => ζ ^ (h i : ℕ)) * fun i => ζ ^ (g i : ℕ)) = fun i => ζ ^ ((g + h) i : ℕ) := by
    funext i
    simp only [Pi.mul_apply, Pi.add_apply, Fin.val_add, ← pow_add, pow_mod_of_pow_eq_one hζ,
      add_comm]
  simp only [tw]
  rw [rescale_rescale, e]

theorem tw_zero [NeZero p] (ζ : O) (f : MvPowerSeries (Fin n) O) :
    tw ζ (0 : Fin n → Fin p) f = f := by
  have : (fun i : Fin n => ζ ^ (((0 : Fin n → Fin p) i : Fin p) : ℕ)) = 1 := by
    funext i; simp
  rw [tw, this, rescale_one, RingHom.id_apply]

theorem tw_C (ζ : O) (g : Fin n → Fin p) (c : O) : tw ζ g (C c) = C c := by
  ext m
  rw [coeff_tw, coeff_C]
  split_ifs with h
  · subst h; simp
  · rw [mul_zero]

theorem tw_frob [Fact p.Prime] {ζ : O} (hζ : ζ ^ p = 1) (g : Fin n → Fin p)
    (f : MvPowerSeries (Fin n) O) : tw ζ g (frob p f) = frob p f := by
  ext m
  rw [coeff_tw]
  by_cases h : ∀ i, p ∣ m i
  · obtain ⟨c, hc⟩ : p ∣ ∑ i, (g i : ℕ) * m i :=
      Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (h i) _
    rw [hc, pow_mul, hζ, one_pow, one_mul]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [coeff_frob_of_not_dvd p f hi, mul_zero]

/-- Polynomials over `B` commute with the twists. -/
theorem eval_tw [Fact p.Prime] {ζ : O} (hζ : ζ ^ p = 1) {P : Polynomial (MvPowerSeries (Fin n) O)}
    (hB : P ∈ BPoly (frob p)) (g : Fin n → Fin p) (x : MvPowerSeries (Fin n) O) :
    P.eval (tw ζ g x) = tw ζ g (P.eval x) := by
  have hmap : P.map (tw ζ g) = P := by
    refine Polynomial.ext fun i => ?_
    rw [Polynomial.coeff_map]
    obtain ⟨a, ha⟩ := mem_BPoly_iff.1 hB i
    rw [← ha]
    exact tw_frob hζ g a
  conv_lhs => rw [← hmap]
  rw [Polynomial.eval_map, Polynomial.eval₂_hom]

/-- Reduction modulo `π = ζ - 1`, coefficientwise. -/
noncomputable def resPi (ζ : O) :
    MvPowerSeries (Fin n) O →+* MvPowerSeries (Fin n) (O ⧸ Ideal.span {ζ - 1}) :=
  MvPowerSeries.map (Ideal.Quotient.mk _)

theorem mk_zeta (ζ : O) : Ideal.Quotient.mk (Ideal.span {ζ - 1}) ζ = 1 := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk (Ideal.span {ζ - 1})), ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

theorem resPi_tw (ζ : O) (g : Fin n → Fin p) (f : MvPowerSeries (Fin n) O) :
    resPi ζ (tw ζ g f) = resPi ζ f := by
  ext m
  rw [resPi, coeff_map, coeff_map, coeff_tw, map_mul, map_pow, mk_zeta, one_pow, one_mul]

theorem resPi_C_pi (ζ : O) : resPi ζ (C (ζ - 1) : MvPowerSeries (Fin n) O) = 0 := by
  have : Ideal.Quotient.mk (Ideal.span {ζ - 1}) (ζ - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))
  rw [resPi, map_C, this, map_zero]

/-- `∑_{a < p} (ζ ^ c) ^ a` is `p` or `0`, so it is divisible by `p`. -/
theorem natCast_dvd_geom [IsDomain O] {ζ : O} (hζ : IsPrimitiveRoot ζ p) (c : ℕ) :
    (p : O) ∣ ∑ a ∈ Finset.range p, (ζ ^ c) ^ a := by
  by_cases h : p ∣ c
  · obtain ⟨d, rfl⟩ := h
    rw [pow_mul, hζ.pow_eq_one, one_pow]
    simp
  · have hne : ζ ^ c ≠ 1 := fun h1 => h ((hζ.pow_eq_one_iff_dvd c).1 h1)
    have hpow : (ζ ^ c) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have : (∑ a ∈ Finset.range p, (ζ ^ c) ^ a) * (ζ ^ c - 1) = 0 := by
      rw [geom_sum_mul, hpow, sub_self]
    rw [(mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)]
    exact dvd_zero _

/-- The trace `∑_g tw g` is divisible by `p ^ n`. -/
theorem natCast_pow_dvd_sum_tw [IsDomain O] {ζ : O} (hζ : IsPrimitiveRoot ζ p)
    (w : MvPowerSeries (Fin n) O) :
    (p : MvPowerSeries (Fin n) O) ^ n ∣ ∑ g : Fin n → Fin p, tw ζ g w := by
  have key : ∀ m : Fin n →₀ ℕ, (p : O) ^ n ∣ ∑ g : Fin n → Fin p, ζ ^ (∑ i, (g i : ℕ) * m i) := by
    intro m
    have : ∑ g : Fin n → Fin p, ζ ^ (∑ i, (g i : ℕ) * m i)
        = ∏ i, ∑ a : Fin p, (ζ ^ m i) ^ (a : ℕ) := by
      rw [Fintype.prod_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]
    rw [this]
    have h1 : ∀ i, (p : O) ∣ ∑ a : Fin p, (ζ ^ m i) ^ (a : ℕ) := fun i => by
      rw [Fin.sum_univ_eq_sum_range (fun a => (ζ ^ m i) ^ a) p]
      exact natCast_dvd_geom hζ (m i)
    have h2 := Finset.prod_dvd_prod_of_dvd (s := Finset.univ) (fun _ => (p : O)) _ fun i _ => h1 i
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
  rw [← map_natCast (C (σ := Fin n) (R := O)), ← map_pow]
  apply C_dvd_of_coeff
  intro m
  rw [map_sum]
  simp_rw [coeff_tw]
  rw [← Finset.sum_mul]
  exact Dvd.dvd.mul_right (key m) _

end Twist

/-! ## 2. Lagrange interpolation, cleared of denominators -/

section Lagrange

open Polynomial

theorem prod_erase_translate {M : Type*} [CommMonoid M] {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (F : G → M) (g : G) :
    ∏ h ∈ Finset.univ.erase g, F h = ∏ h ∈ Finset.univ.erase (0 : G), F (g + h) := by
  refine Finset.prod_nbij' (fun h => h - g) (fun h => g + h) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_erase.2 ⟨sub_ne_zero.2 (Finset.mem_erase.1 ha).1, Finset.mem_univ _⟩
  · intro a ha
    exact Finset.mem_erase.2 ⟨fun e => (Finset.mem_erase.1 ha).1 (by simpa using e),
      Finset.mem_univ _⟩
  · intro a _; simp
  · intro a _; simp
  · intro a _; simp

/-- For `#ι` distinct points `z` of a domain and `Q` monic of degree `#ι - 1`:
`∏_g D_g = ∑_g Q(z_g) ∏_{g' ≠ g} D_{g'}` with `D_g = ∏_{h ≠ g} (z_g - z_h)`. -/
theorem lagrange_cleared {F : Type*} [CommRing F] [IsDomain F] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (z : ι → F) (hz : Function.Injective z) (Q : F[X]) (hQm : Q.Monic)
    (hQd : Q.natDegree + 1 = Fintype.card ι) :
    ∏ g, ∏ h ∈ Finset.univ.erase g, (z g - z h)
      = ∑ g, Q.eval (z g) * ∏ g' ∈ Finset.univ.erase g, ∏ h ∈ Finset.univ.erase g', (z g' - z h) := by
  set K := FractionRing F
  set φ := algebraMap F K
  have hinj : Function.Injective φ := IsFractionRing.injective F K
  set D : ι → F := fun g => ∏ h ∈ Finset.univ.erase g, (z g - z h) with hDdef
  have hD : ∀ g, D g ≠ 0 := fun g => Finset.prod_ne_zero_iff.2 fun h hh =>
    sub_ne_zero.2 fun e => (Finset.mem_erase.1 hh).1 (hz e).symm
  have hDK : ∀ g, φ (D g) ≠ 0 := fun g => (map_ne_zero_iff _ hinj).2 (hD g)
  have hvs : Set.InjOn (fun g => φ (z g)) (Finset.univ : Finset ι) :=
    fun a _ b _ e => hz (hinj e)
  have hdeg : (Q.map φ).degree < (Finset.univ : Finset ι).card := by
    rw [Finset.card_univ, ← hQd, degree_eq_natDegree (hQm.map φ).ne_zero, hQm.natDegree_map]
    exact_mod_cast Nat.lt_succ_self _
  have h1 := Lagrange.coeff_eq_sum hvs hdeg
  have hDi : ∀ i, ∏ j ∈ Finset.univ.erase i, ((fun g => φ (z g)) i - (fun g => φ (z g)) j)
      = φ (D i) := fun i => by simp [hDdef, map_prod, map_sub]
  simp only [hDi, eval_map, eval₂_hom] at h1
  rw [Finset.card_univ, ← hQd, Nat.add_sub_cancel, Polynomial.coeff_map, hQm.coeff_natDegree,
    map_one] at h1
  apply hinj
  rw [map_prod, map_sum]
  have h2 : ∏ g, φ (D g) = (∑ g, φ (Q.eval (z g)) / φ (D g)) * ∏ g, φ (D g) := by
    rw [← h1, one_mul]
  change ∏ g, φ (D g) = _
  rw [h2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_mul, map_prod φ D (Finset.univ.erase g),
    ← Finset.mul_prod_erase Finset.univ (fun g => φ (D g)) (Finset.mem_univ g),
    ← mul_assoc, div_mul_cancel₀ _ (hDK g)]

end Lagrange

/-! ## 3. The core bound -/

section Core

variable {O : Type*} [CommRing O] [IsDomain O] {n p : ℕ}

omit [IsDomain O] in
theorem constantCoeff_C_ne {c : O} (hc : c ≠ 0) : (C c : MvPowerSeries (Fin n) O) ≠ 0 := by
  intro h
  apply hc
  have := congrArg (constantCoeff (σ := Fin n) (R := O)) h
  rwa [constantCoeff_C, map_zero] at this

/-- `u - tw h u = π E_h`, and `E_h ≢ 0 (mod π)` when `h ≠ 0` and `u` satisfies `(hu)` at `h`. -/
theorem exists_E [hp : Fact p.Prime] {ζ : O} (hπ : Prime (ζ - 1)) (hπp : (ζ - 1) ∣ (p : O))
    (u : MvPowerSeries (Fin n) O) (h : Fin n → Fin p) :
    ∃ E, u - tw ζ h u = C (ζ - 1) * E ∧
      ∀ m : Fin n →₀ ℕ, ¬ p ∣ ∑ i, (h i : ℕ) * m i → ¬ (ζ - 1) ∣ coeff m u → resPi ζ E ≠ 0 := by
  have hcoef : ∀ m, coeff m (u - tw ζ h u) = - ((ζ ^ (∑ i, (h i : ℕ) * m i) - 1) * coeff m u) :=
    fun m => by rw [map_sub, coeff_tw]; ring
  have hsub : ∀ c : ℕ, (ζ - 1) ∣ ζ ^ c - 1 := fun c => by
    simpa using sub_dvd_pow_sub_pow ζ 1 c
  have hdvd : ∀ m, (ζ - 1) ∣ coeff m (u - tw ζ h u) := fun m => by
    rw [hcoef]; exact dvd_neg.2 (Dvd.dvd.mul_right (hsub _) _)
  obtain ⟨E, hE⟩ := C_dvd_of_coeff hdvd
  refine ⟨E, hE, fun m hm1 hm2 hzero => ?_⟩
  have hcm : Ideal.Quotient.mk (Ideal.span {ζ - 1}) (coeff m E) = 0 := by
    have := congrArg (coeff m) hzero
    rwa [resPi, coeff_map, map_zero] at this
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hcm
  set c := ∑ i, (h i : ℕ) * m i with hc
  have hs : (∑ j ∈ Finset.range c, ζ ^ j) * (ζ - 1) = ζ ^ c - 1 := geom_sum_mul ζ c
  have h1 : (ζ - 1) * coeff m E = (ζ - 1) * (-((∑ j ∈ Finset.range c, ζ ^ j) * coeff m u)) := by
    have := congrArg (coeff m) hE
    rw [hcoef, coeff_C_mul, ← hs] at this
    rw [← this]; ring
  have h2 := mul_left_cancel₀ hπ.ne_zero h1
  rw [h2, dvd_neg] at hcm
  rcases hπ.dvd_or_dvd hcm with h3 | h3
  · have h4 : (ζ - 1) ∣ (c : O) := by
      have : (c : O) = ∑ j ∈ Finset.range c, ζ ^ j - ∑ j ∈ Finset.range c, (ζ ^ j - 1) := by
        rw [Finset.sum_sub_distrib]; simp
      rw [this]
      exact dvd_sub h3 (Finset.dvd_sum fun j _ => hsub j)
    have hcop : IsCoprime (c : O) (p : O) := by
      have : IsCoprime (c : ℤ) (p : ℤ) :=
        Nat.isCoprime_iff_coprime.2 (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm1))
      simpa using this.map (Int.castRingHom O)
    exact hπ.not_isUnit (hcop.isUnit_of_dvd' h4 hπp)
  · exact hm2 h3

/-- The core bound. -/
theorem core_bound [hp : Fact p.Prime] {ζ : O} (hζ : IsPrimitiveRoot ζ p) (hπ : Prime (ζ - 1))
    (hpπ : Associated ((ζ - 1) ^ (p - 1)) (p : O)) (u : MvPowerSeries (Fin n) O)
    (hu : ∀ h : Fin n → Fin p, h ≠ 0 →
      ∃ m : Fin n →₀ ℕ, ¬ p ∣ ∑ i, (h i : ℕ) * m i ∧ ¬ (ζ - 1) ∣ coeff m u)
    {P : Polynomial (MvPowerSeries (Fin n) O)} (hmon : P.Monic) (hdeg : P.natDegree + 1 = p ^ n)
    (hB : P ∈ BPoly (frob p)) {k : ℕ} (hk : (p : MvPowerSeries (Fin n) O) ^ k ∣ P.eval u) :
    (p - 1) * (k + n) < p ^ n := by
  classical
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : IsDomain (MvPowerSeries (Fin n) O) := NoZeroDivisors.to_isDomain _
  have : (Ideal.span {ζ - 1} : Ideal O).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  have : IsDomain (O ⧸ (Ideal.span {ζ - 1} : Ideal O)) := Ideal.Quotient.isDomain _
  have : IsDomain (MvPowerSeries (Fin n) (O ⧸ (Ideal.span {ζ - 1} : Ideal O))) :=
    NoZeroDivisors.to_isDomain _
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hp2 := hp.out.two_le
  have hπp : (ζ - 1) ∣ (p : O) := (dvd_pow_self (ζ - 1) (by omega)).trans hpπ.dvd
  have hCπ : (C (ζ - 1) : MvPowerSeries (Fin n) O) ≠ 0 := constantCoeff_C_ne hπ.ne_zero
  choose E hEeq hEne using fun h : Fin n → Fin p => exists_E hπ hπp u h
  have hEne' : ∀ h : Fin n → Fin p, h ≠ 0 → resPi ζ (E h) ≠ 0 := fun h hh => by
    obtain ⟨m, hm1, hm2⟩ := hu h hh
    exact hEne h m hm1 hm2
  set N := p ^ n with hN
  have hcard : Fintype.card (Fin n → Fin p) = N := by simp [hN]
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ hp.out.pos
  set D' := ∏ h ∈ Finset.univ.erase (0 : Fin n → Fin p), E h with hD'
  set z : (Fin n → Fin p) → MvPowerSeries (Fin n) O := fun g => tw ζ g u with hz
  have hzdiff : ∀ g h, z g - z (g + h) = C (ζ - 1) * tw ζ g (E h) := by
    intro g h
    simp only [hz]
    rw [← tw_tw hζp, ← map_sub, hEeq, map_mul, tw_C]
  have hzinj : Function.Injective z := by
    intro g g' hgg'
    by_contra hne
    have h0 : g' - g ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have := hzdiff g (g' - g)
    rw [show g + (g' - g) = g' by abel, hgg', sub_self] at this
    have h1 : tw ζ g (E (g' - g)) = 0 := (mul_eq_zero.1 this.symm).resolve_left hCπ
    have h2 : E (g' - g) = 0 := by
      have := congrArg (tw ζ (-g)) h1
      rwa [tw_tw hζp, neg_add_cancel, tw_zero, map_zero] at this
    exact hEne' _ h0 (by rw [h2, map_zero])
  have hD : ∀ g, ∏ h ∈ Finset.univ.erase g, (z g - z h) = C (ζ - 1) ^ (N - 1) * tw ζ g D' := by
    intro g
    rw [prod_erase_translate (fun h => z g - z h) g, Finset.prod_congr rfl fun h _ => hzdiff g h,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hcard, hD', map_prod]
  set c := ∏ h ∈ Finset.univ.erase (0 : Fin n → Fin p), tw ζ h D' with hcdef
  have hc : ∀ g : Fin n → Fin p, ∏ g' ∈ Finset.univ.erase g, tw ζ g' D' = tw ζ g c := by
    intro g
    rw [prod_erase_translate (fun g' => tw ζ g' D') g, hcdef, map_prod]
    exact Finset.prod_congr rfl fun h _ => (tw_tw hζp g h D').symm
  obtain ⟨y, hy⟩ := hk
  have hQz : ∀ g, P.eval (z g) = (p : MvPowerSeries (Fin n) O) ^ k * tw ζ g y := fun g => by
    simp only [hz]
    rw [eval_tw hζp hB, hy, map_mul, map_pow, map_natCast]
  have hL := lagrange_cleared z hzinj P hmon (by rw [hdeg, hcard])
  simp only [hD, hQz] at hL
  have hLHS : ∏ g : Fin n → Fin p, (C (ζ - 1) ^ (N - 1) * tw ζ g D')
      = C (ζ - 1) ^ ((N - 1) * N) * ∏ g : Fin n → Fin p, tw ζ g D' := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, ← pow_mul]
  have hRHS : ∀ g : Fin n → Fin p, (p : MvPowerSeries (Fin n) O) ^ k * tw ζ g y *
      ∏ g' ∈ Finset.univ.erase g, (C (ζ - 1) ^ (N - 1) * tw ζ g' D')
      = C (ζ - 1) ^ ((N - 1) * (N - 1)) * ((p : MvPowerSeries (Fin n) O) ^ k * tw ζ g (y * c)) := by
    intro g
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hcard, ← pow_mul, hc g, map_mul]
    ring
  obtain ⟨s, hs⟩ := natCast_pow_dvd_sum_tw hζ (y * c)
  rw [hLHS, Finset.sum_congr rfl (fun g _ => hRHS g), ← Finset.mul_sum, ← Finset.mul_sum, hs] at hL
  have hsplit : (N - 1) * N = (N - 1) * (N - 1) + (N - 1) := by
    obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [hM, Nat.add_sub_cancel]; ring
  rw [hsplit, pow_add, mul_assoc] at hL
  have hL2 := mul_left_cancel₀ (pow_ne_zero _ hCπ) hL
  -- `p = π ^ (p - 1) v`
  obtain ⟨v, hv⟩ := hpπ
  have hpA : (p : MvPowerSeries (Fin n) O) = C (ζ - 1) ^ (p - 1) * C (v : O) := by
    rw [← map_pow, ← map_mul, hv, map_natCast]
  by_contra hge
  push Not at hge
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hge
  have hX : C (ζ - 1) ^ (N - 1) * ∏ g : Fin n → Fin p, tw ζ g D'
      = C (ζ - 1) ^ (N - 1) * (C (ζ - 1) * (C (ζ - 1) ^ t * (C (v : O) ^ (k + n) * s))) := by
    rw [hL2, show (p : MvPowerSeries (Fin n) O) ^ k * ((p : MvPowerSeries (Fin n) O) ^ n * s)
        = (p : MvPowerSeries (Fin n) O) ^ (k + n) * s by ring, hpA, mul_pow, ← pow_mul,
      show (p - 1) * (k + n) = N - 1 + 1 + t by omega, pow_add, pow_add]
    ring
  have hX2 := mul_left_cancel₀ (pow_ne_zero _ hCπ) hX
  have h0 := congrArg (resPi ζ) hX2
  rw [map_mul, resPi_C_pi, zero_mul, map_prod] at h0
  simp only [resPi_tw] at h0
  rw [Finset.prod_const, hD', map_prod] at h0
  refine pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun h hh => hEne' h ?_) h0
  exact (Finset.mem_erase.1 hh).1

end Core

/-! ## 4. Legendre: `v_p(a!) + v_p(b!)` when `a + b + 1 = p ^ n` -/

section Legendre

open scoped Nat

theorem legendre_split (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    ∀ a b : ℕ, a + b + 1 = p ^ n →
      (p - 1) * (padicValNat p a ! + padicValNat p b !) + n * (p - 1) + 1 = p ^ n := by
  induction n with
  | zero =>
    intro a b hab
    have ha : a = 0 := by simp at hab; omega
    have hb : b = 0 := by simp at hab; omega
    subst ha hb; simp
  | succ n ih =>
    intro a b hab
    have hpos := hp.out.pos
    have ha := Nat.div_add_mod a p
    have hb := Nat.div_add_mod b p
    have hr := Nat.mod_lt a hpos
    have hs := Nat.mod_lt b hpos
    have e : p * (a / p + b / p) + (a % p + b % p + 1) = p * p ^ n := by
      rw [← pow_succ', ← hab]; nlinarith
    have hdvd : p ∣ a % p + b % p + 1 :=
      (Nat.dvd_add_right (dvd_mul_right p _)).1 (e ▸ dvd_mul_right p _)
    obtain ⟨c, hc⟩ := hdvd
    have hc1 : c = 1 := by
      have h1 : 0 < p * c := by omega
      have h2 : p * c < p * 2 := by omega
      have := Nat.lt_of_mul_lt_mul_left h2
      have := Nat.pos_of_mul_pos_left h1
      omega
    rw [hc, hc1, mul_one] at e
    have hsum : a / p + b / p + 1 = p ^ n :=
      Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_add, mul_one]; exact e)
    rw [padicValNat_factorial_div p a, padicValNat_factorial_div p b]
    have key : (p - 1) * (a / p + padicValNat p (a / p)! + (b / p + padicValNat p (b / p)!))
          + (n + 1) * (p - 1) + 1
        = (p - 1) * (a / p + b / p + 1)
          + ((p - 1) * (padicValNat p (a / p)! + padicValNat p (b / p)!) + n * (p - 1) + 1) := by
      ring
    rw [key, hsum, ih _ _ hsum, pow_succ]
    have h1 : p - 1 + 1 = p := by omega
    calc (p - 1) * p ^ n + p ^ n = (p - 1 + 1) * p ^ n := by ring
      _ = p ^ n * p := by rw [h1, mul_comm]

end Legendre

/-! ## 5. The lower bound for `ζ_n = ∏ (1 - x_i)⁻¹` -/

section Zeta

variable (p : ℕ) [hp : Fact p.Prime]

theorem constantCoeff_prod_one_sub_X {R : Type*} [CommRing R] {n : ℕ} (s : Finset (Fin n)) :
    constantCoeff (∏ j ∈ s, (1 - X j : MvPowerSeries (Fin n) R)) = 1 := by
  simp [map_prod]

theorem coeff_single_prod_one_sub_X {R : Type*} [CommRing R] {n : ℕ} (i : Fin n)
    (s : Finset (Fin n)) :
    coeff (Finsupp.single i 1) (∏ j ∈ s, (1 - X j : MvPowerSeries (Fin n) R))
      = if i ∈ s then -1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, coeff_one, if_neg (Finsupp.single_ne_zero.2 one_ne_zero)]
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, sub_mul, one_mul, map_sub, ih, X, coeff_monomial_mul]
    by_cases hai : a = i
    · subst hai
      rw [if_pos le_rfl, tsub_self, coeff_zero_eq_constantCoeff_apply,
        constantCoeff_prod_one_sub_X, one_mul,
        if_neg ha, if_pos (Finset.mem_insert_self _ _)]
      simp
    · have hle : ¬ Finsupp.single a 1 ≤ Finsupp.single i 1 := by
        intro hle
        have := hle a
        simp [Ne.symm hai] at this
      rw [if_neg hle, sub_zero]
      simp [Finset.mem_insert, Ne.symm hai]

/-- `ρ(u) = n` (ledger R-060, R-080): the exponent vectors, modulo `p`, of the monomials of `u`
that survive modulo `p` span `F_p ^ n`; equivalently no `h ≠ 0` in `F_p ^ n` is orthogonal to all
of them. -/
def FullRank (p : ℕ) {R : Type*} [CommRing R] {n : ℕ} (u : MvPowerSeries (Fin n) R) : Prop :=
  ∀ h : Fin n → ℕ, (∀ i, h i < p) → (∃ i, h i ≠ 0) →
    ∃ m : Fin n →₀ ℕ, ¬ p ∣ ∑ i, h i * m i ∧ ¬ (p : R) ∣ coeff m u

omit hp in
theorem not_natCast_dvd_neg_one {R : Type*} [CommRing R] (hpu : ¬ IsUnit (p : R)) :
    ¬ (p : R) ∣ -1 :=
  fun hd => hpu (isUnit_of_dvd_one (dvd_neg.1 hd))

omit hp in
/-- `u = ∏ (1 - x_i)` has full rank (its monomials include every `x_i`, with coefficient `-1`). -/
theorem fullRank_zetaDen {R : Type*} [CommRing R] (hpu : ¬ IsUnit (p : R)) (n : ℕ) :
    FullRank p (zetaDen (R := R) n) := by
  classical
  intro h hlt ⟨i, hi⟩
  refine ⟨Finsupp.single i 1, ?_, ?_⟩
  · have hsum : ∑ j, h j * (Finsupp.single i 1) j = h i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    rw [hsum]
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hi) (hlt i)
  · rw [zetaDen, coeff_single_prod_one_sub_X, if_pos (Finset.mem_univ _)]
    exact not_natCast_dvd_neg_one p hpu

/-- Hypothesis `(hu)` of `core_bound` for the image in `O[[x]]` of a full rank `u ∈ ℤ[[x]]`. -/
theorem hu_of_fullRank {O : Type*} [CommRing O] {ζ : O} (hπ : Prime (ζ - 1))
    (hπp : (ζ - 1) ∣ (p : O)) {n : ℕ} {u : MvPowerSeries (Fin n) ℤ} (hu : FullRank p u)
    (h : Fin n → Fin p) (hh : h ≠ 0) :
    ∃ m : Fin n →₀ ℕ, ¬ p ∣ ∑ i, (h i : ℕ) * m i ∧
      ¬ (ζ - 1) ∣ coeff m (MvPowerSeries.map (Int.castRingHom O) u) := by
  classical
  have : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨i, hi⟩ : ∃ i, h i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hh (funext hc)
  have hi' : (h i : ℕ) ≠ 0 := fun e => hi (Fin.ext (e.trans (Fin.val_zero p).symm))
  obtain ⟨m, hm1, hm2⟩ := hu (fun j => (h j : ℕ)) (fun j => (h j).isLt) ⟨i, hi'⟩
  refine ⟨m, hm1, fun hd => ?_⟩
  rw [coeff_map, eq_intCast] at hd
  have hcop : IsCoprime (coeff m u) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2
      (fun hdv => hm2 (Int.natCast_dvd.2 hdv)))
  have hcopO : IsCoprime ((coeff m u : ℤ) : O) (p : O) := by
    simpa using hcop.map (Int.castRingHom O)
  exact hπ.not_isUnit (hcopO.isUnit_of_dvd' hd hπp)

open NumberField in
/-- Lower bound over `ℤ`: if `u ∈ ℤ[[x_1..x_n]]` has full rank, a monic annihilator of `u` over `B`
modulo `p ^ k` of degree `m < p ^ n` has `S(p ^ k) ≤ m`. -/
theorem kempner_le_of_monicAnn_int {n k m : ℕ} {u : MvPowerSeries (Fin n) ℤ} (hu : FullRank p u)
    (hm : m < p ^ n) (hP : MonicAnn p (frob p) u k m) : kempner p k ≤ m := by
  classical
  obtain ⟨P, hmon, hdeg, hB, hPu⟩ := hP
  set d := p ^ n - 1 - m with hd
  obtain ⟨Q, hQm, hQd, hQB, hQu⟩ := exists_monic_tower (frob_isFrobLift p (int_pow_sub p)) d u
  -- the cyclotomic integers
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : NeZero (p : ℚ) := ⟨by exact_mod_cast hp.out.ne_zero⟩
  have hcyc : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  have hζK : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)) p :=
    IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  have hζ : IsPrimitiveRoot hζK.toInteger p := hζK.toInteger_isPrimitiveRoot
  have hπ : Prime (hζK.toInteger - 1) := hζK.zeta_sub_one_prime'
  have hpπ : Associated ((hζK.toInteger - 1) ^ (p - 1)) (p : 𝓞 (CyclotomicField p ℚ)) :=
    IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζK
  have hπp : (hζK.toInteger - 1) ∣ (p : 𝓞 (CyclotomicField p ℚ)) :=
    (dvd_pow_self _ (by have := hp.out.two_le; omega)).trans hpπ.dvd
  set O := 𝓞 (CyclotomicField p ℚ)
  set φ : MvPowerSeries (Fin n) ℤ →+* MvPowerSeries (Fin n) O :=
    MvPowerSeries.map (Int.castRingHom O) with hφ
  have hfφ : ∀ a, φ (frob p a) = frob p (φ a) := fun a => by
    simp [hφ, frob_apply, MvPowerSeries.map_expand]
  have hRm : ((P * Q).map φ).Monic := (hmon.mul hQm).map φ
  have hRd : ((P * Q).map φ).natDegree + 1 = p ^ n := by
    rw [(hmon.mul hQm).natDegree_map, hmon.natDegree_mul hQm, hdeg, hQd, hd]
    have := Nat.one_le_pow n p hp.out.pos
    omega
  have hRB : (P * Q).map φ ∈ BPoly (frob p) := by
    rw [mem_BPoly_iff]
    intro i
    rw [Polynomial.coeff_map]
    obtain ⟨a, ha⟩ := mem_BPoly_iff.1 (mul_mem hB hQB) i
    exact ⟨φ a, by rw [← ha, hfφ]⟩
  have hRu : (p : MvPowerSeries (Fin n) O) ^ (k + padicValNat p d.factorial)
      ∣ ((P * Q).map φ).eval (φ u) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom, Polynomial.eval_mul, pow_add]
    have := mul_dvd_mul hPu hQu
    obtain ⟨w, hw⟩ := this
    exact ⟨φ w, by rw [hw]; simp only [map_mul, map_pow, map_natCast]⟩
  have hcore := core_bound hζ hπ hpπ (φ u) (fun h hh => hu_of_fullRank p hπ hπp hu h hh)
    hRm hRd hRB hRu
  have hleg := legendre_split p n m d (by rw [hd]; have := Nat.one_le_pow n p hp.out.pos; omega)
  apply kempner_le p
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  have h1 : (p - 1) * (k + padicValNat p d.factorial + n)
      ≤ (p - 1) * (padicValNat p m.factorial + padicValNat p d.factorial + n) := by
    have e : (p - 1) * (padicValNat p m.factorial + padicValNat p d.factorial + n)
        = (p - 1) * (padicValNat p m.factorial + padicValNat p d.factorial) + n * (p - 1) := by ring
    omega
  have := Nat.le_of_mul_le_mul_left h1 hp1
  omega

/-- R-080 (C2) with `ρ = r = n`, over `ℤ`: for a unit `f` of `ℤ[[x_1..x_n]]` whose inverse has
full rank, `L_f(p, k) + 1 = min (p ^ n) (S(p ^ k))` for every `k ≥ 1`. -/
theorem levelCount_eq_of_fullRank_int {n : ℕ} {f u : MvPowerSeries (Fin n) ℤ} (hfu : f * u = 1)
    (hu : FullRank p u) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) f k + 1 = min (p ^ n) (kempner p k) := by
  refine le_antisymm (levelCount_le_min p (int_pow_sub p) ⟨⟨f, u, hfu, by rw [mul_comm]; exact hfu⟩, rfl⟩ hk) ?_
  have hfu' : (p : MvPowerSeries (Fin n) ℤ) ^ k ∣ f * u - 1 := by
    rw [hfu, sub_self]; exact dvd_zero _
  have hpk := not_isUnit_pow_mvPowerSeries (τ := Fin n) p (int_not_isUnit p) hk
  have hex := monicAnn_kempner (frob_isFrobLift p (int_pow_sub p)) u k
  rw [levelCount_add_one hfu' hpk hex]
  have hmin := monicAnn_annDegree hex
  by_cases hlt : annDegree p (frob p) u k < p ^ n
  · exact (min_le_right _ _).trans (kempner_le_of_monicAnn_int p hu hlt hmin)
  · exact (min_le_left _ _).trans (not_lt.1 hlt)

/-- R-080 (C) over `ℤ`: `L(ζ_n; p, k) = min (p ^ n - 1) (S(p ^ k) - 1)` for every `n`, `p`, `k ≥ 1`
(written `L + 1 = min (p ^ n) (S(p ^ k))`). -/
theorem levelCount_zeta_int (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) (zeta (R := ℤ) n) k + 1 = min (p ^ n) (kempner p k) :=
  levelCount_eq_of_fullRank_int p (by rw [mul_comm]; exact zetaDen_mul_zeta n)
    (fullRank_zetaDen p (int_not_isUnit p) n) hk

end Zeta

end FrobLevel
