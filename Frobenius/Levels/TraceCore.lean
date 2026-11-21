module

/-
Run r25, seat L5: the trace bound for a group of twists, with a depth for every character.

1. `trace_core` (abstract). `F` a domain, `ρ : F → Q` a map to a domain killing `π ≠ 0`, a finite
   group `G` acting on `F` by ring maps `τ_g` that fix `π` and the coefficients of `P`, reduce to
   the identity under `ρ`, and whose trace is divisible by `π ^ T`. If `u - τ_h u = π ^ (e h) E_h`
   with `ρ(E_h) ≠ 0` for `h ≠ 0`, then a monic `P` of degree `#G - 1` with `π ^ K ∣ P(u)` has
   `K + T ≤ ∑_{h ≠ 0} e h`. (L1's `core_bound` is the case `G = F_p ^ n`, `e = 1`.)
2. Twists by vectors: `tz ζ v` (`x_i ↦ ζ ^ (v_i) x_i`, `v : Fin n → ZMod p`) on `O[[x]]`, the pairing
   `pair v m = ∑ v_i m_i ∈ F_p`, the character sum over `G` through an additive map
   `M : G → F_p ^ n`.
3. `top_bound_int`: for `u ∈ ℤ[[x_1..x_n]]`, `#G = p ^ s` and depths `dep h` (for `h ≠ 0`: `p ^ dep h`
   divides every coefficient of `u` at a monomial `x ^ m` with `pair (M h) m ≠ 0`, and some such
   coefficient is not divisible by `p ^ (dep h + 1)`), a monic `P ∈ B[X]` of degree `p ^ s - 1` with
   `p ^ k ∣ P(u)` has `(p - 1)(k + s) ≤ p ^ s - 1 + (p - 1) ∑_{h ≠ 0} dep h`.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Lower

@[expose] public section

namespace FrobLevel

open MvPowerSeries

/-! ## 1. The abstract trace bound -/

section Abstract

theorem trace_core {F Q G : Type*} [CommRing F] [IsDomain F] [CommRing Q] [IsDomain Q]
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (ρ : F →+* Q) (τ : G → F →+* F)
    (hτ0 : ∀ x, τ 0 x = x) (hτadd : ∀ g h x, τ g (τ h x) = τ (g + h) x)
    (hρτ : ∀ g x, ρ (τ g x) = ρ x)
    {π : F} (hπ0 : π ≠ 0) (hρπ : ρ π = 0) (hτπ : ∀ g, τ g π = π)
    {T : ℕ} (htr : ∀ w, π ^ T ∣ ∑ g, τ g w)
    (u : F) (e : G → ℕ) (E : G → F)
    (hE : ∀ h, h ≠ 0 → u - τ h u = π ^ e h * E h) (hEρ : ∀ h, h ≠ 0 → ρ (E h) ≠ 0)
    {P : Polynomial F} (hmon : P.Monic) (hdeg : P.natDegree + 1 = Fintype.card G)
    (hfix : ∀ g i, τ g (P.coeff i) = P.coeff i) {K : ℕ} (hK : π ^ K ∣ P.eval u) :
    K + T ≤ ∑ h ∈ Finset.univ.erase (0 : G), e h := by
  classical
  set V := ∑ h ∈ Finset.univ.erase (0 : G), e h with hV
  set N := Fintype.card G with hNdef
  set D' := ∏ h ∈ Finset.univ.erase (0 : G), E h with hD'
  set z : G → F := fun g => τ g u with hz
  have hτπpow : ∀ g j, τ g (π ^ j) = π ^ j := fun g j => by rw [map_pow, hτπ]
  have hzdiff : ∀ g h, h ≠ 0 → z g - z (g + h) = π ^ e h * τ g (E h) := by
    intro g h hh
    simp only [hz]
    rw [← hτadd, ← map_sub, hE h hh, map_mul, hτπpow]
  have hzinj : Function.Injective z := by
    intro g g' hgg'
    by_contra hne
    have h0 : g' - g ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have := hzdiff g (g' - g) h0
    rw [show g + (g' - g) = g' by abel, hgg', sub_self] at this
    have h1 : τ g (E (g' - g)) = 0 := (mul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ hπ0)
    have h2 : E (g' - g) = 0 := by
      have := congrArg (τ (-g)) h1
      rwa [hτadd, neg_add_cancel, hτ0, map_zero] at this
    exact hEρ _ h0 (by rw [h2, map_zero])
  have hD : ∀ g, ∏ h ∈ Finset.univ.erase g, (z g - z h) = π ^ V * τ g D' := by
    intro g
    rw [prod_erase_translate (fun h => z g - z h) g,
      Finset.prod_congr rfl fun h hh => hzdiff g h (Finset.mem_erase.1 hh).1,
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hD', map_prod]
  set c := ∏ h ∈ Finset.univ.erase (0 : G), τ h D' with hcdef
  have hc : ∀ g, ∏ g' ∈ Finset.univ.erase g, τ g' D' = τ g c := by
    intro g
    rw [prod_erase_translate (fun g' => τ g' D') g, hcdef, map_prod]
    exact Finset.prod_congr rfl fun h _ => (hτadd g h D').symm
  obtain ⟨y, hy⟩ := hK
  have heval : ∀ g x, P.eval (τ g x) = τ g (P.eval x) := by
    intro g x
    have hmap : P.map (τ g) = P := Polynomial.ext fun i => by rw [Polynomial.coeff_map, hfix]
    conv_lhs => rw [← hmap]
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have hQz : ∀ g, P.eval (z g) = π ^ K * τ g y := fun g => by
    simp only [hz]; rw [heval, hy, map_mul, hτπpow]
  have hL := lagrange_cleared z hzinj P hmon hdeg
  simp only [hD, hQz] at hL
  have hLHS : ∏ g : G, (π ^ V * τ g D') = π ^ (V * N) * ∏ g : G, τ g D' := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hRHS : ∀ g : G, π ^ K * τ g y * ∏ g' ∈ Finset.univ.erase g, (π ^ V * τ g' D')
      = π ^ (V * (N - 1)) * (π ^ K * τ g (y * c)) := by
    intro g
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ← pow_mul, hc g, map_mul]
    ring
  obtain ⟨s, hs⟩ := htr (y * c)
  rw [hLHS, Finset.sum_congr rfl (fun g _ => hRHS g), ← Finset.mul_sum, ← Finset.mul_sum, hs] at hL
  have hN1 : 1 ≤ N := Fintype.card_pos
  have hsplit : V * N = V * (N - 1) + V := by
    obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [hM, Nat.add_sub_cancel]; ring
  rw [hsplit, pow_add, mul_assoc] at hL
  have hL2 := mul_left_cancel₀ (pow_ne_zero _ hπ0) hL
  by_contra hge
  push Not at hge
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt hge
  have hX : π ^ V * ∏ g : G, τ g D' = π ^ V * (π * (π ^ t * s)) := by
    rw [hL2, ← mul_assoc, ← pow_add, ht, pow_add, pow_add]; ring
  have hX2 := mul_left_cancel₀ (pow_ne_zero _ hπ0) hX
  have h0 := congrArg ρ hX2
  rw [map_mul, hρπ, zero_mul, map_prod] at h0
  simp only [hρτ] at h0
  rw [Finset.prod_const, hD', map_prod] at h0
  refine pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun h hh => hEρ h ?_) h0
  exact (Finset.mem_erase.1 hh).1

end Abstract

/-! ## 2. Twists by vectors of `F_p ^ n` -/

section Twist

variable {O : Type*} [CommRing O] {n p : ℕ}

/-- The pairing `⟨v, m⟩ = ∑ v_i m_i` in `F_p`. -/
def pair (v : Fin n → ZMod p) (m : Fin n →₀ ℕ) : ZMod p := ∑ i, v i * (m i : ZMod p)

/-- The twist `x_i ↦ ζ ^ (v_i) x_i`. -/
noncomputable def tz (ζ : O) (v : Fin n → ZMod p) :
    MvPowerSeries (Fin n) O →+* MvPowerSeries (Fin n) O :=
  rescale fun i => ζ ^ (v i).val

theorem coeff_tz (ζ : O) (v : Fin n → ZMod p) (f : MvPowerSeries (Fin n) O) (m : Fin n →₀ ℕ) :
    coeff m (tz ζ v f) = ζ ^ (∑ i, (v i).val * m i) * coeff m f := by
  rw [tz, coeff_rescale, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    ← Finset.prod_pow_eq_pow_sum]
  congr 1
  exact Finset.prod_congr rfl fun i _ => (pow_mul ζ _ _).symm

theorem pair_eq_cast [NeZero p] (v : Fin n → ZMod p) (m : Fin n →₀ ℕ) :
    pair v m = ((∑ i, (v i).val * m i : ℕ) : ZMod p) := by
  rw [pair, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_mul, ZMod.natCast_zmod_val]

theorem pow_sum_eq_pow_pair [NeZero p] {ζ : O} (hζ : ζ ^ p = 1) (v : Fin n → ZMod p)
    (m : Fin n →₀ ℕ) : ζ ^ (∑ i, (v i).val * m i) = ζ ^ (pair v m).val := by
  rw [pair_eq_cast, ZMod.val_natCast, pow_mod_of_pow_eq_one hζ]

theorem coeff_tz' [NeZero p] {ζ : O} (hζ : ζ ^ p = 1) (v : Fin n → ZMod p)
    (f : MvPowerSeries (Fin n) O) (m : Fin n →₀ ℕ) :
    coeff m (tz ζ v f) = ζ ^ (pair v m).val * coeff m f := by
  rw [coeff_tz, pow_sum_eq_pow_pair hζ]

theorem pow_val_add [NeZero p] {ζ : O} (hζ : ζ ^ p = 1) (a b : ZMod p) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, pow_mod_of_pow_eq_one hζ, pow_add]

theorem tz_tz [NeZero p] {ζ : O} (hζ : ζ ^ p = 1) (v w : Fin n → ZMod p)
    (f : MvPowerSeries (Fin n) O) : tz ζ v (tz ζ w f) = tz ζ (v + w) f := by
  have e : ((fun i => ζ ^ (w i).val) * fun i => ζ ^ (v i).val) = fun i => ζ ^ ((v + w) i).val := by
    funext i
    simp only [Pi.mul_apply, Pi.add_apply, pow_val_add hζ, mul_comm]
  simp only [tz]
  rw [rescale_rescale, e]

theorem tz_zero (ζ : O) (f : MvPowerSeries (Fin n) O) : tz ζ (0 : Fin n → ZMod p) f = f := by
  have : (fun i : Fin n => ζ ^ ((0 : Fin n → ZMod p) i).val) = 1 := by
    funext i; simp
  rw [tz, this, rescale_one, RingHom.id_apply]

theorem tz_C (ζ : O) (v : Fin n → ZMod p) (c : O) : tz ζ v (C c) = C c := by
  ext m
  rw [coeff_tz, coeff_C]
  split_ifs with h
  · subst h; simp
  · rw [mul_zero]

theorem tz_frob [Fact p.Prime] {ζ : O} (hζ : ζ ^ p = 1) (v : Fin n → ZMod p)
    (f : MvPowerSeries (Fin n) O) : tz ζ v (frob p f) = frob p f := by
  ext m
  rw [coeff_tz]
  by_cases h : ∀ i, p ∣ m i
  · obtain ⟨c, hc⟩ : p ∣ ∑ i, (v i).val * m i :=
      Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (h i) _
    rw [hc, pow_mul, hζ, one_pow, one_mul]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [coeff_frob_of_not_dvd p f hi, mul_zero]

theorem resPi_tz (ζ : O) (v : Fin n → ZMod p) (f : MvPowerSeries (Fin n) O) :
    resPi ζ (tz ζ v f) = resPi ζ f := by
  ext m
  rw [resPi, coeff_map, coeff_map, coeff_tz, map_mul, map_pow, mk_zeta, one_pow, one_mul]

theorem pair_add_left (v w : Fin n → ZMod p) (m : Fin n →₀ ℕ) :
    pair (v + w) m = pair v m + pair w m := by
  simp only [pair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem pair_zero_left (m : Fin n →₀ ℕ) : pair (0 : Fin n → ZMod p) m = 0 := by
  simp [pair]

/-- The character sum over `G`: `∑_g ζ ^ ⟨M g, m⟩` is `#G` or `0`. -/
theorem char_sum [IsDomain O] [NeZero p] {ζ : O} (hζ : IsPrimitiveRoot ζ p) {G : Type*}
    [AddCommGroup G] [Fintype G] (M : G →+ (Fin n → ZMod p)) (m : Fin n →₀ ℕ) :
    (Fintype.card G : O) ∣ ∑ g : G, ζ ^ (pair (M g) m).val := by
  by_cases h0 : ∀ g, pair (M g) m = 0
  · simp [h0]
  · push Not at h0
    obtain ⟨g0, hg0⟩ := h0
    set S := ∑ g : G, ζ ^ (pair (M g) m).val
    have hshift : S = ζ ^ (pair (M g0) m).val * S := by
      calc S = ∑ g : G, ζ ^ (pair (M (g + g0)) m).val :=
            (Fintype.sum_equiv (Equiv.addRight g0) _ _ fun g => rfl).symm
        _ = ∑ g : G, ζ ^ (pair (M g0) m).val * ζ ^ (pair (M g) m).val := by
            refine Finset.sum_congr rfl fun g _ => ?_
            rw [map_add, pair_add_left, pow_val_add hζ.pow_eq_one, mul_comm]
        _ = _ := by rw [Finset.mul_sum]
    have hne : ζ ^ (pair (M g0) m).val ≠ 1 := by
      intro h1
      have := (hζ.pow_eq_one_iff_dvd _).1 h1
      have hlt := ZMod.val_lt (pair (M g0) m)
      have hz : (pair (M g0) m).val = 0 := Nat.eq_zero_of_dvd_of_lt this hlt
      exact hg0 ((ZMod.val_eq_zero _).1 hz)
    have : (ζ ^ (pair (M g0) m).val - 1) * S = 0 := by rw [sub_mul, ← hshift]; ring
    rw [(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)]
    exact dvd_zero _

/-- The trace over `G` is divisible by `#G`. -/
theorem card_dvd_sum_tz [IsDomain O] [NeZero p] {ζ : O} (hζ : IsPrimitiveRoot ζ p) {G : Type*}
    [AddCommGroup G] [Fintype G] (M : G →+ (Fin n → ZMod p)) (w : MvPowerSeries (Fin n) O) :
    (Fintype.card G : MvPowerSeries (Fin n) O) ∣ ∑ g : G, tz ζ (M g) w := by
  rw [← map_natCast (C (σ := Fin n) (R := O))]
  apply C_dvd_of_coeff
  intro m
  rw [map_sum]
  simp_rw [coeff_tz' hζ.pow_eq_one]
  rw [← Finset.sum_mul]
  exact Dvd.dvd.mul_right (char_sum hζ M m) _

end Twist

/-! ## 3. The depth factor `E_h` and the top bound over `ℤ` -/

section Int

variable {O : Type*} [CommRing O] [IsDomain O] {n p : ℕ}

theorem not_dvd_geom [hp : Fact p.Prime] {ζ : O} (hπ : Prime (ζ - 1)) (hπp : (ζ - 1) ∣ (p : O))
    {c : ℕ} (hc : ¬ p ∣ c) : ¬ (ζ - 1) ∣ ∑ j ∈ Finset.range c, ζ ^ j := by
  intro h3
  have hsub : ∀ c : ℕ, (ζ - 1) ∣ ζ ^ c - 1 := fun c => by
    simpa using sub_dvd_pow_sub_pow ζ 1 c
  have h4 : (ζ - 1) ∣ (c : O) := by
    have : (c : O) = ∑ j ∈ Finset.range c, ζ ^ j - ∑ j ∈ Finset.range c, (ζ ^ j - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    exact dvd_sub h3 (Finset.dvd_sum fun j _ => hsub j)
  have hcop : IsCoprime (c : O) (p : O) := by
    have : IsCoprime (c : ℤ) (p : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hc))
    simpa using this.map (Int.castRingHom O)
  exact hπ.not_isUnit (hcop.isUnit_of_dvd' h4 hπp)

theorem not_dvd_intCast [hp : Fact p.Prime] {π : O} (hπ : Prime π) (hπp : π ∣ (p : O)) {a : ℤ}
    (ha : ¬ (p : ℤ) ∣ a) : ¬ π ∣ (a : O) := by
  intro hd
  have hcop : IsCoprime a (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2
      (fun hdv => ha (Int.natCast_dvd.2 hdv)))
  have hcopO : IsCoprime (a : O) (p : O) := by simpa using hcop.map (Int.castRingHom O)
  exact hπ.not_isUnit (hcopO.isUnit_of_dvd' hd hπp)

/-- `u - tz v u = π ^ (1 + (p - 1) d) E` with `E ≢ 0 (mod π)`, for `u` with integer coefficients
whose coefficients at `⟨v, m⟩ ≠ 0` are divisible by `p ^ d`, not all by `p ^ (d + 1)`. -/
theorem exists_E_depth [hp : Fact p.Prime] {ζ : O} (hζ : IsPrimitiveRoot ζ p) (hπ : Prime (ζ - 1))
    {ε : O} (hε : (p : O) = (ζ - 1) ^ (p - 1) * ε) (hεu : IsUnit ε)
    (u : MvPowerSeries (Fin n) ℤ) (v : Fin n → ZMod p) (d : ℕ)
    (hdiv : ∀ m, pair v m ≠ 0 → (p : ℤ) ^ d ∣ coeff m u)
    (hstar : ∃ m, pair v m ≠ 0 ∧ ¬ (p : ℤ) ^ (d + 1) ∣ coeff m u) :
    ∃ E, MvPowerSeries.map (Int.castRingHom O) u - tz ζ v (MvPowerSeries.map (Int.castRingHom O) u)
        = C ((ζ - 1) ^ (1 + (p - 1) * d)) * E ∧ resPi ζ E ≠ 0 := by
  classical
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hζp := hζ.pow_eq_one
  have hπp : (ζ - 1) ∣ (p : O) := by
    rw [hε]; exact Dvd.dvd.mul_right (dvd_pow_self _ (by have := hp.out.two_le; omega)) _
  set φ := MvPowerSeries.map (σ := Fin n) (Int.castRingHom O) with hφ
  set c : (Fin n →₀ ℕ) → ℕ := fun m => ∑ i, (v i).val * m i with hc
  set q : (Fin n →₀ ℕ) → ℤ := fun m => coeff m u / (p : ℤ) ^ d with hqdef
  have hq : ∀ m, pair v m ≠ 0 → coeff m u = (p : ℤ) ^ d * q m := fun m hm =>
    (Int.mul_ediv_cancel' (hdiv m hm)).symm
  set E : MvPowerSeries (Fin n) O := fun m =>
    if pair v m = 0 then 0 else -(∑ j ∈ Finset.range (c m), ζ ^ j) * ε ^ d * (q m : O) with hE
  have hcoefE : ∀ m, coeff m E =
      if pair v m = 0 then 0 else -(∑ j ∈ Finset.range (c m), ζ ^ j) * ε ^ d * (q m : O) :=
    fun m => rfl
  refine ⟨E, ?_, ?_⟩
  · ext m
    rw [map_sub, coeff_tz, coeff_C_mul, hcoefE, hφ, coeff_map, eq_intCast]
    split_ifs with hm
    · rw [pow_sum_eq_pow_pair hζp, hm, ZMod.val_zero, pow_zero, one_mul, sub_self, mul_zero]
    · rw [hq m hm, Int.cast_mul, Int.cast_pow, Int.cast_natCast, hε]
      have hg : (∑ j ∈ Finset.range (c m), ζ ^ j) * (ζ - 1) = ζ ^ (c m) - 1 := geom_sum_mul ζ _
      have : ζ ^ (∑ i, (v i).val * m i) = ζ ^ (c m) := rfl
      rw [this, ← sub_eq_zero]
      have h2 : ζ ^ (c m) = (∑ j ∈ Finset.range (c m), ζ ^ j) * (ζ - 1) + 1 := by rw [hg]; ring
      rw [h2]
      ring
  · obtain ⟨m, hm1, hm2⟩ := hstar
    intro h0
    have hcm := congrArg (coeff m) h0
    rw [resPi, coeff_map, map_zero, hcoefE, if_neg hm1, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at hcm
    have hgeom : ¬ (ζ - 1) ∣ ∑ j ∈ Finset.range (c m), ζ ^ j := by
      refine not_dvd_geom hπ hπp fun hpc => hm1 ?_
      rw [pair_eq_cast]
      exact (ZMod.natCast_eq_zero_iff _ _).2 hpc
    have hεd : ¬ (ζ - 1) ∣ ε ^ d := fun h =>
      hπ.not_isUnit (isUnit_of_dvd_unit (hπ.dvd_of_dvd_pow h) hεu)
    have hqm : ¬ (p : ℤ) ∣ q m := by
      intro hpq
      apply hm2
      rw [hq m hm1, pow_succ]
      exact mul_dvd_mul_left _ hpq
    have hqO := not_dvd_intCast hπ hπp hqm
    rcases hπ.dvd_or_dvd hcm with h1 | h1
    · rcases hπ.dvd_or_dvd h1 with h2 | h2
      · exact hgeom ((dvd_neg).1 h2)
      · exact hεd h2
    · exact hqO h1

end Int

section TopInt

open NumberField

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The top bound over `ℤ`, with a depth for every character.** -/
theorem top_bound_int {n s k : ℕ} {u : MvPowerSeries (Fin n) ℤ} {G : Type*} [AddCommGroup G]
    [Fintype G] [DecidableEq G] (hG : Fintype.card G = p ^ s) (M : G →+ (Fin n → ZMod p))
    (dep : G → ℕ)
    (hdiv : ∀ h, h ≠ 0 → ∀ m, pair (M h) m ≠ 0 → (p : ℤ) ^ (dep h) ∣ coeff m u)
    (hstar : ∀ h, h ≠ 0 → ∃ m, pair (M h) m ≠ 0 ∧ ¬ (p : ℤ) ^ (dep h + 1) ∣ coeff m u)
    (hP : MonicAnn p (frob p) u k (p ^ s - 1)) :
    (p - 1) * (k + s) ≤ p ^ s - 1 + (p - 1) * ∑ h ∈ Finset.univ.erase (0 : G), dep h := by
  classical
  obtain ⟨P, hmon, hdeg, hB, hPu⟩ := hP
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
  set O := 𝓞 (CyclotomicField p ℚ)
  set ζ := hζK.toInteger
  obtain ⟨εu, hεu⟩ := hpπ
  set ε : O := (εu : O)
  have hε : (p : O) = (ζ - 1) ^ (p - 1) * ε := hεu.symm
  have : IsDomain (MvPowerSeries (Fin n) O) := NoZeroDivisors.to_isDomain _
  have : (Ideal.span {ζ - 1} : Ideal O).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  have : IsDomain (O ⧸ (Ideal.span {ζ - 1} : Ideal O)) := Ideal.Quotient.isDomain _
  have : IsDomain (MvPowerSeries (Fin n) (O ⧸ (Ideal.span {ζ - 1} : Ideal O))) :=
    NoZeroDivisors.to_isDomain _
  set φ : MvPowerSeries (Fin n) ℤ →+* MvPowerSeries (Fin n) O :=
    MvPowerSeries.map (Int.castRingHom O) with hφ
  have hfφ : ∀ a, φ (frob p a) = frob p (φ a) := fun a => by
    simp [hφ, frob_apply, MvPowerSeries.map_expand]
  -- the factors `E_h`
  have hEx : ∀ h : G, ∃ E : MvPowerSeries (Fin n) O, h ≠ 0 →
      (φ u - tz ζ (M h) (φ u) = C ((ζ - 1) ^ (1 + (p - 1) * dep h)) * E ∧ resPi ζ E ≠ 0) := by
    intro h
    by_cases hh : h = 0
    · exact ⟨0, fun h' => absurd hh h'⟩
    · obtain ⟨E, h1, h2⟩ := exists_E_depth hζ hπ hε εu.isUnit u (M h) (dep h) (hdiv h hh)
        (hstar h hh)
      exact ⟨E, fun _ => ⟨h1, h2⟩⟩
  choose E hE using hEx
  set Cπ : MvPowerSeries (Fin n) O := C (ζ - 1) with hCπ
  have hpF : (p : MvPowerSeries (Fin n) O) = Cπ ^ (p - 1) * C ε := by
    rw [hCπ, ← map_pow, ← map_mul, ← hε, map_natCast]
  have hcore := trace_core (resPi ζ) (fun g => tz ζ (M g))
    (fun x => by simp only [map_zero]; exact tz_zero ζ x)
    (fun g h x => by simp only [map_add]; exact tz_tz hζ.pow_eq_one _ _ x)
    (fun g x => resPi_tz ζ (M g) x) (π := Cπ) (constantCoeff_C_ne hπ.ne_zero) (resPi_C_pi ζ)
    (fun g => tz_C ζ (M g) _) (T := (p - 1) * s)
    (fun w => by
      have h1 := card_dvd_sum_tz hζ M w
      rw [hG, Nat.cast_pow, hpF, mul_pow, ← pow_mul] at h1
      exact (Dvd.dvd.mul_right (dvd_refl _) _).trans h1)
    (φ u) (fun h => 1 + (p - 1) * dep h) E
    (fun h hh => by rw [(hE h hh).1, map_pow])
    (fun h hh => (hE h hh).2)
    (P := P.map φ) (hmon.map φ)
    (by rw [hmon.natDegree_map, hdeg, hG]; have := Nat.one_le_pow s p hp.out.pos; omega)
    (fun g i => by
      rw [Polynomial.coeff_map]
      obtain ⟨a, ha⟩ := mem_BPoly_iff.1 hB i
      rw [← ha, hfφ]
      exact tz_frob hζ.pow_eq_one _ _)
    (K := (p - 1) * k)
    (by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom]
      obtain ⟨y, hy⟩ := hPu
      refine ⟨C ε ^ k * φ y, ?_⟩
      rw [hy, map_mul, map_pow, map_natCast, hpF, mul_pow, ← pow_mul]
      ring)
  have hsum : ∑ h ∈ Finset.univ.erase (0 : G), (1 + (p - 1) * dep h)
      = p ^ s - 1 + (p - 1) * ∑ h ∈ Finset.univ.erase (0 : G), dep h := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hG, smul_eq_mul, mul_one, Finset.mul_sum]
  rw [hsum] at hcore
  rw [mul_add]
  exact hcore

end TopInt

end FrobLevel
