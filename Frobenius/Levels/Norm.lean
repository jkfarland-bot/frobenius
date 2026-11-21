module

/-
Run r25, seat L5: the norm level of Theorem F (note Theorem 6.3, step 2), over `ℤ`.

Setting: `u ∈ ℤ[[x_1..x_n]]`, a subspace `U` with `u ∈ C_U + p ^ ξ A` (`WDiv p U (p ^ ξ) u`),
`a = projW U u` (the `U`-part of `u`), `W = span of the classes of a`, `s = dim W`.
`T` is the Cayley-Hamilton polynomial of `a` in `C_W` (monic of degree `p ^ s` in `B[X]`, `T(a) = 0`).

`norm_level_int`: if every nonzero character `φ` of `W` has depth `< ξ` on `a`, then
`p ^ e ∣ T(u)` whenever `(p - 1) e ≤ (p - 1) ξ + p ^ s - 1 + (p - 1) ∑_{φ ≠ 0} charDep a φ`.

Proof: over `O = ℤ[ζ_p]` the twists `z_φ = tw_φ(a)` are `p ^ s` distinct roots of `T`, so
`T = ∏_φ (X - z_φ)` (both monic of degree `p ^ s`, the difference has `p ^ s` roots), and
`T(u) = ∏_φ (u - z_φ)` with `π ^ ((p-1) ξ) ∣ u - a` and `π ^ (1 + (p-1) charDep φ) ∣ a - z_φ`.
No Galois descent is needed: `T` has integer coefficients from the start.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Lower
public import Frobenius.Levels.Basis
public import Frobenius.Levels.Digit
public import Frobenius.Levels.PropP
public import Frobenius.Levels.Flag
public import Frobenius.Levels.Cap
public import Frobenius.Levels.ValTower
public import Frobenius.Levels.TraceCore
public import Frobenius.Levels.TraceFlag

@[expose] public section

-- Port (Mathlib v4.35.0-rc2): restore the v4.33 instance path for `AddCommGroup (ZMod p)`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace FrobLevel

open MvPowerSeries

open scoped Classical

section NormInt

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ}

/-- If `p ^ d` divides the coefficients of `a` at `⟨v, m⟩ ≠ 0`, then
`π ^ (1 + (p - 1) d) ∣ a - tw_v a` over `O`. -/
theorem dvd_sub_tz {O : Type*} [CommRing O] {ζ : O} (hζp : ζ ^ p = 1) {ε : O}
    (hε : (p : O) = (ζ - 1) ^ (p - 1) * ε) (a : MvPowerSeries (Fin n) ℤ) (v : Fin n → ZMod p)
    (d : ℕ) (hdiv : ∀ m, pair v m ≠ 0 → (p : ℤ) ^ d ∣ coeff m a) :
    (C ((ζ - 1) ^ (1 + (p - 1) * d)) : MvPowerSeries (Fin n) O)
      ∣ MvPowerSeries.map (Int.castRingHom O) a
        - tz ζ v (MvPowerSeries.map (Int.castRingHom O) a) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  apply C_dvd_of_coeff
  intro m
  rw [map_sub, coeff_tz, coeff_map, eq_intCast, pow_sum_eq_pow_pair hζp]
  by_cases hm : pair v m = 0
  · rw [hm, ZMod.val_zero, pow_zero, one_mul, sub_self]; exact dvd_zero _
  · obtain ⟨q, hq⟩ := hdiv m hm
    rw [hq, Int.cast_mul, Int.cast_pow, Int.cast_natCast, hε]
    set c := (pair v m).val
    have hg : (∑ j ∈ Finset.range c, ζ ^ j) * (ζ - 1) = ζ ^ c - 1 := geom_sum_mul ζ _
    refine ⟨-(∑ j ∈ Finset.range c, ζ ^ j) * ε ^ d * (q : O), ?_⟩
    have h2 : ζ ^ c = (∑ j ∈ Finset.range c, ζ ^ j) * (ζ - 1) + 1 := by rw [hg]; ring
    rw [h2]
    ring

/-- `π ^ ((p - 1) e) ∣ c` in `O` for an integer `c` forces `p ^ e ∣ c`. -/
theorem int_dvd_of_pi_dvd {O : Type*} [CommRing O] [IsDomain O] {π ε : O} (hπ : Prime π)
    (hε : (p : O) = π ^ (p - 1) * ε) (hεu : IsUnit ε) {c : ℤ} {e : ℕ}
    (h : π ^ ((p - 1) * e) ∣ (c : O)) : (p : ℤ) ^ e ∣ c := by
  have hπp : π ∣ (p : O) := by
    rw [hε]; exact Dvd.dvd.mul_right (dvd_pow_self _ (by have := hp.out.two_le; omega)) _
  induction e with
  | zero => simp
  | succ e ih =>
    have h1 : π ^ ((p - 1) * e) ∣ (c : O) :=
      (pow_dvd_pow _ (Nat.mul_le_mul_left _ (Nat.le_succ e))).trans h
    obtain ⟨c', hc'⟩ := ih h1
    rw [hc'] at h ⊢
    rw [pow_succ]
    refine mul_dvd_mul_left _ ?_
    by_contra hnd
    have hπc := not_dvd_intCast hπ hπp hnd
    apply hπc
    rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, hε, mul_pow, ← pow_mul,
      show (p - 1) * (e + 1) = (p - 1) * e + (p - 1) by ring, pow_add, mul_assoc] at h
    have h3 := (mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).1 h
    have h4 : π ∣ ε ^ e * (c' : O) :=
      (dvd_pow_self π (by have := hp.out.two_le; omega)).trans h3
    rcases hπ.dvd_or_dvd h4 with h5 | h5
    · exact absurd (isUnit_of_dvd_unit (hπ.dvd_of_dvd_pow h5) hεu) hπ.not_isUnit
    · exact h5

/-- Cayley-Hamilton in `C_W`, `W` the span of the classes of `a`. -/
theorem exists_monic_self (a : MvPowerSeries (Fin n) ℤ) :
    ∃ T : Polynomial (MvPowerSeries (Fin n) ℤ), T.Monic ∧ T.natDegree = p ^ rankF p a ∧
      T ∈ BPoly (frob p) ∧ T.eval a = 0 := by
  set W := fullSpace p a
  have ha : a ∈ CW p W := (fullSpace_le_iff p).1 le_rfl
  obtain ⟨T, hm, hd, hB, hT⟩ := exists_monic_eval_eq_zero_of_subring (CW p W) (frobImage_le_CW p W)
    ((digitExps p n).filter (fun e => classVec p e ∈ W)) (fun e => monomial e 1)
    (fun e he => monomial_mem_CW p (Finset.mem_filter.1 he).2)
    (fun x hx => ⟨classPart p x, span_CW p hx⟩) ha
  refine ⟨T, hm, ?_, hB, hT⟩
  rw [hd, card_filter_digitExps]; rfl

open NumberField in
/-- **The norm level** (Theorem F, step 2, at a jump), over `ℤ`. -/
theorem norm_level_int (u : MvPowerSeries (Fin n) ℤ) (U : Submodule (ZMod p) (Fin n → ZMod p))
    (ξ : ℕ) (hU : WDiv p U ((p : ℤ) ^ ξ) u)
    (hlt : ∀ φ : Module.Dual (ZMod p) (fullSpace p (projW p U u)), φ ≠ 0 →
      charDep p (projW p U u) φ < ξ)
    {e : ℕ} (he : (p - 1) * e ≤ (p - 1) * ξ + (p ^ rankF p (projW p U u) - 1)
      + (p - 1) * ∑ φ ∈ Finset.univ.erase (0 : Module.Dual (ZMod p) (fullSpace p (projW p U u))),
        charDep p (projW p U u) φ) :
    ∃ T : Polynomial (MvPowerSeries (Fin n) ℤ), T.Monic ∧
      T.natDegree = p ^ rankF p (projW p U u) ∧ T ∈ BPoly (frob p) ∧
      (p : MvPowerSeries (Fin n) ℤ) ^ e ∣ T.eval u := by
  set a := projW p U u with ha
  set W := fullSpace p a
  obtain ⟨T, hTm, hTd, hTB, hTa⟩ := exists_monic_self p a
  refine ⟨T, hTm, hTd, hTB, ?_⟩
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
  set O := 𝓞 (CyclotomicField p ℚ)
  set ζ := hζK.toInteger
  obtain ⟨εu, hεu⟩ := hpπ
  set ε : O := (εu : O)
  have hε : (p : O) = (ζ - 1) ^ (p - 1) * ε := hεu.symm
  have : IsDomain (MvPowerSeries (Fin n) O) := NoZeroDivisors.to_isDomain _
  have hζp := hζ.pow_eq_one
  set φ : MvPowerSeries (Fin n) ℤ →+* MvPowerSeries (Fin n) O :=
    MvPowerSeries.map (Int.castRingHom O) with hφ
  have hfφ : ∀ x, φ (frob p x) = frob p (φ x) := fun x => by
    simp [hφ, frob_apply, MvPowerSeries.map_expand]
  set G := Module.Dual (ZMod p) W
  set M := secM p W
  set z : G → MvPowerSeries (Fin n) O := fun g => tz ζ (M g) (φ a) with hz
  -- `T` over `O` commutes with the twists
  have hTfix : ∀ (v : Fin n → ZMod p) (x : MvPowerSeries (Fin n) O),
      (T.map φ).eval (tz ζ v x) = tz ζ v ((T.map φ).eval x) := by
    intro v x
    have hmap : (T.map φ).map (tz ζ v) = T.map φ := by
      refine Polynomial.ext fun i => ?_
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      obtain ⟨b, hb⟩ := mem_BPoly_iff.1 hTB i
      rw [← hb, hfφ]
      exact tz_frob hζp v _
    conv_lhs => rw [← hmap]
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have hTO : ∀ g, (T.map φ).eval (z g) = 0 := by
    intro g
    simp only [hz]
    rw [hTfix, Polynomial.eval_map, Polynomial.eval₂_hom, hTa, map_zero, map_zero]
  -- the twists of `a` are distinct
  have hzinj : Function.Injective z := by
    intro g g' hgg'
    by_contra hne
    have h0 : g' - g ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    obtain ⟨m, hm1, hm2⟩ := exists_charDep_witness p h0
    have hcoef := congrArg (coeff m) hgg'
    simp only [hz] at hcoef
    rw [coeff_tz' hζp, coeff_tz' hζp] at hcoef
    have hM : M g' = M g + M (g' - g) := by rw [← map_add]; congr 1; abel
    rw [hM, pair_add_left, pow_val_add hζp, mul_assoc] at hcoef
    have hne0 : ζ ^ (pair (M g) m).val ≠ 0 := pow_ne_zero _ (hζ.ne_zero hp.out.ne_zero)
    have h1 := mul_left_cancel₀ hne0 hcoef
    have hcm : coeff m (φ a) ≠ 0 := by
      rw [hφ, coeff_map, eq_intCast]; exact_mod_cast hm2
    have h2 : ζ ^ (pair (M (g' - g)) m).val = 1 := by
      have := mul_right_cancel₀ hcm (h1.symm.trans (one_mul _).symm)
      exact this
    have h3 := (hζ.pow_eq_one_iff_dvd _).1 h2
    have hz0 : (pair (M (g' - g)) m).val = 0 := Nat.eq_zero_of_dvd_of_lt h3 (ZMod.val_lt _)
    exact hm1 ((ZMod.val_eq_zero _).1 hz0)
  -- `T = ∏_g (X - z g)` over `O`
  have hprod : T.map φ = ∏ g : G, (Polynomial.X - Polynomial.C (z g)) := by
    have hcard : Fintype.card G = p ^ rankF p a := by rw [card_dual]; rfl
    have hm1 : (T.map φ).Monic := hTm.map φ
    have hm2 : (∏ g : G, (Polynomial.X - Polynomial.C (z g))).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun g _ => Polynomial.monic_X_sub_C _
    have hd1 : (T.map φ).natDegree = Fintype.card G := by rw [hTm.natDegree_map, hTd, hcard]
    have hd2 : (∏ g : G, (Polynomial.X - Polynomial.C (z g))).natDegree = Fintype.card G := by
      rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ]
    rw [← sub_eq_zero]
    by_contra hR
    have hlt : (T.map φ - ∏ g : G, (Polynomial.X - Polynomial.C (z g))).natDegree
        < Fintype.card G := by
      have hdeg : (T.map φ - ∏ g : G, (Polynomial.X - Polynomial.C (z g))).degree
          < (T.map φ).degree :=
        Polynomial.degree_sub_lt_left (by rw [Polynomial.degree_eq_natDegree hm1.ne_zero,
          Polynomial.degree_eq_natDegree hm2.ne_zero, hd1, hd2]) hm1.ne_zero (by rw [hm1.leadingCoeff, hm2.leadingCoeff])
      rw [← hd1]
      exact Polynomial.natDegree_lt_natDegree hR hdeg
    exact hR (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hzinj
      (fun g => by
        rw [Polynomial.eval_sub, hTO, Polynomial.eval_prod, zero_sub, neg_eq_zero]
        exact Finset.prod_eq_zero (Finset.mem_univ g) (by simp)) hlt)
  -- divisibility of each factor
  set Cπ : MvPowerSeries (Fin n) O := C (ζ - 1) with hCπ
  have hpF : ∀ j : ℕ, C ((p : O) ^ j) = Cπ ^ ((p - 1) * j) * C (ε ^ j) := fun j => by
    rw [hε, mul_pow, ← pow_mul, map_mul, map_pow]
  have hua : Cπ ^ ((p - 1) * ξ) ∣ φ (u - a) := by
    have : (C ((p : O) ^ ξ) : MvPowerSeries (Fin n) O) ∣ φ (u - a) := by
      apply C_dvd_of_coeff
      intro m
      rw [hφ, coeff_map, eq_intCast, map_sub, ha, coeff_projW]
      split_ifs with hm
      · rw [sub_self, Int.cast_zero]; exact dvd_zero _
      · rw [sub_zero]
        obtain ⟨q, hq⟩ := hU m hm
        exact ⟨(q : O), by rw [hq]; push_cast; ring⟩
    rw [hpF] at this
    exact (Dvd.intro _ rfl).trans this
  have hfac : ∀ g : G, Cπ ^ (if g = 0 then (p - 1) * ξ else 1 + (p - 1) * charDep p a g)
      ∣ φ u - z g := by
    intro g
    have hsplit : φ u - z g = φ (u - a) + (φ a - z g) := by rw [map_sub]; ring
    split_ifs with hg
    · rw [hsplit, hg]
      have : z 0 = φ a := by simp only [hz, map_zero]; exact tz_zero ζ _
      rw [this, sub_self, add_zero]; exact hua
    · rw [hsplit]
      have hd := hlt g hg
      refine dvd_add ((pow_dvd_pow _ ?_).trans hua) ?_
      · have := hp.out.two_le
        have : 1 + (p - 1) * charDep p a g ≤ (p - 1) * (charDep p a g + 1) := by
          rw [mul_add, mul_one]; omega
        exact this.trans (Nat.mul_le_mul_left _ hd)
      · have := dvd_sub_tz p hζp hε a (M g) (charDep p a g)
          (fun m hm => charDep_hdiv p hg m hm)
        rw [map_pow] at this
        exact this
  -- the product
  have hall : Cπ ^ (∑ g : G, if g = 0 then (p - 1) * ξ else 1 + (p - 1) * charDep p a g)
      ∣ φ (T.eval u) := by
    have : φ (T.eval u) = ∏ g : G, (φ u - z g) := by
      rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, hprod, Polynomial.eval_prod]
      simp
    rw [this, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun g _ => hfac g
  have hsum : (∑ g : G, if g = 0 then (p - 1) * ξ else 1 + (p - 1) * charDep p a g)
      = (p - 1) * ξ + (p ^ rankF p a - 1) + (p - 1) * ∑ g ∈ Finset.univ.erase (0 : G), charDep p a g := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : G)), if_pos rfl]
    rw [Finset.sum_congr rfl fun g hg => if_neg (Finset.mem_erase.1 hg).1, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_dual,
      smul_eq_mul, mul_one, Finset.mul_sum, ← add_assoc]
    rfl
  rw [hsum] at hall
  have hall' : Cπ ^ ((p - 1) * e) ∣ φ (T.eval u) := (pow_dvd_pow _ he).trans hall
  -- pull back to `ℤ`
  rw [natCast_pow_eq_C]
  apply C_dvd_of_coeff
  intro m
  refine int_dvd_of_pi_dvd p hπ hε εu.isUnit ?_
  obtain ⟨y, hy⟩ := hall'
  have := congrArg (coeff m) hy
  rw [hφ, coeff_map, eq_intCast, hCπ, ← map_pow, coeff_C_mul] at this
  rw [this]
  exact dvd_mul_right _ _

end NormInt

end FrobLevel
