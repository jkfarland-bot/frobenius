module

public import Mathlib
public import Frobenius.Mobius.Levels
public import Frobenius.Levels.A1Gen

/-!
# The shape of the levels in Theorem 6.1 (seat L11)

Numbers refer to J. S. Farland, *A proof of a conjecture of Kauers, Krattenthaler and
Müller, and exact level counts for Frobenius lifts* (2026), the larger paper.

`Dir.hasLevel_kempner_any` (A1Gen) proves Theorem 6.1 of the paper over every commutative
ring as a bound on the level, through a monic annihilator of `1/f` given only by existence. This
file proves the shape of the levels as well: over every commutative ring `R`, for every `f` with
`f(1)` a unit and every `k ≥ 1`, there is an identity of level `S(p ^ k) - 1` whose `g_z` vanish
unless `z = p i - 1` with `1 ≤ i ≤ K(p,k)`.

Route. The δ-tower of `exists_monic_tower_weak` (for a weak Frobenius lift, which `E_p` is over
every `R` by `Dir.ep_isWeakFrobLift`) is applied at degree `K = K(p,k)` to `-d`, where
`σ(b) - u ^ p = p d`; with `Q` its `p`-scaled form, `R₀ = Q(X - σ(b))` is monic of degree `K`
over `B = E_p(Dirichlet ring)`, and `P = R₀(X ^ p)` (`Polynomial.expand`) is monic of degree
`p K = S(p ^ k)`, has only exponents divisible by `p`, and has `P(u) ≡ 0 (mod p ^ (K + v_p(K!)))`.
The monic-to-level step (`hasLevel_of_monic_preimage`, `MonicAnn.hasLevel` with the preimages of
the coefficients made explicit) then puts `g_z = -h_{pK - 1 - z}`, which is `0` unless
`p ∣ z + 1`.
-/

@[expose] public section

open Polynomial

namespace FrobLevel

section Shape

variable {A : Type*} [CommRing A]

/-- `FrobLevel.kempner` and `FrobCong.kempner` are the same function. -/
theorem kempner_eq_frobCong (p : ℕ) [Fact p.Prime] (k : ℕ) :
    kempner p k = FrobCong.kempner p k := rfl

/-- `MonicAnn.hasLevel` with the preimages `h i` of the coefficients given explicitly: a monic
`P` of degree `L + 1` with `P.coeff i = σ(h i)` and `p ^ k ∣ P(u)`, for `u` an inverse of `f`
modulo `p ^ k`, gives `p ^ k ∣ 1 - f ∑_{z ≤ L} f ^ z σ(-h (L - z))`. -/
theorem hasLevel_of_monic_preimage {p : ℕ} {σ : A →+* A} {f u : A} {k L : ℕ}
    (hfu : (p : A) ^ k ∣ f * u - 1) (P : A[X]) (hmon : P.Monic) (hdeg : P.natDegree = L + 1)
    (h : ℕ → A) (hh : ∀ i, σ (h i) = P.coeff i) (hP : (p : A) ^ k ∣ P.eval u) :
    (p : A) ^ k ∣ 1 - f * ∑ z ∈ Finset.range (L + 1), f ^ z * σ (- h (L - z)) := by
  have hev : P.eval u = ∑ i ∈ Finset.range (L + 2), P.coeff i * u ^ i := by
    rw [eval_eq_sum_range, hdeg]
  have htop : P.coeff (L + 1) = 1 := by rw [← hdeg]; exact hmon.coeff_natDegree
  have hterm : ∀ i ∈ Finset.range (L + 2),
      f ^ (L + 1) * (P.coeff i * u ^ i) - P.coeff i * f ^ (L + 1 - i) * ((f * u) ^ i - 1)
        = P.coeff i * f ^ (L + 1 - i) := by
    intro i hi
    have hi' : L + 1 = (L + 1 - i) + i := by have := Finset.mem_range.1 hi; omega
    have : f ^ (L + 1) = f ^ (L + 1 - i) * f ^ i := by rw [← pow_add, ← hi']
    rw [this, mul_pow]; ring
  have hR : f ^ (L + 1) * P.eval u
        - ∑ i ∈ Finset.range (L + 2), P.coeff i * f ^ (L + 1 - i) * ((f * u) ^ i - 1)
      = ∑ i ∈ Finset.range (L + 2), P.coeff i * f ^ (L + 1 - i) := by
    rw [hev, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hterm
  have hL : f * ∑ z ∈ Finset.range (L + 1), f ^ z * σ (- h (L - z))
      = - ∑ i ∈ Finset.range (L + 1), P.coeff i * f ^ (L + 1 - i) := by
    rw [Finset.mul_sum, ← Finset.sum_range_reflect (fun i => P.coeff i * f ^ (L + 1 - i)) (L + 1),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' := Finset.mem_range.1 hz
    have e1 : L + 1 - 1 - z = L - z := by omega
    have e2 : L + 1 - (L - z) = z + 1 := by omega
    simp only [e1, e2, map_neg, hh, pow_succ]; ring
  have key : 1 - f * ∑ z ∈ Finset.range (L + 1), f ^ z * σ (- h (L - z))
      = f ^ (L + 1) * P.eval u
        - ∑ i ∈ Finset.range (L + 2), P.coeff i * f ^ (L + 1 - i) * ((f * u) ^ i - 1) := by
    rw [hR, hL, Finset.sum_range_succ _ (L + 1), htop, Nat.sub_self, pow_zero, mul_one]; ring
  rw [key]
  refine dvd_sub (Dvd.dvd.mul_left hP _) (Finset.dvd_sum fun i _ => Dvd.dvd.mul_left ?_ _)
  exact hfu.trans (by simpa using sub_dvd_pow_sub_pow (f * u) 1 i)

/-- The δ-tower in `X ^ p`: for a weak Frobenius lift `σ`, every `K` and every `u`, a monic
`R₀ ∈ B[X]` of degree `K` with `p ^ (K + v_p(K!)) ∣ R₀(u ^ p)`; so `P = R₀(X ^ p)` is monic of
degree `p K`, lies in `B[X ^ p]` and has `p ^ (K + v_p(K!)) ∣ P(u)`. -/
theorem exists_expand_tower {p : ℕ} [hp : Fact p.Prime] [Nontrivial A] {σ : A →+* A}
    (hw : IsWeakFrobLift p σ) (K : ℕ) (u : A) :
    ∃ R₀ : A[X], R₀.Monic ∧ R₀.natDegree = K ∧ R₀ ∈ BPoly σ ∧
      (p : A) ^ (K + padicValNat p K.factorial) ∣ (expand A p R₀).eval u := by
  obtain ⟨b, d, hd⟩ := hw u
  obtain ⟨P', hmon', hdeg', hB', hP'⟩ := exists_monic_tower_weak hw K (- d)
  set Q : A[X] := P'.scaleRoots (p : A) with hQ
  have hQm : Q.Monic := (monic_scaleRoots_iff _).2 hmon'
  have hQd : Q.natDegree = K := by rw [hQ, natDegree_scaleRoots, hdeg']
  have hYm : (X - C (σ b)).Monic := monic_X_sub_C (σ b)
  refine ⟨Q.comp (X - C (σ b)), hQm.comp hYm (by rw [natDegree_X_sub_C]; exact one_ne_zero), ?_,
    comp_mem_BPoly (scaleRoots_mem_BPoly hB' p) (sub_mem (X_mem_BPoly σ) (C_mem_BPoly σ b)), ?_⟩
  · rw [natDegree_comp_eq_of_mul_ne_zero (by rw [hQm.leadingCoeff, hYm.leadingCoeff]; simp),
      hQd, natDegree_X_sub_C, mul_one]
  · rw [expand_eval, eval_comp, eval_sub, eval_X, eval_C]
    have hYu : u ^ p - σ b = (p : A) * (- d) := by linear_combination -hd
    rw [hYu, hQ]
    have := scaleRoots_eval₂_mul (p := P') (RingHom.id A) (- d) (p : A)
    simp only [eval₂_id, RingHom.id_apply] at this
    rw [this, hdeg', pow_add]
    exact mul_dvd_mul_left _ hP'

end Shape

namespace Dir

/-- **Theorem 6.1 of the paper with the shape of the levels**: over every commutative ring
`R`, for every prime `p`, every `k ≥ 1` and every `f` with `f(1)` a unit, there are
`g_z ∈ ArithmeticFunction R` with
`1 ≡ f ∑_{z ≤ S(p^k) - 1} f ^ z E_p(g_z) (mod p ^ k)` (the level form of `HasLevel`) such that
`g_z = 0` unless `z = p i - 1` with `1 ≤ i ≤ K(p,k)`. -/
theorem hasLevel_kempner_shape (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R]
    (f : ArithmeticFunction R) (hf : IsUnit (f 1)) {k : ℕ} (hk : 1 ≤ k) :
    ∃ g : ℕ → ArithmeticFunction R,
      (∀ z, g z ≠ 0 → ∃ i, 1 ≤ i ∧ i ≤ Nat.find (FrobCong.exists_K p k) ∧ z = p * i - 1) ∧
      (p : ArithmeticFunction R) ^ k ∣
        1 - f * ∑ z ∈ Finset.range (kempner p k - 1 + 1), f ^ z * Ep p (g z) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨fun _ => 0, fun z hz => absurd rfl hz, ?_⟩
    have : (1 - f * ∑ z ∈ Finset.range (kempner p k - 1 + 1), f ^ z * (Ep p) 0
        : ArithmeticFunction R) = 0 := by
      ext n; exact Subsingleton.elim _ _
    rw [this]; exact dvd_zero _
  set K := Nat.find (FrobCong.exists_K p k) with hK
  have hSK : kempner p k = p * K := (FrobCong.kempner_eq p k).symm
  have hfu' : IsUnit f := ArithmeticFunction.isUnit_iff_isUnit_apply_one.2 hf
  have hfu : f * ↑hfu'.unit⁻¹ = 1 := hfu'.mul_val_inv
  obtain ⟨R₀, hmon, hdeg, hB, hdvd⟩ :=
    exists_expand_tower (ep_isWeakFrobLift (R := R) p) K (↑hfu'.unit⁻¹)
  rw [mem_BPoly_iff] at hB
  choose h0 hh0 using hB
  set h : ℕ → ArithmeticFunction R := fun i => if p ∣ i then h0 (i / p) else 0 with hh
  have hhP : ∀ i, Ep p (h i) = (expand _ p R₀).coeff i := by
    intro i
    rw [coeff_expand hp.out.pos]
    by_cases hi : p ∣ i
    · simp only [hh, ite_eq_left hi]; exact hh0 _
    · simp only [hh, ite_eq_right hi, map_zero]
  have hPm : (expand _ p R₀).Monic := hmon.expand hp.out.pos
  have hPd : (expand _ p R₀).natDegree = kempner p k - 1 + 1 := by
    rw [natDegree_expand, hdeg, Nat.sub_add_cancel (kempner_pos p hk), hSK, mul_comm]
  have hPu : (p : ArithmeticFunction R) ^ k ∣ (expand _ p R₀).eval (↑hfu'.unit⁻¹) :=
    (pow_dvd_pow _ (Nat.find_spec (FrobCong.exists_K p k))).trans hdvd
  have key := hasLevel_of_monic_preimage (σ := Ep p) (by rw [hfu, sub_self]; exact dvd_zero _)
    (expand _ p R₀) hPm hPd h hhP hPu
  have hL1 : kempner p k - 1 + 1 = p * K := by rw [Nat.sub_add_cancel (kempner_pos p hk), hSK]
  refine ⟨fun z => if z < kempner p k - 1 + 1 then - h (kempner p k - 1 - z) else 0, ?_, ?_⟩
  · intro z hz
    dsimp only at hz
    by_cases hzl : z < kempner p k - 1 + 1
    · rw [ite_eq_left hzl] at hz
      have hz2 : h (kempner p k - 1 - z) ≠ 0 := fun h0 => hz (by rw [h0, neg_zero])
      have hpd : p ∣ kempner p k - 1 - z := by
        by_contra hnd
        exact hz2 (by simp only [hh, ite_eq_right hnd])
      have hsum : kempner p k - 1 - z + (z + 1) = p * K := by omega
      have hpz : p ∣ z + 1 := (Nat.dvd_add_right hpd).mp (hsum ▸ dvd_mul_right p K)
      obtain ⟨i, hi⟩ := hpz
      refine ⟨i, ?_, ?_, by omega⟩
      · rcases Nat.eq_zero_or_pos i with h0 | h0
        · rw [h0, mul_zero] at hi; omega
        · exact h0
      · exact Nat.le_of_mul_le_mul_left (by omega) hp.out.pos
    · exact absurd (ite_eq_right hzl) hz
  · have e : ∑ z ∈ Finset.range (kempner p k - 1 + 1), f ^ z *
        Ep p (if z < kempner p k - 1 + 1 then - h (kempner p k - 1 - z) else 0) =
        ∑ z ∈ Finset.range (kempner p k - 1 + 1), f ^ z * Ep p (- h (kempner p k - 1 - z)) :=
      Finset.sum_congr rfl (fun z hz => by rw [ite_eq_left (Finset.mem_range.mp hz)])
    rw [e]; exact key

/-- **Theorem 6.1 of the paper with the shape of the levels, in the paper's form**: over every
commutative ring `R`, for every `f` with `f(1)` a unit and `k ≥ 1`, there are `g_z` with
`g_z = 0` unless `z = p i - 1`, `1 ≤ i ≤ K(p,k)`, such that for the inverse `u = f⁻¹`,
`u(n) ≡ ∑_{z < S(p ^ k)} (f ^ z * E_p(g_z))(n) (mod p ^ k R)` for every `n`. -/
theorem inv_congr_kempner_shape (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R]
    (f : ArithmeticFunction R) (hf : IsUnit (f 1)) {k : ℕ} (hk : 1 ≤ k) :
    ∃ g : ℕ → ArithmeticFunction R,
      (∀ z, g z ≠ 0 → ∃ i, 1 ≤ i ∧ i ≤ Nat.find (FrobCong.exists_K p k) ∧ z = p * i - 1) ∧
      ∀ u : ArithmeticFunction R, f * u = 1 → ∀ n,
        (p : R) ^ k ∣ (u - ∑ z ∈ Finset.range (kempner p k), f ^ z * Ep p (g z)) n := by
  obtain ⟨g, hshape, hdvd⟩ := hasLevel_kempner_shape p f hf hk
  refine ⟨g, hshape, fun u hfu n => ?_⟩
  rw [Nat.sub_add_cancel (kempner_pos p hk)] at hdvd
  set S := ∑ z ∈ Finset.range (kempner p k), f ^ z * Ep p (g z)
  have e : u - S = u * (1 - f * S) := by
    rw [mul_sub, mul_one, ← mul_assoc, mul_comm u f, hfu, one_mul]
  obtain ⟨E, hE⟩ := hdvd
  have hc : (p : ArithmeticFunction R) ^ k = ((p ^ k : ℕ) : ArithmeticFunction R) := by
    push_cast; rfl
  rw [e, hE, mul_left_comm, hc, natCast_mul_apply]
  push_cast
  exact dvd_mul_right _ _

end Dir

end FrobLevel
