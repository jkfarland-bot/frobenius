module

/-
Run r25, seat L3: the transfer lemma (ledger R-084, note Theorem `thm:dirichlet`, "second proof").

A Dirichlet series in finitely many primes is a power series in one variable per prime. For
distinct primes `q_0, ..., q_(n-1)`:
* `iota`: extension by zero, `R[[x_0..x_(n-1)]] →+* ArithmeticFunction R`, a ring hom with
  `iota ∘ frob p = E_p ∘ iota` and `res ∘ iota = id`;
* `levelCount_iota`: `L_(iota a)(p, k) = L_a(p, k)` (Dirichlet ring with `E_p` against power
  series with `x_i ↦ x_i ^ p`), whenever `a` has some level identity (every unit does);
* `levelCount_eq_res_of_smooth`: for `f` supported on `{q_i}`-smooth arguments,
  `L_f(p, k) = L_(res f)(p, k)`: every power-series theorem in finitely many variables
  (R-080, R-083, ...) applies to such `f` verbatim.
* Instance: the indicator `ζ_S` of the `S`-smooth numbers, `|S| = n`:
  `L(ζ_S; p, k) + 1 = min(p ^ n, S(p ^ k))` over `ℤ` and `ℤ_[p]` (R-080 (C) transported), and
  the full-rank case of (C2) for every unit supported on `S`-smooth numbers.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Lower
public import Frobenius.Levels.LowerPadic
public import Frobenius.Levels.DirBase
public import Frobenius.Levels.DirMain

@[expose] public section

namespace FrobLevel

namespace Dir

open MvPowerSeries

section Iota

variable {R : Type*} [CommRing R] {n : ℕ} {q : Fin n → ℕ}
variable (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)

/-- Extension by zero of a power series to the Dirichlet ring. -/
noncomputable def iotaFun (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (a : MvPowerSeries (Fin n) R) :
    ArithmeticFunction R :=
  ⟨fun N => if smoothNum q (expOf q N) = N then coeff (expOf q N) a else 0, by
    rw [if_neg]; exact smoothNum_ne_zero hq _⟩

include hinj

theorem iotaFun_smooth (a : MvPowerSeries (Fin n) R) (e : Fin n →₀ ℕ) :
    iotaFun q hq a (smoothNum q e) = coeff e a := by
  show (if smoothNum q (expOf q (smoothNum q e)) = smoothNum q e then
    coeff (expOf q (smoothNum q e)) a else 0) = _
  rw [expOf_smoothNum hq hinj, if_pos rfl]

omit hinj in
theorem iotaFun_of_not (a : MvPowerSeries (Fin n) R) {N : ℕ} (hN : ∀ e, smoothNum q e ≠ N) :
    iotaFun q hq a N = 0 := by
  show (if smoothNum q (expOf q N) = N then coeff (expOf q N) a else 0) = 0
  rw [if_neg (hN _)]

theorem res_iotaFun (a : MvPowerSeries (Fin n) R) : res hq hinj (iotaFun q hq a) = a := by
  ext e; rw [coeff_res, iotaFun_smooth hq hinj]

/-- Extension by zero is a ring hom. -/
noncomputable def iota : MvPowerSeries (Fin n) R →+* ArithmeticFunction R where
  toFun := iotaFun q hq
  map_one' := by
    classical
    ext N
    by_cases hN : ∃ e, smoothNum q e = N
    · obtain ⟨e, rfl⟩ := hN
      rw [iotaFun_smooth hq hinj, coeff_one, ArithmeticFunction.one_apply]
      have : smoothNum q e = 1 ↔ e = 0 := by
        rw [← smoothNum_zero (q := q)]; exact (smoothNum_injective hq hinj).eq_iff
      by_cases h : e = 0
      · rw [if_pos h, if_pos (this.2 h)]
      · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]
    · push Not at hN
      rw [iotaFun_of_not hq _ hN, ArithmeticFunction.one_apply, if_neg]
      intro h1; exact hN 0 (by rw [smoothNum_zero, h1])
  map_mul' a b := by
    ext N
    by_cases hN : ∃ e, smoothNum q e = N
    · obtain ⟨e, rfl⟩ := hN
      show iotaFun q hq (a * b) (smoothNum q e) = (iotaFun q hq a * iotaFun q hq b) (smoothNum q e)
      have h2 : (iotaFun q hq a * iotaFun q hq b) (smoothNum q e) = coeff e (a * b) := by
        rw [← coeff_res hq hinj, map_mul, res_iotaFun, res_iotaFun]
      rw [h2, iotaFun_smooth hq hinj]
    · push Not at hN
      rw [iotaFun_of_not hq _ hN, ArithmeticFunction.mul_apply]
      symm
      apply Finset.sum_eq_zero
      intro x hx
      have hx' := Nat.mem_divisorsAntidiagonal.mp hx
      by_cases h1 : ∃ e, smoothNum q e = x.1
      · by_cases h2 : ∃ e, smoothNum q e = x.2
        · obtain ⟨e1, he1⟩ := h1
          obtain ⟨e2, he2⟩ := h2
          exact absurd (by rw [smoothNum_add, he1, he2, hx'.1]) (hN (e1 + e2))
        · push Not at h2; rw [iotaFun_of_not hq _ h2, mul_zero]
      · push Not at h1; rw [iotaFun_of_not hq _ h1, zero_mul]
  map_zero' := by
    ext N
    show (if smoothNum q (expOf q N) = N then coeff (expOf q N) (0 : MvPowerSeries (Fin n) R)
      else 0) = 0
    simp
  map_add' a b := by
    ext N
    rw [ArithmeticFunction.add_apply]
    show (if smoothNum q (expOf q N) = N then coeff (expOf q N) (a + b) else 0) =
      (if smoothNum q (expOf q N) = N then coeff (expOf q N) a else 0) +
      (if smoothNum q (expOf q N) = N then coeff (expOf q N) b else 0)
    split_ifs <;> simp

theorem iota_apply_smooth (a : MvPowerSeries (Fin n) R) (e : Fin n →₀ ℕ) :
    iota hq hinj a (smoothNum q e) = coeff e a :=
  iotaFun_smooth hq hinj a e

theorem res_iota (a : MvPowerSeries (Fin n) R) : res hq hinj (iota hq hinj a) = a :=
  res_iotaFun hq hinj a

/-- A function supported on `{q_i}`-smooth arguments is the extension of its restriction. -/
theorem iota_res_of_smooth (f : ArithmeticFunction R)
    (hf : ∀ N, f N ≠ 0 → ∃ e, smoothNum q e = N) : iota hq hinj (res hq hinj f) = f := by
  ext N
  by_cases hN : ∃ e, smoothNum q e = N
  · obtain ⟨e, rfl⟩ := hN
    rw [iota_apply_smooth, coeff_res]
  · push Not at hN
    show iotaFun q hq (res hq hinj f) N = f N
    rw [iotaFun_of_not hq _ hN]
    by_contra h
    obtain ⟨e, he⟩ := hf N (Ne.symm h)
    exact hN e he

/-- Extension by zero commutes with the lifts: `iota ∘ frob p = E_p ∘ iota`. -/
theorem iota_frob (p : ℕ) [hp : Fact p.Prime] (a : MvPowerSeries (Fin n) R) :
    iota hq hinj (frob p a) = Ep p (iota hq hinj a) := by
  ext N
  by_cases hN : ∃ e, smoothNum q e = N
  · obtain ⟨e, rfl⟩ := hN
    rw [iota_apply_smooth, ← coeff_res hq hinj, res_Ep, res_iota]
  · push Not at hN
    show iotaFun q hq (frob p a) N = frobPush p (iota hq hinj a) N
    rw [iotaFun_of_not hq _ hN, frobPush_apply]
    symm
    apply Finset.sum_eq_zero
    intro d _
    split_ifs with hd
    · show iotaFun q hq a d = 0
      apply iotaFun_of_not hq
      intro e he
      exact hN (p • e) (by rw [smoothNum_smul, he, hd])
    · rfl

end Iota

/-! ## The transfer lemma for level counts -/

section LevelTransfer

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] {n : ℕ} {q : Fin n → ℕ}
variable (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)

/-- **Transfer lemma.** For a power series `a` with some level identity,
`L_(iota a)(p, k)` in the Dirichlet ring equals `L_a(p, k)` in `R[[x_0..x_(n-1)]]`. -/
theorem levelCount_iota {a : MvPowerSeries (Fin n) R} {k L : ℕ}
    (hex : HasLevel p (frob p) a k L) :
    levelCount p (Ep p) (iota hq hinj a) k = levelCount p (frob p) a k := by
  have hc1 : ∀ b : MvPowerSeries (Fin n) R,
      (iota hq hinj) ((frob p) b) = (Ep p) ((iota hq hinj) b) := fun b => iota_frob hq hinj p b
  have hc2 : ∀ g : ArithmeticFunction R,
      (res hq hinj) ((Ep p) g) = (frob p) ((res hq hinj) g) := fun g => res_Ep hq hinj p g
  have h1 : levelCount p (Ep p) (iota hq hinj a) k ≤ levelCount p (frob p) a k :=
    levelCount_map_le _ hc1 hex
  have hex' : HasLevel p (Ep p) (iota hq hinj a) k L := HasLevel.map _ hc1 hex
  have h2 : levelCount p (frob p) (res hq hinj (iota hq hinj a)) k ≤
      levelCount p (Ep p) (iota hq hinj a) k := levelCount_map_le _ hc2 hex'
  rw [res_iota] at h2
  omega

/-- A unit of a power series ring over `R` with `p ∣ a ^ p - a` has a level identity. -/
theorem hasLevel_kempner_mv [Nontrivial R] (hR : ∀ a : R, (p : R) ∣ a ^ p - a)
    {a : MvPowerSeries (Fin n) R} (ha : IsUnit a) {k : ℕ} (hk : 1 ≤ k) :
    HasLevel p (frob p) a k (kempner p k - 1) := by
  have hfu : a * ↑ha.unit⁻¹ = 1 := ha.mul_val_inv
  have hm := monicAnn_kempner (frob_isFrobLift p hR) (↑ha.unit⁻¹ : MvPowerSeries (Fin n) R) k
  have e : kempner p k - 1 + 1 = kempner p k := Nat.sub_add_cancel (kempner_pos p hk)
  apply MonicAnn.hasLevel (by rw [hfu, sub_self]; exact dvd_zero _)
  rwa [e]

/-- **Transfer lemma, Dirichlet form.** If `f` is a unit supported on `{q_i}`-smooth arguments,
then `L_f(p, k) = L_(res f)(p, k)`. -/
theorem levelCount_eq_res_of_smooth [Nontrivial R] (hR : ∀ a : R, (p : R) ∣ a ^ p - a)
    {f : ArithmeticFunction R} (hf : IsUnit f) (hsupp : ∀ N, f N ≠ 0 → ∃ e, smoothNum q e = N)
    {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) f k = levelCount p (frob p) (res hq hinj f) k := by
  have hu : IsUnit (res hq hinj f) := hf.map (res hq hinj)
  have := levelCount_iota p hq hinj (hasLevel_kempner_mv p hR hu hk)
  rwa [iota_res_of_smooth hq hinj f hsupp] at this

/-- The full-rank case of R-080 (C2) in the Dirichlet ring, over `ℤ`: a unit `f` supported on
`{q_i}`-smooth arguments whose inverse restricts to a full-rank series has
`L_f(p, k) + 1 = min(p ^ n, S(p ^ k))`. -/
theorem levelCount_smooth_fullRank_int {f : ArithmeticFunction ℤ} (hf : IsUnit f)
    (hsupp : ∀ N, f N ≠ 0 → ∃ e, smoothNum q e = N)
    (hu : FullRank p (res hq hinj (↑hf.unit⁻¹ : ArithmeticFunction ℤ))) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) f k + 1 = min (p ^ n) (kempner p k) := by
  rw [levelCount_eq_res_of_smooth p hq hinj (int_pow_sub p) hf hsupp hk]
  exact levelCount_eq_of_fullRank_int p (by rw [← map_mul, hf.mul_val_inv, map_one]) hu hk

/-- The same over `ℤ_[p]`. -/
theorem levelCount_smooth_fullRank_padic {f : ArithmeticFunction ℤ_[p]} (hf : IsUnit f)
    (hsupp : ∀ N, f N ≠ 0 → ∃ e, smoothNum q e = N)
    (hu : FullRank p (res hq hinj (↑hf.unit⁻¹ : ArithmeticFunction ℤ_[p]))) {k : ℕ}
    (hk : 1 ≤ k) :
    levelCount p (Ep p) f k + 1 = min (p ^ n) (kempner p k) := by
  rw [levelCount_eq_res_of_smooth p hq hinj (padicInt_pow_sub p) hf hsupp hk]
  exact levelCount_eq_of_fullRank_padic p (by rw [← map_mul, hf.mul_val_inv, map_one]) hu hk

/-- **R-080 (C) in the Dirichlet ring.** The indicator `ζ_S = iota ζ_n` of the `S`-smooth
numbers, `S = {q_0, ..., q_(n-1)}`, has `L(ζ_S; p, k) + 1 = min(p ^ n, S(p ^ k))` over `ℤ`. -/
theorem levelCount_zetaS_int (n : ℕ) {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) (iota hq hinj (zeta (R := ℤ) n)) k + 1 = min (p ^ n) (kempner p k) := by
  rw [levelCount_iota p hq hinj (hasLevel_kempner_mv p (int_pow_sub p) (isUnit_zeta n) hk)]
  exact FrobLevel.levelCount_zeta_int p n hk

/-- The same over `ℤ_[p]`. -/
theorem levelCount_zetaS_padic (n : ℕ) {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) (iota hq hinj (zeta (R := ℤ_[p]) n)) k + 1 =
      min (p ^ n) (kempner p k) := by
  rw [levelCount_iota p hq hinj (hasLevel_kempner_mv p (padicInt_pow_sub p) (isUnit_zeta n) hk)]
  exact FrobLevel.levelCount_zeta_padic p n hk

include hq hinj in
/-- A unit supported on `{q_i}`-smooth arguments with `p ∤ f(q_i)` for every `i` (so `ρ = r = n`):
`L_f(p, k) + 1 = min(p ^ n, S(p ^ k))` over `ℤ`. -/
theorem levelCount_smooth_int {f : ArithmeticFunction ℤ} (hf : IsUnit f)
    (hsupp : ∀ N, f N ≠ 0 → ∃ e, smoothNum q e = N) (hfq : ∀ i, ¬ (p : ℤ) ∣ f (q i)) {k : ℕ}
    (hk : 1 ≤ k) :
    levelCount p (Ep p) f k + 1 = min (p ^ n) (kempner p k) :=
  levelCount_smooth_fullRank_int p hq hinj hf hsupp
    (fullRank_res hq hinj _ (fun i => not_dvd_inv_apply_prime hf.mul_val_inv (hq i) (hfq i))) hk

include hq hinj in
/-- The same over `ℤ_[p]`. -/
theorem levelCount_smooth_padic {f : ArithmeticFunction ℤ_[p]} (hf : IsUnit f)
    (hsupp : ∀ N, f N ≠ 0 → ∃ e, smoothNum q e = N) (hfq : ∀ i, ¬ (p : ℤ_[p]) ∣ f (q i))
    {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) f k + 1 = min (p ^ n) (kempner p k) :=
  levelCount_smooth_fullRank_padic p hq hinj hf hsupp
    (fullRank_res hq hinj _ (fun i => not_dvd_inv_apply_prime hf.mul_val_inv (hq i) (hfq i))) hk

omit hp in
/-- The indicator `ζ_S` of the `S`-smooth numbers, `S = {q_0, ..., q_(n-1)}`. -/
noncomputable def zetaS (R : Type*) [CommRing R] (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) :
    ArithmeticFunction R := by
  classical
  exact ⟨fun N => if ∃ e, smoothNum q e = N then 1 else 0, by
    rw [if_neg]; rintro ⟨e, he⟩; exact smoothNum_ne_zero hq e he⟩

omit hp hinj in
theorem zetaS_apply (N : ℕ) [Decidable (∃ e, smoothNum q e = N)] :
    zetaS R q hq N = if ∃ e, smoothNum q e = N then 1 else 0 := by
  unfold zetaS; simp only [ArithmeticFunction.coe_mk]; congr

include hq hinj in
/-- **R-080 (C) in the Dirichlet ring**, stated with `ζ_S` itself:
`L(ζ_S; p, k) + 1 = min(p ^ n, S(p ^ k))` over `ℤ`, for every prime `p`, `k ≥ 1`, `n`. -/
theorem levelCount_zetaS_int' {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) (zetaS ℤ q hq) k + 1 = min (p ^ n) (kempner p k) := by
  classical
  refine levelCount_smooth_int p hq hinj ?_ ?_ ?_ hk
  · rw [ArithmeticFunction.isUnit_iff_isUnit_apply_one, zetaS_apply, if_pos ⟨0, smoothNum_zero⟩]
    exact isUnit_one
  · intro N hN
    rw [zetaS_apply] at hN
    by_contra h
    exact hN (if_neg h)
  · intro i
    rw [zetaS_apply, if_pos ⟨Finsupp.single i 1, smoothNum_single i⟩]
    exact not_dvd_of_natAbs_one p rfl

include hq hinj in
/-- The same over `ℤ_[p]`. -/
theorem levelCount_zetaS_padic' {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) (zetaS ℤ_[p] q hq) k + 1 = min (p ^ n) (kempner p k) := by
  classical
  refine levelCount_smooth_padic p hq hinj ?_ ?_ ?_ hk
  · rw [ArithmeticFunction.isUnit_iff_isUnit_apply_one, zetaS_apply, if_pos ⟨0, smoothNum_zero⟩]
    exact isUnit_one
  · intro N hN
    rw [zetaS_apply] at hN
    by_contra h
    exact hN (if_neg h)
  · intro i
    rw [zetaS_apply, if_pos ⟨Finsupp.single i 1, smoothNum_single i⟩]
    exact fun h => PadicInt.p_nonunit (isUnit_of_dvd_one h)

end LevelTransfer

end Dir

end FrobLevel
