module

/-
Run r25, seat L5: the rank cap `p ^ r_f` and flag invariance `f ↔ 1/f` (note Theorem 6.3, steps 1
and 4; ledger R-083), for power series over any commutative ring `R`.

For a subspace `W ⊆ F_p ^ n` let `C_W` be the series whose monomials have exponent classes in `W`.
* `projW W`: keep the monomials with class in `W`. It is `C_W`-linear (`projW_mul`).
* `WDiv p W c a`: every coefficient of `a` at a class outside `W` is divisible by `c`
  (`c = 0`: `a ∈ C_W`; `c = p ^ (d + 1)`: `a ∈ C_W + p ^ (d + 1) A`).
* `wDiv_of_mul_eq_one`: `f u = 1` and `WDiv W c f` imply `WDiv W c u` (step 4).
* `depthSpace_le_iff`, `fullSpace_le_iff`: `U_d(f) ≤ W ↔ WDiv W (p ^ (d + 1)) f`, `span ≤ W ↔ f ∈ C_W`.
* Flag invariance: `depthSpace_inv`, `fullSpace_inv`, `rankF_inv`, `depthFlag_inv`,
  `flagJump_inv`, `flagValue_inv`.
* The cap: `exists_monic_cap` (an exact monic annihilator of `u = 1/f` of degree `p ^ r_f` in
  `B[X]`, by Cayley-Hamilton in the subring `C_W`), `monicAnn_cap`.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.Digit
public import Frobenius.Levels.PropP
public import Frobenius.Levels.Flag

@[expose] public section

-- Port (Mathlib v4.35.0-rc2): restore the v4.33 instance path for `AddCommGroup (ZMod p)`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace FrobLevel

open MvPowerSeries

open scoped Classical

section Classes

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] {n : ℕ}

theorem classVec_add (a b : Fin n →₀ ℕ) : classVec p (a + b) = classVec p a + classVec p b := by
  funext i; simp [classVec]

theorem classVec_zero : classVec p (0 : Fin n →₀ ℕ) = 0 := by
  funext i; simp [classVec]

theorem classVec_smul_add (q e : Fin n →₀ ℕ) : classVec p (p • q + e) = classVec p e := by
  funext i; simp [classVec]

/-- The low digits `m mod p` of an exponent. -/
noncomputable def lowDigits (m : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => m i % p

/-- The high part `m div p` of an exponent. -/
noncomputable def highPart (m : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => m i / p

theorem split_exp (m : Fin n →₀ ℕ) : p • highPart p m + lowDigits p m = m := by
  ext i; simp [highPart, lowDigits, Nat.div_add_mod]

theorem lowDigits_mem (m : Fin n →₀ ℕ) : lowDigits p m ∈ digitExps p n :=
  (mem_digitExps p n).2 fun i => by simp [lowDigits, Nat.mod_lt _ hp.out.pos]

theorem classVec_lowDigits (m : Fin n →₀ ℕ) : classVec p (lowDigits p m) = classVec p m := by
  conv_rhs => rw [← split_exp p m]
  rw [classVec_smul_add]

theorem coeff_eq_classPart (a : MvPowerSeries (Fin n) R) (m : Fin n →₀ ℕ) :
    coeff m a = coeff (highPart p m) (classPart p a (lowDigits p m)) := by
  rw [coeff_classPart, split_exp]

/-- Every coefficient of `a` at an exponent whose class is outside `W` is divisible by `c`. -/
def WDiv (W : Submodule (ZMod p) (Fin n → ZMod p)) (c : R) (a : MvPowerSeries (Fin n) R) : Prop :=
  ∀ m, classVec p m ∉ W → c ∣ coeff m a

/-- Keep the monomials whose class lies in `W`. -/
noncomputable def projW (W : Submodule (ZMod p) (Fin n → ZMod p)) (a : MvPowerSeries (Fin n) R) :
    MvPowerSeries (Fin n) R :=
  fun m => if classVec p m ∈ W then coeff m a else 0

theorem coeff_projW (W : Submodule (ZMod p) (Fin n → ZMod p)) (a : MvPowerSeries (Fin n) R)
    (m : Fin n →₀ ℕ) : coeff m (projW p W a) = if classVec p m ∈ W then coeff m a else 0 := rfl

variable {p}

theorem projW_add (W : Submodule (ZMod p) (Fin n → ZMod p)) (a b : MvPowerSeries (Fin n) R) :
    projW p W (a + b) = projW p W a + projW p W b := by
  ext m; simp only [coeff_projW, map_add]; split_ifs <;> simp

theorem projW_C_mul (W : Submodule (ZMod p) (Fin n → ZMod p)) (c : R) (a : MvPowerSeries (Fin n) R) :
    projW p W (C c * a) = C c * projW p W a := by
  ext m; simp only [coeff_projW, coeff_C_mul]; split_ifs <;> simp

theorem projW_one (W : Submodule (ZMod p) (Fin n → ZMod p)) :
    projW p W (1 : MvPowerSeries (Fin n) R) = 1 := by
  ext m
  rw [coeff_projW, coeff_one]
  by_cases h : m = 0
  · subst h; rw [if_pos (by rw [classVec_zero]; exact W.zero_mem)]
  · rw [if_neg h]; split_ifs <;> rfl

/-- `projW` is `C_W`-linear. -/
theorem projW_mul (W : Submodule (ZMod p) (Fin n → ZMod p)) {c : MvPowerSeries (Fin n) R}
    (hc : WDiv p W 0 c) (a : MvPowerSeries (Fin n) R) :
    projW p W (c * a) = c * projW p W a := by
  classical
  have hc' : ∀ i, coeff i c ≠ 0 → classVec p i ∈ W := fun i hi => by
    by_contra h; exact hi (zero_dvd_iff.1 (hc i h))
  ext m
  rw [coeff_projW, coeff_mul, coeff_mul]
  split_ifs with hm
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_projW]
    by_cases h0 : coeff x.1 c = 0
    · simp [h0]
    · have h1 := hc' _ h0
      have h2 : classVec p x.2 ∈ W := by
        have hsum : classVec p m = classVec p x.1 + classVec p x.2 := by
          rw [← classVec_add, (Finset.HasAntidiagonal.mem_antidiagonal.1 hx)]
        have := W.sub_mem hm h1
        rwa [hsum, add_sub_cancel_left] at this
      rw [if_pos h2]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_projW]
    by_cases h0 : coeff x.1 c = 0
    · simp [h0]
    · have h1 := hc' _ h0
      have h2 : classVec p x.2 ∉ W := by
        intro h2
        apply hm
        rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hx, classVec_add]
        exact W.add_mem h1 h2
      rw [if_neg h2, mul_zero]

theorem wDiv_projW (W : Submodule (ZMod p) (Fin n → ZMod p)) (a : MvPowerSeries (Fin n) R) :
    WDiv p W 0 (projW p W a) := fun m hm => by
  rw [coeff_projW, if_neg hm]

/-- **Step 4 of the note's Theorem 6.3.** If `f u = 1` and `f ∈ C_W + c A` (in the sense of
`WDiv`), then `u ∈ C_W + c A`. With `c = 0` this says `C_W` contains the inverses of its units. -/
theorem wDiv_of_mul_eq_one {W : Submodule (ZMod p) (Fin n → ZMod p)} {c : R}
    {f u : MvPowerSeries (Fin n) R} (hfu : f * u = 1) (hf : WDiv p W c f) : WDiv p W c u := by
  set g0 := projW p W f with hg0
  have hdiff : (C c : MvPowerSeries (Fin n) R) ∣ f - g0 := by
    refine C_dvd_of_coeff fun m => ?_
    rw [map_sub, hg0, coeff_projW]
    split_ifs with hm
    · rw [sub_self]; exact dvd_zero _
    · rw [sub_zero]; exact hf m hm
  obtain ⟨g, hg⟩ := hdiff
  have hf' : f = g0 + C c * g := by rw [← hg]; ring
  have hg0W : WDiv p W 0 g0 := wDiv_projW W f
  -- `projW (f u) = 1`
  have h1 : g0 * projW p W u + C c * projW p W (g * u) = 1 := by
    have := congrArg (projW p W) hfu
    rw [projW_one, hf', add_mul, projW_add, projW_mul W hg0W, mul_assoc, projW_C_mul] at this
    exact this
  have h2 : g0 * u + C c * (g * u) = 1 := by rw [← hfu, hf']; ring
  have h3 : g0 * (u - projW p W u) = C c * (projW p W (g * u) - g * u) := by
    linear_combination h2 - h1
  have h4 : u - projW p W u
      = C c * (u * (projW p W (g * u) - g * u) + u * g * (u - projW p W u)) := by
    have hu : u * f = 1 := by rw [mul_comm]; exact hfu
    calc u - projW p W u = (u * f) * (u - projW p W u) := by rw [hu, one_mul]
      _ = u * (g0 * (u - projW p W u)) + C c * (u * g * (u - projW p W u)) := by rw [hf']; ring
      _ = _ := by rw [h3]; ring
  intro m hm
  have : coeff m (u - projW p W u) = coeff m u := by
    rw [map_sub, coeff_projW, if_neg hm, sub_zero]
  rw [← this, h4, coeff_C_mul]
  exact dvd_mul_right _ _

variable (p)

theorem natCast_pow_eq_C (d : ℕ) :
    ((p : MvPowerSeries (Fin n) R) ^ d) = C ((p : R) ^ d) := by
  rw [map_pow, map_natCast]

/-- `U_d(f) ≤ W` iff `f ∈ C_W + p ^ (d + 1) A`. -/
theorem depthSpace_le_iff {W : Submodule (ZMod p) (Fin n → ZMod p)} {f : MvPowerSeries (Fin n) R}
    {d : ℕ} : depthSpace p f d ≤ W ↔ WDiv p W ((p : R) ^ (d + 1)) f := by
  constructor
  · intro h m hm
    rw [coeff_eq_classPart p f m]
    set e := lowDigits p m
    have he : classVec p e ∉ W := by rwa [classVec_lowDigits]
    have hdiv : (p : MvPowerSeries (Fin n) R) ^ (d + 1) ∣ classPart p f e := by
      by_contra hnd
      have he0 : e ≠ 0 := by
        intro h0; apply he; rw [h0, classVec_zero]; exact W.zero_mem
      exact he (h (Submodule.subset_span ⟨e, ⟨lowDigits_mem p m, he0, hnd⟩, rfl⟩))
    rw [natCast_pow_eq_C] at hdiv
    obtain ⟨q, hq⟩ := hdiv
    rw [hq, coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    refine Submodule.span_le.2 ?_
    rintro _ ⟨κ, ⟨_, _, hnd⟩, rfl⟩
    by_contra hW
    apply hnd
    rw [natCast_pow_eq_C]
    refine C_dvd_of_coeff fun q => ?_
    rw [coeff_classPart]
    exact h _ (by rwa [classVec_smul_add])

/-- The span of all classes of `f` is `≤ W` iff `f ∈ C_W`. -/
theorem fullSpace_le_iff {W : Submodule (ZMod p) (Fin n → ZMod p)} {f : MvPowerSeries (Fin n) R} :
    fullSpace p f ≤ W ↔ WDiv p W 0 f := by
  constructor
  · intro h m hm
    rw [coeff_eq_classPart p f m, zero_dvd_iff]
    set e := lowDigits p m
    have he : classVec p e ∉ W := by rwa [classVec_lowDigits]
    have hz : classPart p f e = 0 := by
      by_contra hnz
      have he0 : e ≠ 0 := by
        intro h0; apply he; rw [h0, classVec_zero]; exact W.zero_mem
      exact he (h (Submodule.subset_span ⟨e, ⟨lowDigits_mem p m, he0, hnz⟩, rfl⟩))
    rw [hz, map_zero]
  · intro h
    refine Submodule.span_le.2 ?_
    rintro _ ⟨κ, ⟨_, _, hnz⟩, rfl⟩
    by_contra hW
    apply hnz
    ext q
    rw [coeff_classPart, map_zero]
    exact zero_dvd_iff.1 (h _ (by rwa [classVec_smul_add]))

variable {p}

/-- Flag invariance: `U_d(1/f) = U_d(f)`. -/
theorem depthSpace_inv {f u : MvPowerSeries (Fin n) R} (hfu : f * u = 1) (d : ℕ) :
    depthSpace p u d = depthSpace p f d := by
  have huf : u * f = 1 := by rw [mul_comm]; exact hfu
  refine le_antisymm ?_ ?_
  · exact (depthSpace_le_iff p).2 (wDiv_of_mul_eq_one hfu ((depthSpace_le_iff p).1 le_rfl))
  · exact (depthSpace_le_iff p).2 (wDiv_of_mul_eq_one huf ((depthSpace_le_iff p).1 le_rfl))

theorem fullSpace_inv {f u : MvPowerSeries (Fin n) R} (hfu : f * u = 1) :
    fullSpace p u = fullSpace p f := by
  have huf : u * f = 1 := by rw [mul_comm]; exact hfu
  refine le_antisymm ?_ ?_
  · exact (fullSpace_le_iff p).2 (wDiv_of_mul_eq_one hfu ((fullSpace_le_iff p).1 le_rfl))
  · exact (fullSpace_le_iff p).2 (wDiv_of_mul_eq_one huf ((fullSpace_le_iff p).1 le_rfl))

theorem rankF_inv {f u : MvPowerSeries (Fin n) R} (hfu : f * u = 1) : rankF p u = rankF p f := by
  unfold rankF; rw [fullSpace_inv hfu]

theorem depthFlag_inv {f u : MvPowerSeries (Fin n) R} (hfu : f * u = 1) (j : ℕ) :
    depthFlag p u j = depthFlag p f j := by
  unfold depthFlag; rw [show depthSpace p u = depthSpace p f from funext (depthSpace_inv hfu)]

theorem flagJump_inv {f u : MvPowerSeries (Fin n) R} (hfu : f * u = 1) (j : ℕ) :
    flagJump p u j = flagJump p f j := by
  unfold flagJump; rw [show depthFlag p u = depthFlag p f from funext (depthFlag_inv hfu)]

/-- Flag invariance of the right side of R-083: the formula for `f` and for `1/f` agree. -/
theorem flagValue_inv {f u : MvPowerSeries (Fin n) R} (hfu : f * u = 1) (k : ℕ) :
    flagValue p u k = flagValue p f k := by
  unfold flagValue
  rw [rankF_inv hfu, show flagJump p u = flagJump p f from funext (flagJump_inv hfu)]

end Classes

/-! ## The cap -/

section Cap

open Polynomial

variable {A : Type*} [CommRing A] [Nontrivial A]

/-- Cayley-Hamilton in a subring `C ⊇ B` spanned over `B` by `#t` elements of `C`. -/
theorem exists_monic_eval_eq_zero_of_subring {σ : A →+* A} (Cs : Subring A)
    (hBC : frobImage σ ≤ Cs) {ι : Type*} (t : Finset ι) (b : ι → A) (hb : ∀ i ∈ t, b i ∈ Cs)
    (hs : ∀ a ∈ Cs, ∃ c : ι → A, a = ∑ i ∈ t, σ (c i) * b i) {u : A} (hu : u ∈ Cs) :
    ∃ P : A[X], P.Monic ∧ P.natDegree = t.card ∧ P ∈ BPoly σ ∧ P.eval u = 0 := by
  classical
  set B : Subring A := frobImage σ
  let _ : Algebra B Cs := (Subring.inclusion hBC).toAlgebra
  have hsmul : ∀ (x : B) (y : Cs), ((x • y : Cs) : A) = (x : A) * (y : A) := fun _ _ => rfl
  set bC : ι → Cs := fun i => if h : b i ∈ Cs then ⟨b i, h⟩ else 0 with hbC
  have hbCi : ∀ i ∈ t, ((bC i : Cs) : A) = b i := fun i hi => by simp [hbC, hb i hi]
  have hspan : Submodule.span B (↑(t.image bC) : Set Cs) = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    obtain ⟨c, hc⟩ := hs a a.2
    have ha : a = ∑ i ∈ t, (⟨σ (c i), c i, rfl⟩ : B) • bC i := by
      apply Subtype.ext
      rw [hc, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hsmul, hbCi i hi]
    rw [ha]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span (by simpa using ⟨i, hi, rfl⟩)
  have hfin : Module.Finite B Cs := ⟨⟨t.image bC, hspan⟩⟩
  obtain ⟨q, hqm, hqd, hq⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero B (Algebra.lmul B Cs ⟨u, hu⟩)
  have hrank : (⊤ : Submodule B Cs).spanFinrank ≤ t.card := by
    rw [← hspan]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)).trans ?_
    rw [Set.ncard_coe_finset]
    exact Finset.card_image_le
  have hev : (q.map B.subtype).eval u = 0 := by
    have h2 := Polynomial.aeval_algHom_apply (Algebra.lmul B Cs) ⟨u, hu⟩ q
    rw [hq] at h2
    have h3 : Polynomial.aeval (⟨u, hu⟩ : Cs) q = 0 := by
      have := congrArg (fun φ : Module.End B Cs => φ 1) h2
      simpa using this.symm
    have h4 := congrArg Cs.subtype h3
    rw [map_zero, aeval_def, hom_eval₂] at h4
    rw [eval_map]
    have h5 : Cs.subtype.comp (algebraMap B Cs) = B.subtype := by ext; rfl
    rw [h5] at h4
    exact h4
  have hPm : (q.map B.subtype).Monic := hqm.map _
  have hPB : q.map B.subtype ∈ BPoly σ := by
    rw [mem_BPoly_iff]; intro i; rw [Polynomial.coeff_map]; exact (q.coeff i).2
  refine ⟨q.map B.subtype * Polynomial.X ^ (t.card - q.natDegree), hPm.mul (monic_X_pow _), ?_,
    mul_mem hPB (pow_mem (X_mem_BPoly σ) _), by rw [eval_mul, hev, zero_mul]⟩
  rw [hPm.natDegree_mul (monic_X_pow _), hqm.natDegree_map, natDegree_X_pow]
  omega

end Cap

section CapSeries

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] {n : ℕ}

/-- The subring `C_W`. -/
noncomputable def CW (W : Submodule (ZMod p) (Fin n → ZMod p)) : Subring (MvPowerSeries (Fin n) R) where
  carrier := {a | WDiv p W 0 a}
  mul_mem' := by
    intro a b ha hb m hm
    rw [zero_dvd_iff, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    by_cases h1 : classVec p x.1 ∈ W
    · by_cases h2 : classVec p x.2 ∈ W
      · exact absurd (by rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hx, classVec_add]; exact W.add_mem h1 h2) hm
      · rw [zero_dvd_iff.1 (hb _ h2), mul_zero]
    · rw [zero_dvd_iff.1 (ha _ h1), zero_mul]
  one_mem' := by
    intro m hm
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (by rw [classVec_zero]; exact W.zero_mem)
    rw [coeff_one, if_neg hm0]
  add_mem' := by
    intro a b ha hb m hm
    rw [map_add]; exact dvd_add (ha m hm) (hb m hm)
  zero_mem' := by intro m _; rw [map_zero]
  neg_mem' := by
    intro a ha m hm
    rw [map_neg]; exact (dvd_neg).2 (ha m hm)

theorem mem_CW {W : Submodule (ZMod p) (Fin n → ZMod p)} {a : MvPowerSeries (Fin n) R} :
    a ∈ CW p W ↔ WDiv p W 0 a := Iff.rfl

theorem frobImage_le_CW (W : Submodule (ZMod p) (Fin n → ZMod p)) :
    frobImage (frob p : MvPowerSeries (Fin n) R →+* MvPowerSeries (Fin n) R) ≤ CW p W := by
  rintro _ ⟨a, rfl⟩ m hm
  rw [zero_dvd_iff]
  by_contra hne
  apply hm
  have hdvd : ∀ i, p ∣ m i := by
    intro i; by_contra hi; exact hne (coeff_frob_of_not_dvd p a hi)
  have : classVec p m = 0 := by
    funext i
    simp only [classVec, Pi.zero_apply]
    exact (ZMod.natCast_eq_zero_iff _ _).2 (hdvd i)
  rw [this]; exact W.zero_mem

theorem monomial_mem_CW {W : Submodule (ZMod p) (Fin n → ZMod p)} {e : Fin n →₀ ℕ}
    (he : classVec p e ∈ W) : (monomial e 1 : MvPowerSeries (Fin n) R) ∈ CW p W := by
  intro m hm
  have hme : m ≠ e := by rintro rfl; exact hm he
  rw [coeff_monomial, if_neg hme]

/-- `C_W` is spanned over `B` by the `x ^ e`, `e` a digit vector with class in `W`. -/
theorem span_CW {W : Submodule (ZMod p) (Fin n → ZMod p)}
    {a : MvPowerSeries (Fin n) R} (ha : a ∈ CW p W) :
    a = ∑ e ∈ (digitExps p n).filter (fun e => classVec p e ∈ W),
      frob p (classPart p a e) * monomial e 1 := by
  rw [Finset.sum_filter]
  conv_lhs => rw [eq_sum_digit p a]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs with he
  · rfl
  · have : classPart p a e = 0 := by
      ext q
      rw [coeff_classPart, map_zero]
      exact zero_dvd_iff.1 (ha _ (by rwa [classVec_smul_add]))
    rw [this, map_zero, zero_mul]

/-- `#{e ∈ [0, p) ^ n : e mod p ∈ W} = p ^ dim W`. -/
theorem card_filter_digitExps (W : Submodule (ZMod p) (Fin n → ZMod p)) :
    ((digitExps p n).filter (fun e => classVec p e ∈ W)).card = p ^ Module.finrank (ZMod p) W := by
  classical
  have hW : ((Finset.univ : Finset (Fin n → ZMod p)).filter (· ∈ W)).card
      = p ^ Module.finrank (ZMod p) W := by
    rw [← Fintype.card_subtype, @Module.card_eq_pow_finrank (ZMod p) W, ZMod.card]
  rw [← hW]
  refine Finset.card_bij' (fun e _ => classVec p e)
    (fun v _ => Finsupp.equivFunOnFinite.symm fun i => (v i).val) ?_ ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_filter] at he ⊢
    exact ⟨Finset.mem_univ _, he.2⟩
  · intro v hv
    simp only [Finset.mem_filter] at hv ⊢
    refine ⟨(mem_digitExps p n).2 fun i => by simp [ZMod.val_lt], ?_⟩
    convert hv.2 using 1
    funext i; simp [classVec]
  · intro e he
    have he' := (mem_digitExps p n).1 (Finset.mem_filter.1 he).1
    ext i
    simp [classVec, ZMod.val_natCast, Nat.mod_eq_of_lt (he' i)]
  · intro v _
    funext i; simp [classVec]

/-- **The cap** (note Theorem 6.3, step 1): for `f u = 1` in `R[[x_1..x_n]]` there is a monic
`P ∈ B[X]` of degree exactly `p ^ r_f` with `P(u) = 0`. -/
theorem exists_monic_cap [Nontrivial R] {f u : MvPowerSeries (Fin n) R} (hfu : f * u = 1) :
    ∃ P : Polynomial (MvPowerSeries (Fin n) R), P.Monic ∧ P.natDegree = p ^ rankF p f ∧
      P ∈ BPoly (frob p) ∧ P.eval u = 0 := by
  classical
  set W := fullSpace p f
  have hu : u ∈ CW p W := wDiv_of_mul_eq_one hfu ((fullSpace_le_iff p).1 le_rfl)
  obtain ⟨P, hm, hd, hB, hP⟩ := exists_monic_eval_eq_zero_of_subring (CW p W) (frobImage_le_CW p W)
    ((digitExps p n).filter (fun e => classVec p e ∈ W)) (fun e => monomial e 1)
    (fun e he => monomial_mem_CW p (Finset.mem_filter.1 he).2)
    (fun a ha => ⟨classPart p a, span_CW p ha⟩) hu
  refine ⟨P, hm, ?_, hB, hP⟩
  rw [hd, card_filter_digitExps]; rfl

theorem monicAnn_cap [Nontrivial R] {f u : MvPowerSeries (Fin n) R} (hfu : f * u = 1) (k : ℕ) :
    MonicAnn p (frob p) u k (p ^ rankF p f) := by
  obtain ⟨P, hm, hd, hB, hP⟩ := exists_monic_cap p hfu
  exact ⟨P, hm, hd, hB, by rw [hP]; exact dvd_zero _⟩

end CapSeries

end FrobLevel
