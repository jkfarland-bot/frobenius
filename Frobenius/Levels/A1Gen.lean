module

/-
Run r25, seat L9: Theorem A1 over every commutative ring (note Theorem `thm:A1`, R-056), and the
discharge of the level-identity hypothesis of L7's `Dir.levelCount_eq_max_res_general`.

* `IsWeakFrobLift p σ`: every `a ^ p` is congruent modulo `p` to some element of `σ(A)`.
  A Frobenius lift is one (`IsFrobLift.weak`).
* `exists_monic_tower_weak`, `monicAnn_kempner_weak`: the δ-tower of L1 (`exists_monic_tower`)
  needs only the weak property: for every `u` there is a monic `P ∈ B[X]` of degree `m` with
  `p ^ v_p(m!) ∣ P(u)`, hence a monic annihilator modulo `p ^ k` of degree `S(p ^ k)`.
* `Dir.ep_isWeakFrobLift`: over EVERY commutative ring `R`, `E_p(f^p) ≡ f^(*p)` modulo `p`
  in the Dirichlet ring, with `f^p` the pointwise power (`ptPow`). No hypothesis on `R`.
* `Dir.hasLevel_kempner_any`, `Dir.levelCount_add_one_le_kempner_any`: Theorem A1 over every
  commutative ring: `L_f(p, k) + 1 ≤ S(p ^ k)` for every `f` with `f(1)` a unit, `k ≥ 1`.
* `Dir.levelCount_eq_max_res_unit`: L7's reduction to finitely many variables with the
  hypothesis `HasLevel` discharged: over every `R` with `R / p^k R` finite, every `f` with
  `f(1)` a unit.
* `Dir.levelCount_eq_max_res_numberField`: the same over the ring of integers of any number
  field (for instance `ℤ[χ] = 𝓞(ℚ(ζ_m))`), with the finiteness proved.

Lean v4.33.1 with Mathlib. No sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.DirBase
public import Frobenius.Levels.DirMain
public import Frobenius.Levels.Cor

@[expose] public section

namespace FrobLevel

section Weak

open Polynomial

variable {A : Type*} [CommRing A]

/-- Weak Frobenius lift: every `p`-th power is congruent modulo `p` to an element of `σ(A)`. -/
def IsWeakFrobLift (p : ℕ) (σ : A →+* A) : Prop := ∀ a : A, ∃ b : A, (p : A) ∣ σ b - a ^ p

theorem IsFrobLift.weak {p : ℕ} {σ : A →+* A} (h : IsFrobLift p σ) : IsWeakFrobLift p σ :=
  fun a => ⟨a, h a⟩

variable [Nontrivial A]

/-- The δ-tower with a weak lift: for every `m` and `u` a monic `P ∈ B[X]` of degree `m` with
`p ^ v_p(m!) ∣ P(u)`. -/
theorem exists_monic_tower_weak {p : ℕ} [hp : Fact p.Prime] {σ : A →+* A}
    (h : IsWeakFrobLift p σ) (m : ℕ) : ∀ u : A, ∃ P : A[X], P.Monic ∧ P.natDegree = m ∧
      P ∈ BPoly σ ∧ (p : A) ^ (padicValNat p m.factorial) ∣ P.eval u := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro u
  by_cases hq : m / p = 0
  · refine ⟨X ^ m, monic_X_pow m, natDegree_X_pow m, pow_mem (X_mem_BPoly σ) m, ?_⟩
    have : padicValNat p m.factorial = 0 := by
      rw [padicValNat_factorial_div p m, hq]; simp
    rw [this, pow_zero]; exact one_dvd _
  · have hp1 := hp.out.one_lt
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => hq (by simp [h0])
    have hlt : m / p < m := Nat.div_lt_self hm0 hp1
    obtain ⟨b, d, hd⟩ := h u
    obtain ⟨P', hmon', hdeg', hB', hP'⟩ := ih (m / p) hlt (- d)
    set Q : A[X] := P'.scaleRoots (p : A) with hQ
    set Y : A[X] := X ^ p - C (σ b) with hY
    have hYm : Y.Monic := monic_X_pow_sub_C (σ b) hp.out.ne_zero
    have hYd : Y.natDegree = p := natDegree_X_pow_sub_C
    have hQm : Q.Monic := (monic_scaleRoots_iff _).2 hmon'
    have hQd : Q.natDegree = m / p := by rw [hQ, natDegree_scaleRoots, hdeg']
    have hQYm : (Q.comp Y).Monic := hQm.comp hYm (by rw [hYd]; exact hp.out.ne_zero)
    have hQYd : (Q.comp Y).natDegree = m / p * p := by
      rw [natDegree_comp_eq_of_mul_ne_zero (by rw [hQm.leadingCoeff, hYm.leadingCoeff]; simp),
        hQd, hYd]
    refine ⟨X ^ (m % p) * Q.comp Y, (monic_X_pow _).mul hQYm, ?_, ?_, ?_⟩
    · rw [(monic_X_pow _).natDegree_mul hQYm, natDegree_X_pow, hQYd]
      rw [Nat.mul_comm (m / p) p]; exact Nat.mod_add_div m p
    · exact mul_mem (pow_mem (X_mem_BPoly σ) _)
        (comp_mem_BPoly (scaleRoots_mem_BPoly hB' p)
          (sub_mem (pow_mem (X_mem_BPoly σ) _) (C_mem_BPoly σ b)))
    · have hYu : Y.eval u = (p : A) * (- d) := by
        rw [hY, eval_sub, eval_pow, eval_X, eval_C]; linear_combination -hd
      have hev : (X ^ (m % p) * Q.comp Y).eval u
          = u ^ (m % p) * ((p : A) ^ (m / p) * P'.eval (- d)) := by
        rw [eval_mul, eval_pow, eval_X, eval_comp, hYu, hQ]
        have := scaleRoots_eval₂_mul (p := P') (RingHom.id A) (- d) (p : A)
        simp only [eval₂_id, RingHom.id_apply] at this
        rw [this, hdeg']
      rw [hev, padicValNat_factorial_div p m, pow_add]
      exact Dvd.dvd.mul_left (mul_dvd_mul_left _ hP') _

/-- Kempner bound with a weak lift. -/
theorem monicAnn_kempner_weak {p : ℕ} [Fact p.Prime] {σ : A →+* A} (h : IsWeakFrobLift p σ)
    (u : A) (k : ℕ) : MonicAnn p σ u k (kempner p k) := by
  obtain ⟨P, hm, hd, hB, hP⟩ := exists_monic_tower_weak h (kempner p k) u
  exact ⟨P, hm, hd, hB, (pow_dvd_pow _ (kempner_spec p k)).trans hP⟩

end Weak

namespace Dir

section AnyRing

variable {R : Type*} [CommRing R]

/-- The pointwise `p`-th power of an arithmetic function. -/
def ptPow (p : ℕ) (hp0 : p ≠ 0) (f : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => f n ^ p, by simp [hp0]⟩

theorem ptPow_apply (p : ℕ) (hp0 : p ≠ 0) (f : ArithmeticFunction R) (n : ℕ) :
    ptPow p hp0 f n = f n ^ p := rfl

/-- **Frobenius congruence over every commutative ring** (note Theorem `thm:frob` with the
pointwise power): `E_p(f^p) ≡ f^(*p)` modulo `p`. So `E_p` is a weak Frobenius lift of the
Dirichlet ring over every `R`, with no hypothesis `p ∣ a ^ p - a`. -/
theorem ep_ptPow_congr (p : ℕ) [hp : Fact p.Prime] (f : ArithmeticFunction R) :
    (p : ArithmeticFunction R) ∣ Ep p (ptPow p hp.out.ne_zero f) - f ^ p := by
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
  rw [key, sub_apply', map_sub, sub_eq_zero]
  have h1 : π ((Ep p (ptPow p hp.out.ne_zero f)) n)
      = frobPush p (mapHom π (ptPow p hp.out.ne_zero f)) n := by
    rw [← mapHom_frobPush]; rfl
  have h2 : π ((f ^ p) n) = ((mapHom π f) ^ p) n := by
    rw [← map_pow]; rfl
  rw [h1, h2, frob_apply' p, frobPush_apply]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs
  · rw [mapHom_apply, mapHom_apply, ptPow_apply, map_pow]
  · rfl

theorem ep_isWeakFrobLift (p : ℕ) [hp : Fact p.Prime] :
    IsWeakFrobLift p (Ep p : ArithmeticFunction R →+* ArithmeticFunction R) :=
  fun f => ⟨ptPow p hp.out.ne_zero f, ep_ptPow_congr p f⟩

/-- **Theorem A1 over every commutative ring**: every unit `f` of the Dirichlet ring has a
level identity at level `S(p ^ k) - 1`. -/
theorem hasLevel_kempner_any (p : ℕ) [hp : Fact p.Prime] (f : ArithmeticFunction R)
    (hf : IsUnit f) {k : ℕ} (hk : 1 ≤ k) : HasLevel p (Ep p) f k (kempner p k - 1) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨fun _ => 0, ?_⟩
    have : (1 - f * ∑ z ∈ Finset.range (kempner p k - 1 + 1), f ^ z * (Ep p) 0
        : ArithmeticFunction R) = 0 := by
      ext n; exact Subsingleton.elim _ _
    rw [this]; exact dvd_zero _
  have hfu : f * ↑hf.unit⁻¹ = 1 := hf.mul_val_inv
  have hm := monicAnn_kempner_weak (ep_isWeakFrobLift p)
    (↑hf.unit⁻¹ : ArithmeticFunction R) k
  have e : kempner p k - 1 + 1 = kempner p k := Nat.sub_add_cancel (kempner_pos p hk)
  apply MonicAnn.hasLevel (by rw [hfu, sub_self]; exact dvd_zero _)
  rwa [e]

/-- Theorem A1 in the note's wording: `f(1)` a unit gives `L_f(p, k) + 1 ≤ S(p ^ k)`. -/
theorem levelCount_add_one_le_kempner_any (p : ℕ) [hp : Fact p.Prime] (f : ArithmeticFunction R)
    (hf : IsUnit (f 1)) {k : ℕ} (hk : 1 ≤ k) : levelCount p (Ep p) f k + 1 ≤ kempner p k := by
  have h := levelCount_le (hasLevel_kempner_any p f
    (ArithmeticFunction.isUnit_iff_isUnit_apply_one.2 hf) hk)
  have := kempner_pos p hk
  omega

/-- **L7's reduction with the level-identity hypothesis discharged**: over every commutative
ring `R` with `R / p^k R` finite and every `f` with `f(1)` a unit, `L_f(p, k)` is the largest
level count of a restriction `res_q f` to finitely many primes, and it is attained. -/
theorem levelCount_eq_max_res_unit (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hk : 1 ≤ k)
    [Finite (R ⧸ Ideal.span {(p : R) ^ k})] {f : ArithmeticFunction R} (hf : IsUnit (f 1)) :
    (∀ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      levelCount p (frob p) (res hq hinj f) k ≤ levelCount p (Ep p) f k) ∧
    ∃ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      levelCount p (Ep p) f k = levelCount p (frob p) (res hq hinj f) k :=
  levelCount_eq_max_res_general p
    (hasLevel_kempner_any p f (ArithmeticFunction.isUnit_iff_isUnit_apply_one.2 hf) hk)

end AnyRing

section NumberField

open NumberField

/-- `R / p^k R` is finite for the ring of integers of a number field. -/
theorem finite_quot_ringOfIntegers (K : Type*) [Field K] [NumberField K] (p : ℕ)
    [hp : Fact p.Prime] (k : ℕ) : Finite (𝓞 K ⧸ Ideal.span {((p : 𝓞 K)) ^ k}) := by
  refine Ideal.finiteQuotientOfFreeOfNeBot _ ?_
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)

/-- The reduction over `𝓞 K` for every number field `K` (this covers `ℤ[χ] = 𝓞(ℚ(ζ_m))`),
every `f` with `f(1)` a unit. -/
theorem levelCount_eq_max_res_numberField (K : Type*) [Field K] [NumberField K] (p : ℕ)
    [hp : Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) {f : ArithmeticFunction (𝓞 K)} (hf : IsUnit (f 1)) :
    (∀ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      levelCount p (frob p) (res hq hinj f) k ≤ levelCount p (Ep p) f k) ∧
    ∃ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      levelCount p (Ep p) f k = levelCount p (frob p) (res hq hinj f) k :=
  have := finite_quot_ringOfIntegers K p k
  levelCount_eq_max_res_unit p hk hf

/-- L3's hypothesis `p ∣ a ^ p - a` fails over the Gaussian integers at `p = 2`, `a = i`; so
L3's `hasLevel_kempner` does not apply there, while `hasLevel_kempner_any` does. -/
theorem gauss_not_pow_sub : ¬ ((2 : GaussianInt) ∣ ⟨0, 1⟩ ^ 2 - ⟨0, 1⟩) := by
  rintro ⟨c, hc⟩
  have h1 := congrArg Zsqrtd.re hc
  have h2 := congrArg Zsqrtd.im hc
  simp [sq] at h1 h2
  omega

end NumberField

end Dir

end FrobLevel
