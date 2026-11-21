module

/-
Run r25, seat L10: the hypotheses of `thmM_origin` are satisfiable by lifts other than the
standard one, in every number of variables `n` and for every prime `p`.

* `liftPlusP`: `x_i ↦ x_i ^ p + p`. Not conjugate to the standard lift (note Prop `lifts`(b):
  its fixed point is not a zero of order `p`), it does not fix the origin, and its image is
  exactly `B_std` (`range_liftPlusP`). Theorem M with `θ = id` gives `L_f` = the standard value
  for every unit (`thmM_liftPlusP`).
* `transl`: the continuous automorphism `x_i ↦ x_i + p` (inverse `x_i ↦ x_i - p`), and
  `liftT`: `x_i ↦ (x_i + p) ^ p - p`, with `m_i = x_i + p`, `m_i ^ p ∈ B` (`thmM_liftT`).

Lifts are built with L8v's `gLift` (topological evaluation, `audit/GenLift.lean`, copied unchanged).
-/
public import Mathlib
public import Frobenius.Levels.GenLift
public import Frobenius.Levels.ThmMono

@[expose] public section

namespace L10

open MvPowerSeries MvPowerSeries.WithPiTopology FrobLevel L8v

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

theorem const_natCast_dvd : (p : ℤ_[p]) ∣ constantCoeff ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) := by
  simp

/-- `x_i ↦ x_i ^ p + p`. -/
noncomputable def liftPlusP : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p] :=
  gLift (fun i => X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p])) (fun i => by
    rw [map_add, map_pow, constantCoeff_X, zero_pow hp.out.ne_zero, zero_add]; simp)

theorem liftPlusP_X (i : Fin n) :
    liftPlusP (p := p) (X i) = X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) := by
  unfold liftPlusP; rw [gLift_X]

theorem liftPlusP_isFrobLift : IsFrobLift p (liftPlusP (p := p) (n := n)) := by
  unfold liftPlusP
  exact gLift_isFrobLift _ _ fun i => by simp

theorem liftPlusP_continuous : Continuous (liftPlusP (p := p) (n := n)) := by
  unfold liftPlusP; exact gLift_continuous _ _

theorem liftPlusP_hm (i : Fin n) :
    (RingEquiv.refl (MvPowerSeries (Fin n) ℤ_[p])) (X i) ^ p ∈ (liftPlusP (p := p)).range := by
  refine ⟨X i - ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]), ?_⟩
  rw [map_sub, liftPlusP_X, map_natCast]
  simp

/-- The image of `x ↦ x ^ p + p` is exactly `B_std`. -/
theorem range_liftPlusP : (liftPlusP (p := p) (n := n)).range = (frob p).range := by
  have h := range_eq_map_frob liftPlusP_isFrobLift liftPlusP_continuous
    (RingEquiv.refl (MvPowerSeries (Fin n) ℤ_[p])) continuous_id liftPlusP_hm
  rw [h]
  ext a; simp

/-- **Theorem M instance**: under `x_i ↦ x_i ^ p + p`, every unit has the standard R-083 value. -/
theorem thmM_liftPlusP {f u : MvPowerSeries (Fin n) ℤ_[p]} (hfu : f * u = 1) {k : ℕ}
    (hk : 1 ≤ k) : levelCount p (liftPlusP (p := p)) f k + 1 = flagValue p f k := by
  have := thmM_origin liftPlusP_isFrobLift liftPlusP_continuous
    (RingEquiv.refl (MvPowerSeries (Fin n) ℤ_[p])) continuous_id liftPlusP_hm hfu hk
  simpa using this

/-! ### The translation `x_i ↦ x_i + p` and the lift `x_i ↦ (x_i + p) ^ p - p` -/

theorem dvd_const_add (s : ℤ) (i : Fin n) :
    (p : ℤ_[p]) ∣ constantCoeff (X i + ((s * p : ℤ) : MvPowerSeries (Fin n) ℤ_[p])) := by
  rw [map_add, constantCoeff_X, zero_add, map_intCast]
  exact ⟨(s : ℤ_[p]), by push_cast; ring⟩

/-- `x_i ↦ x_i + s p`. -/
noncomputable def shift (s : ℤ) : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p] :=
  gLift (fun i => X i + ((s * p : ℤ) : MvPowerSeries (Fin n) ℤ_[p])) (dvd_const_add s)

theorem shift_X (s : ℤ) (i : Fin n) :
    shift (p := p) s (X i) = X i + ((s * p : ℤ) : MvPowerSeries (Fin n) ℤ_[p]) := by
  unfold shift; rw [gLift_X]

theorem shift_continuous (s : ℤ) : Continuous (shift (p := p) (n := n) s) := by
  unfold shift; exact gLift_continuous _ _

theorem shift_comp (s t : ℤ) (a : MvPowerSeries (Fin n) ℤ_[p]) :
    shift (p := p) s (shift t a) = shift (s + t) a := by
  let S : Set (MvPowerSeries (Fin n) ℤ_[p]) := {a | shift (p := p) s (shift t a) = shift (s + t) a}
  have hS : IsClosed S :=
    isClosed_eq ((shift_continuous s).comp (shift_continuous t)) (shift_continuous (s + t))
  refine forall_of_poly hS (fun P => ?_) a
  induction P using MvPolynomial.induction_on with
  | C c =>
    show shift (p := p) s (shift t _) = shift (s + t) _
    rw [MvPolynomial.coe_C, ringHom_C, ringHom_C, ringHom_C]
  | add f g hf hg =>
    show shift (p := p) s (shift t _) = shift (s + t) _
    rw [MvPolynomial.coe_add, map_add, map_add, map_add]
    exact congrArg₂ (· + ·) hf hg
  | mul_X f i hf =>
    show shift (p := p) s (shift t _) = shift (s + t) _
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, map_mul]
    refine congrArg₂ (· * ·) hf ?_
    simp only [shift_X, map_add, map_intCast]
    push_cast; ring

theorem shift_zero (a : MvPowerSeries (Fin n) ℤ_[p]) : shift (p := p) 0 a = a := by
  let S : Set (MvPowerSeries (Fin n) ℤ_[p]) := {a | shift (p := p) 0 a = a}
  have hS : IsClosed S := isClosed_eq (shift_continuous 0) continuous_id
  refine forall_of_poly hS (fun P => ?_) a
  induction P using MvPolynomial.induction_on with
  | C c => show shift (p := p) 0 _ = _; rw [MvPolynomial.coe_C, ringHom_C]
  | add f g hf hg =>
    show shift (p := p) 0 _ = _
    rw [MvPolynomial.coe_add, map_add]; exact congrArg₂ (· + ·) hf hg
  | mul_X f i hf =>
    show shift (p := p) 0 _ = _
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, shift_X]
    refine congrArg₂ (· * ·) hf ?_
    simp

/-- The continuous ring automorphism `x_i ↦ x_i + p`. -/
noncomputable def transl : MvPowerSeries (Fin n) ℤ_[p] ≃+* MvPowerSeries (Fin n) ℤ_[p] :=
  RingEquiv.ofRingHom (shift 1) (shift (-1))
    (RingHom.ext fun a => by simp [shift_comp, shift_zero])
    (RingHom.ext fun a => by simp [shift_comp, shift_zero])

theorem transl_apply (a : MvPowerSeries (Fin n) ℤ_[p]) : transl (p := p) a = shift 1 a := rfl

theorem transl_continuous : Continuous (transl (p := p) (n := n)) := shift_continuous 1

/-- `x_i ↦ (x_i + p) ^ p - p`. -/
noncomputable def liftT : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p] :=
  gLift (fun i => (X i + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p])) ^ p
      - ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p])) (fun i => by
    rw [map_sub, map_pow, map_add, constantCoeff_X, zero_add, map_natCast]
    exact dvd_sub (dvd_pow_self _ hp.out.ne_zero) dvd_rfl)

theorem liftT_X (i : Fin n) : liftT (p := p) (X i)
    = (X i + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p])) ^ p - ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) := by
  unfold liftT; rw [gLift_X]

theorem liftT_isFrobLift : IsFrobLift p (liftT (p := p) (n := n)) := by
  unfold liftT
  refine gLift_isFrobLift _ _ fun i => ?_
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (X i : MvPowerSeries (Fin n) ℤ_[p])
    ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p])
  rw [hr]
  refine ⟨((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ (p - 1) - 1
    + X i * ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * r, ?_⟩
  have hp1 : ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ p
      = ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ (p - 1) := by
    rw [← pow_succ']; congr 1; have := hp.out.one_lt; omega
  rw [hp1]; ring

theorem liftT_continuous : Continuous (liftT (p := p) (n := n)) := by
  unfold liftT; exact gLift_continuous _ _

theorem liftT_hm (i : Fin n) : transl (p := p) (X i) ^ p ∈ (liftT (p := p)).range := by
  refine ⟨X i + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]), ?_⟩
  rw [map_add, liftT_X, map_natCast, transl_apply, shift_X]
  push_cast; ring

/-- **Theorem M instance** with `m_i = x_i + p`. -/
theorem thmM_liftT {f u : MvPowerSeries (Fin n) ℤ_[p]} (hfu : f * u = 1) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (liftT (p := p)) f k + 1 = flagValue p (transl.symm f) k :=
  thmM_origin liftT_isFrobLift liftT_continuous transl transl_continuous liftT_hm hfu hk

/-- The image of `liftT` is `θ(B_std)` for the translation. -/
theorem range_liftT : (liftT (p := p) (n := n)).range
    = (frob p).range.map (transl (p := p) (n := n)).toRingHom :=
  range_eq_map_frob liftT_isFrobLift liftT_continuous transl transl_continuous liftT_hm

/-- The hypotheses of `thmM_origin_mclasses` are met, for every `f`, under `liftT`. -/
theorem nv_mclasses (f : MvPowerSeries (Fin n) ℤ_[p]) :
    ∃ b : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p],
      (∀ c ∈ digitExps p n, b c ∈ (liftT (p := p)).range) ∧
      f = ∑ c ∈ digitExps p n, transl (monomial c 1) * b c :=
  exists_mDecomp liftT_isFrobLift liftT_continuous transl transl_continuous liftT_hm f

/-- `liftPlusP` is not the standard lift (it does not fix the origin), for `n ≥ 1`. -/
theorem liftPlusP_ne_frob (hn : 0 < n) : liftPlusP (p := p) (n := n) ≠ frob p := by
  intro h
  have := congrArg (fun σ => constantCoeff (σ (X ⟨0, hn⟩ : MvPowerSeries (Fin n) ℤ_[p]))) h
  simp only [liftPlusP_X, frob_X, map_add, map_pow, constantCoeff_X, map_natCast] at this
  rw [zero_pow hp.out.ne_zero, zero_add] at this
  exact (Nat.cast_ne_zero.2 hp.out.ne_zero : ((p : ℕ) : ℤ_[p]) ≠ 0) this

end L10
