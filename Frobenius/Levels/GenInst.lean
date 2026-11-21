module

public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.G1Series
public import Frobenius.Levels.Span
public import Frobenius.Levels.Free
public import Frobenius.Levels.D1Gen
public import Frobenius.Levels.Chain
public import Frobenius.Levels.ThmN
public import Frobenius.Levels.DeltaChain
public import Frobenius.Levels.GenLift

@[expose] public section

/-! L8v: chain rule for every topological-evaluation lift (`gLift`, any constant terms in `p ℤ_p`),
and instances of L8's theorems on lifts with `h(0) ≠ 0`: `x ↦ x ^ p + p` and the translated torus
lift `x ↦ (1 + p + x) ^ p - (1 + p)`. -/

namespace L8v

open MvPowerSeries MvPowerSeries.WithPiTopology Filter Topology FrobLevel

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

theorem continuous_pderiv (i : Fin n) :
    Continuous (fun f : MvPowerSeries (Fin n) ℤ_[p] => pderiv (R := ℤ_[p]) i f) := by
  refine continuous_pi fun d => ?_
  have : (fun f : MvPowerSeries (Fin n) ℤ_[p] => (pderiv (R := ℤ_[p]) i f) d)
      = fun f => coeff (d + Finsupp.single i 1) f * (((d i : ℕ) : ℤ_[p]) + 1) := by
    funext f; exact coeff_pderiv f d
  rw [this]
  exact (continuous_coeff ℤ_[p] _).mul continuous_const

/-- **Chain rule for every `gLift`** (constant terms arbitrary in `p ℤ_p`), by density of
polynomials and continuity. -/
theorem gLift_chain (a : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (ha : ∀ i, (p : ℤ_[p]) ∣ constantCoeff (a i)) (f : MvPowerSeries (Fin n) ℤ_[p]) (j : Fin n) :
    pderiv (R := ℤ_[p]) j (gLift a ha f)
      = ∑ i, gLift a ha (pderiv (R := ℤ_[p]) i f) * pderiv (R := ℤ_[p]) j (gLift a ha (X i)) := by
  set σ := gLift a ha
  have hσc := gLift_continuous a ha
  have hc1 : Continuous fun f => pderiv (R := ℤ_[p]) j (σ f) := (continuous_pderiv j).comp hσc
  have hc2 : Continuous fun f => ∑ i, σ (pderiv (R := ℤ_[p]) i f) * pderiv (R := ℤ_[p]) j (σ (X i)) :=
    continuous_finsetSum _ fun i _ =>
      ((hσc.comp (continuous_pderiv i)).mul continuous_const)
  have hcl := isClosed_eq hc1 hc2
  have hpoly : ∀ Q : MvPolynomial (Fin n) ℤ_[p],
      pderiv (R := ℤ_[p]) j (σ (Q : MvPowerSeries (Fin n) ℤ_[p]))
        = ∑ i, σ (pderiv (R := ℤ_[p]) i (Q : MvPowerSeries (Fin n) ℤ_[p])) * pderiv (R := ℤ_[p]) j (σ (X i)) := by
    intro Q
    rw [gLift_coe, pderiv_aeval_chain]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pderiv_coe, gLift_coe, gLift_X]
  have hdense : Dense (Set.range (MvPolynomial.toMvPowerSeries (σ := Fin n) (R := ℤ_[p]))) :=
    MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries
  have hsub : Set.range (MvPolynomial.toMvPowerSeries (σ := Fin n) (R := ℤ_[p]))
      ⊆ {f | pderiv (R := ℤ_[p]) j (σ f) = ∑ i, σ (pderiv (R := ℤ_[p]) i f) * pderiv (R := ℤ_[p]) j (σ (X i))} := by
    rintro _ ⟨Q, rfl⟩; exact hpoly Q
  have := closure_minimal hsub hcl
  rw [hdense.closure_eq] at this
  exact this (Set.mem_univ f)

/-! ### Lift 1: `x ↦ x ^ p + p` (h = 1, h(0) = 1) -/

theorem a1_const : ∀ i : Fin 1, (p : ℤ_[p]) ∣ constantCoeff
    ((fun _ => X 0 ^ p + ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p])) i) := by
  intro i
  simp [hp.out.ne_zero]

noncomputable def liftPlusP : MvPowerSeries (Fin 1) ℤ_[p] →+* MvPowerSeries (Fin 1) ℤ_[p] :=
  gLift (fun _ => X 0 ^ p + ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p])) a1_const

theorem liftPlusP_X : liftPlusP (p := p) (X 0)
    = X 0 ^ p + ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p]) * 1 := by
  rw [mul_one]; exact gLift_X _ _ 0

theorem liftPlusP_isFrobLift : IsFrobLift p (liftPlusP (p := p)) :=
  gLift_isFrobLift _ a1_const (fun i => ⟨1, by fin_cases i; simp⟩)

/-- the lift does not fix the origin: `h(0) = 1 ≠ 0` -/
theorem liftPlusP_h0 : constantCoeff (1 : MvPowerSeries (Fin 1) ℤ_[p]) ≠ 0 := by simp

/-- Freeness applies to `x ↦ x ^ p + p`. -/
theorem free_liftPlusP (f : MvPowerSeries (Fin 1) ℤ_[p]) :
    (∃ c : (Fin 1 →₀ ℕ) → MvPowerSeries (Fin 1) ℤ_[p],
      f = ∑ e ∈ digitExps p 1, liftPlusP (c e) * monomial e 1) ∧
    ∀ c c' : (Fin 1 →₀ ℕ) → MvPowerSeries (Fin 1) ℤ_[p],
      f = ∑ e ∈ digitExps p 1, liftPlusP (c e) * monomial e 1 →
      f = ∑ e ∈ digitExps p 1, liftPlusP (c' e) * monomial e 1 → ∀ e ∈ digitExps p 1, c e = c' e :=
  free_every_lift (liftPlusP_isFrobLift (p := p)) f

/-- D1 with `m = σ(x) ∈ B` (so `m ^ p ∈ B`). -/
theorem d1_liftPlusP : (p : ℤ_[p]) ∣ ∑ i, coeff (Finsupp.single i 1) (liftPlusP (p := p) (X 0))
      * coeff (Finsupp.single 0 1) ((fun _ => (1 : MvPowerSeries (Fin 1) ℤ_[p])) i)
      - constantCoeff (liftPlusP (p := p) (X 0)) ^ (p - 1)
        * coeff (Finsupp.single 0 1) (liftPlusP (p := p) (X 0)) :=
  d1_linear_test_gen (liftPlusP_isFrobLift (p := p)) (fun _ => 1) (fun i => by
    fin_cases i; exact liftPlusP_X) (m := liftPlusP (X 0)) ⟨X 0 ^ p, by rw [map_pow]⟩ 0

/-- Theorem N, instantiated on a lift with `h(0) ≠ 0` (chain rule discharged by `gLift_chain`). -/
theorem thmN_liftPlusP {m : MvPowerSeries (Fin 1) ℤ_[p]} (hm : m ^ p ∈ frobImage (liftPlusP (p := p)))
    (hm0 : redp p m ≠ 0) :
    Fsig (fun _ => redp p (1 : MvPowerSeries (Fin 1) ℤ_[p])) (dlog (redp p m)) = dlog (redp p m) :=
  thmN_fixed (liftPlusP_isFrobLift (p := p)) (fun _ => 1) (fun i => by fin_cases i; exact liftPlusP_X)
    (gLift_chain _ a1_const) hm hm0

/-! ### Lift 2: translated torus `x ↦ (u + x) ^ p - u`, `u = 1 + p` -/

noncomputable abbrev uu : MvPowerSeries (Fin 1) ℤ_[p] := C (1 + (p : ℤ_[p]))

noncomputable abbrev aT : Fin 1 → MvPowerSeries (Fin 1) ℤ_[p] := fun _ => (uu + X 0) ^ p - uu

theorem aT_const : ∀ i, (p : ℤ_[p]) ∣ constantCoeff (aT (p := p) i) := by
  intro i
  simp only [aT, uu, map_sub, map_pow, map_add, constantCoeff_C, constantCoeff_X, add_zero]
  exact FrobLevel.padicInt_pow_sub p _

theorem aT_red : ∀ i, ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p]) ∣ aT (p := p) i - X i ^ p := by
  intro i
  fin_cases i
  obtain ⟨z, hz⟩ := exists_add_pow_prime_eq hp.out (uu (p := p)) (X 0)
  obtain ⟨w, hw⟩ := FrobLevel.padicInt_pow_sub p (1 + (p : ℤ_[p]))
  refine ⟨C w + uu * X 0 * z, ?_⟩
  simp only [aT, Fin.zero_eta]
  rw [hz]
  have : uu (p := p) ^ p - uu = ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p]) * C w := by
    simp only [uu]
    rw [← map_pow, ← map_sub, hw, map_mul, map_natCast]
  calc uu ^ p + X 0 ^ p + (p : MvPowerSeries (Fin 1) ℤ_[p]) * uu * X 0 * z - uu - X 0 ^ p
      = (uu ^ p - uu) + (p : MvPowerSeries (Fin 1) ℤ_[p]) * (uu * X 0 * z) := by ring
    _ = _ := by rw [this]; push_cast; ring

noncomputable def liftT : MvPowerSeries (Fin 1) ℤ_[p] →+* MvPowerSeries (Fin 1) ℤ_[p] :=
  gLift aT aT_const

theorem liftT_isFrobLift : IsFrobLift p (liftT (p := p)) := gLift_isFrobLift _ _ aT_red

noncomputable abbrev mT : MvPowerSeries (Fin 1) ℤ_[p] := uu + X 0

theorem liftT_m : liftT (p := p) mT = mT ^ p := by
  simp only [liftT, mT, map_add, uu, gLift_C, gLift_X, aT]
  ring

theorem liftT_mem : mT (p := p) ^ p ∈ frobImage (liftT (p := p)) := ⟨mT, liftT_m⟩

/-- `h` for the translated torus lift, from the Frobenius congruence. -/
noncomputable def hT : Fin 1 → MvPowerSeries (Fin 1) ℤ_[p] :=
  fun i => Classical.choose (aT_red (p := p) i)

theorem liftT_X : ∀ i, liftT (p := p) (X i) = X i ^ p + ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p]) * hT i := by
  intro i
  have := Classical.choose_spec (aT_red (p := p) i)
  rw [liftT, gLift_X, hT, ← this]; ring

/-- `h_T(0) ≠ 0`: the lift does not fix the origin. -/
theorem hT_const_ne : constantCoeff (hT (p := p) 0) ≠ 0 := by
  intro h0
  have := Classical.choose_spec (aT_red (p := p) 0)
  have h2 := congrArg constantCoeff this
  rw [← hT] at h2
  simp only [aT, uu, map_sub, map_pow, map_add, constantCoeff_C, constantCoeff_X, add_zero, map_mul,
    h0, mul_zero, ne_eq, hp.out.ne_zero, not_false_eq_true, zero_pow, sub_zero, map_natCast] at h2
  -- `(1 + p) ^ p = 1 + p` in `ℤ_[p]`, false
  have h3 : (((1 + p) ^ p : ℕ) : ℤ_[p]) = ((1 + p : ℕ) : ℤ_[p]) := by
    push_cast; exact sub_eq_zero.1 h2
  have h4 := Nat.cast_injective h3
  have h5 : (1 + p) ^ 1 < (1 + p) ^ p :=
    Nat.pow_lt_pow_right (by have := hp.out.one_lt; omega) hp.out.one_lt
  rw [pow_one] at h5
  omega

theorem coeff_mT : coeff (Finsupp.single (0 : Fin 1) 1) (mT (p := p)) = 1 := by
  rw [mT, uu, LinearMap.map_add, coeff_C, if_neg (Finsupp.single_ne_zero.2 (one_ne_zero : (1 : ℕ) ≠ 0)),
    coeff_X, if_pos rfl, zero_add]

theorem linMat_mT : IsUnit (linMat (p := p) (fun _ : Fin 1 => mT (p := p))) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique, isUnit_iff_ne_zero]
  change PadicInt.toZMod (coeff (Finsupp.single (0 : Fin 1) 1) (mT (p := p))) ≠ 0
  rw [coeff_mT, map_one]
  exact one_ne_zero

/-- D1 on the translated torus lift (h(0) ≠ 0, m with unit linear part). -/
theorem d1_liftT : (p : ℤ_[p]) ∣ ∑ i, coeff (Finsupp.single i 1) (mT (p := p))
      * coeff (Finsupp.single 0 1) (hT i)
      - constantCoeff (mT (p := p)) ^ (p - 1) * coeff (Finsupp.single 0 1) (mT (p := p)) :=
  d1_linear_test_gen (liftT_isFrobLift (p := p)) hT liftT_X liftT_mem 0

/-- Λ idempotent on the translated torus lift. -/
theorem idem_liftT : Λmat (hT (p := p)) * Λmat hT = Λmat hT :=
  lambda_idempotent liftT_isFrobLift hT liftT_X (fun _ => mT) (fun _ => liftT_mem) linMat_mT

theorem redp_mT_ne : redp p (mT (p := p)) ≠ 0 := by
  intro h
  have := congrArg (coeff (Finsupp.single 0 1)) h
  rw [redp, coeff_map] at this
  rw [coeff_mT, map_one, map_zero] at this
  exact one_ne_zero this

/-- Theorem N on the translated torus lift (h(0) ≠ 0). -/
theorem thmN_liftT : Fsig (fun i => redp p (hT (p := p) i)) (dlog (redp p mT)) = dlog (redp p mT) :=
  thmN_fixed liftT_isFrobLift hT liftT_X (gLift_chain _ aT_const) liftT_mem redp_mT_ne

/-- Prop monotests (b) on the translated torus lift. -/
theorem monoB_liftT :
    (∀ _i : Fin 1, Fsig (fun i => redp p (hT (p := p) i)) (dlog (redp p mT)) = dlog (redp p mT)) ∧
      Submodule.span (FractionRing (MvPowerSeries (Fin 1) (ZMod p)))
        (Set.range fun (_ : Fin 1) => dlog (redp p (mT (p := p)))) = ⊤ := monotests_b_span (liftT_isFrobLift (p := p)) hT liftT_X (gLift_chain _ aT_const)
  (fun _ => mT) (fun _ => liftT_mem) linMat_mT

/-- δ chain rule on the translated torus lift. -/
theorem dchain_liftT (m : MvPowerSeries (Fin 1) ℤ_[p]) :
    pderiv (R := ZMod p) 0 (redp p (delta (liftT_isFrobLift (p := p)) m))
      = pderiv (R := ZMod p) 0 (redp p m) ^ p * (X 0 : MvPowerSeries (Fin 1) (ZMod p)) ^ (p - 1)
        + ∑ i, pderiv (R := ZMod p) i (redp p m) ^ p * pderiv (R := ZMod p) 0 (redp p (hT i))
        - redp p m ^ (p - 1) * pderiv (R := ZMod p) 0 (redp p m) :=
  delta_chain_rule (liftT_isFrobLift (p := p)) hT liftT_X (gLift_chain _ aT_const) m 0

/-- Sanity: the identity is not a Frobenius lift (the hypothesis is not trivially satisfiable). -/
theorem id_not_frobLift : ¬ IsFrobLift p (RingHom.id (MvPowerSeries (Fin 1) ℤ_[p])) := by
  intro h
  obtain ⟨w, hw⟩ := h (X 0)
  have := congrArg (coeff (Finsupp.single 0 1)) hw
  rw [RingHom.id_apply, map_sub, coeff_X, if_pos rfl, ← map_natCast (C (σ := Fin 1)), coeff_C_mul,
    coeff_X_pow, if_neg] at this
  · have hd : (p : ℤ_[p]) ∣ 1 := ⟨_, by rw [sub_zero] at this; exact this⟩
    exact PadicInt.p_nonunit (p := p) (isUnit_of_dvd_one hd)
  · intro h'
    have := congrArg (· 0) h'
    simp at this
    exact hp.out.one_lt.ne this

end L8v

