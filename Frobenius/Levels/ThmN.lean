module

/-
Run r25, seat L8: **R-087 Theorem N with `F_σ`** (note Proposition `monotests` (b)).

`Ā = 𝔽_p[[x_1..x_n]]` (a domain), `K` its fraction field, `Ω_K ≅ K ^ n` with basis `dx_j`.
For `σ(x_i) = x_i ^ p + p h_i`, the note's `F_σ(∑_i v_i dx_i) = ∑_i v_i ^ p (x_i ^ (p-1) dx_i + d h̄_i)`
has `j`-th coordinate `v_j ^ p x_j ^ (p-1) + ∑_i v_i ^ p ∂_j h̄_i` (`Fsig`).

* `thmN_poly` (any lift satisfying the chain rule, e.g. every `x_i ↦ x_i ^ p + p h_i` with
  `h_i(0) = 0`): if `m ^ p ∈ B` then in `Ā`, for every `j`,
  `(∂_j m̄) ^ p x_j ^ (p-1) + ∑_i (∂_i m̄) ^ p ∂_j h̄_i = m̄ ^ (p-1) ∂_j m̄`.
* `thmN_fixed`: if moreover `m̄ ≠ 0`, then `d m̄ / m̄` is fixed by `F_σ` (`Fsig (dlog m̄) = dlog m̄`).
* `monotests_b_span`: if `B` is monomial (`m_1..m_n` with `m_i ^ p ∈ B` and invertible matrix
  of linear parts mod `p`), the fixed vectors `d m̄_i / m̄_i` of `F_σ` span `Ω_K`.
* `*_frobForm`: the same for L4's lifts `x_i ↦ x_i ^ p + p h_i`, `h_i(0) = 0`, with the chain
  rule discharged by `pderiv_frobForm` (Chain.lean).

The abstract theorems take the chain rule as a hypothesis (`hchain`); for a general continuous
lift it holds on paper (continuity), but only lifts fixing the origin are reachable by Mathlib's
`subst`, so only those are instantiated here.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.PropT
public import Frobenius.Levels.G1
public import Frobenius.Levels.G1Series
public import Frobenius.Levels.ThmR
public import Frobenius.Levels.Lifts
public import Frobenius.Levels.D1Linear
public import Frobenius.Levels.D1Gen
public import Frobenius.Levels.Chain

@[expose] public section

-- Port (Mathlib v4.35.0-rc2): restore the v4.33 instance path for `AddCommGroup (ZMod p)`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace FrobLevel

open MvPowerSeries

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

theorem redp_pderiv (i : Fin n) (f : MvPowerSeries (Fin n) ℤ_[p]) :
    redp p (pderiv (R := ℤ_[p]) i f) = pderiv (R := ZMod p) i (redp p f) := by
  ext d
  rw [redp, coeff_map, coeff_pderiv, coeff_pderiv, coeff_map, map_mul]
  simp

theorem redp_frob_eq_pow {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}
    (hσ : IsFrobLift p σ) (x : MvPowerSeries (Fin n) ℤ_[p]) : redp p (σ x) = redp p x ^ p := by
  obtain ⟨w, hw⟩ := hσ x
  have : σ x = x ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * w := by rw [← hw]; ring
  rw [this, map_add, map_mul, redp_p, zero_mul, add_zero, map_pow]

/-- The `j`-th coordinate of `F_σ(v)` for `σ(x_i) = x_i ^ p + p h_i` (`hb i = h̄_i`). -/
noncomputable def Fsig (hb : Fin n → MvPowerSeries (Fin n) (ZMod p))
    (v : Fin n → FractionRing (MvPowerSeries (Fin n) (ZMod p))) :
    Fin n → FractionRing (MvPowerSeries (Fin n) (ZMod p)) := fun j =>
  v j ^ p * algebraMap _ _ ((X j : MvPowerSeries (Fin n) (ZMod p)) ^ (p - 1))
    + ∑ i, v i ^ p * algebraMap _ _ (pderiv (R := ZMod p) j (hb i))

/-- `d m̄ / m̄` in coordinates. -/
noncomputable def dlog (mb : MvPowerSeries (Fin n) (ZMod p)) :
    Fin n → FractionRing (MvPowerSeries (Fin n) (ZMod p)) := fun j =>
  algebraMap _ _ (pderiv (R := ZMod p) j mb) / algebraMap _ _ mb

section Abstract

variable {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}

/-- **Theorem N, polynomial form** (any lift with the chain rule). -/
theorem thmN_poly (hσ : IsFrobLift p σ) (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (hh : ∀ i, σ (X i) = X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * h i)
    (hchain : ∀ (f : MvPowerSeries (Fin n) ℤ_[p]) (j : Fin n),
      pderiv (R := ℤ_[p]) j (σ f) = ∑ i, σ (pderiv (R := ℤ_[p]) i f) * pderiv (R := ℤ_[p]) j (σ (X i)))
    {m : MvPowerSeries (Fin n) ℤ_[p]} (hm : m ^ p ∈ frobImage σ) (j : Fin n) :
    pderiv (R := ZMod p) j (redp p m) ^ p * (X j : MvPowerSeries (Fin n) (ZMod p)) ^ (p - 1)
      + ∑ i, pderiv (R := ZMod p) i (redp p m) ^ p * pderiv (R := ZMod p) j (redp p (h i))
      = redp p m ^ (p - 1) * pderiv (R := ZMod p) j (redp p m) := by
  classical
  set P := ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) with hP
  set D := pderiv (R := ℤ_[p]) j
  have hDP : ∀ y, D (P * y) = P * D y := fun y => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hP, Derivation.map_natCast, mul_zero,
      add_zero]
  have hDX : ∀ i, D (σ (X i)) = P * (X i ^ (p - 1) * D (X i) + D (h i)) := fun i => by
    rw [hh i, map_add, hDP, pderiv_pow, hP]; ring
  set T := ∑ i, σ (pderiv (R := ℤ_[p]) i m) * (X i ^ (p - 1) * D (X i) + D (h i)) with hT
  have hDσ : D (σ m) = P * T := by
    rw [hchain m j, hT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hDX i]; ring
  have hδ : D (delta hσ m) = T - m ^ (p - 1) * D m := by
    have hpd := congrArg D (p_mul_delta hσ m)
    rw [hDP, map_sub, hDσ, pderiv_pow] at hpd
    apply sub_eq_zero.1
    apply noPTorsion_series (p := p) (n := n)
    rw [mul_sub, hpd]
    simp only [hP]
    ring
  have hDr : ∀ y, redp p (D y) = pderiv (R := ZMod p) j (redp p y) := fun y => redp_pderiv j y
  have h0 := pderiv_redp_delta_eq_zero hσ hm j
  rw [← redp_pderiv] at h0
  change redp p (D (delta hσ m)) = 0 at h0
  rw [hδ, map_sub, sub_eq_zero] at h0
  rw [map_mul, map_pow, redp_pderiv] at h0
  rw [← h0, hT, map_sum]
  simp only [map_mul, map_add, map_pow, redp_frob_eq_pow hσ, redp_pderiv, hDr, redp_X]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j]
  · rw [pderiv_X_self]; ring
  · intro i _ hij
    rw [pderiv_X_of_ne hij]
    ring
  · intro h'; exact absurd (Finset.mem_univ j) h'

/-- **Theorem N** (note Proposition `monotests` (b), first sentence): if `m ^ p ∈ B` and
`m̄ ≠ 0`, then `d m̄ / m̄` is fixed by `F_σ`. -/
theorem thmN_fixed (hσ : IsFrobLift p σ) (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (hh : ∀ i, σ (X i) = X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * h i)
    (hchain : ∀ (f : MvPowerSeries (Fin n) ℤ_[p]) (j : Fin n),
      pderiv (R := ℤ_[p]) j (σ f) = ∑ i, σ (pderiv (R := ℤ_[p]) i f) * pderiv (R := ℤ_[p]) j (σ (X i)))
    {m : MvPowerSeries (Fin n) ℤ_[p]} (hm : m ^ p ∈ frobImage σ) (hm0 : redp p m ≠ 0) :
    Fsig (fun i => redp p (h i)) (dlog (redp p m)) = dlog (redp p m) := by
  funext j
  set K := FractionRing (MvPowerSeries (Fin n) (ZMod p))
  set φ := algebraMap (MvPowerSeries (Fin n) (ZMod p)) K
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have ha : φ (redp p m) ≠ 0 := fun h0 => hm0 (hinj (by rw [h0, map_zero]))
  have key := congrArg φ (thmN_poly hσ h hh hchain hm j)
  simp only [map_add, map_mul, map_pow, map_sum] at key
  have hpow : ∀ x : K, x ^ p = x ^ (p - 1) * x := fun x => by
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
  simp only [Fsig, dlog]
  set a := φ (redp p m)
  calc (φ (pderiv (R := ZMod p) j (redp p m)) / a) ^ p * φ (X j ^ (p - 1))
        + ∑ i, (φ (pderiv (R := ZMod p) i (redp p m)) / a) ^ p * φ (pderiv (R := ZMod p) j (redp p (h i)))
      = (φ (pderiv (R := ZMod p) j (redp p m)) ^ p * φ (X j) ^ (p - 1)
        + ∑ i, φ (pderiv (R := ZMod p) i (redp p m)) ^ p * φ (pderiv (R := ZMod p) j (redp p (h i))))
          / a ^ p := by
        rw [add_div, Finset.sum_div, map_pow]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun i _ => by ring
    _ = a ^ (p - 1) * φ (pderiv (R := ZMod p) j (redp p m)) / (a ^ (p - 1) * a) := by
        rw [key, ← hpow]
    _ = φ (pderiv (R := ZMod p) j (redp p m)) / a := mul_div_mul_left _ _ (pow_ne_zero _ ha)

/-- **Prop `monotests` (b), second sentence**: if `B` is monomial (`m_i ^ p ∈ B`, linear parts
of `m̄_i` a basis), then the `F_σ`-fixed vectors `d m̄_i / m̄_i` span `Ω_K`. -/
theorem monotests_b_span (hσ : IsFrobLift p σ) (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (hh : ∀ i, σ (X i) = X i ^ p + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) * h i)
    (hchain : ∀ (f : MvPowerSeries (Fin n) ℤ_[p]) (j : Fin n),
      pderiv (R := ℤ_[p]) j (σ f) = ∑ i, σ (pderiv (R := ℤ_[p]) i f) * pderiv (R := ℤ_[p]) j (σ (X i)))
    (m : Fin n → MvPowerSeries (Fin n) ℤ_[p]) (hm : ∀ i, m i ^ p ∈ frobImage σ)
    (hM : IsUnit (linMat m)) :
    (∀ i, Fsig (fun i => redp p (h i)) (dlog (redp p (m i))) = dlog (redp p (m i))) ∧
      Submodule.span (FractionRing (MvPowerSeries (Fin n) (ZMod p)))
        (Set.range fun i => dlog (redp p (m i))) = ⊤ := by
  classical
  set K := FractionRing (MvPowerSeries (Fin n) (ZMod p))
  set φ := algebraMap (MvPowerSeries (Fin n) (ZMod p)) K
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  -- the Jacobian of the `m̄_i`, its constant term is `linMat m`
  let Jac : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) (ZMod p)) :=
    Matrix.of fun i j => pderiv (R := ZMod p) j (redp p (m i))
  have hJ0 : Jac.map constantCoeff = linMat m := by
    ext i j
    simp only [Matrix.map_apply, Jac, Matrix.of_apply, linMat]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add, redp, coeff_map]
    simp
  have hdetJ : Jac.det ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    rw [map_zero, RingHom.map_det, RingHom.mapMatrix_apply, hJ0] at this
    exact (Matrix.isUnit_iff_isUnit_det _).1 hM |>.ne_zero this
  -- `m̄_i ≠ 0`
  have hm0 : ∀ i, redp p (m i) ≠ 0 := by
    intro i h0
    apply hdetJ
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    simp only [Jac, Matrix.of_apply, h0, map_zero]
  refine ⟨fun i => thmN_fixed hσ h hh hchain (hm i) (hm0 i), ?_⟩
  -- the matrix of the vectors `d m̄_i / m̄_i`
  let W : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => dlog (redp p (m i)) j
  have hW : W = Matrix.diagonal (fun i => (φ (redp p (m i)))⁻¹) * Jac.map φ := by
    ext i j
    rw [Matrix.diagonal_mul]
    simp only [W, dlog, Matrix.map_apply, Jac, Matrix.of_apply]
    rw [div_eq_inv_mul]
  have hWu : IsUnit W := by
    rw [Matrix.isUnit_iff_isUnit_det, hW, Matrix.det_mul, Matrix.det_diagonal, isUnit_iff_ne_zero]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero fun h0 =>
      hm0 i (hinj (by rw [h0, map_zero]))) ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h0 => hdetJ (hinj (by rw [h0, map_zero]))
  have hli : LinearIndependent K W.row := Matrix.linearIndependent_rows_iff_isUnit.2 hWu
  have := hli.span_eq_top_of_card_eq_finrank' (by simp)
  exact this

end Abstract

section FrobForm

/-- Theorem N for `x_i ↦ x_i ^ p + p h_i`, `h_i(0) = 0` (polynomial form). -/
theorem thmN_poly_frobForm (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (h0 : ∀ i, constantCoeff (h i) = 0) {m : MvPowerSeries (Fin n) ℤ_[p]}
    (hm : m ^ p ∈ frobImage (frobForm h h0)) (j : Fin n) :
    pderiv (R := ZMod p) j (redp p m) ^ p * (X j : MvPowerSeries (Fin n) (ZMod p)) ^ (p - 1)
      + ∑ i, pderiv (R := ZMod p) i (redp p m) ^ p * pderiv (R := ZMod p) j (redp p (h i))
      = redp p m ^ (p - 1) * pderiv (R := ZMod p) j (redp p m) :=
  thmN_poly (frobForm_isFrobLift h h0) h (frobForm_X h h0) (pderiv_frobForm h h0) hm j

/-- **Theorem N** for `x_i ↦ x_i ^ p + p h_i`, `h_i(0) = 0`: `d m̄ / m̄` is `F_σ`-fixed. -/
theorem thmN_fixed_frobForm (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (h0 : ∀ i, constantCoeff (h i) = 0) {m : MvPowerSeries (Fin n) ℤ_[p]}
    (hm : m ^ p ∈ frobImage (frobForm h h0)) (hm0 : redp p m ≠ 0) :
    Fsig (fun i => redp p (h i)) (dlog (redp p m)) = dlog (redp p m) :=
  thmN_fixed (frobForm_isFrobLift h h0) h (frobForm_X h h0) (pderiv_frobForm h h0) hm hm0

/-- **Prop `monotests` (b)** for `x_i ↦ x_i ^ p + p h_i`, `h_i(0) = 0`. -/
theorem monotests_b_frobForm (h : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (h0 : ∀ i, constantCoeff (h i) = 0) (m : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (hm : ∀ i, m i ^ p ∈ frobImage (frobForm h h0)) (hM : IsUnit (linMat m)) :
    (∀ i, Fsig (fun i => redp p (h i)) (dlog (redp p (m i))) = dlog (redp p (m i))) ∧
      Submodule.span (FractionRing (MvPowerSeries (Fin n) (ZMod p)))
        (Set.range fun i => dlog (redp p (m i))) = ⊤ :=
  monotests_b_span (frobForm_isFrobLift h h0) h (frobForm_X h h0) (pderiv_frobForm h h0) m hm hM

end FrobForm

end FrobLevel
