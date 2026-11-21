module

public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.G1Series
public import Frobenius.Levels.Span

@[expose] public section

/-! L8v: lifts `x_i ↦ a_i` with `a_i(0) ∈ p ℤ_p` arbitrary (not nilpotent), built with Mathlib's
topological evaluation `MvPowerSeries.aeval`, to test L8's "every lift" theorems on lifts that do
not fix the origin. -/

namespace L8v

open MvPowerSeries MvPowerSeries.WithPiTopology Filter Topology

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

theorem closedBall_eq_span (k : ℕ) :
    Metric.closedBall (0 : ℤ_[p]) (((p : ℝ)⁻¹) ^ k) = (Ideal.span {(p : ℤ_[p]) ^ k} : Set ℤ_[p]) := by
  ext x
  rw [Metric.mem_closedBall, dist_zero_right, SetLike.mem_coe,
    ← PadicInt.norm_le_pow_iff_mem_span_pow, inv_pow, zpow_neg, zpow_natCast]

instance padic_isLinearTopology : IsLinearTopology ℤ_[p] ℤ_[p] := by
  have h1 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hp.out.pos)
  have h2 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have hb := Metric.nhds_basis_closedBall_pow (x := (0 : ℤ_[p])) h1 h2
  refine IsLinearTopology.mk_of_hasBasis ℤ_[p] (S := Ideal ℤ_[p])
    (s := fun k : ℕ => Ideal.span {(p : ℤ_[p]) ^ k}) (p := fun _ => True) ?_
  simpa only [closedBall_eq_span] using hb

theorem isTopNil_padic {c : ℤ_[p]} (hc : (p : ℤ_[p]) ∣ c) : IsTopologicallyNilpotent c := by
  obtain ⟨d, rfl⟩ := hc
  have : ‖(p : ℤ_[p]) * d‖ < 1 := by
    rw [norm_mul]
    calc ‖(p : ℤ_[p])‖ * ‖d‖ ≤ ‖(p : ℤ_[p])‖ * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one d) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one this

theorem hasEval_of_const (a : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (ha : ∀ i, (p : ℤ_[p]) ∣ constantCoeff (a i)) : HasEval a where
  hpow i := MvPowerSeries.LinearTopology.isTopologicallyNilpotent_of_constantCoeff (isTopNil_padic (ha i))
  tendsto_zero := by rw [Filter.cofinite_eq_bot]; exact tendsto_bot

/-- The lift `x_i ↦ a_i` (any `a_i` with `p ∣ a_i(0)`), via topological evaluation. -/
noncomputable def gLift (a : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (ha : ∀ i, (p : ℤ_[p]) ∣ constantCoeff (a i)) :
    MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p] :=
  (MvPowerSeries.aeval (R := ℤ_[p]) (hasEval_of_const a ha)).toRingHom

theorem gLift_X (a : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (ha : ∀ i, (p : ℤ_[p]) ∣ constantCoeff (a i)) (i : Fin n) : gLift a ha (X i) = a i := by
  have := MvPowerSeries.aeval_coe (R := ℤ_[p]) (hasEval_of_const a ha) (MvPolynomial.X i)
  simp only [MvPolynomial.coe_X, MvPolynomial.aeval_X] at this
  exact this

theorem gLift_C (a : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (ha : ∀ i, (p : ℤ_[p]) ∣ constantCoeff (a i)) (c : ℤ_[p]) : gLift a ha (C c) = C c := by
  have := (MvPowerSeries.aeval (R := ℤ_[p]) (hasEval_of_const a ha)).commutes c
  simpa [gLift, MvPowerSeries.algebraMap_apply] using this

theorem gLift_continuous (a : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (ha : ∀ i, (p : ℤ_[p]) ∣ constantCoeff (a i)) : Continuous (gLift a ha) :=
  MvPowerSeries.continuous_aeval (R := ℤ_[p]) (hasEval_of_const a ha)

theorem gLift_coe (a : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (ha : ∀ i, (p : ℤ_[p]) ∣ constantCoeff (a i)) (P : MvPolynomial (Fin n) ℤ_[p]) :
    gLift a ha (P : MvPowerSeries (Fin n) ℤ_[p]) = MvPolynomial.aeval a P :=
  MvPowerSeries.aeval_coe (R := ℤ_[p]) (hasEval_of_const a ha) P

/-- `p A` is closed in the product topology. -/
theorem isClosed_pdvd :
    IsClosed {g : MvPowerSeries (Fin n) ℤ_[p] | ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ∣ g} := by
  have : {g : MvPowerSeries (Fin n) ℤ_[p] | ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ∣ g}
      = ⋂ d, (fun g => coeff d g) ⁻¹' (Ideal.span {(p : ℤ_[p]) ^ 1} : Set ℤ_[p]) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe,
      Ideal.mem_span_singleton]
    have := FrobLevel.series_dvd_iff (p := p) 1 g
    rw [pow_one] at this
    simpa only [pow_one] using this
  rw [this]
  refine isClosed_iInter fun d => IsClosed.preimage (continuous_coeff ℤ_[p] d) ?_
  rw [← closedBall_eq_span]; exact Metric.isClosed_closedBall

theorem gLift_isFrobLift (a : Fin n → MvPowerSeries (Fin n) ℤ_[p])
    (ha : ∀ i, (p : ℤ_[p]) ∣ constantCoeff (a i))
    (hred : ∀ i, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ∣ a i - X i ^ p) :
    FrobLevel.IsFrobLift p (gLift a ha) := by
  set σ := gLift a ha
  set P : MvPowerSeries (Fin n) ℤ_[p] := ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p])
  let T : Set (MvPowerSeries (Fin n) ℤ_[p]) := {f | P ∣ σ f - f ^ p}
  have hadd : ∀ f g, f ∈ T → g ∈ T → f + g ∈ T := by
    intro f g hf hg
    obtain ⟨z, hz⟩ := exists_add_pow_prime_eq hp.out f g
    show P ∣ σ (f + g) - (f + g) ^ p
    rw [map_add, hz]
    have : σ f + σ g - (f ^ p + g ^ p + (p : MvPowerSeries (Fin n) ℤ_[p]) * f * g * z)
        = (σ f - f ^ p) + (σ g - g ^ p) - P * (f * g * z) := by simp only [P]; push_cast; ring
    rw [this]; exact dvd_sub (dvd_add hf hg) (dvd_mul_right _ _)
  have hmul : ∀ f g, f ∈ T → g ∈ T → f * g ∈ T := by
    intro f g hf hg
    show P ∣ σ (f * g) - (f * g) ^ p
    have : σ (f * g) - (f * g) ^ p = (σ f - f ^ p) * σ g + f ^ p * (σ g - g ^ p) := by
      rw [map_mul]; ring
    rw [this]; exact dvd_add (dvd_mul_of_dvd_left hf _) (dvd_mul_of_dvd_right hg _)
  have hC : ∀ c, C c ∈ T := by
    intro c
    show P ∣ σ (C c) - C c ^ p
    rw [gLift_C, ← map_pow]
    obtain ⟨w, hw⟩ := FrobLevel.padicInt_pow_sub p c
    refine ⟨C (-w), ?_⟩
    rw [← map_sub, show c - c ^ p = - (c ^ p - c) by ring, hw, show P = C (p : ℤ_[p]) by simp [P]]
    rw [← map_mul]; congr 1; ring
  have hX : ∀ i, X i ∈ T := by
    intro i
    show P ∣ σ (X i) - X i ^ p
    rw [gLift_X]; exact hred i
  have hpoly : ∀ Q : MvPolynomial (Fin n) ℤ_[p], (Q : MvPowerSeries (Fin n) ℤ_[p]) ∈ T := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C c => simpa using hC c
    | add f g hf hg => simpa using hadd _ _ hf hg
    | mul_X f i hf => simpa using hmul _ _ hf (hX i)
  have hclosed : IsClosed T := by
    have hc : Continuous fun f : MvPowerSeries (Fin n) ℤ_[p] => σ f - f ^ p :=
      (gLift_continuous a ha).sub (continuous_pow p)
    exact isClosed_pdvd.preimage hc
  have hdense : Dense (Set.range (MvPolynomial.toMvPowerSeries (σ := Fin n) (R := ℤ_[p]))) :=
    MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries
  intro f
  have hsub : Set.range (MvPolynomial.toMvPowerSeries (σ := Fin n) (R := ℤ_[p])) ⊆ T := by
    rintro _ ⟨Q, rfl⟩; exact hpoly Q
  have : closure (Set.range (MvPolynomial.toMvPowerSeries (σ := Fin n) (R := ℤ_[p]))) ⊆ T :=
    closure_minimal hsub hclosed
  rw [hdense.closure_eq] at this
  exact this (Set.mem_univ f)

end L8v
