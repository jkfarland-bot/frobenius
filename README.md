# Frobenius

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24410644.svg)](https://doi.org/10.5281/zenodo.24410644)

Lean 4 / Mathlib formalization accompanying Joseph S. Farland, *Minimal polynomials of
sum z^(p^n) modulo prime powers: a proof of a conjecture of Kauers, Krattenthaler and Müller,
and the exact number of divisor levels for the Möbius function* (preprint,
version 2.0 [doi:10.5281/zenodo.24466526](https://doi.org/10.5281/zenodo.24466526), which matches this release; all versions [doi:10.5281/zenodo.24411194](https://doi.org/10.5281/zenodo.24411194)). The preprint contains only results proved here; every theorem in it is
followed by the names of its Lean proofs, and [CLAIMS.md](CLAIMS.md) gives the same map.

**AI assistance:** the Lean code in this repository was written by Claude (Anthropic), an AI
model, which also helped draft the preprint, develop and check the proofs, run the computations, and
search the literature. The formalized statements are machine-checked in Lean 4; the rest of the
preprint is not. The author, Joseph S. Farland, chose the problems, directed the work, and is
responsible for its content. No external human referee has reviewed the preprint or the
formalization.

Toolchain: `leanprover/lean4:v4.35.0-rc2`, Mathlib `v4.35.0-rc2` (the versions of the Palomar
template). Every file uses Lean's module system.

```
lake exe cache get
lake build
```

No `sorry` in the development, no `native_decide`, no new axioms: every declaration depends only
on `propext`, `Classical.choice` and `Quot.sound` (`Challenge.lean` states the fourteen
results with `sorry` by design; `Solution.lean` proves them).

## What is proved

For a prime `p` and `k ≥ 1`, let `S(p^k)` be the Kempner value, the least `N` with `p^k ∣ N!`.

* **The Möbius function** (Theorem 4.4). The least `L` for which `μ ≡ ∑_{z ≤ L} ζ^z * E_p(g_z)
  (mod p^k)` at every `n`, with `ζ^z` the Dirichlet powers of `ζ`, `E_p` the Frobenius
  pushforward `(E_p g)(j^p) = g(j)` and integer valued `g_z`, is `S(p^k) - 1`.
* **Conjecture 4 of Kauers, Krattenthaler and Müller, for every prime** (Theorem 5.1). With
  `Φ_p(z) = ∑_n z^(p^n)`, the least `t`-degree of a monic `A ∈ ℤ[z][t]` with
  `A(z, Φ_p(z)) ≡ 0 (mod p^γ)` is `S(p^γ)`; the possible degrees are exactly the `d` with
  `p^γ ∣ d!`.
* **Dirichlet inverses** (Theorem 6.1, Corollary 7.8). For every commutative ring and every `f`
  with `f(1)` a unit, `L_f(p,k) ≤ S(p^k) - 1`. Over `ℤ` and `ℤ_p`, `n` primes `q` with
  `p ∤ f(q)` and `p^n ≥ S(p^k)` give equality, with no multiplicativity assumed.
* **The depth-flag formula** (Theorems 7.4 and 7.7). For every unit of `ℤ[[x_1, …, x_n]]` or
  `ℤ_p[[x_1, …, x_n]]` with the lift `x_i ↦ x_i^p`, and for every `f` with `f(1)` a unit in the
  Dirichlet ring over `ℤ` or `ℤ_p`, the exact level count is
  `min(p^{r_f}, min{m : v_p(m!) + ∑_{j<r_f} (d(j+1) - d(j)) ⌊m/p^j⌋ ≥ k})`, with `d` the depth
  flag of `f`.

**Added in version 1.1.0** (seven modules, each verified by a seat that did not write it):

* **The lower bound in full** (`Frobenius/Mobius/LowerGen.lean`). If `c_0, …, c_L` in a ring `Λ`
  that is a `ℤ/p^k`-algebra with `p^(k-1) ≠ 0` satisfy `∑_z c_z z^r = (-1)^r` for
  `k ≤ r ≤ 2k - 1 + (p - 2) p^(k-1)`, then `L + 1 ≥ S(p^k)` (`thm_lower`); fewer rows suffice
  (`lower_slice_shift`). An identity for `μ` required only at squarefree `n` already needs
  `S(p^k) - 1` levels (`level_bound_squarefree`).
* **Closed forms** (`Frobenius/Mobius/Closed.lean`): `S(p^k) = p (k - ⌊k/(p+1)⌋)` for
  `k ≤ p^2 + p`, and `(p - 1) k < S(p^k) < (p - 1) k + p + s_p(K(p,k) - 1)`.
* **The shape of the levels** (`Frobenius/Levels/A1Shape.lean`): over every commutative ring the
  identity of level `S(p^k) - 1` can use only the levels `z = p i - 1`.
* **The lower bound over every commutative ring** (`Frobenius/Levels/A2Gen.lean`): if
  `p^(k-1) ∉ p^k O` and `f` is multiplicative on enough primes `q` with `f(q)` a unit modulo `p`, then
  `L_f(p,k) = S(p^k) - 1`.
* **Krattenthaler and Müller's Proposition 2** (`Frobenius/KKM/Prop2.lean`): their polynomial
  for the modulus `p^(p+1)` does not vanish modulo `p^(p+1)` at `Φ_p`; the corrected polynomial
  is the tower polynomial `A_2` for odd `p`.
* **Multiplicative `f`** (`Frobenius/Levels/MultFlag.lean`): over `ℤ` and `ℤ_p` the depth flag is the
  sorted list of the prime depths `ν_q = min {v_p f(q^a) : a ≥ 1, p ∤ a}`.
* **The Mertens function modulo 8** (`Frobenius/Mobius/ModEight.lean`):
  `μ ≡ 2 ζ * E_2(μ) - d_3 * E_2(μ * μ - 4a) (mod 8)`, and the summed form for `M(x)` through the
  squarefree count and `D_3`.

Results over coefficient rings Z[chi] and further results on other Frobenius lifts are proved on
paper in the larger paper; they are not claimed here.

## Layout for the Palomar registry

- `Challenge.lean` is the statement surface a reader should audit. It imports only Mathlib,
  defines the objects with docstrings (`kempner`, `frobPush`, `HasLevel`, `levelCount`, `Phi`,
  `evalPhi`, `VanishesMod`, the depth flag `flagValue` and its Dirichlet form
  `Dir.dirFlagValue`) and states the fourteen headline results with `sorry`.
- `Frobenius/Statements.lean` is a byte-identical copy of the Challenge's definitions.
- `Solution.lean` imports `Frobenius.Statements` and the development, proves bridge lemmas
  identifying each Challenge definition with the development's, and proves the fourteen
  statements.
- `comparator.json` lists the fourteen theorems. Its `definition_names` is empty on purpose:
  Comparator then checks every definition the statements use, bodies included, instead of
  treating definitions as holes whose bodies the solution may choose.
- `formalization.yaml` records authorship, sources, AI use, scope and fidelity.
- `scripts/` holds Palomar's checks, copied from the
  [Palomar starter template](https://github.com/PalomarRegistry/PalomarTemplate).

| Preprint | Challenge declaration |
|---|---|
| **Theorem 4.4** (`L(p,k) = S(p^k) - 1` for `μ`) | `Frobenius.mobius_levels` |
| **Theorem 5.1** (Conjecture 4 of Kauers, Krattenthaler and Müller) | `Frobenius.kkm_degrees`, `Frobenius.kkm_conjecture4` |
| Theorem 5.1, best modulus | `Frobenius.kkm_greatest_modulus` |
| **Theorem 6.1** (upper bound over every commutative ring) | `Frobenius.dirichlet_identity`, `Frobenius.dirichlet_upper` |
| Corollary 7.8 over `ℤ` | `Frobenius.dirichlet_lower_int`, `Frobenius.dirichlet_exact_int` |
| Corollary 7.8 over `ℤ_p` | `Frobenius.dirichlet_lower_padic`, `Frobenius.dirichlet_exact_padic` |
| **Theorem 7.4** (depth-flag formula, power series) | `Frobenius.flag_formula_int`, `Frobenius.flag_formula_padic` |
| **Theorem 7.7** (depth-flag formula, Dirichlet ring) | `Frobenius.dirichlet_flag_formula_int`, `Frobenius.dirichlet_flag_formula_padic` |

## The development

| Part | Namespace | Contents |
|---|---|---|
| `Frobenius/Mobius/Levels.lean` | `FrobCong` | Sections 2 to 4: the Frobenius congruence, the truncated expansion, Theorem 4.4 (`levels_sharp_kempner`), the identity modulo 8 |
| `Frobenius/KKM/` | `Frobenius.KKM` | Section 5: the tower `A_a(z, Φ_p) = c_a δ^a(Φ_p)`, the digit products, the coefficient `d!` (`exists_coeff_evalPhi_eq_factorial`), Conjecture 4 (`minimal_degree_eq_kempner`) |
| `Frobenius/Levels/` | `FrobLevel`, `FrobLevel.Dir`, `L8v`, `L10` | Sections 6 and 7: level counts over general rings, the Dirichlet ring, power series with the standard and other Frobenius lifts |
| `Frobenius/Mobius/LowerGen.lean`, `Closed.lean`, `ModEight.lean` | `FrobCong` | Version 1.1.0: the lower bound in full, closed forms, the identity modulo 8 in displayed form |
| `Frobenius/Levels/A1Shape.lean`, `A2Gen.lean`, `MultFlag.lean` | `FrobLevel.Dir` | Version 1.1.0: the shape of the levels, the lower bound over every commutative ring, multiplicative `f` |
| `Frobenius/KKM/Prop2.lean` | `Frobenius.KKM` | Version 1.1.0: Krattenthaler and Müller's Proposition 2 and its correction |

## Run Palomar's checks

```
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh      # needs bubblewrap (bwrap)
```

## How this was made

The work was done by Claude Opus agent seats under the author's direction. Each paper proof was
read by an independent cold reader with its own exact computations, and each Lean file was
verified by a seat that did not write it (fresh rebuild, module-wide axiom collector, non-vacuity
instances, planted errors).

## Citation

Software, version 1.1.0: [10.5281/zenodo.24466017](https://doi.org/10.5281/zenodo.24466017). Version 1.0.0: [10.5281/zenodo.24410645](https://doi.org/10.5281/zenodo.24410645). All versions: [10.5281/zenodo.24410644](https://doi.org/10.5281/zenodo.24410644).
Preprint: J. S. Farland, *Minimal polynomials of sum z^(p^n) modulo prime powers: a proof of a
conjecture of Kauers, Krattenthaler and Müller, and the exact number of divisor levels for the Möbius
function*, Zenodo, 2026, version 2.0 [10.5281/zenodo.24466526](https://doi.org/10.5281/zenodo.24466526) (version 1.0 [10.5281/zenodo.24411195](https://doi.org/10.5281/zenodo.24411195); all versions [10.5281/zenodo.24411194](https://doi.org/10.5281/zenodo.24411194)).
Every theorem of the preprint is proved in this repository. See [CITATION.cff](CITATION.cff).

Palomar registry: [PALOMAR-2026-11-21-000014](https://palomar-registry.org/), version 1, approved
21 November 2026 for commit `8587838137d563ef938e2d0db66ac31043cce7ad` (the fourteen statements of
`Challenge.lean`, checked against `Solution.lean` by `lake comparator`).

## License

Apache-2.0 (this repository). Cited papers keep their own licences.
