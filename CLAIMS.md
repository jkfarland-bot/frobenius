# Claims, sources, review status and Lean certification

Every result of the preprint *Minimal polynomials of sum z^(p^n) modulo prime powers: a proof of a
conjecture of Kauers, Krattenthaler and Mueller, and the exact number of divisor levels for the Moebius
function* (Joseph S. Farland, 2026), where it came from, how it was checked, and which Lean theorems
certify it. Numbers are those of the preprint. Every result listed is **proved (Lean)**: a kernel-checked
theorem in this repository, in the form stated in the preprint, on the standard axioms only (propext,
Classical.choice, Quot.sound), with no `sorry` and no `native_decide`. **Review** gives the independent
checks besides Lean.

Sources: seat names are Claude Opus agents (Anthropic) run by the author; the record numbers (R-...) are
those of the project's research ledger. Lean names are given as `namespace.theorem`; `FrobCong` is
`Frobenius/Mobius/Levels.lean`, `Frobenius.KKM` is `Frobenius/KKM/`, `FrobLevel` is `Frobenius/Levels/`.

| Result | Statement (short) | Source | Review | Lean |
|---|---|---|---|---|
| (2.1) | Summation: sum_{n<=x} (f * E_p g)(n) = sum_{m^p<=x} g(m) Sigma_f(x/m^p) | standard | Lean | `FrobCong.sum_mul_frobPush` |
| Thm 2.3 | Frobenius congruence f^{*p} = E_p(f^p) in characteristic p; mod p over every ring; f^{*p} = E_p f mod p over Z | classical | Lean | `FrobCong.frob_apply`, `FrobLevel.Dir.ep_ptPow_congr`, `FrobCong.cong_pow_frobPush`, `FrobCong.zeta_pow_cong` |
| Cor 2.4 | mu = d_{p-1} * mu_p over Z/p; M(N) mod p from D_{p-1} | seat PR-O (R-049) | Lean, cold reader | `FrobCong.moebius_eq_zeta_pow_mul_muP`, `FrobCong.mertens_mod` |
| Lemma 2.5 | Dwork iterate; mu = d_{p^k-1} * E_p(mu^{*p^{k-1}}) mod p^k | standard | Lean | `FrobCong.lift_cong`, `FrobCong.dwork_cong`, `FrobCong.moebius_dwork_cong` |
| Prop 3.1 | Truncated expansion: mu mod p^k with levels p-1, ..., kp-1; M(x) mod p^k | seat GZ-O (R-050) | Lean, cold reader, exact checks | `FrobCong.newton_cong_binom`, `FrobCong.mertens_cong_binom` |
| S(p^k) = pK(p,k) | The Kempner value of p^k | standard | Lean | `FrobCong.kempner_eq` |
| **Thm 4.4** | L(p,k) = S(p^k) - 1 for mu (identity at every n, integer g_z) | seat GZ-O2 (R-053) | Lean, two cold readers, exact checks | `FrobCong.levels_sharp_kempner`, `FrobCong.levels_sharp`; second proof `FrobLevel.Dir.levelCount_zetaZ_int`; Challenge `Frobenius.mobius_levels` |
| Thm 4.5 | Lower bound: a representation of level L has k <= K_0 + v_p(K_0!), K_0 = floor((L+1)/p) | seat GZ-O2 (R-053) | Lean, cold readers | `FrobCong.level_bound`, `FrobCong.level_bound_K`, `FrobCong.moment_bound` |
| Thm 4.9 | Construction: levels p i - 1, i <= K, whenever K + v_p(K!) >= k | seat GZ-O2 (R-053) | Lean, cold readers, exact checks | `FrobCong.tower_levels`, `FrobCong.tower_upper`, `FrobCong.tower_upper_min` |
| Prop 4.10 | An identity for mu mod 8 with levels 1 and 3; L(2,3) = 3; M(x) mod 8 | seat GZ-O2 (R-054) | Lean, exact checks | `FrobCong.mod_eight_identity`, `FrobCong.mod_eight_levels`, `FrobCong.mod_eight_sharp` |
| **Thm 5.1** | Conjecture 4 of Kauers, Krattenthaler and Mueller, every prime: a monic A in Z[z][t] of t-degree d with A(z, Phi_p) = 0 mod p^gamma exists iff p^gamma divides d!; least degree S(p^gamma); best modulus p^(v_p(d!)) | tower: seats N1, N2 (R-206); section: Claude Opus 5.5 | Lean (verified by seat V), cold reader C1 with own code | `Frobenius.KKM.degrees_vanishesMod`, `Frobenius.KKM.minimal_degree_eq_kempner`, `Frobenius.KKM.isGreatest_vanishesMod`; Challenge `Frobenius.kkm_degrees`, `Frobenius.kkm_conjecture4`, `Frobenius.kkm_greatest_modulus` |
| Lemma 5.2 | Some coefficient of A(z, Phi_p) equals d! | Claude Opus 5.5 (R-206) | Lean (seat LB, verified by seat V), cold reader C1 | `Frobenius.KKM.exists_coeff_evalPhi_eq_factorial`, `Frobenius.KKM.pow_dvd_factorial_of_vanishesMod` |
| Prop 5.3 | The tower A_a with A_a(z, Phi) = c_a delta^a(Phi), monic of degree p^a; A_1, A_2 explicit | seats N1, N2 (R-206) | Lean, cold reader C1 | `Frobenius.KKM.evalPhi_tower`, `tower_monic_natDegree`, `padicValInt_c`, `vanishesMod_tower`, `tower_one`, `tower_two` |
| **Thm 6.1** | Over every commutative ring, f(1) a unit: a level identity of level S(p^k) - 1 exists | seat GZ-O3 (R-056) | Lean (seat L9, verified L9v), cold readers | `FrobLevel.Dir.hasLevel_kempner_any`, `FrobLevel.Dir.levelCount_add_one_le_kempner_any`; Challenge `Frobenius.dirichlet_identity`, `Frobenius.dirichlet_upper` |
| Lemma 7.1 | Monic form of the level count | seats GZ-O4, GZ-O5 (R-058, R-060) | Lean (seat L1, verified L1v) | `FrobLevel.hasLevel_iff_monicAnn`, `FrobLevel.monicAnn_iff_revAnn`, `FrobLevel.levelCount_add_one` |
| Prop 7.2 | L_f + 1 <= S(p^k) for every Frobenius lift; <= min(t, S(p^k)) for t spanning elements | seats GZ-O4, GZ-O5 | Lean (L1), cold reader C4 | `FrobLevel.monicAnn_kempner`, `FrobLevel.levelCount_le_min_of_span`, `FrobLevel.levelCount_le_min` |
| **Thm 7.4** | Depth-flag formula for every unit of Z[[x_1..x_n]] and Z_p[[x_1..x_n]]; L_f = L_{1/f} | seat GZ-O8 (R-083) | Lean (seat L5, verified L5v), cold readers | `FrobLevel.levelCount_eq_flagValue_int`, `_padic`, `FrobLevel.levelCount_inv_int`; Challenge `Frobenius.flag_formula_int`, `_padic` |
| Cor 7.6 | Special cases: full rank, Z_n, pure depth, rank one mod p, 1 + p^a x + p^b y, two examples | seats GZ-O6 (R-080), GZ-O7 (R-082) | Lean (L1, L2, L5, L6), cold readers | `FrobLevel.levelCount_eq_of_fullRank_int`, `levelCount_zeta_int`, `levelCount_thmD_ge_int`, `levelCount_thmD_eq_int`, `levelCount_thmM_int`, `levelCount_propP_all_int`, `ce_two`, `ce_three` (and `_padic`) |
| **Thm 7.7** | Depth-flag formula in the Dirichlet ring over Z and Z_p, every f with f(1) a unit, flag of finite or infinite length | seat GZ-O9 (R-084) | Lean (seats L3, L5, L6, L7, verified), cold reader | `FrobLevel.Dir.levelCount_eq_dirFlagValue_int`, `_padic` (and primed forms), `FrobLevel.Dir.levelCount_inv_dir_int`; Challenge `Frobenius.dirichlet_flag_formula_int`, `_padic` |
| **Cor 7.8** | Over Z and Z_p: n primes with p not dividing f(q) give L_f + 1 >= min(p^n, S(p^k)); exact if S(p^k) <= p^n; no multiplicativity | seat GZ-O3 (R-056, weaker form); this form seat L3 | Lean (L3, verified L3v) | `FrobLevel.Dir.min_le_levelCount_int`, `FrobLevel.Dir.levelCount_eq_kempner_int` (and `_padic`); Challenge `Frobenius.dirichlet_lower_int`, `Frobenius.dirichlet_exact_int` (and `_padic`) |
| Cor 7.9 | mu, zeta, lambda, mu^2: S(p^k) - 1; d_2, mu * mu; pure depth in the Dirichlet ring; mu * chi_4 at p = 2 with values 1,1,3,3,3,5,5,7,7,7,7,9 | seats GZ-O9 (R-084), GZ-O10 (R-085) | Lean (L3, L9) | `FrobLevel.Dir.levelCount_moebius_int`, `levelCount_zetaZ_int`, `levelCount_liouville_int`, `levelCount_moebiusSq_int`, `levelCount_d2_int`, `levelCount_moebius_mul_moebius_int`, `levelCount_d2_two`, `levelCount_moebius_mul_moebius_two`, `levelCount_dir_depth_int`, `levelCount_muchi4`, `muchi4_values` |

## Palomar statement file

`Challenge.lean` restates the definitions using only Mathlib and states the fourteen results marked
"Challenge" above with `sorry`; `Solution.lean` proves them, and `lake comparator` checks every
definition they use, bodies included (`definition_names` is empty), with Lean's kernel, nanoda and
con-ron.

## Not in this release

Stronger forms of several results (the lower bound of Thm 4.5 from squarefree n alone and over every
Z/p^k-algebra; the shape of the levels in Thm 6.1; the lower bound over general rings; coefficient rings
Z[chi]; other Frobenius lifts) are proved on paper and will appear in a companion preprint. The
repository also contains further Lean results on other Frobenius lifts (`FrobLevel`, `L8v`, `L10`) that
the preprint does not use.
